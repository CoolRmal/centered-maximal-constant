/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.TailSeries
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Tangent-line minorants for the radial part of the `α = 6/5` generator certificate

`CenteredMaximal.Fractional.jumpGen_truncBase_ge_radial` together with
`CenteredMaximal.Fractional.integral_tailRadial_ge` bounds the generator of the truncated diamond
base below by

`S · r ^ (-2α) + 4 · R ^ (-2α) · ∑_{n < K} tailCoeff α n · (r / R) ^ n`,     `r = diamondNorm z`,

a function of the diamond radius alone.  A certificate leaf has to turn that into a *number*, valid
throughout a dyadic rectangle.  **Endpoint monotonicity is not good enough.**  At subdivision depth
`3` the radius varies by `2 / 16 / 8 = 1 / 64` across a rectangle and `d/dr r ^ (-12/5) ≈ -2.4` near
`r = 1`, so replacing `r` by the largest radius of the rectangle throws away about `0.038`, against
a certificate margin of `7.05 · 10⁻⁵`.

Both summands are *convex* in `r`, so both lie above their tangent lines, and the tangent line loses
nothing to first order.  This file supplies those two tangent minorants and the observation that
makes them usable: a tangent line is affine in `r = |z₀| + |z₁|`, hence affine in `(|z₀|, |z₁|)`,
hence minimised over a rectangle at one of its two extreme corners.

## Main results

* `tangent_le_of_convexOn`: a convex function lies above its tangent line (the argument of
  `CenteredMaximal.Cauchy.Certificate`, made public and reusable).
* `rpow_neg_ge_tangent`: **the tangent minorant of the intrinsic power**,
  `r₀ ^ (-p) - p · r₀ ^ (-p-1) · (r - r₀) ≤ r ^ (-p)` for `p, r, r₀ > 0`.  Proved from Bernoulli's
  inequality at exponent `p + 1`, which needs no convexity plumbing.
* `pow_ge_tangent`: the tangent minorant of a monomial, `convexOn_pow` plus the tangent lemma.
* `tailSum_ge_tangent`: **the tangent minorant of the tail partial sum**.  Every `tailCoeff` is
  positive (`tailCoeff_pos`), so the partial sum is a nonnegative combination of the convex
  monomials `(r / R) ^ n` and is itself convex on `[0, ∞)`.
* `radialMinorant`, `radialMinorant_le`: the two tangents added together, and the fact that they
  minorise the radial reserve of `jumpGen_truncBase_ge_radial`.
* `min_affine_le`, `radialMinorant_corner_le`: **the corner principle**.  `radialMinorant` is
  affine in `r`, so over a rectangle `|z₀| ∈ [u₀, u₁]`, `|z₁| ∈ [v₀, v₁]` its minimum is attained
  at the smallest or at the largest radius, and a leaf check evaluates it at exactly those two
  corners.

## Why the intrinsic constant is a parameter

`jumpGen_truncBase_ge_radial` carries the closed form
`-4 π Γ(2α) cos(πα/2) / (α Γ(α)² sin(πα/2))` of the intrinsic constant.  Turning that into a
rational is `CenteredMaximal.Fractional.lt_sixFifths_const`, and the bridge between the two
expressions is not this file's business.  `radialMinorant_le` therefore takes the constant as a
parameter `S` with `0 ≤ S` and `S ≤ (the closed form)`; a leaf supplies
`S = 125337337 / 50000000` once the bridge is available.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### A convex function lies above its tangent line -/

/-- **A convex function lies above its tangent line at a point of its domain.**  Both secant-slope
comparisons of `ConvexOn` are needed, one on each side of the sample point. -/
theorem tangent_le_of_convexOn {f : ℝ → ℝ} {S : Set ℝ} (hconv : ConvexOn ℝ S f) {x y D : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hD : HasDerivAt f D x) : f x + D * (y - x) ≤ f y := by
  rcases lt_trichotomy y x with h | h | h
  · have hs := hconv.slope_le_of_hasDerivAt hy hx h hD
    rw [slope_def_field] at hs
    have := (div_le_iff₀ (sub_pos.2 h)).1 hs
    linarith
  · subst h; simp
  · have hs := hconv.le_slope_of_hasDerivAt hx hy h hD
    rw [slope_def_field] at hs
    have := (le_div_iff₀ (sub_pos.2 h)).1 hs
    linarith

/-! ### The tangent minorant of a negative power -/

/-- **The tangent line of `r ↦ r ^ (-p)` at `r₀` lies below the graph**, for `p > 0` on the open
half-line.  This is convexity of the negative power, but it is quicker to derive it from Bernoulli's
inequality at exponent `p + 1`: dividing the claim by `r₀ ^ (-p-1) > 0` and then by `r > 0` turns it
into `1 + (p + 1) (u - 1) ≤ u ^ (p + 1)` at `u = r₀ / r > 0`. -/
theorem rpow_neg_ge_tangent {p r r₀ : ℝ} (hp : 0 < p) (hr : 0 < r) (hr₀ : 0 < r₀) :
    r₀ ^ (-p) - p * r₀ ^ (-p - 1) * (r - r₀) ≤ r ^ (-p) := by
  have hu : 0 < r₀ / r := div_pos hr₀ hr
  have hA : (0 : ℝ) < r₀ ^ (-p - 1) := Real.rpow_pos_of_pos hr₀ _
  have key : (1 + p) * (r₀ / r) - p ≤ (r₀ / r) ^ (p + 1) := by
    have hb := one_add_mul_self_le_rpow_one_add (s := r₀ / r - 1) (by linarith)
      (p := p + 1) (by linarith)
    rw [show (1 : ℝ) + (r₀ / r - 1) = r₀ / r from by ring] at hb
    have hid : 1 + (p + 1) * (r₀ / r - 1) = (1 + p) * (r₀ / r) - p := by ring
    linarith [hb, hid.symm.le, hid.le]
  have h1 : r₀ ^ (-p - 1) * r₀ = r₀ ^ (-p) := by
    have h := Real.rpow_add hr₀ (-p - 1) 1
    rw [Real.rpow_one] at h
    rw [← h]
    congr 1
    ring
  have h2 : r₀ ^ (-p - 1) * r₀ ^ (p + 1) = 1 := by
    rw [← Real.rpow_add hr₀, show -p - 1 + (p + 1) = (0 : ℝ) from by ring, Real.rpow_zero]
  have h3 : r * (r₀ / r) ^ (p + 1) = r * r₀ ^ (p + 1) / r ^ (p + 1) := by
    rw [Real.div_rpow hr₀.le hr.le]
    ring
  have h4 : r₀ ^ (-p - 1) * (r * (r₀ / r) ^ (p + 1)) = r ^ (-p) := by
    rw [h3, show r₀ ^ (-p - 1) * (r * r₀ ^ (p + 1) / r ^ (p + 1))
      = r₀ ^ (-p - 1) * r₀ ^ (p + 1) * (r / r ^ (p + 1)) from by ring, h2, one_mul]
    rw [eq_comm, show (-p : ℝ) = 1 - (p + 1) from by ring, Real.rpow_sub hr, Real.rpow_one]
  have hmul := mul_le_mul_of_nonneg_left key (le_of_lt (mul_pos hA hr))
  rw [show r₀ ^ (-p - 1) * r * ((1 + p) * (r₀ / r) - p)
    = r₀ ^ (-p - 1) * r₀ * (1 + p) - p * r₀ ^ (-p - 1) * r from by field_simp,
    show r₀ ^ (-p - 1) * r * (r₀ / r) ^ (p + 1) = r₀ ^ (-p - 1) * (r * (r₀ / r) ^ (p + 1))
      from by ring, h4, h1] at hmul
  have hgoal : r₀ ^ (-p) - p * r₀ ^ (-p - 1) * (r - r₀)
      = r₀ ^ (-p) * (1 + p) - p * r₀ ^ (-p - 1) * r := by linear_combination p * h1
  rw [hgoal]
  exact hmul

/-! ### The tangent minorant of a monomial -/

/-- **The tangent line of `x ↦ x ^ n` at `y ≥ 0` lies below the graph on `[0, ∞)`.**  This is
`convexOn_pow` fed to `tangent_le_of_convexOn`; the natural subtraction in `y ^ (n - 1)` is harmless
because the whole term carries the factor `n`. -/
theorem pow_ge_tangent (n : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    y ^ n + (n : ℝ) * y ^ (n - 1) * (x - y) ≤ x ^ n :=
  tangent_le_of_convexOn (convexOn_pow n) hy hx (hasDerivAt_pow n y)

/-! ### The tangent minorant of the tail partial sum -/

/-- **The tangent line of the tail partial sum at `r₀` lies below the graph.**  The partial sum is
`∑_{n < K} tailCoeff α n (r / R) ^ n` and every coefficient is positive (`tailCoeff_pos`), so the
tangent inequality is `pow_ge_tangent` term by term, scaled by a nonnegative number.  The chain rule
contributes the factor `1 / R` of the linear term. -/
theorem tailSum_ge_tangent {α R r r₀ : ℝ} (hα : 0 < α) (hR : 0 < R) (hr : 0 ≤ r) (hr₀ : 0 ≤ r₀)
    (K : ℕ) :
    (∑ n ∈ Finset.range K, tailCoeff α n * (r₀ / R) ^ n)
        + (∑ n ∈ Finset.range K, tailCoeff α n * (n : ℝ) * (r₀ / R) ^ (n - 1)) * ((r - r₀) / R)
      ≤ ∑ n ∈ Finset.range K, tailCoeff α n * (r / R) ^ n := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  have hstep := pow_ge_tangent n (x := r / R) (y := r₀ / R) (div_nonneg hr hR.le)
    (div_nonneg hr₀ hR.le)
  have hdiff : r / R - r₀ / R = (r - r₀) / R := by ring
  rw [hdiff] at hstep
  have := mul_le_mul_of_nonneg_left hstep (tailCoeff_pos hα n).le
  calc tailCoeff α n * (r₀ / R) ^ n
        + tailCoeff α n * (n : ℝ) * (r₀ / R) ^ (n - 1) * ((r - r₀) / R)
      = tailCoeff α n * ((r₀ / R) ^ n + (n : ℝ) * (r₀ / R) ^ (n - 1) * ((r - r₀) / R)) := by ring
    _ ≤ tailCoeff α n * (r / R) ^ n := this

/-! ### The two tangents together -/

/-- **The affine-in-`r` minorant of the radial reserve.**  The tangent line at `r₀` of
`S r ^ (-2α)` plus the tangent line at `r₀` of `4 R ^ (-2α) ∑_{n < K} tailCoeff α n (r/R) ^ n`. -/
def radialMinorant (α R S : ℝ) (K : ℕ) (r₀ r : ℝ) : ℝ :=
  S * (r₀ ^ (-(2 * α)) - 2 * α * r₀ ^ (-(2 * α) - 1) * (r - r₀))
    + 4 * R ^ (-2 * α) * ((∑ n ∈ Finset.range K, tailCoeff α n * (r₀ / R) ^ n)
        + (∑ n ∈ Finset.range K, tailCoeff α n * (n : ℝ) * (r₀ / R) ^ (n - 1)) * ((r - r₀) / R))

/-- `radialMinorant` is an affine function of the radius: `radialMinorant … r₀ r = a + b r` with
the two coefficients displayed here. -/
theorem radialMinorant_eq_affine (α R S : ℝ) (K : ℕ) (r₀ r : ℝ) :
    radialMinorant α R S K r₀ r
      = (S * (r₀ ^ (-(2 * α)) + 2 * α * r₀ ^ (-(2 * α) - 1) * r₀)
          + 4 * R ^ (-2 * α) * ((∑ n ∈ Finset.range K, tailCoeff α n * (r₀ / R) ^ n)
              - (∑ n ∈ Finset.range K, tailCoeff α n * (n : ℝ) * (r₀ / R) ^ (n - 1)) * (r₀ / R)))
        + (-(S * (2 * α * r₀ ^ (-(2 * α) - 1)))
            + 4 * R ^ (-2 * α) *
              (∑ n ∈ Finset.range K, tailCoeff α n * (n : ℝ) * (r₀ / R) ^ (n - 1)) / R) * r := by
  rw [radialMinorant]
  ring

/-- **The radial reserve dominates its tangent minorant.**  The intrinsic constant is a parameter:
`S` has to be nonnegative and at most the closed form `jumpGen_truncBase_ge_radial` produces. -/
theorem radialMinorant_le {α R S r₀ : ℝ} (hα : 1 < α) (hα' : α < 2) (hR : 0 < R) (hS : 0 ≤ S)
    (hSle : S ≤ -4 * Real.pi * Real.Gamma (2 * α) * Real.cos (Real.pi * α / 2)
      / (α * Real.Gamma α ^ 2 * Real.sin (Real.pi * α / 2)))
    (hr₀ : 0 < r₀) (K : ℕ) {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0)
    (hz : diamondNorm z < R) :
    radialMinorant α R S K r₀ (diamondNorm z) ≤ jumpGen α (truncBase α R) z := by
  have hα0 : 0 < α := by linarith
  have hzne : z ≠ 0 := fun h => h0 (by simp [h])
  have hrpos : 0 < diamondNorm z := diamondNorm_pos hzne
  have hrpow : (0 : ℝ) < diamondNorm z ^ (-(2 * α)) := Real.rpow_pos_of_pos hrpos _
  -- the intrinsic power term
  have hint : S * (r₀ ^ (-(2 * α)) - 2 * α * r₀ ^ (-(2 * α) - 1) * (diamondNorm z - r₀))
      ≤ -4 * Real.pi * Real.Gamma (2 * α) * Real.cos (Real.pi * α / 2)
          / (α * Real.Gamma α ^ 2 * Real.sin (Real.pi * α / 2)) * diamondNorm z ^ (-2 * α) := by
    have htan := rpow_neg_ge_tangent (p := 2 * α) (r := diamondNorm z) (r₀ := r₀)
      (by linarith) hrpos hr₀
    have hexp : diamondNorm z ^ (-2 * α) = diamondNorm z ^ (-(2 * α)) := by
      congr 1
      ring
    rw [hexp]
    have hstep : S * (r₀ ^ (-(2 * α)) - 2 * α * r₀ ^ (-(2 * α) - 1) * (diamondNorm z - r₀))
        ≤ S * diamondNorm z ^ (-(2 * α)) := mul_le_mul_of_nonneg_left htan hS
    nlinarith [hrpow, hstep, hSle]
  -- the tail reserve
  have htail : 4 * R ^ (-2 * α) *
        ((∑ n ∈ Finset.range K, tailCoeff α n * (r₀ / R) ^ n)
          + (∑ n ∈ Finset.range K, tailCoeff α n * (n : ℝ) * (r₀ / R) ^ (n - 1))
            * ((diamondNorm z - r₀) / R))
      ≤ 2 * ∫ t : ℝ, tailRadial α R (diamondNorm z) t * |t| ^ (-(1 + α)) := by
    have hser := integral_tailRadial_ge (α := α) (R := R) (r := diamondNorm z) hα hα' hR
      hrpos.le hz K
    have htan := tailSum_ge_tangent (α := α) (R := R) (r := diamondNorm z) (r₀ := r₀) hα0 hR
      hrpos.le hr₀.le K
    have hRpow : (0 : ℝ) < R ^ (-2 * α) := Real.rpow_pos_of_pos hR _
    nlinarith [hser, htan, hRpow]
  have hbase := jumpGen_truncBase_ge_radial hα hα' h0 h1 hz
  rw [radialMinorant]
  linarith

/-! ### The corner principle -/

/-- **An affine function of the radius is minimised at an end of the radius range.** -/
theorem min_affine_le {a b r rlo rhi : ℝ} (hlo : rlo ≤ r) (hhi : r ≤ rhi) :
    min (a + b * rlo) (a + b * rhi) ≤ a + b * r := by
  rcases le_total 0 b with hb | hb
  · exact (min_le_left _ _).trans (by nlinarith)
  · exact (min_le_right _ _).trans (by nlinarith)

/-- **The corner principle.**  `radialMinorant` is affine in `r = |z₀| + |z₁|`, so over the
rectangle `|z₀| ∈ [u₀, u₁]`, `|z₁| ∈ [v₀, v₁]` it is at least its smaller value at the two extreme
corners `u₀ + v₀` and `u₁ + v₁`.  A leaf check therefore evaluates the minorant twice, not on a
grid. -/
theorem radialMinorant_corner_le (α R S : ℝ) (K : ℕ) (r₀ : ℝ) {u₀ u₁ v₀ v₁ : ℝ}
    {z : Fin 2 → ℝ} (hu : u₀ ≤ |z 0|) (hu' : |z 0| ≤ u₁) (hv : v₀ ≤ |z 1|) (hv' : |z 1| ≤ v₁) :
    min (radialMinorant α R S K r₀ (u₀ + v₀)) (radialMinorant α R S K r₀ (u₁ + v₁))
      ≤ radialMinorant α R S K r₀ (diamondNorm z) := by
  rw [radialMinorant_eq_affine, radialMinorant_eq_affine, radialMinorant_eq_affine]
  exact min_affine_le (by rw [diamondNorm]; linarith) (by rw [diamondNorm]; linarith)

end CenteredMaximal.Fractional

end

end
