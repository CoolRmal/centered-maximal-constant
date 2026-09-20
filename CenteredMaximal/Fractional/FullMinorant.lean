/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.AntiReserve
public import CenteredMaximal.Fractional.LeafAssembly

/-!
# The affine minorant of the full reserve, and the leaf inequality it proves

`CenteredMaximal.Fractional.radialMinorant` is the tangent line, in the diamond radius `r`, of the
*radial* reserve of `CenteredMaximal.Fractional.jumpGen_truncBase_ge_radial`.  With the anti-radial
reserve of `CenteredMaximal.Fractional.AntiReserve` there is a second convex summand, a function of
the coordinate difference `d = |z₀| − |z₁|`, and it needs a tangent of its own.

## Why a second tangent, and why four corners

The even tail series `∑_{n<L} evenTailCoeff α n x^n` has only *even* powers, so it is convex on the
whole line — not merely on `[0, ∞)` — and its tangent at any `d₀`, of either sign, minorises it
(`evenSum_ge_tangent`, from `Even.convexOn_pow`).  Adding the two tangents gives a function that is
affine in `r = |z₀| + |z₁|` *and* in `d = |z₀| − |z₁|`, hence affine in `(|z₀|, |z₁|)` — but with
**different** coefficients in the two coordinates, unlike `radialMinorant`, whose coefficients are
equal.  Its minimum over a rectangle is therefore attained at one of the **four** corners, not at
one of the two extreme radii, and a leaf check evaluates it four times.

## Main results

* `evenPow_ge_tangent`, `evenSum_ge_tangent`: the tangent minorant of the even tail series, valid
  at every real `d₀` and `d`.
* `antiMinorant`, `antiMinorant_eq_affine`: the anti-radial tangent and its affine form.
* `fullMinorant`, `fullMinorant_le`: **the two tangents together**, and the fact that they minorise
  the generator of the truncated base.
* `min_four_affine_le`, `fullMinorant_corner_le`: **the four-corner principle.**
* `jumpGen_fracKernel_nonneg_of_full`: **the leaf inequality of the `α = 6/5` generator
  certificate**, the replacement for `jumpGen_fracKernel_nonneg_of_bounds` that the certificate can
  actually afford.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### The tangent minorant of an even monomial -/

/-- **The tangent line of `x ↦ x ^ n` at any real `y` lies below the graph for even `n`.**  Unlike
`pow_ge_tangent`, which needs the half-line, this holds on the whole line, because an even power is
convex there. -/
theorem evenPow_ge_tangent {n : ℕ} (hn : Even n) (x y : ℝ) :
    y ^ n + (n : ℝ) * y ^ (n - 1) * (x - y) ≤ x ^ n :=
  tangent_le_of_convexOn hn.convexOn_pow (mem_univ y) (mem_univ x) (hasDerivAt_pow n y)

/-- **The tangent line of the even tail partial sum lies below the graph**, at every real `d₀`.
The odd-index terms vanish identically, and the even-index ones are handled by
`evenPow_ge_tangent` with a nonnegative coefficient. -/
theorem evenSum_ge_tangent {α R d d₀ : ℝ} (hα : 0 < α) (L : ℕ) :
    (∑ n ∈ Finset.range L, evenTailCoeff α n * (d₀ / R) ^ n)
        + (∑ n ∈ Finset.range L, evenTailCoeff α n * (n : ℝ) * (d₀ / R) ^ (n - 1))
          * ((d - d₀) / R)
      ≤ ∑ n ∈ Finset.range L, evenTailCoeff α n * (d / R) ^ n := by
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  have hdiff : d / R - d₀ / R = (d - d₀) / R := by ring
  rcases Nat.even_or_odd n with he | ho
  · have hstep := evenPow_ge_tangent he (d / R) (d₀ / R)
    rw [hdiff] at hstep
    have hmul := mul_le_mul_of_nonneg_left hstep (evenTailCoeff_nonneg hα n)
    calc evenTailCoeff α n * (d₀ / R) ^ n
          + evenTailCoeff α n * (n : ℝ) * (d₀ / R) ^ (n - 1) * ((d - d₀) / R)
        = evenTailCoeff α n * ((d₀ / R) ^ n
            + (n : ℝ) * (d₀ / R) ^ (n - 1) * ((d - d₀) / R)) := by ring
      _ ≤ evenTailCoeff α n * (d / R) ^ n := hmul
  · have h1 : n % 2 = 1 := Nat.odd_iff.1 ho
    have hzero : evenTailCoeff α n = 0 := by rw [evenTailCoeff, if_neg (by omega)]
    rw [hzero]
    simp

/-! ### The two tangents together -/

/-- The tangent line at `d₀` of the anti-radial reserve, a function of the coordinate difference
`d = |z₀| − |z₁|` alone. -/
def antiMinorant (α R : ℝ) (L : ℕ) (d₀ d : ℝ) : ℝ :=
  4 * R ^ (-2 * α) * ((∑ n ∈ Finset.range L, evenTailCoeff α n * (d₀ / R) ^ n)
    + (∑ n ∈ Finset.range L, evenTailCoeff α n * (n : ℝ) * (d₀ / R) ^ (n - 1)) * ((d - d₀) / R))

/-- `antiMinorant` is an affine function of the coordinate difference. -/
theorem antiMinorant_eq_affine (α R : ℝ) (L : ℕ) (d₀ d : ℝ) :
    antiMinorant α R L d₀ d
      = 4 * R ^ (-2 * α) * ((∑ n ∈ Finset.range L, evenTailCoeff α n * (d₀ / R) ^ n)
            - (∑ n ∈ Finset.range L, evenTailCoeff α n * (n : ℝ) * (d₀ / R) ^ (n - 1)) * (d₀ / R))
        + 4 * R ^ (-2 * α) *
            (∑ n ∈ Finset.range L, evenTailCoeff α n * (n : ℝ) * (d₀ / R) ^ (n - 1)) / R * d := by
  rw [antiMinorant]
  ring

/-- **The affine minorant of the full reserve**: the radial tangent at `r₀` plus the anti-radial
tangent at `d₀`. -/
def fullMinorant (α R S : ℝ) (K L : ℕ) (r₀ d₀ r d : ℝ) : ℝ :=
  radialMinorant α R S K r₀ r + antiMinorant α R L d₀ d

/-- **The full reserve dominates its affine minorant.**  As for `radialMinorant_le`, the intrinsic
constant is a parameter: `S` has to be nonnegative and at most the closed form that
`jumpGen_truncBase_ge_series` produces. -/
theorem fullMinorant_le {α R S r₀ d₀ : ℝ} (hα : 1 < α) (hα' : α < 2) (hR : 0 < R) (hS : 0 ≤ S)
    (hSle : S ≤ -4 * Real.pi * Real.Gamma (2 * α) * Real.cos (Real.pi * α / 2)
      / (α * Real.Gamma α ^ 2 * Real.sin (Real.pi * α / 2)))
    (hr₀ : 0 < r₀) (K L : ℕ) {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0)
    (hz : diamondNorm z < R) :
    fullMinorant α R S K L r₀ d₀ (diamondNorm z) (|z 0| - |z 1|)
      ≤ jumpGen α (truncBase α R) z := by
  have hα0 : 0 < α := by linarith
  have hzne : z ≠ 0 := fun h => h0 (by simp [h])
  have hrpos : 0 < diamondNorm z := diamondNorm_pos hzne
  have hrpow : (0 : ℝ) < diamondNorm z ^ (-(2 * α)) := Real.rpow_pos_of_pos hrpos _
  have hRpow : (0 : ℝ) < R ^ (-2 * α) := Real.rpow_pos_of_pos hR _
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
  -- the two tangent minorants of the two series
  have htan := tailSum_ge_tangent (α := α) (R := R) (r := diamondNorm z) (r₀ := r₀) hα0 hR
    hrpos.le hr₀.le K
  have hetan := evenSum_ge_tangent (α := α) (R := R) (d := |z 0| - |z 1|) (d₀ := d₀) hα0 L
  have hmul1 := mul_le_mul_of_nonneg_left htan (by positivity : (0 : ℝ) ≤ 4 * R ^ (-2 * α))
  have hmul2 := mul_le_mul_of_nonneg_left hetan (by positivity : (0 : ℝ) ≤ 4 * R ^ (-2 * α))
  have hser := jumpGen_truncBase_ge_series hα hα' hR h0 h1 hz K L
  rw [fullMinorant, radialMinorant, antiMinorant]
  linarith

/-! ### The four-corner principle -/

/-- **An affine function of two variables is minimised at a corner of a rectangle.** -/
theorem min_four_affine_le {a b c u v u₀ u₁ v₀ v₁ : ℝ}
    (hu : u₀ ≤ u) (hu' : u ≤ u₁) (hv : v₀ ≤ v) (hv' : v ≤ v₁) :
    min (min (a + b * u₀ + c * v₀) (a + b * u₀ + c * v₁))
        (min (a + b * u₁ + c * v₀) (a + b * u₁ + c * v₁))
      ≤ a + b * u + c * v := by
  rcases le_total 0 b with hb | hb <;> rcases le_total 0 c with hc | hc
  · exact ((min_le_left _ _).trans (min_le_left _ _)).trans (by nlinarith)
  · exact ((min_le_left _ _).trans (min_le_right _ _)).trans (by nlinarith)
  · exact ((min_le_right _ _).trans (min_le_left _ _)).trans (by nlinarith)
  · exact ((min_le_right _ _).trans (min_le_right _ _)).trans (by nlinarith)

/-- **The four-corner principle.**  `fullMinorant`, read at `r = |z₀| + |z₁|` and
`d = |z₀| − |z₁|`, is affine in `(|z₀|, |z₁|)` with unequal coefficients, so over the rectangle
`|z₀| ∈ [u₀, u₁]`, `|z₁| ∈ [v₀, v₁]` it is at least its smallest value at the four corners. -/
theorem fullMinorant_corner_le (α R S : ℝ) (K L : ℕ) (r₀ d₀ : ℝ) {u₀ u₁ v₀ v₁ : ℝ}
    {z : Fin 2 → ℝ} (hu : u₀ ≤ |z 0|) (hu' : |z 0| ≤ u₁) (hv : v₀ ≤ |z 1|) (hv' : |z 1| ≤ v₁) :
    min (min (fullMinorant α R S K L r₀ d₀ (u₀ + v₀) (u₀ - v₀))
             (fullMinorant α R S K L r₀ d₀ (u₀ + v₁) (u₀ - v₁)))
        (min (fullMinorant α R S K L r₀ d₀ (u₁ + v₀) (u₁ - v₀))
             (fullMinorant α R S K L r₀ d₀ (u₁ + v₁) (u₁ - v₁)))
      ≤ fullMinorant α R S K L r₀ d₀ (diamondNorm z) (|z 0| - |z 1|) := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℝ, ∀ r : ℝ, radialMinorant α R S K r₀ r = a + b * r :=
    ⟨_, _, radialMinorant_eq_affine α R S K r₀⟩
  obtain ⟨c, e, hce⟩ : ∃ c e : ℝ, ∀ d : ℝ, antiMinorant α R L d₀ d = c + e * d :=
    ⟨_, _, antiMinorant_eq_affine α R L d₀⟩
  have key : ∀ u v : ℝ, fullMinorant α R S K L r₀ d₀ (u + v) (u - v)
      = a + c + (b + e) * u + (b - e) * v := by
    intro u v
    rw [fullMinorant, hab, hce]
    ring
  rw [show diamondNorm z = |z 0| + |z 1| from rfl, key, key, key, key, key]
  exact min_four_affine_le hu hu' hv hv'

/-! ### One rectangle of the certificate -/

/-- **The leaf inequality of the `α = 6/5` generator certificate.**  On a rectangle
`|z₀| ∈ [u₀, u₁]`, `|z₁| ∈ [v₀, v₁]` of the open diamond, off the coordinate axes, the generator of
the comparison kernel is nonnegative as soon as

* `S` is a nonnegative lower bound for the intrinsic constant,
* `splineLo` is a lower bound for the spline sum at `z`, and
* the *rational* inequality `hcheck` holds between `splineLo` and the smallest of the **four**
  corner values of the full affine minorant.

This replaces `jumpGen_fracKernel_nonneg_of_bounds`, whose minorant keeps only the radial half of
the exterior tail's reserve and is short of the certificate by about `0.8`. -/
theorem jumpGen_fracKernel_nonneg_of_full {S r₀ d₀ splineLo u₀ u₁ v₀ v₁ : ℝ} {K L : ℕ}
    (hS : 0 ≤ S)
    (hSle : S ≤ -4 * Real.pi * Real.Gamma (2 * (6 / 5)) * Real.cos (Real.pi * (6 / 5) / 2)
      / (6 / 5 * Real.Gamma (6 / 5) ^ 2 * Real.sin (Real.pi * (6 / 5) / 2)))
    (hr₀ : 0 < r₀)
    (hcheck : 0 ≤ fracBaseCoeff *
        min (min (fullMinorant (6 / 5) (7 / 4) S K L r₀ d₀ (u₀ + v₀) (u₀ - v₀))
                 (fullMinorant (6 / 5) (7 / 4) S K L r₀ d₀ (u₀ + v₁) (u₀ - v₁)))
            (min (fullMinorant (6 / 5) (7 / 4) S K L r₀ d₀ (u₁ + v₀) (u₁ - v₀))
                 (fullMinorant (6 / 5) (7 / 4) S K L r₀ d₀ (u₁ + v₁) (u₁ - v₁)))
      + splineLo)
    {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < 7 / 4)
    (hu : u₀ ≤ |z 0|) (hu' : |z 0| ≤ u₁) (hv : v₀ ≤ |z 1|) (hv' : |z 1| ≤ v₁)
    (hspl : splineLo ≤ ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
        ((16 : ℝ) ^ (6 / 5 : ℝ) *
          (jumpGen1 (6 / 5) bspline (16 * z 0 - ij.1) * bspline (16 * z 1 - ij.2)
            + bspline (16 * z 0 - ij.1) * jumpGen1 (6 / 5) bspline (16 * z 1 - ij.2)))) :
    0 ≤ jumpGen (6 / 5) fracKernel z := by
  rw [jumpGen_fracKernel_eq h0 h1 hz]
  have hfull := fullMinorant_le (α := 6 / 5) (R := 7 / 4) (S := S) (r₀ := r₀) (d₀ := d₀)
    (by norm_num) (by norm_num) (by norm_num) hS hSle hr₀ K L h0 h1 hz
  have hcorner := fullMinorant_corner_le (6 / 5) (7 / 4) S K L r₀ d₀ hu hu' hv hv'
  have hmul := mul_le_mul_of_nonneg_left (hcorner.trans hfull) fracBaseCoeff_pos.le
  linarith

end CenteredMaximal.Fractional

end

end
