/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.BoundedFunctional
public import CenteredMaximal.Cauchy.Semigroup
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The potential kernel is the fundamental solution of the coordinate generator

The coordinate Cauchy generator `A = (1 / (2π)) jumpGen 1` of `CenteredMaximal.Cauchy.Semigroup`
has the potential kernel `potential z = 1 / (2π (|u| + |v|))` of
`CenteredMaximal.Cauchy.Potential` as its fundamental solution: for every test function `φ` on the
plane,

`(1 / (2π)) * ∫ z, potential z * jumpGen 1 φ z = -φ 0`,

which is `potential_jumpGen`, the main result of this file. Writing `p_t = heatKernel t` and
`P t = ∫ p_t φ`, the proof integrates the semigroup equation `A p_t = ∂_t p_t`
(`jumpGen_heatKernel_deriv`) in time against `φ`:

`∫ G · Aφ = ∫_z (∫₀^∞ p_t dt) Aφ = ∫₀^∞ (∫_z p_t · Aφ) dt = ∫₀^∞ (∫_z (A p_t) · φ) dt
  = ∫₀^∞ P' t dt = lim_{T→∞} P T − lim_{ε→0⁺} P ε = 0 − φ 0.`

The five ingredients are the following.

## Decay and integrability of the generator

A test function is supported in some closed ball of radius `r > 0`
(`exists_radius_of_isTestFunction`). If `|φ| ≤ M₀` and `tsupport φ ⊆ closedBall 0 r`, then the
`j`-th coordinate term of `jumpGen α φ` at `x` has three features: `φ x = 0` as soon as `r < ‖x‖`;
the second difference `secondDiff φ j x t` vanishes for every small step, so the weight
`|t|^{-(1+α)}` is bounded on the support of the integrand; and the `t`-integral of
`|φ (x + t e_j)| + |φ (x − t e_j)|` is at most `4 r M₀`, because the support constrains `x j ± t` to
an interval of length `2 r`. This is `abs_jumpTerm_le_of_vanishing`, and it yields two estimates:

* `abs_jumpGen_le_of_norm_le`, `abs_jumpGen_one_le_of_norm_le`: the radial decay
  `|jumpGen α φ x| ≤ 8 r M₀ 2^{1+α} ‖x‖^{-(1+α)}` for `2 r ≤ ‖x‖`, using the vanishing radius
  `‖x‖ − r ≥ ‖x‖ / 2`;
* `abs_jumpTerm_le_of_abs_le`: the per-coordinate decay `|z j|^{-(1+α)}` of the `j`-th term for
  `2 r ≤ |z j|`, irrespective of the other coordinate.

The second difference in the direction `e_j` leaves the other coordinate untouched, so the `j`-th
term also *vanishes* unless that coordinate lies in `[−r, r]`. The `j`-th term is therefore
dominated by the product of an integrable profile in `z j` (`integrable_jumpProfile`) and the
indicator of a strip in the other coordinate, which gives
`integrable_jumpGen_of_isTestFunction`: `jumpGen α φ` is integrable for `0 < α < 2`.

Combining the radial decay with `potential z ≤ 1 / (2π ‖z‖)` (from `norm_le_diamondNorm`) makes the
product `potential · jumpGen 1 φ` decay like `‖z‖^{-3}`, dominated by `(1 + ‖z‖)^{-3}`; near the
origin `potential` is integrable and `jumpGen 1 φ` is bounded. This is
`integrable_potential_mul_jumpGen`, which is exactly the absolute convergence needed for Fubini.

## Self-adjointness of the generator

`integral_heatKernel_mul_jumpGen`: `∫ p_t · jumpGen 1 φ = ∫ jumpGen 1 p_t · φ`. Expanding the
generator coordinate by coordinate, the `z`- and `s`-integrals are exchanged (the double integral is
dominated by `p_t(z) · jumpBound s`), each of the three terms of the second difference is translated
by `z ↦ z ∓ s e_j` (`integral_mul_comp_add`, `integral_mul_comp_sub`), and the integrals are
exchanged back. The second exchange needs the second differences of `p_t` to be dominated by
`min (M₂ s², 4 M₀) M₀`, which is `abs_secondDiff_heatKernel_le`: the one-dimensional bounds
`|q_t| ≤ 1/(π t)` and `|∂²_x q_t| ≤ 6/(π t³)` (`cauchyDensity_le`, `abs_cauchyDensity_deriv_two_le`)
feed into the one-variable second-difference estimate `abs_secondDiff_le_sq_of_deriv`, and the
untouched factor of the product kernel is at most `1/(π t)`.

## The time derivative and the two boundary limits

* `hasDerivAt_integral_heatKernel_mul`: `P` is differentiable with `P' t = ∫ (∂_t p_t) φ`, by
  differentiation under the integral sign; on `|u − t| < t/2` the time derivative of `p_u` is
  bounded by `2 / (π² (t/2)³)` (`abs_deriv_heatKernel_le`), so `|φ|` times that constant dominates;
* `tendsto_integral_heatKernel_mul_atTop`: `P t → 0` as `t → ∞`, since `p_t ≤ (π t)^{-2}`;
* `tendsto_integral_heatKernel_mul_zero`: `P t → φ 0` as `t → 0⁺`. After the scaling `z = t w`
  (`integral_heatKernel_mul_eq_scaled`) the pairing is `∫ p_1(w) φ (t w) dw`, `p_1` is a
  probability density (`integral_heatKernel`), and dominated convergence applies with the
  dominating function `p_1 · M₀`.

## Assembling

`integrableOn_Ioi_heatKernel` makes the time slices integrable away from the origin, so Tonelli
turns `∫ G · Aφ` into `∫₀^∞ ∫_z p_t · Aφ`; self-adjointness and the semigroup equation identify
each slice with `P' t`; and the fundamental theorem of calculus on `(0, ∞)`, applied at `1/(n+1)`
and passed to the limit through `tendsto_setIntegral_of_monotone`, evaluates `∫₀^∞ P' = 0 − φ 0`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Metric Set
open scoped ENNReal Topology

namespace CenteredMaximal.Cauchy

variable {φ : (Fin 2 → ℝ) → ℝ} {α M₀ M₂ r : ℝ}

/-! ### The support radius of a test function -/

/-- A test function on the plane is supported in a closed ball of positive radius. -/
theorem exists_radius_of_isTestFunction (hφ : IsTestFunction φ) :
    ∃ r : ℝ, 0 < r ∧ tsupport φ ⊆ closedBall 0 r := by
  obtain ⟨R, hR⟩ := (hφ.2 : IsCompact (tsupport φ)).isBounded.subset_closedBall (0 : Fin 2 → ℝ)
  exact ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩

/-- A function supported in the closed ball of radius `r` vanishes outside that ball. -/
private theorem apply_eq_zero_of_lt_norm (hsupp : tsupport φ ⊆ closedBall 0 r)
    {y : Fin 2 → ℝ} (hy : r < ‖y‖) : φ y = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem =>
    absurd (mem_closedBall_zero_iff.1 (hsupp hmem)) (not_le.2 hy)

/-- A function supported in the closed ball of radius `r` vanishes at `x + s e_j` as soon as the
`j`-th coordinate `x j + s` exceeds `r` in absolute value. -/
private theorem apply_add_smul_single_eq_zero (hsupp : tsupport φ ⊆ closedBall 0 r) (j : Fin 2)
    (x : Fin 2 → ℝ) {s : ℝ} (hs : r < |x j + s|) : φ (x + s • Pi.single j 1) = 0 := by
  refine apply_eq_zero_of_lt_norm hsupp (hs.trans_le ?_)
  have h₁ := norm_le_pi_norm (x + s • Pi.single j (1 : ℝ)) j
  have h₂ : |x j + s| ≤ ‖x + s • Pi.single j (1 : ℝ)‖ := by
    simpa [Real.norm_eq_abs] using h₁
  exact h₂

/-! ### Decay of the generator far from the support -/

/-- **The core decay estimate for one coordinate term of the generator.** Suppose `|φ| ≤ M₀`, that
`φ` is supported in the closed ball of radius `r > 0`, that `φ x = 0`, and that the second
difference in the direction `e_j` vanishes for every step `|t| < ρ`. Then the weight
`|t|^{-(1+α)}` is at most `ρ^{-(1+α)}` wherever the integrand is supported, and the support
constrains `x j ± t` to an interval of length `2 r`, so the `t`-integral of
`|φ (x + t e_j)| + |φ (x − t e_j)|` is at most `4 r M₀`; altogether the `j`-th term of the
generator is at most `4 r M₀ ρ^{-(1+α)}`. -/
private theorem abs_jumpTerm_le_of_vanishing (hα : 0 < α) (h₀ : ∀ y, |φ y| ≤ M₀)
    (hsupp : tsupport φ ⊆ closedBall 0 r) (hr : 0 < r) (j : Fin 2) (x : Fin 2 → ℝ)
    (hx0 : φ x = 0) {ρ : ℝ} (hρ : 0 < ρ) (hvan : ∀ t : ℝ, |t| < ρ → secondDiff φ j x t = 0) :
    |∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α))| ≤ 4 * r * M₀ * ρ ^ (-(1 + α)) := by
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ 0)
  have hind1 : ∀ t : ℝ, |φ (x + t • Pi.single j 1)| ≤
      (Icc (-x j - r) (-x j + r)).indicator (fun _ => M₀) t := by
    intro t
    by_cases ht : t ∈ Icc (-x j - r) (-x j + r)
    · rw [indicator_of_mem ht]
      exact h₀ _
    · have hcon : r < |x j + t| := by
        by_contra hcon
        obtain ⟨h1, h2⟩ := abs_le.1 (not_lt.1 hcon)
        exact ht ⟨by linarith, by linarith⟩
      rw [apply_add_smul_single_eq_zero hsupp j x hcon, abs_zero]
      exact indicator_nonneg (fun _ _ => hM₀) t
  have hind2 : ∀ t : ℝ, |φ (x - t • Pi.single j 1)| ≤
      (Icc (x j - r) (x j + r)).indicator (fun _ => M₀) t := by
    intro t
    by_cases ht : t ∈ Icc (x j - r) (x j + r)
    · rw [indicator_of_mem ht]
      exact h₀ _
    · have hcon : r < |x j + -t| := by
        by_contra hcon
        obtain ⟨h1, h2⟩ := abs_le.1 (not_lt.1 hcon)
        exact ht ⟨by linarith, by linarith⟩
      rw [show x - t • Pi.single j (1 : ℝ) = x + (-t) • Pi.single j (1 : ℝ) by
        rw [neg_smul, ← sub_eq_add_neg], apply_add_smul_single_eq_zero hsupp j x hcon, abs_zero]
      exact indicator_nonneg (fun _ _ => hM₀) t
  have hpt : ∀ t : ℝ, ‖secondDiff φ j x t * |t| ^ (-(1 + α))‖ ≤
      ((Icc (-x j - r) (-x j + r)).indicator (fun _ => M₀) t
        + (Icc (x j - r) (x j + r)).indicator (fun _ => M₀) t) * ρ ^ (-(1 + α)) := by
    intro t
    have hnn : (0 : ℝ) ≤ (Icc (-x j - r) (-x j + r)).indicator (fun _ => M₀) t
        + (Icc (x j - r) (x j + r)).indicator (fun _ => M₀) t :=
      add_nonneg (indicator_nonneg (fun _ _ => hM₀) t) (indicator_nonneg (fun _ _ => hM₀) t)
    rcases lt_or_ge |t| ρ with ht | ht
    · rw [hvan t ht, zero_mul, norm_zero]
      exact mul_nonneg hnn (Real.rpow_nonneg hρ.le _)
    · have hw : |t| ^ (-(1 + α)) ≤ ρ ^ (-(1 + α)) := by
        rw [Real.rpow_neg (abs_nonneg t), Real.rpow_neg hρ.le, ← one_div, ← one_div]
        exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos hρ _)
          (Real.rpow_le_rpow hρ.le ht (by linarith))
      have hsd : |secondDiff φ j x t| ≤
          (Icc (-x j - r) (-x j + r)).indicator (fun _ => M₀) t
            + (Icc (x j - r) (x j + r)).indicator (fun _ => M₀) t := by
        rw [secondDiff, hx0]
        calc |φ (x + t • Pi.single j (1 : ℝ)) + φ (x - t • Pi.single j (1 : ℝ)) - 2 * 0|
            = |φ (x + t • Pi.single j (1 : ℝ)) + φ (x - t • Pi.single j (1 : ℝ))| := by
              rw [mul_zero, sub_zero]
          _ ≤ |φ (x + t • Pi.single j (1 : ℝ))| + |φ (x - t • Pi.single j (1 : ℝ))| :=
              abs_add_le _ _
          _ ≤ _ := add_le_add (hind1 t) (hind2 t)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
      exact mul_le_mul hsd hw (Real.rpow_nonneg (abs_nonneg t) _) hnn
  have hvol : ∀ a : ℝ, volume.real (Icc (a - r) (a + r)) = 2 * r := fun a => by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  have hind : ∀ a : ℝ, Integrable ((Icc (a - r) (a + r)).indicator fun _ => M₀) := fun a =>
    (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hIsum : Integrable fun t : ℝ =>
      ((Icc (-x j - r) (-x j + r)).indicator (fun _ => M₀) t
        + (Icc (x j - r) (x j + r)).indicator (fun _ => M₀) t) * ρ ^ (-(1 + α)) :=
    ((hind (-x j)).add (hind (x j))).mul_const _
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hIsum (Eventually.of_forall hpt)).trans_eq ?_
  rw [integral_mul_const, integral_add (hind (-x j)) (hind (x j)),
    integral_indicator_const _ measurableSet_Icc, integral_indicator_const _ measurableSet_Icc,
    hvol (-x j), hvol (x j)]
  simp only [smul_eq_mul]
  ring

/-- The elementary comparison `(v − r)^{-(1+α)} ≤ 2^{1+α} v^{-(1+α)}` for `2 r ≤ v`, which turns
the vanishing radius `v − r` of the core estimate into a power of `v`. -/
private theorem rpow_neg_sub_le (hα : 0 < α) (hr : 0 < r) {v : ℝ} (hv : 2 * r ≤ v) :
    (v - r) ^ (-(1 + α)) ≤ (2 : ℝ) ^ (1 + α) * v ^ (-(1 + α)) := by
  have hvpos : (0 : ℝ) < v := lt_of_lt_of_le (by positivity) hv
  have hb : (0 : ℝ) < v / 2 := by positivity
  have hb' : (0 : ℝ) < (v / 2) ^ (1 + α) := Real.rpow_pos_of_pos hb _
  have h1 : (v / 2) ^ (1 + α) ≤ (v - r) ^ (1 + α) :=
    Real.rpow_le_rpow hb.le (by linarith) (by linarith)
  have hp : (0 : ℝ) < (2 : ℝ) ^ (1 + α) := Real.rpow_pos_of_pos (by norm_num) _
  have hq : (0 : ℝ) < v ^ (1 + α) := Real.rpow_pos_of_pos hvpos _
  have hp' : (2 : ℝ) ^ (1 + α) ≠ 0 := hp.ne'
  have hq' : v ^ (1 + α) ≠ 0 := hq.ne'
  rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ v - r), Real.rpow_neg hvpos.le, ← one_div, ← one_div]
  refine (one_div_le_one_div_of_le hb' h1).trans_eq ?_
  rw [Real.div_rpow hvpos.le (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp

/-- **Decay of the jump generator far from the support.** If `|φ| ≤ M₀` and `φ` is supported in the
closed ball of radius `r > 0`, then for `2 r ≤ ‖x‖` the value `φ x` and all the translates
`φ (x ± t e_j)` with `|t| < ‖x‖ − r` vanish, so the core estimate applies with vanishing radius
`‖x‖ − r ≥ ‖x‖ / 2` in each of the two coordinates. -/
theorem abs_jumpGen_le_of_norm_le (hα : 0 < α) (h₀ : ∀ y, |φ y| ≤ M₀)
    (hsupp : tsupport φ ⊆ closedBall 0 r) (hr : 0 < r) {x : Fin 2 → ℝ} (hx : 2 * r ≤ ‖x‖) :
    |jumpGen α φ x| ≤ 8 * r * M₀ * ((2 : ℝ) ^ (1 + α) * ‖x‖ ^ (-(1 + α))) := by
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ 0)
  have hxpos : (0 : ℝ) < ‖x‖ := lt_of_lt_of_le (by positivity) hx
  have hx0 : φ x = 0 := apply_eq_zero_of_lt_norm hsupp (by linarith)
  have hterm : ∀ j : Fin 2, |∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α))|
      ≤ 4 * r * M₀ * ((2 : ℝ) ^ (1 + α) * ‖x‖ ^ (-(1 + α))) := by
    intro j
    refine (abs_jumpTerm_le_of_vanishing hα h₀ hsupp hr j x hx0
      (by linarith : (0 : ℝ) < ‖x‖ - r) fun t ht => ?_).trans
      (mul_le_mul_of_nonneg_left (rpow_neg_sub_le hα hr hx) (by positivity))
    have h1 : φ (x + t • Pi.single j (1 : ℝ)) = 0 := by
      refine apply_eq_zero_of_lt_norm hsupp ?_
      have h := norm_sub_norm_le x (-(t • Pi.single j (1 : ℝ)))
      rw [sub_neg_eq_add, norm_neg, norm_smul, Real.norm_eq_abs, Pi.norm_single, norm_one,
        mul_one] at h
      linarith
    have h2 : φ (x - t • Pi.single j (1 : ℝ)) = 0 := by
      refine apply_eq_zero_of_lt_norm hsupp ?_
      have h := norm_sub_norm_le x (t • Pi.single j (1 : ℝ))
      rw [norm_smul, Real.norm_eq_abs, Pi.norm_single, norm_one, mul_one] at h
      linarith
    rw [secondDiff, h1, h2, hx0]
    ring
  calc |jumpGen α φ x| = ‖∑ j : Fin 2, ∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α))‖ := by
        rw [jumpGen, Real.norm_eq_abs]
    _ ≤ ∑ j : Fin 2, ‖∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α))‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin 2, 4 * r * M₀ * ((2 : ℝ) ^ (1 + α) * ‖x‖ ^ (-(1 + α))) :=
        Finset.sum_le_sum fun j _ => by rw [Real.norm_eq_abs]; exact hterm j
    _ = 8 * r * M₀ * ((2 : ℝ) ^ (1 + α) * ‖x‖ ^ (-(1 + α))) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_ofNat]
        ring

/-- **Per-coordinate decay.** The `j`-th term of the generator decays like `|x j|^{-(1+α)}` as soon
as `2 r ≤ |x j|`, irrespective of the other coordinate: a translate `φ (x ± t e_j)` can only be
nonzero when `|x j ± t| ≤ r`, which forces `|t| ≥ |x j| − r`. -/
private theorem abs_jumpTerm_le_of_abs_le (hα : 0 < α) (h₀ : ∀ y, |φ y| ≤ M₀)
    (hsupp : tsupport φ ⊆ closedBall 0 r) (hr : 0 < r) (j : Fin 2) {x : Fin 2 → ℝ}
    (hx : 2 * r ≤ |x j|) :
    |∫ t : ℝ, secondDiff φ j x t * |t| ^ (-(1 + α))|
      ≤ 4 * r * M₀ * ((2 : ℝ) ^ (1 + α) * |x j| ^ (-(1 + α))) := by
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ 0)
  have hnx : |x j| ≤ ‖x‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm x j
  have hx0 : φ x = 0 := apply_eq_zero_of_lt_norm hsupp (by linarith)
  refine (abs_jumpTerm_le_of_vanishing hα h₀ hsupp hr j x hx0
    (by linarith : (0 : ℝ) < |x j| - r) fun t ht => ?_).trans
    (mul_le_mul_of_nonneg_left (rpow_neg_sub_le hα hr hx) (by positivity))
  have h1 : φ (x + t • Pi.single j (1 : ℝ)) = 0 := by
    refine apply_add_smul_single_eq_zero hsupp j x ?_
    have h := abs_sub_abs_le_abs_sub (x j) (-t)
    rw [abs_neg, sub_neg_eq_add] at h
    linarith
  have h2 : φ (x - t • Pi.single j (1 : ℝ)) = 0 := by
    rw [show x - t • Pi.single j (1 : ℝ) = x + (-t) • Pi.single j (1 : ℝ) by
      rw [neg_smul, ← sub_eq_add_neg]]
    refine apply_add_smul_single_eq_zero hsupp j x ?_
    have h := abs_sub_abs_le_abs_sub (x j) t
    rw [show x j - t = x j + -t from sub_eq_add_neg _ _] at h
    linarith
  rw [secondDiff, h1, h2, hx0]
  ring

/-- The `α = 1` form of the decay estimate: `|jumpGen 1 φ x| ≤ 32 r M₀ / ‖x‖²`. -/
theorem abs_jumpGen_one_le_of_norm_le (h₀ : ∀ y, |φ y| ≤ M₀)
    (hsupp : tsupport φ ⊆ closedBall 0 r) (hr : 0 < r) {x : Fin 2 → ℝ} (hx : 2 * r ≤ ‖x‖) :
    |jumpGen 1 φ x| ≤ 32 * r * M₀ / ‖x‖ ^ 2 := by
  have h := abs_jumpGen_le_of_norm_le (α := 1) one_pos h₀ hsupp hr hx
  have h1 : (2 : ℝ) ^ (1 + (1 : ℝ)) = 4 := by
    rw [show (1 : ℝ) + 1 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    norm_num
  have h2 : ‖x‖ ^ (-(1 + (1 : ℝ))) = (‖x‖ ^ 2)⁻¹ := by
    have h := abs_rpow_neg_two ‖x‖
    rwa [abs_norm] at h
  rw [h1, h2] at h
  refine h.trans_eq ?_
  rw [div_eq_mul_inv]
  ring

/-! ### Integrability of the generator of a test function -/

/-- The even profile `C (max |u| (2 r))^{-(1+α)}` is integrable on the line for `α > 0`: it is
constant on `[−2 r, 2 r]` and equal to `C |u|^{-(1+α)}` outside. -/
private theorem integrable_jumpProfile (hα : 0 < α) (hr : 0 < r) (C : ℝ) :
    Integrable fun u : ℝ => C * max |u| (2 * r) ^ (-(1 + α)) := by
  have hpos : ∀ u : ℝ, (0 : ℝ) < max |u| (2 * r) := fun u =>
    lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hcont : Continuous fun u : ℝ => C * max |u| (2 * r) ^ (-(1 + α)) :=
    continuous_const.mul ((continuous_abs.max continuous_const).rpow_const
      fun u => Or.inl (hpos u).ne')
  refine integrable_of_even (fun u => by rw [abs_neg]) ?_
  rw [← Ioc_union_Ioi_eq_Ioi (by positivity : (0 : ℝ) ≤ 2 * r), integrableOn_union]
  refine ⟨hcont.integrableOn_Ioc, ?_⟩
  have heq : EqOn (fun u : ℝ => C * max |u| (2 * r) ^ (-(1 + α)))
      (fun u : ℝ => C * u ^ (-(1 + α))) (Ioi (2 * r)) := fun u hu => by
    have hu' : 2 * r < u := hu
    show C * max |u| (2 * r) ^ (-(1 + α)) = C * u ^ (-(1 + α))
    rw [abs_of_pos (by linarith : (0 : ℝ) < u), max_eq_left hu'.le]
  rw [integrableOn_congr_fun heq measurableSet_Ioi]
  exact (integrableOn_Ioi_rpow_of_lt (by linarith) (by positivity)).const_mul C

/-- **The generator of a test function is integrable.** The `j`-th coordinate term vanishes unless
the other coordinate lies in `[−r, r]`, because the second difference in the direction `e_j` leaves
the other coordinate untouched; along the `j`-th coordinate the term is bounded by the constant
`∫ jumpBound` and decays like `|z j|^{-(1+α)}` beyond `2 r`. The product of these two profiles is
integrable in the plane, and the generator is the sum of the two coordinate terms. -/
theorem integrable_jumpGen_of_isTestFunction (hα : 0 < α) (hα' : α < 2) (hφ : IsTestFunction φ) :
    Integrable (jumpGen α φ) := by
  obtain ⟨r, hr, hsupp⟩ := exists_radius_of_isTestFunction hφ
  have hφc : Continuous φ := hφ.continuous
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (by norm_cast)
  obtain ⟨M₀, M₂, h₀, h₂⟩ := exists_bounds_of_hasCompactSupport hφ2 hφ.2
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ 0)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h₂ 0)
  have hjb : Integrable (jumpBound α M₀ M₂) := integrable_jumpBound hα hα' hM₀ hM₂
  obtain ⟨B, hB0, hFb⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ (j : Fin 2) (z : Fin 2 → ℝ),
      |∫ t : ℝ, secondDiff φ j z t * |t| ^ (-(1 + α))| ≤ B :=
    ⟨∫ s, jumpBound α M₀ M₂ s, integral_nonneg fun s => jumpBound_nonneg hM₀ hM₂ α s,
      fun j z => by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le hjb
          (Eventually.of_forall (norm_secondDiff_mul_rpow_le_jumpBound hφ2 h₀ h₂ α j z))⟩
  obtain ⟨C, hC1, hC2⟩ : ∃ C : ℝ, B ≤ C * (2 * r) ^ (-(1 + α))
      ∧ 4 * r * M₀ * (2 : ℝ) ^ (1 + α) ≤ C := by
    have h2r : (0 : ℝ) < 2 * r := by positivity
    have hp : (0 : ℝ) < (2 * r) ^ (1 + α) := Real.rpow_pos_of_pos h2r _
    have hp' : (2 * r) ^ (1 + α) ≠ 0 := hp.ne'
    refine ⟨B * (2 * r) ^ (1 + α) + 4 * r * M₀ * (2 : ℝ) ^ (1 + α), ?_, ?_⟩
    · rw [Real.rpow_neg h2r.le, add_mul]
      have e1 : B * (2 * r) ^ (1 + α) * ((2 * r) ^ (1 + α))⁻¹ = B := by field_simp
      have e2 : (0 : ℝ) ≤ 4 * r * M₀ * (2 : ℝ) ^ (1 + α) * ((2 * r) ^ (1 + α))⁻¹ := by positivity
      linarith
    · have e3 : (0 : ℝ) ≤ B * (2 * r) ^ (1 + α) := by positivity
      linarith
  have hbd : ∀ (j : Fin 2) (z : Fin 2 → ℝ),
      |∫ t : ℝ, secondDiff φ j z t * |t| ^ (-(1 + α))| ≤ C * max |z j| (2 * r) ^ (-(1 + α)) := by
    intro j z
    rcases le_or_gt |z j| (2 * r) with hk | hk
    · rw [max_eq_right hk]
      exact (hFb j z).trans hC1
    · rw [max_eq_left hk.le]
      refine (abs_jumpTerm_le_of_abs_le hα h₀ hsupp hr j hk.le).trans ?_
      calc 4 * r * M₀ * ((2 : ℝ) ^ (1 + α) * |z j| ^ (-(1 + α)))
          = 4 * r * M₀ * (2 : ℝ) ^ (1 + α) * |z j| ^ (-(1 + α)) := by ring
        _ ≤ C * |z j| ^ (-(1 + α)) :=
            mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg (abs_nonneg _) _)
  have hvan : ∀ (j k : Fin 2), j ≠ k → ∀ z : Fin 2 → ℝ, r < |z k| →
      (∫ t : ℝ, secondDiff φ j z t * |t| ^ (-(1 + α))) = 0 := by
    intro j k hjk z hz
    have hsingle : (Pi.single j (1 : ℝ) : Fin 2 → ℝ) k = 0 :=
      Pi.single_eq_of_ne (Ne.symm hjk) 1
    have hzk : r < ‖z‖ :=
      lt_of_lt_of_le hz (by simpa [Real.norm_eq_abs] using norm_le_pi_norm z k)
    have hzero : ∀ c : ℝ, φ (z + c • Pi.single j (1 : ℝ)) = 0 := fun c => by
      refine apply_eq_zero_of_lt_norm hsupp (lt_of_lt_of_le hz ?_)
      have h := norm_le_pi_norm (z + c • Pi.single j (1 : ℝ)) k
      simpa [Real.norm_eq_abs, hsingle] using h
    have hz0 : φ z = 0 := apply_eq_zero_of_lt_norm hsupp hzk
    have hsd : ∀ t : ℝ, secondDiff φ j z t = 0 := fun t => by
      rw [secondDiff, hz0, show z - t • Pi.single j (1 : ℝ) = z + (-t) • Pi.single j (1 : ℝ) by
        rw [neg_smul, ← sub_eq_add_neg], hzero t, hzero (-t)]
      ring
    simp only [hsd, zero_mul, integral_zero]
  have hFc : ∀ j : Fin 2,
      Continuous fun z : Fin 2 → ℝ => ∫ t : ℝ, secondDiff φ j z t * |t| ^ (-(1 + α)) :=
    fun j => continuous_of_dominated (bound := jumpBound α M₀ M₂)
      (fun z => (integrable_secondDiff_mul_rpow hα hα' hφ2 h₀ h₂ j z).aestronglyMeasurable)
      (fun z => Eventually.of_forall (norm_secondDiff_mul_rpow_le_jumpBound hφ2 h₀ h₂ α j z))
      hjb (Eventually.of_forall fun t =>
        (continuous_secondDiff_left hφc j t).mul continuous_const)
  have hprofile : Integrable fun u : ℝ => C * max |u| (2 * r) ^ (-(1 + α)) :=
    integrable_jumpProfile hα hr C
  have hstrip : Integrable ((Icc (-r) r).indicator fun _ : ℝ => (1 : ℝ)) :=
    (integrable_indicator_iff measurableSet_Icc).2
      (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))
  have hprod : ∀ f g : ℝ → ℝ, Integrable f → Integrable g →
      Integrable fun z : Fin 2 → ℝ => f (z 0) * g (z 1) := by
    intro f g hf hg
    have h : Integrable fun p : ℝ × ℝ => f p.1 * g p.2 := by
      rw [Measure.volume_eq_prod]
      exact hf.mul_prod hg
    exact ((volume_preserving_finTwoArrow ℝ).integrable_comp_emb
      MeasurableEquiv.finTwoArrow.measurableEmbedding).2 h
  have hout : ∀ v : ℝ, v ∉ Icc (-r) r → r < |v| := by
    intro v hv
    rcases lt_or_ge v (-r) with h | h
    · rw [abs_of_neg (by linarith)]
      linarith
    · have h' : r < v := by
        by_contra hc
        exact hv ⟨h, not_lt.1 hc⟩
      rw [abs_of_pos (by linarith)]
      linarith
  have hterm0 : Integrable fun z : Fin 2 → ℝ =>
      ∫ t : ℝ, secondDiff φ 0 z t * |t| ^ (-(1 + α)) := by
    refine Integrable.mono' (hprod _ _ hprofile hstrip) (hFc 0).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    show ‖∫ t : ℝ, secondDiff φ 0 z t * |t| ^ (-(1 + α))‖
      ≤ C * max |z 0| (2 * r) ^ (-(1 + α)) * (Icc (-r) r).indicator (fun _ : ℝ => (1 : ℝ)) (z 1)
    by_cases hz : z 1 ∈ Icc (-r) r
    · rw [indicator_of_mem hz]
      simp only [mul_one]
      rw [Real.norm_eq_abs]
      exact hbd 0 z
    · rw [indicator_of_notMem hz, mul_zero, hvan 0 1 (by decide) z (hout _ hz), norm_zero]
  have hterm1 : Integrable fun z : Fin 2 → ℝ =>
      ∫ t : ℝ, secondDiff φ 1 z t * |t| ^ (-(1 + α)) := by
    refine Integrable.mono' (hprod _ _ hstrip hprofile) (hFc 1).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    show ‖∫ t : ℝ, secondDiff φ 1 z t * |t| ^ (-(1 + α))‖
      ≤ (Icc (-r) r).indicator (fun _ : ℝ => (1 : ℝ)) (z 0) * (C * max |z 1| (2 * r) ^ (-(1 + α)))
    by_cases hz : z 0 ∈ Icc (-r) r
    · rw [indicator_of_mem hz]
      simp only [one_mul]
      rw [Real.norm_eq_abs]
      exact hbd 1 z
    · rw [indicator_of_notMem hz, zero_mul, hvan 1 0 (by decide) z (hout _ hz), norm_zero]
  have hall : ∀ j : Fin 2, Integrable fun z : Fin 2 → ℝ =>
      ∫ t : ℝ, secondDiff φ j z t * |t| ^ (-(1 + α)) := by
    rw [Fin.forall_fin_two]
    exact ⟨hterm0, hterm1⟩
  have hsum : jumpGen α φ
      = fun z : Fin 2 → ℝ => ∑ j : Fin 2, ∫ t : ℝ, secondDiff φ j z t * |t| ^ (-(1 + α)) := rfl
  rw [hsum]
  exact integrable_finsetSum _ fun j _ => hall j

/-! ### Integrability of the potential against the generator -/

/-- **The potential kernel times the generator of a test function is integrable.** Near the origin
the potential is integrable and the generator bounded; away from the origin
`potential z ≤ 1 / (2π ‖z‖)` and `|jumpGen 1 φ z| ≤ 32 r M₀ / ‖z‖²`, so the product decays like
`‖z‖^{-3}` and is dominated by `(1 + ‖z‖)^{-3}`, integrable in the plane. -/
theorem integrable_potential_mul_jumpGen (hφ : IsTestFunction φ) :
    Integrable fun z => potential z * jumpGen 1 φ z := by
  obtain ⟨r, hr, hsupp⟩ := exists_radius_of_isTestFunction hφ
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (by norm_cast)
  obtain ⟨M₀, M₂, h₀, h₂⟩ := exists_bounds_of_hasCompactSupport hφ2 hφ.2
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ 0)
  have hAc : Continuous (jumpGen 1 φ) := continuous_jumpGen one_pos (by norm_num) hφ2 h₀ h₂
  obtain ⟨B, hAb⟩ : ∃ B, ∀ z, |jumpGen 1 φ z| ≤ B :=
    ⟨_, fun z => abs_jumpGen_le one_pos (by norm_num) hφ2 h₀ h₂ z⟩
  have hR1 : (1 : ℝ) ≤ max (2 * r) 1 := le_max_right _ _
  have hR2 : 2 * r ≤ max (2 * r) 1 := le_max_left _ _
  rw [← integrableOn_univ, ← union_compl_self (closedBall (0 : Fin 2 → ℝ) (max (2 * r) 1)),
    integrableOn_union]
  refine ⟨(integrableOn_potential_closedBall _).mul_bdd (c := B) hAc.aestronglyMeasurable
    (Eventually.of_forall fun z => (Real.norm_eq_abs _).trans_le (hAb z)), ?_⟩
  have hg : Integrable fun z : Fin 2 → ℝ => (1 + ‖z‖) ^ (-(3 : ℝ)) :=
    integrable_one_add_norm (E := Fin 2 → ℝ) (μ := volume)
      (by norm_num [Module.finrank_fin_fun])
  refine Integrable.mono' (hg.const_mul (128 * r * M₀ / Real.pi)).integrableOn
    (measurable_potential.mul hAc.measurable).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_closedBall.compl fun z hz => ?_)
  have hznorm : max (2 * r) 1 < ‖z‖ := by
    rw [mem_compl_iff, mem_closedBall, dist_zero_right, not_le] at hz
    exact hz
  have hz1 : (1 : ℝ) < ‖z‖ := lt_of_le_of_lt hR1 hznorm
  have hz2 : 2 * r ≤ ‖z‖ := hR2.trans hznorm.le
  have hp : potential z ≤ 1 / (2 * Real.pi * ‖z‖) := by
    rw [potential]
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left (norm_le_diamondNorm z) (by positivity))
  have h8 : (1 + ‖z‖) ^ 3 ≤ 8 * ‖z‖ ^ 3 := by
    calc (1 + ‖z‖) ^ 3 ≤ (2 * ‖z‖) ^ 3 := by gcongr; linarith
      _ = 8 * ‖z‖ ^ 3 := by ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (potential_nonneg z)]
  calc potential z * |jumpGen 1 φ z|
      ≤ 1 / (2 * Real.pi * ‖z‖) * (32 * r * M₀ / ‖z‖ ^ 2) :=
        mul_le_mul hp (abs_jumpGen_one_le_of_norm_le h₀ hsupp hr hz2) (abs_nonneg _)
          (by positivity)
    _ = 16 * r * M₀ / (Real.pi * ‖z‖ ^ 3) := by
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        have hzn : ‖z‖ ≠ 0 := by positivity
        field_simp
        ring
    _ ≤ 128 * r * M₀ / (Real.pi * (1 + ‖z‖) ^ 3) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        calc 16 * r * M₀ * (Real.pi * (1 + ‖z‖) ^ 3)
            = 16 * r * M₀ * Real.pi * (1 + ‖z‖) ^ 3 := by ring
          _ ≤ 16 * r * M₀ * Real.pi * (8 * ‖z‖ ^ 3) :=
              mul_le_mul_of_nonneg_left h8 (by positivity)
          _ = 128 * r * M₀ * (Real.pi * ‖z‖ ^ 3) := by ring
    _ = 128 * r * M₀ / Real.pi * (1 + ‖z‖) ^ (-(3 : ℝ)) := by
        have hrp : (1 + ‖z‖) ^ (-(3 : ℝ)) = ((1 + ‖z‖) ^ 3)⁻¹ := by
          rw [← Real.rpow_natCast (1 + ‖z‖) 3,
            ← Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖z‖)]
          norm_num
        have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
        have h1 : (1 + ‖z‖) ^ 3 ≠ 0 := by positivity
        rw [hrp]
        field_simp

/-! ### A one-dimensional second-difference bound from the second derivative -/

/-- **A second-difference bound in one variable.** If `f'' ` is bounded by `M` then
`|f (x + s) + f (x − s) − 2 f x| ≤ M s²`: the mean value inequality gives
`|f' (x + u) − f' (x − u)| ≤ 2 M u` for `u ≥ 0`, and the fundamental theorem of calculus applied
to `u ↦ f (x + u) + f (x − u) − 2 f x` on `[0, s]` integrates this to `M s²`. -/
theorem abs_secondDiff_le_sq_of_deriv {f f' f'' : ℝ → ℝ} {M : ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hM : ∀ y, |f'' y| ≤ M) (x s : ℝ) : |f (x + s) + f (x - s) - 2 * f x| ≤ M * s ^ 2 := by
  have hG : ∀ u : ℝ, HasDerivAt (fun u => f (x + u) + f (x - u) - 2 * f x)
      (f' (x + u) - f' (x - u)) u := fun u => by
    have h1 : HasDerivAt (fun u : ℝ => f (x + u)) (f' (x + u)) u :=
      ((hf (x + u)).comp u ((hasDerivAt_id u).const_add x)).congr_deriv (mul_one _)
    have h2 : HasDerivAt (fun u : ℝ => f (x - u)) (-f' (x - u)) u :=
      ((hf (x - u)).comp u ((hasDerivAt_id u).const_sub x)).congr_deriv (by ring)
    exact ((h1.add h2).sub_const (2 * f x)).congr_deriv (by ring)
  have hmv : ∀ u : ℝ, 0 ≤ u → |f' (x + u) - f' (x - u)| ≤ 2 * M * u := fun u hu => by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (s := univ)
      (fun y _ => (hf' y).hasDerivWithinAt) (fun y _ => by simpa [Real.norm_eq_abs] using hM y)
      convex_univ (mem_univ (x - u)) (mem_univ (x + u))
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ x + u - (x - u))] at h
    linarith
  have hf'c : Continuous f' := continuous_iff_continuousAt.2 fun y => (hf' y).continuousAt
  have hcont : Continuous fun u : ℝ => f' (x + u) - f' (x - u) := by fun_prop
  have hzero : f (x + 0) + f (x - 0) - 2 * f x = 0 := by rw [add_zero, sub_zero]; ring
  have key : ∀ s : ℝ, 0 ≤ s → |f (x + s) + f (x - s) - 2 * f x| ≤ M * s ^ 2 := fun s hs => by
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hG u)
      (hcont.intervalIntegrable 0 s)
    have hle : ‖∫ u in (0 : ℝ)..s, (f' (x + u) - f' (x - u))‖
        ≤ ∫ u in (0 : ℝ)..s, 2 * M * u := by
      refine intervalIntegral.norm_integral_le_of_norm_le hs
        (Eventually.of_forall fun u hu => ?_)
        ((by fun_prop : Continuous fun u : ℝ => 2 * M * u).intervalIntegrable 0 s)
      rw [Real.norm_eq_abs]
      exact hmv u (le_of_lt hu.1)
    rw [hftc, hzero, sub_zero, intervalIntegral.integral_const_mul, integral_id,
      Real.norm_eq_abs] at hle
    calc |f (x + s) + f (x - s) - 2 * f x| ≤ 2 * M * ((s ^ 2 - 0 ^ 2) / 2) := hle
      _ = M * s ^ 2 := by ring
  rcases le_or_gt 0 s with hs | hs
  · exact key s hs
  · have h := key (-s) (by linarith)
    rw [show x + -s = x - s by ring, show x - -s = x + s by ring] at h
    calc |f (x + s) + f (x - s) - 2 * f x| = |f (x - s) + f (x + s) - 2 * f x| := by
          rw [add_comm (f (x + s))]
      _ ≤ M * (-s) ^ 2 := h
      _ = M * s ^ 2 := by ring

/-! ### Pointwise bounds on the Cauchy density and its second differences -/

/-- The Cauchy density of scale `t` is bounded by `1 / (π t)`. -/
theorem cauchyDensity_le {t : ℝ} (ht : 0 < t) (x : ℝ) : cauchyDensity t x ≤ 1 / (Real.pi * t) := by
  rw [cauchyDensity, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg Real.pi_pos.le (sq_nonneg x)]

/-- The space derivative of the Cauchy density, `∂_x q_t (x) = −2 t x / (π (t² + x²)²)`. -/
theorem hasDerivAt_cauchyDensity_space {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun y : ℝ => cauchyDensity t y)
      (-(2 * t * x) / (Real.pi * (t ^ 2 + x ^ 2) ^ 2)) x := by
  have hden : (0 : ℝ) < Real.pi * (t ^ 2 + x ^ 2) := by positivity
  have hd : HasDerivAt (fun y : ℝ => Real.pi * (t ^ 2 + y ^ 2)) (Real.pi * (2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_add (t ^ 2)).const_mul Real.pi
  simp only [cauchyDensity]
  refine ((hasDerivAt_const x t).fun_div hd hden.ne').congr_deriv ?_
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h2 : t ^ 2 + x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The second space derivative of the Cauchy density,
`∂²_x q_t (x) = 2 t (3 x² − t²) / (π (t² + x²)³)`. -/
theorem hasDerivAt_cauchyDensity_space_deriv {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -(2 * t * y) / (Real.pi * (t ^ 2 + y ^ 2) ^ 2))
      (2 * t * (3 * x ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + x ^ 2) ^ 3)) x := by
  have hden : (0 : ℝ) < Real.pi * (t ^ 2 + x ^ 2) ^ 2 := by positivity
  have hnum : HasDerivAt (fun y : ℝ => -(2 * t * y)) (-(2 * t)) x :=
    (((hasDerivAt_id x).const_mul (2 * t)).neg).congr_deriv (by ring)
  have h1 : HasDerivAt (fun y : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add (t ^ 2)
  have hd : HasDerivAt (fun y : ℝ => Real.pi * (t ^ 2 + y ^ 2) ^ 2)
      (Real.pi * (2 * (t ^ 2 + x ^ 2) * (2 * x))) x := by
    simpa using (h1.pow 2).const_mul Real.pi
  refine (hnum.fun_div hd hden.ne').congr_deriv ?_
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h2 : t ^ 2 + x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The second space derivative of the Cauchy density is bounded by `6 / (π t³)`, since
`|3 x² − t²| ≤ 3 (t² + x²)` and `t⁴ (t² + x²) ≤ (t² + x²)³`. -/
theorem abs_cauchyDensity_deriv_two_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |2 * t * (3 * x ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + x ^ 2) ^ 3)| ≤ 6 / (Real.pi * t ^ 3) := by
  have hs : (0 : ℝ) < t ^ 2 + x ^ 2 := by positivity
  have habs : |2 * t * (3 * x ^ 2 - t ^ 2)| ≤ 6 * t * (t ^ 2 + x ^ 2) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
    have h : |3 * x ^ 2 - t ^ 2| ≤ 3 * (t ^ 2 + x ^ 2) :=
      abs_le.2 ⟨by nlinarith [sq_nonneg x, sq_nonneg t], by nlinarith [sq_nonneg t]⟩
    nlinarith [mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * t)]
  have h1 : t ^ 4 * (t ^ 2 + x ^ 2) ≤ (t ^ 2 + x ^ 2) ^ 3 := by
    nlinarith [mul_nonneg hs.le (by positivity : (0 : ℝ) ≤ x ^ 4 + 2 * t ^ 2 * x ^ 2)]
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.pi * (t ^ 2 + x ^ 2) ^ 3),
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc |2 * t * (3 * x ^ 2 - t ^ 2)| * (Real.pi * t ^ 3)
      ≤ 6 * t * (t ^ 2 + x ^ 2) * (Real.pi * t ^ 3) :=
        mul_le_mul_of_nonneg_right habs (by positivity)
    _ = 6 * Real.pi * (t ^ 4 * (t ^ 2 + x ^ 2)) := by ring
    _ ≤ 6 * Real.pi * (t ^ 2 + x ^ 2) ^ 3 := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 6 * (Real.pi * (t ^ 2 + x ^ 2) ^ 3) := by ring

/-- The quadratic second-difference bound for the Cauchy density. -/
theorem abs_secondDiff_cauchyDensity_le_sq {t : ℝ} (ht : 0 < t) (x s : ℝ) :
    |cauchyDensity t (x + s) + cauchyDensity t (x - s) - 2 * cauchyDensity t x|
      ≤ 6 / (Real.pi * t ^ 3) * s ^ 2 :=
  abs_secondDiff_le_sq_of_deriv (fun y => hasDerivAt_cauchyDensity_space ht y)
    (fun y => hasDerivAt_cauchyDensity_space_deriv ht y)
    (fun y => abs_cauchyDensity_deriv_two_le ht y) x s

/-- The uniform second-difference bound for the Cauchy density. -/
theorem abs_secondDiff_cauchyDensity_le {t : ℝ} (ht : 0 < t) (x s : ℝ) :
    |cauchyDensity t (x + s) + cauchyDensity t (x - s) - 2 * cauchyDensity t x|
      ≤ 4 * (1 / (Real.pi * t)) := by
  have h1 := cauchyDensity_le ht (x + s)
  have h2 := cauchyDensity_le ht (x - s)
  have h3 := cauchyDensity_le ht x
  have g1 := cauchyDensity_nonneg ht.le (x + s)
  have g2 := cauchyDensity_nonneg ht.le (x - s)
  have g3 := cauchyDensity_nonneg ht.le x
  rw [abs_le]
  constructor <;> linarith

/-! ### Integrability of the semigroup density -/

/-- The semigroup density is integrable on the plane, by the product structure. -/
theorem integrable_heatKernel {t : ℝ} (ht : 0 < t) : Integrable (heatKernel t) := by
  have h : Integrable fun p : ℝ × ℝ => cauchyDensity t p.1 * cauchyDensity t p.2 := by
    rw [Measure.volume_eq_prod]
    exact (integrable_cauchyDensity ht).mul_prod (integrable_cauchyDensity ht)
  exact ((volume_preserving_finTwoArrow ℝ).integrable_comp_emb
    MeasurableEquiv.finTwoArrow.measurableEmbedding).2 h

/-! ### Second differences of the semigroup density -/

/-- The second difference of the product kernel in the first coordinate moves only the first
factor. -/
private theorem secondDiff_heatKernel_fst (t : ℝ) (z : Fin 2 → ℝ) (s : ℝ) :
    secondDiff (heatKernel t) 0 z s
      = (cauchyDensity t (z 0 + s) + cauchyDensity t (z 0 - s) - 2 * cauchyDensity t (z 0))
        * cauchyDensity t (z 1) := by
  simp only [secondDiff, heatKernel, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  norm_num
  ring

/-- The second difference of the product kernel in the second coordinate moves only the second
factor. -/
private theorem secondDiff_heatKernel_snd (t : ℝ) (z : Fin 2 → ℝ) (s : ℝ) :
    secondDiff (heatKernel t) 1 z s
      = cauchyDensity t (z 0)
        * (cauchyDensity t (z 1 + s) + cauchyDensity t (z 1 - s) - 2 * cauchyDensity t (z 1)) := by
  simp only [secondDiff, heatKernel, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  norm_num
  ring

/-- The second difference of the semigroup density is dominated by
`min (M₂ s², 4 M₀) M₀` with `M₀ = 1 / (π t)` and `M₂ = 6 / (π t³)`: the moved factor obeys the
one-dimensional bounds and the untouched factor is at most `M₀`. -/
theorem abs_secondDiff_heatKernel_le {t : ℝ} (ht : 0 < t) (j : Fin 2) (z : Fin 2 → ℝ) (s : ℝ) :
    |secondDiff (heatKernel t) j z s|
      ≤ min (6 / (Real.pi * t ^ 3) * s ^ 2) (4 * (1 / (Real.pi * t))) * (1 / (Real.pi * t)) := by
  have hq0 : ∀ y, 0 ≤ cauchyDensity t y := fun y => cauchyDensity_nonneg ht.le y
  have hq1 : ∀ y, cauchyDensity t y ≤ 1 / (Real.pi * t) := fun y => cauchyDensity_le ht y
  have hsd : ∀ y, |cauchyDensity t (y + s) + cauchyDensity t (y - s) - 2 * cauchyDensity t y|
      ≤ min (6 / (Real.pi * t ^ 3) * s ^ 2) (4 * (1 / (Real.pi * t))) := fun y =>
    le_min (abs_secondDiff_cauchyDensity_le_sq ht y s) (abs_secondDiff_cauchyDensity_le ht y s)
  have hmn : (0 : ℝ) ≤ min (6 / (Real.pi * t ^ 3) * s ^ 2) (4 * (1 / (Real.pi * t))) :=
    le_min (by positivity) (by positivity)
  revert j
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [secondDiff_heatKernel_fst, abs_mul, abs_of_nonneg (hq0 (z 1))]
    exact mul_le_mul (hsd (z 0)) (hq1 (z 1)) (hq0 (z 1)) hmn
  · rw [secondDiff_heatKernel_snd, abs_mul, abs_of_nonneg (hq0 (z 0))]
    calc cauchyDensity t (z 0)
          * |cauchyDensity t (z 1 + s) + cauchyDensity t (z 1 - s) - 2 * cauchyDensity t (z 1)|
        ≤ 1 / (Real.pi * t)
          * min (6 / (Real.pi * t ^ 3) * s ^ 2) (4 * (1 / (Real.pi * t))) :=
          mul_le_mul (hq1 (z 0)) (hsd (z 1)) (abs_nonneg _) (by positivity)
      _ = min (6 / (Real.pi * t ^ 3) * s ^ 2) (4 * (1 / (Real.pi * t))) * (1 / (Real.pi * t)) :=
          mul_comm _ _

/-! ### Self-adjointness of the generator against the semigroup density -/

/-- Moving a translation from one factor of a product integral to the other. -/
private theorem integral_mul_comp_add (p ψ : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) :
    ∫ z, p z * ψ (z + a) = ∫ z, p (z - a) * ψ z := by
  have h := integral_add_right_eq_self (μ := (volume : Measure (Fin 2 → ℝ)))
    (fun z : Fin 2 → ℝ => p (z - a) * ψ z) a
  simpa using h

/-- Moving a translation from one factor of a product integral to the other. -/
private theorem integral_mul_comp_sub (p ψ : (Fin 2 → ℝ) → ℝ) (a : Fin 2 → ℝ) :
    ∫ z, p z * ψ (z - a) = ∫ z, p (z + a) * ψ z := by
  have h := integral_mul_comp_add p ψ (-a)
  simpa [sub_eq_add_neg] using h

/-- **Self-adjointness of the coordinate jump generator.** Pairing the semigroup density against
the generator of a test function is the same as pairing the generator of the semigroup density
against the test function. Expand the generator coordinate by coordinate, exchange the `z`- and
`s`-integrals (the double integral is dominated by `p_t(z) · jumpBound s`), translate
`z ↦ z ∓ s e_j` in the two outer terms of the second difference, and exchange back (now dominated by
`M₀ · jumpBound s · |φ z|`). -/
theorem integral_heatKernel_mul_jumpGen {t : ℝ} (ht : 0 < t) (hφ : IsTestFunction φ) :
    ∫ z, heatKernel t z * jumpGen 1 φ z = ∫ z, jumpGen 1 (heatKernel t) z * φ z := by
  have hφc : Continuous φ := hφ.continuous
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (by norm_cast)
  obtain ⟨N₀, N₂, hN₀, hN₂⟩ := exists_bounds_of_hasCompactSupport hφ2 hφ.2
  have hN₀' : 0 ≤ N₀ := (abs_nonneg _).trans (hN₀ 0)
  have hN₂' : 0 ≤ N₂ := (norm_nonneg _).trans (hN₂ 0)
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφ.2
  have hpi : Integrable (heatKernel t) := integrable_heatKernel ht
  have hpc : Continuous (heatKernel t) := continuous_heatKernel ht
  obtain ⟨M₀, M₂, hM₀, hM₂, hpsd⟩ :
      ∃ M₀ M₂ : ℝ, 0 ≤ M₀ ∧ 0 ≤ M₂ ∧ ∀ (j : Fin 2) (z : Fin 2 → ℝ) (s : ℝ),
        |secondDiff (heatKernel t) j z s| ≤ min (M₂ * s ^ 2) (4 * M₀) * M₀ :=
    ⟨1 / (Real.pi * t), 6 / (Real.pi * t ^ 3), by positivity, by positivity,
      fun j z s => abs_secondDiff_heatKernel_le ht j z s⟩
  have hwm : Measurable fun s : ℝ => |s| ^ (-(1 + (1 : ℝ))) :=
    continuous_abs.measurable.pow_const _
  have hjb : Integrable (jumpBound 1 N₀ N₂) := integrable_jumpBound one_pos (by norm_num) hN₀' hN₂'
  have hjb' : Integrable (jumpBound 1 M₀ M₂) := integrable_jumpBound one_pos (by norm_num) hM₀ hM₂
  have hpdom : ∀ (j : Fin 2) (z : Fin 2 → ℝ) (s : ℝ),
      ‖secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ)))‖ ≤ M₀ * jumpBound 1 M₀ M₂ s := by
    intro j z s
    have hw : (0 : ℝ) ≤ |s| ^ (-(1 + (1 : ℝ))) := Real.rpow_nonneg (abs_nonneg s) _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    simp only [jumpBound]
    calc |secondDiff (heatKernel t) j z s| * |s| ^ (-(1 + (1 : ℝ)))
        ≤ min (M₂ * s ^ 2) (4 * M₀) * M₀ * |s| ^ (-(1 + (1 : ℝ))) :=
          mul_le_mul_of_nonneg_right (hpsd j z s) hw
      _ = M₀ * (min (M₂ * s ^ 2) (4 * M₀) * |s| ^ (-(1 + (1 : ℝ)))) := by ring
  -- continuity and boundedness of the coordinate terms of the two generators
  have hJφc : ∀ j : Fin 2,
      Continuous fun z : Fin 2 → ℝ => ∫ s : ℝ, secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ))) :=
    fun j => continuous_of_dominated (bound := jumpBound 1 N₀ N₂)
      (fun z => (integrable_secondDiff_mul_rpow one_pos (by norm_num) hφ2 hN₀ hN₂ j
        z).aestronglyMeasurable)
      (fun z => Eventually.of_forall (norm_secondDiff_mul_rpow_le_jumpBound hφ2 hN₀ hN₂ 1 j z))
      hjb (Eventually.of_forall fun s => (continuous_secondDiff_left hφc j s).mul continuous_const)
  have hJpc : ∀ j : Fin 2, Continuous fun z : Fin 2 → ℝ =>
      ∫ s : ℝ, secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ))) :=
    fun j => continuous_of_dominated (bound := fun s => M₀ * jumpBound 1 M₀ M₂ s)
      (fun z => ((continuous_secondDiff hpc j z).measurable.mul hwm).aestronglyMeasurable)
      (fun z => Eventually.of_forall (hpdom j z)) (hjb'.const_mul M₀)
      (Eventually.of_forall fun s => (continuous_secondDiff_left hpc j s).mul continuous_const)
  have hJφb : ∀ (j : Fin 2) (z : Fin 2 → ℝ),
      ‖∫ s : ℝ, secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ)))‖ ≤ ∫ s, jumpBound 1 N₀ N₂ s :=
    fun j z => norm_integral_le_of_norm_le hjb
      (Eventually.of_forall (norm_secondDiff_mul_rpow_le_jumpBound hφ2 hN₀ hN₂ 1 j z))
  have hJpb : ∀ (j : Fin 2) (z : Fin 2 → ℝ),
      ‖∫ s : ℝ, secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ)))‖
        ≤ ∫ s, M₀ * jumpBound 1 M₀ M₂ s :=
    fun j z => norm_integral_le_of_norm_le (hjb'.const_mul M₀)
      (Eventually.of_forall (hpdom j z))
  have hIφ : ∀ j : Fin 2, Integrable fun z : Fin 2 → ℝ =>
      heatKernel t z * ∫ s : ℝ, secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ))) := fun j =>
    hpi.mul_bdd (hJφc j).aestronglyMeasurable (Eventually.of_forall (hJφb j))
  have hIp : ∀ j : Fin 2, Integrable fun z : Fin 2 → ℝ =>
      (∫ s : ℝ, secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ)))) * φ z := fun j =>
    hφi.bdd_mul (hJpc j).aestronglyMeasurable (Eventually.of_forall (hJpb j))
  -- the coordinate identity
  have hkey : ∀ j : Fin 2,
      (∫ z, heatKernel t z * ∫ s : ℝ, secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ))))
        = ∫ z, (∫ s : ℝ, secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ)))) * φ z := by
    intro j
    have hm1 : Measurable (Function.uncurry fun (z : Fin 2 → ℝ) (s : ℝ) =>
        heatKernel t z * (secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ))))) := by
      have hsd : Continuous fun q : (Fin 2 → ℝ) × ℝ => secondDiff φ j q.1 q.2 := by
        unfold secondDiff
        fun_prop
      exact (hpc.comp continuous_fst).measurable.mul
        (hsd.measurable.mul (hwm.comp measurable_snd))
    have hint1 : Integrable (Function.uncurry fun (z : Fin 2 → ℝ) (s : ℝ) =>
        heatKernel t z * (secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ)))))
        (volume.prod volume) := by
      refine Integrable.mono' (hpi.mul_prod hjb) hm1.aestronglyMeasurable
        (Eventually.of_forall fun q => ?_)
      show ‖heatKernel t q.1 * (secondDiff φ j q.1 q.2 * |q.2| ^ (-(1 + (1 : ℝ))))‖
        ≤ heatKernel t q.1 * jumpBound 1 N₀ N₂ q.2
      have h := norm_secondDiff_mul_rpow_le_jumpBound hφ2 hN₀ hN₂ 1 j q.1 q.2
      rw [Real.norm_eq_abs] at h ⊢
      rw [abs_mul, abs_of_nonneg (heatKernel_nonneg ht.le q.1)]
      exact mul_le_mul_of_nonneg_left h (heatKernel_nonneg ht.le q.1)
    have hm2 : Measurable (Function.uncurry fun (s : ℝ) (z : Fin 2 → ℝ) =>
        secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ))) * φ z) := by
      have hsd : Continuous fun q : ℝ × (Fin 2 → ℝ) => secondDiff (heatKernel t) j q.2 q.1 := by
        unfold secondDiff
        fun_prop
      exact (hsd.measurable.mul (hwm.comp measurable_fst)).mul
        (hφc.comp continuous_snd).measurable
    have hint2 : Integrable (Function.uncurry fun (s : ℝ) (z : Fin 2 → ℝ) =>
        secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ))) * φ z)
        (volume.prod volume) := by
      refine Integrable.mono' ((hjb'.const_mul M₀).mul_prod hφi.abs) hm2.aestronglyMeasurable
        (Eventually.of_forall fun q => ?_)
      show ‖secondDiff (heatKernel t) j q.2 q.1 * |q.1| ^ (-(1 + (1 : ℝ))) * φ q.2‖
        ≤ M₀ * jumpBound 1 M₀ M₂ q.1 * |φ q.2|
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      have h := hpdom j q.2 q.1
      rwa [Real.norm_eq_abs] at h
    -- the fixed-step translation identity
    have hfix : ∀ s : ℝ,
        (∫ z, heatKernel t z * (secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ)))))
          = ∫ z, secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ))) * φ z := by
      intro s
      obtain ⟨a, ha⟩ : ∃ a : Fin 2 → ℝ, a = s • Pi.single j (1 : ℝ) := ⟨_, rfl⟩
      have hbd : ∀ᵐ z : Fin 2 → ℝ, ‖φ z‖ ≤ N₀ :=
        Eventually.of_forall fun z => (Real.norm_eq_abs _).trans_le (hN₀ z)
      have hA : Integrable fun z : Fin 2 → ℝ => heatKernel t z * φ (z + a) :=
        hpi.mul_bdd (c := N₀) ((hφc.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
          (Eventually.of_forall fun z => (Real.norm_eq_abs _).trans_le (hN₀ _))
      have hB : Integrable fun z : Fin 2 → ℝ => heatKernel t z * φ (z - a) :=
        hpi.mul_bdd (c := N₀) ((hφc.comp (continuous_id.sub continuous_const)).aestronglyMeasurable)
          (Eventually.of_forall fun z => (Real.norm_eq_abs _).trans_le (hN₀ _))
      have hC : Integrable fun z : Fin 2 → ℝ => heatKernel t z * φ z :=
        hpi.mul_bdd (c := N₀) hφc.aestronglyMeasurable hbd
      have hA' : Integrable fun z : Fin 2 → ℝ => heatKernel t (z + a) * φ z :=
        (hpi.comp_add_right a).mul_bdd (c := N₀) hφc.aestronglyMeasurable hbd
      have hB' : Integrable fun z : Fin 2 → ℝ => heatKernel t (z - a) * φ z :=
        (hpi.comp_sub_right a).mul_bdd (c := N₀) hφc.aestronglyMeasurable hbd
      have hAB : Integrable fun z : Fin 2 → ℝ =>
          heatKernel t z * φ (z + a) + heatKernel t z * φ (z - a) := hA.add hB
      have hAB' : Integrable fun z : Fin 2 → ℝ =>
          heatKernel t (z + a) * φ z + heatKernel t (z - a) * φ z := hA'.add hB'
      have hsdφ : ∀ z : Fin 2 → ℝ, secondDiff φ j z s
          = φ (z + a) + φ (z - a) - 2 * φ z := fun z => by rw [ha]; rfl
      have hsdp : ∀ z : Fin 2 → ℝ, secondDiff (heatKernel t) j z s
          = heatKernel t (z + a) + heatKernel t (z - a) - 2 * heatKernel t z := fun z => by
        rw [ha]; rfl
      have h1 : (∫ z, heatKernel t z * secondDiff φ j z s)
          = (∫ z, heatKernel t (z - a) * φ z) + (∫ z, heatKernel t (z + a) * φ z)
            - 2 * ∫ z, heatKernel t z * φ z := by
        calc (∫ z, heatKernel t z * secondDiff φ j z s)
            = ∫ z, (heatKernel t z * φ (z + a) + heatKernel t z * φ (z - a)
                - 2 * (heatKernel t z * φ z)) :=
              integral_congr_ae (Eventually.of_forall fun z => by
                show heatKernel t z * secondDiff φ j z s
                  = heatKernel t z * φ (z + a) + heatKernel t z * φ (z - a)
                    - 2 * (heatKernel t z * φ z)
                rw [hsdφ z]; ring)
          _ = (∫ z, (heatKernel t z * φ (z + a) + heatKernel t z * φ (z - a)))
                - ∫ z, 2 * (heatKernel t z * φ z) := integral_sub hAB (hC.const_mul 2)
          _ = ((∫ z, heatKernel t z * φ (z + a)) + ∫ z, heatKernel t z * φ (z - a))
                - 2 * ∫ z, heatKernel t z * φ z := by
              rw [integral_add hA hB, integral_const_mul]
          _ = (∫ z, heatKernel t (z - a) * φ z) + (∫ z, heatKernel t (z + a) * φ z)
                - 2 * ∫ z, heatKernel t z * φ z := by
              rw [integral_mul_comp_add (heatKernel t) φ a,
                integral_mul_comp_sub (heatKernel t) φ a]
      have h2 : (∫ z, secondDiff (heatKernel t) j z s * φ z)
          = (∫ z, heatKernel t (z + a) * φ z) + (∫ z, heatKernel t (z - a) * φ z)
            - 2 * ∫ z, heatKernel t z * φ z := by
        calc (∫ z, secondDiff (heatKernel t) j z s * φ z)
            = ∫ z, (heatKernel t (z + a) * φ z + heatKernel t (z - a) * φ z
                - 2 * (heatKernel t z * φ z)) :=
              integral_congr_ae (Eventually.of_forall fun z => by
                show secondDiff (heatKernel t) j z s * φ z
                  = heatKernel t (z + a) * φ z + heatKernel t (z - a) * φ z
                    - 2 * (heatKernel t z * φ z)
                rw [hsdp z]; ring)
          _ = (∫ z, (heatKernel t (z + a) * φ z + heatKernel t (z - a) * φ z))
                - ∫ z, 2 * (heatKernel t z * φ z) := integral_sub hAB' (hC.const_mul 2)
          _ = ((∫ z, heatKernel t (z + a) * φ z) + ∫ z, heatKernel t (z - a) * φ z)
                - 2 * ∫ z, heatKernel t z * φ z := by
              rw [integral_add hA' hB', integral_const_mul]
      calc (∫ z, heatKernel t z * (secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ)))))
          = ∫ z, |s| ^ (-(1 + (1 : ℝ))) * (heatKernel t z * secondDiff φ j z s) :=
            integral_congr_ae (Eventually.of_forall fun z => by ring)
        _ = |s| ^ (-(1 + (1 : ℝ))) * ∫ z, heatKernel t z * secondDiff φ j z s :=
            integral_const_mul _ _
        _ = |s| ^ (-(1 + (1 : ℝ))) * ∫ z, secondDiff (heatKernel t) j z s * φ z := by
            rw [h1, h2]; ring
        _ = ∫ z, |s| ^ (-(1 + (1 : ℝ))) * (secondDiff (heatKernel t) j z s * φ z) :=
            (integral_const_mul _ _).symm
        _ = ∫ z, secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ))) * φ z :=
            integral_congr_ae (Eventually.of_forall fun z => by ring)
    calc (∫ z, heatKernel t z * ∫ s : ℝ, secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ))))
        = ∫ z, ∫ s : ℝ, heatKernel t z * (secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ)))) :=
          integral_congr_ae (Eventually.of_forall fun z => (integral_const_mul _ _).symm)
      _ = ∫ s : ℝ, ∫ z, heatKernel t z * (secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ)))) :=
          integral_integral_swap hint1
      _ = ∫ s : ℝ, ∫ z, secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ))) * φ z :=
          integral_congr_ae (Eventually.of_forall hfix)
      _ = ∫ z, ∫ s : ℝ, secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ))) * φ z :=
          integral_integral_swap hint2
      _ = ∫ z, (∫ s : ℝ, secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ)))) * φ z :=
          integral_congr_ae (Eventually.of_forall fun z => integral_mul_const _ _)
  have hL : (∫ z, heatKernel t z * jumpGen 1 φ z)
      = ∑ j : Fin 2, ∫ z, heatKernel t z * ∫ s : ℝ,
          secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ))) := by
    rw [← integral_finsetSum _ fun j _ => hIφ j]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show heatKernel t z * (∑ j : Fin 2, ∫ s : ℝ, secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ))))
      = ∑ j : Fin 2, heatKernel t z * ∫ s : ℝ, secondDiff φ j z s * |s| ^ (-(1 + (1 : ℝ)))
    rw [Finset.mul_sum]
  have hR : (∫ z, jumpGen 1 (heatKernel t) z * φ z)
      = ∑ j : Fin 2, ∫ z, (∫ s : ℝ,
          secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ)))) * φ z := by
    rw [← integral_finsetSum _ fun j _ => hIp j]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show (∑ j : Fin 2, ∫ s : ℝ,
        secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ)))) * φ z
      = ∑ j : Fin 2, (∫ s : ℝ, secondDiff (heatKernel t) j z s * |s| ^ (-(1 + (1 : ℝ)))) * φ z
    rw [Finset.sum_mul]
  rw [hL, hR]
  exact Finset.sum_congr rfl fun j _ => hkey j

/-! ### The time derivative and the two boundary limits of the semigroup pairing -/

/-- The time derivative of the one-dimensional Cauchy density is bounded by `1 / (π t²)`. -/
private theorem abs_cauchyDensity_time_deriv_le {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |(x ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + x ^ 2) ^ 2)| ≤ 1 / (Real.pi * t ^ 2) := by
  have hs : (0 : ℝ) < t ^ 2 + x ^ 2 := by positivity
  have habs : |x ^ 2 - t ^ 2| ≤ t ^ 2 + x ^ 2 :=
    abs_le.2 ⟨by nlinarith [sq_nonneg x, sq_nonneg t], by nlinarith [sq_nonneg t]⟩
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.pi * (t ^ 2 + x ^ 2) ^ 2),
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc |x ^ 2 - t ^ 2| * (Real.pi * t ^ 2) ≤ (t ^ 2 + x ^ 2) * (Real.pi * t ^ 2) :=
        mul_le_mul_of_nonneg_right habs (by positivity)
    _ ≤ 1 * (Real.pi * (t ^ 2 + x ^ 2) ^ 2) := by
        rw [one_mul]
        nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hs.le) (sq_nonneg x)]

/-- The time derivative of the semigroup density is bounded by `2 / (π² t³)`. -/
private theorem abs_deriv_heatKernel_le {t : ℝ} (ht : 0 < t) (z : Fin 2 → ℝ) :
    |(z 0 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 0 ^ 2) ^ 2) * cauchyDensity t (z 1)
      + cauchyDensity t (z 0) * ((z 1 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 1 ^ 2) ^ 2))|
      ≤ 2 / (Real.pi ^ 2 * t ^ 3) := by
  have h1 := abs_cauchyDensity_time_deriv_le ht (z 0)
  have h2 := abs_cauchyDensity_time_deriv_le ht (z 1)
  have g1 : |cauchyDensity t (z 1)| ≤ 1 / (Real.pi * t) := by
    rw [abs_of_nonneg (cauchyDensity_nonneg ht.le _)]
    exact cauchyDensity_le ht _
  have g2 : |cauchyDensity t (z 0)| ≤ 1 / (Real.pi * t) := by
    rw [abs_of_nonneg (cauchyDensity_nonneg ht.le _)]
    exact cauchyDensity_le ht _
  have heq : 1 / (Real.pi * t ^ 2) * (1 / (Real.pi * t))
      + 1 / (Real.pi * t) * (1 / (Real.pi * t ^ 2)) = 2 / (Real.pi ^ 2 * t ^ 3) := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have ht' : t ≠ 0 := ht.ne'
    field_simp
    ring
  calc |(z 0 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 0 ^ 2) ^ 2) * cauchyDensity t (z 1)
        + cauchyDensity t (z 0) * ((z 1 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 1 ^ 2) ^ 2))|
      ≤ |(z 0 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 0 ^ 2) ^ 2) * cauchyDensity t (z 1)|
        + |cauchyDensity t (z 0) * ((z 1 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 1 ^ 2) ^ 2))| :=
        abs_add_le _ _
    _ ≤ 1 / (Real.pi * t ^ 2) * (1 / (Real.pi * t))
          + 1 / (Real.pi * t) * (1 / (Real.pi * t ^ 2)) := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul h1 g1 (abs_nonneg _) (by positivity))
          (mul_le_mul g2 h2 (abs_nonneg _) (by positivity))
    _ = 2 / (Real.pi ^ 2 * t ^ 3) := heq

/-- **Differentiation under the integral sign** for the semigroup pairing: the time derivative of
`t ↦ ∫ p_t φ` is `∫ (∂_t p_t) φ`. On the ball `|u − t| < t/2` the time derivative of `p_u` is
bounded by `2 / (π² (t/2)³)` uniformly, so `|φ|` times that constant dominates. -/
theorem hasDerivAt_integral_heatKernel_mul (hφ : IsTestFunction φ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => ∫ z, heatKernel t z * φ z)
      (∫ z, deriv (fun t => heatKernel t z) t * φ z) t := by
  have hφc : Continuous φ := hφ.continuous
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφ.2
  obtain ⟨N₀, N₂, hN₀, hN₂⟩ :=
    exists_bounds_of_hasCompactSupport (hφ.1.of_le (by norm_cast)) hφ.2
  have hpos : ∀ u ∈ ball t (t / 2), 0 < u := by
    intro u hu
    rw [mem_ball, Real.dist_eq, abs_lt] at hu
    linarith [hu.1]
  have hmul : ∀ u : ℝ, 0 < u → Integrable fun z : Fin 2 → ℝ => heatKernel u z * φ z := fun u hu =>
    (integrable_heatKernel hu).mul_bdd (c := N₀) hφc.aestronglyMeasurable
      (Eventually.of_forall fun z => (Real.norm_eq_abs _).trans_le (hN₀ z))
  have hcontD : Continuous fun z : Fin 2 → ℝ =>
      (z 0 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 0 ^ 2) ^ 2) * cauchyDensity t (z 1)
        + cauchyDensity t (z 0) * ((z 1 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 1 ^ 2) ^ 2)) := by
    have hq : Continuous (cauchyDensity t) := continuous_cauchyDensity ht
    have h0 : Continuous fun z : Fin 2 → ℝ =>
        (z 0 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 0 ^ 2) ^ 2) :=
      Continuous.div (by fun_prop) (by fun_prop) fun z => by positivity
    have h1 : Continuous fun z : Fin 2 → ℝ =>
        (z 1 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 1 ^ 2) ^ 2) :=
      Continuous.div (by fun_prop) (by fun_prop) fun z => by positivity
    exact (h0.mul (hq.comp (continuous_apply 1))).add ((hq.comp (continuous_apply 0)).mul h1)
  have hF'meas : AEStronglyMeasurable
      (fun z : Fin 2 → ℝ => deriv (fun v => heatKernel v z) t * φ z) volume := by
    have he : (fun z : Fin 2 → ℝ => deriv (fun v => heatKernel v z) t * φ z)
        = fun z : Fin 2 → ℝ =>
          ((z 0 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 0 ^ 2) ^ 2) * cauchyDensity t (z 1)
            + cauchyDensity t (z 0)
              * ((z 1 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 1 ^ 2) ^ 2))) * φ z := by
      funext z
      rw [(hasDerivAt_heatKernel z ht).deriv]
    rw [he]
    exact (hcontD.mul hφc).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := ball t (t / 2)) (F := fun u z => heatKernel u z * φ z)
    (F' := fun u z => deriv (fun v => heatKernel v z) u * φ z)
    (bound := fun z => 2 / (Real.pi ^ 2 * (t / 2) ^ 3) * |φ z|)
    (ball_mem_nhds t (by positivity))
    (eventually_of_mem (ball_mem_nhds t (by positivity)) fun u hu =>
      ((continuous_heatKernel (hpos u hu)).mul hφc).aestronglyMeasurable)
    (hmul t ht) hF'meas (Eventually.of_forall fun z u hu => ?_)
    (hφi.abs.const_mul _) (Eventually.of_forall fun z u hu => ?_)).2
  · have hu' : 0 < u := hpos u hu
    have hu2 : t / 2 ≤ u := by
      rw [mem_ball, Real.dist_eq, abs_lt] at hu
      linarith [hu.1]
    have h3 : (t / 2) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by positivity) hu2 3
    have hle : 2 / (Real.pi ^ 2 * u ^ 3) ≤ 2 / (Real.pi ^ 2 * (t / 2) ^ 3) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 2 * Real.pi ^ 2)]
    rw [(hasDerivAt_heatKernel z hu').deriv, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((abs_deriv_heatKernel_le hu' z).trans hle) le_rfl (abs_nonneg _)
      (by positivity)
  · rw [(hasDerivAt_heatKernel z (hpos u hu)).deriv]
    exact (hasDerivAt_heatKernel z (hpos u hu)).mul_const (φ z)

/-- The semigroup pairing tends to `0` at infinite time, since `p_t ≤ (π t)^{-2}`. -/
theorem tendsto_integral_heatKernel_mul_atTop (hφ : IsTestFunction φ) :
    Tendsto (fun t => ∫ z, heatKernel t z * φ z) atTop (𝓝 0) := by
  have hφc : Continuous φ := hφ.continuous
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφ.2
  have hπ : Tendsto (fun t : ℝ => Real.pi * t) atTop atTop :=
    Filter.Tendsto.const_mul_atTop Real.pi_pos tendsto_id
  have h1 : Tendsto (fun t : ℝ => (Real.pi * t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hπ
  have h2 : Tendsto (fun t : ℝ => (Real.pi * t)⁻¹ ^ 2 * ∫ z, |φ z|) atTop (𝓝 0) := by
    simpa using (h1.pow 2).mul_const (∫ z, |φ z|)
  refine squeeze_zero_norm' ?_ h2
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have hb : ∀ z : Fin 2 → ℝ, ‖heatKernel t z * φ z‖ ≤ (Real.pi * t)⁻¹ ^ 2 * |φ z| := by
    intro z
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg ht.le z)]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    rw [heatKernel, show (Real.pi * t)⁻¹ ^ 2 = 1 / (Real.pi * t) * (1 / (Real.pi * t)) by
      rw [one_div]; ring]
    exact mul_le_mul (cauchyDensity_le ht _) (cauchyDensity_le ht _)
      (cauchyDensity_nonneg ht.le _) (by positivity)
  calc ‖∫ z, heatKernel t z * φ z‖ ≤ ∫ z, (Real.pi * t)⁻¹ ^ 2 * |φ z| :=
        norm_integral_le_of_norm_le (hφi.abs.const_mul _) (Eventually.of_forall hb)
    _ = (Real.pi * t)⁻¹ ^ 2 * ∫ z, |φ z| := integral_const_mul _ _

/-- The scaling law of the semigroup pairing: `∫ p_t φ = ∫ p_1(w) φ (t w) dw` for `t > 0`. -/
private theorem integral_heatKernel_mul_eq_scaled {t : ℝ} (ht : 0 < t) (φ : (Fin 2 → ℝ) → ℝ) :
    (∫ z, heatKernel t z * φ z) = ∫ w, heatKernel 1 w * φ (t • w) := by
  have ht' : t ≠ 0 := ht.ne'
  have hk : ∀ w : Fin 2 → ℝ, heatKernel t (t • w) = (t ^ 2)⁻¹ * heatKernel 1 w := by
    intro w
    have h0 : ∀ u : ℝ, cauchyDensity t (t * u) = t⁻¹ * cauchyDensity 1 u := by
      intro u
      have h2 : (1 : ℝ) + u ^ 2 ≠ 0 := by positivity
      have h3 : t ^ 2 + (t * u) ^ 2 ≠ 0 := by positivity
      rw [cauchyDensity, cauchyDensity]
      field_simp
    simp only [heatKernel, Pi.smul_apply, smul_eq_mul, h0]
    field_simp
  have hcs := Measure.integral_comp_smul (volume : Measure (Fin 2 → ℝ))
    (fun z => heatKernel t z * φ z) t
  rw [Module.finrank_fin_fun] at hcs
  have hL : (∫ w, heatKernel t (t • w) * φ (t • w))
      = (t ^ 2)⁻¹ * ∫ w, heatKernel 1 w * φ (t • w) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    show heatKernel t (t • w) * φ (t • w) = (t ^ 2)⁻¹ * (heatKernel 1 w * φ (t • w))
    rw [hk w]
    ring
  rw [hL, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (t ^ 2)⁻¹), smul_eq_mul] at hcs
  exact (mul_left_cancel₀ (by positivity : ((t : ℝ) ^ 2)⁻¹ ≠ 0) hcs).symm

/-- The semigroup pairing tends to `φ 0` as the time goes to `0⁺`: after the scaling `z = t w` the
pairing is `∫ p_1(w) φ (t w) dw`, `p_1` is a probability density, and dominated convergence with
the dominating function `p_1 · M₀` applies. -/
theorem tendsto_integral_heatKernel_mul_zero (hφ : IsTestFunction φ) :
    Tendsto (fun t => ∫ z, heatKernel t z * φ z) (𝓝[>] 0) (𝓝 (φ 0)) := by
  have hφc : Continuous φ := hφ.continuous
  obtain ⟨N₀, N₂, hN₀, hN₂⟩ :=
    exists_bounds_of_hasCompactSupport (hφ.1.of_le (by norm_cast)) hφ.2
  have hp1 : Integrable (heatKernel 1) := integrable_heatKernel one_pos
  have hlim : Tendsto (fun t : ℝ => ∫ w, heatKernel 1 w * φ (t • w)) (𝓝[>] 0)
      (𝓝 (∫ w, heatKernel 1 w * φ 0)) := by
    have hmeas : ∀ u : ℝ,
        AEStronglyMeasurable (fun w : Fin 2 → ℝ => heatKernel 1 w * φ (u • w)) volume := fun u =>
      ((continuous_heatKernel one_pos).mul
        (hφc.comp (continuous_const_smul u))).aestronglyMeasurable
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun w => heatKernel 1 w * N₀) (Eventually.of_forall hmeas)
      (Eventually.of_forall fun u => Eventually.of_forall fun w => ?_)
      (hp1.mul_const N₀) (Eventually.of_forall fun w => ?_)
    · show ‖heatKernel 1 w * φ (u • w)‖ ≤ heatKernel 1 w * N₀
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg one_pos.le w)]
      exact mul_le_mul_of_nonneg_left (hN₀ _) (heatKernel_nonneg one_pos.le w)
    · show Tendsto (fun u : ℝ => heatKernel 1 w * φ (u • w)) (𝓝[>] (0 : ℝ))
        (𝓝 (heatKernel 1 w * φ 0))
      have hs : Tendsto (fun u : ℝ => u • w) (𝓝[>] (0 : ℝ)) (𝓝 (0 : Fin 2 → ℝ)) := by
        have hc : Continuous fun u : ℝ => u • w := continuous_id.smul continuous_const
        simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
      exact Tendsto.const_mul _ ((hφc.tendsto (0 : Fin 2 → ℝ)).comp hs)
  have hval : (∫ w, heatKernel 1 w * φ 0) = φ 0 := by
    rw [integral_mul_const, integral_heatKernel one_pos, one_mul]
  rw [← hval]
  refine Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (integral_heatKernel_mul_eq_scaled ht φ).symm

/-! ### The potential kernel is the fundamental solution -/

/-- The semigroup density is integrable in time away from the origin: with `b` a nonzero
coordinate of `z`, `p_t(z) ≤ (π²)⁻¹ (t² + b²)⁻¹`, which is integrable on `(0, ∞)`. -/
theorem integrableOn_Ioi_heatKernel {z : Fin 2 → ℝ} (hz : z ≠ 0) :
    IntegrableOn (fun t => heatKernel t z) (Ioi 0) := by
  have key : ∀ b c : ℝ, b ≠ 0 →
      IntegrableOn (fun t : ℝ => cauchyDensity t b * cauchyDensity t c) (Ioi 0) := by
    intro b c hb
    have hm : Measurable fun t : ℝ => cauchyDensity t b * cauchyDensity t c := by
      unfold cauchyDensity
      fun_prop
    refine ((integrableOn_Ioi_one_div_sq_add_sq (abs_pos.2 hb)).const_mul
      ((Real.pi ^ 2)⁻¹)).mono' hm.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (cauchyDensity_nonneg ht0.le _)
      (cauchyDensity_nonneg ht0.le _)), sq_abs, cauchyDensity, cauchyDensity]
    have hb2 : (0 : ℝ) < t ^ 2 + b ^ 2 := by positivity
    have h1 : t / (Real.pi * (t ^ 2 + b ^ 2)) * (t / (Real.pi * (t ^ 2 + c ^ 2)))
        = t ^ 2 / (Real.pi ^ 2 * ((t ^ 2 + b ^ 2) * (t ^ 2 + c ^ 2))) := by
      have e1 : Real.pi ≠ 0 := Real.pi_ne_zero
      have e2 : t ^ 2 + b ^ 2 ≠ 0 := hb2.ne'
      have e3 : t ^ 2 + c ^ 2 ≠ 0 := by positivity
      field_simp
    have h2 : (Real.pi ^ 2)⁻¹ * (1 / (t ^ 2 + b ^ 2))
        = t ^ 2 / (Real.pi ^ 2 * ((t ^ 2 + b ^ 2) * t ^ 2)) := by
      have e1 : Real.pi ≠ 0 := Real.pi_ne_zero
      have e2 : t ^ 2 + b ^ 2 ≠ 0 := hb2.ne'
      have e3 : t ≠ 0 := ht0.ne'
      field_simp
    rw [h1, h2, div_le_div_iff₀ (by positivity) (by positivity)]
    calc t ^ 2 * (Real.pi ^ 2 * ((t ^ 2 + b ^ 2) * t ^ 2))
        = t ^ 2 * Real.pi ^ 2 * (t ^ 2 + b ^ 2) * t ^ 2 := by ring
      _ ≤ t ^ 2 * Real.pi ^ 2 * (t ^ 2 + b ^ 2) * (t ^ 2 + c ^ 2) :=
          mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg c]) (by positivity)
      _ = t ^ 2 * (Real.pi ^ 2 * ((t ^ 2 + b ^ 2) * (t ^ 2 + c ^ 2))) := by ring
  rcases eq_or_ne (z 0) 0 with h0 | h0
  · rcases eq_or_ne (z 1) 0 with h1 | h1
    · refine absurd (funext fun i => ?_) hz
      revert i
      rw [Fin.forall_fin_two]
      exact ⟨h0, h1⟩
    · exact (key (z 1) (z 0) h1).congr (Eventually.of_forall fun t => by
        show cauchyDensity t (z 1) * cauchyDensity t (z 0) = heatKernel t z
        rw [heatKernel]
        ring)
  · exact (key (z 0) (z 1) h0).congr (Eventually.of_forall fun _ => rfl)

/-- **The potential kernel is the fundamental solution of the coordinate generator.** For every
test function `φ`,
`(1 / (2π)) ∫ G(z) (jumpGen 1 φ)(z) dz = −φ 0` with `G` the potential kernel.

Writing `A = (1/(2π)) jumpGen 1` and `P t = ∫ p_t φ`, the proof integrates the semigroup equation
in time:
`∫ G · Aφ = ∫_z (∫₀^∞ p_t dt) Aφ = ∫₀^∞ (∫_z p_t Aφ) dt = ∫₀^∞ (∫_z (A p_t) φ) dt
  = ∫₀^∞ P' t dt = lim_{T→∞} P T − lim_{ε→0⁺} P ε = 0 − φ 0`.
The exchange of the `z`- and `t`-integrals is justified by
`∫_z ∫₀^∞ p_t(z) |Aφ(z)| dt dz = ∫_z G(z) |Aφ(z)| dz < ∞`, the self-adjointness step is
`integral_heatKernel_mul_jumpGen`, and the last equality is the fundamental theorem of calculus on
`(0, ∞)` applied along the sequence `1/(n+1) ↓ 0`. -/
theorem potential_jumpGen (hφ : IsTestFunction φ) :
    (1 / (2 * Real.pi)) * ∫ z, potential z * jumpGen 1 φ z = -φ 0 := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.1.of_le (by norm_cast)
  obtain ⟨N₀, N₂, hN₀, hN₂⟩ := exists_bounds_of_hasCompactSupport hφ2 hφ.2
  have hAc : Continuous (jumpGen 1 φ) := continuous_jumpGen one_pos (by norm_num) hφ2 hN₀ hN₂
  -- almost every point of the plane is nonzero
  have hae : ∀ᵐ z : Fin 2 → ℝ, z ≠ 0 := by
    have h0 : volume ({0} : Set (Fin 2 → ℝ)) = 0 := measure_singleton 0
    filter_upwards [compl_mem_ae_iff.2 h0] with z hz
    simpa using hz
  -- the double integral over the plane and the half-line is absolutely convergent
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (z : Fin 2 → ℝ) (t : ℝ) => heatKernel t z * jumpGen 1 φ z)
      (volume.prod (volume.restrict (Ioi 0))) := by
    have h1 : Measurable fun q : (Fin 2 → ℝ) × ℝ => heatKernel q.2 q.1 := by
      unfold heatKernel cauchyDensity
      fun_prop
    exact (h1.mul (hAc.measurable.comp measurable_fst)).aestronglyMeasurable
  have hnorm : ∀ᵐ z : Fin 2 → ℝ,
      (∫ t in Ioi 0, ‖heatKernel t z * jumpGen 1 φ z‖) = |potential z * jumpGen 1 φ z| := by
    filter_upwards [hae] with z hz
    have h1 : EqOn (fun t : ℝ => ‖heatKernel t z * jumpGen 1 φ z‖)
        (fun t : ℝ => heatKernel t z * |jumpGen 1 φ z|) (Ioi 0) := fun t ht => by
      have ht0 : (0 : ℝ) < t := ht
      show ‖heatKernel t z * jumpGen 1 φ z‖ = heatKernel t z * |jumpGen 1 φ z|
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg ht0.le z)]
    rw [setIntegral_congr_fun measurableSet_Ioi h1, integral_mul_const,
      integral_Ioi_heatKernel hz, abs_mul, abs_of_nonneg (potential_nonneg z)]
  have hint : Integrable
      (Function.uncurry fun (z : Fin 2 → ℝ) (t : ℝ) => heatKernel t z * jumpGen 1 φ z)
      (volume.prod (volume.restrict (Ioi 0))) := by
    refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
    · filter_upwards [hae] with z hz
      show Integrable (fun y : ℝ => heatKernel y z * jumpGen 1 φ z) (volume.restrict (Ioi 0))
      exact (integrableOn_Ioi_heatKernel hz).mul_const _
    · exact ((integrable_potential_mul_jumpGen hφ).abs).congr (hnorm.mono fun z h => h.symm)
  -- the potential pairing as a time integral of semigroup pairings
  have hpot : (∫ z, potential z * jumpGen 1 φ z)
      = ∫ t in Ioi 0, ∫ z, heatKernel t z * jumpGen 1 φ z := by
    have h1 : (∫ z, potential z * jumpGen 1 φ z)
        = ∫ z, ∫ t in Ioi 0, heatKernel t z * jumpGen 1 φ z := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with z hz
      rw [integral_mul_const, integral_Ioi_heatKernel hz]
    rw [h1, integral_integral_swap hint]
  -- the semigroup equation turns each slice into the time derivative of the pairing
  have hP' : ∀ t : ℝ, 0 < t → (1 / (2 * Real.pi)) * ∫ z, heatKernel t z * jumpGen 1 φ z
      = ∫ z, deriv (fun t => heatKernel t z) t * φ z := by
    intro t ht
    rw [integral_heatKernel_mul_jumpGen ht hφ, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    show (1 / (2 * Real.pi)) * (jumpGen 1 (heatKernel t) z * φ z)
      = deriv (fun t => heatKernel t z) t * φ z
    rw [← jumpGen_heatKernel_deriv ht z]
    ring
  have hP'int : IntegrableOn
      (fun t => ∫ z, deriv (fun t => heatKernel t z) t * φ z) (Ioi 0) := by
    refine (hint.integral_prod_right.const_mul (1 / (2 * Real.pi))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hP' t ht
  -- the fundamental theorem of calculus on the half-line, along `1/(n+1) ↓ 0`
  have hupos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have humono : Monotone fun n : ℕ => Ioi (1 / ((n : ℝ) + 1)) := by
    intro m n hmn
    refine Ioi_subset_Ioi (one_div_le_one_div_of_le (by positivity) ?_)
    have : (m : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hmn
    linarith
  have hunion : (⋃ n : ℕ, Ioi (1 / ((n : ℝ) + 1))) = Ioi (0 : ℝ) := by
    refine subset_antisymm (iUnion_subset fun n => Ioi_subset_Ioi (hupos n).le) fun t ht => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < t from ht)
    exact mem_iUnion.2 ⟨n, hn⟩
  have hval : ∀ n : ℕ,
      (∫ t in Ioi (1 / ((n : ℝ) + 1)), ∫ z, deriv (fun t => heatKernel t z) t * φ z)
        = 0 - ∫ z, heatKernel (1 / ((n : ℝ) + 1)) z * φ z := fun n =>
    integral_Ioi_of_hasDerivAt_of_tendsto
      ((hasDerivAt_integral_heatKernel_mul hφ (hupos n)).continuousAt.continuousWithinAt)
      (fun x hx => hasDerivAt_integral_heatKernel_mul hφ (lt_trans (hupos n) hx))
      (hP'int.mono_set (Ioi_subset_Ioi (hupos n).le))
      (tendsto_integral_heatKernel_mul_atTop hφ)
  have hPu : Tendsto (fun n : ℕ => ∫ z, heatKernel (1 / ((n : ℝ) + 1)) z * φ z) atTop (𝓝 (φ 0)) :=
    (tendsto_integral_heatKernel_mul_zero hφ).comp
      (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall hupos))
  have hfinal : (∫ t in Ioi 0, ∫ z, deriv (fun t => heatKernel t z) t * φ z) = -φ 0 := by
    have h1 : Tendsto
        (fun n : ℕ => ∫ t in Ioi (1 / ((n : ℝ) + 1)),
          ∫ z, deriv (fun t => heatKernel t z) t * φ z)
        atTop (𝓝 (∫ t in Ioi 0, ∫ z, deriv (fun t => heatKernel t z) t * φ z)) := by
      have h := tendsto_setIntegral_of_monotone (μ := volume)
        (f := fun t => ∫ z, deriv (fun t => heatKernel t z) t * φ z)
        (s := fun n : ℕ => Ioi (1 / ((n : ℝ) + 1))) (fun _ => measurableSet_Ioi) humono
        (by rw [hunion]; exact hP'int)
      rwa [hunion] at h
    have h2 : Tendsto
        (fun n : ℕ => ∫ t in Ioi (1 / ((n : ℝ) + 1)),
          ∫ z, deriv (fun t => heatKernel t z) t * φ z) atTop (𝓝 (-φ 0)) := by
      refine Tendsto.congr (fun n => (hval n).symm) ?_
      simpa using hPu.neg
    exact tendsto_nhds_unique h1 h2
  rw [hpot, ← integral_const_mul,
    setIntegral_congr_fun measurableSet_Ioi fun t ht => hP' t ht]
  exact hfinal

end CenteredMaximal.Cauchy

end
