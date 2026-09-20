/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.BaseMoment
public import CenteredMaximal.Fractional.KernelPositivity
public import CenteredMaximal.Fractional.MajorBase
public import CenteredMaximal.Fractional.SplineTaylor

/-!
# The weighted `L²` moment of the comparison density

`CenteredMaximal.Fractional.weakTypeConstant_two_le_frac` asks for the moment
`∫ g² min(1, ‖z‖^{16/5}) < ∞` of the generator density `g = fracDensity` of the `α = 6/5`
comparison kernel. This file supplies it.

## The shape of the majorant

The density is *not* dominated by `A (r^{-12/5} + r^{-11/5})`, `r = diamondNorm`: the kernel is
supported in the diamond `r ≤ 7/4`, so at a point `(D, ε)` with `D > 7/4` the second difference in
the `j = 1` direction vanishes identically while the `j = 0` direction sweeps the line
`{(s, ε)}` across the kernel's non-integrable `r^{-6/5}` singularity at distance `ε` from it,
contributing `≈ D^{-11/5} ∫ (|s| + ε)^{-6/5} ds ≈ 10 D^{-11/5} ε^{-1/5}`, which is unbounded at
fixed `D`. A second, independent blow-up sits on the support boundary: the base has a *corner*
there, and the `6/5`-generator of a corner at distance `δ` is of size `δ^{1-6/5} = δ^{-1/5}`.
Both are harmless after squaring against the weight, and the majorant used here is

`|fracDensity z| ≤ A (r^{-12/5} + r^{-11/5} + r^{-11/5} m^{-1/5} + s(z))`,
`m = min(|z₀|, |z₁|)`,  `s(z) = |r − 7/4|^{-1/5}` on `|r − 7/4| < 1` and `0` beyond,

away from the two coordinate axes and the support boundary — a null set.

## Main results

* `integrable_fracDensity_sq_moment`: the moment itself.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### One-dimensional profiles

Every integrability statement below is reduced to the integrability on `ℝ` of a *profile*
`min (|x|^p, |x|^q)` with `p < −1 < q`: the small exponent controls the singularity at the origin
and the large one the decay at infinity. -/

/-- The one-dimensional profile `min(|x|^p, |x|^q)`. -/
private def axisProfile (p q x : ℝ) : ℝ := min (|x| ^ p) (|x| ^ q)

private theorem axisProfile_nonneg (p q x : ℝ) : 0 ≤ axisProfile p q x :=
  le_min (Real.rpow_nonneg (abs_nonneg x) p) (Real.rpow_nonneg (abs_nonneg x) q)

private theorem measurable_axisProfile (p q : ℝ) : Measurable (axisProfile p q) :=
  (continuous_abs.measurable.pow_const p).min (continuous_abs.measurable.pow_const q)

private theorem axisProfile_neg (p q x : ℝ) : axisProfile p q (-x) = axisProfile p q x := by
  rw [axisProfile, axisProfile, abs_neg]

/-- **The profile is integrable on the line** when the exponents straddle `−1`. -/
private theorem integrable_axisProfile {p q : ℝ} (hp : p < -1) (hq : -1 < q) :
    Integrable (axisProfile p q) := by
  refine CenteredMaximal.integrable_of_even (axisProfile_neg p q) ?_
  rw [← Ioc_union_Ioi_eq_Ioi (zero_le_one : (0 : ℝ) ≤ 1), integrableOn_union]
  constructor
  · have hint : IntegrableOn (fun x : ℝ => x ^ q) (Ioc 0 1) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' hq)
    refine hint.mono' (measurable_axisProfile p q).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioc fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (axisProfile_nonneg p q x)]
    calc axisProfile p q x ≤ |x| ^ q := min_le_right _ _
      _ = x ^ q := by rw [abs_of_pos hx.1]
  · have hint : IntegrableOn (fun x : ℝ => x ^ p) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt hp one_pos
    refine hint.mono' (measurable_axisProfile p q).aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (axisProfile_nonneg p q x)]
    calc axisProfile p q x ≤ |x| ^ p := min_le_left _ _
      _ = x ^ p := by rw [abs_of_pos (zero_lt_one.trans hx)]

/-! ### The radial profile of the weight

The weight `min(1, ‖z‖^{16/5})` against the power `r^{-22/5}` is dominated by the radial profile
`min(r^{-22/5}, r^{-6/5})`, which is what the product majorant of the axis term consumes. -/

/-- The radial profile `min(r^{-22/5}, r^{-6/5})` of `r^{-22/5} min(1, ‖z‖^{16/5})`. -/
private def radialProfile (t : ℝ) : ℝ := min (t ^ (-(22 / 5) : ℝ)) (t ^ (-(6 / 5) : ℝ))

private theorem radialProfile_nonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ radialProfile t :=
  le_min (Real.rpow_nonneg ht _) (Real.rpow_nonneg ht _)

/-- The weighted power is dominated by the radial profile. -/
private theorem rpow_mul_min_le_radialProfile (z : Fin 2 → ℝ) :
    diamondNorm z ^ (-(22 / 5) : ℝ) * min 1 (‖z‖ ^ (16 / 5 : ℝ))
      ≤ radialProfile (diamondNorm z) := by
  have hr : 0 ≤ diamondNorm z := diamondNorm_nonneg z
  have hpow : 0 ≤ diamondNorm z ^ (-(22 / 5) : ℝ) := Real.rpow_nonneg hr _
  refine le_min ?_ ?_
  · simpa using mul_le_mul_of_nonneg_left (min_le_left 1 (‖z‖ ^ (16 / 5 : ℝ))) hpow
  · rcases eq_or_lt_of_le hr with h0 | h0
    · have hz : z = 0 := diamondNorm_eq_zero_iff.1 h0.symm
      rw [hz, norm_zero, Real.zero_rpow (by norm_num), min_eq_right zero_le_one, mul_zero]
      exact Real.rpow_nonneg (diamondNorm_nonneg 0) _
    · have hle : min 1 (‖z‖ ^ (16 / 5 : ℝ)) ≤ diamondNorm z ^ (16 / 5 : ℝ) :=
        (min_le_right _ _).trans
          (Real.rpow_le_rpow (norm_nonneg z) (norm_le_diamondNorm z) (by norm_num))
      refine (mul_le_mul_of_nonneg_left hle hpow).trans_eq ?_
      rw [← Real.rpow_add h0]
      norm_num

/-! ### The axis term

The square of `r^{-11/5} m^{-1/5}` against the weight is `radialProfile r · m^{-2/5}`, and
`m^{-2/5} ≤ |z₀|^{-2/5} + |z₁|^{-2/5}`. Each of the two resulting terms is dominated by a
*product* of one-dimensional profiles, so the plane integral splits. -/

/-- Monotonicity of a truncated negative power in the radius. -/
private theorem min_rpow_le_min_rpow {c u r : ℝ} (hc : 0 ≤ c) (hu : 0 < u) (hur : u ≤ r) :
    min (r ^ (-(11 / 5) : ℝ)) (r ^ (-c)) ≤ min (u ^ (-(11 / 5) : ℝ)) (u ^ (-c)) :=
  min_le_min (Real.rpow_le_rpow_of_nonpos hu hur (by norm_num))
    (Real.rpow_le_rpow_of_nonpos hu hur (by linarith))

/-- **The radial profile splits.** For nonnegative exponents with `c₁ + c₂ = 6/5`,
`min(r^{-22/5}, r^{-6/5}) ≤ min(r^{-11/5}, r^{-c₁}) · min(r^{-11/5}, r^{-c₂})`: below `r = 1` the
two right factors are `r^{-c₁}` and `r^{-c₂}`, whose product is `r^{-6/5}`, and above it they are
both `r^{-11/5}`, whose product is `r^{-22/5}`. -/
private theorem radialProfile_le_mul {c₁ c₂ : ℝ} (h1 : 0 ≤ c₁) (h2 : 0 ≤ c₂)
    (hsum : c₁ + c₂ = 6 / 5) {r : ℝ} (hr : 0 < r) :
    radialProfile r ≤ min (r ^ (-(11 / 5) : ℝ)) (r ^ (-c₁))
      * min (r ^ (-(11 / 5) : ℝ)) (r ^ (-c₂)) := by
  rcases le_total r 1 with hr1 | hr1
  · have e1 : min (r ^ (-(11 / 5) : ℝ)) (r ^ (-c₁)) = r ^ (-c₁) :=
      min_eq_right (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith))
    have e2 : min (r ^ (-(11 / 5) : ℝ)) (r ^ (-c₂)) = r ^ (-c₂) :=
      min_eq_right (Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith))
    rw [e1, e2, ← Real.rpow_add hr]
    refine (min_le_right _ _).trans_eq ?_
    rw [show -c₁ + -c₂ = -(6 / 5 : ℝ) from by linarith]
  · have e1 : min (r ^ (-(11 / 5) : ℝ)) (r ^ (-c₁)) = r ^ (-(11 / 5) : ℝ) :=
      min_eq_left (Real.rpow_le_rpow_of_exponent_le hr1 (by linarith))
    have e2 : min (r ^ (-(11 / 5) : ℝ)) (r ^ (-c₂)) = r ^ (-(11 / 5) : ℝ) :=
      min_eq_left (Real.rpow_le_rpow_of_exponent_le hr1 (by linarith))
    rw [e1, e2, ← Real.rpow_add hr]
    refine (min_le_left _ _).trans_eq ?_
    norm_num

/-- One half of the product majorant: the profile against `|x|^{-2/5}`, with the exponent `1/2` on
the `x`-side and `7/10` on the `y`-side. -/
private theorem radialProfile_mul_le_prod {x y : ℝ} (hx : 0 < |x|) (hy : 0 < |y|) :
    radialProfile (|x| + |y|) * |x| ^ (-(2 / 5) : ℝ)
      ≤ axisProfile (-(13 / 5)) (-(9 / 10)) x * axisProfile (-(11 / 5)) (-(7 / 10)) y := by
  have hr : 0 < |x| + |y| := by linarith
  have hsplit := radialProfile_le_mul (c₁ := 1 / 2) (c₂ := 7 / 10) (by norm_num) (by norm_num)
    (by norm_num) hr
  have hxr := min_rpow_le_min_rpow (c := 1 / 2) (r := |x| + |y|) (by norm_num) hx (by linarith)
  have hyr := min_rpow_le_min_rpow (c := 7 / 10) (r := |x| + |y|) (by norm_num) hy (by linarith)
  have hxnn : 0 ≤ min (|x| ^ (-(11 / 5) : ℝ)) (|x| ^ (-(1 / 2) : ℝ)) :=
    le_min (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg hx.le _)
  have hynn : 0 ≤ min (|y| ^ (-(11 / 5) : ℝ)) (|y| ^ (-(7 / 10) : ℝ)) :=
    le_min (Real.rpow_nonneg hy.le _) (Real.rpow_nonneg hy.le _)
  have hstep : radialProfile (|x| + |y|)
      ≤ min (|x| ^ (-(11 / 5) : ℝ)) (|x| ^ (-(1 / 2) : ℝ))
        * min (|y| ^ (-(11 / 5) : ℝ)) (|y| ^ (-(7 / 10) : ℝ)) := by
    refine hsplit.trans ?_
    exact mul_le_mul hxr hyr
      (le_min (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr.le _)) hxnn
  have hprod : min (|x| ^ (-(11 / 5) : ℝ)) (|x| ^ (-(1 / 2) : ℝ)) * |x| ^ (-(2 / 5) : ℝ)
      = axisProfile (-(13 / 5)) (-(9 / 10)) x := by
    rw [axisProfile, min_mul_of_nonneg _ _ (Real.rpow_nonneg (abs_nonneg x) _),
      ← Real.rpow_add hx, ← Real.rpow_add hx]
    norm_num
  calc radialProfile (|x| + |y|) * |x| ^ (-(2 / 5) : ℝ)
      ≤ (min (|x| ^ (-(11 / 5) : ℝ)) (|x| ^ (-(1 / 2) : ℝ))
          * min (|y| ^ (-(11 / 5) : ℝ)) (|y| ^ (-(7 / 10) : ℝ))) * |x| ^ (-(2 / 5) : ℝ) :=
        mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg (abs_nonneg x) _)
    _ = (min (|x| ^ (-(11 / 5) : ℝ)) (|x| ^ (-(1 / 2) : ℝ)) * |x| ^ (-(2 / 5) : ℝ))
          * min (|y| ^ (-(11 / 5) : ℝ)) (|y| ^ (-(7 / 10) : ℝ)) := by ring
    _ = _ := by rw [hprod]; rfl

/-- The swapped half of the product majorant, with the two exponents exchanged. -/
private theorem radialProfile_mul_le_prod' {x y : ℝ} (hx : 0 < |x|) (hy : 0 < |y|) :
    radialProfile (|x| + |y|) * |y| ^ (-(2 / 5) : ℝ)
      ≤ axisProfile (-(11 / 5)) (-(7 / 10)) x * axisProfile (-(13 / 5)) (-(9 / 10)) y := by
  have h := radialProfile_mul_le_prod hy hx
  rw [show |y| + |x| = |x| + |y| from add_comm _ _] at h
  exact h.trans_eq (mul_comm _ _)

/-- `(x^a)² = x^{2a}` for `x ≥ 0`, the one power identity the squaring needs. -/
private theorem rpow_sq {x : ℝ} (hx : 0 ≤ x) (a : ℝ) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_natCast (x ^ a) 2, ← Real.rpow_mul hx]
  norm_num
  ring_nf

/-- The distance to the nearer axis has a negative power dominated by the sum of the two
coordinate powers; both sides vanish on the axes. -/
private theorem min_abs_rpow_le (z : Fin 2 → ℝ) :
    (min |z 0| |z 1|) ^ (-(2 / 5) : ℝ)
      ≤ |z 0| ^ (-(2 / 5) : ℝ) + |z 1| ^ (-(2 / 5) : ℝ) := by
  have h0 : (0 : ℝ) ≤ |z 0| ^ (-(2 / 5) : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
  have h1 : (0 : ℝ) ≤ |z 1| ^ (-(2 / 5) : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
  rcases min_cases |z 0| |z 1| with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]; linarith
  · rw [h]; linarith

/-! ### Integrability of the axis term -/

/-- **The axis term of the squared majorant is integrable.** The weighted square
`r^{-22/5} m^{-2/5} min(1, ‖z‖^{16/5})` is dominated by `radialProfile r · m^{-2/5}`, which in turn
is dominated by a sum of two *products* of one-dimensional profiles; the plane integral therefore
factors through `volume_preserving_finTwoArrow` into a product of two finite line integrals. -/
private theorem integrable_radialProfile_mul_min_rpow :
    Integrable fun z : Fin 2 → ℝ =>
      radialProfile (diamondNorm z) * (min |z 0| |z 1|) ^ (-(2 / 5) : ℝ) := by
  set F : ℝ → ℝ := axisProfile (-(13 / 5)) (-(9 / 10)) with hF
  set G : ℝ → ℝ := axisProfile (-(11 / 5)) (-(7 / 10)) with hG
  have hFint : Integrable F := integrable_axisProfile (by norm_num) (by norm_num)
  have hGint : Integrable G := integrable_axisProfile (by norm_num) (by norm_num)
  have hprod : Integrable fun p : ℝ × ℝ => F p.1 * G p.2 + G p.1 * F p.2 := by
    rw [Measure.volume_eq_prod]
    exact (hFint.mul_prod hGint).add (hGint.mul_prod hFint)
  have hcomp : Integrable fun z : Fin 2 → ℝ =>
      F (z 0) * G (z 1) + G (z 0) * F (z 1) :=
    (volume_preserving_finTwoArrow ℝ).integrable_comp_of_integrable hprod
  have hm : Measurable fun z : Fin 2 → ℝ =>
      radialProfile (diamondNorm z) * (min |z 0| |z 1|) ^ (-(2 / 5) : ℝ) := by
    have h1 : Measurable fun z : Fin 2 → ℝ => radialProfile (diamondNorm z) :=
      ((measurable_diamondNorm.pow_const _).min (measurable_diamondNorm.pow_const _))
    have ha0 : Measurable fun z : Fin 2 → ℝ => |z 0| :=
      continuous_abs.measurable.comp (measurable_pi_apply (0 : Fin 2))
    have ha1 : Measurable fun z : Fin 2 → ℝ => |z 1| :=
      continuous_abs.measurable.comp (measurable_pi_apply (1 : Fin 2))
    have h2 : Measurable fun z : Fin 2 → ℝ => (min |z 0| |z 1|) ^ (-(2 / 5) : ℝ) :=
      (ha0.min ha1).pow_const _
    exact h1.mul h2
  refine hcomp.mono' hm.aestronglyMeasurable (.of_forall fun z => ?_)
  have hr : diamondNorm z = |z 0| + |z 1| := rfl
  have hprof : 0 ≤ radialProfile (diamondNorm z) :=
    radialProfile_nonneg _ (diamondNorm_nonneg z)
  have hnn : 0 ≤ radialProfile (diamondNorm z) * (min |z 0| |z 1|) ^ (-(2 / 5) : ℝ) :=
    mul_nonneg hprof (Real.rpow_nonneg (le_min (abs_nonneg _) (abs_nonneg _)) _)
  rw [Real.norm_eq_abs, abs_of_nonneg hnn]
  rcases eq_or_lt_of_le (abs_nonneg (z 0)) with h0 | h0
  · have hmin : min |z 0| |z 1| = 0 := by
      rw [← h0]
      exact min_eq_left (h0 ▸ abs_nonneg (z 1))
    rw [hmin, Real.zero_rpow (by norm_num), mul_zero]
    exact add_nonneg (mul_nonneg (axisProfile_nonneg _ _ _) (axisProfile_nonneg _ _ _))
      (mul_nonneg (axisProfile_nonneg _ _ _) (axisProfile_nonneg _ _ _))
  rcases eq_or_lt_of_le (abs_nonneg (z 1)) with h1 | h1
  · have hmin : min |z 0| |z 1| = 0 := by
      rw [← h1]
      exact min_eq_right (h1 ▸ abs_nonneg (z 0))
    rw [hmin, Real.zero_rpow (by norm_num), mul_zero]
    exact add_nonneg (mul_nonneg (axisProfile_nonneg _ _ _) (axisProfile_nonneg _ _ _))
      (mul_nonneg (axisProfile_nonneg _ _ _) (axisProfile_nonneg _ _ _))
  calc radialProfile (diamondNorm z) * (min |z 0| |z 1|) ^ (-(2 / 5) : ℝ)
      ≤ radialProfile (|z 0| + |z 1|) * (|z 0| ^ (-(2 / 5) : ℝ) + |z 1| ^ (-(2 / 5) : ℝ)) := by
        rw [hr]
        exact mul_le_mul_of_nonneg_left (min_abs_rpow_le z) (hr ▸ hprof)
    _ = radialProfile (|z 0| + |z 1|) * |z 0| ^ (-(2 / 5) : ℝ)
          + radialProfile (|z 0| + |z 1|) * |z 1| ^ (-(2 / 5) : ℝ) := by ring
    _ ≤ F (z 0) * G (z 1) + G (z 0) * F (z 1) :=
        add_le_add (radialProfile_mul_le_prod h0 h1) (radialProfile_mul_le_prod' h0 h1)

/-! ### The shell term

The base of the kernel has a corner on the support boundary `r = 7/4`, and the `6/5`-generator of a
corner at distance `δ` is `O(δ^{-1/5})`. Squared, that is `δ^{-2/5}`, which is integrable against
the radial element `4 r dr` because `−2/5 > −1`; the window `|r − 7/4| < 1` keeps the term bounded
and compactly supported. -/

/-- The corner profile `|t − 7/4|^{-1/5}` on the window `|t − 7/4| < 1`. -/
private def shellProfile (t : ℝ) : ℝ :=
  if |t - 7 / 4| < 1 then |t - 7 / 4| ^ (-(1 / 5) : ℝ) else 0

private theorem shellProfile_nonneg (t : ℝ) : 0 ≤ shellProfile t := by
  rw [shellProfile]
  split
  · exact Real.rpow_nonneg (abs_nonneg _) _
  · exact le_rfl

private theorem measurable_shellProfile : Measurable shellProfile := by
  refine Measurable.ite ?_ ((continuous_abs.measurable.comp
    (measurable_id.sub measurable_const)).pow_const _) measurable_const
  exact (continuous_abs.comp (continuous_id.sub continuous_const)).measurable
    measurableSet_Iio

/-- The squared corner profile against the radial element is dominated by a translated
one-dimensional profile. -/
private theorem radial_shellProfile_sq_le (t : ℝ) :
    4 * t * shellProfile t ^ 2 ≤ 11 * axisProfile (-(5 / 2)) (-(2 / 5)) (t - 7 / 4) := by
  rw [shellProfile]
  split
  · rename_i hwin
    have habs : 0 ≤ |t - 7 / 4| := abs_nonneg _
    have hsq : (|t - 7 / 4| ^ (-(1 / 5) : ℝ)) ^ 2 = |t - 7 / 4| ^ (-(2 / 5) : ℝ) := by
      rw [rpow_sq habs]
      norm_num
    have hmin : axisProfile (-(5 / 2)) (-(2 / 5)) (t - 7 / 4) = |t - 7 / 4| ^ (-(2 / 5) : ℝ) := by
      rw [axisProfile]
      rcases eq_or_lt_of_le habs with h0 | h0
      · rw [← h0, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num)]
        simp
      · exact min_eq_right (Real.rpow_le_rpow_of_exponent_ge h0 hwin.le (by norm_num))
    have h4t : 4 * t ≤ 11 := by
      have := (abs_lt.1 hwin).2
      linarith
    rw [hsq, hmin]
    exact mul_le_mul_of_nonneg_right h4t (Real.rpow_nonneg habs _)
  · have : (0 : ℝ) ≤ 11 * axisProfile (-(5 / 2)) (-(2 / 5)) (t - 7 / 4) := by
      have := axisProfile_nonneg (-(5 / 2)) (-(2 / 5)) (t - 7 / 4)
      linarith
    simpa using this

/-- **The shell term of the squared majorant is integrable.** -/
private theorem integrable_shellProfile_sq :
    Integrable fun z : Fin 2 → ℝ => shellProfile (diamondNorm z) ^ 2 := by
  have hm : Measurable fun z : Fin 2 → ℝ => shellProfile (diamondNorm z) ^ 2 :=
    (measurable_shellProfile.comp measurable_diamondNorm).pow_const 2
  have hnn : ∀ z : Fin 2 → ℝ, 0 ≤ shellProfile (diamondNorm z) ^ 2 := fun z => sq_nonneg _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (.of_forall hnn)]
  have hline : Integrable fun u : ℝ => 11 * axisProfile (-(5 / 2)) (-(2 / 5)) (u - 7 / 4) :=
    ((integrable_axisProfile (by norm_num) (by norm_num)).comp_sub_right (7 / 4)).const_mul 11
  have hbound : ∫⁻ t in Ioi (0 : ℝ), 4 * ENNReal.ofReal t
        * ENNReal.ofReal (shellProfile t ^ 2)
      ≤ ∫⁻ u : ℝ, ENNReal.ofReal (11 * axisProfile (-(5 / 2)) (-(2 / 5)) (u - 7 / 4)) := by
    refine le_trans (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_)
      (setLIntegral_le_lintegral _ _)
    have ht0 : (0 : ℝ) < t := ht
    rw [← ENNReal.ofReal_ofNat (n := 4), ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
      ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * t)]
    exact ENNReal.ofReal_le_ofReal (radial_shellProfile_sq_le t)
  calc ∫⁻ z : Fin 2 → ℝ, ENNReal.ofReal (shellProfile (diamondNorm z) ^ 2)
      = ∫⁻ t in Ioi (0 : ℝ), 4 * ENNReal.ofReal t * ENNReal.ofReal (shellProfile t ^ 2) :=
        lintegral_comp_diamondNorm
          (ENNReal.measurable_ofReal.comp (measurable_shellProfile.pow_const 2))
    _ ≤ ∫⁻ u : ℝ, ENNReal.ofReal (11 * axisProfile (-(5 / 2)) (-(2 / 5)) (u - 7 / 4)) := hbound
    _ < ⊤ := by
        rw [← ofReal_integral_eq_lintegral_ofReal hline
          (.of_forall fun u => by
            have := axisProfile_nonneg (-(5 / 2)) (-(2 / 5)) (u - 7 / 4)
            positivity)]
        exact ENNReal.ofReal_lt_top

end CenteredMaximal.Fractional

end

end
