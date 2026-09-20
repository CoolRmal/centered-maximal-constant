/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.JumpGenerator
public import CenteredMaximal.Cauchy.Potential
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Cauchy potential is generator-harmonic away from the coordinate axes

`CenteredMaximal.Cauchy.Delta` proves that the potential kernel `G z = 1 / (2π r(z))` of the
coordinate Cauchy generator, `r = diamondNorm`, is its fundamental solution in the *weak* sense.
This file proves the pointwise statement off the two coordinate axes,

`jumpGen_potential_eq_zero`: `z 0 ≠ 0 → z 1 ≠ 0 → jumpGen 1 potential z = 0`,

together with the affine variant `jumpGen_affine_potential_eq_zero` used by the kernel
certificate: adding a constant to a multiple of the potential changes nothing.

## The one-dimensional reduction

Since `r (z + t e_j) = |z j + t| + |z (j + 1)|`, the axis-`j` second difference of the potential
at `z` is `(2π)⁻¹` times that of the one-dimensional profile `x ↦ 1 / (|x| + b)` with
`b = |z (j + 1)|`, evaluated at `a = |z j|`. Writing

`profileDiff a b t = (1 / (|a + t| + b) + 1 / (|a − t| + b) − 2 / (a + b)) / t²`,

the generator is therefore `2π jumpGen 1 potential z = I a b + I b a` with `I a b` the integral of
`profileDiff a b` over the line and `a = |z 0|`, `b = |z 1|`, so everything rests on the
antisymmetry `integral_profileDiff_antisymm`: `I a b + I b a = 0`.

## The closed form

The integrand is even, so `I a b = 2 ∫_0^∞`, and the half-line is split at `t = a`, where
`|a − t|` turns. On `(0, a]` the second difference collapses:
`profileDiff a b t = 2 / (s (s² − t²))` with `s = a + b` — in particular it is *bounded* there,
which is what makes the integral converge at the origin — and the antiderivative
`(log (s + t) − log (s − t)) / s²` gives `(log (2a + b) − log b) / s²`
(`integral_profileDiff_Ioc`). On `(a, ∞)` the integrand is
`1 / (t² (t + s)) + 1 / (t² (t + d)) − (2 / s) / t²` with `d = b − a`, with antiderivative
`(1/s − 1/d) / t + (log (t + s) − log t) / s² + (log (t + d) − log t) / d²` vanishing at infinity
(`integral_profileDiff_Ioi`). The `1 / d²` is a removable singularity of the *sum*, not of the
tail alone, so the diagonal `a = b` is computed separately (`integral_profileDiff_Ioi_self`,
where the middle term is `1 / t³`). Adding the two pieces,

`I a b = 2 (log a − log b) (1 / (a + b)² + 1 / (b − a)²) + 4 / ((b − a) (a + b))`,

which is `integral_profileDiff`; on the diagonal Lean's `x / 0 = 0` makes the right-hand side
vanish, so the statement needs no `a ≠ b`. Antisymmetry is then visible: swapping `a` and `b`
negates the logarithm and the rational term while fixing `(b − a)²`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace CenteredMaximal.Cauchy

/-- The one-dimensional jump integrand of the potential profile `x ↦ 1 / (|x| + b)` at `a > 0`,
normalised by dropping the factor `2π`: the second difference of the profile with step `t`,
divided by `t²`. -/
def profileDiff (a b t : ℝ) : ℝ :=
  (1 / (|a + t| + b) + 1 / (|a - t| + b) - 2 / (a + b)) / t ^ 2

/-! ### Elementary properties of the integrand -/

theorem profileDiff_neg_right (a b t : ℝ) : profileDiff a b (-t) = profileDiff a b t := by
  simp only [profileDiff, ← sub_eq_add_neg, sub_neg_eq_add, neg_sq]
  ring

/-- The second difference of the profile only sees `|a|`, the sign of `a` merely exchanging the
two outer terms. -/
theorem profileDiff_abs_left (a b t : ℝ) :
    (1 / (|a + t| + b) + 1 / (|a - t| + b) - 2 / (|a| + b)) / t ^ 2 = profileDiff |a| b t := by
  simp only [profileDiff]
  rcases abs_cases a with ⟨h, _⟩ | ⟨h, _⟩
  · rw [h]
  · rw [h, show -a + t = -(a - t) from by ring, abs_neg, show -a - t = -(a + t) from by ring,
      abs_neg]
    ring

private theorem measurable_profileDiff (a b : ℝ) : Measurable (profileDiff a b) := by
  unfold profileDiff
  fun_prop

/-- **Inside the corner.** For `0 < t ≤ a` the second difference is `2 t² / (s (s² − t²))` with
`s = a + b`, so the integrand is the bounded function `2 / (s (s² − t²))`. -/
private theorem profileDiff_of_mem_Ioc {a b t : ℝ} (hb : 0 < b) (ht : t ∈ Ioc 0 a) :
    profileDiff a b t = 2 / ((a + b) * ((a + b) ^ 2 - t ^ 2)) := by
  obtain ⟨ht0, hta⟩ := ht
  have ha : 0 < a := ht0.trans_le hta
  have h1 : |a + t| = a + t := abs_of_pos (by linarith)
  have h2 : |a - t| = a - t := abs_of_nonneg (by linarith)
  have n0 : t ≠ 0 := ht0.ne'
  have n1 : a + t + b ≠ 0 := ne_of_gt (by linarith)
  have n2 : a - t + b ≠ 0 := ne_of_gt (by linarith)
  have n3 : a + b ≠ 0 := ne_of_gt (by linarith)
  have n4 : (a + b) ^ 2 - t ^ 2 ≠ 0 := by nlinarith
  rw [profileDiff, h1, h2]
  field_simp
  ring

/-- **Past the corner.** For `a ≤ t` the modulus `|a − t|` turns, and the integrand becomes a
rational function with the three poles `0`, `−(a + b)` and `−(b − a)`. -/
private theorem profileDiff_of_le {a b t : ℝ} (ha : 0 < a) (ht : a ≤ t) :
    profileDiff a b t = (1 / (t + (a + b)) + 1 / (t + (b - a)) - 2 / (a + b)) / t ^ 2 := by
  have h1 : |a + t| = a + t := abs_of_pos (by linarith)
  have h2 : |a - t| = -(a - t) := abs_of_nonpos (by linarith)
  rw [profileDiff, h1, h2, show a + t + b = t + (a + b) from by ring,
    show -(a - t) + b = t + (b - a) from by ring]

/-! ### Integrability -/

private theorem hasDerivAt_neg_one_div {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun y : ℝ => -1 / y) ((t ^ 2)⁻¹) t := by
  refine ((hasDerivAt_const t (-1 : ℝ)).div (hasDerivAt_id' (x := t)) ht).congr_deriv ?_
  field_simp
  ring

private theorem tendsto_neg_one_div : Tendsto (fun y : ℝ => -1 / y) atTop (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have h' := h.neg
  rw [neg_zero] at h'
  exact h'.congr fun y => by simp [neg_div]

private theorem integrableOn_Ioi_inv_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun t ht => hasDerivAt_neg_one_div (ne_of_gt (lt_of_lt_of_le ha ht)))
    (fun t _ => by positivity) tendsto_neg_one_div

private theorem integrableOn_profileDiff_Ioc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (profileDiff a b) (Ioc 0 a) := by
  have hd : (0 : ℝ) < (a + b) * ((a + b) ^ 2 - a ^ 2) := by
    nlinarith [mul_pos (mul_pos ha ha) hb, mul_pos (mul_pos ha hb) hb, mul_pos (mul_pos hb hb) hb]
  refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
    (measurable_profileDiff a b).aestronglyMeasurable
    (M := 2 * (1 / ((a + b) * ((a + b) ^ 2 - a ^ 2))))
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  have hd' : (a + b) * ((a + b) ^ 2 - a ^ 2) ≤ (a + b) * ((a + b) ^ 2 - t ^ 2) := by
    have h : (0 : ℝ) ≤ (a + b) * ((a - t) * (a + t)) :=
      mul_nonneg (by linarith) (mul_nonneg (by linarith [ht.2]) (by linarith [ht.1]))
    nlinarith [h]
  rw [profileDiff_of_mem_Ioc hb ht, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by norm_num) (hd.trans_le hd').le)]
  calc 2 / ((a + b) * ((a + b) ^ 2 - t ^ 2))
      = 2 * (1 / ((a + b) * ((a + b) ^ 2 - t ^ 2))) := by ring
    _ ≤ 2 * (1 / ((a + b) * ((a + b) ^ 2 - a ^ 2))) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hd hd') (by norm_num)

private theorem integrableOn_profileDiff_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (profileDiff a b) (Ioi a) := by
  refine ((integrableOn_Ioi_inv_sq ha).const_mul (3 * (1 / (a + b)) + 1 / b)).mono'
    (measurable_profileDiff a b).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_)
  have hta : a < t := ht
  have ht0 : (0 : ℝ) < t := ha.trans hta
  have e3 : 1 / (t + (a + b)) ≤ 1 / (a + b) := one_div_le_one_div_of_le (by linarith) (by linarith)
  have e4 : 1 / (t + (b - a)) ≤ 1 / b := one_div_le_one_div_of_le hb (by linarith)
  have e5 : (0 : ℝ) < 1 / (t + (a + b)) := one_div_pos.2 (by linarith)
  have e6 : (0 : ℝ) < 1 / (t + (b - a)) := one_div_pos.2 (by linarith)
  have e7 : (0 : ℝ) < 1 / (a + b) := one_div_pos.2 (by linarith)
  have e8 : (0 : ℝ) < 1 / b := one_div_pos.2 hb
  rw [Real.norm_eq_abs, profileDiff_of_le ha hta.le, abs_div, abs_of_nonneg (sq_nonneg t),
    show (3 * (1 / (a + b)) + 1 / b) * (t ^ 2)⁻¹ = (3 * (1 / (a + b)) + 1 / b) / t ^ 2 from by ring]
  gcongr
  rw [show (2 : ℝ) / (a + b) = 2 * (1 / (a + b)) from by ring, abs_le]
  constructor <;> linarith

private theorem integrableOn_profileDiff_Ioi_zero {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (profileDiff a b) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi ha.le, integrableOn_union]
  exact ⟨integrableOn_profileDiff_Ioc ha hb, integrableOn_profileDiff_Ioi ha hb⟩

/-- **The jump integrand of the profile is integrable.** Near the origin the second difference is
`O(t²)` because `a > 0` keeps the corner of `x ↦ 1 / (|x| + b)` away, and at infinity the bracket
tends to `−2 / (a + b)`, leaving the integrable decay `t^{−2}`. -/
theorem integrable_profileDiff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (profileDiff a b) :=
  CenteredMaximal.integrable_of_even (profileDiff_neg_right a b)
    (integrableOn_profileDiff_Ioi_zero ha hb)

/-! ### The two half-line pieces -/

private theorem integral_profileDiff_Ioc {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Ioc 0 a, profileDiff a b t
      = (Real.log (2 * a + b) - Real.log b) / (a + b) ^ 2 := by
  have hpos : ∀ t ∈ uIcc (0 : ℝ) a, 0 < a + b + t ∧ 0 < a + b - t := by
    intro t ht
    rw [uIcc_of_le ha.le] at ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hcongr : EqOn (profileDiff a b)
      (fun t : ℝ => (1 / (a + b + t) + 1 / (a + b - t)) / (a + b) ^ 2) (Ioc 0 a) := by
    intro t ht
    have n1 : a + b + t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have n2 : a + b - t ≠ 0 := ne_of_gt (by linarith [ht.2])
    have n3 : a + b ≠ 0 := ne_of_gt (by linarith)
    have n4 : (a + b) ^ 2 - t ^ 2 ≠ 0 := by
      have : (a + b) ^ 2 - t ^ 2 = (a + b + t) * (a + b - t) := by ring
      rw [this]
      exact mul_ne_zero n1 n2
    rw [profileDiff_of_mem_Ioc hb ht]
    field_simp
    ring
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) a,
      HasDerivAt (fun y : ℝ => (Real.log (a + b + y) - Real.log (a + b - y)) / (a + b) ^ 2)
        ((1 / (a + b + t) + 1 / (a + b - t)) / (a + b) ^ 2) t := by
    intro t ht
    obtain ⟨h1, h2⟩ := hpos t ht
    refine ((((hasDerivAt_id' (x := t)).const_add (a + b)).log h1.ne').sub
      (((hasDerivAt_id' (x := t)).const_sub (a + b)).log h2.ne')).div_const
        ((a + b) ^ 2) |>.congr_deriv ?_
    simp only [neg_div, sub_neg_eq_add]
  have hcont : ContinuousOn (fun t : ℝ => (1 / (a + b + t) + 1 / (a + b - t)) / (a + b) ^ 2)
      (uIcc 0 a) :=
    ((continuousOn_const.div (by fun_prop) fun t ht => (hpos t ht).1.ne').add
      (continuousOn_const.div (by fun_prop) fun t ht => (hpos t ht).2.ne')).div_const _
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, ← intervalIntegral.integral_of_le ha.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  show (Real.log (a + b + a) - Real.log (a + b - a)) / (a + b) ^ 2
      - (Real.log (a + b + 0) - Real.log (a + b - 0)) / (a + b) ^ 2 = _
  rw [show a + b + a = 2 * a + b from by ring, show a + b - a = b from by ring, add_zero, sub_zero]
  ring

private theorem tendsto_log_add_sub_log (c : ℝ) :
    Tendsto (fun t : ℝ => Real.log (t + c) - Real.log t) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => 1 + c * t⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul c)
  have h2 := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
  rw [Real.log_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_gt_atTop (-c)] with t ht htc
  have h3 : t + c ≠ 0 := ne_of_gt (by linarith)
  show Real.log (1 + c * t⁻¹) = Real.log (t + c) - Real.log t
  rw [← Real.log_div h3 ht.ne', show 1 + c * t⁻¹ = (t + c) / t from by field_simp]

private theorem integral_profileDiff_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ∫ t in Ioi a, profileDiff a b t
      = -((1 / (a + b) - 1 / (b - a)) * a⁻¹ + (Real.log (2 * a + b) - Real.log a) / (a + b) ^ 2
          + (Real.log b - Real.log a) / (b - a) ^ 2) := by
  have hd : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
  have hs : a + b ≠ 0 := ne_of_gt (by linarith)
  have hderiv : ∀ t ∈ Ici a,
      HasDerivAt (fun y : ℝ => (1 / (a + b) - 1 / (b - a)) * y⁻¹
        + (Real.log (y + (a + b)) - Real.log y) / (a + b) ^ 2
        + (Real.log (y + (b - a)) - Real.log y) / (b - a) ^ 2) (profileDiff a b t) t := by
    intro t ht
    have hat : a ≤ t := ht
    have ht0 : (0 : ℝ) < t := ha.trans_le hat
    have h1 : (0 : ℝ) < t + (a + b) := by linarith
    have h2 : (0 : ℝ) < t + (b - a) := by linarith
    have d1 : HasDerivAt (fun y : ℝ => (1 / (a + b) - 1 / (b - a)) * y⁻¹)
        ((1 / (a + b) - 1 / (b - a)) * -(t ^ 2)⁻¹) t := (hasDerivAt_inv ht0.ne').const_mul _
    have d2 : HasDerivAt (fun y : ℝ => (Real.log (y + (a + b)) - Real.log y) / (a + b) ^ 2)
        ((1 / (t + (a + b)) - t⁻¹) / (a + b) ^ 2) t :=
      ((((hasDerivAt_id' (x := t)).add_const (a + b)).log h1.ne').sub
        (Real.hasDerivAt_log ht0.ne')).div_const _
    have d3 : HasDerivAt (fun y : ℝ => (Real.log (y + (b - a)) - Real.log y) / (b - a) ^ 2)
        ((1 / (t + (b - a)) - t⁻¹) / (b - a) ^ 2) t :=
      ((((hasDerivAt_id' (x := t)).add_const (b - a)).log h2.ne').sub
        (Real.hasDerivAt_log ht0.ne')).div_const _
    refine ((d1.add d2).add d3).congr_deriv ?_
    rw [profileDiff_of_le ha hat]
    field_simp
    ring
  have hlim : Tendsto (fun y : ℝ => (1 / (a + b) - 1 / (b - a)) * y⁻¹
      + (Real.log (y + (a + b)) - Real.log y) / (a + b) ^ 2
      + (Real.log (y + (b - a)) - Real.log y) / (b - a) ^ 2) atTop (𝓝 0) := by
    have t1 : Tendsto (fun y : ℝ => (1 / (a + b) - 1 / (b - a)) * y⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (1 / (a + b) - 1 / (b - a))
    have t2 := (tendsto_log_add_sub_log (a + b)).div_const ((a + b) ^ 2)
    have t3 := (tendsto_log_add_sub_log (b - a)).div_const ((b - a) ^ 2)
    rw [zero_div] at t2 t3
    simpa using (t1.add t2).add t3
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_profileDiff_Ioi ha hb) hlim]
  show (0 : ℝ) - ((1 / (a + b) - 1 / (b - a)) * a⁻¹
      + (Real.log (a + (a + b)) - Real.log a) / (a + b) ^ 2
      + (Real.log (a + (b - a)) - Real.log a) / (b - a) ^ 2) = _
  rw [show a + (a + b) = 2 * a + b from by ring, show a + (b - a) = b from by ring]
  ring

private theorem integral_profileDiff_Ioi_self {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi a, profileDiff a a t = -((Real.log (3 * a) - Real.log a) / (2 * a) ^ 2) := by
  have ha' : a ≠ 0 := ha.ne'
  have hderiv : ∀ t ∈ Ici a,
      HasDerivAt (fun y : ℝ => (1 / a - 1 / (2 * a)) * y⁻¹ + -(1 / 2) * (y⁻¹ * y⁻¹)
        + (Real.log (y + 2 * a) - Real.log y) / (2 * a) ^ 2) (profileDiff a a t) t := by
    intro t ht
    have hat : a ≤ t := ht
    have ht0 : (0 : ℝ) < t := ha.trans_le hat
    have h1 : (0 : ℝ) < t + 2 * a := by linarith
    have d1 : HasDerivAt (fun y : ℝ => (1 / a - 1 / (2 * a)) * y⁻¹)
        ((1 / a - 1 / (2 * a)) * -(t ^ 2)⁻¹) t := (hasDerivAt_inv ht0.ne').const_mul _
    have d2 : HasDerivAt (fun y : ℝ => -(1 / 2) * (y⁻¹ * y⁻¹))
        (-(1 / 2) * (-(t ^ 2)⁻¹ * t⁻¹ + t⁻¹ * -(t ^ 2)⁻¹)) t :=
      ((hasDerivAt_inv ht0.ne').mul (hasDerivAt_inv ht0.ne')).const_mul _
    have d3 : HasDerivAt (fun y : ℝ => (Real.log (y + 2 * a) - Real.log y) / (2 * a) ^ 2)
        ((1 / (t + 2 * a) - t⁻¹) / (2 * a) ^ 2) t :=
      ((((hasDerivAt_id' (x := t)).add_const (2 * a)).log h1.ne').sub
        (Real.hasDerivAt_log ht0.ne')).div_const _
    refine ((d1.add d2).add d3).congr_deriv ?_
    rw [profileDiff_of_le ha hat, show a - a = 0 from by ring, add_zero,
      show a + a = 2 * a from by ring]
    field_simp
    ring
  have hlim : Tendsto (fun y : ℝ => (1 / a - 1 / (2 * a)) * y⁻¹ + -(1 / 2) * (y⁻¹ * y⁻¹)
      + (Real.log (y + 2 * a) - Real.log y) / (2 * a) ^ 2) atTop (𝓝 0) := by
    have t1 : Tendsto (fun y : ℝ => (1 / a - 1 / (2 * a)) * y⁻¹) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (1 / a - 1 / (2 * a))
    have t2 : Tendsto (fun y : ℝ => -(1 / 2) * (y⁻¹ * y⁻¹)) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.mul tendsto_inv_atTop_zero).const_mul (-(1 / 2) : ℝ)
    have t3 := (tendsto_log_add_sub_log (2 * a)).div_const ((2 * a) ^ 2)
    rw [zero_div] at t3
    simpa using (t1.add t2).add t3
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_profileDiff_Ioi ha ha) hlim]
  show (0 : ℝ) - ((1 / a - 1 / (2 * a)) * a⁻¹ + -(1 / 2) * (a⁻¹ * a⁻¹)
      + (Real.log (a + 2 * a) - Real.log a) / (2 * a) ^ 2) = _
  rw [show a + 2 * a = 3 * a from by ring]
  field_simp
  ring

/-! ### The closed form and its antisymmetry -/

private theorem integral_profileDiff_eq_add {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t : ℝ, profileDiff a b t
      = 2 * ((∫ t in Ioc 0 a, profileDiff a b t) + ∫ t in Ioi a, profileDiff a b t) := by
  rw [CenteredMaximal.integral_of_even (profileDiff_neg_right a b)
    (integrableOn_profileDiff_Ioi_zero ha hb), ← Ioc_union_Ioi_eq_Ioi ha.le,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (integrableOn_profileDiff_Ioc ha hb) (integrableOn_profileDiff_Ioi ha hb)]

/-- On the diagonal the two half-line pieces cancel. -/
theorem integral_profileDiff_self {a : ℝ} (ha : 0 < a) : ∫ t : ℝ, profileDiff a a t = 0 := by
  have ha' : a ≠ 0 := ha.ne'
  rw [integral_profileDiff_eq_add ha ha, integral_profileDiff_Ioc ha ha,
    integral_profileDiff_Ioi_self ha, show 2 * a + a = 3 * a from by ring]
  field_simp
  ring

/-- **The closed form of the jump integral of the profile.** On the diagonal `a = b` both
`1 / (b − a)²` and `4 / ((b − a) (a + b))` are `0` by Lean's convention for division by zero, and
the logarithm vanishes, so the formula also reads correctly there. -/
theorem integral_profileDiff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t : ℝ, profileDiff a b t
      = 2 * (Real.log a - Real.log b) * (1 / (a + b) ^ 2 + 1 / (b - a) ^ 2)
        + 4 / ((b - a) * (a + b)) := by
  rcases eq_or_ne a b with rfl | hab
  · rw [integral_profileDiff_self ha]
    simp
  · have hd : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    have hs : a + b ≠ 0 := ne_of_gt (by linarith)
    have ha' : a ≠ 0 := ha.ne'
    rw [integral_profileDiff_eq_add ha hb, integral_profileDiff_Ioc ha hb,
      integral_profileDiff_Ioi ha hb hab]
    field_simp
    ring

/-- **The antisymmetry.** The two coordinate directions at `(a, b)` contribute opposite jump
integrals, which is the one-dimensional heart of the harmonicity of the potential. -/
theorem integral_profileDiff_antisymm {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ, profileDiff a b t) + ∫ t : ℝ, profileDiff b a t = 0 := by
  rw [integral_profileDiff ha hb, integral_profileDiff hb ha]
  rcases eq_or_ne a b with rfl | hab
  · simp
  · have hd : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
    have hd' : a - b ≠ 0 := sub_ne_zero.2 hab
    have hs : a + b ≠ 0 := ne_of_gt (by linarith)
    have hs' : b + a ≠ 0 := ne_of_gt (by linarith)
    field_simp
    ring

/-! ### The two-dimensional statement -/

private theorem abs_rpow_neg_two (t : ℝ) : |t| ^ (-(1 + 1) : ℝ) = 1 / t ^ 2 := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [abs_zero, Real.zero_rpow (by norm_num)]
    norm_num
  · rw [show (-(1 + 1) : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (abs_nonneg t),
      Real.rpow_natCast, sq_abs, one_div]

private theorem diamondNorm_eq_abs_add (z : Fin 2 → ℝ) (j : Fin 2) :
    diamondNorm z = |z j| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem diamondNorm_add_single (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z + s • Pi.single j 1) = |z j + s| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

/-- Each coordinate direction contributes the corresponding one-dimensional profile integral. -/
private theorem integral_secondDiff_potential (z : Fin 2 → ℝ) (j : Fin 2) :
    ∫ t : ℝ, secondDiff potential j z t * |t| ^ (-(1 + 1) : ℝ)
      = (2 * Real.pi)⁻¹ * ∫ t : ℝ, profileDiff |z j| |z (j + 1)| t := by
  have key : ∀ t : ℝ, secondDiff potential j z t * |t| ^ (-(1 + 1) : ℝ)
      = (2 * Real.pi)⁻¹ * profileDiff |z j| |z (j + 1)| t := by
    intro t
    have h1 : potential (z + t • Pi.single j 1)
        = (2 * Real.pi)⁻¹ * (|z j + t| + |z (j + 1)|)⁻¹ := by
      rw [potential, diamondNorm_add_single, one_div, mul_inv]
    have h2 : potential (z - t • Pi.single j 1)
        = (2 * Real.pi)⁻¹ * (|z j - t| + |z (j + 1)|)⁻¹ := by
      rw [sub_eq_add_neg, ← neg_smul, potential, diamondNorm_add_single, ← sub_eq_add_neg,
        one_div, mul_inv]
    have h3 : potential z = (2 * Real.pi)⁻¹ * (|z j| + |z (j + 1)|)⁻¹ := by
      rw [potential, diamondNorm_eq_abs_add z j, one_div, mul_inv]
    rw [secondDiff, h1, h2, h3, abs_rpow_neg_two, ← profileDiff_abs_left]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall key), integral_const_mul]

/-- **The potential is generator-harmonic off the axes.** For `z` with both coordinates nonzero
the two coordinate directions contribute opposite one-dimensional jump integrals, so the Cauchy
jump generator of the potential kernel vanishes at `z`. -/
theorem jumpGen_potential_eq_zero {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) :
    jumpGen 1 potential z = 0 := by
  have e0 := integral_secondDiff_potential z 0
  have e1 := integral_secondDiff_potential z 1
  rw [show (0 : Fin 2) + 1 = 1 from by decide] at e0
  rw [show (1 : Fin 2) + 1 = 0 from by decide] at e1
  unfold jumpGen
  rw [Fin.sum_univ_two, e0, e1, ← mul_add,
    integral_profileDiff_antisymm (abs_pos.2 h0) (abs_pos.2 h1), mul_zero]

/-- **The affine form needed by the kernel certificate.** A constant has vanishing second
differences and the generator is homogeneous, so `c₁ G + c₂` is generator-harmonic off the axes
along with `G`. -/
theorem jumpGen_affine_potential_eq_zero {c₁ c₂ : ℝ} {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0)
    (h1 : z 1 ≠ 0) : jumpGen 1 (fun w => c₁ * potential w + c₂) z = 0 := by
  have key : ∀ (j : Fin 2) (t : ℝ),
      secondDiff (fun w => c₁ * potential w + c₂) j z t * |t| ^ (-(1 + 1) : ℝ)
        = c₁ * (secondDiff potential j z t * |t| ^ (-(1 + 1) : ℝ)) := by
    intro j t
    simp only [secondDiff]
    ring
  have h : jumpGen 1 (fun w => c₁ * potential w + c₂) z = c₁ * jumpGen 1 potential z := by
    unfold jumpGen
    simp only [key, integral_const_mul, Finset.mul_sum]
  rw [h, jumpGen_potential_eq_zero h0 h1, mul_zero]

end CenteredMaximal.Cauchy

end

end
