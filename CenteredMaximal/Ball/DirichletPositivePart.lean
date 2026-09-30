/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.DirichletSmoothComposition
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

/-!
# Smooth approximation of the positive part

The scalar maps `smoothPositive ε` are smooth, one-Lipschitz, and fix zero for `ε > 0`.
As `ε` tends to zero, their values approach `t ↦ max t 0`, while their derivatives
approach the indicator of `t > 0`, including derivative zero at `t = 0`. This choice
removes the need for a separate theorem that Sobolev gradients vanish on level sets.
-/

@[expose] public section
open MeasureTheory Set Filter Topology
open scoped RealInnerProductSpace ENNReal NNReal
noncomputable section
namespace CenteredMaximal.Ball.DirichletSobolev

/-- A smooth one-Lipschitz regularization of the positive part, adjusted so that its
derivative at zero is zero. -/
def smoothPositive (ε t : ℝ) : ℝ :=
  (t + Real.sqrt (t ^ 2 + ε ^ 2) - ε - ε * t / Real.sqrt (t ^ 2 + ε ^ 2)) / 2

private theorem smoothPositive_arg_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 < t ^ 2 + ε ^ 2 := by positivity

private theorem smoothPositive_sqrt_pos {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 < Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_pos.mpr (smoothPositive_arg_pos hε t)

theorem smoothPositive_contDiff {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothPositive ε) := by
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => Real.sqrt (t ^ 2 + ε ^ 2)) :=
    ((contDiff_id.pow 2).add contDiff_const).sqrt
      (fun t => (smoothPositive_arg_pos hε t).ne')
  have hr : ContDiff ℝ (⊤ : ℕ∞)
      (fun t : ℝ => ε * t / Real.sqrt (t ^ 2 + ε ^ 2)) :=
    (contDiff_const.mul contDiff_id).div hs
      (fun t => (smoothPositive_sqrt_pos hε t).ne')
  unfold smoothPositive
  fun_prop

private theorem smoothPositive_hasDerivAt {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    HasDerivAt (smoothPositive ε)
      ((1 + t / Real.sqrt (t ^ 2 + ε ^ 2) -
        ε ^ 3 / Real.sqrt (t ^ 2 + ε ^ 2) ^ 3) / 2) t := by
  let s : ℝ := Real.sqrt (t ^ 2 + ε ^ 2)
  have hspos : 0 < s := smoothPositive_sqrt_pos hε t
  have hsne : s ≠ 0 := hspos.ne'
  have hsq : s ^ 2 = t ^ 2 + ε ^ 2 := Real.sq_sqrt (smoothPositive_arg_pos hε t).le
  have harg : HasDerivAt (fun y : ℝ => y ^ 2 + ε ^ 2) (2 * t) t := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using
      (hasDerivAt_pow 2 t).add_const (ε ^ 2)
  have hs : HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + ε ^ 2)) (t / s) t := by
    convert harg.sqrt (smoothPositive_arg_pos hε t).ne' using 1
    change t / s = 2 * t / (2 * s)
    field_simp
  have hnum : HasDerivAt (fun y : ℝ => ε * y) ε t := by
    simpa using (hasDerivAt_id t).const_mul ε
  have hq := hnum.div hs hsne
  have hfull := (((hasDerivAt_id t).add hs).sub_const ε).sub hq |>.div_const 2
  change HasDerivAt (smoothPositive ε)
    ((1 + t / s - (ε * s - ε * t * (t / s)) / s ^ 2) / 2) t at hfull
  refine hfull.congr_deriv ?_
  change (1 + t / s - (ε * s - ε * t * (t / s)) / s ^ 2) / 2 =
    (1 + t / s - ε ^ 3 / s ^ 3) / 2
  field_simp
  nlinarith [hsq]

theorem deriv_smoothPositive {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    deriv (smoothPositive ε) t =
      (1 + t / Real.sqrt (t ^ 2 + ε ^ 2) -
        ε ^ 3 / Real.sqrt (t ^ 2 + ε ^ 2) ^ 3) / 2 :=
  (smoothPositive_hasDerivAt hε t).deriv

theorem smoothPositive_deriv_bound {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ‖deriv (smoothPositive ε) t‖ ≤ 1 := by
  let s : ℝ := Real.sqrt (t ^ 2 + ε ^ 2)
  have hspos : 0 < s := smoothPositive_sqrt_pos hε t
  have hsq : s ^ 2 = t ^ 2 + ε ^ 2 := Real.sq_sqrt (smoothPositive_arg_pos hε t).le
  have htsq : t ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg ε]
  have htlo : -s ≤ t := by nlinarith [htsq]
  have hthi : t ≤ s := by nlinarith [htsq]
  have hεsq : ε ^ 2 ≤ s ^ 2 := by nlinarith [sq_nonneg t]
  have hεle : ε ≤ s := by nlinarith [hεsq]
  have hqlo : -1 ≤ t / s := (le_div_iff₀ hspos).mpr (by nlinarith)
  have hqhi : t / s ≤ 1 := (div_le_iff₀ hspos).mpr (by nlinarith)
  have hcubelo : 0 ≤ ε ^ 3 / s ^ 3 := by positivity
  have hcubehi : ε ^ 3 / s ^ 3 ≤ 1 :=
    (div_le_one (pow_pos hspos 3)).mpr (pow_le_pow_left₀ hε.le hεle 3)
  rw [deriv_smoothPositive hε]
  simp only [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> dsimp [s] at * <;> linarith

theorem smoothPositive_zero {ε : ℝ} (hε : 0 < ε) : smoothPositive ε 0 = 0 := by
  simp [smoothPositive, Real.sqrt_sq hε.le]

theorem smoothPositive_lipschitz {ε : ℝ} (hε : 0 < ε) :
    LipschitzWith 1 (smoothPositive ε) := by
  apply lipschitzWith_of_nnnorm_deriv_le
    ((smoothPositive_contDiff hε).differentiable (by simp))
  intro t
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  exact smoothPositive_deriv_bound hε t

theorem smoothPositive_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => smoothPositive (1 / (n + 1 : ℝ)) t)
      atTop (𝓝 (max t 0)) := by
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  by_cases ht : t = 0
  · subst t
    have hzero : ∀ n, smoothPositive (ε n) 0 = 0 := fun n =>
      smoothPositive_zero (by positivity)
    simp only [max_self]
    change Tendsto (fun n => smoothPositive (ε n) 0) atTop (𝓝 0)
    simp_rw [hzero]
    exact tendsto_const_nhds
  · have harg : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have hcont : ContinuousAt (fun e : ℝ => smoothPositive e t) 0 := by
      unfold smoothPositive
      fun_prop (disch := positivity)
    have hlim := hcont.tendsto.comp hε0
    have hval : smoothPositive 0 t = max t 0 := by
      simp only [smoothPositive, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
        zero_mul, zero_div, sub_zero, add_zero]
      rw [Real.sqrt_sq_eq_abs]
      rcases lt_or_gt_of_ne ht with hneg | hpos
      · rw [max_eq_right hneg.le, abs_of_neg hneg]
        ring
      · rw [max_eq_left hpos.le, abs_of_pos hpos]
        ring
    simpa only [Function.comp_def, ε, hval] using hlim

theorem smoothPositive_deriv_tendsto (t : ℝ) :
    Tendsto (fun n : ℕ => deriv (smoothPositive (1 / (n + 1 : ℝ))) t)
      atTop (𝓝 (if 0 < t then 1 else 0)) := by
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  by_cases ht : t = 0
  · subst t
    have hzero : ∀ n, deriv (smoothPositive (ε n)) 0 = 0 := by
      intro n
      rw [deriv_smoothPositive (hεpos n)]
      simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, zero_div,
        Real.sqrt_sq (hεpos n).le]
      rw [div_self (pow_ne_zero 3 (hεpos n).ne')]
      norm_num
    simp only [lt_self_iff_false, ↓reduceIte]
    change Tendsto (fun n => deriv (smoothPositive (ε n)) 0) atTop (𝓝 0)
    simp_rw [hzero]
    exact tendsto_const_nhds
  · have harg : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    let Q : ℝ → ℝ := fun e =>
      (1 + t / Real.sqrt (t ^ 2 + e ^ 2) -
        e ^ 3 / Real.sqrt (t ^ 2 + e ^ 2) ^ 3) / 2
    have hcont : ContinuousAt Q 0 := by
      dsimp [Q]
      fun_prop (disch := positivity)
    have hlim := hcont.tendsto.comp hε0
    have hval : Q 0 = if 0 < t then 1 else 0 := by
      simp only [Q, zero_pow (by norm_num : (3 : ℕ) ≠ 0), zero_div, sub_zero,
        zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
      rw [Real.sqrt_sq_eq_abs]
      split_ifs with hpos
      · rw [abs_of_pos hpos]
        field_simp
        norm_num
      · have hneg : t < 0 := lt_of_le_of_ne (not_lt.mp hpos) ht
        rw [abs_of_neg hneg]
        field_simp
        ring
    have hrewrite : (fun n : ℕ => deriv (smoothPositive (ε n)) t) = Q ∘ ε := by
      funext n
      exact deriv_smoothPositive (hεpos n) t
    change Tendsto (fun n => deriv (smoothPositive (ε n)) t) atTop _
    rw [hrewrite]
    simpa only [hval] using hlim

end CenteredMaximal.Ball.DirichletSobolev
