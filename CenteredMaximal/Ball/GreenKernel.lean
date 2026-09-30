/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.Comparison

/-!
# Logarithmic and Newtonian comparison kernels

The kernels are normalized to equal one on the unit sphere. The `ENNReal` value at the origin
records their singularity; the origin has zero Lebesgue measure.
-/

@[expose] public section

noncomputable section

open Metric
open scoped ENNReal

namespace CenteredMaximal.Ball

/-- The truncated logarithmic kernel in the plane, extended by infinity at the origin. -/
def planarKernel (z : EuclideanSpace ℝ (Fin 2)) : ℝ≥0∞ :=
  if z = 0 then ∞ else ENNReal.ofReal (1 - 2 * Real.log ‖z‖)

/-- The truncated Newtonian kernel in dimension `n ≥ 3`, extended by infinity at the origin. -/
def newtonianKernel (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  if z = 0 then ∞ else
    ENNReal.ofReal (((n : ℝ) * ‖z‖ ^ ((2 : ℝ) - (n : ℝ)) - 2) / ((n : ℝ) - 2))

theorem measurable_planarKernel : Measurable planarKernel := by
  unfold planarKernel
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

theorem measurable_newtonianKernel (n : ℕ) : Measurable (newtonianKernel n) := by
  unfold newtonianKernel
  exact Measurable.ite (measurableSet_singleton 0) measurable_const (by fun_prop)

theorem one_le_planarKernel_on_unit_ball
    (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    1 ≤ planarKernel z := by
  by_cases hzero : z = 0
  · simp [planarKernel, hzero]
  have hnorm : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hnorm₀ : 0 < ‖z‖ := norm_pos_iff.mpr hzero
  have hlog : Real.log ‖z‖ ≤ 0 := Real.log_nonpos hnorm₀.le hnorm.le
  have hreal : (1 : ℝ) ≤ 1 - 2 * Real.log ‖z‖ := by nlinarith
  simpa [planarKernel, hzero] using ENNReal.ofReal_le_ofReal hreal

theorem planarKernel_eq_zero_of_radius_le (z : EuclideanSpace ℝ (Fin 2))
    (hz : planarGreenRadius ≤ ‖z‖) : planarKernel z = 0 := by
  have hR : 0 < planarGreenRadius := by unfold planarGreenRadius; positivity
  have hnorm : 0 < ‖z‖ := hR.trans_le hz
  have hzero : z ≠ 0 := (norm_pos_iff.mp hnorm)
  have hlog : Real.log planarGreenRadius ≤ Real.log ‖z‖ := Real.log_le_log hR hz
  have hlogR : Real.log planarGreenRadius = 1 / 2 := by
    simp [planarGreenRadius, Real.log_sqrt (Real.exp_pos 1).le]
  have hnonpos : 1 - 2 * Real.log ‖z‖ ≤ 0 := by linarith
  simp [planarKernel, hzero, ENNReal.ofReal_eq_zero.mpr hnonpos]

theorem one_le_newtonianKernel_on_unit_ball (n : ℕ) (hn : 3 ≤ n)
    (z : EuclideanSpace ℝ (Fin n)) (hz : z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1) :
    1 ≤ newtonianKernel n z := by
  by_cases hzero : z = 0
  · simp [newtonianKernel, hzero]
  have hnorm : ‖z‖ < 1 := by simpa [mem_ball_zero_iff] using hz
  have hnorm₀ : 0 < ‖z‖ := norm_pos_iff.mpr hzero
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hexp : (2 : ℝ) - (n : ℝ) ≤ 0 := by linarith
  have hpow : 1 ≤ ‖z‖ ^ ((2 : ℝ) - (n : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hnorm₀ hnorm.le hexp
  have hden : 0 < (n : ℝ) - 2 := by linarith
  have hreal : (1 : ℝ) ≤
      ((n : ℝ) * ‖z‖ ^ ((2 : ℝ) - (n : ℝ)) - 2) / ((n : ℝ) - 2) := by
    apply (le_div_iff₀ hden).2
    nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ)) (sub_nonneg.mpr hpow)]
  simpa [newtonianKernel, hzero] using ENNReal.ofReal_le_ofReal hreal

theorem newtonianKernel_eq_zero_of_radius_le (n : ℕ) (hn : 3 ≤ n)
    (z : EuclideanSpace ℝ (Fin n)) (hz : greenRadius n ≤ ‖z‖) :
    newtonianKernel n z = 0 := by
  have hR : 0 < greenRadius n := greenRadius_pos n hn
  have hnorm : 0 < ‖z‖ := hR.trans_le hz
  have hzero : z ≠ 0 := norm_pos_iff.mp hnorm
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hexp : (2 : ℝ) - (n : ℝ) ≤ 0 := by linarith
  have hRpow : greenRadius n ^ ((2 : ℝ) - (n : ℝ)) = 2 / (n : ℝ) := by
    calc
      _ = (greenRadius n ^ ((n : ℝ) - 2))⁻¹ := by
        rw [show (2 : ℝ) - (n : ℝ) = -((n : ℝ) - 2) by ring]
        exact Real.rpow_neg hR.le _
      _ = ((n : ℝ) / 2)⁻¹ := by rw [greenRadius_rpow_sub_two n hn]
      _ = 2 / (n : ℝ) := by field_simp
  have hpow : ‖z‖ ^ ((2 : ℝ) - (n : ℝ)) ≤ 2 / (n : ℝ) :=
    (Real.rpow_le_rpow_of_nonpos hR hz hexp).trans_eq hRpow
  have hprod : (n : ℝ) * ‖z‖ ^ ((2 : ℝ) - (n : ℝ)) ≤ 2 := by
    calc
      _ ≤ (n : ℝ) * (2 / (n : ℝ)) := mul_le_mul_of_nonneg_left hpow (by linarith)
      _ = 2 := by field_simp
  have hnonpos :
      ((n : ℝ) * ‖z‖ ^ ((2 : ℝ) - (n : ℝ)) - 2) / ((n : ℝ) - 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp [newtonianKernel, hzero, ENNReal.ofReal_eq_zero.mpr hnonpos]

/-- The planar challenge follows from the weak type estimate for the logarithmic kernel. -/
theorem ballWeakTypeConstant_two_le_exp_of_planarKernel_bound
    (h : IsKernelWeakTypeBound planarKernel (ENNReal.ofReal (Real.exp 1))) :
    ballWeakTypeConstant 2 ≤ ENNReal.ofReal (Real.exp 1) :=
  ballWeakTypeConstant_le_of_isKernelWeakTypeBound one_le_planarKernel_on_unit_ball h

/-- The higher-dimensional challenge follows from the weak type estimate for the Newtonian
kernel. -/
theorem ballWeakTypeConstant_le_rpow_of_newtonianKernel_bound (n : ℕ) (hn : 3 ≤ n)
    (h : IsKernelWeakTypeBound (newtonianKernel n) (ENNReal.ofReal (greenBound n))) :
    ballWeakTypeConstant n ≤
      ENNReal.ofReal (((n : ℝ) / 2) ^ ((n : ℝ) / ((n : ℝ) - 2))) := by
  simpa only [greenBound] using
    ballWeakTypeConstant_le_of_isKernelWeakTypeBound
      (one_le_newtonianKernel_on_unit_ball n hn) h

end CenteredMaximal.Ball
