/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.Constants

/-!
# Reduction of ball averages to a kernel maximal operator

The kernel is normalized by the volume of the ball at each scale. Thus a kernel at least one on
the unit Euclidean ball dominates each ball average with no additional scale factor.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace CenteredMaximal.Ball

variable {d : ℕ}

/-- The maximal operator formed from all normalized dilates of a nonnegative kernel `K`. -/
def kernelMaximal (K : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), ∫⁻ y,
    (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ

/-- A weak type bound for the normalized dilation maximal operator of `K`. -/
def IsKernelWeakTypeBound (K : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < kernelMaximal K f x} ≤ C * ∫⁻ x, ‖f x‖ₑ

/-- Every dilated kernel integral is at most the kernel maximal operator. -/
theorem le_kernelMaximal (K : EuclideanSpace ℝ (Fin d) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d))
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
      kernelMaximal K f x :=
  le_iSup₂ (f := fun r (_ : 0 < r) ↦
    ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) r hr

/-- A kernel at least one on the unit ball dominates the centred ball maximal function. -/
theorem ballMaximalFunction_le_kernelMaximal
    {K : EuclideanSpace ℝ (Fin d) → ℝ≥0∞}
    (hK : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1, 1 ≤ K z)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    ballMaximalFunction f x ≤ kernelMaximal K f x := by
  refine iSup₂_le fun r hr ↦ ?_
  calc
    (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ
        ≤ ∫⁻ y in ball x r, (volume (ball x r))⁻¹ * ‖f y‖ₑ :=
          lintegral_const_mul_le _ _
    _ ≤ ∫⁻ y in ball x r,
          (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ := by
      refine setLIntegral_mono' measurableSet_ball fun y hy ↦ ?_
      have hz : r⁻¹ • (x - y) ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
        rw [mem_ball_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr.le]
        have hxy : ‖x - y‖ < r := by rwa [mem_ball', dist_eq_norm] at hy
        calc
          r⁻¹ * ‖x - y‖ = ‖x - y‖ / r := by ring
          _ < 1 := (div_lt_one hr).2 hxy
      calc
        _ = (volume (ball x r))⁻¹ * 1 * ‖f y‖ₑ := by simp
        _ ≤ (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ := by
          gcongr
          exact hK _ hz
    _ ≤ ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ :=
      setLIntegral_le_lintegral _ _
    _ ≤ kernelMaximal K f x := le_kernelMaximal K f x hr

/-- A weak type bound for the kernel maximal operator gives the same ball bound. -/
theorem isBallWeakTypeBound_of_isKernelWeakTypeBound
    {K : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} {C : ℝ≥0∞}
    (hK : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1, 1 ≤ K z)
    (h : IsKernelWeakTypeBound K C) : IsBallWeakTypeBound d C := by
  intro f hf α
  have hsub : {x | α < ballMaximalFunction f x} ⊆
      {x | α < kernelMaximal K f x} := fun x hx ↦
    lt_of_lt_of_le hx (ballMaximalFunction_le_kernelMaximal hK f x)
  exact (mul_le_mul_right (measure_mono hsub) α).trans (h f hf α)

/-- An admissible kernel bound gives an upper bound for the optimal ball constant. -/
theorem ballWeakTypeConstant_le_of_isKernelWeakTypeBound
    {K : EuclideanSpace ℝ (Fin d) → ℝ≥0∞} {C : ℝ≥0∞}
    (hK : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1, 1 ≤ K z)
    (h : IsKernelWeakTypeBound K C) : ballWeakTypeConstant d ≤ C :=
  ballWeakTypeConstant_le (isBallWeakTypeBound_of_isKernelWeakTypeBound hK h)

end CenteredMaximal.Ball
