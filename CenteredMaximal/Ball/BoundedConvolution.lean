/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.LocalMollifier

/-!
# An a.e. bound passes through a normalized positive convolution

The source of the obstacle equation is capped only almost everywhere. Translation
invariance of Lebesgue measure lets a normalized nonnegative mollifier preserve
that cap at every convolution center.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Convolution

namespace CenteredMaximal.Ball

/-- A normalized nonnegative integrable convolution kernel preserves an a.e.
absolute bound, pointwise at every center. -/
theorem norm_convolution_le_of_ae_bound (n : ℕ)
    (φ g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : Integrable φ) (hφnonneg : ∀ y, 0 ≤ φ y)
    (hφone : (∫ y, φ y) = 1)
    (hg : AEStronglyMeasurable g volume)
    (B : ℝ)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B)
    (x : EuclideanSpace ℝ (Fin n)) :
    ‖(φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x‖ ≤ B := by
  have hBgcomp : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ‖g (x - y)‖ ≤ B :=
    (quasiMeasurePreserving_sub_left_of_right_invariant volume x).ae hBg
  have hmeas : AEStronglyMeasurable (fun y ↦ φ y * g (x - y)) volume := by
    simpa only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] using
      (hφ.aestronglyMeasurable.convolution_integrand_snd
        (ContinuousLinearMap.lsmul ℝ ℝ) hg x)
  have hbound : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ‖φ y * g (x - y)‖ ≤ B * ‖φ y‖ := by
    filter_upwards [hBgcomp] with y hy
    calc
      ‖φ y * g (x - y)‖ = ‖φ y‖ * ‖g (x - y)‖ := norm_mul _ _
      _ ≤ ‖φ y‖ * B := mul_le_mul_of_nonneg_left hy (norm_nonneg _)
      _ = B * ‖φ y‖ := mul_comm _ _
  have hint : Integrable (fun y ↦ φ y * g (x - y)) :=
    (hφ.norm.const_mul B).mono' hmeas hbound
  have hφnorm : (∫ y, ‖φ y‖) = 1 := by
    convert hφone using 1
    apply integral_congr_ae
    filter_upwards with y
    exact Real.norm_eq_abs (φ y) |>.trans (abs_of_nonneg (hφnonneg y))
  change ‖∫ y, φ y * g (x - y)‖ ≤ B
  calc
    ‖∫ y, φ y * g (x - y)‖ ≤
        ∫ y, ‖φ y * g (x - y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, B * ‖φ y‖ :=
      integral_mono_ae hint.norm (hφ.norm.const_mul B) hbound
    _ = B := by rw [integral_const_mul, hφnorm, mul_one]

end CenteredMaximal.Ball
