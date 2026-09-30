/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.KernelScaling
public import CenteredMaximal.Ball.PlanarMass

/-!
# Normalized mass of the planar Green kernel

The planar kernel has mass `πe`. Normalizing its dilates by the area of each disc makes their mass
exactly `e`, for every center and positive radius.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace CenteredMaximal.Ball

/-- The planar Green kernel has mass `e` after division by the area of the unit disc. -/
theorem planarKernel_unit_mass :
    (volume (ball (0 : EuclideanSpace ℝ (Fin 2)) 1))⁻¹ *
        (∫⁻ z : EuclideanSpace ℝ (Fin 2), planarKernel z) =
      ENNReal.ofReal (Real.exp 1) := by
  rw [planarKernel_mass, EuclideanSpace.volume_ball_fin_two]
  simp only [ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.ofReal_mul Real.pi_nonneg]
  exact ENNReal.inv_mul_cancel_left (by positivity) ENNReal.ofReal_ne_top

/-- Every normalized dilation of the planar Green kernel has mass `e`. -/
theorem planarKernel_normalized_mass (x : EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ y, (volume (ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))) =
      ENNReal.ofReal (Real.exp 1) := by
  rw [lintegral_normalized_kernel_eq_unit_mass 2 (by omega) planarKernel x hr]
  exact planarKernel_unit_mass

end CenteredMaximal.Ball
