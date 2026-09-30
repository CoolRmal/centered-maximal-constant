/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.GreenKernel
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Mass of the planar logarithmic comparison kernel

The layer cake formula reduces the integral to the areas of the kernel's superlevel discs.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped ENNReal

noncomputable section

namespace CenteredMaximal.Ball

private def planarRealKernel (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  max (1 - 2 * Real.log ‖z‖) 0

private theorem level_measure (t : ℝ) (ht : 0 < t) :
    volume {z : EuclideanSpace ℝ (Fin 2) | t < planarRealKernel z} =
      volume (ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.exp ((1 - t) / 2))) := by
  apply measure_congr
  filter_upwards [(volume : Measure (EuclideanSpace ℝ (Fin 2))).ae_ne 0]
    with z hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he : 0 < Real.exp ((1 - t) / 2) := Real.exp_pos _
  change (t < max (1 - 2 * Real.log ‖z‖) 0) =
    (z ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) (Real.exp ((1 - t) / 2)))
  apply propext
  rw [mem_ball_zero_iff]
  simp only [lt_max_iff, not_lt.mpr ht.le, or_false]
  constructor
  · intro h
    apply (Real.log_lt_iff_lt_exp hn).mp
    linarith
  · intro h
    have := (Real.log_lt_iff_lt_exp hn).mpr h
    linarith

private theorem level_measure_exp (t : ℝ) (ht : 0 < t) :
    volume {z : EuclideanSpace ℝ (Fin 2) | t < planarRealKernel z} =
      ENNReal.ofReal (Real.pi * Real.exp (1 - t)) := by
  rw [level_measure t ht, EuclideanSpace.volume_ball_fin_two]
  have hpow : ENNReal.ofReal (Real.exp ((1 - t) / 2)) ^ 2 =
      ENNReal.ofReal (Real.exp (1 - t)) := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hpow]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
  congr 1
  ring

private theorem lintegral_level_exp :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.pi * Real.exp (1 - t))) =
      ENNReal.ofReal (Real.pi * Real.exp 1) := by
  have hfactor : ∀ t : ℝ,
      Real.pi * Real.exp (1 - t) = (Real.pi * Real.exp 1) * Real.exp (-t) := by
    intro t
    rw [show 1 - t = 1 + -t by ring, Real.exp_add]
    ring
  have hint : IntegrableOn (fun t : ℝ => Real.pi * Real.exp (1 - t)) (Ioi 0) := by
    simpa only [hfactor, IntegrableOn] using
      (integrableOn_exp_neg_Ioi 0).const_mul (Real.pi * Real.exp 1)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ => Real.pi * Real.exp (1 - t)) :=
    Filter.Eventually.of_forall fun _ => mul_nonneg Real.pi_nonneg (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  simp_rw [hfactor]
  rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

private theorem planarRealKernel_mass :
    (∫⁻ z : EuclideanSpace ℝ (Fin 2), ENNReal.ofReal (planarRealKernel z)) =
      ENNReal.ofReal (Real.pi * Real.exp 1) := by
  have hnonneg : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2)))] planarRealKernel :=
    Filter.Eventually.of_forall fun z => le_max_right _ _
  have hmeas : AEMeasurable planarRealKernel
      (volume : Measure (EuclideanSpace ℝ (Fin 2))) := by
    unfold planarRealKernel
    fun_prop
  rw [lintegral_eq_lintegral_meas_lt volume hnonneg hmeas]
  calc
    (∫⁻ t in Ioi (0 : ℝ),
      volume {z : EuclideanSpace ℝ (Fin 2) | t < planarRealKernel z}) =
        ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.pi * Real.exp (1 - t)) := by
          refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
          exact level_measure_exp t ht
    _ = _ := lintegral_level_exp

theorem planarKernel_mass :
    (∫⁻ z : EuclideanSpace ℝ (Fin 2), planarKernel z) =
      ENNReal.ofReal (Real.pi * Real.exp 1) := by
  have hAE : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      planarKernel z = ENNReal.ofReal (planarRealKernel z) := by
    filter_upwards [(volume : Measure (EuclideanSpace ℝ (Fin 2))).ae_ne 0] with z hz
    simp [planarKernel, planarRealKernel, hz, ENNReal.ofReal_max]
  rw [lintegral_congr_ae hAE]
  exact planarRealKernel_mass

end CenteredMaximal.Ball
