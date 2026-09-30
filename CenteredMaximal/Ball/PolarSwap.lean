/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.GreenIdentity

/-!
# Swapping radial and angular integration

The Green pairing needs polar coordinates with radius integrated on the outside. This file
derives that orientation directly from the measure-preserving polar homeomorphism, so Fubini
applies to every integrable signed test function.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace CenteredMaximal.Ball

private theorem integral_volumeIoiPow_outer (k : ℕ) (h : ℝ → ℝ) :
    (∫ s : Set.Ioi (0 : ℝ), h (s : ℝ) ∂Measure.volumeIoiPow k) =
      ∫ s in Set.Ioi (0 : ℝ), s ^ k * h s := by
  rw [Measure.volumeIoiPow]
  change (∫ s : Set.Ioi (0 : ℝ), h (s : ℝ) ∂
    (Measure.comap Subtype.val volume).withDensity
      (fun r ↦ ((Real.toNNReal ((r : ℝ) ^ k) : NNReal) : ENNReal))) = _
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap (hs := measurableSet_Ioi)
      (f := fun s : ℝ ↦ (s ^ k).toNNReal • h s)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    change (s ^ k).toNNReal • h s = s ^ k * h s
    rw [NNReal.smul_def, Real.coe_toNNReal (s ^ k) (pow_nonneg hs.out.le _), smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

/-- Polar integration with the radial variable outside the angular integral. The signed
integrability follows from integrability of the original function on Euclidean space. -/
theorem integral_polar_ball_swapped (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : Integrable F) :
    (∫ y, F y) =
      ∫ s in Set.Ioi (0 : ℝ), s ^ (n - 1) *
        (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          F (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let μ : Measure E := volume
  let P := homeomorphUnitSphereProd E
  have hcomp : Integrable (fun z : ({0}ᶜ : Set E) ↦ F (x + z.1))
      (μ.comap Subtype.val) := by
    exact (integrableOn_iff_comap_subtypeVal
      (measurableSet_singleton (0 : E)).compl).mp
      (hF.comp_add_left x).integrableOn
  have hprod : Integrable (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) ↦
      F (x + (P.symm p).1))
      (μ.toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
    have h := μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
      (Homeomorph.measurableEmbedding P)
      (g := fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) ↦
        F (x + (P.symm p).1))
    have hp := h.mp (by
      convert hcomp using 1
      funext z
      change F (x + (P.symm (P z)).1) = F (x + z.1)
      simp)
    simpa only [E, finrank_euclideanSpace_fin] using hp
  calc
    (∫ y, F y) = ∫ z, F (x + z) := by
      rw [integral_add_left_eq_self F x]
    _ = ∫ z : ({0}ᶜ : Set E), F (x + z.1) ∂(μ.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton (0 : E)).compl
        (fun z : E ↦ F (x + z)), restrict_compl_singleton]
    _ = ∫ p, F (x + (P.symm p).1) ∂
        (μ.toSphere.prod (Measure.volumeIoiPow (n - 1))) := by
      simpa [P, E, finrank_euclideanSpace_fin] using
        μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding P)
        (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) ↦ F (x + (P.symm p).1))
    _ = ∫ s : Set.Ioi (0 : ℝ),
        ∫ ω : Metric.sphere (0 : E) 1,
          F (x + (s : ℝ) • (ω : E)) ∂μ.toSphere
          ∂Measure.volumeIoiPow (n - 1) := by
      rw [integral_prod_symm _ hprod]
      simp only [P, homeomorphUnitSphereProd_symm_apply_coe]
    _ = _ := by
      simpa only [E, μ] using
        integral_volumeIoiPow_outer (n - 1)
          (fun s : ℝ ↦ ∫ ω : Metric.sphere (0 : E) 1,
            F (x + s • (ω : E)) ∂μ.toSphere)

/-- Move a signed radial factor outside both integrals in the swapped polar formula. -/
theorem integral_radial_mul_polar_swapped (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin n)) (φ : ℝ → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Integrable (fun y ↦ φ ‖y - x‖ * g y)) :
    (∫ y, φ ‖y - x‖ * g y) =
      ∫ s in Set.Ioi (0 : ℝ), s ^ (n - 1) * φ s *
        (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          g (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) := by
  rw [integral_polar_ball_swapped n x _ hg]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have hnorm (ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
      ‖x + s • (ω : EuclideanSpace ℝ (Fin n)) - x‖ = s := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs.out]
    have hω : ‖(ω : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      simpa only [Metric.mem_sphere, dist_zero_right] using ω.property
    simp [hω]
  have hint : (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        φ ‖x + s • (ω : EuclideanSpace ℝ (Fin n)) - x‖ *
          g (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) =
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        φ s * g (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere) := by
    apply integral_congr_ae
    filter_upwards with ω
    rw [hnorm]
  change s ^ (n - 1) *
    (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      φ ‖x + s • (ω : EuclideanSpace ℝ (Fin n)) - x‖ *
        g (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) = _
  rw [hint, integral_const_mul]
  ring

/-- Restrict the radial integral to the support radius of a radial profile. -/
theorem integral_radial_mul_polar_swapped_of_support (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin n)) (R : ℝ) (φ : ℝ → ℝ)
    (hφ : ∀ s, R ≤ s → φ s = 0)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Integrable (fun y ↦ φ ‖y - x‖ * g y)) :
    (∫ y, φ ‖y - x‖ * g y) =
      ∫ s in Set.Ioo (0 : ℝ) R, s ^ (n - 1) * φ s *
        (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          g (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) := by
  rw [integral_radial_mul_polar_swapped n x φ g hg]
  let H : ℝ → ℝ := fun s ↦ s ^ (n - 1) * φ s *
    (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      g (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere))
  change (∫ s in Set.Ioi (0 : ℝ), H s) = ∫ s in Set.Ioo (0 : ℝ) R, H s
  calc
    (∫ s in Set.Ioi (0 : ℝ), H s) =
        ∫ s in Set.Ioi (0 : ℝ), (Set.Iio R).indicator H s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s _
      by_cases hsR : s < R
      · simp only [Set.indicator_of_mem (show s ∈ Set.Iio R from hsR)]
      · have hs0 : H s = 0 := by simp [H, hφ s (le_of_not_gt hsR)]
        simp [Set.indicator_of_notMem (show s ∉ Set.Iio R from hsR), hs0]
    _ = ∫ s in Set.Ioo (0 : ℝ) R, H s := by
      rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]

end CenteredMaximal.Ball
