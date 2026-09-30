/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.CenterLimits

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

/-- The positive part of the planar profile vanishes outside its Green radius. -/
theorem planarGreenProfile_posPart_eq_zero_of_radius_le {s : ℝ}
    (hs : planarGreenRadius ≤ s) : max (planarGreenProfile s) 0 = 0 := by
  have hR : 0 < planarGreenRadius := by unfold planarGreenRadius; positivity
  have hlog : Real.log planarGreenRadius ≤ Real.log s :=
    Real.log_le_log hR hs
  have hlogR : Real.log planarGreenRadius = 1 / 2 := by
    simp [planarGreenRadius, Real.log_sqrt (Real.exp_pos 1).le]
  apply max_eq_right
  unfold planarGreenProfile
  linarith

/-- The positive part of the Newtonian profile vanishes outside its Green radius. -/
theorem newtonianGreenProfile_posPart_eq_zero_of_radius_le
    (n : ℕ) (hn : 3 ≤ n) {s : ℝ} (hs : greenRadius n ≤ s) :
    max (newtonianGreenProfile n s) 0 = 0 := by
  have hR : 0 < greenRadius n := greenRadius_pos n hn
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
  have hpow : s ^ ((2 : ℝ) - (n : ℝ)) ≤ 2 / (n : ℝ) :=
    (Real.rpow_le_rpow_of_nonpos hR hs hexp).trans_eq hRpow
  have hprod : (n : ℝ) * s ^ ((2 : ℝ) - (n : ℝ)) ≤ 2 := by
    calc
      _ ≤ (n : ℝ) * (2 / (n : ℝ)) := mul_le_mul_of_nonneg_left hpow (by linarith)
      _ = 2 := by field_simp
  apply max_eq_right
  unfold newtonianGreenProfile
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)

/-- A bounded measurable function is integrable against the positive part of the planar
Green profile. -/
theorem integrable_planarGreenProfile_posPart_mul_bdd
    (x : EuclideanSpace ℝ (Fin 2))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hg : AEStronglyMeasurable g volume)
    {B : ℝ} (hB : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))), ‖g y‖ ≤ B) :
    Integrable (fun y : EuclideanSpace ℝ (Fin 2) ↦
      max (planarGreenProfile ‖y - x‖) 0 * g y) := by
  let a : ℝ := ((volume (Metric.ball x 1))⁻¹).toReal
  have ha : a ≠ 0 := by
    have hvolpos : 0 < volume (Metric.ball x 1) := measure_ball_pos volume x (by norm_num)
    have hvolfin : volume (Metric.ball x 1) < ∞ := measure_ball_lt_top
    exact (ENNReal.toReal_pos
      (ENNReal.inv_pos.mpr hvolfin.ne).ne'
      (ENNReal.inv_lt_top.mpr hvolpos).ne).ne'
  have hNorm : Integrable (fun y : EuclideanSpace ℝ (Fin 2) ↦
      a * (max (planarGreenProfile ‖y - x‖) 0 * g y)) := by
    apply (integrable_normalized_planarKernel_mul_bdd x (r := 1) (by norm_num) g hg hB).congr
    filter_upwards [normalized_planarKernel_toReal_ae_eq_profile x
      (r := 1) (by norm_num)] with y hy
    simpa only [inv_one, one_smul, div_one, a, mul_assoc] using
      congrArg (fun t : ℝ ↦ t * g y) hy
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr ha) _).mp hNorm

/-- A bounded measurable function is integrable against the positive part of the Newtonian
Green profile. -/
theorem integrable_newtonianGreenProfile_posPart_mul_bdd
    (n : ℕ) (hn : 3 ≤ n) (x : EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : AEStronglyMeasurable g volume)
    {B : ℝ} (hB : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
      max (newtonianGreenProfile n ‖y - x‖) 0 * g y) := by
  letI : NeZero n := ⟨by omega⟩
  let a : ℝ := ((volume (Metric.ball x 1))⁻¹).toReal
  have ha : a ≠ 0 := by
    have hvolpos : 0 < volume (Metric.ball x 1) := measure_ball_pos volume x (by norm_num)
    have hvolfin : volume (Metric.ball x 1) < ∞ := measure_ball_lt_top
    exact (ENNReal.toReal_pos
      (ENNReal.inv_pos.mpr hvolfin.ne).ne'
      (ENNReal.inv_lt_top.mpr hvolpos).ne).ne'
  have hNorm : Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
      a * (max (newtonianGreenProfile n ‖y - x‖) 0 * g y)) := by
    apply (integrable_normalized_newtonianKernel_mul_bdd n hn x
      (r := 1) (by norm_num) g hg hB).congr
    filter_upwards [normalized_newtonianKernel_toReal_ae_eq_profile n hn x
      (r := 1) (by norm_num)] with y hy
    simpa only [inv_one, one_smul, div_one, a, mul_assoc] using
      congrArg (fun t : ℝ ↦ t * g y) hy
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr ha) _).mp hNorm

/-- Radial integrability of a Green profile times the spherical integral of a bounded
continuous function. -/
theorem integrableOn_radial_profile_mul_sphereIntegral
    (n : ℕ) [NeZero n] (φ : ℝ → ℝ)
    (hφ : Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦ φ ‖y‖))
    (x : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Continuous g) (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B) (R : ℝ) :
    IntegrableOn (fun s : ℝ ↦ φ s * (s ^ (n - 1) *
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        g (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)))
      (Set.Ioo (0 : ℝ) R) := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let ν : Measure S := volume.toSphere
  let m : ℝ → ℝ := fun s ↦ ∫ ω : S, g (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂ν
  have hrad : IntegrableOn (fun s : ℝ ↦ s ^ (n - 1) * φ s) (Set.Ioi (0 : ℝ)) := by
    simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using
      (integrable_fun_norm_addHaar volume).mp hφ
  have hradR : IntegrableOn (fun s : ℝ ↦ s ^ (n - 1) * φ s)
      (Set.Ioo (0 : ℝ) R) := hrad.mono_set (by intro s hs; exact hs.1)
  have hm : Continuous m := continuous_sphereIntegral n g hg x
  have hbound : ∀ᵐ s ∂(volume.restrict (Set.Ioo (0 : ℝ) R)),
      ‖m s‖ ≤ B * ν.real Set.univ := by
    filter_upwards with s
    exact norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun ω : S ↦ hB _)
  have hprod := hradR.mul_bdd
    (hm.aestronglyMeasurable (μ := volume.restrict (Set.Ioo (0 : ℝ) R))) hbound
  change Integrable (fun s : ℝ ↦ φ s * (s ^ (n - 1) * m s))
    (volume.restrict (Set.Ioo (0 : ℝ) R))
  convert hprod using 1
  funext s
  dsimp [m]
  ring

/-- The radial planar Green pairing with a bounded continuous function is integrable on
its support interval. -/
theorem integrableOn_planarGreenProfile_mul_sphereIntegral
    (x : EuclideanSpace ℝ (Fin 2)) (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hg : Continuous g) (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B) :
    IntegrableOn (fun s : ℝ ↦ planarGreenProfile s *
      (s * ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        g (x + s • (ω : EuclideanSpace ℝ (Fin 2))) ∂(volume.toSphere)))
      (Set.Ioo (0 : ℝ) planarGreenRadius) := by
  let φ : ℝ → ℝ := fun s ↦ max (planarGreenProfile s) 0
  have hφ : Integrable (fun y : EuclideanSpace ℝ (Fin 2) ↦ φ ‖y‖) := by
    have h := integrable_planarGreenProfile_posPart_mul_bdd
      (0 : EuclideanSpace ℝ (Fin 2)) (fun _ ↦ (1 : ℝ))
      (by fun_prop) (B := 1) (by simp)
    simpa [φ] using h
  have hrad := integrableOn_radial_profile_mul_sphereIntegral
    2 φ hφ x g hg B hB planarGreenRadius
  apply hrad.congr_fun ?_ measurableSet_Ioo
  intro s hs
  have hnonneg : 0 ≤ planarGreenProfile s :=
    planarGreenProfile_nonneg hs.1 hs.2.le
  simp [φ, max_eq_left hnonneg]

/-- The radial Newtonian Green pairing with a bounded continuous function is integrable on
its support interval. -/
theorem integrableOn_newtonianGreenProfile_mul_sphereIntegral
    (n : ℕ) (hn : 3 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Continuous g) (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B) :
    IntegrableOn (fun s : ℝ ↦ newtonianGreenProfile n s *
      (s ^ (n - 1) *
        ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          g (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)))
      (Set.Ioo (0 : ℝ) (greenRadius n)) := by
  letI : NeZero n := ⟨by omega⟩
  let φ : ℝ → ℝ := fun s ↦ max (newtonianGreenProfile n s) 0
  have hφ : Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦ φ ‖y‖) := by
    have h := integrable_newtonianGreenProfile_posPart_mul_bdd n hn
      (0 : EuclideanSpace ℝ (Fin n)) (fun _ ↦ (1 : ℝ))
      (by fun_prop) (B := 1) (by simp)
    simpa [φ] using h
  have hrad := integrableOn_radial_profile_mul_sphereIntegral
    n φ hφ x g hg B hB (greenRadius n)
  apply hrad.congr_fun ?_ measurableSet_Ioo
  intro s hs
  have hnonneg : 0 ≤ newtonianGreenProfile n s :=
    newtonianGreenProfile_nonneg n hn hs.1 hs.2.le
  simp [φ, max_eq_left hnonneg]

end CenteredMaximal.Ball
