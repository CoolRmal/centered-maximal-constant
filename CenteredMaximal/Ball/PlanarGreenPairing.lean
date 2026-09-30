/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.GreenIdentity
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.CircleAverage
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Circle averages and radial differentiation

This file develops the circle-average side of the planar Green pairing. The first step is
differentiation of a circle average with respect to its radius. It uses Mathlib's parametric
integral theorem and applies to any circle integrand with a uniformly bounded radial derivative.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Metric Set Filter
open scoped Real Interval Topology Pointwise

namespace CenteredMaximal.Ball

/-- The standard real-linear isometry from the Euclidean plane to the complex plane. -/
noncomputable def planarComplexIsometry : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ :=
  Complex.orthonormalBasisOneI.repr.symm

/-- The isometry identifies the Euclidean and complex unit circles as topological spaces. -/
noncomputable def planarSphereEquiv :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ
      Metric.sphere (0 : ℂ) 1 :=
  planarComplexIsometry.toHomeomorph.subtype (by
    intro z
    simp [planarComplexIsometry.norm_map])

@[simp] theorem planarSphereEquiv_coe
    (ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    ((planarSphereEquiv ω : Metric.sphere (0 : ℂ) 1) : ℂ) =
      planarComplexIsometry (ω : EuclideanSpace ℝ (Fin 2)) := rfl

/-- The same plane-to-complex isometry preserves Lebesgue measure. -/
theorem planarComplexIsometry_measurePreserving :
    MeasurePreserving planarComplexIsometry
      (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (volume : Measure ℂ) :=
  planarComplexIsometry.measurePreserving

private theorem unitSphereCone_eq (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (A : Set (Metric.sphere (0 : V) 1)) :
    (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' A) : Set V) =
      Subtype.val '' ((homeomorphUnitSphereProd V).symm ''
        (A ×ˢ Set.Iio (⟨1, by simp⟩ : Set.Ioi (0 : ℝ)))) := by
  ext y
  rw [← Set.image2_smul]
  simp only [Set.mem_image, Set.mem_prod, Set.mem_image2, Set.mem_Ioo, Set.mem_Iio]
  constructor
  · rintro ⟨r, ⟨hr0, hr1⟩, z, ⟨ω, hω, rfl⟩, hEq⟩
    let rp : Set.Ioi (0 : ℝ) := ⟨r, hr0⟩
    let p : Metric.sphere (0 : V) 1 × Set.Ioi (0 : ℝ) := (ω, rp)
    refine ⟨(homeomorphUnitSphereProd V).symm p,
      ⟨p, ⟨hω, hr1⟩, rfl⟩, ?_⟩
    simpa [p, rp, homeomorphUnitSphereProd_symm_apply_coe] using hEq
  · rintro ⟨q, ⟨p, ⟨hpA, hpr⟩, rfl⟩, rfl⟩
    refine ⟨(p.2 : ℝ), ⟨p.2.property, hpr⟩, (p.1 : V),
      ⟨p.1, hpA, rfl⟩, ?_⟩
    exact (homeomorphUnitSphereProd_symm_apply_coe V p).symm

private theorem measurableSet_unitSphereCone (V : Type*)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
    (A : Set (Metric.sphere (0 : V) 1)) (hA : MeasurableSet A) :
    MeasurableSet (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' A) : Set V) := by
  rw [unitSphereCone_eq]
  apply (MeasurableEmbedding.subtype_coe
    (measurableSet_singleton (0 : V)).compl).measurableSet_image'
  apply (Homeomorph.measurableEmbedding (homeomorphUnitSphereProd V).symm).measurableSet_image'
  exact hA.prod measurableSet_Iio

/-- The plane-to-complex isometry also preserves the angular measure appearing in polar
integration. -/
theorem planarSphereEquiv_measurePreserving :
    MeasurePreserving planarSphereEquiv
      (volume.toSphere : Measure (Metric.sphere
        (0 : EuclideanSpace ℝ (Fin 2)) 1))
      (volume.toSphere : Measure (Metric.sphere (0 : ℂ) 1)) := by
  refine ⟨planarSphereEquiv.continuous.measurable, ?_⟩
  ext A hA
  rw [Measure.map_apply planarSphereEquiv.continuous.measurable hA,
    Measure.toSphere_apply' _ (planarSphereEquiv.continuous.measurable hA),
    Measure.toSphere_apply' _ hA]
  have hgeom : planarComplexIsometry ⁻¹'
      (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' A) : Set ℂ) =
      (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (planarSphereEquiv ⁻¹' A)) :
        Set (EuclideanSpace ℝ (Fin 2))) := by
    ext z
    simp only [Set.mem_preimage, ← Set.image2_smul, Set.mem_image2,
      Set.mem_image, Set.mem_Ioo]
    constructor
    · rintro ⟨r, hr, v, ⟨ω, hω, rfl⟩, hz⟩
      let η := planarSphereEquiv.symm ω
      refine ⟨r, hr, (η : EuclideanSpace ℝ (Fin 2)), ⟨η, ?_, rfl⟩, ?_⟩
      · exact show planarSphereEquiv η ∈ A by simpa [η] using hω
      · apply planarComplexIsometry.injective
        rw [map_smul]
        have hη : planarComplexIsometry (η : EuclideanSpace ℝ (Fin 2)) =
            (ω : ℂ) := by simpa [η] using (planarSphereEquiv_coe η).symm
        rw [hη]
        exact hz
    · rintro ⟨r, hr, v, ⟨ω, hω, rfl⟩, hz⟩
      refine ⟨r, hr, ((planarSphereEquiv ω : Metric.sphere (0 : ℂ) 1) : ℂ),
        ⟨planarSphereEquiv ω, hω, rfl⟩, ?_⟩
      simpa [map_smul, planarSphereEquiv_coe] using congrArg planarComplexIsometry hz
  have hmeas : (volume : Measure (EuclideanSpace ℝ (Fin 2)))
      (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' (planarSphereEquiv ⁻¹' A))) =
      (volume : Measure ℂ) (Set.Ioo (0 : ℝ) 1 • (Subtype.val '' A)) := by
    rw [← hgeom]
    exact (planarComplexIsometry_measurePreserving.measure_preimage
      (measurableSet_unitSphereCone ℂ A hA).nullMeasurableSet)
  rw [hmeas]
  congr 1
  norm_num

/-- Transport a planar sphere integral to the complex unit circle without changing its
angular measure. -/
theorem integral_planarSphereEquiv (g : Metric.sphere (0 : ℂ) 1 → ℝ) :
    (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        g (planarSphereEquiv ω) ∂(volume.toSphere)) =
      ∫ ζ : Metric.sphere (0 : ℂ) 1, g ζ ∂(volume.toSphere) :=
  planarSphereEquiv_measurePreserving.integral_comp
    planarSphereEquiv.measurableEmbedding g

/-- The angular measure obtained by polar decomposition of planar Lebesgue measure has total
mass `2π`. -/
theorem planar_toSphere_mass :
    (volume.toSphere : Measure (Metric.sphere
      (0 : EuclideanSpace ℝ (Fin 2)) 1)).real Set.univ = 2 * Real.pi := by
  rw [Measure.toSphere_real_apply_univ]
  simp [measureReal_def, EuclideanSpace.volume_ball_fin_two, Real.pi_nonneg]

/-- Integrate a real function over a planar ball using the spherical measure and radial
Lebesgue measure. The radius factor is the two-dimensional polar Jacobian. -/
theorem integral_polar_ball_two
    (x : EuclideanSpace ℝ (Fin 2)) (R : ℝ)
    (F : EuclideanSpace ℝ (Fin 2) → ℝ) (hF : Integrable F) :
    (∫ y in ball x R, F y) =
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        ∫ s in Set.Ioo (0 : ℝ) R,
          s * F (x + s • (ω : EuclideanSpace ℝ (Fin 2))) ∂volume
        ∂(volume.toSphere) := by
  let E := EuclideanSpace ℝ (Fin 2)
  have hFb : Integrable ((ball x R).indicator F) :=
    hF.integrableOn.integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball,
    integral_polar_ball 2 x ((ball x R).indicator F) hFb]
  simp only [Nat.reduceSub, pow_one]
  apply integral_congr_ae
  filter_upwards with ω
  have hωnorm : ‖(ω : E)‖ = 1 := by
    have hω : dist (ω : E) 0 = 1 := mem_sphere.mp ω.property
    simpa only [dist_zero_right] using hω
  have hmem (s : ℝ) (hs : 0 < s) :
      x + s • (ω : E) ∈ ball x R ↔ s < R := by
    simp [mem_ball, dist_eq_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs, hωnorm]
  calc
    (∫ s in Set.Ioi (0 : ℝ),
      s * (ball x R).indicator F (x + s • (ω : E))) =
        ∫ s in Set.Ioi (0 : ℝ),
          (Set.Iio R).indicator (fun s ↦ s * F (x + s • (ω : E))) s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      by_cases hsr : s < R
      · have hb := (hmem s hs).2 hsr
        simp only [Set.indicator_of_mem hb,
          Set.indicator_of_mem (show s ∈ Set.Iio R from hsr)]
      · have hb : x + s • (ω : E) ∉ ball x R := fun h ↦ hsr ((hmem s hs).1 h)
        simp only [Set.indicator_of_notMem hb,
          Set.indicator_of_notMem (show s ∉ Set.Iio R from hsr), mul_zero]
    _ = ∫ s in Set.Ioo (0 : ℝ) R,
          s * F (x + s • (ω : E)) := by
      rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]

/-- The planar polar formula with complex unit directions. -/
theorem integral_polar_ball_two_complex
    (x : EuclideanSpace ℝ (Fin 2)) (R : ℝ)
    (F : EuclideanSpace ℝ (Fin 2) → ℝ) (hF : Integrable F) :
    (∫ y in ball x R, F y) =
      ∫ ζ : Metric.sphere (0 : ℂ) 1,
        ∫ s in Set.Ioo (0 : ℝ) R,
          s * F (x + s • planarComplexIsometry.symm (ζ : ℂ)) ∂volume
        ∂(volume.toSphere) := by
  rw [integral_polar_ball_two x R F hF,
    ← integral_planarSphereEquiv (fun ζ : Metric.sphere (0 : ℂ) 1 ↦
      ∫ s in Set.Ioo (0 : ℝ) R,
        s * F (x + s • planarComplexIsometry.symm (ζ : ℂ)) ∂volume)]
  apply integral_congr_ae
  filter_upwards with ω
  congr 1
  simp [planarSphereEquiv_coe]

/-- Differentiate a circle average by differentiating its integrand in the radial variable.
The uniform bound is needed only near the radius at which the derivative is taken. -/
theorem hasDerivAt_circleAverage_of_bounded_radial_deriv
    (w : ℂ → ℝ) (c : ℂ) (r : ℝ) (g : ℝ → ℝ → ℝ) (U : Set ℝ)
    (hU : U ∈ 𝓝 r) (hw : Continuous w) (hg : Continuous (g r))
    (B : ℝ)
    (hbound : ∀ s ∈ U, ∀ θ ∈ Ι (0 : ℝ) (2 * Real.pi), ‖g s θ‖ ≤ B)
    (hderiv : ∀ s ∈ U, ∀ θ ∈ Ι (0 : ℝ) (2 * Real.pi),
      HasDerivAt (fun t ↦ w (circleMap c t θ)) (g s θ) s) :
    HasDerivAt (fun t ↦ Real.circleAverage w c t)
      ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, g r θ) r := by
  have hFmeas : ∀ᶠ s in 𝓝 r,
      AEStronglyMeasurable (fun θ ↦ w (circleMap c s θ))
        (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := by
    apply Filter.Eventually.of_forall
    intro s
    exact (hw.comp (differentiable_circleMap c s).continuous).measurable.aestronglyMeasurable
  have hFint : IntervalIntegrable (fun θ ↦ w (circleMap c r θ)) volume
      (0 : ℝ) (2 * Real.pi) :=
    (hw.comp (differentiable_circleMap c r).continuous).intervalIntegrable _ _
  have hgmeas : AEStronglyMeasurable (g r)
      (volume.restrict (Ι (0 : ℝ) (2 * Real.pi))) := hg.measurable.aestronglyMeasurable
  have hbound' : ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (2 * Real.pi) →
      ∀ s ∈ U, ‖g s θ‖ ≤ (fun _ : ℝ ↦ B) θ :=
    Filter.Eventually.of_forall fun θ hθ s hs ↦ hbound s hs θ hθ
  have hderiv' : ∀ᵐ θ ∂volume, θ ∈ Ι (0 : ℝ) (2 * Real.pi) →
      ∀ s ∈ U, HasDerivAt (fun t ↦ w (circleMap c t θ)) (g s θ) s :=
    Filter.Eventually.of_forall fun θ hθ s hs ↦ hderiv s hs θ hθ
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    hU hFmeas hFint hgmeas hbound' (intervalIntegrable_const) hderiv'
  simpa only [Real.circleAverage_def, smul_eq_mul] using
    h.2.const_mul ((2 * Real.pi)⁻¹)

/-- For a smooth function with bounded first derivative, the radial derivative of its circle
average is the circle average of its directional derivative along the radial unit vector. -/
theorem hasDerivAt_circleAverage_of_contDiff
    (w : ℂ → ℝ) (c : ℂ) (r : ℝ) (hw : ContDiff ℝ 1 w)
    (B : ℝ) (hB : ∀ z, ‖fderiv ℝ w z‖ ≤ B) :
    HasDerivAt (fun t ↦ Real.circleAverage w c t)
      ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        fderiv ℝ w (circleMap c r θ) (circleMap 0 1 θ)) r := by
  let g : ℝ → ℝ → ℝ := fun s θ ↦
    fderiv ℝ w (circleMap c s θ) (circleMap 0 1 θ)
  have hgradcont : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by norm_num)
  have hg : Continuous (g r) := by
    dsimp [g]
    fun_prop
  have hbound : ∀ s ∈ (Set.univ : Set ℝ),
      ∀ θ ∈ Ι (0 : ℝ) (2 * Real.pi), ‖g s θ‖ ≤ B := by
    intro s _ θ _
    calc
      ‖g s θ‖ ≤ ‖fderiv ℝ w (circleMap c s θ)‖ * ‖circleMap 0 1 θ‖ :=
        (fderiv ℝ w (circleMap c s θ)).le_opNorm _
      _ = ‖fderiv ℝ w (circleMap c s θ)‖ := by
        simp [norm_circleMap_zero]
      _ ≤ B := hB _
  have hderiv : ∀ s ∈ (Set.univ : Set ℝ),
      ∀ θ ∈ Ι (0 : ℝ) (2 * Real.pi),
        HasDerivAt (fun t ↦ w (circleMap c t θ)) (g s θ) s := by
    intro s _ θ _
    have hcircle : HasDerivAt (fun t : ℝ ↦ circleMap c t θ)
        (circleMap 0 1 θ) s := by
      simpa [circleMap] using
        ((Complex.ofRealCLM.hasDerivAt (x := s)).mul_const
          (Complex.exp ((θ : ℂ) * Complex.I))).const_add c
    exact ((hw.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt s hcircle
  exact hasDerivAt_circleAverage_of_bounded_radial_deriv
    w c r g Set.univ (by simp) hw.continuous hg B hbound hderiv

/-- Compact support supplies the global derivative bound needed to differentiate the circle
average of a smooth function. -/
theorem hasDerivAt_circleAverage_of_contDiff_compactSupport
    (w : ℂ → ℝ) (c : ℂ) (r : ℝ)
    (hw : ContDiff ℝ 1 w) (hsupp : HasCompactSupport w) :
    HasDerivAt (fun t ↦ Real.circleAverage w c t)
      ((2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi,
        fderiv ℝ w (circleMap c r θ) (circleMap 0 1 θ)) r := by
  obtain ⟨B, hB⟩ :=
    (hw.continuous_fderiv (by norm_num)).bounded_above_of_compact_support
      (hsupp.fderiv ℝ)
  exact hasDerivAt_circleAverage_of_contDiff w c r hw B hB

end CenteredMaximal.Ball
