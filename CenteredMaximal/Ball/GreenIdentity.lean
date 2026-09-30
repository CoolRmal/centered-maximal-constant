/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.PlanarNormalized
public import CenteredMaximal.Ball.NewtonianMass
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Radial identities for the Green comparison kernels

The logarithmic and Newtonian profiles vanish at their support radii. Their radial derivatives
have constant flux, the scalar identity behind the Green pairing with the Laplacian.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

namespace CenteredMaximal.Ball

/-- A finite-mass extended kernel has an integrable real representative almost everywhere. -/
theorem real_representative_of_finite_lintegral {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (Q : E → ℝ≥0∞) (hQ : AEMeasurable Q μ)
    (hfin : (∫⁻ y, Q y ∂μ) ≠ ∞) :
    Integrable (fun y ↦ (Q y).toReal) μ ∧
      ∀ᵐ y ∂μ, Q y = ENNReal.ofReal ((Q y).toReal) := by
  refine ⟨integrable_toReal_of_lintegral_ne_top hQ hfin, ?_⟩
  filter_upwards [ae_lt_top' hQ hfin] with y hy
  exact (ENNReal.ofReal_toReal hy.ne).symm

/-- The normalized planar kernel has an integrable real representative at every positive scale. -/
theorem normalized_planarKernel_real_representative
    (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : EuclideanSpace ℝ (Fin 2) ↦
      ((MeasureTheory.volume (Metric.ball x r))⁻¹ *
        planarKernel (r⁻¹ • (x - y))).toReal) ∧
    ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 2))),
      (MeasureTheory.volume (Metric.ball x r))⁻¹ *
        planarKernel (r⁻¹ • (x - y)) =
      ENNReal.ofReal (((MeasureTheory.volume (Metric.ball x r))⁻¹ *
        planarKernel (r⁻¹ • (x - y))).toReal) := by
  apply real_representative_of_finite_lintegral volume
  · exact (measurable_planarKernel.comp (by fun_prop)).const_mul _ |>.aemeasurable
  · rw [planarKernel_normalized_mass x hr]
    exact ENNReal.ofReal_ne_top

/-- The normalized Newtonian kernel has an integrable real representative in dimension `n ≥ 3`. -/
theorem normalized_newtonianKernel_real_representative (n : ℕ) (hn : 3 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
      ((MeasureTheory.volume (Metric.ball x r))⁻¹ *
        newtonianKernel n (r⁻¹ • (x - y))).toReal) ∧
    ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
      (MeasureTheory.volume (Metric.ball x r))⁻¹ *
        newtonianKernel n (r⁻¹ • (x - y)) =
      ENNReal.ofReal (((MeasureTheory.volume (Metric.ball x r))⁻¹ *
        newtonianKernel n (r⁻¹ • (x - y))).toReal) := by
  apply real_representative_of_finite_lintegral volume
  · exact (measurable_newtonianKernel n |>.comp (by fun_prop)).const_mul _ |>.aemeasurable
  · rw [lintegral_normalized_newtonianKernel n hn x hr]
    exact ENNReal.ofReal_ne_top

/-- A bounded measurable function can be paired integrably with the normalized planar kernel. -/
theorem integrable_normalized_planarKernel_mul_bdd
    (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) (hg : AEStronglyMeasurable g volume)
    {C : ℝ} (hC : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))), ‖g y‖ ≤ C) :
    Integrable (fun y : EuclideanSpace ℝ (Fin 2) ↦
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal * g y) :=
  (normalized_planarKernel_real_representative x hr).1.mul_bdd hg hC

/-- A bounded measurable function can be paired integrably with the normalized Newtonian kernel. -/
theorem integrable_normalized_newtonianKernel_mul_bdd (n : ℕ) (hn : 3 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : AEStronglyMeasurable g volume)
    {C : ℝ} (hC : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ C) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal * g y) :=
  (normalized_newtonianKernel_real_representative n hn x hr).1.mul_bdd hg hC

/-- Polar integration for an arbitrary integrable test function, with the natural sphere measure.
This is the integral identity underlying the Green-kernel pairing. -/
private theorem integral_polar_ball_aux (n : ℕ) [NeZero n]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : Integrable F) :
    (∫ z, F z) =
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∫ s : Set.Ioi (0 : ℝ), F ((s : ℝ) • (ω : EuclideanSpace ℝ (Fin n)))
          ∂Measure.volumeIoiPow (n - 1)
        ∂(volume.toSphere) := by
  let E := EuclideanSpace ℝ (Fin n)
  let μ : Measure E := volume
  let P := homeomorphUnitSphereProd E
  have hcomp : Integrable (fun z : ({0}ᶜ : Set E) ↦ F z.1) (μ.comap Subtype.val) := by
    exact (integrableOn_iff_comap_subtypeVal
      (measurableSet_singleton (0 : E)).compl).mp hF.integrableOn
  have hprod : Integrable (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) ↦
      F ((P.symm p).1)) (μ.toSphere.prod (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
    have h := μ.measurePreserving_homeomorphUnitSphereProd.integrable_comp_emb
      (Homeomorph.measurableEmbedding P)
      (g := fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) ↦ F ((P.symm p).1))
    apply h.mp
    convert hcomp using 1
    funext z
    change F ((P.symm (P z)).1) = F z.1
    simp
  calc
    (∫ z, F z) = ∫ z : ({0}ᶜ : Set E), F z.1 ∂(μ.comap Subtype.val) := by
      rw [integral_subtype_comap (measurableSet_singleton (0 : E)).compl F,
        restrict_compl_singleton]
    _ = ∫ p, F ((P.symm p).1) ∂(μ.toSphere.prod
          (Measure.volumeIoiPow (Module.finrank ℝ E - 1))) := by
      simpa [P] using μ.measurePreserving_homeomorphUnitSphereProd.integral_comp
        (Homeomorph.measurableEmbedding P)
        (fun p : Metric.sphere (0 : E) 1 × Set.Ioi (0 : ℝ) ↦ F ((P.symm p).1))
    _ = ∫ ω : Metric.sphere (0 : E) 1,
        ∫ s : Set.Ioi (0 : ℝ), F ((s : ℝ) • (ω : E))
          ∂Measure.volumeIoiPow (Module.finrank ℝ E - 1)
        ∂μ.toSphere := by
      rw [integral_prod _ hprod]
      simp only [P, homeomorphUnitSphereProd_symm_apply_coe]
    _ = _ := by simp only [E, μ, finrank_euclideanSpace_fin]

private theorem integral_polar_ball_center_aux (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : Integrable F) :
    (∫ y, F y) =
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∫ s : Set.Ioi (0 : ℝ),
          F (x + (s : ℝ) • (ω : EuclideanSpace ℝ (Fin n)))
          ∂Measure.volumeIoiPow (n - 1)
        ∂(volume.toSphere) := by
  have h := integral_polar_ball_aux n (fun z ↦ F (x + z)) (hF.comp_add_left x)
  rw [integral_add_left_eq_self F x] at h
  exact h

/-- Convert integration against the radial density into an ordinary real integral. -/
private theorem integral_volumeIoiPow (k : ℕ) (g : ℝ → ℝ) :
    (∫ s : Set.Ioi (0 : ℝ), g (s : ℝ) ∂Measure.volumeIoiPow k) =
      ∫ s in Set.Ioi (0 : ℝ), s ^ k * g s := by
  rw [Measure.volumeIoiPow]
  change (∫ s : Set.Ioi (0 : ℝ), g (s : ℝ) ∂
    (Measure.comap Subtype.val volume).withDensity
      (fun r ↦ ((Real.toNNReal ((r : ℝ) ^ k) : NNReal) : ENNReal))) = _
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap (hs := measurableSet_Ioi)
      (f := fun s : ℝ ↦ (s ^ k).toNNReal • g s)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    change (s ^ k).toNNReal • g s = s ^ k * g s
    rw [NNReal.smul_def, Real.coe_toNNReal (s ^ k) (pow_nonneg hs.out.le _),
      smul_eq_mul]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

/-- Polar integration about `x` for every integrable real test function. It converts a Green
pairing into radial integrals of spherical Laplacian means. -/
theorem integral_polar_ball (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : Integrable F) :
    (∫ y, F y) =
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∫ s in Set.Ioi (0 : ℝ),
          s ^ (n - 1) * F (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂volume
        ∂(volume.toSphere) := by
  rw [integral_polar_ball_center_aux n x F hF]
  apply integral_congr_ae
  filter_upwards with ω
  exact integral_volumeIoiPow (n - 1)
    (fun s ↦ F (x + s • (ω : EuclideanSpace ℝ (Fin n))))

/-- Polar integration of a radial weight against an integrable test function. This is the form
used when the weight is a real Green kernel and the test function is an obstacle Laplacian. -/
theorem integral_radial_mul_polar (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin n)) (φ : ℝ → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : Integrable (fun y ↦ φ ‖y - x‖ * g y)) :
    (∫ y, φ ‖y - x‖ * g y) =
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∫ s in Set.Ioi (0 : ℝ),
          s ^ (n - 1) * φ s * g (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂volume
        ∂(volume.toSphere) := by
  rw [integral_polar_ball n x _ hg]
  apply integral_congr_ae
  filter_upwards with ω
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have hnorm : ‖x + s • (ω : EuclideanSpace ℝ (Fin n)) - x‖ = s := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs.out]
    have hω : ‖(ω : EuclideanSpace ℝ (Fin n))‖ = 1 := by
      have h := ω.property
      simpa only [Metric.mem_sphere, dist_zero_right] using h
    simp [hω]
  change s ^ (n - 1) * (φ ‖x + s • (ω : EuclideanSpace ℝ (Fin n)) - x‖ *
    g (x + s • (ω : EuclideanSpace ℝ (Fin n)))) = _
  rw [hnorm]
  ring

/-- Differentiate the unnormalized sphere integral of a smooth function in its radius. A global
gradient bound supplies the integrable domination; smooth compactly supported functions satisfy
such a bound. -/
theorem hasDerivAt_sphereIntegral (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (x : EuclideanSpace ℝ (Fin n)) (r C : ℝ)
    (hC : ∀ z, ‖fderiv ℝ w z‖ ≤ C) :
    HasDerivAt
      (fun t : ℝ ↦ ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (x + t • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere))
      (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        fderiv ℝ w (x + r • (ω : EuclideanSpace ℝ (Fin n)))
          (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere)) r := by
  let E := EuclideanSpace ℝ (Fin n)
  let S := Metric.sphere (0 : E) 1
  let ν : Measure S := volume.toSphere
  have hF_meas : ∀ᶠ t in 𝓝 r, AEStronglyMeasurable
      (fun ω : S ↦ w (x + t • (ω : E))) ν := by
    filter_upwards [] with t
    exact (hw.continuous.comp (by fun_prop)).aestronglyMeasurable
  have hF_int : Integrable (fun ω : S ↦ w (x + r • (ω : E))) ν := by
    have hcont : Continuous (fun ω : S ↦ w (x + r • (ω : E))) :=
      hw.continuous.comp (by fun_prop)
    simpa [IntegrableOn] using hcont.continuousOn.integrableOn_compact isCompact_univ
  have hF'_meas : AEStronglyMeasurable (fun ω : S ↦
      fderiv ℝ w (x + r • (ω : E)) (ω : E)) ν := by
    have hc : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by norm_num)
    exact (by fun_prop : Continuous (fun ω : S ↦
      fderiv ℝ w (x + r • (ω : E)) (ω : E))).aestronglyMeasurable
  have hbound : ∀ᵐ (ω : S) ∂ν, ∀ t ∈ (Set.univ : Set ℝ),
      ‖fderiv ℝ w (x + t • (ω : E)) (ω : E)‖ ≤ C := by
    filter_upwards with ω
    intro t _
    have hω : ‖(ω : E)‖ = 1 := by
      have h := ω.property
      simpa only [S, Metric.mem_sphere, dist_zero_right] using h
    calc
      ‖fderiv ℝ w (x + t • (ω : E)) (ω : E)‖ ≤
        ‖fderiv ℝ w (x + t • (ω : E))‖ * ‖(ω : E)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ w (x + t • (ω : E))‖ := by rw [hω, mul_one]
      _ ≤ C := hC _
  have hdiff : ∀ᵐ (ω : S) ∂ν, ∀ t ∈ (Set.univ : Set ℝ),
      HasDerivAt (fun u : ℝ ↦ w (x + u • (ω : E)))
        (fderiv ℝ w (x + t • (ω : E)) (ω : E)) t := by
    filter_upwards with ω
    intro t _
    have hline : HasDerivAt (fun u : ℝ ↦ x + u • (ω : E)) (ω : E) t := by
      simpa using ((hasDerivAt_id t).smul_const (ω : E)).const_add x
    simpa only [Function.comp_def] using
      (hw.differentiable (by norm_num) (x + t • (ω : E))).hasFDerivAt.comp_hasDerivAt
        t hline
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (s := Set.univ)
    (bound := fun _ : S ↦ C) (F := fun t ω ↦ w (x + t • (ω : E)))
    (F' := fun t ω ↦ fderiv ℝ w (x + t • (ω : E)) (ω : E))
    (by simp) hF_meas hF_int hF'_meas hbound (integrable_const C) hdiff).2

/-- For a smooth compactly supported function, the sphere integral can be differentiated with
respect to radius without a separate bound on its gradient. -/
theorem hasDerivAt_sphereIntegral_of_hasCompactSupport (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    HasDerivAt
      (fun t : ℝ ↦ ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (x + t • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere))
      (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        fderiv ℝ w (x + r • (ω : EuclideanSpace ℝ (Fin n)))
          (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere)) r := by
  obtain ⟨C, hC⟩ := (hsupp.fderiv ℝ).exists_bound_of_continuous
    (hw.continuous_fderiv (by norm_num))
  exact hasDerivAt_sphereIntegral n w hw x r C hC

/-- The Laplacian does not enlarge the support of a function. -/
theorem hasCompactSupport_laplacian (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hsupp : HasCompactSupport w) :
    HasCompactSupport (Laplacian.laplacian w) := by
  apply hsupp.mono'
  intro x hx
  by_contra hxt
  have hzero : w =ᶠ[𝓝 x] (0 : EuclideanSpace ℝ (Fin n) → ℝ) :=
    notMem_tsupport_iff_eventuallyEq.mp hxt
  have hΔzero := (InnerProductSpace.laplacian_congr_nhds hzero).eq_of_nhds
  have hΔx : Laplacian.laplacian w x = 0 := by simpa [Pi.zero_def] using hΔzero
  exact hx hΔx

/-- A twice continuously differentiable function has a continuous Laplacian. -/
theorem continuous_laplacian (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w) :
    Continuous (Laplacian.laplacian w) := by
  have hiter : Continuous (iteratedFDeriv ℝ 2 w) :=
    hw.continuous_iteratedFDeriv (by norm_num)
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  fun_prop

/-- A smooth compactly supported function has a globally bounded Laplacian. -/
theorem exists_bound_laplacian (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) :
    ∃ C : ℝ, ∀ y, ‖Laplacian.laplacian w y‖ ≤ C :=
  (hasCompactSupport_laplacian n w hsupp).exists_bound_of_continuous
    (continuous_laplacian n w hw)

/-- The normalized planar Green weight has an integrable pairing with the Laplacian of a smooth,
compactly supported test function. -/
theorem integrable_normalized_planarKernel_mul_laplacian
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : EuclideanSpace ℝ (Fin 2) ↦
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) := by
  obtain ⟨C, hC⟩ := exists_bound_laplacian 2 w hw hsupp
  exact integrable_normalized_planarKernel_mul_bdd x hr (Laplacian.laplacian w)
    (continuous_laplacian 2 w hw).aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- The normalized Newtonian Green weight has an integrable pairing with the Laplacian of a smooth,
compactly supported test function. -/
theorem integrable_normalized_newtonianKernel_mul_laplacian
    (n : ℕ) (hn : 3 ≤ n) (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hw : ContDiff ℝ 2 w) (hsupp : HasCompactSupport w)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) := by
  obtain ⟨C, hC⟩ := exists_bound_laplacian n w hw hsupp
  exact integrable_normalized_newtonianKernel_mul_bdd n hn x hr (Laplacian.laplacian w)
    (continuous_laplacian n w hw).aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- The untruncated radial logarithmic profile in dimension two. -/
def planarGreenProfile (s : ℝ) : ℝ := 1 - 2 * Real.log s

/-- The untruncated radial Newtonian profile in dimension at least three. -/
def newtonianGreenProfile (n : ℕ) (s : ℝ) : ℝ :=
  ((n : ℝ) * s ^ ((2 : ℝ) - (n : ℝ)) - 2) / ((n : ℝ) - 2)

/-- Away from the origin, the planar kernel is the positive part of the radial profile. -/
theorem planarKernel_eq_profile (z : EuclideanSpace ℝ (Fin 2)) (hz : z ≠ 0) :
    planarKernel z = ENNReal.ofReal (planarGreenProfile ‖z‖) := by
  simp [planarKernel, planarGreenProfile, hz]

/-- Away from the origin, the Newtonian kernel is the positive part of the radial profile. -/
theorem newtonianKernel_eq_profile (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) (hz : z ≠ 0) :
    newtonianKernel n z = ENNReal.ofReal (newtonianGreenProfile n ‖z‖) := by
  simp [newtonianKernel, newtonianGreenProfile, hz]

/-- Away from its singular point, the normalized planar Green weight is a radial profile. -/
theorem normalized_planarKernel_toReal_eq_profile
    (x y : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) (hy : y ≠ x) :
    ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal =
      (volume (Metric.ball x r))⁻¹.toReal *
        max (planarGreenProfile (‖y - x‖ / r)) 0 := by
  have hz : r⁻¹ • (x - y) ≠ 0 := by
    simp [hr.ne', sub_ne_zero.mpr hy.symm]
  rw [planarKernel_eq_profile _ hz, ENNReal.toReal_mul, ENNReal.toReal_ofReal']
  congr 1
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  rw [norm_sub_rev]
  ring_nf

/-- Away from its singular point, the normalized Newtonian Green weight is a radial profile. -/
theorem normalized_newtonianKernel_toReal_eq_profile (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) (hy : y ≠ x) :
    ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal =
      (volume (Metric.ball x r))⁻¹.toReal *
        max (newtonianGreenProfile n (‖y - x‖ / r)) 0 := by
  have hz : r⁻¹ • (x - y) ≠ 0 := by
    simp [hr.ne', sub_ne_zero.mpr hy.symm]
  rw [newtonianKernel_eq_profile n _ hz, ENNReal.toReal_mul, ENNReal.toReal_ofReal']
  congr 1
  congr 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  rw [norm_sub_rev]
  ring_nf

/-- The normalized planar Green weight agrees with its radial real profile almost everywhere. -/
theorem normalized_planarKernel_toReal_ae_eq_profile
    (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal =
        (volume (Metric.ball x r))⁻¹.toReal *
          max (planarGreenProfile (‖y - x‖ / r)) 0 := by
  filter_upwards [(volume : Measure (EuclideanSpace ℝ (Fin 2))).ae_ne x] with y hy
  exact normalized_planarKernel_toReal_eq_profile x y hr hy

/-- The normalized Newtonian Green weight agrees with its radial real profile almost everywhere. -/
theorem normalized_newtonianKernel_toReal_ae_eq_profile (n : ℕ) (hn : 3 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal =
        (volume (Metric.ball x r))⁻¹.toReal *
          max (newtonianGreenProfile n (‖y - x‖ / r)) 0 := by
  letI : NeZero n := ⟨by omega⟩
  filter_upwards [(volume : Measure (EuclideanSpace ℝ (Fin n))).ae_ne x] with y hy
  exact normalized_newtonianKernel_toReal_eq_profile n x y hr hy

/-- The logarithmic profile vanishes at its support radius. -/
theorem planarGreenProfile_at_radius : planarGreenProfile planarGreenRadius = 0 := by
  have hlog : Real.log planarGreenRadius = 1 / 2 := by
    simp [planarGreenRadius, Real.log_sqrt (Real.exp_pos 1).le]
  simp [planarGreenProfile, hlog]

/-- The Newtonian profile vanishes at its support radius. -/
theorem newtonianGreenProfile_at_radius (n : ℕ) (hn : 3 ≤ n) :
    newtonianGreenProfile n (greenRadius n) = 0 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hR : 0 < greenRadius n := greenRadius_pos n hn
  have hpow : greenRadius n ^ ((2 : ℝ) - (n : ℝ)) = 2 / (n : ℝ) := by
    calc
      _ = (greenRadius n ^ ((n : ℝ) - 2))⁻¹ := by
        rw [show (2 : ℝ) - (n : ℝ) = -((n : ℝ) - 2) by ring]
        exact Real.rpow_neg hR.le _
      _ = ((n : ℝ) / 2)⁻¹ := by rw [greenRadius_rpow_sub_two n hn]
      _ = 2 / (n : ℝ) := by field_simp
  have hnum : (n : ℝ) * (2 / (n : ℝ)) - 2 = 0 := by
    field_simp
    ring
  simp [newtonianGreenProfile, hpow, hnum]

/-- The planar Green profile is nonnegative inside its support radius. -/
theorem planarGreenProfile_nonneg {s : ℝ} (hs : 0 < s)
    (hle : s ≤ planarGreenRadius) : 0 ≤ planarGreenProfile s := by
  have hlog : Real.log s ≤ Real.log planarGreenRadius := Real.log_le_log hs hle
  have hlogR : Real.log planarGreenRadius = 1 / 2 := by
    simp [planarGreenRadius, Real.log_sqrt (Real.exp_pos 1).le]
  unfold planarGreenProfile
  rw [hlogR] at hlog
  linarith

/-- The Newtonian Green profile is nonnegative inside its support radius. -/
theorem newtonianGreenProfile_nonneg (n : ℕ) (hn : 3 ≤ n)
    {s : ℝ} (hs : 0 < s) (hle : s ≤ greenRadius n) :
    0 ≤ newtonianGreenProfile n s := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hexp : (2 : ℝ) - (n : ℝ) ≤ 0 := by linarith
  have hR : 0 < greenRadius n := greenRadius_pos n hn
  have hRpow : greenRadius n ^ ((2 : ℝ) - (n : ℝ)) = 2 / (n : ℝ) := by
    calc
      _ = (greenRadius n ^ ((n : ℝ) - 2))⁻¹ := by
        rw [show (2 : ℝ) - (n : ℝ) = -((n : ℝ) - 2) by ring]
        exact Real.rpow_neg hR.le _
      _ = ((n : ℝ) / 2)⁻¹ := by rw [greenRadius_rpow_sub_two n hn]
      _ = 2 / (n : ℝ) := by field_simp
  have hpow : 2 / (n : ℝ) ≤ s ^ ((2 : ℝ) - (n : ℝ)) :=
    hRpow ▸ Real.rpow_le_rpow_of_nonpos hs hle hexp
  have hprod : 2 ≤ (n : ℝ) * s ^ ((2 : ℝ) - (n : ℝ)) := by
    calc
      2 = (n : ℝ) * (2 / (n : ℝ)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by linarith)
  unfold newtonianGreenProfile
  exact div_nonneg (by linarith) (by linarith)

/-- The radial derivative of the planar logarithmic Green profile. -/
theorem hasDerivAt_planarGreenProfile {s : ℝ} (hs : 0 < s) :
    HasDerivAt planarGreenProfile (-2 / s) s := by
  have hlog := Real.hasDerivAt_log hs.ne'
  unfold planarGreenProfile
  convert! (hasDerivAt_const s (1 : ℝ)).sub (hlog.const_mul 2) using 1
  ring

/-- The radial derivative of the Newtonian Green profile. -/
theorem hasDerivAt_newtonianGreenProfile (n : ℕ) (hn : 3 ≤ n)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (newtonianGreenProfile n)
      (-(n : ℝ) * s ^ ((1 : ℝ) - (n : ℝ))) s := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (n : ℝ) - 2 ≠ 0 := by linarith
  have hpow : HasDerivAt (fun t : ℝ ↦ t ^ ((2 : ℝ) - (n : ℝ)))
      (((2 : ℝ) - (n : ℝ)) * s ^ ((1 : ℝ) - (n : ℝ))) s := by
    simpa only [show (2 : ℝ) - (n : ℝ) - 1 = 1 - n by ring] using
      Real.hasDerivAt_rpow_const (p := (2 : ℝ) - (n : ℝ)) (Or.inl hs.ne')
  unfold newtonianGreenProfile
  convert! ((hpow.const_mul (n : ℝ)).sub_const 2).div_const ((n : ℝ) - 2) using 1
  field_simp
  ring

/-- The planar radial flux is constant on the punctured plane. -/
theorem planarGreenProfile_flux {s : ℝ} (hs : 0 < s) :
    s * deriv planarGreenProfile s = -2 := by
  rw [(hasDerivAt_planarGreenProfile hs).deriv]
  field_simp

/-- The Newtonian radial flux is constant on the punctured space. -/
theorem newtonianGreenProfile_flux (n : ℕ) (hn : 3 ≤ n)
    {s : ℝ} (hs : 0 < s) :
    s ^ (n - 1) * deriv (newtonianGreenProfile n) s = -(n : ℝ) := by
  rw [(hasDerivAt_newtonianGreenProfile n hn hs).deriv]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hne : (n : ℕ) ≠ 0 := by omega
  have hpow : s ^ (n - 1) * s ^ ((1 : ℝ) - (n : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hcast]
    convert Real.rpow_zero s using 1
    ring_nf
  calc
    s ^ (n - 1) * (-(n : ℝ) * s ^ ((1 : ℝ) - (n : ℝ))) =
        -(n : ℝ) * (s ^ (n - 1) * s ^ ((1 : ℝ) - (n : ℝ))) := by ring
    _ = -(n : ℝ) := by rw [hpow, mul_one]

end CenteredMaximal.Ball
