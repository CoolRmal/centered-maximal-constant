/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.GreenIdentity
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
open scoped Real Interval Topology

namespace CenteredMaximal.Ball

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
