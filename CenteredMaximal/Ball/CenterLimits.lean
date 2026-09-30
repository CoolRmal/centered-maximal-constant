/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.RadialGreenCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Center limits in the Green pairing

The radial Green formula is first proved on a finite annulus. These lemmas control its
inner boundary as the annulus shrinks to the center.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise

namespace CenteredMaximal.Ball

/-- Spherical integrals of a continuous function vary continuously with radius. -/
theorem continuous_sphereIntegral (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Continuous w)
    (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun r : ℝ ↦
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (x + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let ν : Measure S := volume.toSphere
  have hf : Continuous (fun p : ℝ × S ↦ w (x + p.1 • (p.2 : EuclideanSpace ℝ (Fin n)))) := by
    fun_prop
  have h := continuous_parametric_integral_of_continuous
    (μ := ν) (s := (Set.univ : Set S))
    (f := fun r (ω : S) ↦ w (x + r • (ω : EuclideanSpace ℝ (Fin n)))) hf isCompact_univ
  simpa [ν, S] using h

/-- If a continuous function vanishes at the center, its unnormalized spherical integral
vanishes as the radius tends to zero. -/
theorem tendsto_sphereIntegral_zero (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Continuous w)
    (x : EuclideanSpace ℝ (Fin n)) (hx : w x = 0) :
    Tendsto (fun r : ℝ ↦
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (x + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere))
      (𝓝 0) (𝓝 0) := by
  have h := ((continuous_sphereIntegral n w hw x).continuousAt (x := (0 : ℝ))).tendsto
  simpa [hx] using h

end CenteredMaximal.Ball
