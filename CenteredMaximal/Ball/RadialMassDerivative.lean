/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.RadialGreenCalculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Radial cumulative mass on Euclidean balls

This file develops the radius-dependent integral of a test function over a ball. The first
step is polar integration restricted to a ball of arbitrary radius. Its radial Jacobian is
`s^(n-1)`, and its angular measure is Mathlib's `volume.toSphere`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal Interval Topology

namespace CenteredMaximal.Ball

/-- The integral over `(0,r)` has the expected derivative for a continuous integrand at every
positive radius. This lets polar formulas use set integrals while the fundamental theorem of
calculus uses interval integrals. -/
theorem hasDerivAt_integral_Ioo_zero
    (g : ℝ → ℝ) (hg : Continuous g) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t : ℝ ↦ ∫ s in Ioo (0 : ℝ) t, g s) (g r) r := by
  have hFTC : HasDerivAt (fun t : ℝ ↦ ∫ s in (0 : ℝ)..t, g s) (g r) r :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 r)
      (hg.stronglyMeasurableAtFilter volume (𝓝 r)) hg.continuousAt
  apply hFTC.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hr] with t ht
  rw [intervalIntegral.integral_of_le ht.le, integral_Ioc_eq_integral_Ioo]

/-- Differentiate an angular integral of cumulative radial masses. The measurable and bounded
hypotheses are arranged for direct use of Mathlib's dominated differentiation theorem. -/
theorem hasDerivAt_sphereIntegral_radial_mass (n : ℕ) [NeZero n]
    (g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ → ℝ)
    (r B : ℝ) (hr : 0 < r)
    (hgcont : ∀ ω, Continuous (g ω))
    (hmeas : ∀ᶠ t in 𝓝 r, AEStronglyMeasurable
      (fun ω ↦ ∫ s in Ioo (0 : ℝ) t, g ω s)
      (volume.toSphere : Measure (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
    (hint : Integrable (fun ω ↦ ∫ s in Ioo (0 : ℝ) r, g ω s)
      (volume.toSphere : Measure (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
    (hderivmeas : AEStronglyMeasurable (fun ω ↦ g ω r)
      (volume.toSphere : Measure (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)))
    (hbound : ∀ᵐ ω ∂(volume.toSphere : Measure
      (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)),
      ∀ t ∈ Ioo (0 : ℝ) (r + 1), ‖g ω t‖ ≤ B) :
    HasDerivAt
      (fun t : ℝ ↦ ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫ s in Ioo (0 : ℝ) t, g ω s) ∂(volume.toSphere))
      (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        g ω r ∂(volume.toSphere)) r := by
  let S := sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let ν : Measure S := volume.toSphere
  have hU : Ioo (0 : ℝ) (r + 1) ∈ 𝓝 r :=
    Ioo_mem_nhds hr (by linarith)
  have hdiff : ∀ᵐ ω ∂ν, ∀ t ∈ Ioo (0 : ℝ) (r + 1),
      HasDerivAt (fun u : ℝ ↦ ∫ s in Ioo (0 : ℝ) u, g ω s) (g ω t) t := by
    filter_upwards with ω
    intro t ht
    exact hasDerivAt_integral_Ioo_zero (g ω) (hgcont ω) ht.1
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioo (0 : ℝ) (r + 1)) (bound := fun _ : S ↦ B)
    (F := fun t ω ↦ ∫ s in Ioo (0 : ℝ) t, g ω s)
    (F' := fun t ω ↦ g ω t)
    hU hmeas hint hderivmeas hbound (integrable_const B) hdiff).2

/-- The same radius differentiation when the radial integrand is jointly continuous and
uniformly bounded on a slightly larger interval. -/
theorem hasDerivAt_sphereIntegral_radial_mass_of_continuous (n : ℕ) [NeZero n]
    (g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ → ℝ)
    (r B : ℝ) (hr : 0 < r)
    (hg : Continuous (fun p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ ↦
      g p.1 p.2))
    (hbound : ∀ ω, ∀ t ∈ Ioo (0 : ℝ) (r + 1), ‖g ω t‖ ≤ B) :
    HasDerivAt
      (fun t : ℝ ↦ ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫ s in Ioo (0 : ℝ) t, g ω s) ∂(volume.toSphere))
      (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        g ω r ∂(volume.toSphere)) r := by
  let S := sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let ν : Measure S := volume.toSphere
  have hmeas (t : ℝ) : AEStronglyMeasurable
      (fun ω : S ↦ ∫ s in Ioo (0 : ℝ) t, g ω s) ν := by
    have hG : StronglyMeasurable (fun p : S × ℝ ↦
        (Ioo (0 : ℝ) t).indicator (g p.1) p.2) := by
      have hG' : StronglyMeasurable (fun p : S × ℝ ↦
          if p.2 ∈ Ioo (0 : ℝ) t then g p.1 p.2 else 0) :=
        (Measurable.ite (measurableSet_Ioo.preimage measurable_snd)
          hg.measurable measurable_const).stronglyMeasurable
      convert hG' using 1
      funext p
      by_cases hp : p.2 ∈ Ioo (0 : ℝ) t <;> simp [Set.indicator, hp]
    have h := hG.integral_prod_right' (ν := volume)
    convert h.aestronglyMeasurable using 1
    funext ω
    exact (integral_indicator measurableSet_Ioo).symm
  have hgcont (ω : S) : Continuous (g ω) := by
    have hω : Continuous (fun s : ℝ ↦ (ω, s)) := by fun_prop
    exact hg.comp hω
  have hderivmeas : AEStronglyMeasurable (fun ω : S ↦ g ω r) ν := by
    have hω : Continuous (fun ω : S ↦ (ω, r)) := by fun_prop
    exact (hg.comp hω).aestronglyMeasurable
  have hint : Integrable (fun ω : S ↦ ∫ s in Ioo (0 : ℝ) r, g ω s) ν := by
    apply Integrable.of_bound (hmeas r) (volume.real (Ioo (0 : ℝ) r) * B)
    filter_upwards with ω
    simpa only [mul_comm] using
      (norm_setIntegral_le_of_norm_le_const measure_Ioo_lt_top
        (fun s hs ↦ hbound ω s ⟨hs.1, lt_trans hs.2 (by linarith)⟩))
  exact hasDerivAt_sphereIntegral_radial_mass n g r B hr hgcont
    (Filter.Eventually.of_forall hmeas) hint hderivmeas (ae_of_all _ hbound)

/-- Polar integration over a ball of arbitrary radius about `x`, for any globally integrable
real-valued test function. The radial integral uses ordinary Lebesgue measure. -/
theorem integral_polar_ball_radius (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : Integrable F) :
    (∫ y in ball x R, F y) =
      ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        ∫ s in Ioo (0 : ℝ) R,
          s ^ (n - 1) * F (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂volume
        ∂(volume.toSphere) := by
  let E := EuclideanSpace ℝ (Fin n)
  have hFb : Integrable ((ball x R).indicator F) :=
    hF.integrableOn.integrable_indicator measurableSet_ball
  rw [← integral_indicator measurableSet_ball,
    integral_polar_ball n x ((ball x R).indicator F) hFb]
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
    (∫ s in Ioi (0 : ℝ),
      s ^ (n - 1) * (ball x R).indicator F (x + s • (ω : E))) =
        ∫ s in Ioi (0 : ℝ),
          (Iio R).indicator
            (fun s ↦ s ^ (n - 1) * F (x + s • (ω : E))) s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      by_cases hsr : s < R
      · have hb := (hmem s hs).2 hsr
        simp only [Set.indicator_of_mem hb,
          Set.indicator_of_mem (show s ∈ Iio R from hsr)]
      · have hb : x + s • (ω : E) ∉ ball x R := fun h ↦ hsr ((hmem s hs).1 h)
        simp only [Set.indicator_of_notMem hb,
          Set.indicator_of_notMem (show s ∉ Iio R from hsr), mul_zero]
    _ = ∫ s in Ioo (0 : ℝ) R,
          s ^ (n - 1) * F (x + s • (ω : E)) := by
      rw [setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]

/-- Differentiate the polar expression for the mass inside a ball. Compact support gives a
global bound on the density, which dominates the radial derivative near any positive radius. -/
theorem hasDerivAt_polar_ball_mass (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : Continuous F) (hsupp : HasCompactSupport F)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun t : ℝ ↦ ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫ s in Ioo (0 : ℝ) t,
          s ^ (n - 1) * F (x + s • (ω : EuclideanSpace ℝ (Fin n))))
        ∂(volume.toSphere))
      (r ^ (n - 1) *
        ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          F (x + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) r := by
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hF
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (F x)) (hC x)
  let g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ → ℝ :=
    fun ω s ↦ s ^ (n - 1) * F (x + s • (ω : EuclideanSpace ℝ (Fin n)))
  have hg : Continuous
      (fun p : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 × ℝ ↦ g p.1 p.2) := by
    dsimp [g]
    fun_prop
  have hbound : ∀ ω, ∀ t ∈ Ioo (0 : ℝ) (r + 1),
      ‖g ω t‖ ≤ (r + 1) ^ (n - 1) * C := by
    intro ω t ht
    dsimp [g]
    rw [abs_mul, abs_of_nonneg (pow_nonneg ht.1.le _), ← Real.norm_eq_abs]
    calc
      t ^ (n - 1) * ‖F (x + t • (ω : EuclideanSpace ℝ (Fin n)))‖
          ≤ t ^ (n - 1) * C :=
            mul_le_mul_of_nonneg_left (hC _) (pow_nonneg ht.1.le _)
      _ ≤ (r + 1) ^ (n - 1) * C :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht.1.le ht.2.le _) hC0
  have h := hasDerivAt_sphereIntegral_radial_mass_of_continuous n g r
    ((r + 1) ^ (n - 1) * C) hr hg hbound
  simpa only [g, integral_const_mul] using h

/-- The derivative of the mass of a continuous compactly supported density inside a
Euclidean ball is its spherical integral times the polar Jacobian. -/
theorem hasDerivAt_integral_ball_radius (n : ℕ) [NeZero n]
    (x : EuclideanSpace ℝ (Fin n))
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hF : Continuous F) (hsupp : HasCompactSupport F)
    {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun t : ℝ ↦ ∫ y in ball x t, F y)
      (r ^ (n - 1) *
        ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          F (x + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) r := by
  have hI : Integrable F := hF.integrable_of_hasCompactSupport hsupp
  have hfun : (fun t : ℝ ↦ ∫ y in ball x t, F y) =
      (fun t : ℝ ↦ ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        (∫ s in Ioo (0 : ℝ) t,
          s ^ (n - 1) * F (x + s • (ω : EuclideanSpace ℝ (Fin n))))
        ∂(volume.toSphere)) := by
    funext t
    exact integral_polar_ball_radius n x t F hI
  rw [hfun]
  exact hasDerivAt_polar_ball_mass n x F hF hsupp hr

end CenteredMaximal.Ball
