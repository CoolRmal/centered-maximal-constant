/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.PolarSwap
public import CenteredMaximal.Ball.RadialGreenLimit
public import CenteredMaximal.Ball.RadialMassDerivative

/-!
# Green pairing for the ball comparison kernels

These theorems combine signed polar integration, radial integration by parts, and center
limits. The only geometric hypothesis is the ball flux identity, stated explicitly so it
can be supplied by a divergence theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace CenteredMaximal.Ball

/-- The planar Green profile pairs with a smooth compactly supported Laplacian as twice the
increment of the spherical integral above its center value. -/
theorem integral_planarGreenProfile_posPart_mul_laplacian_of_ball_flux_general
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin 2))
    (hflux : ∀ s ∈ Set.Ioc (0 : ℝ) planarGreenRadius,
      (∫ y in Metric.ball x s, Laplacian.laplacian w y) =
        s * (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          fderiv ℝ w (x + s • (ω : EuclideanSpace ℝ (Fin 2)))
            (ω : EuclideanSpace ℝ (Fin 2)) ∂(volume.toSphere))) :
    (∫ y : EuclideanSpace ℝ (Fin 2),
      max (planarGreenProfile ‖y - x‖) 0 * Laplacian.laplacian w y) =
      2 * ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        w (x + planarGreenRadius • (ω : EuclideanSpace ℝ (Fin 2)))
          ∂(volume.toSphere)) -
        (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          w x ∂(volume.toSphere))) := by
  let g : EuclideanSpace ℝ (Fin 2) → ℝ := Laplacian.laplacian w
  let F : ℝ → ℝ := fun s ↦ ∫ y in Metric.ball x s, g y
  let m : ℝ → ℝ := fun s ↦
    ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      w (x + s • (ω : EuclideanSpace ℝ (Fin 2))) ∂(volume.toSphere)
  let q : ℝ → ℝ := fun s ↦ s *
    ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      g (x + s • (ω : EuclideanSpace ℝ (Fin 2))) ∂(volume.toSphere)
  let dm : ℝ → ℝ := fun s ↦
    ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      fderiv ℝ w (x + s • (ω : EuclideanSpace ℝ (Fin 2)))
        (ω : EuclideanSpace ℝ (Fin 2)) ∂(volume.toSphere)
  have hg : Continuous g := continuous_laplacian 2 w hw
  have hgsupp : HasCompactSupport g := hasCompactSupport_laplacian 2 w hsupp
  obtain ⟨B, hB⟩ := exists_bound_laplacian 2 w hw hsupp
  have hF : ∀ s ∈ Set.Ioc (0 : ℝ) planarGreenRadius,
      HasDerivAt F (q s) s := by
    intro s hs
    simpa only [F, q, Nat.reduceSub, pow_one] using
      hasDerivAt_integral_ball_radius 2 x g hg hgsupp hs.1
  have hm : ∀ s ∈ Set.Ioc (0 : ℝ) planarGreenRadius,
      HasDerivAt m (dm s) s := by
    intro s _
    exact hasDerivAt_sphereIntegral_of_hasCompactSupport 2 w hw hsupp x s
  have hFflux : ∀ s ∈ Set.Ioc (0 : ℝ) planarGreenRadius,
      F s = s * dm s := by
    intro s hs
    exact hflux s hs
  have hint : IntegrableOn (fun s ↦ planarGreenProfile s * q s)
      (Set.Ioo (0 : ℝ) planarGreenRadius) := by
    exact integrableOn_planarGreenProfile_mul_sphereIntegral x g hg B hB
  have hm0 : Tendsto m (𝓝[>] (0 : ℝ))
      (𝓝 (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        w x ∂(volume.toSphere))) := by
    have h := ((continuous_sphereIntegral 2 w hw.continuous x).continuousAt
      (x := (0 : ℝ))).tendsto
    simpa only [m, zero_smul, add_zero] using h.mono_left nhdsWithin_le_nhds
  have hboundary : Tendsto (fun s ↦ planarGreenProfile s * F s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_planarGreenProfile_mul_integral_ball_zero g x B hB
  have hradial := integral_planar_green_profile_of_center_limits
    (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      w x ∂(volume.toSphere)) F m q dm hF hm hFflux hint hm0 hboundary
  have hambient : Integrable (fun y : EuclideanSpace ℝ (Fin 2) ↦
      max (planarGreenProfile ‖y - x‖) 0 * g y) :=
    integrable_planarGreenProfile_posPart_mul_bdd x g
      hg.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have hpolar := integral_radial_mul_polar_swapped_of_support 2 x
    planarGreenRadius (fun s ↦ max (planarGreenProfile s) 0)
    (fun s hs ↦ planarGreenProfile_posPart_eq_zero_of_radius_le hs)
    g hambient
  calc
    (∫ y : EuclideanSpace ℝ (Fin 2),
      max (planarGreenProfile ‖y - x‖) 0 * Laplacian.laplacian w y) =
        ∫ s in Set.Ioo (0 : ℝ) planarGreenRadius,
          s * max (planarGreenProfile s) 0 *
            (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
              g (x + s • (ω : EuclideanSpace ℝ (Fin 2))) ∂(volume.toSphere)) :=
          (by simpa only [Nat.reduceSub, pow_one] using hpolar)
    _ = ∫ s in Set.Ioo (0 : ℝ) planarGreenRadius,
        planarGreenProfile s * q s := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      have hnonneg := planarGreenProfile_nonneg hs.1 hs.2.le
      simp only [max_eq_left hnonneg, q]
      ring
    _ = 2 * ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        w (x + planarGreenRadius • (ω : EuclideanSpace ℝ (Fin 2)))
          ∂(volume.toSphere)) -
        (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          w x ∂(volume.toSphere))) := by simpa [m] using hradial

/-- The planar Green profile pairs with a smooth compactly supported Laplacian as twice the
spherical obstacle value when the obstacle vanishes at its center. -/
theorem integral_planarGreenProfile_posPart_mul_laplacian_of_ball_flux
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin 2))
    (hx : w x = 0)
    (hflux : ∀ s ∈ Set.Ioc (0 : ℝ) planarGreenRadius,
      (∫ y in Metric.ball x s, Laplacian.laplacian w y) =
        s * (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          fderiv ℝ w (x + s • (ω : EuclideanSpace ℝ (Fin 2)))
            (ω : EuclideanSpace ℝ (Fin 2)) ∂(volume.toSphere))) :
    (∫ y : EuclideanSpace ℝ (Fin 2),
      max (planarGreenProfile ‖y - x‖) 0 * Laplacian.laplacian w y) =
      2 * (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        w (x + planarGreenRadius • (ω : EuclideanSpace ℝ (Fin 2)))
          ∂(volume.toSphere)) := by
  simpa only [hx, integral_zero, sub_zero] using
    integral_planarGreenProfile_posPart_mul_laplacian_of_ball_flux_general
      w hw hsupp x hflux

/-- The Newtonian Green profile pairs with a smooth compactly supported Laplacian as `n`
times the increment of its spherical integral above the center value. -/
theorem integral_newtonianGreenProfile_posPart_mul_laplacian_of_ball_flux_general
    (n : ℕ) (hn : 3 ≤ n)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin n))
    (hflux : ∀ s ∈ Set.Ioc (0 : ℝ) (greenRadius n),
      (∫ y in Metric.ball x s, Laplacian.laplacian w y) =
        s ^ (n - 1) *
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            fderiv ℝ w (x + s • (ω : EuclideanSpace ℝ (Fin n)))
              (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere))) :
    (∫ y : EuclideanSpace ℝ (Fin n),
      max (newtonianGreenProfile n ‖y - x‖) 0 * Laplacian.laplacian w y) =
      (n : ℝ) * ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (x + greenRadius n • (ω : EuclideanSpace ℝ (Fin n)))
          ∂(volume.toSphere)) -
        (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          w x ∂(volume.toSphere))) := by
  letI : NeZero n := ⟨by omega⟩
  let g : EuclideanSpace ℝ (Fin n) → ℝ := Laplacian.laplacian w
  let F : ℝ → ℝ := fun s ↦ ∫ y in Metric.ball x s, g y
  let m : ℝ → ℝ := fun s ↦
    ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      w (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)
  let q : ℝ → ℝ := fun s ↦ s ^ (n - 1) *
    ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      g (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)
  let dm : ℝ → ℝ := fun s ↦
    ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      fderiv ℝ w (x + s • (ω : EuclideanSpace ℝ (Fin n)))
        (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere)
  have hg : Continuous g := continuous_laplacian n w hw
  have hgsupp : HasCompactSupport g := hasCompactSupport_laplacian n w hsupp
  obtain ⟨B, hB⟩ := exists_bound_laplacian n w hw hsupp
  have hF : ∀ s ∈ Set.Ioc (0 : ℝ) (greenRadius n),
      HasDerivAt F (q s) s := by
    intro s hs
    exact hasDerivAt_integral_ball_radius n x g hg hgsupp hs.1
  have hm : ∀ s ∈ Set.Ioc (0 : ℝ) (greenRadius n),
      HasDerivAt m (dm s) s := by
    intro s _
    exact hasDerivAt_sphereIntegral_of_hasCompactSupport n w hw hsupp x s
  have hFflux : ∀ s ∈ Set.Ioc (0 : ℝ) (greenRadius n),
      F s = s ^ (n - 1) * dm s := by
    intro s hs
    exact hflux s hs
  have hint : IntegrableOn (fun s ↦ newtonianGreenProfile n s * q s)
      (Set.Ioo (0 : ℝ) (greenRadius n)) := by
    exact integrableOn_newtonianGreenProfile_mul_sphereIntegral n hn x g hg B hB
  have hm0 : Tendsto m (𝓝[>] (0 : ℝ))
      (𝓝 (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w x ∂(volume.toSphere))) := by
    have h := ((continuous_sphereIntegral n w hw.continuous x).continuousAt
      (x := (0 : ℝ))).tendsto
    simpa only [m, zero_smul, add_zero] using h.mono_left nhdsWithin_le_nhds
  have hboundary : Tendsto (fun s ↦ newtonianGreenProfile n s * F s)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_newtonianGreenProfile_mul_integral_ball_zero n hn g x B hB
  have hradial := integral_newtonian_green_profile_of_center_limits
    n hn (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      w x ∂(volume.toSphere)) F m q dm hF hm hFflux hint hm0 hboundary
  have hambient : Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
      max (newtonianGreenProfile n ‖y - x‖) 0 * g y) :=
    integrable_newtonianGreenProfile_posPart_mul_bdd n hn x g
      hg.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have hpolar := integral_radial_mul_polar_swapped_of_support n x
    (greenRadius n) (fun s ↦ max (newtonianGreenProfile n s) 0)
    (fun s hs ↦ newtonianGreenProfile_posPart_eq_zero_of_radius_le n hn hs)
    g hambient
  calc
    (∫ y : EuclideanSpace ℝ (Fin n),
      max (newtonianGreenProfile n ‖y - x‖) 0 * Laplacian.laplacian w y) =
        ∫ s in Set.Ioo (0 : ℝ) (greenRadius n),
          s ^ (n - 1) * max (newtonianGreenProfile n s) 0 *
            (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              g (x + s • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) :=
          hpolar
    _ = ∫ s in Set.Ioo (0 : ℝ) (greenRadius n),
        newtonianGreenProfile n s * q s := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      have hnonneg := newtonianGreenProfile_nonneg n hn hs.1 hs.2.le
      simp only [max_eq_left hnonneg, q]
      ring
    _ = (n : ℝ) *
        ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          w (x + greenRadius n • (ω : EuclideanSpace ℝ (Fin n)))
            ∂(volume.toSphere)) -
         (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          w x ∂(volume.toSphere))) := by simpa [m] using hradial

/-- The Newtonian Green profile pairs with a smooth compactly supported Laplacian as `n`
times the spherical obstacle value when the obstacle vanishes at its center. -/
theorem integral_newtonianGreenProfile_posPart_mul_laplacian_of_ball_flux
    (n : ℕ) (hn : 3 ≤ n)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin n))
    (hx : w x = 0)
    (hflux : ∀ s ∈ Set.Ioc (0 : ℝ) (greenRadius n),
      (∫ y in Metric.ball x s, Laplacian.laplacian w y) =
        s ^ (n - 1) *
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            fderiv ℝ w (x + s • (ω : EuclideanSpace ℝ (Fin n)))
              (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere))) :
    (∫ y : EuclideanSpace ℝ (Fin n),
      max (newtonianGreenProfile n ‖y - x‖) 0 * Laplacian.laplacian w y) =
      (n : ℝ) * (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (x + greenRadius n • (ω : EuclideanSpace ℝ (Fin n)))
          ∂(volume.toSphere)) := by
  simpa only [hx, integral_zero, sub_zero] using
    integral_newtonianGreenProfile_posPart_mul_laplacian_of_ball_flux_general
      n hn w hw hsupp x hflux

end CenteredMaximal.Ball
