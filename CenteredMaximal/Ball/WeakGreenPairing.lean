/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.ScaledGreenPairing
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Stability of Green pairings under bounded approximation

The obstacle supplied by the variational construction need not be twice continuously
differentiable. This file isolates the convergence argument that transfers a Green
pairing from smooth approximants to a continuous obstacle with a bounded weak
Laplacian. The existence and properties of the approximants remain explicit hypotheses.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

namespace CenteredMaximal.Ball

private theorem tendsto_sphereIntegral_of_bounded_approximations (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, Continuous (wₖ k))
    (hlim : ∀ y, Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
    (B : ℝ) (hB : ∀ k y, ‖wₖ k y‖ ≤ B)
    (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 →
      EuclideanSpace ℝ (Fin n)) (hp : Continuous p) :
    Tendsto (fun k ↦ ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      wₖ k (p ω) ∂(volume.toSphere)) atTop
      (𝓝 (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (p ω) ∂(volume.toSphere))) := by
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ B)
  · intro k
    exact ((hwₖ k).comp hp).aestronglyMeasurable
  · exact integrable_const B
  · intro k
    filter_upwards with ω
    exact hB k (p ω)
  · filter_upwards with ω
    exact hlim (p ω)

/-- An exact Green identity for uniformly bounded smooth approximants passes to a
continuous obstacle when their Laplacians converge almost everywhere under a common
bound. This theorem applies to any integrable real kernel. -/
theorem green_pairing_stable_under_bounded_approximation (n : ℕ) [NeZero n]
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (w g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ gₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, Continuous (wₖ k))
    (hgₖ : ∀ k, AEStronglyMeasurable (gₖ k) volume)
    (hlimw : ∀ y, Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
    (hlimg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun k ↦ gₖ k y) atTop (𝓝 (g y)))
    (B₁ B₂ : ℝ) (hB₁ : ∀ k y, ‖wₖ k y‖ ≤ B₁)
    (hB₂ : ∀ k y, ‖gₖ k y‖ ≤ B₂)
    (x : EuclideanSpace ℝ (Fin n)) (ρ c : ℝ)
    (hpair : ∀ k,
      (∫ y, K y * gₖ k y) = c *
        ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          wₖ k (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) -
         (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          wₖ k x ∂(volume.toSphere)))) :
    (∫ y, K y * g y) = c *
      ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) -
       (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w x ∂(volume.toSphere))) := by
  have hleft : Tendsto (fun k ↦ ∫ y, K y * gₖ k y) atTop
      (𝓝 (∫ y, K y * g y)) := by
    apply tendsto_integral_of_dominated_convergence (fun y ↦ B₂ * ‖K y‖)
    · intro k
      exact hK.aestronglyMeasurable.mul (hgₖ k)
    · exact hK.norm.const_mul B₂
    · intro k
      filter_upwards with y
      calc
        ‖K y * gₖ k y‖ = ‖K y‖ * ‖gₖ k y‖ := norm_mul _ _
        _ ≤ ‖K y‖ * B₂ := mul_le_mul_of_nonneg_left (hB₂ k y) (norm_nonneg _)
        _ = B₂ * ‖K y‖ := mul_comm _ _
    · filter_upwards [hlimg] with y hy
      exact tendsto_const_nhds.mul hy
  have houter : Tendsto (fun k ↦
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        wₖ k (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) atTop
      (𝓝 (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere))) :=
    tendsto_sphereIntegral_of_bounded_approximations n w wₖ hwₖ hlimw B₁ hB₁
      (fun ω ↦ x + ρ • (ω : EuclideanSpace ℝ (Fin n))) (by fun_prop)
  have hcenter : Tendsto (fun k ↦
      ∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        wₖ k x ∂(volume.toSphere)) atTop
      (𝓝 (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w x ∂(volume.toSphere))) :=
    tendsto_sphereIntegral_of_bounded_approximations n w wₖ hwₖ hlimw B₁ hB₁
      (fun _ ↦ x) continuous_const
  have hright := (houter.sub hcenter).const_mul c
  exact tendsto_nhds_unique (hleft.congr' (Filter.Eventually.of_forall hpair)) hright

/-- Stability under convergence of the single weighted Laplacian pairing. This is the
form supplied by weak Lᵖ or weak-star L∞ convergence of the penalized obstacle
Laplacians; pointwise convergence of those Laplacians is unnecessary. -/
theorem green_pairing_stable_under_weighted_integral_convergence (n : ℕ) [NeZero n]
    (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (w g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ gₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, Continuous (wₖ k))
    (hlimw : ∀ y, Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
    (B : ℝ) (hB : ∀ k y, ‖wₖ k y‖ ≤ B)
    (hweighted : Tendsto (fun k ↦ ∫ y, K y * gₖ k y) atTop
      (𝓝 (∫ y, K y * g y)))
    (x : EuclideanSpace ℝ (Fin n)) (ρ c : ℝ)
    (hpair : ∀ k,
      (∫ y, K y * gₖ k y) = c *
        ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          wₖ k (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) -
         (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          wₖ k x ∂(volume.toSphere)))) :
    (∫ y, K y * g y) = c *
      ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) -
       (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w x ∂(volume.toSphere))) := by
  have houter : Tendsto (fun k ↦
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        wₖ k (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) atTop
      (𝓝 (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere))) :=
    tendsto_sphereIntegral_of_bounded_approximations n w wₖ hwₖ hlimw B hB
      (fun ω ↦ x + ρ • (ω : EuclideanSpace ℝ (Fin n))) (by fun_prop)
  have hcenter : Tendsto (fun k ↦
      ∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        wₖ k x ∂(volume.toSphere)) atTop
      (𝓝 (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w x ∂(volume.toSphere))) :=
    tendsto_sphereIntegral_of_bounded_approximations n w wₖ hwₖ hlimw B hB
      (fun _ ↦ x) continuous_const
  have hright := (houter.sub hcenter).const_mul c
  exact tendsto_nhds_unique (hweighted.congr' (Filter.Eventually.of_forall hpair)) hright

/-- The planar Green identity extends to a continuous obstacle with bounded weak
Laplacian once it has uniformly bounded smooth approximants whose Laplacians converge
almost everywhere. -/
theorem integral_normalized_planarKernel_mul_weakLaplacian_of_approximation
    (w g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hlimw : ∀ y, Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
    (hlimg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      Tendsto (fun k ↦ Laplacian.laplacian (wₖ k) y) atTop (𝓝 (g y)))
    (B₁ B₂ : ℝ) (hB₁ : ∀ k y, ‖wₖ k y‖ ≤ B₁)
    (hB₂ : ∀ k y, ‖Laplacian.laplacian (wₖ k) y‖ ≤ B₂)
    (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    (∫ y : EuclideanSpace ℝ (Fin 2),
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal * g y) =
      ((volume (Metric.ball x r))⁻¹).toReal * 2 *
        ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          w (x + (r * planarGreenRadius) • (ω : EuclideanSpace ℝ (Fin 2)))
            ∂(volume.toSphere)) -
         (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          w x ∂(volume.toSphere))) := by
  let K : EuclideanSpace ℝ (Fin 2) → ℝ := fun y ↦
    ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal
  have hK : Integrable K := (normalized_planarKernel_real_representative x hr).1
  apply green_pairing_stable_under_bounded_approximation 2 K hK w g wₖ
    (fun k ↦ Laplacian.laplacian (wₖ k))
    (fun k ↦ (hwₖ k).continuous)
    (fun k ↦ (continuous_laplacian 2 (wₖ k) (hwₖ k)).aestronglyMeasurable)
    hlimw hlimg B₁ B₂ hB₁ hB₂ x (r * planarGreenRadius)
    (((volume (Metric.ball x r))⁻¹).toReal * 2)
  intro k
  have h := integral_normalized_planarKernel_mul_laplacian_general
    (wₖ k) (hwₖ k) (hsuppₖ k) x hr
  simpa only [K, mul_assoc, smul_smul, mul_comm r planarGreenRadius] using h

/-- The Newtonian Green identity extends to a continuous obstacle with bounded weak
Laplacian under the same bounded approximation hypotheses. -/
theorem integral_normalized_newtonianKernel_mul_weakLaplacian_of_approximation
    (n : ℕ) (hn : 3 ≤ n)
    (w g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hlimw : ∀ y, Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
    (hlimg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun k ↦ Laplacian.laplacian (wₖ k) y) atTop (𝓝 (g y)))
    (B₁ B₂ : ℝ) (hB₁ : ∀ k y, ‖wₖ k y‖ ≤ B₁)
    (hB₂ : ∀ k y, ‖Laplacian.laplacian (wₖ k) y‖ ≤ B₂)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    (∫ y : EuclideanSpace ℝ (Fin n),
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
        g y) =
      ((volume (Metric.ball x r))⁻¹).toReal * r ^ (n - 2) * (n : ℝ) *
        ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          w (x + (r * greenRadius n) • (ω : EuclideanSpace ℝ (Fin n)))
            ∂(volume.toSphere)) -
         (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          w x ∂(volume.toSphere))) := by
  letI : NeZero n := ⟨by omega⟩
  let K : EuclideanSpace ℝ (Fin n) → ℝ := fun y ↦
    ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal
  have hK : Integrable K := (normalized_newtonianKernel_real_representative n hn x hr).1
  apply green_pairing_stable_under_bounded_approximation n K hK w g wₖ
    (fun k ↦ Laplacian.laplacian (wₖ k))
    (fun k ↦ (hwₖ k).continuous)
    (fun k ↦ (continuous_laplacian n (wₖ k) (hwₖ k)).aestronglyMeasurable)
    hlimw hlimg B₁ B₂ hB₁ hB₂ x (r * greenRadius n)
    (((volume (Metric.ball x r))⁻¹).toReal * r ^ (n - 2) * (n : ℝ))
  intro k
  have h := integral_normalized_newtonianKernel_mul_laplacian_general
    n hn (wₖ k) (hwₖ k) (hsuppₖ k) x hr
  simpa only [K, mul_assoc, smul_smul, mul_comm r (greenRadius n)] using h

end CenteredMaximal.Ball
