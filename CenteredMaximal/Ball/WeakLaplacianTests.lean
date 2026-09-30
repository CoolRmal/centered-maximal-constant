/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.WeakPairingDensity
public import CenteredMaximal.Ball.CompactSupportIBP

/-!
# Distributional Laplacians and weak convergence against smooth tests

For uniformly bounded smooth compact approximants, pointwise convergence passes the
integration-by-parts identity to the limit. This supplies the weak-test hypothesis of the
Green pairing theorem from the definition of a distributional Laplacian.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace CenteredMaximal.Ball

/-- The Laplacian of `w` is represented by `g` in the distributional sense, tested
against smooth compactly supported functions. -/
def HasDistributionalLaplacian (n : ℕ)
    (w g : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
    HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      (∫ y, φ y * g y) = (∫ y, w y * Laplacian.laplacian φ y)

/-- A distributional Laplacian is the weak test limit of Laplacians of uniformly
bounded smooth compact approximants that converge pointwise to the obstacle. -/
theorem weak_test_convergence_of_distributional_laplacian (n : ℕ)
    (w g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hlimw : ∀ y, Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
    (B : ℝ) (hB : ∀ k y, ‖wₖ k y‖ ≤ B)
    (hdistribution : HasDistributionalLaplacian n w g) :
    ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        Tendsto (fun k ↦ ∫ y, φ y * Laplacian.laplacian (wₖ k) y)
          atTop (𝓝 (∫ y, φ y * g y)) := by
  intro φ hφsupp hφsmooth
  have hφtwo : ContDiff ℝ 2 φ := hφsmooth.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hΔφcont : Continuous (Laplacian.laplacian φ) :=
    continuous_laplacian n φ hφtwo
  have hΔφint : Integrable (Laplacian.laplacian φ) :=
    hΔφcont.integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian n φ hφsupp)
  have hlim : Tendsto
      (fun k ↦ ∫ y, wₖ k y * Laplacian.laplacian φ y) atTop
      (𝓝 (∫ y, w y * Laplacian.laplacian φ y)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun y ↦ B * ‖Laplacian.laplacian φ y‖)
    · intro k
      exact (hwₖ k).continuous.aestronglyMeasurable.mul
        hΔφcont.aestronglyMeasurable
    · exact hΔφint.norm.const_mul B
    · intro k
      filter_upwards with y
      calc
        ‖wₖ k y * Laplacian.laplacian φ y‖ =
            ‖wₖ k y‖ * ‖Laplacian.laplacian φ y‖ := norm_mul _ _
        _ ≤ B * ‖Laplacian.laplacian φ y‖ :=
          mul_le_mul_of_nonneg_right (hB k y) (norm_nonneg _)
    · filter_upwards with y
      exact (hlimw y).mul tendsto_const_nhds
  have hsym (k : ℕ) :
      (∫ y, φ y * Laplacian.laplacian (wₖ k) y) =
        (∫ y, wₖ k y * Laplacian.laplacian φ y) := by
    convert integral_laplacian_mul_eq_integral_mul_laplacian n
      (wₖ k) φ (hwₖ k) hφtwo (hsuppₖ k) hφsupp using 1
    · congr 1
      funext y
      ring
  simpa only [hsym, (hdistribution φ hφsupp hφsmooth).symm] using hlim

end CenteredMaximal.Ball
