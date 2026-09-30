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
bounded smooth compact approximants that converge almost everywhere to the obstacle. -/
theorem weak_test_convergence_of_distributional_laplacian (n : ℕ)
    (w g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hlimw : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
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
    · filter_upwards [hlimw] with y hy
      exact hy.mul tendsto_const_nhds
  have hsym (k : ℕ) :
      (∫ y, φ y * Laplacian.laplacian (wₖ k) y) =
        (∫ y, wₖ k y * Laplacian.laplacian φ y) := by
    convert integral_laplacian_mul_eq_integral_mul_laplacian n
      (wₖ k) φ (hwₖ k) hφtwo (hsuppₖ k) hφsupp using 1
    · congr 1
      funext y
      ring
  simpa only [hsym, (hdistribution φ hφsupp hφsmooth).symm] using hlim

/-- Positivity of the limiting Green pairing only requires convergence of the
pairings and convergence of the approximating obstacles at the center. The
spherical averages stay nonnegative and need not converge. -/
theorem nonneg_green_pairing_of_integral_convergence (n : ℕ) [NeZero n]
    (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ gₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (hlimK : Tendsto (fun k ↦ ∫ y, K y * gₖ k y) atTop
      (𝓝 (∫ y, K y * g y)))
    (x : EuclideanSpace ℝ (Fin n))
    (hcenter : Tendsto (fun k ↦ wₖ k x) atTop (𝓝 0))
    (ρ c : ℝ) (hc : 0 ≤ c)
    (hpair : ∀ k,
      (∫ y, K y * gₖ k y) = c *
        ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          wₖ k (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) -
         (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          wₖ k x ∂(volume.toSphere)))) :
    0 ≤ ∫ y, K y * g y := by
  have hcenterInt : Tendsto
      (fun k ↦ ∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        wₖ k x ∂(volume.toSphere)) atTop (𝓝 0) := by
    simp only [integral_const, smul_eq_mul]
    convert (tendsto_const_nhds.mul hcenter) using 1
    simp
  have hleft : Tendsto (fun k ↦
      -(c * ∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        wₖ k x ∂(volume.toSphere))) atTop (𝓝 0) := by
    simpa using (hcenterInt.const_mul c).neg
  apply le_of_tendsto_of_tendsto hleft hlimK
  apply Filter.Eventually.of_forall
  intro k
  have hsphere : 0 ≤
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        wₖ k (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere) :=
    integral_nonneg fun ω ↦ hwₖ_nonneg k _
  dsimp only
  rw [hpair k]
  nlinarith [mul_nonneg hc hsphere]

/-- Weak convergence of bounded densities supplies the pairing convergence in
`nonneg_green_pairing_of_integral_convergence`. The same center set works for
every radius. -/
theorem nonneg_green_pairing_of_weak_test_convergence (n : ℕ) [NeZero n]
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ gₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (hg : AEStronglyMeasurable g volume)
    (hgₖ : ∀ k, AEStronglyMeasurable (gₖ k) volume)
    (B : ℝ) (hB₀ : 0 ≤ B)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B)
    (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ‖gₖ k y‖ ≤ B)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        Tendsto (fun k ↦ ∫ y, φ y * gₖ k y) atTop (𝓝 (∫ y, φ y * g y)))
    (x : EuclideanSpace ℝ (Fin n))
    (hcenter : Tendsto (fun k ↦ wₖ k x) atTop (𝓝 0))
    (ρ c : ℝ) (hc : 0 ≤ c)
    (hpair : ∀ k,
      (∫ y, K y * gₖ k y) = c *
        ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          wₖ k (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) -
         (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          wₖ k x ∂(volume.toSphere)))) :
    0 ≤ ∫ y, K y * g y := by
  apply nonneg_green_pairing_of_integral_convergence n K g wₖ gₖ hwₖ_nonneg
    (tendsto_integral_mul_of_weak_test_convergence n g gₖ
      hg hgₖ B hB₀ hBg hBgₖ hweak K hK) x hcenter ρ c hc hpair

/-- The planar normalized Green pairing is nonnegative at every center where
nonnegative smooth approximants converge to zero. No spherical trace of the
limit obstacle is required. -/
theorem integral_normalized_planarKernel_mul_weakLaplacian_nonneg_of_weak_tests
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (hg : AEStronglyMeasurable g volume)
    (B : ℝ) (hB₀ : 0 ≤ B)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))), ‖g y‖ ≤ B)
    (hBgₖ : ∀ k y, ‖Laplacian.laplacian (wₖ k) y‖ ≤ B)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        Tendsto (fun k ↦ ∫ y, φ y * Laplacian.laplacian (wₖ k) y)
          atTop (𝓝 (∫ y, φ y * g y)))
    (x : EuclideanSpace ℝ (Fin 2))
    (hcenter : Tendsto (fun k ↦ wₖ k x) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r) :
    0 ≤ (∫ y : EuclideanSpace ℝ (Fin 2),
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal * g y) := by
  let K : EuclideanSpace ℝ (Fin 2) → ℝ := fun y ↦
    ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal
  have hK : Integrable K := (normalized_planarKernel_real_representative x hr).1
  apply nonneg_green_pairing_of_weak_test_convergence 2 K hK g wₖ
    (fun k ↦ Laplacian.laplacian (wₖ k)) hwₖ_nonneg hg
    (fun k ↦ (continuous_laplacian 2 (wₖ k) (hwₖ k)).aestronglyMeasurable)
    B hB₀ hBg (fun k ↦ Filter.Eventually.of_forall (hBgₖ k)) hweak
    x hcenter (r * planarGreenRadius)
    (((volume (Metric.ball x r))⁻¹).toReal * 2)
    (mul_nonneg ENNReal.toReal_nonneg (by norm_num))
  intro k
  have h := integral_normalized_planarKernel_mul_laplacian_general
    (wₖ k) (hwₖ k) (hsuppₖ k) x hr
  simpa only [K, mul_assoc, smul_smul, mul_comm r planarGreenRadius] using h

/-- The corresponding Newtonian comparison in every dimension at least three. -/
theorem integral_normalized_newtonianKernel_mul_weakLaplacian_nonneg_of_weak_tests
    (n : ℕ) (hn : 3 ≤ n)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (hg : AEStronglyMeasurable g volume)
    (B : ℝ) (hB₀ : 0 ≤ B)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B)
    (hBgₖ : ∀ k y, ‖Laplacian.laplacian (wₖ k) y‖ ≤ B)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        Tendsto (fun k ↦ ∫ y, φ y * Laplacian.laplacian (wₖ k) y)
          atTop (𝓝 (∫ y, φ y * g y)))
    (x : EuclideanSpace ℝ (Fin n))
    (hcenter : Tendsto (fun k ↦ wₖ k x) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r) :
    0 ≤ (∫ y : EuclideanSpace ℝ (Fin n),
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
        g y) := by
  letI : NeZero n := ⟨by omega⟩
  let K : EuclideanSpace ℝ (Fin n) → ℝ := fun y ↦
    ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal
  have hK : Integrable K := (normalized_newtonianKernel_real_representative n hn x hr).1
  apply nonneg_green_pairing_of_weak_test_convergence n K hK g wₖ
    (fun k ↦ Laplacian.laplacian (wₖ k)) hwₖ_nonneg hg
    (fun k ↦ (continuous_laplacian n (wₖ k) (hwₖ k)).aestronglyMeasurable)
    B hB₀ hBg (fun k ↦ Filter.Eventually.of_forall (hBgₖ k)) hweak
    x hcenter (r * greenRadius n)
    (((volume (Metric.ball x r))⁻¹).toReal * r ^ (n - 2) * (n : ℝ))
    (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hr.le _))
      (Nat.cast_nonneg _))
  intro k
  have h := integral_normalized_newtonianKernel_mul_laplacian_general
    n hn (wₖ k) (hwₖ k) (hsuppₖ k) x hr
  simpa only [K, mul_assoc, smul_smul, mul_comm r (greenRadius n)] using h

/-- A distributional planar obstacle gives Green comparison for almost every
point of its zero set, simultaneously for every positive radius. -/
theorem ae_planar_green_pairing_nonneg_of_distributional_laplacian
    (w g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (hlimw : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
    (B₁ : ℝ) (hB₁ : ∀ k y, ‖wₖ k y‖ ≤ B₁)
    (hdistribution : HasDistributionalLaplacian 2 w g)
    (hg : AEStronglyMeasurable g volume)
    (B₂ : ℝ) (hB₂₀ : 0 ≤ B₂)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))), ‖g y‖ ≤ B₂)
    (hBgₖ : ∀ k y, ‖Laplacian.laplacian (wₖ k) y‖ ≤ B₂)
    (Ω : Set (EuclideanSpace ℝ (Fin 2)))
    (hzero : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      x ∉ Ω → w x = 0) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      x ∉ Ω → ∀ r : ℝ, 0 < r →
        0 ≤ (∫ y : EuclideanSpace ℝ (Fin 2),
          ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal *
            g y) := by
  have hweak := weak_test_convergence_of_distributional_laplacian 2 w g wₖ
    hwₖ hsuppₖ hlimw B₁ hB₁ hdistribution
  filter_upwards [hlimw, hzero] with x hxlim hxzero
  intro hx r hr
  apply integral_normalized_planarKernel_mul_weakLaplacian_nonneg_of_weak_tests
    g wₖ hwₖ hsuppₖ hwₖ_nonneg hg B₂ hB₂₀ hBg hBgₖ hweak x
  · simpa only [hxzero hx] using hxlim
  · exact hr

/-- The corresponding Newtonian comparison for almost every center outside
the contact set, with one full-measure set valid for all positive radii. -/
theorem ae_newtonian_green_pairing_nonneg_of_distributional_laplacian
    (n : ℕ) (hn : 3 ≤ n)
    (w g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (hlimw : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
    (B₁ : ℝ) (hB₁ : ∀ k y, ‖wₖ k y‖ ≤ B₁)
    (hdistribution : HasDistributionalLaplacian n w g)
    (hg : AEStronglyMeasurable g volume)
    (B₂ : ℝ) (hB₂₀ : 0 ≤ B₂)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B₂)
    (hBgₖ : ∀ k y, ‖Laplacian.laplacian (wₖ k) y‖ ≤ B₂)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hzero : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∉ Ω → w x = 0) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∉ Ω → ∀ r : ℝ, 0 < r →
        0 ≤ (∫ y : EuclideanSpace ℝ (Fin n),
          ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
            g y) := by
  have hweak := weak_test_convergence_of_distributional_laplacian n w g wₖ
    hwₖ hsuppₖ hlimw B₁ hB₁ hdistribution
  filter_upwards [hlimw, hzero] with x hxlim hxzero
  intro hx r hr
  apply integral_normalized_newtonianKernel_mul_weakLaplacian_nonneg_of_weak_tests
    n hn g wₖ hwₖ hsuppₖ hwₖ_nonneg hg B₂ hB₂₀ hBg hBgₖ hweak x
  · simpa only [hxzero hx] using hxlim
  · exact hr

end CenteredMaximal.Ball
