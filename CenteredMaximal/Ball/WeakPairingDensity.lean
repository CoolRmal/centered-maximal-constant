/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.WeakGreenPairing
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Extending weak convergence of bounded densities to integrable kernels

Uniformly bounded densities define uniformly bounded functionals on `L¹`.
Consequently, convergence of their pairings with smooth compact tests extends to
all integrable kernels, including the singular Green kernels.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter
open scoped ENNReal Topology

namespace CenteredMaximal.Ball

private theorem norm_integral_mul_sub_le (n : ℕ)
    (K φ g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hK : Integrable K) (hφ : Integrable φ)
    (hg : AEStronglyMeasurable g volume)
    {B : ℝ} (hB : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B) :
    ‖(∫ y, K y * g y) - (∫ y, φ y * g y)‖ ≤
      B * ∫ y, ‖K y - φ y‖ := by
  have hKg : Integrable (fun y ↦ K y * g y) := hK.mul_bdd hg hB
  have hφg : Integrable (fun y ↦ φ y * g y) := hφ.mul_bdd hg hB
  have hdiff : Integrable (fun y ↦ (K y - φ y) * g y) :=
    (hK.sub hφ).mul_bdd hg hB
  have hnormdiff : Integrable (fun y ↦ ‖K y - φ y‖) := (hK.sub hφ).norm
  rw [← integral_sub hKg hφg]
  have hfun : (fun y ↦ K y * g y - φ y * g y) =
      (fun y ↦ (K y - φ y) * g y) := by
    funext y
    ring
  rw [hfun]
  calc
    ‖∫ y, (K y - φ y) * g y‖ ≤
        ∫ y, ‖(K y - φ y) * g y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, B * ‖K y - φ y‖ := by
      apply integral_mono_ae hdiff.norm (hnormdiff.const_mul B)
      filter_upwards [hB] with y hy
      rw [norm_mul]
      calc
        ‖K y - φ y‖ * ‖g y‖ ≤ ‖K y - φ y‖ * B :=
          mul_le_mul_of_nonneg_left hy (norm_nonneg _)
        _ = B * ‖K y - φ y‖ := mul_comm _ _
    _ = B * ∫ y, ‖K y - φ y‖ := by rw [integral_const_mul]

private theorem exists_smooth_compact_integral_norm_sub_le (n : ℕ)
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ ∧ ContDiff ℝ (↑(⊤ : ℕ∞)) φ ∧
        (∫ y, ‖K y - φ y‖) ≤ ε := by
  obtain ⟨φ, hφsupp, hφsmooth, hclose⟩ :=
    (memLp_one_iff_integrable.mpr hK).exist_eLpNorm_sub_le
      (by norm_num) (by norm_num) hε
  refine ⟨φ, hφsupp, hφsmooth, ?_⟩
  have hφint : Integrable φ := hφsmooth.continuous.integrable_of_hasCompactSupport hφsupp
  have hdiff : Integrable (K - φ) := hK.sub hφint
  have hreal := ENNReal.toReal_le_of_le_ofReal hε.le hclose
  simp only [eLpNorm_one_eq_lintegral_enorm hdiff.aestronglyMeasurable,
    Pi.sub_apply] at hreal
  have hEq := integral_norm_eq_lintegral_enorm hdiff.aestronglyMeasurable
  simp only [Pi.sub_apply] at hEq
  exact hEq.trans_le hreal

/-- A uniformly bounded sequence of densities that converges weakly against every
smooth compactly supported test also converges against every integrable kernel.
This is the density step needed for Green kernels, which are singular but in `L¹`. -/
theorem tendsto_integral_mul_of_weak_test_convergence (n : ℕ)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (gₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : AEStronglyMeasurable g volume)
    (hgₖ : ∀ k, AEStronglyMeasurable (gₖ k) volume)
    (B : ℝ) (hB₀ : 0 ≤ B)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B)
    (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ‖gₖ k y‖ ≤ B)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        Tendsto (fun k ↦ ∫ y, φ y * gₖ k y) atTop (𝓝 (∫ y, φ y * g y)))
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K) :
    Tendsto (fun k ↦ ∫ y, K y * gₖ k y) atTop (𝓝 (∫ y, K y * g y)) := by
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  let δ : ℝ := ε / (8 * (B + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨φ, hφsupp, hφsmooth, hclose⟩ :=
    exists_smooth_compact_integral_norm_sub_le n K hK hδ
  have hφint : Integrable φ := hφsmooth.continuous.integrable_of_hasCompactSupport hφsupp
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 (hweak φ hφsupp hφsmooth))
    (ε / 2) (half_pos hε)
  refine ⟨N, fun k hk ↦ ?_⟩
  rw [Real.dist_eq]
  have hleft := norm_integral_mul_sub_le n K φ (gₖ k) hK hφint
    (hgₖ k) (hBgₖ k)
  have hright := norm_integral_mul_sub_le n K φ g hK hφint hg hBg
  have hsmall : B * (∫ y, ‖K y - φ y‖) ≤ B * δ :=
    mul_le_mul_of_nonneg_left hclose hB₀
  have hmiddle : |(∫ y, φ y * gₖ k y) - (∫ y, φ y * g y)| < ε / 2 := by
    simpa only [Real.dist_eq] using hN k hk
  have htri : |(∫ y, K y * gₖ k y) - (∫ y, K y * g y)| ≤
      |(∫ y, K y * gₖ k y) - (∫ y, φ y * gₖ k y)| +
      |(∫ y, φ y * gₖ k y) - (∫ y, φ y * g y)| +
      |(∫ y, φ y * g y) - (∫ y, K y * g y)| := by
    have h₁ := abs_add_le
      ((∫ y, K y * gₖ k y) - (∫ y, φ y * gₖ k y))
      ((∫ y, φ y * gₖ k y) - (∫ y, φ y * g y))
    have h₂ := abs_add_le
      (((∫ y, K y * gₖ k y) - (∫ y, φ y * gₖ k y)) +
        ((∫ y, φ y * gₖ k y) - (∫ y, φ y * g y)))
      ((∫ y, φ y * g y) - (∫ y, K y * g y))
    have h₃ :
        |((∫ y, K y * gₖ k y) - (∫ y, φ y * gₖ k y)) +
          ((∫ y, φ y * gₖ k y) - (∫ y, φ y * g y)) +
          ((∫ y, φ y * g y) - (∫ y, K y * g y))| ≤
        |(∫ y, K y * gₖ k y) - (∫ y, φ y * gₖ k y)| +
        |(∫ y, φ y * gₖ k y) - (∫ y, φ y * g y)| +
        |(∫ y, φ y * g y) - (∫ y, K y * g y)| := by linarith
    convert h₃ using 1; ring_nf
  calc
    |(∫ y, K y * gₖ k y) - (∫ y, K y * g y)| ≤ _ := htri
    _ < B * δ + ε / 2 + B * δ := by
      rw [abs_sub_comm (∫ y, φ y * g y) (∫ y, K y * g y)]
      have hl : |(∫ y, K y * gₖ k y) - (∫ y, φ y * gₖ k y)| ≤ B * δ :=
        hleft.trans hsmall
      have hr : |(∫ y, K y * g y) - (∫ y, φ y * g y)| ≤ B * δ :=
        hright.trans hsmall
      linarith
    _ < ε := by
      have hBpos : 0 < B + 1 := by linarith
      have hratio : B / (B + 1) < 1 :=
        (div_lt_one hBpos).2 (by linarith)
      have hbound : B * δ < ε / 8 := by
        calc
          B * δ = (ε / 8) * (B / (B + 1)) := by
            dsimp [δ]
            field_simp
          _ < (ε / 8) * 1 := mul_lt_mul_of_pos_left hratio (by positivity)
          _ = ε / 8 := by ring
      linarith

/-- A Green identity survives weak convergence against smooth compact tests when
the approximating Laplacians are uniformly bounded. The singular Green kernel
enters only through its `L¹` integrability. -/
theorem green_pairing_stable_under_weak_test_convergence (n : ℕ) [NeZero n]
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (w g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ gₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, Continuous (wₖ k))
    (hg : AEStronglyMeasurable g volume)
    (hgₖ : ∀ k, AEStronglyMeasurable (gₖ k) volume)
    (hlimw : ∀ y, Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
    (B₁ B₂ : ℝ) (hB₁ : ∀ k y, ‖wₖ k y‖ ≤ B₁)
    (hB₂₀ : 0 ≤ B₂)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B₂)
    (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ‖gₖ k y‖ ≤ B₂)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        Tendsto (fun k ↦ ∫ y, φ y * gₖ k y) atTop (𝓝 (∫ y, φ y * g y)))
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
  apply green_pairing_stable_under_weighted_integral_convergence n K w g wₖ gₖ
    hwₖ hlimw B₁ hB₁
    (tendsto_integral_mul_of_weak_test_convergence n g gₖ hg hgₖ B₂
      hB₂₀ hBg hBgₖ hweak K hK) x ρ c hpair

/-- The planar Green pairing extends to an obstacle whose Laplacian is only a bounded
measurable function, provided smooth approximants converge pointwise and their
Laplacians converge weakly against smooth compact tests. -/
theorem integral_normalized_planarKernel_mul_weakLaplacian_of_weak_tests
    (w g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hlimw : ∀ y, Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
    (hg : AEStronglyMeasurable g volume)
    (B₁ B₂ : ℝ) (hB₁ : ∀ k y, ‖wₖ k y‖ ≤ B₁)
    (hB₂₀ : 0 ≤ B₂)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))), ‖g y‖ ≤ B₂)
    (hBgₖ : ∀ k y, ‖Laplacian.laplacian (wₖ k) y‖ ≤ B₂)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        Tendsto (fun k ↦ ∫ y, φ y * Laplacian.laplacian (wₖ k) y)
          atTop (𝓝 (∫ y, φ y * g y)))
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
  apply green_pairing_stable_under_weak_test_convergence 2 K hK w g wₖ
    (fun k ↦ Laplacian.laplacian (wₖ k))
    (fun k ↦ (hwₖ k).continuous) hg
    (fun k ↦ (continuous_laplacian 2 (wₖ k) (hwₖ k)).aestronglyMeasurable)
    hlimw B₁ B₂ hB₁ hB₂₀ hBg
    (fun k ↦ Filter.Eventually.of_forall (hBgₖ k)) hweak x
    (r * planarGreenRadius) (((volume (Metric.ball x r))⁻¹).toReal * 2)
  intro k
  have h := integral_normalized_planarKernel_mul_laplacian_general
    (wₖ k) (hwₖ k) (hsuppₖ k) x hr
  simpa only [K, mul_assoc, smul_smul, mul_comm r planarGreenRadius] using h

/-- The corresponding weak Newtonian Green pairing in every dimension `n ≥ 3`. -/
theorem integral_normalized_newtonianKernel_mul_weakLaplacian_of_weak_tests
    (n : ℕ) (hn : 3 ≤ n)
    (w g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hlimw : ∀ y, Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
    (hg : AEStronglyMeasurable g volume)
    (B₁ B₂ : ℝ) (hB₁ : ∀ k y, ‖wₖ k y‖ ≤ B₁)
    (hB₂₀ : 0 ≤ B₂)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B₂)
    (hBgₖ : ∀ k y, ‖Laplacian.laplacian (wₖ k) y‖ ≤ B₂)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        Tendsto (fun k ↦ ∫ y, φ y * Laplacian.laplacian (wₖ k) y)
          atTop (𝓝 (∫ y, φ y * g y)))
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
  apply green_pairing_stable_under_weak_test_convergence n K hK w g wₖ
    (fun k ↦ Laplacian.laplacian (wₖ k))
    (fun k ↦ (hwₖ k).continuous) hg
    (fun k ↦ (continuous_laplacian n (wₖ k) (hwₖ k)).aestronglyMeasurable)
    hlimw B₁ B₂ hB₁ hB₂₀ hBg
    (fun k ↦ Filter.Eventually.of_forall (hBgₖ k)) hweak x
    (r * greenRadius n)
    (((volume (Metric.ball x r))⁻¹).toReal * r ^ (n - 2) * (n : ℝ))
  intro k
  have h := integral_normalized_newtonianKernel_mul_laplacian_general
    n hn (wₖ k) (hwₖ k) (hsuppₖ k) x hr
  simpa only [K, mul_assoc, smul_smul, mul_comm r (greenRadius n)] using h

end CenteredMaximal.Ball
