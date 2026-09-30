/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.PairingComparison
public import CenteredMaximal.Ball.BallDensityExtension

/-!
# Kernel comparison from a local Laplacian equation

The weak obstacle equation gives the identity `f = ρ - Δu` only inside the Dirichlet domain.
The Green kernel is supported there. Hence the identity is only needed wherever the real kernel
weight is nonzero; values of the chosen Laplacian representative elsewhere can be changed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace CenteredMaximal.Ball

variable {E : Type*} [MeasurableSpace E] (μ : Measure E)

/-- The real zero extension is a representative of the extended-real density already used in
the obstacle certificate. -/
theorem extendRestrictedDensity_eq_ofReal_indicator
    (D : Set E) (ρ : E → ℝ) (x : E) :
    extendRestrictedDensity D ρ x = ENNReal.ofReal (D.indicator ρ x) := by
  classical
  by_cases hx : x ∈ D
  · simp [extendRestrictedDensity, hx]
  · simp [extendRestrictedDensity, hx]

/-- A local source identity is enough for comparison when the kernel is supported inside the
domain. The certificate density is extended by zero. -/
theorem source_relation_on_kernel_support
    (D : Set E) (hD : MeasurableSet D)
    (q f ρ g : E → ℝ)
    (hsupport : ∀ᵐ y ∂μ, q y ≠ 0 → y ∈ D)
    (hlocal : ∀ᵐ y ∂(μ.restrict D), g y = ρ y - f y) :
    ∀ᵐ y ∂μ, q y ≠ 0 → f y = D.indicator ρ y - g y := by
  have hlocal' : ∀ᵐ y ∂μ, y ∈ D → g y = ρ y - f y :=
    (ae_restrict_iff' hD).mp hlocal
  filter_upwards [hsupport, hlocal'] with y hqD hgrel hqy
  have hyD := hqD hqy
  rw [Set.indicator_of_mem hyD]
  linarith [hgrel hyD]

/-- Nonnegativity of a local real density passes to its real zero extension. -/
theorem ae_nonneg_indicator_of_ae_restrict
    (D : Set E) (hD : MeasurableSet D) (ρ : E → ℝ)
    (hρ : 0 ≤ᵐ[μ.restrict D] ρ) :
    0 ≤ᵐ[μ] D.indicator ρ := by
  have hρ' : ∀ᵐ y ∂μ, y ∈ D → 0 ≤ ρ y :=
    (ae_restrict_iff' hD).mp hρ
  filter_upwards [hρ'] with y hy
  by_cases hyD : y ∈ D
  · simpa only [Set.indicator_of_mem hyD, Pi.zero_apply] using hy hyD
  · simp [Set.indicator_of_notMem hyD]

/-- An integrable weight times a measurable function is integrable when the function is bounded
wherever the weight is nonzero. Values away from the kernel support are irrelevant. -/
theorem integrable_weighted_of_bound_on_support
    (q v : E → ℝ) (hq : Integrable q μ) (hv : AEStronglyMeasurable v μ)
    (B : ℝ)
    (hbound : ∀ᵐ y ∂μ, q y ≠ 0 → ‖v y‖ ≤ B) :
    Integrable (fun y => q y * v y) μ := by
  apply (hq.norm.const_mul B).mono' (hq.aestronglyMeasurable.mul hv)
  filter_upwards [hbound] with y hy
  by_cases hzero : q y = 0
  · simp [hzero]
  · calc
      ‖q y * v y‖ = ‖q y‖ * ‖v y‖ := norm_mul _ _
      _ ≤ ‖q y‖ * B := mul_le_mul_of_nonneg_left (hy hzero) (norm_nonneg _)
      _ = B * ‖q y‖ := mul_comm _ _

/-- Integrability specialized to a weight supported almost everywhere in a region where the
second factor is bounded. -/
theorem integrable_weighted_of_local_bound
    (q v : E → ℝ) (D : Set E)
    (hq : Integrable q μ) (hv : AEStronglyMeasurable v μ)
    (hsupport : ∀ᵐ y ∂μ, q y ≠ 0 → y ∈ D)
    (B : ℝ) (hbound : ∀ᵐ y ∂μ, y ∈ D → ‖v y‖ ≤ B) :
    Integrable (fun y => q y * v y) μ := by
  apply integrable_weighted_of_bound_on_support μ q v hq hv B
  filter_upwards [hsupport, hbound] with y hqD hvD hqy
  exact hvD (hqD hqy)

/-- A real pairing and the source identity on the support of the weight suffice for an
extended-real weighted comparison. The extended-real density may merely agree almost
everywhere with the real density viewed through `ofReal`. -/
theorem lintegral_enorm_le_of_laplacian_pairing_on_support
    {Q N : E → ℝ≥0∞} {q f ρ Δw : E → ℝ}
    (hQ : ∀ᵐ y ∂μ, Q y = ENNReal.ofReal (q y))
    (hN : ∀ᵐ y ∂μ, N y = ENNReal.ofReal (ρ y))
    (hq : 0 ≤ᵐ[μ] q) (hf : 0 ≤ᵐ[μ] f) (hρ : 0 ≤ᵐ[μ] ρ)
    (hfint : Integrable (fun y ↦ q y * f y) μ)
    (hρint : Integrable (fun y ↦ q y * ρ y) μ)
    (hΔint : Integrable (fun y ↦ q y * Δw y) μ)
    (hrel : ∀ᵐ y ∂μ, q y ≠ 0 → f y = ρ y - Δw y)
    (hpair : 0 ≤ ∫ y, q y * Δw y ∂μ) :
    (∫⁻ y, Q y * ‖f y‖ₑ ∂μ) ≤ ∫⁻ y, Q y * N y ∂μ := by
  let Δ' : E → ℝ := fun y => if q y = 0 then ρ y - f y else Δw y
  have hrel' : ∀ᵐ y ∂μ, f y = ρ y - Δ' y := by
    filter_upwards [hrel] with y hy
    by_cases hzero : q y = 0
    · simp [Δ', hzero]
    · simpa only [Δ', if_neg hzero] using hy hzero
  have hweighted : (fun y => q y * Δ' y) =ᵐ[μ] fun y => q y * Δw y := by
    filter_upwards with y
    by_cases hzero : q y = 0
    · simp [hzero]
    · simp [Δ', hzero]
  have hΔint' : Integrable (fun y => q y * Δ' y) μ := hΔint.congr hweighted.symm
  have hpair' : 0 ≤ ∫ y, q y * Δ' y ∂μ := by
    rw [integral_congr_ae hweighted]
    exact hpair
  have hcore := lintegral_enorm_le_of_laplacian_pairing μ hQ hq hf hρ
    hfint hρint hΔint' hrel' hpair'
  calc
    (∫⁻ y, Q y * ‖f y‖ₑ ∂μ)
        ≤ ∫⁻ y, Q y * ENNReal.ofReal (ρ y) ∂μ := hcore
    _ = ∫⁻ y, Q y * N y ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hN] with y hy
      rw [hy]

/-- Ball-normalized version of the comparison on the support of a Green kernel. -/
theorem normalized_green_comparison_of_pairing_on_support
    {n : ℕ} (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    {N : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    {q f ρ Δw : EuclideanSpace ℝ (Fin n) → ℝ}
    (hQ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (volume (Metric.ball x r))⁻¹ * K (r⁻¹ • (x - y)) = ENNReal.ofReal (q y))
    (hN : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      N y = ENNReal.ofReal (ρ y))
    (hq : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] q)
    (hf : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] f)
    (hρ : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] ρ)
    (hfint : Integrable (fun y ↦ q y * f y))
    (hρint : Integrable (fun y ↦ q y * ρ y))
    (hΔint : Integrable (fun y ↦ q y * Δw y))
    (hrel : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      q y ≠ 0 → f y = ρ y - Δw y)
    (hpair : 0 ≤ ∫ y, q y * Δw y) :
    (∫⁻ y, (volume (Metric.ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
      ∫⁻ y, (volume (Metric.ball x r))⁻¹ * K (r⁻¹ • (x - y)) * N y :=
  lintegral_enorm_le_of_laplacian_pairing_on_support volume hQ hN hq hf hρ
    hfint hρint hΔint hrel hpair

end CenteredMaximal.Ball
