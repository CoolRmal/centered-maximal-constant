/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.ObstacleTransfer

/-!
# Passing from the Green identity to an extended-real kernel comparison

The Green identity is naturally an ordinary real integral: a nonnegative kernel `q` pairs
nonnegatively with the Laplacian of an obstacle at a zero of that obstacle. The maximal-function
statement uses nonnegative extended-real integrals. This file converts the former into the latter,
allowing the kernel and capped density to agree with their real representatives only almost
everywhere. In particular, the infinite value of a Green kernel at its center causes no issue.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace CenteredMaximal.Ball

variable {E : Type*} [MeasurableSpace E] (μ : Measure E)

/-- If `f = ν - Δw` almost everywhere and a nonnegative weight has nonnegative pairing with
`Δw`, the weighted real integral of `f` is at most that of `ν`. -/
theorem weighted_integral_le_of_laplacian_pairing
    {q f ν Δw : E → ℝ}
    (hν : Integrable (fun y ↦ q y * ν y) μ)
    (hΔ : Integrable (fun y ↦ q y * Δw y) μ)
    (hrel : ∀ᵐ y ∂μ, f y = ν y - Δw y)
    (hpair : 0 ≤ ∫ y, q y * Δw y ∂μ) :
    (∫ y, q y * f y ∂μ) ≤ ∫ y, q y * ν y ∂μ := by
  have heq : (∫ y, q y * f y ∂μ) =
      (∫ y, q y * ν y ∂μ) - ∫ y, q y * Δw y ∂μ := by
    rw [← integral_sub hν hΔ]
    exact integral_congr_ae <| hrel.mono fun y hy ↦ by
      dsimp
      rw [hy]
      ring
  rw [heq]
  linarith

/-- The real Green-pairing inequality implies the corresponding `ENNReal` kernel inequality.
The extended-real weight `Q` may be infinite on a null set. -/
theorem lintegral_le_of_laplacian_pairing
    {Q : E → ℝ≥0∞} {q f ν Δw : E → ℝ}
    (hQ : ∀ᵐ y ∂μ, Q y = ENNReal.ofReal (q y))
    (hq : 0 ≤ᵐ[μ] q) (hf : 0 ≤ᵐ[μ] f) (hν : 0 ≤ᵐ[μ] ν)
    (hfint : Integrable (fun y ↦ q y * f y) μ)
    (hνint : Integrable (fun y ↦ q y * ν y) μ)
    (hΔint : Integrable (fun y ↦ q y * Δw y) μ)
    (hrel : ∀ᵐ y ∂μ, f y = ν y - Δw y)
    (hpair : 0 ≤ ∫ y, q y * Δw y ∂μ) :
    (∫⁻ y, Q y * ENNReal.ofReal (f y) ∂μ) ≤
      ∫⁻ y, Q y * ENNReal.ofReal (ν y) ∂μ := by
  have hqf : 0 ≤ᵐ[μ] (fun y ↦ q y * f y) := by
    filter_upwards [hq, hf] with y hqy hfy
    exact mul_nonneg hqy hfy
  have hqν : 0 ≤ᵐ[μ] (fun y ↦ q y * ν y) := by
    filter_upwards [hq, hν] with y hqy hνy
    exact mul_nonneg hqy hνy
  have hleft : (∫⁻ y, Q y * ENNReal.ofReal (f y) ∂μ) =
      ENNReal.ofReal (∫ y, q y * f y ∂μ) := by
    calc
      (∫⁻ y, Q y * ENNReal.ofReal (f y) ∂μ)
          = ∫⁻ y, ENNReal.ofReal (q y * f y) ∂μ := by
            apply lintegral_congr_ae
            filter_upwards [hQ, hq] with y hQy hqy
            rw [hQy, ENNReal.ofReal_mul hqy]
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hfint hqf).symm
  have hright : (∫⁻ y, Q y * ENNReal.ofReal (ν y) ∂μ) =
      ENNReal.ofReal (∫ y, q y * ν y ∂μ) := by
    calc
      (∫⁻ y, Q y * ENNReal.ofReal (ν y) ∂μ)
          = ∫⁻ y, ENNReal.ofReal (q y * ν y) ∂μ := by
            apply lintegral_congr_ae
            filter_upwards [hQ, hq] with y hQy hqy
            rw [hQy, ENNReal.ofReal_mul hqy]
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hνint hqν).symm
  rw [hleft, hright]
  exact ENNReal.ofReal_le_ofReal
    (weighted_integral_le_of_laplacian_pairing μ hνint hΔint hrel hpair)

/-- Version of `lintegral_le_of_laplacian_pairing` in the form used by the ball maximal function,
whose input is the extended norm of a real-valued nonnegative function. -/
theorem lintegral_enorm_le_of_laplacian_pairing
    {Q : E → ℝ≥0∞} {q f ν Δw : E → ℝ}
    (hQ : ∀ᵐ y ∂μ, Q y = ENNReal.ofReal (q y))
    (hq : 0 ≤ᵐ[μ] q) (hf : 0 ≤ᵐ[μ] f) (hν : 0 ≤ᵐ[μ] ν)
    (hfint : Integrable (fun y ↦ q y * f y) μ)
    (hνint : Integrable (fun y ↦ q y * ν y) μ)
    (hΔint : Integrable (fun y ↦ q y * Δw y) μ)
    (hrel : ∀ᵐ y ∂μ, f y = ν y - Δw y)
    (hpair : 0 ≤ ∫ y, q y * Δw y ∂μ) :
    (∫⁻ y, Q y * ‖f y‖ₑ ∂μ) ≤ ∫⁻ y, Q y * ENNReal.ofReal (ν y) ∂μ := by
  have heq : (∫⁻ y, Q y * ‖f y‖ₑ ∂μ) =
      ∫⁻ y, Q y * ENNReal.ofReal (f y) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hf] with y hfy
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hfy]
  rw [heq]
  exact lintegral_le_of_laplacian_pairing μ hQ hq hf hν hfint hνint hΔint hrel hpair

/-- A normalized Green-kernel comparison in exactly the form expected by an obstacle
certificate. The only kernel-specific input is its real representative almost everywhere. -/
theorem normalized_green_comparison_of_pairing
    {n : ℕ} (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ)
    {q f ν Δw : EuclideanSpace ℝ (Fin n) → ℝ}
    (hQ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      (volume (Metric.ball x r))⁻¹ * K (r⁻¹ • (x - y)) = ENNReal.ofReal (q y))
    (hq : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] q)
    (hf : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] f)
    (hν : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))] ν)
    (hfint : Integrable (fun y ↦ q y * f y))
    (hνint : Integrable (fun y ↦ q y * ν y))
    (hΔint : Integrable (fun y ↦ q y * Δw y))
    (hrel : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      f y = ν y - Δw y)
    (hpair : 0 ≤ ∫ y, q y * Δw y) :
    (∫⁻ y, (volume (Metric.ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
      ∫⁻ y, (volume (Metric.ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ENNReal.ofReal (ν y) :=
  lintegral_enorm_le_of_laplacian_pairing volume hQ hq hf hν hfint hνint hΔint hrel hpair

end CenteredMaximal.Ball
