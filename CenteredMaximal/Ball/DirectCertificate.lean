/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.FinalReduction

/-!
# A direct contact-mass obstacle criterion

The obstacle variational inequality can control the contact-set measure directly by testing
against a truncation of the obstacle. This avoids integrating its Laplacian over the outer
boundary. The criterion here accepts that direct measure bound, together with the density cap
and local Green comparison, and gives the same maximal inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal ContDiff

namespace CenteredMaximal.Ball

variable {n : ℕ} [Nonempty (Fin n)]

/-- The direct form of an obstacle certificate. It asks for a contact-set mass bound rather
than a total-mass bound on the capped density. -/
def HasDirectObstacleCertificates (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) : Prop :=
  ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
    HasCompactSupport f → ContDiff ℝ ∞ f → (∀ x, 0 ≤ f x) →
    ∀ (κ : ℝ≥0∞), 0 < κ → κ ≠ (∞ : ℝ≥0∞) →
      ∀ (R r₀ : ℝ), 0 < r₀ → (∀ y, R ≤ ‖y‖ → f y = 0) →
        ∃ (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (ν : EuclideanSpace ℝ (Fin n) → ℝ≥0∞),
          κ * volume Ω ≤ ∫⁻ y, ‖f y‖ₑ ∧
          (∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ν y ≤ κ) ∧
          (∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ),
            x ∉ Ω → 0 < r → r < r₀ → ‖x‖ < R + r₀ →
              (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
                ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y)

omit [Nonempty (Fin n)] in
/-- A certificate with density mass and contact equality also supplies the direct
contact-set mass bound. -/
theorem HasObstacleCertificates.toDirect
    {K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (h : HasObstacleCertificates K) : HasDirectObstacleCertificates K := by
  intro f hfcomp hfsmooth hfnn κ hκ₀ hκtop R r₀ hr₀ hsupp
  obtain ⟨Ω, ν, hΩ, hcontact, hmass, hcap, hgreen⟩ :=
    h f hfcomp hfsmooth hfnn κ hκ₀ hκtop R r₀ hr₀ hsupp
  exact ⟨Ω, ν, (contact_measure_le_density_mass Ω hΩ ν κ hcontact).trans hmass,
    hcap, hgreen⟩

/-- Direct obstacle certificates give the weak type estimate for smooth nonnegative data. -/
theorem isSmoothBallWeakTypeBound_of_direct_obstacle_certificates
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (C : ℝ≥0∞)
    (hC₀ : 0 < C) (hCtop : C ≠ (∞ : ℝ≥0∞))
    (hKunit : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1 ≤ K z)
    (hKmass : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) = C)
    (hcertificate : HasDirectObstacleCertificates K) :
    IsSmoothBallWeakTypeBound n C := by
  intro f hfcomp hfsmooth hfnn α
  have hf : Integrable f := hfsmooth.continuous.integrable_of_hasCompactSupport hfcomp
  obtain ⟨R, hsupp⟩ := exists_support_radius hfcomp
  refine ball_level_bound_of_scaled_levels C hC₀ hCtop f ?_ α
  intro κ hκ₀ hκtop
  have hA₀ : 0 < C * κ := ENNReal.mul_pos hC₀.ne' hκ₀.ne'
  have hAtop : C * κ ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top hCtop hκtop
  obtain ⟨r₀, hr₀, hlarge⟩ := exists_large_radius_for_mass f hf (C * κ) hA₀ hAtop
  obtain ⟨Ω, ν, hcontact, hν, hgreen⟩ :=
    hcertificate f hfcomp hfsmooth hfnn κ hκ₀ hκtop R r₀ hr₀ hsupp
  exact ball_level_bound_of_obstacle_certificate_ae
    K f C κ R r₀ hκtop hr₀ hsupp hlarge hKunit hKmass Ω ν hcontact hν hgreen

/-- A normalized majorizing kernel with direct obstacle certificates bounds the optimal
weak type constant for Euclidean balls. -/
theorem ballWeakTypeConstant_le_of_direct_obstacle_certificates
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (C : ℝ≥0∞)
    (hC₀ : 0 < C) (hCtop : C ≠ (∞ : ℝ≥0∞))
    (hKunit : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1 ≤ K z)
    (hKmass : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) = C)
    (hcertificate : HasDirectObstacleCertificates K) :
    ballWeakTypeConstant n ≤ C := by
  apply CenteredMaximal.ballWeakTypeConstant_le
  apply isBallWeakTypeBound_of_smooth_nonneg hCtop
  exact isSmoothBallWeakTypeBound_of_direct_obstacle_certificates
    K C hC₀ hCtop hKunit hKmass hcertificate

end CenteredMaximal.Ball
