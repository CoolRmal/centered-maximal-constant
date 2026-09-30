/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.DirectCertificate

/-!
# Obstacle certificates with Green comparison at almost every center

The maximal weak type estimate only concerns the measure of a superlevel set. Consequently,
Green comparison is sufficient at almost every center, as long as it holds for every radius at
each of those centers. This interface accommodates weak solutions whose Green identities are
known almost everywhere without choosing pointwise representatives.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal ContDiff

namespace CenteredMaximal.Ball

variable {n : ℕ} [Nonempty (Fin n)]

/-- The three-radius transfer needs Green comparison only at almost every center. -/
theorem ball_level_bound_of_ae_obstacle_certificate
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (C κ : ℝ≥0∞) (R r₀ : ℝ)
    (hκfin : κ ≠ (∞ : ℝ≥0∞))
    (hr₀ : 0 < r₀) (hsupp : ∀ y, R ≤ ‖y‖ → f y = 0)
    (hlarge : (∫⁻ y, ‖f y‖ₑ) ≤
      (C * κ) * volume (ball (0 : EuclideanSpace ℝ (Fin n)) r₀))
    (hKunit : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1 ≤ K z)
    (hKmass : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) = C)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (ν : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (hcontact : κ * volume Ω ≤ ∫⁻ y, ‖f y‖ₑ)
    (hν : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ν y ≤ κ)
    (hgreen : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ∀ (r : ℝ), x ∉ Ω → 0 < r → r < r₀ → ‖x‖ < R + r₀ →
        (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
          ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y) :
    (C * κ) * volume {x | C * κ < ballMaximalFunction f x} ≤
      C * ∫⁻ y, ‖f y‖ₑ := by
  have hsubset : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ {x | C * κ < ballMaximalFunction f x} → x ∈ Ω := by
    filter_upwards [hgreen] with x hxgreen
    intro hx
    by_contra hxΩ
    have hbound : ballMaximalFunction f x ≤ C * κ := by
      refine iSup₂_le fun r hr ↦ ?_
      by_cases hbig : r₀ ≤ r
      · exact ball_average_le_of_large_radius f x hr₀ hbig hlarge
      by_cases hfar : R + r₀ ≤ ‖x‖
      · rw [ball_average_eq_zero_of_far hsupp (lt_of_not_ge hbig) hfar]
        exact bot_le
      calc
        (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ
            ≤ ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ :=
              ball_average_le_kernel_integral hKunit f x hr
        _ ≤ ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y :=
          hxgreen r hxΩ hr (lt_of_not_ge hbig) (lt_of_not_ge hfar)
        _ ≤ C * κ :=
          kernel_integral_le_of_density_le_ae K ν x r κ C hκfin hν (hKmass x r hr)
    exact (not_lt_of_ge hbound) hx
  have hmeasure : volume {x | C * κ < ballMaximalFunction f x} ≤ volume Ω := by
    exact measure_mono_ae hsubset
  calc
    (C * κ) * volume {x | C * κ < ballMaximalFunction f x}
        ≤ (C * κ) * volume Ω := by
          simpa only [mul_comm] using
            (mul_le_mul_left hmeasure (C * κ))
    _ = C * (κ * volume Ω) := by ac_rfl
    _ ≤ C * ∫⁻ y, ‖f y‖ₑ := by
      simpa only [mul_comm] using (mul_le_mul_left hcontact C)

/-- A direct obstacle certificate with Green comparison at almost every center. -/
def HasAEDirectObstacleCertificates (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) : Prop :=
  ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
    HasCompactSupport f → ContDiff ℝ ∞ f → (∀ x, 0 ≤ f x) →
    ∀ (κ : ℝ≥0∞), 0 < κ → κ ≠ (∞ : ℝ≥0∞) →
      ∀ (R r₀ : ℝ), 0 < r₀ → (∀ y, R ≤ ‖y‖ → f y = 0) →
        ∃ (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (ν : EuclideanSpace ℝ (Fin n) → ℝ≥0∞),
          κ * volume Ω ≤ ∫⁻ y, ‖f y‖ₑ ∧
          (∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ν y ≤ κ) ∧
          (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            ∀ (r : ℝ), x ∉ Ω → 0 < r → r < r₀ → ‖x‖ < R + r₀ →
              (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
                ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y)

omit [Nonempty (Fin n)] in
/-- A pointwise direct certificate supplies an almost-everywhere one. -/
theorem HasDirectObstacleCertificates.toAE
    {K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (h : HasDirectObstacleCertificates K) : HasAEDirectObstacleCertificates K := by
  intro f hfcomp hfsmooth hfnn κ hκ₀ hκtop R r₀ hr₀ hsupp
  obtain ⟨Ω, ν, hcontact, hν, hgreen⟩ :=
    h f hfcomp hfsmooth hfnn κ hκ₀ hκtop R r₀ hr₀ hsupp
  exact ⟨Ω, ν, hcontact, hν, ae_of_all _ (fun x r ↦ hgreen x r)⟩

/-- Almost-everywhere direct obstacle certificates give the smooth weak type estimate. -/
theorem isSmoothBallWeakTypeBound_of_ae_direct_obstacle_certificates
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (C : ℝ≥0∞)
    (hC₀ : 0 < C) (hCtop : C ≠ (∞ : ℝ≥0∞))
    (hKunit : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1 ≤ K z)
    (hKmass : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) = C)
    (hcertificate : HasAEDirectObstacleCertificates K) :
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
  exact ball_level_bound_of_ae_obstacle_certificate
    K f C κ R r₀ hκtop hr₀ hsupp hlarge hKunit hKmass Ω ν hcontact hν hgreen

/-- Almost-everywhere direct obstacle certificates bound the optimal ball constant. -/
theorem ballWeakTypeConstant_le_of_ae_direct_obstacle_certificates
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (C : ℝ≥0∞)
    (hC₀ : 0 < C) (hCtop : C ≠ (∞ : ℝ≥0∞))
    (hKunit : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1 ≤ K z)
    (hKmass : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) = C)
    (hcertificate : HasAEDirectObstacleCertificates K) :
    ballWeakTypeConstant n ≤ C := by
  apply CenteredMaximal.ballWeakTypeConstant_le
  apply isBallWeakTypeBound_of_smooth_nonneg hCtop
  exact isSmoothBallWeakTypeBound_of_ae_direct_obstacle_certificates
    K C hC₀ hCtop hKunit hKmass hcertificate

end CenteredMaximal.Ball
