/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.ObstacleTransfer

/-!
# The analytic certificate needed for the ball maximal bound

This module packages the obstacle argument at the point where the PDE construction and the
local Green identity enter. The certificate hypothesis is deliberately explicit: it gives a
measurable contact set, a capped density, a total-mass bound, and local Green comparison.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal ContDiff

namespace CenteredMaximal.Ball

/-- The desired weak type estimate restricted to nonnegative smooth compactly supported
functions. The approximation argument later extends this to all integrable functions. -/
def IsSmoothBallWeakTypeBound (n : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
    HasCompactSupport f → ContDiff ℝ ∞ f → (∀ x, 0 ≤ f x) →
      ∀ α : ℝ≥0∞,
        α * volume {x | α < ballMaximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ

variable {n : ℕ} [Nonempty (Fin n)]

omit [Nonempty (Fin n)] in
/-- Every compactly supported function vanishes outside some ball centred at the origin. -/
theorem exists_support_radius
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : HasCompactSupport f) :
    ∃ R : ℝ, ∀ y, R ≤ ‖y‖ → f y = 0 := by
  obtain ⟨R, hR⟩ := (isBounded_iff_subset_ball
    (0 : EuclideanSpace ℝ (Fin n))).mp hf.isBounded
  refine ⟨R, fun y hy ↦ ?_⟩
  by_contra hfy
  have hys : y ∈ tsupport f := subset_tsupport f (by simpa [Function.mem_support] using hfy)
  have hball := hR hys
  rw [mem_ball_zero_iff] at hball
  exact (not_lt_of_ge hy) hball

/-- A Green kernel with exact normalized mass and an obstacle certificate for every smooth
nonnegative input yields the weak type estimate for such inputs. This theorem isolates the
remaining PDE and local Green-comparison obligations in `hcertificate`. -/
theorem isSmoothBallWeakTypeBound_of_obstacle_certificates
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (C : ℝ≥0∞)
    (hC₀ : 0 < C) (hCtop : C ≠ (∞ : ℝ≥0∞))
    (hKunit : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1 ≤ K z)
    (hKmass : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) = C)
    (hcertificate :
      ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
        HasCompactSupport f → ContDiff ℝ ∞ f → (∀ x, 0 ≤ f x) →
        ∀ (κ : ℝ≥0∞), 0 < κ → κ ≠ (∞ : ℝ≥0∞) →
          ∀ (R r₀ : ℝ), 0 < r₀ → (∀ y, R ≤ ‖y‖ → f y = 0) →
            ∃ (Ω : Set (EuclideanSpace ℝ (Fin n)))
              (ν : EuclideanSpace ℝ (Fin n) → ℝ≥0∞),
              MeasurableSet Ω ∧
              (∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
                y ∈ Ω → ν y = κ) ∧
              (∫⁻ y, ν y) ≤ ∫⁻ y, ‖f y‖ₑ ∧
              (∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ν y ≤ κ) ∧
              (∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ),
                x ∉ Ω → 0 < r → r < r₀ → ‖x‖ < R + r₀ →
                  (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
                    ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y)) :
    IsSmoothBallWeakTypeBound n C := by
  intro f hfcomp hfsmooth hfnn α
  have hf : Integrable f := hfsmooth.continuous.integrable_of_hasCompactSupport hfcomp
  obtain ⟨R, hsupp⟩ := exists_support_radius hfcomp
  refine ball_level_bound_of_scaled_levels C hC₀ hCtop f ?_ α
  intro κ hκ₀ hκtop
  have hA₀ : 0 < C * κ := ENNReal.mul_pos hC₀.ne' hκ₀.ne'
  have hAtop : C * κ ≠ (∞ : ℝ≥0∞) := ENNReal.mul_ne_top hCtop hκtop
  obtain ⟨r₀, hr₀, hlarge⟩ := exists_large_radius_for_mass f hf (C * κ) hA₀ hAtop
  obtain ⟨Ω, ν, hΩ, hνcontact, hmass, hν, hgreen⟩ :=
    hcertificate f hfcomp hfsmooth hfnn κ hκ₀ hκtop R r₀ hr₀ hsupp
  have hcontact : κ * volume Ω ≤ ∫⁻ y, ‖f y‖ₑ :=
    (contact_measure_le_density_mass Ω hΩ ν κ hνcontact).trans hmass
  exact ball_level_bound_of_obstacle_certificate_ae
    K f C κ R r₀ hκtop hr₀ hsupp hlarge hKunit hKmass Ω ν hcontact hν hgreen

end CenteredMaximal.Ball
