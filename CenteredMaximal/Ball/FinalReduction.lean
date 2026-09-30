/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.SmoothReduction

/-!
# From obstacle certificates to the optimal ball weak type constant

The analytic input is a kernel with exact normalized mass and an obstacle certificate at
every finite positive level. The certificate produces a weak type estimate for smooth
nonnegative functions; smooth reduction then gives the same estimate for all integrable
functions and hence bounds the optimal constant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal ContDiff

namespace CenteredMaximal.Ball

variable {n : ℕ} [Nonempty (Fin n)]

/-- The obstacle certificate required for a kernel at every smooth nonnegative input and
every finite positive level. The contact set is measurable, the density equals the level on
that set, is capped by the level, has controlled total mass, and satisfies the local Green
comparison. -/
def HasObstacleCertificates (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) : Prop :=
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
                ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y)

/-- A normalized majorizing kernel and its obstacle certificates bound the optimal weak
type constant for Euclidean balls. -/
theorem ballWeakTypeConstant_le_of_obstacle_certificates
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (C : ℝ≥0∞)
    (hC₀ : 0 < C) (hCtop : C ≠ (∞ : ℝ≥0∞))
    (hKunit : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, 1 ≤ K z)
    (hKmass : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), 0 < r →
      (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) = C)
    (hcertificate : HasObstacleCertificates K) :
    ballWeakTypeConstant n ≤ C := by
  apply CenteredMaximal.ballWeakTypeConstant_le
  apply isBallWeakTypeBound_of_smooth_nonneg hCtop
  exact isSmoothBallWeakTypeBound_of_obstacle_certificates
    K C hC₀ hCtop hKunit hKmass hcertificate

end CenteredMaximal.Ball
