/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.AEObstacleTransfer

/-!
# Real-valued cap interface for almost-everywhere obstacle certificates

The penalized Dirichlet equation uses a finite real cap. The maximal-function theorem uses an
extended nonnegative cap. This lemma converts the former certificate into the latter.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal ContDiff

namespace CenteredMaximal.Ball

variable {n : ℕ}

/-- Direct obstacle certificates phrased with a positive real cap. -/
def HasRealAEDirectObstacleCertificates
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) : Prop :=
  ∀ (f : EuclideanSpace ℝ (Fin n) → ℝ),
    HasCompactSupport f → ContDiff ℝ ∞ f → (∀ x, 0 ≤ f x) →
    ∀ (κ : ℝ), 0 < κ →
      ∀ (R r₀ : ℝ), 0 < r₀ → (∀ y, R ≤ ‖y‖ → f y = 0) →
        ∃ (Ω : Set (EuclideanSpace ℝ (Fin n)))
          (ν : EuclideanSpace ℝ (Fin n) → ℝ≥0∞),
          ENNReal.ofReal κ * volume Ω ≤ ∫⁻ y, ‖f y‖ₑ ∧
          (∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            ν y ≤ ENNReal.ofReal κ) ∧
          (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
            ∀ (r : ℝ), x ∉ Ω → 0 < r → r < r₀ → ‖x‖ < R + r₀ →
              (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
                ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ν y)

/-- A real-cap certificate is exactly strong enough for the extended-real maximal transfer. -/
theorem HasRealAEDirectObstacleCertificates.toENNReal
    {K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞}
    (h : HasRealAEDirectObstacleCertificates K) : HasAEDirectObstacleCertificates K := by
  intro f hfcomp hfsmooth hfnn κ hκ₀ hκtop R r₀ hr₀ hsupp
  have hκpos : 0 < κ.toReal := ENNReal.toReal_pos hκ₀.ne' hκtop
  obtain ⟨Ω, ν, hcontact, hcap, hgreen⟩ :=
    h f hfcomp hfsmooth hfnn κ.toReal hκpos R r₀ hr₀ hsupp
  have hκeq : ENNReal.ofReal κ.toReal = κ := ENNReal.ofReal_toReal hκtop
  exact ⟨Ω, ν, by simpa only [hκeq] using hcontact,
    by simpa only [hκeq] using hcap, hgreen⟩

end CenteredMaximal.Ball
