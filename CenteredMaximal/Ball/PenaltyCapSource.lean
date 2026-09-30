/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallSourceL2

/-!
# Sign of the penalized source at a shifted negative-part test

The test `max(-u-εκ,0)` is supported where the negative-part penalty exceeds the cap.
On that set, `f-κ+ε⁻¹u⁻` is nonnegative whenever `f` is nonnegative.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace CenteredMaximal.Ball

variable {X : Type*}

/-- The scalar sign calculation behind the penalized obstacle cap. -/
theorem penalized_scalar_source_mul_shifted_negPart_nonneg
    (u f κ ε : ℝ) (hκ : 0 ≤ κ) (hε : 0 < ε) (hf : 0 ≤ f) :
    0 ≤ (f - κ + ε⁻¹ * max (-u) 0) * max (-u - ε * κ) 0 := by
  by_cases hx : -u - ε * κ ≤ 0
  · rw [max_eq_right hx]
    simp
  · have hshift : 0 < -u - ε * κ := lt_of_not_ge hx
    have hu : 0 ≤ -u := by nlinarith [mul_nonneg hε.le hκ]
    rw [max_eq_left hu, max_eq_left hshift.le]
    have hεinv : 0 ≤ ε⁻¹ := (inv_pos.mpr hε).le
    have hprod : 0 ≤ ε⁻¹ * (-u - ε * κ) := mul_nonneg hεinv hshift.le
    have hrewrite : ε⁻¹ * (-u - ε * κ) = ε⁻¹ * (-u) - κ := by
      field_simp
    rw [hrewrite] at hprod
    exact mul_nonneg (by linarith) hshift.le

/-- Pointwise sign of the source in the penalized obstacle equation after testing
against the shifted negative part. -/
theorem penalized_source_mul_shifted_negPart_nonneg
    (u f : X → ℝ) (κ ε : ℝ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hf : ∀ x, 0 ≤ f x) (x : X) :
    0 ≤ (f x - κ + ε⁻¹ * max (-u x) 0) * max (-u x - ε * κ) 0 :=
  penalized_scalar_source_mul_shifted_negPart_nonneg (u x) (f x) κ ε hκ hε (hf x)

variable [MeasurableSpace X] (μ : Measure X)

/-- Integrated sign of the penalized source; no separate integrability assumption is
needed for this nonnegativity statement. -/
theorem integral_penalized_source_mul_shifted_negPart_nonneg
    (u f : X → ℝ) (κ ε : ℝ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ∫ x, (f x - κ + ε⁻¹ * max (-u x) 0) * max (-u x - ε * κ) 0 ∂μ := by
  apply integral_nonneg
  intro x
  exact penalized_source_mul_shifted_negPart_nonneg u f κ ε hκ hε hf x

end CenteredMaximal.Ball
