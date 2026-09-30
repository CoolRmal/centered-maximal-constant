/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.PenaltyCapSource

/-!
# The penalized source tested against the shifted negative part

This is the `L²` form of the pointwise sign estimate for the penalty. It is used with
`p=(−u−εκ)⁺` to bound the negative part of a penalized Dirichlet solution.
-/

@[expose] public section

noncomputable section

open InnerProductSpace MeasureTheory
open scoped RealInnerProductSpace NNReal ENNReal

namespace CenteredMaximal.Ball

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The penalized source has nonnegative `L²` pairing with the shifted negative-part test. -/
theorem l2_penalized_source_shifted_negPart_nonneg
    (u f p one : Lp ℝ 2 μ) (κ ε : ℝ) (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hf : ∀ᵐ x ∂μ, 0 ≤ f x)
    (hone : ∀ᵐ x ∂μ, one x = 1)
    (hp : ∀ᵐ x ∂μ, p x = max (-u x - ε * κ) 0) :
    0 ≤ ⟪f, p⟫_ℝ - κ * ⟪one, p⟫_ℝ +
      ε⁻¹ * ⟪Lp.negPart u, p⟫_ℝ := by
  have hlin : ⟪f, p⟫_ℝ - κ * ⟪one, p⟫_ℝ +
      ε⁻¹ * ⟪Lp.negPart u, p⟫_ℝ =
      ⟪f - κ • one + ε⁻¹ • Lp.negPart u, p⟫_ℝ := by
    rw [inner_add_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
  rw [hlin, L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hf, hone, hp, Lp.coeFn_negPart_eq_max u,
    Lp.coeFn_add (f - κ • one) (ε⁻¹ • Lp.negPart u),
    Lp.coeFn_sub f (κ • one), Lp.coeFn_smul κ one,
    Lp.coeFn_smul ε⁻¹ (Lp.negPart u)] with x hfx honex hpx hneg hadd hsub hsmul hpsmul
  rw [hadd, Pi.add_apply, hsub, Pi.sub_apply, hsmul, hpsmul,
    Pi.smul_apply, Pi.smul_apply, honex, hneg, hpx]
  have hpoint := penalized_scalar_source_mul_shifted_negPart_nonneg
    (u x) (f x) κ ε hκ hε hfx
  simpa [mul_comm, mul_left_comm, mul_assoc] using hpoint

end CenteredMaximal.Ball
