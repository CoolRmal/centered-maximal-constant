/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.ObstacleExistence

/-!
# Solving a strongly monotone Lipschitz equation

A penalized obstacle equation is nonlinear, but its operator is Lipschitz and strongly
monotone. A small gradient step is a contraction, so the equation has a unique solution.
-/

@[expose] public section

noncomputable section

open InnerProductSpace
open scoped RealInnerProductSpace NNReal

namespace CenteredMaximal.Ball

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- The contraction bound for one gradient step of a nonlinear, strongly monotone map. -/
theorem monotoneGradientStep_norm_le (d b : H) {L α τ : ℝ}
    (hτ : 0 < τ) (hτL : τ * L ^ 2 ≤ α) (hτα : τ * α < 1)
    (hmono : α * ‖d‖ ^ 2 ≤ ⟪b, d⟫_ℝ) (hLip : ‖b‖ ≤ L * ‖d‖) :
    ‖d - τ • b‖ ≤ (1 - τ * α / 2) * ‖d‖ := by
  have hq : 0 ≤ 1 - τ * α / 2 := by linarith
  have hbsq : ‖b‖ ^ 2 ≤ L ^ 2 * ‖d‖ ^ 2 := by
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hLip 2]
  have hstepsq : ‖d - τ • b‖ ^ 2 =
      ‖d‖ ^ 2 - 2 * τ * ⟪b, d⟫_ℝ + τ ^ 2 * ‖b‖ ^ 2 := by
    rw [norm_sub_sq_real, inner_smul_right, real_inner_comm d b, norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos hτ]
    ring
  have h₁ := mul_le_mul_of_nonneg_left hmono (by positivity : 0 ≤ 2 * τ)
  have h₂ := mul_le_mul_of_nonneg_left hbsq (sq_nonneg τ)
  have h₃ : τ ^ 2 * L ^ 2 ≤ τ * α := by
    nlinarith [mul_le_mul_of_nonneg_left hτL hτ.le]
  have h₄ := mul_le_mul_of_nonneg_right h₃ (sq_nonneg (‖d‖))
  have hbound : ‖d - τ • b‖ ^ 2 ≤ ((1 - τ * α / 2) * ‖d‖) ^ 2 := by
    rw [hstepsq]
    nlinarith [sq_nonneg (τ * α), sq_nonneg (‖d‖)]
  have htarget : 0 ≤ (1 - τ * α / 2) * ‖d‖ := mul_nonneg hq (norm_nonneg d)
  nlinarith [norm_nonneg (d - τ • b)]

/-- A globally Lipschitz strongly monotone map on a real Hilbert space is surjective.
The proof uses the fixed point of an explicit contracting gradient step. -/
theorem exists_eq_of_stronglyMonotone_lipschitz (A : H → H) (g : H)
    {L α : ℝ} (hα : 0 < α)
    (hLip : ∀ u v, ‖A u - A v‖ ≤ L * ‖u - v‖)
    (hmono : ∀ u v, α * ‖u - v‖ ^ 2 ≤ ⟪A u - A v, u - v⟫_ℝ) :
    ∃ u : H, A u = g := by
  let D : ℝ := 1 + α ^ 2 + L ^ 2
  let τ : ℝ := α / D
  let q : ℝ := 1 - τ * α / 2
  have hD : 0 < D := by dsimp [D]; positivity
  have hτ : 0 < τ := div_pos hα hD
  have hτL : τ * L ^ 2 ≤ α := by
    rw [show τ * L ^ 2 = α * L ^ 2 / D by simp [τ]; ring]
    apply (div_le_iff₀ hD).2
    dsimp [D]
    nlinarith [mul_nonneg hα.le (show 0 ≤ 1 + α ^ 2 by positivity)]
  have hτα : τ * α < 1 := by
    rw [show τ * α = α ^ 2 / D by simp [τ]; ring]
    apply (div_lt_iff₀ hD).2
    dsimp [D]
    nlinarith [sq_nonneg L]
  have hq1 : q < 1 := by
    dsimp [q]
    nlinarith [mul_pos hτ hα]
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  let qNN : ℝ≥0 := ⟨q, hq0⟩
  let T : H → H := fun u ↦ u - τ • (A u - g)
  have hT : ContractingWith qNN T := by
    refine ⟨(by exact_mod_cast hq1), LipschitzWith.of_dist_le_mul fun u v ↦ ?_⟩
    have hdiff : T u - T v = (u - v) - τ • (A u - A v) := by
      dsimp [T]
      simp only [smul_sub]
      module
    have hnorm : ‖T u - T v‖ ≤ q * ‖u - v‖ := by
      rw [hdiff]
      exact monotoneGradientStep_norm_le (u - v) (A u - A v) hτ hτL hτα
        (hmono u v) (hLip u v)
    have hqcoe : (qNN : ℝ) = q := rfl
    simpa only [dist_eq_norm, hqcoe] using hnorm
  let u : H := hT.fixedPoint T
  have hfixed : T u = u := hT.fixedPoint_isFixedPt
  have hzero : τ • (A u - g) = 0 := by
    have : u - τ • (A u - g) = u := hfixed
    exact sub_eq_self.mp this
  have hτne : τ ≠ 0 := hτ.ne'
  have hAu : A u - g = 0 := by
    exact (smul_eq_zero.mp hzero).resolve_left hτne
  exact ⟨u, sub_eq_zero.mp hAu⟩

/-- A coercive linear operator minus an antitone Lipschitz penalty is solvable. The
negative-part penalty in the obstacle construction has exactly these properties. -/
theorem exists_penalized_solution
    (A : H →L[ℝ] H) (N : H → H) (g : H) {α L ε : ℝ}
    (hα : 0 < α) (hε : 0 < ε)
    (hAmono : ∀ d : H, α * ‖d‖ ^ 2 ≤ ⟪A d, d⟫_ℝ)
    (hNanti : ∀ u v : H, ⟪N u - N v, u - v⟫_ℝ ≤ 0)
    (hNLip : ∀ u v : H, ‖N u - N v‖ ≤ L * ‖u - v‖) :
    ∃ u : H, A u - ε⁻¹ • N u = g := by
  let P : H → H := fun u ↦ A u - ε⁻¹ • N u
  have hεinv : 0 ≤ ε⁻¹ := (inv_pos.mpr hε).le
  have hLip : ∀ u v : H,
      ‖P u - P v‖ ≤ (‖A‖ + ε⁻¹ * L) * ‖u - v‖ := by
    intro u v
    have hdiff : P u - P v = A (u - v) - ε⁻¹ • (N u - N v) := by
      dsimp [P]
      rw [map_sub]
      module
    rw [hdiff]
    calc
      ‖A (u - v) - ε⁻¹ • (N u - N v)‖
          ≤ ‖A (u - v)‖ + ‖ε⁻¹ • (N u - N v)‖ := norm_sub_le _ _
      _ ≤ ‖A‖ * ‖u - v‖ + ε⁻¹ * ‖N u - N v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hεinv]
        exact add_le_add (A.le_opNorm (u - v)) le_rfl
      _ ≤ (‖A‖ + ε⁻¹ * L) * ‖u - v‖ := by
        nlinarith [mul_le_mul_of_nonneg_left (hNLip u v) hεinv]
  have hmono : ∀ u v : H,
      α * ‖u - v‖ ^ 2 ≤ ⟪P u - P v, u - v⟫_ℝ := by
    intro u v
    have hdiff : P u - P v = A (u - v) - ε⁻¹ • (N u - N v) := by
      dsimp [P]
      rw [map_sub]
      module
    rw [hdiff, inner_sub_left, real_inner_smul_left]
    have hpen := mul_nonpos_of_nonneg_of_nonpos hεinv (hNanti u v)
    linarith [hAmono (u - v)]
  exact exists_eq_of_stronglyMonotone_lipschitz P g hα hLip hmono

end CenteredMaximal.Ball
