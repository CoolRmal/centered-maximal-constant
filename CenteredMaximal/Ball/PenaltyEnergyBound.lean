/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallPenaltyCap

/-!
# Uniform energy bound for penalized obstacles

The negative-part penalty dissipates energy. Coercivity therefore bounds each penalized
solution independently of the penalty parameter.
-/

@[expose] public section

noncomputable section

open InnerProductSpace MeasureTheory
open scoped RealInnerProductSpace NNReal ENNReal

namespace CenteredMaximal.Ball

variable {X H : Type*} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The negative part of an `L²` function has nonpositive pairing with that function. -/
theorem l2_negPart_inner_self_nonpos (u : Lp ℝ 2 μ) :
    ⟪Lp.negPart u, u⟫_ℝ ≤ 0 := by
  have h := l2_negPart_antitone_inner u 0
  simpa [Lp.negPart, Lp.posPart] using h

omit [CompleteSpace H] in
/-- A penalized solution of a coercive weak equation satisfies a uniform energy bound.
The bound is independent of `ε`. -/
theorem penalized_solution_norm_le
    (B : H →L[ℝ] H →L[ℝ] ℝ) (J : H →L[ℝ] Lp ℝ 2 μ)
    (source : H →L[ℝ] ℝ) (U : H) (ε : ℝ) (hε : 0 < ε)
    {α : ℝ} (hα : 0 < α)
    (hcoerc : ∀ V : H, α * ‖V‖ * ‖V‖ ≤ B V V)
    (hweak : ∀ V : H, B U V = source V + ε⁻¹ * ⟪Lp.negPart (J U), J V⟫_ℝ) :
    ‖U‖ ≤ ‖source‖ / α := by
  have hpen : ε⁻¹ * ⟪Lp.negPart (J U), J U⟫_ℝ ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (inv_pos.mpr hε).le
      (l2_negPart_inner_self_nonpos (J U))
  have hsource : source U ≤ ‖source‖ * ‖U‖ := by
    exact (le_trans (le_abs_self _) (source.le_opNorm U))
  have henergy := hcoerc U
  rw [hweak U] at henergy
  have hbasic : α * ‖U‖ * ‖U‖ ≤ ‖source‖ * ‖U‖ := by linarith
  by_cases hzero : ‖U‖ = 0
  · simpa only [hzero] using div_nonneg (norm_nonneg source) hα.le
  · have hpos : 0 < ‖U‖ := lt_of_le_of_ne (norm_nonneg U) (Ne.symm hzero)
    apply (le_div_iff₀ hα).2
    nlinarith

namespace DirichletSobolev

variable {n : ℕ}

/-- A common norm bound works for every penalty parameter and every penalized solution
of the fixed ball problem. -/
theorem exists_uniform_ball_penalized_norm_bound
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : L2D (Metric.ball center R)) (κ : ℝ) :
    ∃ C : ℝ, ∀ (ε : ℝ), 0 < ε → ∀ (U : H01 (Metric.ball center R)),
      (∀ V : H01 (Metric.ball center R),
        laplaceBilin (Metric.ball center R) U V =
          l2Functional (Metric.ball center R) f V -
            κ * l2Functional (Metric.ball center R) (ballUnitL2 center R) V +
            ε⁻¹ * ⟪Lp.negPart (valueEmbedding (Metric.ball center R) U),
              valueEmbedding (Metric.ball center R) V⟫_ℝ) →
        ‖U‖ ≤ C := by
  let D := Metric.ball center R
  let source : H01 D →L[ℝ] ℝ :=
    l2Functional D f - κ • l2Functional D (ballUnitL2 center R)
  obtain ⟨α, hα, hcoerc⟩ := laplaceBilin_coercive_ball center R
  refine ⟨‖source‖ / α, fun ε hε U hU ↦ ?_⟩
  have hweak : ∀ V : H01 D, laplaceBilin D U V = source V +
      ε⁻¹ * ⟪Lp.negPart (valueEmbedding D U), valueEmbedding D V⟫_ℝ := by
    intro V
    simpa only [source, sub_apply, smul_apply, smul_eq_mul] using hU V
  exact penalized_solution_norm_le (laplaceBilin D) (valueEmbedding D)
    source U ε hε hα hcoerc hweak

end DirichletSobolev

end CenteredMaximal.Ball
