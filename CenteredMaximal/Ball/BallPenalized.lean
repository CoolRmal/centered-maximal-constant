/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.L2Penalty

/-!
# Penalized Dirichlet obstacle equation on a ball

The abstract nonlinear Hilbert solver applies to the concrete `H¹₀` Dirichlet space on a
Euclidean ball. The resulting equation uses the `L²` negative part of the value coordinate.
-/

@[expose] public section

noncomputable section

open InnerProductSpace MeasureTheory Metric
open scoped RealInnerProductSpace NNReal ENNReal

namespace CenteredMaximal.Ball.DirichletSobolev

variable {n : ℕ}

/-- Existence of the penalized weak Dirichlet equation on a Euclidean ball. -/
theorem exists_ball_negativePart_penalized_solution
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : L2D (ball center R)) (κ ε : ℝ) (hε : 0 < ε) :
    ∃ U : H01 (ball center R), ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        l2Functional (ball center R) f V -
          κ * l2Functional (ball center R) (ballUnitL2 center R) V +
          ε⁻¹ * ⟪Lp.negPart (valueEmbedding (ball center R) U),
            valueEmbedding (ball center R) V⟫_ℝ := by
  let D := ball center R
  let source : H01 D →L[ℝ] ℝ :=
    l2Functional D f - κ • l2Functional D (ballUnitL2 center R)
  obtain ⟨U, hU⟩ := exists_l2_negativePart_penalized_solution
    (laplaceBilin D) (laplaceBilin_coercive_ball center R)
    (valueEmbedding D) source ε hε
  refine ⟨U, fun V ↦ ?_⟩
  specialize hU V
  change laplaceBilin D U V = source V +
    ε⁻¹ * ⟪Lp.negPart (valueEmbedding D U), valueEmbedding D V⟫_ℝ at hU
  simpa only [source, sub_apply, smul_apply, smul_eq_mul] using hU

end CenteredMaximal.Ball.DirichletSobolev
