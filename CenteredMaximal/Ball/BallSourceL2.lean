/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallPenalized

/-!
# Smooth source data for the penalized ball equation

A continuous compactly supported real function defines an `L²` source on every ball.
This connects the smooth maximal-function input to the weak Dirichlet equation.
-/

@[expose] public section

noncomputable section

open InnerProductSpace MeasureTheory Metric
open scoped RealInnerProductSpace NNReal ENNReal

namespace CenteredMaximal.Ball.DirichletSobolev

variable {n : ℕ}

/-- A continuous compactly supported function as an `L²` source on a ball. -/
def ballSourceL2 (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f) :
    L2D (ball center R) :=
  ((hfcont.memLp_of_hasCompactSupport hfcomp).restrict (ball center R)).toLp f

/-- The `L²` source agrees almost everywhere with the original function. -/
theorem ballSourceL2_coeFn (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f) :
    ⇑(ballSourceL2 center R f hfcont hfcomp)
      =ᵐ[volume.restrict (ball center R)] f := by
  exact MemLp.coeFn_toLp _

/-- The penalized equation with an ordinary continuous compactly supported density. -/
theorem exists_ball_negativePart_penalized_solution_smoothSource
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f)
    (κ ε : ℝ) (hε : 0 < ε) :
    ∃ U : H01 (ball center R), ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        ((∫ x in ball center R,
          f x * ((V : H1amb (ball center R)) 0 x : ℝ)) -
          κ * (∫ x in ball center R, ((V : H1amb (ball center R)) 0 x : ℝ))) +
          ε⁻¹ * ⟪Lp.negPart (valueEmbedding (ball center R) U),
            valueEmbedding (ball center R) V⟫_ℝ := by
  obtain ⟨U, hU⟩ := exists_ball_negativePart_penalized_solution center R
    (ballSourceL2 center R f hfcont hfcomp) κ ε hε
  refine ⟨U, fun V ↦ ?_⟩
  specialize hU V
  rw [l2Functional_eq_integral, ballMassFunctional_apply] at hU
  have hpair :
      (∫ x in ball center R,
        (ballSourceL2 center R f hfcont hfcomp x : ℝ) *
          ((V : H1amb (ball center R)) 0 x : ℝ)) =
      ∫ x in ball center R,
        f x * ((V : H1amb (ball center R)) 0 x : ℝ) := by
    apply integral_congr_ae
    filter_upwards [ballSourceL2_coeFn center R f hfcont hfcomp] with x hx
    rw [hx]
  rw [hpair] at hU
  exact hU

end CenteredMaximal.Ball.DirichletSobolev
