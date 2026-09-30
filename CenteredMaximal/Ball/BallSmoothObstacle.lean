/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallPenaltyObstacle
public import CenteredMaximal.Ball.BallSourceL2

/-!
# Capped ball obstacle for a smooth whole-space source

The local `L²` source constructed from a continuous compactly supported function agrees with
the original source almost everywhere on the ball. The penalized obstacle therefore gives
whole-space contact and density bounds directly in terms of that function.
-/

@[expose] public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Filter Topology
open scoped RealInnerProductSpace NNReal ENNReal

namespace CenteredMaximal.Ball.DirichletSobolev

variable {n : ℕ}

/-- A nonnegative smooth source gives an obstacle with a capped whole-space density and
contact mass bounded by the original whole-space source mass. -/
theorem exists_ball_smooth_obstacle_with_density
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f)
    (hf0 : ∀ x, 0 ≤ f x) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ U : H01 (ball center R), ∃ νlocal : L2D (ball center R),
      ∃ Ω : Set (EuclideanSpace ℝ (Fin (n + 1))),
      ∃ ν : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞,
        Ω = {x | x ∈ ball center R ∧
          0 < ((U : H1amb (ball center R)) 0 x : ℝ)} ∧
        ν = extendRestrictedDensity (ball center R) νlocal ∧
        ENNReal.ofReal κ * volume Ω ≤ ∫⁻ x, ‖f x‖ₑ ∧
        (∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
          ν x ≤ ENNReal.ofReal κ) ∧
        0 ≤ valueEmbedding (ball center R) U ∧
        (∀ V : H01 (ball center R),
          laplaceBilin (ball center R) U V =
            l2Functional (ball center R)
              (ballSourceL2 center R f hfcont hfcomp) V -
              κ * l2Functional (ball center R) (ballUnitL2 center R) V +
              ⟪νlocal, valueEmbedding (ball center R) V⟫_ℝ) := by
  let F := ballSourceL2 center R f hfcont hfcomp
  have hF0 : 0 ≤ F := by
    rw [← Lp.coeFn_nonneg]
    filter_upwards [ballSourceL2_coeFn center R f hfcont hfcomp] with x hx
    rw [hx]
    exact hf0 x
  exact exists_ball_penalty_wholeSpace_density_of_ae_eq
    center R f F (ballSourceL2_coeFn center R f hfcont hfcomp) κ hκ hF0

end CenteredMaximal.Ball.DirichletSobolev
