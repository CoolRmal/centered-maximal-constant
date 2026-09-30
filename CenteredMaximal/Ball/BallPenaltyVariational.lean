/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallPenaltyLimit
public import CenteredMaximal.Ball.PenaltyVariationalLimit
public import CenteredMaximal.Ball.ObstacleContact
public import Mathlib.Tactic

/-!
# Variational limit of capped penalties on a ball

The penalized Dirichlet states satisfy an obstacle variational inequality against every
nonnegative test. Weak convergence preserves that inequality, and ball coercivity gives
uniqueness of the limit obstacle state.
-/

@[expose] public section
set_option maxHeartbeats 800000
open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace ENNReal NNReal
noncomputable section
namespace CenteredMaximal.Ball.DirichletSobolev
variable {n : ℕ}

/-- A weak limit of capped ball penalties solves the nonnegative obstacle
variational inequality. -/
theorem ball_penalized_weak_limit_variational
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : L2D (ball center R)) (κ : ℝ)
    (U : ℕ → H01 (ball center R)) (Ulim : H01 (ball center R))
    (χ : ℕ → ℕ)
    (hweak : Tendsto (fun k => toWeakSpace ℝ (H01 (ball center R)) (U (χ k)))
      atTop (𝓝 (toWeakSpace ℝ (H01 (ball center R)) Ulim)))
    (heq : ∀ k, ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) (U k) V =
        l2Functional (ball center R) f V -
          κ * l2Functional (ball center R) (ballUnitL2 center R) V +
          ⟪ballPenaltyDensity center R k (U k),
            valueEmbedding (ball center R) V⟫_ℝ) :
    ∀ V : H01 (ball center R),
      0 ≤ (V : H1amb (ball center R)) 0 →
        (l2Functional (ball center R) f -
          κ • l2Functional (ball center R) (ballUnitL2 center R)) (V - Ulim) ≤
          laplaceBilin (ball center R) Ulim (V - Ulim) := by
  let D := ball center R
  let source : H01 D →L[ℝ] ℝ :=
    l2Functional D f - κ • l2Functional D (ballUnitL2 center R)
  apply variational_inequality_of_weak_penalty_limit
    (laplaceBilin D) source U Ulim χ hweak
  · intro W
    rw [laplaceBilin_self]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  · intro k V hV
    apply variational_inequality_of_penalized_equation
      (laplaceBilin D) (valueEmbedding D) source (U k)
      (ballPenaltyEpsilon k)⁻¹ (inv_nonneg.mpr (ballPenaltyEpsilon_pos k).le)
    · intro W
      have h := heq k W
      simpa only [source, sub_apply, smul_apply, smul_eq_mul,
        ballPenaltyDensity, real_inner_smul_left] using h
    · exact hV

/-- Coercivity makes the ball obstacle variational solution unique. -/
theorem ball_obstacle_variational_unique
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : L2D (ball center R)) (κ : ℝ)
    (U V : H01 (ball center R))
    (hU : 0 ≤ (U : H1amb (ball center R)) 0)
    (hV : 0 ≤ (V : H1amb (ball center R)) 0)
    (hVIU : ∀ W : H01 (ball center R),
      0 ≤ (W : H1amb (ball center R)) 0 →
        (l2Functional (ball center R) f -
          κ • l2Functional (ball center R) (ballUnitL2 center R)) (W - U) ≤
          laplaceBilin (ball center R) U (W - U))
    (hVIV : ∀ W : H01 (ball center R),
      0 ≤ (W : H1amb (ball center R)) 0 →
        (l2Functional (ball center R) f -
          κ • l2Functional (ball center R) (ballUnitL2 center R)) (W - V) ≤
          laplaceBilin (ball center R) V (W - V)) : U = V := by
  let D := ball center R
  let source : H01 D →L[ℝ] ℝ :=
    l2Functional D f - κ • l2Functional D (ballUnitL2 center R)
  have h₁ := hVIU V hV
  have h₂ := hVIV U hU
  change source (V - U) ≤ laplaceBilin D U (V - U) at h₁
  change source (U - V) ≤ laplaceBilin D V (U - V) at h₂
  have hsource : source (V - U) + source (U - V) = 0 := by
    rw [← map_add]
    have h : (V - U) + (U - V) = 0 := by abel
    rw [h, map_zero]
  have hform : laplaceBilin D U (V - U) + laplaceBilin D V (U - V) =
      -laplaceBilin D (U - V) (U - V) := by
    have h : V - U = -(U - V) := by abel
    rw [h]
    simp [map_sub]
    ring
  have henergy : laplaceBilin D (U - V) (U - V) ≤ 0 := by linarith
  obtain ⟨c, hc, hcoer⟩ := laplaceBilin_coercive_ball center R
  have hnorm : ‖U - V‖ = 0 := by
    have h := hcoer (U - V)
    by_contra hnonzero
    have hpos : 0 < ‖U - V‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hnonzero)
    have hprod : 0 < c * ‖U - V‖ * ‖U - V‖ := by positivity
    linarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)

end CenteredMaximal.Ball.DirichletSobolev
