/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallWeakDistribution

/-!
# A positive whole-space representative of a ball obstacle

The `H₀¹` obstacle is an `L²` class on a ball. Taking its positive part inside the ball and zero
outside supplies a pointwise nonnegative, integrable, compactly supported representative. It
agrees with the Sobolev value almost everywhere and vanishes at every point outside the
contact set, which is convenient for mollification and Green comparison.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter
open scoped RealInnerProductSpace ENNReal

namespace CenteredMaximal.Ball.DirichletSobolev

variable {n : ℕ}

/-- Zero extension of the positive part of the value component of an `H₀¹` state. -/
def ballPositiveRepresentative
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (U : H01 (ball center R)) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
  (ball center R).indicator
    (fun x => max ((U : H1amb (ball center R)) 0 x : ℝ) 0)

theorem ballPositiveRepresentative_nonneg
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (U : H01 (ball center R)) (x : EuclideanSpace ℝ (Fin (n + 1))) :
    0 ≤ ballPositiveRepresentative center R U x := by
  by_cases hx : x ∈ ball center R
  · simp only [ballPositiveRepresentative, Set.indicator_of_mem hx]
    exact le_max_right _ _
  · simp [ballPositiveRepresentative, Set.indicator_of_notMem hx]

/-- The representative is pointwise zero outside the obstacle contact set. -/
theorem ballPositiveRepresentative_eq_zero_of_not_contact
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (U : H01 (ball center R)) (x : EuclideanSpace ℝ (Fin (n + 1)))
    (hx : x ∉ {y | y ∈ ball center R ∧
      0 < ((U : H1amb (ball center R)) 0 y : ℝ)}) :
    ballPositiveRepresentative center R U x = 0 := by
  by_cases hball : x ∈ ball center R
  · have hle : ((U : H1amb (ball center R)) 0 x : ℝ) ≤ 0 :=
      le_of_not_gt (fun hpos => hx ⟨hball, hpos⟩)
    simp [ballPositiveRepresentative, hball, max_eq_right hle]
  · simp [ballPositiveRepresentative, hball]

/-- The representative equals the value component on the ball almost everywhere when the
obstacle is nonnegative as an `L²` class. -/
theorem ballPositiveRepresentative_ae_eq_value
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (U : H01 (ball center R))
    (hU : 0 ≤ (U : H1amb (ball center R)) 0) :
    ballPositiveRepresentative center R U =ᵐ[volume.restrict (ball center R)]
      fun x => ((U : H1amb (ball center R)) 0 x : ℝ) := by
  filter_upwards [(Lp.coeFn_nonneg ((U : H1amb (ball center R)) 0)).2 hU,
    ae_restrict_mem (μ := volume) measurableSet_ball] with x hx hball
  simp only [Pi.zero_apply] at hx
  simp [ballPositiveRepresentative, hball, max_eq_left hx]

/-- A ball representative has compact support, independently of the Sobolev state. -/
theorem ballPositiveRepresentative_hasCompactSupport
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (U : H01 (ball center R)) :
    HasCompactSupport (ballPositiveRepresentative center R U) := by
  have hsupport : Function.support (ballPositiveRepresentative center R U) ⊆
      ball center R := by
    intro x hx
    by_contra hnot
    exact hx (by simp [ballPositiveRepresentative, Set.indicator_of_notMem hnot])
  exact (Metric.isBounded_ball.isCompact_closure).of_isClosed_subset
    isClosed_closure (closure_mono hsupport)

/-- The representative is integrable because the ball has finite measure and the
underlying value component lies in `L²` there. -/
theorem ballPositiveRepresentative_integrable
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (U : H01 (ball center R))
    (hU : 0 ≤ (U : H1amb (ball center R)) 0) :
    Integrable (ballPositiveRepresentative center R U) := by
  letI : IsFiniteMeasure (volume.restrict (ball center R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hvalue : Integrable
      (fun x => ((U : H1amb (ball center R)) 0 x : ℝ))
      (volume.restrict (ball center R)) :=
    (Lp.memLp ((U : H1amb (ball center R)) 0)).integrable (by norm_num)
  have hlocal : Integrable
      (fun x => max ((U : H1amb (ball center R)) 0 x : ℝ) 0)
      (volume.restrict (ball center R)) := by
    apply hvalue.congr
    filter_upwards [(Lp.coeFn_nonneg ((U : H1amb (ball center R)) 0)).2 hU]
      with x hx
    exact (max_eq_left hx).symm
  exact MeasureTheory.IntegrableOn.integrable_indicator hlocal measurableSet_ball

end CenteredMaximal.Ball.DirichletSobolev
