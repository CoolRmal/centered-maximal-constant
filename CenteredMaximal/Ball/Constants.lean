/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.Basic

/-!
# Radius and value of the Newtonian comparison kernel

For `n ≥ 3`, the radius `Rₙ` satisfies `Rₙ ^ (n - 2) = n / 2`. Its `n`th power is the
dimension-dependent constant in the ball maximal inequality.
-/

@[expose] public section

noncomputable section

namespace CenteredMaximal.Ball

/-- The support radius of the optimal truncated Newtonian comparison kernel. -/
def greenRadius (n : ℕ) : ℝ := ((n : ℝ) / 2) ^ (1 / ((n : ℝ) - 2))

/-- The constant supplied by the truncated Newtonian comparison kernel. -/
def greenBound (n : ℕ) : ℝ := ((n : ℝ) / 2) ^ ((n : ℝ) / ((n : ℝ) - 2))

/-- The support radius of the optimal truncated logarithmic kernel in the plane. -/
def planarGreenRadius : ℝ := Real.sqrt (Real.exp 1)

theorem volume_ball_planarGreenRadius_mul (x : EuclideanSpace ℝ (Fin 2)) (r : ℝ) :
    MeasureTheory.volume (Metric.ball x (planarGreenRadius * r)) =
      ENNReal.ofReal (Real.exp 1) * MeasureTheory.volume (Metric.ball x r) := by
  simp only [EuclideanSpace.volume_ball_fin_two]
  unfold planarGreenRadius
  rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), mul_pow]
  have hpow : (ENNReal.ofReal (Real.sqrt (Real.exp 1))) ^ 2 =
      ENNReal.ofReal (Real.exp 1) := by
    calc
      _ = ENNReal.ofReal ((Real.sqrt (Real.exp 1)) ^ 2) :=
        (ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2).symm
      _ = _ := by rw [Real.sq_sqrt (Real.exp_pos 1).le]
  rw [hpow]
  ac_rfl

theorem greenRadius_pos (n : ℕ) (hn : 3 ≤ n) : 0 < greenRadius n := by
  unfold greenRadius
  apply Real.rpow_pos_of_pos
  have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  positivity

theorem greenRadius_rpow_sub_two (n : ℕ) (hn : 3 ≤ n) :
    greenRadius n ^ ((n : ℝ) - 2) = (n : ℝ) / 2 := by
  have hne : (n : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  unfold greenRadius
  rw [← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ) / 2)]
  rw [one_div, inv_mul_cancel₀ hne, Real.rpow_one]

theorem greenRadius_rpow_dim (n : ℕ) (hn : 3 ≤ n) :
    greenRadius n ^ (n : ℝ) = greenBound n := by
  unfold greenRadius greenBound
  rw [← Real.rpow_mul (by positivity : 0 ≤ (n : ℝ) / 2)]
  congr 1
  ring

/-- Dilating a Euclidean ball by the Green radius multiplies its volume by the proposed
weak type bound. -/
theorem volume_ball_greenRadius_mul (n : ℕ) (hn : 3 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    MeasureTheory.volume (Metric.ball x (greenRadius n * r)) =
      ENNReal.ofReal (greenBound n) * MeasureTheory.volume (Metric.ball x r) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  simp only [EuclideanSpace.volume_ball, Fintype.card_fin]
  rw [ENNReal.ofReal_mul (greenRadius_pos n hn).le, mul_pow]
  have hpow : (ENNReal.ofReal (greenRadius n)) ^ n = ENNReal.ofReal (greenBound n) := by
    rw [← ENNReal.ofReal_pow (greenRadius_pos n hn).le]
    congr 1
    rw [← Real.rpow_natCast, greenRadius_rpow_dim n hn]
  rw [hpow]
  ac_rfl

theorem greenBound_three : greenBound 3 = 27 / 8 := by
  norm_num [greenBound, Real.rpow_natCast]

theorem greenBound_four : greenBound 4 = 4 := by
  norm_num [greenBound, Real.rpow_natCast]

end CenteredMaximal.Ball
