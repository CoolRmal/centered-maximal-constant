/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Statement

/-!
# Numerical enclosure of `Φ`

`1.685 < Φ < 1.686`, from rational enclosures of `√2`, `√11`, `√22`, `√(70 + 8√22)` and
`√(17 + 4√22)`. The same proof appears in `Challenge.lean`.
-/

@[expose] public section

noncomputable section

namespace CenteredMaximal

/-- Both numerical bounds on `Φ`, from rational enclosures of the five square roots. -/
theorem phi_mem_Ioo : phi ∈ Set.Ioo (1685 / 1000 : ℝ) (1686 / 1000) := by
  have s22l : (4.6904 : ℝ) < √22 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have s22u : √22 < (4.6905 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have s2l : (1.4142 : ℝ) < √2 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have s2u : √2 < (1.41422 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have s11l : (3.3166 : ℝ) < √11 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  have s11u : √11 < (3.31663 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have sAl : (10.369 : ℝ) < √(70 + 8 * √22) := (Real.lt_sqrt (by norm_num)).2 (by linarith)
  have sAu : √(70 + 8 * √22) < (10.3696 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by linarith)
  have sBl : (5.98 : ℝ) < √(17 + 4 * √22) := (Real.lt_sqrt (by norm_num)).2 (by linarith)
  have sBu : √(17 + 4 * √22) < (5.9803 : ℝ) := (Real.sqrt_lt' (by norm_num)).2 (by linarith)
  have hD : (0 : ℝ) < 26 + 4 * √22 := by positivity
  have hF₁l : (2.3208 : ℝ) < 8 + √22 - √(70 + 8 * √22) := by linarith
  have hF₁u : 8 + √22 - √(70 + 8 * √22) < (2.3215 : ℝ) := by linarith
  have hF₂l : (0.2484 : ℝ) < 11 + √22 - 2 * √2 - 2 * √11 - √(17 + 4 * √22) := by linarith
  have hF₂u : 11 + √22 - 2 * √2 - 2 * √11 - √(17 + 4 * √22) < (0.2489 : ℝ) := by linarith
  have hPl : (2.3208 * 0.2484 : ℝ) <
      (8 + √22 - √(70 + 8 * √22)) * (11 + √22 - 2 * √2 - 2 * √11 - √(17 + 4 * √22)) := by
    nlinarith [mul_pos (sub_pos.2 hF₁l) (sub_pos.2 hF₂l)]
  have hPu : (8 + √22 - √(70 + 8 * √22)) * (11 + √22 - 2 * √2 - 2 * √11 - √(17 + 4 * √22)) <
      (2.3215 * 0.2489 : ℝ) := by
    nlinarith [mul_pos (sub_pos.2 hF₁u) (sub_pos.2 hF₂u), mul_pos (sub_pos.2 hF₁u)
      (show (0 : ℝ) < 11 + √22 - 2 * √2 - 2 * √11 - √(17 + 4 * √22) by linarith)]
  constructor
  · rw [phi, lt_div_iff₀ hD]
    linarith
  · rw [phi, div_lt_iff₀ hD]
    linarith

end CenteredMaximal
