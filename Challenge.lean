/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Challenge: the weak type constant of the centred maximal operator over cubes

For `f : ℝᵈ → ℝ` the centred Hardy–Littlewood maximal function over axis-parallel cubes is
`M f (x) = sup_{r > 0} |Q(x, r)|⁻¹ ∫_{Q(x, r)} |f|`, where `Q(x, r) = ∏ᵢ [xᵢ - r, xᵢ + r]` is the
closed cube of side `2r` centred at `x`. Its weak type `(1, 1)` constant `c_d` is the least `C` with
`α · |{M f > α}| ≤ C ‖f‖₁` for all integrable `f` and all levels `α`.

This file states:

* `weakTypeConstant_le_two_pow`: `c_d ≤ 2 ^ d` in every dimension (the Vitali covering argument
  with centred cubes);
* `ofReal_phi_le_weakTypeConstant_two`: `Φ ≤ c₂`, where `Φ = 1.68550999…` is the explicit
  algebraic number `phi`; the previously published lower bound is `c₂ ≥ 1.62119…` (Aldaz, 2000);
* `weakTypeConstant_two_gt`: consequently `c₂ > 1.685`;
* `lt_phi` and `phi_lt`: `1.685 < Φ < 1.686`. These two are proved in this file, so that a reader
  can check the size of `Φ` without reading the solution.

The type `Fin d → ℝ` carries the sup norm in Mathlib, so `Metric.closedBall x r` is exactly the cube
`Q(x, r)`, and `volume` is Lebesgue measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace CenteredMaximal

/-- The centred Hardy–Littlewood maximal function of `f : ℝᵈ → ℝ` over axis-parallel cubes:
`M f (x) = sup_{r > 0} |Q(x, r)|⁻¹ ∫_{Q(x, r)} |f|`, with values in `[0, ∞]`.

Since `Fin d → ℝ` carries the sup norm, `closedBall x r` is the closed cube `∏ᵢ [xᵢ - r, xᵢ + r]`
of side length `2r` centred at `x`; `volume` is Lebesgue measure. -/
def maximalFunction {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ≥0∞ :=
  ⨆ (r : ℝ) (_ : 0 < r), (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ

/-- `C` is a weak type `(1, 1)` bound for the centred maximal operator in dimension `d`: for every
integrable `f : ℝᵈ → ℝ` and every level `α ∈ [0, ∞]`, `α · |{x : M f (x) > α}| ≤ C · ‖f‖₁`. -/
def IsWeakTypeBound (d : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : (Fin d → ℝ) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < maximalFunction f x} ≤ C * ∫⁻ x, ‖f x‖ₑ

/-- The weak type `(1, 1)` constant `c_d` of the centred Hardy–Littlewood maximal operator over
axis-parallel cubes in `ℝᵈ`: the least weak type bound. -/
def weakTypeConstant (d : ℕ) : ℝ≥0∞ :=
  sInf {C | IsWeakTypeBound d C}

/-- The constant `Φ = 1.68550999335552518…`, an algebraic number of degree 16:
`Φ = ((77 + 16√22)/2 - (8 + √22 - √(70 + 8√22)) (11 + √22 - 2√2 - 2√11 - √(17 + 4√22)))
/ (26 + 4√22)`.

It is the covered area per unit mass of a periodic measure: unit masses and masses
`w = (17 + 4√22)/9` alternate along the columns `x = i h`, `h = (5 + √22)/6`, and the rows are
`y = j V`, `V = (11 + √22)/6`. -/
def phi : ℝ :=
  ((77 + 16 * √22) / 2 -
      (8 + √22 - √(70 + 8 * √22)) * (11 + √22 - 2 * √2 - 2 * √11 - √(17 + 4 * √22))) /
    (26 + 4 * √22)

/-- Both numerical bounds on `Φ`, from rational enclosures of the five square roots. -/
private theorem phi_mem_Ioo : phi ∈ Set.Ioo (1685 / 1000 : ℝ) (1686 / 1000) := by
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

/-- `1.685 < Φ`. -/
theorem lt_phi : (1685 / 1000 : ℝ) < phi :=
  phi_mem_Ioo.1

/-- `Φ < 1.686`. -/
theorem phi_lt : phi < 1686 / 1000 :=
  phi_mem_Ioo.2

/-- **Upper bound.** In every dimension `d`, `c_d ≤ 2ᵈ`: the Vitali covering argument, which for
centred cubes only needs to cover the centres, gives the factor `2ᵈ` instead of `3ᵈ`. -/
theorem weakTypeConstant_le_two_pow (d : ℕ) : weakTypeConstant d ≤ 2 ^ d := by
  sorry

/-- **Lower bound.** `Φ ≤ c₂`. The previously published lower bound was
`c₂ ≥ 3/4 - √2/4 + √6/2 = 1.62119…` (Aldaz, 2000, Proposition 1.4 with `n = 2`). -/
theorem ofReal_phi_le_weakTypeConstant_two : ENNReal.ofReal phi ≤ weakTypeConstant 2 := by
  sorry

/-- `c₂ > 1.685`. -/
theorem weakTypeConstant_two_gt : ENNReal.ofReal (1685 / 1000) < weakTypeConstant 2 := by
  sorry

end CenteredMaximal
