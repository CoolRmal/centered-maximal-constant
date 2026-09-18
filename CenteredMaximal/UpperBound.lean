/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Basic
public import Mathlib.MeasureTheory.Covering.Vitali

/-!
# The upper bound `c_d ≤ 2ᵈ`

Let `E = {M f > α}`. Every `x ∈ E` is the centre of a cube `Q_x` with `α |Q_x| < ∫_{Q_x} |f|`;
these cubes have bounded radii. Mathlib's Vitali lemma with enlargement `τ > 1` selects a disjoint
subfamily such that every `Q_x` meets a selected `Q_b` with `r_x ≤ τ r_b`. Then the *centre*
`x` lies in the cube of radius `(1 + τ) r_b` about `b`; covering only the centres is what saves
the factor `3ᵈ` of the uncentred argument. Summing over the disjoint selected cubes gives
`α |E| ≤ (1 + τ)ᵈ ‖f‖₁`, and letting `τ → 1` gives `2ᵈ` (Tao, 245A Notes 5, Exercise 42, whose
hint notes that one needs an epsilon of room).
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter Set
open scoped ENNReal Topology

namespace CenteredMaximal

variable {d : ℕ}

/-- In dimension `0` the space is a point, and `1` is a weak type bound. -/
theorem isWeakTypeBound_one_of_dim_zero : IsWeakTypeBound 0 1 := by
  sorry

/-- A cube whose volume times `α > 0` stays below a finite `K` has radius at most
`max 1 (K / α)`, in positive dimension. -/
theorem radius_le_of_mul_volume_lt (hd : 0 < d) {α K : ℝ≥0∞} (hα : 0 < α) (hK : K ≠ ∞)
    {x : Fin d → ℝ} {r : ℝ} (hr : 0 < r) (h : α * volume (closedBall x r) < K) :
    r ≤ max 1 (K / α).toReal := by
  sorry

/-- The Vitali argument with an epsilon of room: `α |{M f > α}| ≤ (1 + τ)ᵈ ‖f‖₁` for `τ > 1`. -/
theorem mul_volume_le_of_one_lt (hd : 0 < d) {f : (Fin d → ℝ) → ℝ} (hf : Integrable f)
    (α : ℝ≥0∞) {τ : ℝ} (hτ : 1 < τ) :
    α * volume {x | α < maximalFunction f x} ≤ ENNReal.ofReal ((1 + τ) ^ d) * ∫⁻ x, ‖f x‖ₑ := by
  sorry

/-- `2ᵈ` is a weak type bound in dimension `d`. -/
theorem isWeakTypeBound_two_pow (d : ℕ) : IsWeakTypeBound d (2 ^ d) := by
  sorry

end CenteredMaximal
