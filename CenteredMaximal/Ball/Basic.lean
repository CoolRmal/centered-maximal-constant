/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Basic

/-!
# Basic API for the centred maximal function over Euclidean balls

These definitions are distinct from the existing cube maximal function. In particular, the
ambient space has the Euclidean norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace CenteredMaximal

variable {d : ℕ}

/-- Every ball average is at most the ball maximal function. -/
theorem le_ballMaximalFunction (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) {r : ℝ} (hr : 0 < r) :
    (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ ≤ ballMaximalFunction f x :=
  le_iSup₂ (f := fun r (_ : 0 < r) =>
    (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ) r hr

/-- If a level is below the ball maximal function, some ball average exceeds it. -/
theorem exists_lt_ball_average_of_lt_ballMaximalFunction
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)} {α : ℝ≥0∞}
    (h : α < ballMaximalFunction f x) :
    ∃ r, 0 < r ∧ α < (volume (ball x r))⁻¹ * ∫⁻ y in ball x r, ‖f y‖ₑ := by
  obtain ⟨r, hr⟩ := lt_iSup_iff.1 h
  obtain ⟨hr₀, hr⟩ := lt_iSup_iff.1 hr
  exact ⟨r, hr₀, hr⟩

/-- A ball weak type bound remains one when increased. -/
theorem IsBallWeakTypeBound.mono {C C' : ℝ≥0∞}
    (h : IsBallWeakTypeBound d C) (hCC' : C ≤ C') : IsBallWeakTypeBound d C' :=
  fun f hf α => (h f hf α).trans (mul_le_mul_left hCC' _)

/-- The ball weak type constant is no larger than any ball weak type bound. -/
theorem ballWeakTypeConstant_le {C : ℝ≥0∞} (h : IsBallWeakTypeBound d C) :
    ballWeakTypeConstant d ≤ C :=
  sInf_le h

/-- A bound below every ball weak type bound is below the optimal ball constant. -/
theorem le_ballWeakTypeConstant {c : ℝ≥0∞}
    (h : ∀ C, IsBallWeakTypeBound d C → c ≤ C) : c ≤ ballWeakTypeConstant d :=
  le_sInf h

end CenteredMaximal
