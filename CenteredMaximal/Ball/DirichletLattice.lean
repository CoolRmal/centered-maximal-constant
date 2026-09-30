/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.DirichletForm
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Tactic

/-!
# Truncations of Dirichlet Sobolev functions

We build the lattice operations on `H₀¹` from smooth scalar compositions of test functions.
The scalar regularizations used below vanish at zero, so composing them with a test function
does not enlarge its support. This file also records the Dirichlet form's Markov identity.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped RealInnerProductSpace ENNReal

noncomputable section

namespace CenteredMaximal.Ball.DirichletSobolev

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))}

/-- A smooth scalar map fixing zero preserves the class of smooth compactly supported test
functions. -/
theorem IsTestFn.comp_smooth {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : IsTestFn Ω φ) {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hF0 : F 0 = 0) :
    IsTestFn Ω (F ∘ φ) := by
  have hsupp : Function.support (F ∘ φ) ⊆ Function.support φ := by
    intro x hx
    contrapose! hx
    simp only [Function.mem_support, not_not] at hx ⊢
    simp [hx, hF0]
  have htsupp : tsupport (F ∘ φ) ⊆ tsupport φ := by
    exact closure_minimal (hsupp.trans (subset_tsupport φ)) (isClosed_tsupport φ)
  exact ⟨hF.comp hφ.1,
    hφ.2.1.of_isClosed_subset isClosed_closure htsupp,
    htsupp.trans hφ.2.2⟩

/-- Pointwise chain rule for the coordinate partials of a smooth test function. -/
theorem partialD_comp_smooth {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialD i (F ∘ φ) x = deriv F (φ x) * partialD i φ x := by
  rw [partialD, fderiv_comp x (hF.differentiable (by simp) (φ x))
    (hφ.differentiable (by simp) x)]
  simp only [ContinuousLinearMap.comp_apply, fderiv_eq_deriv_mul]
  rfl

end CenteredMaximal.Ball.DirichletSobolev
