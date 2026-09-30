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

/-- Positive and negative truncations have disjoint gradients. This is the Dirichlet
form's Markov identity in the exact coordinate format delivered by a Sobolev lattice
theorem. -/
theorem laplaceBilin_positive_negative_eq_zero
    (U P N : H01 Ω)
    (hP : ∀ i : Fin d, ((P : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x =>
        if 0 < ((U : H1amb Ω) 0 x : ℝ) then ((U : H1amb Ω) i.succ x : ℝ) else 0)
    (hN : ∀ i : Fin d, ((N : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
      =ᵐ[volume.restrict Ω] fun x =>
        if ((U : H1amb Ω) 0 x : ℝ) < 0 then -((U : H1amb Ω) i.succ x : ℝ) else 0) :
    laplaceBilin Ω P N = 0 := by
  rw [laplaceBilin_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [L2.inner_def]
  have hzero : ∀ᵐ x ∂(volume.restrict Ω),
      (((P : H1amb Ω) i.succ x : ℝ) * ((N : H1amb Ω) i.succ x : ℝ)) = 0 := by
    filter_upwards [hP i, hN i] with x hp hn
    rw [hp, hn]
    split_ifs <;> simp_all; linarith
  rw [integral_eq_zero_of_ae]
  exact hzero.mono fun x hx => by simpa only [Real.inner_apply, Pi.zero_apply] using hx

end CenteredMaximal.Ball.DirichletSobolev
