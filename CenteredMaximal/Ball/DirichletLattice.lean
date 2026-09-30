/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.DirichletForm
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
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

/-- The value and weak-gradient coordinates characterizing the positive part of a
Dirichlet Sobolev function. -/
def IsPositivePartGraph (U P : H01 Ω) : Prop :=
  (((P : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
    =ᵐ[volume.restrict Ω] fun x => max ((U : H1amb Ω) 0 x : ℝ) 0) ∧
  ∀ i : Fin d, ((P : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
    =ᵐ[volume.restrict Ω] fun x =>
      if 0 < ((U : H1amb Ω) 0 x : ℝ) then ((U : H1amb Ω) i.succ x : ℝ) else 0

/-- The value and weak-gradient coordinates characterizing the pointwise minimum.
At equality we choose the first gradient; the two gradients agree a.e. on the equality
set for Sobolev functions. -/
def IsMinimumGraph (U V M : H01 Ω) : Prop :=
  (((M : H1amb Ω) 0 : EuclideanSpace ℝ (Fin d) → ℝ)
    =ᵐ[volume.restrict Ω] fun x =>
      min ((U : H1amb Ω) 0 x : ℝ) ((V : H1amb Ω) 0 x : ℝ)) ∧
  ∀ i : Fin d, ((M : H1amb Ω) i.succ : EuclideanSpace ℝ (Fin d) → ℝ)
    =ᵐ[volume.restrict Ω] fun x =>
      if ((V : H1amb Ω) 0 x : ℝ) < ((U : H1amb Ω) 0 x : ℝ)
      then ((V : H1amb Ω) i.succ x : ℝ)
      else ((U : H1amb Ω) i.succ x : ℝ)

/-- A weak-gradient graph in `H₀¹` is uniquely determined by its value coordinate.
This packages uniqueness of distributional derivatives in the local graph model. -/
theorem H01_eq_of_value_eq (hΩ : IsOpen Ω) (U V : H01 Ω)
    (hval : (U : H1amb Ω) 0 = (V : H1amb Ω) 0) : U = V := by
  let D : H01 Ω := U - V
  have hD0 : (D : H1amb Ω) 0 = 0 := by
    simp [D, hval]
  have hDw : (D : H1amb Ω) ∈ W12 Ω := H01_le_W12 Ω D.2
  have hgrad : ∀ i : Fin d, (D : H1amb Ω) i.succ = 0 := by
    intro i
    let f : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ((D : H1amb Ω) i.succ x : ℝ)
    have hf : LocallyIntegrableOn f Ω volume :=
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Lp.memLp ((D : H1amb Ω) i.succ)).locallyIntegrable one_le_two)
    have htest : ∀ φ : EuclideanSpace ℝ (Fin d) → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
        ∫ x, φ x • f x ∂volume = 0 := by
      intro φ hφ hcs hs
      let h : IsTestFn Ω φ := ⟨hφ, hcs, hs⟩
      have hrel := (mem_W12_iff (D : H1amb Ω)).mp hDw φ h i
      rw [hD0] at hrel
      simp only [inner_zero_right, zero_add] at hrel
      have hclass : inner ℝ h.testCls ((D : H1amb Ω) i.succ) =
          ∫ x in Ω, φ x * f x := by
        rw [L2.inner_def]
        refine integral_congr_ae ?_
        filter_upwards [h.mem_lp.coeFn_toLp] with x hx
        simp only [Real.inner_apply, IsTestFn.testCls, f, hx]
      rw [hclass] at hrel
      have hcompl : ∀ x ∉ Ω, φ x • f x = 0 := by
        intro x hx
        have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport fun hc => hx (hs hc)
        simp [hφx]
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hcompl]
      simpa only [smul_eq_mul] using hrel
    have hzero := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf htest
    apply Lp.ext
    filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem hΩ.measurableSet,
      Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx hxΩ hz
    simpa only [f, hz, Pi.zero_apply] using hx hxΩ
  have hD : D = 0 := by
    apply Subtype.ext
    apply PiLp.ext
    intro j
    induction j using Fin.cases with
    | zero => exact hD0
    | succ i => exact hgrad i
  have : U - V = 0 := hD
  exact sub_eq_zero.mp this

/-- Positive and negative part graphs decompose the original Sobolev element. -/
theorem H01_eq_positive_sub_negative (hΩ : IsOpen Ω) (U P N : H01 Ω)
    (hP : IsPositivePartGraph U P) (hN : IsPositivePartGraph (-U) N) :
    U = P - N := by
  apply H01_eq_of_value_eq hΩ
  apply Lp.ext
  filter_upwards [hP.1, hN.1, Lp.coeFn_neg ((U : H1amb Ω) 0),
    Lp.coeFn_sub ((P : H1amb Ω) 0) ((N : H1amb Ω) 0)] with x hp hn hneg hsub
  simp only [Submodule.coe_neg, PiLp.neg_apply] at hn
  simp only [Submodule.coe_sub, PiLp.sub_apply]
  rw [hsub]
  change ((U : H1amb Ω) 0 x : ℝ) =
    ((P : H1amb Ω) 0 x : ℝ) - ((N : H1amb Ω) 0 x : ℝ)
  rw [hp, hn, hneg, Pi.neg_apply]
  exact (max_zero_sub_max_neg_zero_eq_self _).symm

/-- The positive and negative part graphs are orthogonal for the pure-gradient
Dirichlet form. -/
theorem laplaceBilin_positive_negative_eq_zero_of_graph (U P N : H01 Ω)
    (hP : IsPositivePartGraph U P) (hN : IsPositivePartGraph (-U) N) :
    laplaceBilin Ω P N = 0 := by
  apply laplaceBilin_positive_negative_eq_zero U P N hP.2
  intro i
  filter_upwards [hN.2 i, Lp.coeFn_neg ((U : H1amb Ω) 0),
    Lp.coeFn_neg ((U : H1amb Ω) i.succ)] with x hn hval hgrad
  simp only [Submodule.coe_neg, PiLp.neg_apply] at hn
  rw [hn, hval, hgrad]
  simp only [Pi.neg_apply, neg_pos]

/-- A positive-part graph for `U - V` produces the pointwise minimum graph
`U - (U - V)⁺`. -/
theorem isMinimumGraph_of_isPositivePartGraph (U V P : H01 Ω)
    (hP : IsPositivePartGraph (U - V) P) : IsMinimumGraph U V (U - P) := by
  constructor
  · filter_upwards [hP.1, Lp.coeFn_sub ((U : H1amb Ω) 0) ((V : H1amb Ω) 0),
      Lp.coeFn_sub ((U : H1amb Ω) 0) ((P : H1amb Ω) 0)] with x hp huv hum
    simp only [Submodule.coe_sub, PiLp.sub_apply, huv, hum, Pi.sub_apply] at hp ⊢
    rw [hp]
    by_cases h : ((U : H1amb Ω) 0 x : ℝ) ≤ ((V : H1amb Ω) 0 x : ℝ)
    · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]
      ring
    · have h' : ((V : H1amb Ω) 0 x : ℝ) ≤ ((U : H1amb Ω) 0 x : ℝ) :=
        le_of_lt (lt_of_not_ge h)
      rw [min_eq_right h', max_eq_left (sub_nonneg.mpr h')]
      ring
  · intro i
    filter_upwards [hP.2 i, Lp.coeFn_sub ((U : H1amb Ω) 0) ((V : H1amb Ω) 0),
      Lp.coeFn_sub ((U : H1amb Ω) i.succ) ((V : H1amb Ω) i.succ),
      Lp.coeFn_sub ((U : H1amb Ω) i.succ) ((P : H1amb Ω) i.succ)]
      with x hp huv hug hum
    simp only [Submodule.coe_sub, PiLp.sub_apply, huv, hug, hum, Pi.sub_apply] at hp ⊢
    rw [hp]
    by_cases h : ((V : H1amb Ω) 0 x : ℝ) < ((U : H1amb Ω) 0 x : ℝ)
    · rw [if_pos (sub_pos.mpr h), if_pos h]
      ring
    · rw [if_neg (not_lt.mpr (sub_nonpos.mpr (not_lt.mp h))), if_neg h]
      ring

end CenteredMaximal.Ball.DirichletSobolev
