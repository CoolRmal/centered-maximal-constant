/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.ObstacleExistence
public import CenteredMaximal.Ball.CompactSupportIBP

/-!
# Local distributional Laplacian of a Dirichlet solution

A weak Dirichlet equation on a ball implies the corresponding distributional Laplacian identity
for smooth tests whose support lies inside the ball. This connects the penalized weak limit to
the local Green pairing.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped RealInnerProductSpace ENNReal

namespace CenteredMaximal.Ball.DirichletSobolev

variable {d : ℕ}

/-- The graph of a smooth compactly supported test function is an element of `H₀¹`. -/
def IsTestFn.toH01 {D : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn D φ) : H01 D :=
  ⟨h.testGraph,
    (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨φ, h, rfl⟩)⟩

@[simp] theorem IsTestFn.toH01_value {D : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn D φ) :
    ((h.toH01 : H1amb D) 0) = h.testCls := by
  rfl

@[simp] theorem IsTestFn.toH01_partial {D : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn D φ) (i : Fin d) :
    ((h.toH01 : H1amb D) i.succ) = h.partialCls i := by
  rfl

/-- The classical partial derivative of a test function is again a test function. -/
theorem IsTestFn.partialD {D : Set (EuclideanSpace ℝ (Fin d))}
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn D φ) (i : Fin d) :
    IsTestFn D (partialD i φ) := by
  refine ⟨?_, h.hasCompactSupport_partialD i, (tsupport_partialD_subset i φ).trans h.2.2⟩
  exact (h.1.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- Testing a weak Dirichlet equation with a smooth compactly supported function. -/
theorem weak_equation_testFn {D : Set (EuclideanSpace ℝ (Fin d))}
    (U : H01 D) (g : L2D D)
    (heq : ∀ V : H01 D, laplaceBilin D U V = l2Functional D g V)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn D φ) :
    (∑ i : Fin d, ⟪(U : H1amb D) i.succ, h.partialCls i⟫) =
      ∫ x in D, (g x : ℝ) * φ x := by
  have htest := heq h.toH01
  rw [laplaceBilin_apply, l2Functional_eq_integral] at htest
  have hint : (∫ x in D, (g x : ℝ) * (h.testCls x : ℝ)) =
      ∫ x in D, (g x : ℝ) * φ x := by
    apply integral_congr_ae
    filter_upwards [h.mem_lp.coeFn_toLp] with x hx
    simp only [IsTestFn.testCls, hx]
  simpa only [IsTestFn.toH01_partial, IsTestFn.toH01_value, hint] using htest

/-- The coordinate gradient pairing equals the negative pairing with a second derivative
of the test function. -/
theorem weak_gradient_second_partial {D : Set (EuclideanSpace ℝ (Fin d))}
    (U : H01 D) {φ : EuclideanSpace ℝ (Fin d) → ℝ}
    (h : IsTestFn D φ) (i : Fin d) :
    ⟪(U : H1amb D) i.succ, h.partialCls i⟫ =
      -(∫ x in D, ((U : H1amb D) 0 x : ℝ) * partialD i (partialD i φ) x) := by
  let hpartial := h.partialD i
  have hgrad := (mem_W12_iff (U : H1amb D)).1
    ((H01_le_W12 D) U.property) (partialD i φ) hpartial i
  have hclass : hpartial.testCls = h.partialCls i := by
    rfl
  rw [hclass, real_inner_comm ((U : H1amb D) i.succ) (h.partialCls i)] at hgrad
  have hint : ⟪hpartial.partialCls i, (U : H1amb D) 0⟫ =
      ∫ x in D, ((U : H1amb D) 0 x : ℝ) * partialD i (partialD i φ) x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hpartial.memLp_partialD i |>.coeFn_toLp] with x hx
    simp only [Real.inner_apply, IsTestFn.partialCls, hx]
    ring
  rw [hint] at hgrad
  linarith

/-- The Euclidean Laplacian is the sum of the second coordinate partial derivatives. -/
theorem laplacian_eq_sum_partialD
    (φ : EuclideanSpace ℝ (Fin d) → ℝ) (hφ : ContDiff ℝ 2 φ)
    (y : EuclideanSpace ℝ (Fin d)) :
    Laplacian.laplacian φ y = ∑ i : Fin d, partialD i (partialD i φ) y := by
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis φ
    (EuclideanSpace.basisFun (Fin d) ℝ)) y]
  simp only [EuclideanSpace.basisFun_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← fderiv_partial_eq_iteratedFDeriv d φ hφ (EuclideanSpace.single i 1) y]
  rfl

/-- A weak Dirichlet equation gives the distributional Laplacian identity for every smooth
test compactly supported in the domain. With the convention `B(U,V)=∫gV`, the
distributional Laplacian of `U` is `-g`. -/
theorem weak_equation_local_distributional_laplacian
    {D : Set (EuclideanSpace ℝ (Fin d))}
    (U : H01 D) (g : L2D D)
    (heq : ∀ V : H01 D, laplaceBilin D U V = l2Functional D g V)
    {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn D φ) :
    (∫ x in D, ((U : H1amb D) 0 x : ℝ) * Laplacian.laplacian φ x) =
      -(∫ x in D, (g x : ℝ) * φ x) := by
  have hint (i : Fin d) :
      Integrable (fun x => ((U : H1amb D) 0 x : ℝ) *
        partialD i (partialD i φ) x) (volume.restrict D) :=
    (Lp.memLp ((U : H1amb D) 0)).integrable_mul ((h.partialD i).memLp_partialD i)
  have hφtwo : ContDiff ℝ 2 φ := h.1.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hsum :
      (∫ x in D, ((U : H1amb D) 0 x : ℝ) * Laplacian.laplacian φ x) =
        ∑ i : Fin d, ∫ x in D, ((U : H1amb D) 0 x : ℝ) *
          partialD i (partialD i φ) x := by
    calc
      (∫ x in D, ((U : H1amb D) 0 x : ℝ) * Laplacian.laplacian φ x) =
          ∫ x in D, ∑ i : Fin d, ((U : H1amb D) 0 x : ℝ) *
            partialD i (partialD i φ) x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [laplacian_eq_sum_partialD φ hφtwo x]
        simp only [Finset.mul_sum]
      _ = ∑ i : Fin d, ∫ x in D, ((U : H1amb D) 0 x : ℝ) *
            partialD i (partialD i φ) x := by
        rw [integral_finsetSum]
        exact fun i _ => hint i
  have hgradient :
      (∑ i : Fin d, ⟪(U : H1amb D) i.succ, h.partialCls i⟫) =
        -(∑ i : Fin d, ∫ x in D, ((U : H1amb D) 0 x : ℝ) *
          partialD i (partialD i φ) x) := by
    simp_rw [weak_gradient_second_partial U h]
    simp only [Finset.sum_neg_distrib]
  have hweak := weak_equation_testFn U g heq h
  rw [hsum]
  linarith

/-- The weak ball equation from the penalized obstacle has a local distributional Laplacian.
The `L²` right-hand side is the source minus the cap plus the capped density. -/
theorem ball_obstacle_local_distributional_laplacian
    {n : ℕ} (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (U : H01 (ball center R)) (f ν : L2D (ball center R)) (κ : ℝ)
    (heq : ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        l2Functional (ball center R) f V -
          κ * l2Functional (ball center R) (ballUnitL2 center R) V +
          ⟪ν, valueEmbedding (ball center R) V⟫)
    {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ}
    (hφ : IsTestFn (ball center R) φ) :
    (∫ x in ball center R,
      ((U : H1amb (ball center R)) 0 x : ℝ) * Laplacian.laplacian φ x) =
      -(∫ x in ball center R,
        ((f - κ • ballUnitL2 center R + ν) x : ℝ) * φ x) := by
  have heq' : ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        l2Functional (ball center R) (f - κ • ballUnitL2 center R + ν) V := by
    intro V
    rw [heq V]
    simp only [l2Functional_apply, valueEmbedding_apply,
      inner_add_left, inner_sub_left, real_inner_smul_left]
  exact weak_equation_local_distributional_laplacian U
    (f - κ • ballUnitL2 center R + ν) heq' hφ

end CenteredMaximal.Ball.DirichletSobolev
