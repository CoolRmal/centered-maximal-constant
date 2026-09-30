/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.LocalMollifier
public import CenteredMaximal.Ball.BallWeakDistribution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Laplacian of a smooth convolution

A compactly supported smooth kernel may be differentiated twice under convolution with an
integrable function. The resulting identity prepares the local transfer from a weak
Laplacian equation to a pointwise bound on the Laplacian of mollifications.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology ContinuousLinearMap
open scoped Convolution RealInnerProductSpace

namespace CenteredMaximal.Ball
open DirichletSobolev
variable {n : ℕ}

/-- A coordinate derivative passes through convolution with a smooth compact kernel. -/
theorem partialD_convolution_left
    (u φ : EuclideanSpace ℝ (Fin n) → ℝ) (hu : Integrable u)
    (hφsupp : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    partialD i (φ ⋆[lsmul ℝ ℝ, volume] u) x =
      ((partialD i φ) ⋆[lsmul ℝ ℝ, volume] u) x := by
  have hd := hφsupp.hasFDerivAt_convolution_left (lsmul ℝ ℝ)
    (hφ.of_le (by simp)) hu.locallyIntegrable x
  rw [partialD, hd.fderiv]
  have hfc : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hci := (hφsupp.fderiv ℝ).convolutionExists_left
    ((lsmul ℝ ℝ).precompL (EuclideanSpace ℝ (Fin n))) hfc hu.locallyIntegrable x
  simp only [convolution_def] at hci ⊢
  rw [ContinuousLinearMap.integral_apply hci]
  rfl

/-- The Laplacian is a finite sum of convolutions with second coordinate derivatives. -/
theorem laplacian_convolution_left_eq_sum
    (u φ : EuclideanSpace ℝ (Fin n) → ℝ) (hu : Integrable u)
    (hφsupp : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian (φ ⋆[lsmul ℝ ℝ, volume] u) x =
      ∑ i : Fin n, ((partialD i (partialD i φ)) ⋆[lsmul ℝ ℝ, volume] u) x := by
  have htest : IsTestFn (Set.univ : Set (EuclideanSpace ℝ (Fin n))) φ :=
    ⟨hφ, hφsupp, Set.subset_univ _⟩
  have hconv : ContDiff ℝ 2 (φ ⋆[lsmul ℝ ℝ, volume] u) :=
    (hφsupp.contDiff_convolution_left (lsmul ℝ ℝ) hφ hu.locallyIntegrable).of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  rw [laplacian_eq_sum_partialD _ hconv x]
  apply Finset.sum_congr rfl
  intro i _
  have hp : partialD i (φ ⋆[lsmul ℝ ℝ, volume] u) =
      (partialD i φ) ⋆[lsmul ℝ ℝ, volume] u := by
    funext y
    exact partialD_convolution_left u φ hu hφsupp hφ i y
  rw [hp]
  exact partialD_convolution_left u (partialD i φ) hu
    (htest.partialD i).2.1 (htest.partialD i).1 i x

/-- The Laplacian passes through convolution with a smooth compact kernel. -/
theorem laplacian_convolution_left
    (u φ : EuclideanSpace ℝ (Fin n) → ℝ) (hu : Integrable u)
    (hφsupp : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian (φ ⋆[lsmul ℝ ℝ, volume] u) x =
      ((Laplacian.laplacian φ) ⋆[lsmul ℝ ℝ, volume] u) x := by
  have htest : IsTestFn (Set.univ : Set (EuclideanSpace ℝ (Fin n))) φ :=
    ⟨hφ, hφsupp, Set.subset_univ _⟩
  have hφtwo : ContDiff ℝ 2 φ := hφ.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [laplacian_convolution_left_eq_sum u φ hu hφsupp hφ x]
  have hint (i : Fin n) : Integrable
      (fun t => partialD i (partialD i φ) t * u (x - t)) volume := by
    have htest2 := (htest.partialD i).partialD i
    have h := htest2.2.1.convolutionExists_left (lsmul ℝ ℝ)
      htest2.1.continuous hu.locallyIntegrable x
    simpa only [ConvolutionExistsAt, lsmul_apply, smul_eq_mul] using h
  simp only [convolution_def, lsmul_apply, smul_eq_mul]
  rw [← integral_finsetSum (s := Finset.univ) (fun i _ => hint i)]
  congr 1
  funext t
  rw [laplacian_eq_sum_partialD φ hφtwo t]
  simp only [Finset.sum_mul]

end CenteredMaximal.Ball
