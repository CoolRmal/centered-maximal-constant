/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.GreenIdentity
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-!
# Integration by parts for compactly supported smooth functions

A whole-space integration by parts formula provides a route to the ball flux identity using
smooth radial cutoffs. It follows from Mathlib's Rademacher integration by parts theorem after
showing that smooth compactly supported functions are globally Lipschitz.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal

namespace CenteredMaximal.Ball

/-- A continuously differentiable compactly supported function is globally Lipschitz. -/
theorem exists_lipschitzWith_of_contDiff_hasCompactSupport (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : HasCompactSupport f) : ∃ K : ℝ≥0, LipschitzWith K f := by
  obtain ⟨C, hC⟩ := (hs.fderiv ℝ).exists_bound_of_continuous
    (hf.continuous_fderiv (by norm_num))
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  refine ⟨K, lipschitzOnWith_univ.mp ?_⟩
  have hconv : Convex ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := convex_univ
  apply hconv.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
    (𝕜 := ℝ) (f' := fderiv ℝ f)
  · intro x _
    exact (hf.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt
  · intro x _
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hC x).trans (le_max_left _ _)

/-- Integration by parts along a fixed vector for two smooth compactly supported functions. -/
theorem integral_fderiv_mul_eq_neg (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ y, fderiv ℝ f y v * g y) =
      -(∫ y, f y * fderiv ℝ g y v) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport n f hf hsf
  obtain ⟨D, hD⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport n g hg hsg
  have h := hC.integral_lineDeriv_mul_eq (μ := volume) hD hsg v
  simp_rw [show ∀ y, lineDeriv ℝ f y v = fderiv ℝ f y v from
      fun y ↦ (hf.differentiable (by norm_num) y).lineDeriv_eq_fderiv,
    show ∀ y, lineDeriv ℝ g y (-v) = -(fderiv ℝ g y v) from
      fun y ↦ by rw [(hg.differentiable (by norm_num) y).lineDeriv_eq_fderiv, map_neg]] at h
  rw [← integral_neg]
  apply h.trans
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- Differentiating a fixed directional derivative gives the second directional derivative. -/
theorem fderiv_partial_eq_iteratedFDeriv (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (v y : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun z => fderiv ℝ w z v) y v =
      iteratedFDeriv ℝ 2 w y ![v, v] := by
  rw [iteratedFDeriv_two_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ w) y :=
    (hw.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) y
  simpa using congrArg (fun φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => φ v)
    (fderiv_clm_apply hd (differentiableAt_const v))

/-- Integration by parts for a second directional derivative. -/
theorem integral_second_partial_mul_eq_neg (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ y, iteratedFDeriv ℝ 2 f y ![v, v] * g y) =
      -(∫ y, fderiv ℝ f y v * fderiv ℝ g y v) := by
  have hpartial : ContDiff ℝ 1 (fun z => fderiv ℝ f z v) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hbase := integral_fderiv_mul_eq_neg n
    (fun z => fderiv ℝ f z v) g hpartial hg (hsf.fderiv_apply ℝ v) hsg v
  simpa only [fderiv_partial_eq_iteratedFDeriv n f hf v] using hbase

/-- A second directional derivative is self-adjoint under integration. -/
theorem integral_second_partial_selfadjoint (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin n)) :
    (∫ y, iteratedFDeriv ℝ 2 f y ![v, v] * g y) =
      (∫ y, f y * iteratedFDeriv ℝ 2 g y ![v, v]) := by
  have h1 := integral_second_partial_mul_eq_neg n f g hf
    (hg.of_le (by norm_num)) hsf hsg v
  have hpartial : ContDiff ℝ 1 (fun z => fderiv ℝ g z v) :=
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have h2 := integral_fderiv_mul_eq_neg n f (fun z => fderiv ℝ g z v)
    (hf.of_le (by norm_num)) hpartial hsf (hsg.fderiv_apply ℝ v) v
  simp_rw [fderiv_partial_eq_iteratedFDeriv n g hg v] at h2
  rw [h1, h2]
  ring

private theorem integrable_second_partial_mul (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (hsg : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y => iteratedFDeriv ℝ 2 f y ![v,v] * g y) := by
  have hiter : Continuous (iteratedFDeriv ℝ 2 f) :=
    hf.continuous_iteratedFDeriv (by norm_num)
  have hcont : Continuous (fun y => iteratedFDeriv ℝ 2 f y ![v,v] * g y) := by
    fun_prop
  exact hcont.integrable_of_hasCompactSupport hsg.mul_left

/-- The Laplacian is self-adjoint on twice continuously differentiable compactly supported
functions on Euclidean space. -/
theorem integral_laplacian_mul_eq_integral_mul_laplacian (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) :
    (∫ y, Laplacian.laplacian f y * g y) =
      (∫ y, f y * Laplacian.laplacian g y) := by
  let b := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))
  have hlf : ∀ y, Laplacian.laplacian f y =
      ∑ i, iteratedFDeriv ℝ 2 f y ![b i, b i] := by
    intro y
    exact congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f) y
  have hlg : ∀ y, Laplacian.laplacian g y =
      ∑ i, iteratedFDeriv ℝ 2 g y ![b i, b i] := by
    intro y
    exact congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis g) y
  simp_rw [hlf, hlg, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (by
      intro i _
      exact integrable_second_partial_mul n f g hf
        (hg.of_le (by norm_num)) hsg (b i)),
    integral_finsetSum Finset.univ (by
      intro i _
      have h : Integrable (fun y => iteratedFDeriv ℝ 2 g y ![b i,b i] * f y) :=
        integrable_second_partial_mul n g f hg
          (hf.of_le (by norm_num)) hsf (b i)
      convert h using 1
      funext y
      ring)]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_second_partial_selfadjoint n f g hf hg hsf hsg (b i)

/-- Weak integration by parts for the Laplacian. This is the form needed to pair a Laplacian
with a smooth radial cutoff and recover the ball boundary flux. -/
theorem integral_laplacian_mul_eq_neg_gradient (n : ℕ)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 1 g)
    (hsf : HasCompactSupport f) (hsg : HasCompactSupport g) :
    (∫ y, Laplacian.laplacian f y * g y) =
      -(∫ y, ∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
        fderiv ℝ f y ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i) *
        fderiv ℝ g y ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i)) := by
  let b := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))
  have hlf : ∀ y, Laplacian.laplacian f y =
      ∑ i, iteratedFDeriv ℝ 2 f y ![b i, b i] := by
    intro y
    exact congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis f) y
  have hint (i) : Integrable (fun y => fderiv ℝ f y (b i) * fderiv ℝ g y (b i)) := by
    have hfc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
    have hgc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
    have hc : Continuous (fun y => fderiv ℝ f y (b i) * fderiv ℝ g y (b i)) := by
      fun_prop
    exact hc.integrable_of_hasCompactSupport (hsf.fderiv_apply ℝ (b i)).mul_right
  simp_rw [hlf, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (by
      intro i _
      exact integrable_second_partial_mul n f g hf hg hsg (b i))]
  change (∑ i, ∫ y, iteratedFDeriv ℝ 2 f y ![b i,b i] * g y) =
    -(∫ y, ∑ i, fderiv ℝ f y (b i) * fderiv ℝ g y (b i))
  rw [integral_finsetSum Finset.univ (by intro i _; exact hint i), ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_second_partial_mul_eq_neg n f g hf hg hsf hsg (b i)

end CenteredMaximal.Ball
