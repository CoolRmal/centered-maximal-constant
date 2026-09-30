/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.LocalMollifierLaplacian
public import CenteredMaximal.Ball.LocalWeakPairing
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Mollification of a local distributional Laplacian

At an interior point where a translated kernel remains supported in the weak-equation domain,
the classical Laplacian of a mollification equals convolution with the distributional Laplacian.
-/

@[expose] public section

open MeasureTheory Metric Set Filter Topology ContinuousLinearMap
open scoped Convolution RealInnerProductSpace
noncomputable section
namespace CenteredMaximal.Ball
variable {n : ℕ}
/-- Reflection about a fixed point preserves the Laplacian. -/
theorem laplacian_comp_const_sub (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : ContDiff ℝ 2 φ) (a y : EuclideanSpace ℝ (Fin n)) :
    Laplacian.laplacian (fun z => φ (a - z)) y =
      Laplacian.laplacian φ (a - y) := by
  let ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun z => φ (a + z)
  have hψ : ContDiff ℝ 2 ψ := by fun_prop
  have hid : (fun z : EuclideanSpace ℝ (Fin n) => φ (a - z)) =
      (fun z => ψ ((-1 : ℝ) • z)) := by
    funext z
    simp [ψ, sub_eq_add_neg]
  rw [hid]
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (fun z => ψ ((-1 : ℝ) • z)) (EuclideanSpace.basisFun (Fin n) ℝ)) y]
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    φ (EuclideanSpace.basisFun (Fin n) ℝ)) (a-y)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [iteratedFDeriv_comp_const_smul (-1 : ℝ) hψ]
  simp only [neg_one_sq, one_smul]
  rw [iteratedFDeriv_comp_add_left 2 a]
  simp [sub_eq_add_neg]

/-- Convolution turns a local distributional equation into a classical pointwise equation. -/
theorem laplacian_convolution_eq_of_local_distribution
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (u g φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : Integrable u)
    (hlocal : HasLocalDistributionalLaplacian n D u g)
    (hφsupp : HasCompactSupport φ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (x : EuclideanSpace ℝ (Fin n))
    (hφx : tsupport (fun y => φ (x - y)) ⊆ D) :
    Laplacian.laplacian (φ ⋆[lsmul ℝ ℝ, volume] u) x =
      (φ ⋆[lsmul ℝ ℝ, volume] g) x := by
  have htestSupp : HasCompactSupport (fun y => φ (x-y)) := by
    simpa [Function.comp_def, Homeomorph.subLeft, Equiv.subLeft] using
      (hφsupp.comp_homeomorph (Homeomorph.subLeft x))
  have htestSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun y => φ (x-y)) := by
    fun_prop
  have hdist := hlocal (fun y => φ (x-y)) htestSupp htestSmooth hφx
  have hφtwo : ContDiff ℝ 2 φ := hφ.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  calc
    Laplacian.laplacian (φ ⋆[lsmul ℝ ℝ, volume] u) x =
        ((Laplacian.laplacian φ) ⋆[lsmul ℝ ℝ, volume] u) x :=
      laplacian_convolution_left u φ hu hφsupp hφ x
    _ = ∫ y, u y * Laplacian.laplacian (fun z => φ (x-z)) y := by
      rw [convolution_lsmul_swap]
      apply integral_congr_ae
      filter_upwards with y
      rw [laplacian_comp_const_sub φ hφtwo x y]
      simp [smul_eq_mul, mul_comm]
    _ = ∫ y, φ (x-y) * g y := hdist.symm
    _ = (φ ⋆[lsmul ℝ ℝ, volume] g) x := by
      rw [convolution_lsmul_swap]
      simp only [smul_eq_mul]
end CenteredMaximal.Ball
