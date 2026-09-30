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
/-- A reflected kernel supported in a small ball stays inside a larger ball. -/
theorem reflected_kernel_support_inside_ball
    (center x : EuclideanSpace ℝ (Fin n)) (R ε : ℝ)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : tsupport φ ⊆ closedBall 0 ε)
    (hx : x ∈ ball center (R - ε)) :
    tsupport (fun y => φ (x-y)) ⊆ ball center R := by
  have hcomp : tsupport (fun y => φ (x-y)) =
      (fun y => x-y) ⁻¹' tsupport φ := by
    simpa [Function.comp_def, Homeomorph.subLeft, Equiv.subLeft] using
      (tsupport_comp_eq_preimage φ (Homeomorph.subLeft x))
  intro y hy
  rw [hcomp] at hy
  have hxy : dist y x ≤ ε := by
    have hs := hφ hy
    simpa [mem_closedBall, dist_eq_norm, norm_sub_rev] using hs
  have hxc : dist x center < R-ε := by simpa only [mem_ball] using hx
  have htri := dist_triangle y x center
  have hsum : dist y x + dist x center < ε + (R-ε) :=
    add_lt_add_of_le_of_lt hxy hxc
  have hR : ε + (R-ε) = R := by ring
  exact mem_ball.mpr (lt_of_le_of_lt htri (hR ▸ hsum))
/-- A normalized bump mollification satisfies the classical Laplace equation at interior points. -/
theorem laplacian_normed_bump_convolution_eq_of_local_distribution
    (center : EuclideanSpace ℝ (Fin n)) (R : ℝ)
    (u g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : Integrable u)
    (hlocal : HasLocalDistributionalLaplacian n (ball center R) u g)
    (φ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ ball center (R - φ.rOut)) :
    Laplacian.laplacian (φ.normed volume ⋆[lsmul ℝ ℝ, volume] u) x =
      (φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) x := by
  apply laplacian_convolution_eq_of_local_distribution (ball center R) u g
    (φ.normed volume) hu hlocal φ.hasCompactSupport_normed φ.contDiff_normed x
  exact reflected_kernel_support_inside_ball center x R φ.rOut (φ.normed volume)
    (by rw [φ.tsupport_normed_eq]) hx

/-- The Laplacians of normalized bump mollifications converge almost everywhere on interior
balls. -/
theorem ae_tendsto_laplacian_mollification_on_ball
    (center : EuclideanSpace ℝ (Fin n)) (R r : ℝ) (hr : r < R)
    (u g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : Integrable u) (hg : LocallyIntegrable g volume)
    (hlocal : HasLocalDistributionalLaplacian n (ball center R) u g)
    (φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)))
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0))
    (hratio : ∃ K : ℝ, ∀ᶠ k : ℕ in atTop, (φ k).rOut ≤ K * (φ k).rIn) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ ball center r →
      Tendsto (fun k => Laplacian.laplacian
        ((φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u) x)
        atTop (𝓝 (g x)) := by
  rcases hratio with ⟨K,hK⟩
  have hconv := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    hφ hK hg
  have hgap : 0 < R-r := sub_pos.mpr hr
  have hev : ∀ᶠ k : ℕ in atTop, (φ k).rOut < R-r :=
    hφ.eventually (isOpen_Iio.mem_nhds hgap)
  filter_upwards [hconv] with x hxconv hxin
  apply hxconv.congr'
  filter_upwards [hev] with k hk
  have hsmall : x ∈ ball center (R - (φ k).rOut) := by
    have hxr : dist x center < r := mem_ball.mp hxin
    apply mem_ball.mpr
    linarith
  exact (laplacian_normed_bump_convolution_eq_of_local_distribution
    center R u g hu hlocal (φ k) x hsmall).symm
end CenteredMaximal.Ball
