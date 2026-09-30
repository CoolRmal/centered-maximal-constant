/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.LocalWeakPairing
public import CenteredMaximal.Ball.BallWeakDistribution

/-!
# From a weak ball equation to the local Green-pairing interface

The Dirichlet equation is expressed using integrals over a ball. Smooth tests
supported inside that ball, along with their Laplacians, vanish outside it.
This converts the equation to the whole-space local distributional identity
used by the Green-pairing argument.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter
open scoped ENNReal RealInnerProductSpace Topology

namespace CenteredMaximal.Ball

private theorem integral_eq_setIntegral_of_zero_outside {n : ℕ}
    (D : Set (EuclideanSpace ℝ (Fin n))) (hD : MeasurableSet D)
    (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hzero : ∀ x, x ∉ D → F x = 0) :
    (∫ x, F x) = ∫ x in D, F x := by
  have hsupport : Function.support F ⊆ D := by
    intro x hx
    by_contra hxD
    exact hx (hzero x hxD)
  rw [← integral_indicator hD, Set.indicator_eq_self.mpr hsupport]

private theorem laplacian_eq_zero_outside_tsupport {n : ℕ}
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (hφD : tsupport φ ⊆ D)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ D) :
    Laplacian.laplacian φ x = 0 := by
  have hnot : x ∉ tsupport φ := fun h ↦ hx (hφD h)
  have hzero : φ =ᶠ[𝓝 x] (0 : EuclideanSpace ℝ (Fin n) → ℝ) :=
    notMem_tsupport_iff_eventuallyEq.mp hnot
  have hΔzero := (InnerProductSpace.laplacian_congr_nhds hzero).eq_of_nhds
  simpa [Pi.zero_def] using hΔzero

/-- The weak ball obstacle equation has the local distributional Laplacian
`κ - f - ν`. The representatives of `H₀¹` and `L²` may be arbitrary outside
the ball; all test integrals are insensitive to those values. -/
theorem DirichletSobolev.ball_obstacle_hasLocalDistributionalLaplacian
    {n : ℕ} (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (U : DirichletSobolev.H01 (ball center R))
    (f ν : DirichletSobolev.L2D (ball center R)) (κ : ℝ)
    (heq : ∀ V : DirichletSobolev.H01 (ball center R),
      DirichletSobolev.laplaceBilin (ball center R) U V =
        DirichletSobolev.l2Functional (ball center R) f V -
          κ * DirichletSobolev.l2Functional (ball center R)
            (DirichletSobolev.ballUnitL2 center R) V +
          ⟪ν, DirichletSobolev.valueEmbedding (ball center R) V⟫) :
    HasLocalDistributionalLaplacian (n + 1) (ball center R)
      (fun x ↦ ((U : DirichletSobolev.H1amb (ball center R)) 0 x : ℝ))
      (fun x ↦ -((f - κ • DirichletSobolev.ballUnitL2 center R + ν) x : ℝ)) := by
  let D := ball center R
  let s : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
    fun x ↦ ((f - κ • DirichletSobolev.ballUnitL2 center R + ν) x : ℝ)
  intro φ hφsupp hφsmooth hφD
  have htest : DirichletSobolev.IsTestFn D φ := ⟨hφsmooth, hφsupp, hφD⟩
  have hφzero (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : x ∉ D) : φ x = 0 := by
    by_contra hnonzero
    exact hx (hφD (subset_tsupport φ (by simpa [Function.mem_support] using hnonzero)))
  have hleft : (∫ x, φ x * -s x) = ∫ x in D, φ x * -s x :=
    integral_eq_setIntegral_of_zero_outside D measurableSet_ball _
      (fun x hx ↦ by simp [hφzero x hx])
  have hright :
      (∫ x, ((U : DirichletSobolev.H1amb D) 0 x : ℝ) *
        Laplacian.laplacian φ x) =
      ∫ x in D, ((U : DirichletSobolev.H1amb D) 0 x : ℝ) *
        Laplacian.laplacian φ x :=
    integral_eq_setIntegral_of_zero_outside D measurableSet_ball _
      (fun x hx ↦ by simp [laplacian_eq_zero_outside_tsupport φ D hφD x hx])
  have hweak := DirichletSobolev.ball_obstacle_local_distributional_laplacian
    center R U f ν κ heq htest
  change (∫ x, φ x * -s x) =
    ∫ x, ((U : DirichletSobolev.H1amb D) 0 x : ℝ) * Laplacian.laplacian φ x
  rw [hleft, hright]
  calc
    (∫ x in D, φ x * -s x) = -(∫ x in D, s x * φ x) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = ∫ x in D,
        ((U : DirichletSobolev.H1amb D) 0 x : ℝ) * Laplacian.laplacian φ x := hweak.symm

end CenteredMaximal.Ball
