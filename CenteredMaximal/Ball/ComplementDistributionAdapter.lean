/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.LocalDistributionAdapter

/-!
# Local distributional equation for a complementary obstacle density

A weak ball equation `B U = F - ρ` says that the positive representative of `U` has
distributional Laplacian `ρ - F` in the interior of the ball.
-/

@[expose] public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CenteredMaximal.Ball

/-- A local distributional equation is insensitive to changing its density almost everywhere
inside the domain containing the test functions' supports. -/
theorem HasLocalDistributionalLaplacian.congr_ae_restrict
    {n : ℕ} (D : Set (EuclideanSpace ℝ (Fin n))) (hD : MeasurableSet D)
    (w g g' : EuclideanSpace ℝ (Fin n) → ℝ)
    (h : HasLocalDistributionalLaplacian n D w g)
    (hgg' : g =ᵐ[volume.restrict D] g') :
    HasLocalDistributionalLaplacian n D w g' := by
  intro φ hφsupp hφsmooth hφD
  have hae : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∈ D → g x = g' x := (ae_restrict_iff' hD).mp hgg'
  calc
    (∫ x, φ x * g' x) = ∫ x, φ x * g x := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      by_cases hmem : x ∈ D
      · rw [hx hmem]
      · have hφzero : φ x = 0 := by
          by_contra hnonzero
          exact hmem (hφD (subset_tsupport φ
            (by simpa [Function.mem_support] using hnonzero)))
        simp [hφzero]
    _ = ∫ x, w x * Laplacian.laplacian φ x := h φ hφsupp hφsmooth hφD

namespace DirichletSobolev

variable {n : ℕ}

/-- Turn a difference of weak `L²` functionals into the functional of the difference. -/
theorem ball_weak_equation_sub
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (U : H01 (ball center R)) (F ρ : L2D (ball center R))
    (heq : ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        l2Functional (ball center R) F V -
          l2Functional (ball center R) ρ V) :
    ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        l2Functional (ball center R) (F - ρ) V := by
  intro V
  simpa only [l2Functional_apply, inner_sub_left] using heq V

/-- The positive representative of a weak obstacle satisfying `B U = F - ρ` has
distributional Laplacian `ρ - F` on the ball. -/
theorem ballPositiveRepresentative_hasLocalDistributionalLaplacian_of_complement
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (U : H01 (ball center R)) (F ρ : L2D (ball center R))
    (hU : 0 ≤ (U : H1amb (ball center R)) 0)
    (heq : ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        l2Functional (ball center R) (F - ρ) V) :
    HasLocalDistributionalLaplacian (n + 1) (ball center R)
      (ballPositiveRepresentative center R U)
      (fun x ↦ ((ρ - F) x : ℝ)) := by
  have heqOld : ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        l2Functional (ball center R) (F - ρ) V -
          (0 : ℝ) * l2Functional (ball center R) (ballUnitL2 center R) V +
          ⟪(0 : L2D (ball center R)), valueEmbedding (ball center R) V⟫_ℝ := by
    intro V
    simpa using heq V
  have hOld := ballPositiveRepresentative_hasLocalDistributionalLaplacian
    center R U hU (F - ρ) 0 0 heqOld
  have hOld' : HasLocalDistributionalLaplacian (n + 1) (ball center R)
      (ballPositiveRepresentative center R U)
      (fun x ↦ -(((F - ρ) x : ℝ))) := by
    simpa only [zero_smul, sub_zero, add_zero] using hOld
  have hρF : ρ - F = -(F - ρ) := by abel
  have hae : (fun x : EuclideanSpace ℝ (Fin (n + 1)) ↦ -(((F - ρ) x : ℝ)))
      =ᵐ[volume.restrict (ball center R)] (fun x ↦ ((ρ - F) x : ℝ)) := by
    rw [hρF]
    exact (Lp.coeFn_neg (F - ρ)).symm
  exact hOld'.congr_ae_restrict (ball center R) measurableSet_ball _ _ _ hae

end DirichletSobolev

end CenteredMaximal.Ball
