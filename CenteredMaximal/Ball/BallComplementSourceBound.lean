/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallComplementCertificate

/-!
# Bounded whole-space representative of the local obstacle Laplacian

The complementary density lies between zero and the cap on the ball, while the smooth input is
bounded. Extending their difference by zero gives a globally measurable bounded function. This
is the density in the local distributional Laplacian and in mollifier convergence.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped RealInnerProductSpace ENNReal

namespace CenteredMaximal.Ball.DirichletSobolev

variable {n : ℕ}

/-- Extend the real local Laplacian density `ρ-F` by zero. -/
def ballComplementSourceExtension
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (F ρ : L2D (ball center R)) : EuclideanSpace ℝ (Fin (n + 1)) → ℝ :=
  (ball center R).indicator (fun x => ((ρ - F) x : ℝ))

/-- The zero-extended local density is measurable up to null sets. -/
theorem ballComplementSourceExtension_aestronglyMeasurable
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (F ρ : L2D (ball center R)) :
    AEStronglyMeasurable (ballComplementSourceExtension center R F ρ) volume := by
  have hlocal : AEStronglyMeasurable
      (fun x => ((ρ - F) x : ℝ))
      (volume.restrict (ball center R)) := Lp.aestronglyMeasurable (ρ - F)
  exact (aestronglyMeasurable_indicator_iff measurableSet_ball).2 hlocal

/-- The zero-extended density is integrable because `ρ-F` lies in `L²` on a finite-volume
ball. -/
theorem ballComplementSourceExtension_integrable
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (F ρ : L2D (ball center R)) :
    Integrable (ballComplementSourceExtension center R F ρ) := by
  letI : IsFiniteMeasure (volume.restrict (ball center R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  have hlocal : Integrable (fun x => ((ρ - F) x : ℝ))
      (volume.restrict (ball center R)) :=
    (Lp.memLp (ρ - F)).integrable (by norm_num)
  exact MeasureTheory.IntegrableOn.integrable_indicator hlocal measurableSet_ball

/-- The zero extension agrees with the local `L²` density almost everywhere on the ball. -/
theorem ballComplementSourceExtension_ae_eq_local
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (F ρ : L2D (ball center R)) :
    ballComplementSourceExtension center R F ρ
      =ᵐ[volume.restrict (ball center R)]
        fun x => ((ρ - F) x : ℝ) := by
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_ball] with x hx
  simp [ballComplementSourceExtension, hx]

/-- The complementary density and a bounded source give a local bound for `ρ-F`. -/
theorem ballComplementSource_local_bound
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (F ρ : L2D (ball center R)) (κ M : ℝ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ κ • ballUnitL2 center R)
    (hF : ∀ᵐ x ∂(volume.restrict (ball center R)), ‖(F x : ℝ)‖ ≤ M) :
    ∀ᵐ x ∂(volume.restrict (ball center R)),
      ‖((ρ - F) x : ℝ)‖ ≤ κ + M := by
  filter_upwards [(Lp.coeFn_nonneg ρ).2 hρ.1,
    (Lp.coeFn_le ρ (κ • ballUnitL2 center R)).2 hρ.2,
    Lp.coeFn_smul κ (ballUnitL2 center R), ballUnitL2_coeFn center R,
    Lp.coeFn_sub ρ F, hF] with x hρ0 hρκ hsmul hunit hsub hFbound
  have hρ0' : (0 : ℝ) ≤ (ρ x : ℝ) := by simpa only [Pi.zero_apply] using hρ0
  have hρκ' : (ρ x : ℝ) ≤ κ := by
    simpa only [hsmul, Pi.smul_apply, smul_eq_mul, hunit, mul_one] using hρκ
  have hρnorm : ‖(ρ x : ℝ)‖ ≤ κ := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg hρ0'] using hρκ'
  rw [hsub]
  exact (norm_sub_le _ _).trans (add_le_add hρnorm hFbound)

/-- A local cap gives a global almost-everywhere bound after zero extension. -/
theorem ballComplementSourceExtension_bound
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (F ρ : L2D (ball center R)) (κ M : ℝ)
    (hκ : 0 ≤ κ) (hM : 0 ≤ M)
    (hρ : 0 ≤ ρ ∧ ρ ≤ κ • ballUnitL2 center R)
    (hF : ∀ᵐ x ∂(volume.restrict (ball center R)), ‖(F x : ℝ)‖ ≤ M) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      ‖ballComplementSourceExtension center R F ρ x‖ ≤ κ + M := by
  have hlocal := ballComplementSource_local_bound center R F ρ κ M hρ hF
  have hglobal : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      x ∈ ball center R → ‖((ρ - F) x : ℝ)‖ ≤ κ + M :=
    (ae_restrict_iff' measurableSet_ball).mp hlocal
  filter_upwards [hglobal] with x hx
  by_cases hball : x ∈ ball center R
  · simpa only [ballComplementSourceExtension, Set.indicator_of_mem hball]
      using hx hball
  · simp [ballComplementSourceExtension, hball, add_nonneg hκ hM]

/-- A continuous compactly supported input supplies a finite uniform bound for its local
`L²` source on every ball. -/
theorem exists_ballSourceL2_bound
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᵐ x ∂(volume.restrict (ball center R)),
        ‖((ballSourceL2 center R f hfcont hfcomp) x : ℝ)‖ ≤ M := by
  obtain ⟨M, hM⟩ := hfcomp.exists_bound_of_continuous hfcont
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  filter_upwards [ballSourceL2_coeFn center R f hfcont hfcomp] with x hx
  rw [hx]
  exact (hM x).trans (le_max_left _ _)

/-- The local Laplacian density of a smooth ball obstacle has a bounded, measurable
whole-space zero extension. -/
theorem exists_bounded_ballComplementSourceExtension
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f)
    (ρ : L2D (ball center R)) (κ : ℝ) (hκ : 0 ≤ κ)
    (hρ : 0 ≤ ρ ∧ ρ ≤ κ • ballUnitL2 center R) :
    ∃ B : ℝ, 0 ≤ B ∧
      AEStronglyMeasurable
        (ballComplementSourceExtension center R
          (ballSourceL2 center R f hfcont hfcomp) ρ) volume ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
        ‖ballComplementSourceExtension center R
          (ballSourceL2 center R f hfcont hfcomp) ρ x‖ ≤ B := by
  obtain ⟨M, hM, hF⟩ := exists_ballSourceL2_bound center R f hfcont hfcomp
  exact ⟨κ + M, add_nonneg hκ hM,
    ballComplementSourceExtension_aestronglyMeasurable center R
      (ballSourceL2 center R f hfcont hfcomp) ρ,
    ballComplementSourceExtension_bound center R
      (ballSourceL2 center R f hfcont hfcomp) ρ κ M hκ hM hρ hF⟩

end CenteredMaximal.Ball.DirichletSobolev
