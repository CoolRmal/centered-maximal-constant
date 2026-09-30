/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.KernelComparisonOnSupport
public import CenteredMaximal.Ball.BallComplementSourceBound

/-!
# Green comparison for the complementary obstacle density

The weak obstacle equation gives `ΔU = ρ - f` only inside the Dirichlet ball. A Green weight
supported there can still be compared with the whole-space zero extension of `ρ`.
-/

@[expose] public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CenteredMaximal.Ball

variable {n : ℕ}

/-- A nonnegative real Green pairing with the local Laplacian yields the exact extended-real
kernel comparison needed by the direct obstacle certificate. -/
theorem normalized_green_comparison_of_ballComplement
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f)
    (hf0 : ∀ y, 0 ≤ f y)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (ρlocal : DirichletSobolev.L2D (ball center R))
    (hρ : 0 ≤ ρlocal ∧ ρlocal ≤ κ • DirichletSobolev.ballUnitL2 center R)
    (K : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ)
    (q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hqint : Integrable q)
    (hQ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) = ENNReal.ofReal (q y))
    (hq0 : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))] q)
    (hsupport : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      q y ≠ 0 → y ∈ ball center R)
    (hpair : 0 ≤ ∫ y, q y *
      DirichletSobolev.ballComplementSourceExtension center R
        (DirichletSobolev.ballSourceL2 center R f hfcont hfcomp) ρlocal y) :
    (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
      ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) *
        extendRestrictedDensity (ball center R) ρlocal y := by
  let D := ball center R
  let F := DirichletSobolev.ballSourceL2 center R f hfcont hfcomp
  let g := DirichletSobolev.ballComplementSourceExtension center R F ρlocal
  let ρ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := D.indicator (ρlocal : _ → ℝ)
  have hF : (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) =ᵐ[volume.restrict D] f :=
    DirichletSobolev.ballSourceL2_coeFn center R f hfcont hfcomp
  have hlocal : g =ᵐ[volume.restrict D]
      (fun y ↦ (ρlocal y : ℝ) - f y) := by
    filter_upwards [DirichletSobolev.ballComplementSourceExtension_ae_eq_local
      center R F ρlocal, Lp.coeFn_sub ρlocal F, hF]
      with y hg hsub hfy
    calc
      g y = ((ρlocal - F) y : ℝ) := hg
      _ = (ρlocal y : ℝ) - (F y : ℝ) := hsub
      _ = (ρlocal y : ℝ) - f y := by rw [hfy]
  have hrel : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      q y ≠ 0 → f y = ρ y - g y :=
    source_relation_on_kernel_support volume D measurableSet_ball q f
      ρlocal g hsupport hlocal
  have hρ0 : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))] ρ :=
    ae_nonneg_indicator_of_ae_restrict volume D measurableSet_ball ρlocal
      ((Lp.coeFn_nonneg ρlocal).2 hρ.1)
  have hN : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      extendRestrictedDensity D ρlocal y = ENNReal.ofReal (ρ y) := by
    filter_upwards with y
    exact extendRestrictedDensity_eq_ofReal_indicator D ρlocal y
  obtain ⟨M, hM⟩ := hfcomp.exists_bound_of_continuous hfcont
  have hfint : Integrable (fun y ↦ q y * f y) :=
    hqint.mul_bdd hfcont.aestronglyMeasurable (Filter.Eventually.of_forall hM)
  obtain ⟨B, hB0, hgmeas, hgbound⟩ :=
    DirichletSobolev.exists_bounded_ballComplementSourceExtension
      center R f hfcont hfcomp ρlocal κ hκ hρ
  have hgint : Integrable (fun y ↦ q y * g y) :=
    hqint.mul_bdd hgmeas hgbound
  have hρint : Integrable (fun y ↦ q y * ρ y) := by
    apply (hfint.add hgint).congr
    filter_upwards [hrel] with y hy
    by_cases hqy : q y = 0
    · simp [hqy]
    · dsimp
      rw [hy hqy]
      ring
  exact normalized_green_comparison_of_pairing_on_support K x r hQ hN
    hq0 (Filter.Eventually.of_forall hf0) hρ0 hfint hρint hgint hrel hpair

end CenteredMaximal.Ball
