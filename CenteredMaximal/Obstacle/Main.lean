/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Obstacle.Complementarity

/-!
# The obstacle decomposition

Fix `0 < α < 2`, a cap `0 < κ` and an obstacle `f : ℝ² → ℝ` which is measurable, nonnegative,
bounded by `Mf` and supported in the cube `Q(0, b)`. This file packages the four files
`CenteredMaximal.Obstacle.Functional`, `CenteredMaximal.Obstacle.Variational`,
`CenteredMaximal.Obstacle.Complementarity` and the generator of
`CenteredMaximal.Analysis.JumpGenerator` into the single interface theorem
`exists_obstacle_solution`, which is the form in which the obstacle problem is consumed by the
transfer argument: a nonnegative integrable `u` and a density `σ` with values in `[0, κ]` solving
the weak equation `∫ u A φ = ∫ (σ − f) φ` for every test function `φ`, where `A = jumpGen α`,
together with the complementarity relation `σ = κ` almost everywhere on the contact set
`{u > 0}`, mass conservation `∫ σ = ∫ f` and the contact-set bound `|{u > 0}| ≤ (∫ f) / κ`.

Nothing new is proved here. The minimiser `u` is `CenteredMaximal.exists_isMinOn_nonnegCone`, the
density is `CenteredMaximal.exists_density`, the weak equation is the test-function identity of the
density rewritten by the duality `CenteredMaximal.jumpForm_eq_neg_integral_jumpGen` between the
form and the generator, and the last three conclusions are
`CenteredMaximal.ae_eq_of_pos`, `CenteredMaximal.integrable_and_integral_density_eq` and
`CenteredMaximal.volume_pos_lt_le`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set

namespace CenteredMaximal

open EnergySpace

variable {α : ℝ}

/-- The obstacle decomposition for the coordinate-stable generator of order `α`. -/
theorem exists_obstacle_solution (hα : 0 < α) (hα' : α < 2) {κ : ℝ} (hκ : 0 < κ)
    {f : (Fin 2 → ℝ) → ℝ} (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {Mf : ℝ}
    (hfb : ∀ x, f x ≤ Mf) {b : ℝ} (hb : 0 < b) (hfsupp : ∀ x, b < ‖x‖ → f x = 0) :
    ∃ u σ : (Fin 2 → ℝ) → ℝ,
      Measurable u ∧ (0 ≤ᵐ[volume] u) ∧ Integrable u volume ∧
      Measurable σ ∧ (∀ x, 0 ≤ σ x) ∧ (∀ x, σ x ≤ κ) ∧ Integrable σ volume ∧
      (∀ φ, IsTestFunction φ → ∫ x, u x * jumpGen α φ x = ∫ x, (σ x - f x) * φ x) ∧
      (∀ᵐ x ∂volume, 0 < u x → σ x = κ) ∧
      (∫ x, σ x = ∫ x, f x) ∧
      volume {x | 0 < u x} ≤ ENNReal.ofReal ((∫ x, f x) / κ) := by
  have hf2 : MemLp f 2 volume := memLp_two_of_bounded hfm hf0 hfb hfsupp
  -- a bounded measurable function supported in a cube is integrable
  have hf₁ : Integrable f volume := by
    have hg : Integrable ((closedBall (0 : Fin 2 → ℝ) b).indicator fun _ => Mf) volume :=
      (integrableOn_const (volume_closedBall_ne_top hb.le)).integrable_indicator
        measurableSet_closedBall
    refine hg.mono' hfm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
    by_cases hx : x ∈ closedBall (0 : Fin 2 → ℝ) b
    · rw [indicator_of_mem hx]
      exact hfb x
    · rw [indicator_of_notMem hx, hfsupp x (by simpa [mem_closedBall, dist_eq_norm] using hx)]
  obtain ⟨u₀, hu₀, hu₀fin, hu₀min⟩ := exists_isMinOn_nonnegCone hα hκ hfm hf0 hfb hb hfsupp
  obtain ⟨σ, hσm, hσ0, hσκ, hσT⟩ := exists_density hα hα' hκ.le hf2 hf0 hu₀ hu₀fin hu₀min
  obtain ⟨hσint, hmass⟩ :=
    integrable_and_integral_density_eq hα hα' hf₁ hf0 hu₀fin hσm hσ0 hσκ hσT
  refine ⟨⇑u₀, σ, measurable_coeFn u₀, mem_nonnegCone_iff_ae.1 hu₀,
    integrable_of_l1Norm_ne_top hu₀fin, hσm, hσ0, hσκ, hσint, fun φ hφ => ?_,
    ae_eq_of_pos hα hα' hf2 hf0 hfb hu₀ hu₀fin hu₀min hσm hσ0 hσκ hσT, hmass,
    volume_pos_lt_le hα hα' hκ hf₁ hf2 hf0 hfb hu₀ hu₀fin hu₀min hσm hσ0 hσκ hσT⟩
  -- the weak equation: the test-function identity of the density, read through the generator
  have hfφ : Integrable (fun x => f x * φ x) volume :=
    hf2.integrable_mul (memLp_two_of_isTestFunction hφ)
  have hσφ : Integrable (fun x => σ x * φ x) volume :=
    (integrable_of_isTestFunction hφ).bdd_mul hσm.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hσ0 x)]; exact hσκ x)
  have hsplit : (∫ x, (σ x - f x) * φ x) = (∫ x, σ x * φ x) - ∫ x, f x * φ x := by
    rw [← integral_sub hσφ hfφ]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have hdual : jumpForm α ⇑u₀ φ = -∫ x, u₀ x * jumpGen α φ x :=
    jumpForm_eq_neg_integral_jumpGen hα hα' (measurable_coeFn u₀)
      (integrable_of_l1Norm_ne_top hu₀fin) u₀.jumpEnergy_ne_top hφ
  have hid := hσT φ hφ
  rw [jumpForm_coeFn_ofTestFunction hα hα' hφ, hdual] at hid
  rw [hsplit]
  linarith

end CenteredMaximal

end
