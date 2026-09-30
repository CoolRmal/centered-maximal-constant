/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.GreenIdentity
public import Mathlib.Analysis.Calculus.Rademacher

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

end CenteredMaximal.Ball
