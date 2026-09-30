/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# Smooth nonnegative approximation by local mollifiers

Normalized bump convolutions preserve nonnegativity and compact support, are infinitely
smooth, and converge almost everywhere. This supplies the pointwise part of the smooth
approximation required by the weak Green pairing argument.
-/

@[expose] public section
open MeasureTheory Metric Set Filter Topology ContinuousLinearMap
open scoped Convolution RealInnerProductSpace
noncomputable section
namespace CenteredMaximal.Ball
variable {n : ℕ}

/-- Standard normalized bump convolutions give smooth, compactly supported,
nonnegative approximants converging almost everywhere to an integrable input. -/
theorem exists_smooth_nonnegative_compact_mollifiers
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu_int : Integrable u) (hu_comp : HasCompactSupport u)
    (hu_nonneg : ∀ x, 0 ≤ u x) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (w k)) ∧
      (∀ k, HasCompactSupport (w k)) ∧
      (∀ k x, 0 ≤ w k x) ∧
      ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        Tendsto (fun k => w k x) atTop (𝓝 (u x)) := by
  let ε : ℕ → ℝ := fun k => 1 / (k + 1 : ℝ)
  have hε : ∀ k, 0 < ε k := fun k => by positivity
  let φ : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := fun k =>
    ⟨ε k / 2, ε k, half_pos (hε k), half_lt_self (hε k)⟩
  let w : ℕ → EuclideanSpace ℝ (Fin n) → ℝ := fun k =>
    (φ k).normed volume ⋆[lsmul ℝ ℝ, volume] u
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (φ k).hasCompactSupport_normed.contDiff_convolution_left
      (lsmul ℝ ℝ) (φ k).contDiff_normed hu_int.locallyIntegrable
  · intro k
    exact HasCompactSupport.convolution (lsmul ℝ ℝ)
      (φ k).hasCompactSupport_normed hu_comp
  · intro k x
    change 0 ≤ ∫ y, (φ k).normed volume y • u (x - y)
    apply integral_nonneg
    intro y
    simpa only [smul_eq_mul, Pi.zero_apply] using
      mul_nonneg ((φ k).nonneg_normed (μ := volume) y) (hu_nonneg (x - y))
  · have hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0) := by
      simpa only [φ, ε, one_div] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have hratio : ∀ᶠ k : ℕ in atTop, (φ k).rOut ≤ 2 * (φ k).rIn := by
      filter_upwards with k
      dsimp [φ]
      have h : 2 * (ε k / 2) = ε k := by ring
      rw [h]
    exact (ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      hφ hratio hu_int.locallyIntegrable)

end CenteredMaximal.Ball
