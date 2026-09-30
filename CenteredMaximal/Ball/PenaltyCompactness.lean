/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.WeakCompact
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.Topology.Sequences

/-!
# Weak compactness for penalized obstacle densities

Bounded sequences in a separable Hilbert space have weakly convergent subsequences. Closed convex
constraints, including the pointwise interval `0 ≤ ν ≤ κ` in `L²`, pass to the weak limit.
-/

@[expose] public section

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory Metric Set Filter Topology InnerProductSpace
open scoped RealInnerProductSpace ENNReal

namespace CenteredMaximal.Ball

/-- Bounded sequences in a separable real Hilbert space admit a weakly convergent subsequence,
and every closed convex constraint passes to its limit. -/
theorem exists_weakly_convergent_subsequence_of_bounded
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {C : Set H} (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (u : ℕ → H) (B : ℝ) (hu : ∀ k, u k ∈ C)
    (hbound : ∀ k, ‖u k‖ ≤ B) :
    ∃ v ∈ C, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k => toWeakSpace ℝ H (u (φ k))) atTop
        (𝓝 (toWeakSpace ℝ H v)) := by
  let K : Set (WeakDual ℝ H) :=
    WeakDual.toStrongDual ⁻¹' closedBall (toDual ℝ H 0) B
  have hK : IsSeqCompact K :=
    WeakDual.isSeqCompact_closedBall ℝ H (toDual ℝ H 0) B
  let z : ℕ → WeakDual ℝ H := fun k =>
    InnerProductSpace.toWeakDualHomeomorph (toWeakSpace ℝ H (u k))
  have hz : ∀ k, z k ∈ K := by
    intro k
    simp only [z, K, mem_preimage, toStrongDual_toWeakDualHomeomorph]
    change dist (toDual ℝ H (u k)) (toDual ℝ H 0) ≤ B
    simpa [dist_eq_norm, ← map_sub] using hbound k
  obtain ⟨q, hq, φ, hmono, hlim⟩ := hK hz
  let v : H := (toWeakSpace ℝ H).symm
    (InnerProductSpace.toWeakDualHomeomorph.symm q)
  have hweak : Tendsto (fun k => toWeakSpace ℝ H (u (φ k))) atTop
      (𝓝 (toWeakSpace ℝ H v)) := by
    have hmap := InnerProductSpace.toWeakDualHomeomorph.symm.continuous.tendsto q
    have ht := hmap.comp hlim
    convert ht using 1
    · funext k
      simp [z]
    · simp [v]
  have hCweak : IsClosed (toWeakSpace ℝ H '' C) :=
    hconv.isClosed_toWeakSpace_image hclosed
  have hv : v ∈ C := by
    have hmem : toWeakSpace ℝ H v ∈ toWeakSpace ℝ H '' C :=
      hCweak.mem_of_tendsto hweak (Filter.Eventually.of_forall fun k =>
        ⟨u (φ k), hu (φ k), rfl⟩)
    rcases hmem with ⟨t, ht, heq⟩
    have : t = v := (toWeakSpace ℝ H).injective heq
    simpa [this] using ht
  exact ⟨v, hv, φ, hmono, hweak⟩

private instance l2PosSMulMono
    {X : Type*} [MeasurableSpace X] {μ : Measure X} :
    PosSMulMono ℝ (Lp ℝ 2 μ) where
  smul_le_smul_of_nonneg_left := by
    intro a ha f g hfg
    rw [← Lp.coeFn_le] at hfg ⊢
    filter_upwards [hfg, Lp.coeFn_smul a f, Lp.coeFn_smul a g]
      with y hy hfy hgy
    rw [hfy, hgy]
    exact mul_le_mul_of_nonneg_left hy ha

/-- Uniformly bounded `L²` densities satisfying `0 ≤ νₖ ≤ κ` have a weakly convergent
subsequence. Its limit satisfies the same almost-everywhere bounds. -/
theorem exists_weakly_convergent_l2_density_subsequence
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsSeparable μ]
    (ν : ℕ → Lp ℝ 2 μ) (κ : Lp ℝ 2 μ) (B : ℝ)
    (hν : ∀ k, 0 ≤ ν k ∧ ν k ≤ κ)
    (hbound : ∀ k, ‖ν k‖ ≤ B) :
    ∃ νlim : Lp ℝ 2 μ, (0 ≤ νlim ∧ νlim ≤ κ) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun k => toWeakSpace ℝ (Lp ℝ 2 μ) (ν (φ k))) atTop
          (𝓝 (toWeakSpace ℝ (Lp ℝ 2 μ) νlim)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have h := exists_weakly_convergent_subsequence_of_bounded
    (C := Icc (0 : Lp ℝ 2 μ) κ) (convex_Icc _ _) isClosed_Icc ν B
    (fun k => hν k) hbound
  obtain ⟨νlim, hmem, φ, hmono, hweak⟩ := h
  exact ⟨νlim, hmem, φ, hmono, hweak⟩

end CenteredMaximal.Ball
