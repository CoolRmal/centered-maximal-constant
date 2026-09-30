/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.WeakCompact
public import CenteredMaximal.Ball.DirichletH01
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

/-- Bounded sequences in a separable real Hilbert space have a weakly convergent subsequence,
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

/-- A nonnegative density bounded by an `L²` cap has no larger `L²` norm. -/
theorem norm_l2_le_of_nonneg_le
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (ν κ : Lp ℝ 2 μ) (hν : 0 ≤ ν) (hνκ : ν ≤ κ) : ‖ν‖ ≤ ‖κ‖ := by
  apply norm_le_norm_of_abs_le_abs
  simpa only [abs_of_nonneg hν, abs_of_nonneg (hν.trans hνκ)] using hνκ

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

/-- The cap alone supplies the uniform `L²` bound needed for weak sequential compactness. -/
theorem exists_weakly_convergent_l2_density_subsequence_of_cap
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsSeparable μ]
    (ν : ℕ → Lp ℝ 2 μ) (κ : Lp ℝ 2 μ)
    (hν : ∀ k, 0 ≤ ν k ∧ ν k ≤ κ) :
    ∃ νlim : Lp ℝ 2 μ, (0 ≤ νlim ∧ νlim ≤ κ) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun k => toWeakSpace ℝ (Lp ℝ 2 μ) (ν (φ k))) atTop
          (𝓝 (toWeakSpace ℝ (Lp ℝ 2 μ) νlim)) := by
  apply exists_weakly_convergent_l2_density_subsequence ν κ ‖κ‖ hν
  intro k
  exact norm_l2_le_of_nonneg_le (ν k) κ (hν k).1 (hν k).2

/-- Bounded states and capped densities have a common weakly convergent subsequence. A
bounded bilinear weak equation passes to the two limits. -/
theorem exists_weak_limit_of_bounded_penalized_equations
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H]
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsSeparable μ]
    (B : H →L[ℝ] H →L[ℝ] ℝ)
    (J : H →L[ℝ] Lp ℝ 2 μ) (source : H →L[ℝ] ℝ)
    (u : ℕ → H) (ν : ℕ → Lp ℝ 2 μ) (κ : Lp ℝ 2 μ)
    (Bu Bν : ℝ)
    (hboundu : ∀ k, ‖u k‖ ≤ Bu)
    (hboundν : ∀ k, ‖ν k‖ ≤ Bν)
    (hν : ∀ k, 0 ≤ ν k ∧ ν k ≤ κ)
    (heq : ∀ k v, B (u k) v = source v + ⟪ν k, J v⟫_ℝ) :
    ∃ ulim : H, ∃ νlim : Lp ℝ 2 μ, ∃ χ : ℕ → ℕ,
      (0 ≤ νlim ∧ νlim ≤ κ) ∧ StrictMono χ ∧
      Tendsto (fun k => toWeakSpace ℝ H (u (χ k))) atTop
        (𝓝 (toWeakSpace ℝ H ulim)) ∧
      Tendsto (fun k => toWeakSpace ℝ (Lp ℝ 2 μ) (ν (χ k))) atTop
        (𝓝 (toWeakSpace ℝ (Lp ℝ 2 μ) νlim)) ∧
      ∀ v, B ulim v = source v + ⟪νlim, J v⟫_ℝ := by
  obtain ⟨ulim, -, φ, hφ, huweak⟩ :=
    exists_weakly_convergent_subsequence_of_bounded
      (C := Set.univ) convex_univ isClosed_univ u Bu
      (fun _ => Set.mem_univ _) hboundu
  obtain ⟨νlim, hνlim, ψ, hψ, hνweak⟩ :=
    exists_weakly_convergent_l2_density_subsequence
      (fun k => ν (φ k)) κ Bν (fun k => hν (φ k))
      (fun k => hboundν (φ k))
  let χ := φ ∘ ψ
  have hχ : StrictMono χ := hφ.comp hψ
  have huweak' : Tendsto (fun k => toWeakSpace ℝ H (u (χ k))) atTop
      (𝓝 (toWeakSpace ℝ H ulim)) := by
    convert huweak.comp hψ.tendsto_atTop using 1
    funext k
    rfl
  refine ⟨ulim, νlim, χ, hνlim, hχ, huweak', hνweak, ?_⟩
  intro v
  have hBu : Tendsto (fun k => B (u (χ k)) v) atTop (𝓝 (B ulim v)) := by
    have hc := (B.flip v).continuous_comp_toWeakSpace_symm
    have h := hc.continuousAt.tendsto.comp huweak'
    simpa [Function.comp_def] using h
  have hνinner : Tendsto (fun k => ⟪ν (χ k), J v⟫_ℝ) atTop
      (𝓝 ⟪νlim, J v⟫_ℝ) := by
    let ℓ : Lp ℝ 2 μ →L[ℝ] ℝ := toDual ℝ (Lp ℝ 2 μ) (J v)
    have hc := ℓ.continuous_comp_toWeakSpace_symm
    have h := hc.continuousAt.tendsto.comp hνweak
    simpa [ℓ, χ, Function.comp_def, real_inner_comm] using h
  have hrhs := tendsto_const_nhds.add hνinner (a := source v)
  exact tendsto_nhds_unique
    (hBu.congr' (Filter.Eventually.of_forall fun k => heq (χ k) v)) hrhs

/-- The ball Dirichlet space is separable, so its norm-bounded sequences have weakly
convergent subsequences. -/
theorem separableSpace_H01_ball {n : ℕ}
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ) :
    TopologicalSpace.SeparableSpace (DirichletSobolev.H01 (ball center R)) := by
  letI : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  infer_instance

end CenteredMaximal.Ball
