/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Normed.Module.WeakDual
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Weak compactness in Hilbert spaces and the direct method

The direct method of the calculus of variations minimises a weakly lower semicontinuous functional
over a weakly compact set. This file collects the general lemmas about the weak topology
`WeakSpace ℝ H` of a real Hilbert space `H` that make this possible.

* `ContinuousLinearMap.continuous_comp_toWeakSpace_symm`: a continuous linear functional is
  continuous for the weak topology;
* `Convex.isClosed_toWeakSpace_image`: a closed convex set is weakly closed;
* `ConvexOn.lowerSemicontinuous_comp_toWeakSpace_symm`: a lower semicontinuous convex function is
  weakly lower semicontinuous;
* `InnerProductSpace.toWeakDualHomeomorph`: the Fréchet–Riesz map is a homeomorphism from `H` with
  the weak topology onto its dual with the weak-star topology;
* `isCompact_toWeakSpace_image_closedBall`, `Convex.isCompact_toWeakSpace_image`: closed balls, and
  more generally bounded closed convex sets, of a Hilbert space are weakly compact
  (Banach–Alaoglu transported through `toWeakDualHomeomorph`);
* `exists_isMinOn_of_isCompact_toWeakSpace_image`, `Convex.exists_isMinOn_of_isBounded_sublevel`:
  the direct method: a weakly lower semicontinuous function attains its minimum on a weakly
  compact set, and on a closed convex set as soon as one of its sublevel sets is bounded.
-/

@[expose] public section

noncomputable section

open Bornology Metric Set Topology
open scoped ENNReal RealInnerProductSpace

section WeakSpace

variable {𝕜 E : Type*} [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

/-- A continuous linear functional is continuous for the weak topology. -/
theorem ContinuousLinearMap.continuous_comp_toWeakSpace_symm (ℓ : E →L[𝕜] 𝕜) :
    Continuous (ℓ ∘ (toWeakSpace 𝕜 E).symm) :=
  WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip ℓ

/-- A supremum of weakly continuous `ℝ≥0∞`-valued functions is weakly lower semicontinuous. -/
theorem lowerSemicontinuous_iSup_comp_toWeakSpace_symm {ι : Sort*} {F : ι → E → ℝ≥0∞}
    (hF : ∀ i, Continuous (F i ∘ (toWeakSpace 𝕜 E).symm)) :
    LowerSemicontinuous ((fun x ↦ ⨆ i, F i x) ∘ (toWeakSpace 𝕜 E).symm) :=
  lowerSemicontinuous_iSup fun i ↦ (hF i).lowerSemicontinuous

/-- **Direct method**: a function that is lower semicontinuous for the weak topology on a
nonempty weakly compact set attains its minimum there. -/
theorem exists_isMinOn_of_isCompact_toWeakSpace_image {β : Type*} [LinearOrder β] {K : Set E}
    (hK : K.Nonempty) (hKc : IsCompact (toWeakSpace 𝕜 E '' K)) {J : E → β}
    (hJ : LowerSemicontinuousOn (J ∘ (toWeakSpace 𝕜 E).symm) (toWeakSpace 𝕜 E '' K)) :
    ∃ u ∈ K, IsMinOn J K u := by
  obtain ⟨a, ⟨u, hu, rfl⟩, ha⟩ := hJ.exists_isMinOn (hK.image _) hKc
  refine ⟨u, hu, isMinOn_iff.2 fun x hx ↦ ?_⟩
  simpa using isMinOn_iff.1 ha _ (mem_image_of_mem _ hx)

end WeakSpace

section LocallyConvex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E]

/-- A closed convex subset of a locally convex space is weakly closed. -/
theorem Convex.isClosed_toWeakSpace_image {s : Set E} (hs : Convex ℝ s) (hc : IsClosed s) :
    IsClosed (toWeakSpace ℝ E '' s) := by
  rw [← closure_eq_iff_isClosed, ← hs.toWeakSpace_closure ℝ, hc.closure_eq]

/-- A lower semicontinuous convex function on a locally convex space is lower semicontinuous for
the weak topology. -/
theorem ConvexOn.lowerSemicontinuous_comp_toWeakSpace_symm {J : E → ℝ} (hJ : ConvexOn ℝ univ J)
    (hJc : LowerSemicontinuous J) : LowerSemicontinuous (J ∘ (toWeakSpace ℝ E).symm) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  have : (J ∘ (toWeakSpace ℝ E).symm) ⁻¹' Iic c = toWeakSpace ℝ E '' (J ⁻¹' Iic c) := by
    rw [(toWeakSpace ℝ E).image_eq_preimage_symm]
    rfl
  have hc : Convex ℝ {x | J x ≤ c} := by simpa using hJ.convex_le c
  rw [this]
  exact hc.isClosed_toWeakSpace_image (hJc.isClosed_preimage c)

end LocallyConvex

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

namespace InnerProductSpace

/-- The Fréchet–Riesz representation `toDual ℝ H`, as a homeomorphism from `H` with its weak
topology onto the dual of `H` with its weak-star topology. -/
def toWeakDualHomeomorph : WeakSpace ℝ H ≃ₜ WeakDual ℝ H where
  toFun x := StrongDual.toWeakDual (toDual ℝ H ((toWeakSpace ℝ H).symm x))
  invFun ℓ := toWeakSpace ℝ H ((toDual ℝ H).symm (WeakDual.toStrongDual ℓ))
  left_inv x := by simp
  right_inv ℓ := by simp
  continuous_toFun := WeakBilin.continuous_of_continuous_eval _ fun y ↦
    -- the functional `x ↦ ⟪x, y⟫ = ⟪y, x⟫` is represented by `toDual ℝ H y`
    (toDual ℝ H y).continuous_comp_toWeakSpace_symm.congr fun x ↦ by
      simp only [Function.comp_apply, topDualPairing_apply, toDual_apply_apply]
      exact real_inner_comm _ _
  continuous_invFun := WeakBilin.continuous_of_continuous_eval _ fun f ↦
    -- the functional `ℓ ↦ f ((toDual ℝ H).symm ℓ)` is the evaluation at `(toDual ℝ H).symm f`
    (WeakDual.eval_continuous ((toDual ℝ H).symm f)).congr fun ℓ ↦ by
      change (WeakDual.toStrongDual ℓ) ((toDual ℝ H).symm f) =
        f ((toDual ℝ H).symm (WeakDual.toStrongDual ℓ))
      rw [← toDual_symm_apply, ← toDual_symm_apply, real_inner_comm]

/-- `toWeakDualHomeomorph x` is the functional `y ↦ ⟪x, y⟫`. -/
@[simp]
theorem toWeakDualHomeomorph_apply (x : WeakSpace ℝ H) (y : H) :
    toWeakDualHomeomorph x y = ⟪(toWeakSpace ℝ H).symm x, y⟫ :=
  rfl

/-- Read in the strong dual, `toWeakDualHomeomorph` is `toDual ℝ H`. -/
@[simp]
theorem toStrongDual_toWeakDualHomeomorph (x : WeakSpace ℝ H) :
    WeakDual.toStrongDual (toWeakDualHomeomorph x) = toDual ℝ H ((toWeakSpace ℝ H).symm x) :=
  rfl

/-- The inverse of `toWeakDualHomeomorph` is the Fréchet–Riesz representative map. -/
@[simp]
theorem toWeakDualHomeomorph_symm_apply (ℓ : WeakDual ℝ H) :
    toWeakDualHomeomorph.symm ℓ = toWeakSpace ℝ H ((toDual ℝ H).symm (WeakDual.toStrongDual ℓ)) :=
  rfl

end InnerProductSpace

open InnerProductSpace

/-- **Banach–Alaoglu** for Hilbert spaces: closed balls are weakly compact. -/
theorem isCompact_toWeakSpace_image_closedBall (x : H) (r : ℝ) :
    IsCompact (toWeakSpace ℝ H '' closedBall x r) := by
  have : toWeakSpace ℝ H '' closedBall x r =
      toWeakDualHomeomorph ⁻¹' (WeakDual.toStrongDual ⁻¹' closedBall (toDual ℝ H x) r) := by
    ext y
    simp [(toWeakSpace ℝ H).image_eq_preimage_symm, dist_eq_norm, ← map_sub]
  rw [this, toWeakDualHomeomorph.isCompact_preimage]
  exact WeakDual.isCompact_closedBall _ _

/-- A bounded closed convex subset of a Hilbert space is weakly compact. -/
theorem Convex.isCompact_toWeakSpace_image {s : Set H} (hs : Convex ℝ s) (hc : IsClosed s)
    (hb : IsBounded s) : IsCompact (toWeakSpace ℝ H '' s) := by
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall 0).1 hb
  exact (isCompact_toWeakSpace_image_closedBall 0 r).of_isClosed_subset
    (hs.isClosed_toWeakSpace_image hc) (image_mono hr)

/-- **Direct method** on a closed convex subset `K` of a Hilbert space: a function that is lower
semicontinuous for the weak topology on `K` and has a bounded sublevel set `{u ∈ K | J u ≤ J u₀}`
attains its minimum on `K`. -/
theorem Convex.exists_isMinOn_of_isBounded_sublevel {β : Type*} [LinearOrder β] {K : Set H}
    (hK : Convex ℝ K) (hKc : IsClosed K) {J : H → β}
    (hJ : LowerSemicontinuousOn (J ∘ (toWeakSpace ℝ H).symm) (toWeakSpace ℝ H '' K))
    {u₀ : H} (hu₀ : u₀ ∈ K) (hb : IsBounded {u ∈ K | J u ≤ J u₀}) :
    ∃ u ∈ K, IsMinOn J K u := by
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall 0).1 hb
  -- minimise over the weakly compact set `K ∩ closedBall 0 r`, which contains `u₀`
  have hK' : IsCompact (toWeakSpace ℝ H '' (K ∩ closedBall 0 r)) :=
    (hK.inter (convex_closedBall 0 r)).isCompact_toWeakSpace_image
      (hKc.inter isClosed_closedBall) (isBounded_closedBall.subset inter_subset_right)
  have hu₀' : u₀ ∈ K ∩ closedBall 0 r := ⟨hu₀, hr ⟨hu₀, le_rfl⟩⟩
  obtain ⟨u, ⟨huK, -⟩, hu⟩ := exists_isMinOn_of_isCompact_toWeakSpace_image ⟨u₀, hu₀'⟩ hK'
    (hJ.mono (image_mono inter_subset_left))
  refine ⟨u, huK, isMinOn_iff.2 fun x hx ↦ ?_⟩
  -- a point of `K` outside the ball lies above `J u₀ ≥ J u`
  rcases le_or_gt (J x) (J u₀) with h | h
  · exact isMinOn_iff.1 hu x ⟨hx, hr ⟨hx, h⟩⟩
  · exact (isMinOn_iff.1 hu u₀ hu₀').trans h.le

end Hilbert
