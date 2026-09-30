/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Geometry.Convex.Cone.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpOrder
public import CenteredMaximal.Ball.DirichletH01
public import CenteredMaximal.Ball.DirichletPoincareBounded
public import Mathlib.Tactic

/-!
# Existence and variational inequality for a Hilbert obstacle

The classical obstacle construction starts by minimizing a Dirichlet energy over a positive cone
in a Hilbert space. This file isolates that step: for any closed convex cone `K` in a real Hilbert
space and any continuous linear source functional, the quadratic energy has a minimizer. The
minimizer satisfies the variational inequality and the complementary energy identity. A later
application can take the Hilbert space to be the Dirichlet space `H¹₀(D)` and `K` to be its
nonnegative cone.
-/

@[expose] public section

noncomputable section

open InnerProductSpace
open scoped RealInnerProductSpace
open scoped ENNReal

namespace CenteredMaximal.Ball

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The quadratic energy with a bounded source functional. -/
def obstacleEnergy (ℓ : H →L[ℝ] ℝ) (u : H) : ℝ := (1 / 2 : ℝ) * ‖u‖ ^ 2 - ℓ u

/-- Completion of the square identifies the obstacle energy with distance from the Riesz
representative of the source. -/
theorem obstacleEnergy_eq_distance_sq (ℓ : H →L[ℝ] ℝ) (u : H) :
    obstacleEnergy ℓ u =
      (1 / 2 : ℝ) * ‖(toDual ℝ H).symm ℓ - u‖ ^ 2 -
        (1 / 2 : ℝ) * ‖(toDual ℝ H).symm ℓ‖ ^ 2 := by
  rw [norm_sub_sq_real, toDual_symm_apply]
  unfold obstacleEnergy
  ring

/-! ### Projection onto a closed convex admissible set -/

/-- The metric projection onto a nonempty closed convex set of a real Hilbert space. -/
def obstacleProjection (K : Set H) (hK : IsClosed K) (hconv : Convex ℝ K)
    (hne : K.Nonempty) (x : H) : H :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex hne hK.isComplete hconv x)

theorem obstacleProjection_mem_and_variational (K : Set H) (hK : IsClosed K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (x : H) :
    obstacleProjection K hK hconv hne x ∈ K ∧
      ∀ v ∈ K, ⟪x - obstacleProjection K hK hconv hne x,
        v - obstacleProjection K hK hconv hne x⟫_ℝ ≤ 0 := by
  obtain ⟨hmem, hmin⟩ :=
    Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex hne hK.isComplete hconv x)
  exact ⟨hmem, (norm_eq_iInf_iff_real_inner_le_zero hconv hmem).1 hmin⟩

/-- Metric projection onto a closed convex set is nonexpansive. -/
theorem obstacleProjection_norm_sub_le (K : Set H) (hK : IsClosed K)
    (hconv : Convex ℝ K) (hne : K.Nonempty) (x y : H) :
    ‖obstacleProjection K hK hconv hne x - obstacleProjection K hK hconv hne y‖ ≤ ‖x - y‖ := by
  let p := obstacleProjection K hK hconv hne x
  let q := obstacleProjection K hK hconv hne y
  obtain ⟨hp, hpVI⟩ := obstacleProjection_mem_and_variational K hK hconv hne x
  obtain ⟨hq, hqVI⟩ := obstacleProjection_mem_and_variational K hK hconv hne y
  have h₁ : 0 ≤ ⟪x - p, p - q⟫_ℝ := by
    have h := hpVI q hq
    have hneg : q - p = -(p - q) := by abel
    rw [hneg, inner_neg_right] at h
    linarith
  have h₂ : ⟪y - q, p - q⟫_ℝ ≤ 0 := hqVI p hp
  have hidentity : ⟪x - p, p - q⟫_ℝ - ⟪y - q, p - q⟫_ℝ =
      ⟪x - y, p - q⟫_ℝ - ‖p - q‖ ^ 2 := by
    rw [← inner_sub_left]
    have hvec : (x - p) - (y - q) = (x - y) - (p - q) := by abel
    rw [hvec, inner_sub_left, real_inner_self_eq_norm_sq]
  have hsq : ‖p - q‖ ^ 2 ≤ ⟪x - y, p - q⟫_ℝ := by linarith
  have hcauchy := real_inner_le_norm (x - y) (p - q)
  change ‖p - q‖ ≤ ‖x - y‖
  by_cases hz : ‖p - q‖ = 0
  · simp [hz]
  · have hpqpos : 0 < ‖p - q‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    nlinarith

/-- The Hilbert obstacle minimizer exists on every nonempty closed convex admissible set. Its
variational inequality has the sign convention appropriate for `-Δu = f - ν`. -/
theorem exists_obstacle_minimizer (ℓ : H →L[ℝ] ℝ) {K : Set H}
    (hK : IsClosed K) (hconv : Convex ℝ K) (hne : K.Nonempty) :
    ∃ u ∈ K, (∀ v ∈ K, obstacleEnergy ℓ u ≤ obstacleEnergy ℓ v) ∧
      (∀ v ∈ K, ℓ (v - u) ≤ ⟪u, v - u⟫_ℝ) := by
  let g : H := (toDual ℝ H).symm ℓ
  obtain ⟨u, hu, hproj⟩ :=
    exists_norm_eq_iInf_of_complete_convex hne hK.isComplete hconv g
  refine ⟨u, hu, ?_, ?_⟩
  · intro v hv
    have hnorm : ‖g - u‖ ≤ ‖g - v‖ := by
      rw [hproj]
      have hbelow : BddBelow (Set.range (fun w : K => ‖g - (w : H)‖)) :=
        ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩
      exact ciInf_le hbelow (⟨v, hv⟩ : K)
    rw [obstacleEnergy_eq_distance_sq, obstacleEnergy_eq_distance_sq]
    dsimp [g] at hnorm ⊢
    nlinarith [norm_nonneg (g - u), norm_nonneg (g - v)]
  · intro v hv
    have hinner := (norm_eq_iInf_iff_real_inner_le_zero hconv hu).1 hproj v hv
    change ⟪g - u, v - u⟫_ℝ ≤ 0 at hinner
    rw [inner_sub_left, toDual_symm_apply] at hinner
    exact sub_nonpos.mp hinner

/-- On a closed positive cone, the minimizer obeys the complementary energy identity. This is
obtained by using `0` and `2 • u` as the two competitors in the variational inequality. -/
theorem exists_obstacle_minimizer_cone (ℓ : H →L[ℝ] ℝ) (K : ConvexCone ℝ H)
    (hK : IsClosed (K : Set H)) (hzero : K.Pointed) :
    ∃ u ∈ K, (∀ v ∈ K, obstacleEnergy ℓ u ≤ obstacleEnergy ℓ v) ∧
      (∀ v ∈ K, ℓ (v - u) ≤ ⟪u, v - u⟫_ℝ) ∧
      ℓ u = ‖u‖ ^ 2 ∧ ‖u‖ ≤ ‖(toDual ℝ H).symm ℓ‖ := by
  obtain ⟨u, hu, hmin, hvi⟩ :=
    exists_obstacle_minimizer ℓ hK K.convex ⟨0, hzero⟩
  have hzeroVI := hvi 0 hzero
  have hdoubleVI := hvi ((2 : ℝ) • u) (K.smul_mem (by norm_num) hu)
  have hsub : (2 : ℝ) • u - u = u := by module
  rw [hsub] at hdoubleVI
  simp only [zero_sub, map_neg, inner_neg_right] at hzeroVI
  have henergy : ℓ u = ‖u‖ ^ 2 := by
    rw [real_inner_self_eq_norm_sq] at hzeroVI hdoubleVI
    linarith
  refine ⟨u, hu, hmin, hvi, henergy, ?_⟩
  have hinner : ⟪(toDual ℝ H).symm ℓ, u⟫_ℝ = ‖u‖ ^ 2 := by
    rw [toDual_symm_apply, henergy]
  have hbound := real_inner_le_norm ((toDual ℝ H).symm ℓ) u
  rw [hinner] at hbound
  by_cases hu0 : ‖u‖ = 0
  · simp [hu0]
  · have hupos : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg u) (Ne.symm hu0)
    nlinarith

omit [CompleteSpace H] in
/-- A variational-inequality solution on a convex admissible set is unique. -/
theorem obstacle_variational_unique (ℓ : H →L[ℝ] ℝ) {K : Set H} {u v : H}
    (hu : u ∈ K) (hv : v ∈ K)
    (huVI : ∀ w ∈ K, ℓ (w - u) ≤ ⟪u, w - u⟫_ℝ)
    (hvVI : ∀ w ∈ K, ℓ (w - v) ≤ ⟪v, w - v⟫_ℝ) : u = v := by
  have h₁ := huVI v hv
  have h₂ := hvVI u hu
  have hlin : ℓ (v - u) + ℓ (u - v) = 0 := by
    have hsum : v - u + (u - v) = 0 := by abel
    rw [← map_add, hsum, map_zero]
  have hinner : ⟪u, v - u⟫_ℝ + ⟪v, u - v⟫_ℝ = -‖u - v‖ ^ 2 := by
    calc
      _ = 2 * ⟪u, v⟫_ℝ - ‖u‖ ^ 2 - ‖v‖ ^ 2 := by
        rw [inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
          real_inner_self_eq_norm_sq, real_inner_comm v u]
        ring
      _ = -‖u - v‖ ^ 2 := by rw [norm_sub_sq_real]; ring
  have hnorm : ‖u - v‖ ^ 2 ≤ 0 := by linarith
  have hzero : ‖u - v‖ = 0 := by nlinarith [norm_nonneg (u - v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)

/-- The positive-direction half of the capped-density estimate. In the Dirichlet application,
`source` integrates against `f`, `mass` integrates against `1`, and the inner product is the
Dirichlet form; the conclusion is the distributional upper bound `f + Δu ≤ κ`. -/
theorem exists_obstacle_upper_cap (source mass : H →L[ℝ] ℝ) (κ : ℝ)
    (K : ConvexCone ℝ H) (hK : IsClosed (K : Set H)) (hzero : K.Pointed) :
    ∃ u ∈ K, ∀ φ ∈ K, source φ - ⟪u, φ⟫_ℝ ≤ κ * mass φ := by
  obtain ⟨u, hu, _, hvi, _, _⟩ :=
    exists_obstacle_minimizer_cone (source - κ • mass) K hK hzero
  refine ⟨u, hu, fun φ hφ => ?_⟩
  have h := hvi (u + φ) (K.add_mem hu hφ)
  have hsub : u + φ - u = φ := by abel
  rw [hsub] at h
  change source φ - κ * mass φ ≤ ⟪u, φ⟫_ℝ at h
  linarith

/-! ### Positive cone pulled back through a Dirichlet-space embedding -/

variable {X : Type*} [MeasurableSpace X] {μ : MeasureTheory.Measure X}

/-- The positive cone in an abstract Hilbert space whose elements have an `L²` representative.
For `H = H¹₀(D)`, the map is the usual continuous embedding into `L²(D)`. -/
def positiveLpCone (J : H →L[ℝ] MeasureTheory.Lp ℝ 2 μ) : ConvexCone ℝ H :=
  { carrier := {u | 0 ≤ J u}
    smul_mem' := by
      intro c hc u hu
      change 0 ≤ J u at hu
      change 0 ≤ J (c • u)
      rw [map_smul]
      rw [← MeasureTheory.Lp.coeFn_nonneg] at hu ⊢
      filter_upwards [hu, MeasureTheory.Lp.coeFn_smul c (J u)] with x hx hs
      rw [hs]
      exact mul_nonneg hc.le hx
    add_mem' := by
      intro u hu v hv
      change 0 ≤ J (u + v)
      rw [map_add]
      exact add_nonneg hu hv }

omit [CompleteSpace H] in
@[simp]
theorem mem_positiveLpCone (J : H →L[ℝ] MeasureTheory.Lp ℝ 2 μ) (u : H) :
    u ∈ positiveLpCone J ↔ 0 ≤ J u := Iff.rfl

omit [CompleteSpace H] in
theorem isClosed_positiveLpCone (J : H →L[ℝ] MeasureTheory.Lp ℝ 2 μ) :
    IsClosed (positiveLpCone J : Set H) := by
  change IsClosed (J ⁻¹' Set.Ici 0)
  exact isClosed_Ici.preimage J.continuous

omit [CompleteSpace H] in
theorem pointed_positiveLpCone (J : H →L[ℝ] MeasureTheory.Lp ℝ 2 μ) :
    (positiveLpCone J).Pointed := by
  simp [ConvexCone.Pointed, positiveLpCone]

/-- The abstract capped obstacle exists on any Hilbert space continuously embedded into `L²`.
The remaining PDE work is to equip `H¹₀(D)` with its gradient inner product and verify the
Markov truncation needed for the opposite inequality. -/
theorem exists_positiveLp_obstacle_upper_cap
    (J : H →L[ℝ] MeasureTheory.Lp ℝ 2 μ)
    (source mass : H →L[ℝ] ℝ) (κ : ℝ) :
    ∃ u : H, 0 ≤ J u ∧ ∀ φ : H, 0 ≤ J φ →
      source φ - ⟪u, φ⟫_ℝ ≤ κ * mass φ := by
  obtain ⟨u, hu, hcap⟩ := exists_obstacle_upper_cap source mass κ (positiveLpCone J)
    (isClosed_positiveLpCone J) (pointed_positiveLpCone J)
  exact ⟨u, (mem_positiveLpCone J u).1 hu,
    fun φ hφ => hcap φ ((mem_positiveLpCone J φ).2 hφ)⟩

/-! ### The concrete Sobolev Dirichlet space -/

namespace DirichletSobolev

variable {d : ℕ}

/-- Continuous coordinate-zero embedding of the concrete `H¹₀(D)` graph space into `L²(D)`. -/
def valueEmbedding (D : Set (EuclideanSpace ℝ (Fin d))) : H01 D →L[ℝ] L2D D :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin (d + 1) => L2D D) (0 : Fin (d + 1))).comp
    (H01 D).subtypeL

@[simp]
theorem valueEmbedding_apply (D : Set (EuclideanSpace ℝ (Fin d))) (U : H01 D) :
    valueEmbedding D U = (U : H1amb D) 0 := by
  simp only [valueEmbedding, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    PiLp.proj_apply]

/-- The closed convex nonnegative cone in the concrete Sobolev Dirichlet space. -/
def positiveH01Cone (D : Set (EuclideanSpace ℝ (Fin d))) : ConvexCone ℝ (H01 D) :=
  positiveLpCone (valueEmbedding D)

@[simp]
theorem mem_positiveH01Cone (D : Set (EuclideanSpace ℝ (Fin d))) (U : H01 D) :
    U ∈ positiveH01Cone D ↔ 0 ≤ (U : H1amb D) 0 := by
  rw [positiveH01Cone, mem_positiveLpCone, valueEmbedding_apply]

theorem isClosed_positiveH01Cone (D : Set (EuclideanSpace ℝ (Fin d))) :
    IsClosed (positiveH01Cone D : Set (H01 D)) :=
  isClosed_positiveLpCone (valueEmbedding D)

theorem pointed_positiveH01Cone (D : Set (EuclideanSpace ℝ (Fin d))) :
    (positiveH01Cone D).Pointed :=
  pointed_positiveLpCone (valueEmbedding D)

end DirichletSobolev

end CenteredMaximal.Ball
