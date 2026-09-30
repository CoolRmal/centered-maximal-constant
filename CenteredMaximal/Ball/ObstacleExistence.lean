/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
public import Mathlib.Geometry.Convex.Cone.Basic
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

end CenteredMaximal.Ball
