/-
Copyright (c) 2026 Aaron. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
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

end CenteredMaximal.Ball
