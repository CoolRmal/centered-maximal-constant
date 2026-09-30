/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.MonotoneSurjectivity
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Function.LpOrder

/-!
# The negative-part penalty in an `L²` embedding

The negative part is antitone and one-Lipschitz on real `L²`. Pulling it back through
an embedding into `L²` gives an antitone Lipschitz penalty on the Hilbert space.
-/

@[expose] public section

noncomputable section

open InnerProductSpace MeasureTheory
open scoped RealInnerProductSpace NNReal InnerProduct ENNReal

namespace CenteredMaximal.Ball

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- Negative part is one-Lipschitz on real `L²`. -/
theorem norm_l2_negPart_sub_le (a b : Lp ℝ 2 μ) :
    ‖Lp.negPart a - Lp.negPart b‖ ≤ ‖a - b‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [Lp.coeFn_sub (Lp.negPart a) (Lp.negPart b),
    Lp.coeFn_sub a b, Lp.coeFn_negPart_eq_max a,
    Lp.coeFn_negPart_eq_max b] with x hsub hdiff ha hb
  rw [hsub, hdiff, Pi.sub_apply, Pi.sub_apply, ha, hb]
  simp only [Real.norm_eq_abs]
  have h := abs_max_sub_max_le_abs (-a x) (-b x) (0 : ℝ)
  have heq : (-a x) - (-b x) = -(a x - b x) := by ring
  simpa only [heq, abs_neg] using h

/-- Negative part has nonpositive increment pairing with the original `L²` increment. -/
theorem l2_negPart_antitone_inner (a b : Lp ℝ 2 μ) :
    ⟪Lp.negPart a - Lp.negPart b, a - b⟫_ℝ ≤ 0 := by
  rw [L2.inner_def]
  apply integral_nonpos_of_ae
  filter_upwards [Lp.coeFn_sub (Lp.negPart a) (Lp.negPart b),
    Lp.coeFn_sub a b, Lp.coeFn_negPart_eq_max a,
    Lp.coeFn_negPart_eq_max b] with x hsub hdiff ha hb
  rw [hsub, hdiff, Pi.sub_apply, Pi.sub_apply, ha, hb]
  have hpoint : (max (-a x) 0 - max (-b x) 0) * (a x - b x) ≤ 0 := by
    rcases le_total (a x) (b x) with hab | hba
    · have hmax : max (-b x) 0 ≤ max (-a x) 0 := by gcongr
      exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hmax) (sub_nonpos.mpr hab)
    · have hmax : max (-a x) 0 ≤ max (-b x) 0 := by gcongr
      exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hmax) (sub_nonneg.mpr hba)
  simpa [mul_comm] using hpoint

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Pull back the `L²` negative part to the Hilbert space through the adjoint embedding. -/
def l2NegativePartPenalty (J : H →L[ℝ] Lp ℝ 2 μ) (u : H) : H :=
  (J†) (Lp.negPart (J u))

theorem l2NegativePartPenalty_antitone (J : H →L[ℝ] Lp ℝ 2 μ) (u v : H) :
    ⟪l2NegativePartPenalty J u - l2NegativePartPenalty J v, u - v⟫_ℝ ≤ 0 := by
  have hdiff : l2NegativePartPenalty J u - l2NegativePartPenalty J v =
      (J†) (Lp.negPart (J u) - Lp.negPart (J v)) := by
    simp [l2NegativePartPenalty, map_sub]
  rw [hdiff, ContinuousLinearMap.adjoint_inner_left]
  have hJ : J (u - v) = J u - J v := map_sub J u v
  rw [hJ]
  exact l2_negPart_antitone_inner (J u) (J v)

theorem l2NegativePartPenalty_lipschitz (J : H →L[ℝ] Lp ℝ 2 μ) (u v : H) :
    ‖l2NegativePartPenalty J u - l2NegativePartPenalty J v‖ ≤
      ‖J‖ ^ 2 * ‖u - v‖ := by
  have hdiff : l2NegativePartPenalty J u - l2NegativePartPenalty J v =
      (J†) (Lp.negPart (J u) - Lp.negPart (J v)) := by
    simp [l2NegativePartPenalty, map_sub]
  rw [hdiff]
  calc
    ‖(J†) (Lp.negPart (J u) - Lp.negPart (J v))‖
        ≤ ‖J†‖ * ‖Lp.negPart (J u) - Lp.negPart (J v)‖ := (J†).le_opNorm _
    _ ≤ ‖J†‖ * ‖J u - J v‖ := by
      exact mul_le_mul_of_nonneg_left (norm_l2_negPart_sub_le (J u) (J v)) (norm_nonneg _)
    _ ≤ ‖J‖ ^ 2 * ‖u - v‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map, ← map_sub]
      nlinarith [J.le_opNorm (u - v), norm_nonneg J,
        mul_le_mul_of_nonneg_left (J.le_opNorm (u - v)) (norm_nonneg J)]

/-- A coercive Dirichlet form admits a solution of the penalized weak obstacle equation.
The penalty is the `L²` negative part of the solution's value coordinate. -/
theorem exists_l2_negativePart_penalized_solution
    (B : H →L[ℝ] H →L[ℝ] ℝ) (hB : IsCoercive B)
    (J : H →L[ℝ] Lp ℝ 2 μ) (source : H →L[ℝ] ℝ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ u : H, ∀ v : H,
      B u v = source v + ε⁻¹ * ⟪Lp.negPart (J u), J v⟫_ℝ := by
  obtain ⟨α, hα, hcoerc⟩ := hB
  let A : H →L[ℝ] H := continuousLinearMapOfBilin B
  let g : H := (toDual ℝ H).symm source
  have hAmono : ∀ d : H, α * ‖d‖ ^ 2 ≤ ⟪A d, d⟫_ℝ := by
    intro d
    change α * ‖d‖ ^ 2 ≤ ⟪(continuousLinearMapOfBilin B) d, d⟫_ℝ
    rw [continuousLinearMapOfBilin_apply]
    nlinarith [hcoerc d]
  obtain ⟨u, hu⟩ := exists_penalized_solution A (l2NegativePartPenalty J) g
    hα hε hAmono (l2NegativePartPenalty_antitone J)
    (l2NegativePartPenalty_lipschitz J)
  refine ⟨u, fun v ↦ ?_⟩
  have hinner := congrArg (fun z : H ↦ ⟪z, v⟫_ℝ) hu
  dsimp [A, g] at hinner
  rw [inner_sub_left, real_inner_smul_left, continuousLinearMapOfBilin_apply,
    toDual_symm_apply] at hinner
  dsimp [l2NegativePartPenalty] at hinner
  rw [ContinuousLinearMap.adjoint_inner_left] at hinner
  linarith

end CenteredMaximal.Ball
