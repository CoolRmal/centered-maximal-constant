/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.L2PenaltyCap
public import CenteredMaximal.Ball.DirichletShiftedPart

/-!
# Uniform cap for the penalized ball obstacle

Testing the penalized weak equation with `(-u-εκ)⁺` controls the negative part. The
test lies in `H¹₀` and has exactly the negative gradient energy on its support.
-/

@[expose] public section

noncomputable section

open InnerProductSpace MeasureTheory Metric
open scoped RealInnerProductSpace NNReal ENNReal

namespace CenteredMaximal.Ball.DirichletSobolev

variable {n : ℕ}

/-- Every nonnegative-source penalized solution lies above `-εκ` almost everywhere. -/
theorem ball_penalized_solution_lower_bound
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : L2D (ball center R)) (κ ε : ℝ)
    (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hf : ∀ᵐ x ∂(volume.restrict (ball center R)), 0 ≤ f x)
    (U : H01 (ball center R))
    (hU : ∀ V : H01 (ball center R),
      laplaceBilin (ball center R) U V =
        l2Functional (ball center R) f V -
          κ * l2Functional (ball center R) (ballUnitL2 center R) V +
          ε⁻¹ * ⟪Lp.negPart (valueEmbedding (ball center R) U),
            valueEmbedding (ball center R) V⟫_ℝ) :
    ∀ᵐ x ∂(volume.restrict (ball center R)),
      -ε * κ ≤ (valueEmbedding (ball center R) U) x := by
  let D := ball center R
  let t : ℝ := ε * κ
  have ht : 0 ≤ t := mul_nonneg hε.le hκ
  obtain ⟨P, hP0, hPi⟩ := exists_shiftedPositivePartGraph (-U) t ht
  have hPvalue : ∀ᵐ x ∂(volume.restrict D),
      (valueEmbedding D P) x = max (-(valueEmbedding D U) x - t) 0 := by
    filter_upwards [hP0, Lp.coeFn_neg ((U : H1amb D) 0)] with x hp hn
    simpa only [valueEmbedding_apply, Submodule.coe_neg, PiLp.neg_apply,
      Pi.neg_apply, hn] using hp
  have hsource : 0 ≤
      ⟪f, valueEmbedding D P⟫_ℝ -
        κ * ⟪ballUnitL2 center R, valueEmbedding D P⟫_ℝ +
        ε⁻¹ * ⟪Lp.negPart (valueEmbedding D U), valueEmbedding D P⟫_ℝ :=
    l2_penalized_source_shifted_negPart_nonneg
      (valueEmbedding D U) f (valueEmbedding D P) (ballUnitL2 center R)
      κ ε hκ hε hf (ballUnitL2_coeFn center R) hPvalue
  have henergy := laplaceBilin_shiftedNegativePart_identity U P t hPi
  have hweak : laplaceBilin D U P =
      ⟪f, valueEmbedding D P⟫_ℝ -
        κ * ⟪ballUnitL2 center R, valueEmbedding D P⟫_ℝ +
        ε⁻¹ * ⟪Lp.negPart (valueEmbedding D U), valueEmbedding D P⟫_ℝ := by
    simpa only [l2Functional_apply, valueEmbedding_apply] using hU P
  have hPP : laplaceBilin D P P ≤ 0 := by
    rw [henergy] at hweak
    linarith
  obtain ⟨α, hα, hcoerc⟩ := laplaceBilin_coercive_ball center R
  have hPzero : P = 0 := by
    have hbound := hcoerc P
    have hnorm : ‖P‖ = 0 := by
      by_contra hz
      have hp : 0 < ‖P‖ := lt_of_le_of_ne (norm_nonneg P) (Ne.symm hz)
      have hpos := mul_pos (mul_pos hα hp) hp
      linarith
    exact norm_eq_zero.mp hnorm
  have hPae : ∀ᵐ x ∂(volume.restrict D), (valueEmbedding D P) x = 0 := by
    rw [hPzero, map_zero]
    exact Lp.coeFn_zero ℝ 2 (volume.restrict D)
  filter_upwards [hPvalue, hPae] with x hp hpzero
  have hp0 : max (-(valueEmbedding D U) x - t) 0 = 0 := by
    exact hp.symm.trans hpzero
  have hle := le_max_left (-(valueEmbedding D U) x - t) 0
  rw [hp0] at hle
  change -ε * κ ≤ (valueEmbedding D U) x
  dsimp [t] at hle
  linarith

/-- Existence of a penalized ball solution with a uniform pointwise cap on the
negative-part density. -/
theorem exists_ball_penalized_solution_capped
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : L2D (ball center R)) (κ ε : ℝ)
    (hκ : 0 ≤ κ) (hε : 0 < ε)
    (hf : ∀ᵐ x ∂(volume.restrict (ball center R)), 0 ≤ f x) :
    ∃ U : H01 (ball center R),
      (∀ V : H01 (ball center R),
        laplaceBilin (ball center R) U V =
          l2Functional (ball center R) f V -
            κ * l2Functional (ball center R) (ballUnitL2 center R) V +
            ε⁻¹ * ⟪Lp.negPart (valueEmbedding (ball center R) U),
              valueEmbedding (ball center R) V⟫_ℝ) ∧
      (∀ᵐ x ∂(volume.restrict (ball center R)),
        ε⁻¹ * (Lp.negPart (valueEmbedding (ball center R) U)) x ≤ κ) := by
  obtain ⟨U, hU⟩ := exists_ball_negativePart_penalized_solution center R f κ ε hε
  refine ⟨U, hU, ?_⟩
  have hbound := ball_penalized_solution_lower_bound center R f κ ε hκ hε hf U hU
  filter_upwards [hbound, Lp.coeFn_negPart_eq_max (valueEmbedding (ball center R) U)]
    with x hx hneg
  rw [hneg]
  have ht : 0 ≤ ε * κ := mul_nonneg hε.le hκ
  have hmax : max (-(valueEmbedding (ball center R) U) x) 0 ≤ ε * κ :=
    max_le (by linarith) ht
  have hεinv : 0 ≤ ε⁻¹ := (inv_pos.mpr hε).le
  have hmul := mul_le_mul_of_nonneg_left hmax hεinv
  have hcancel : ε⁻¹ * (ε * κ) = κ := by field_simp
  rw [hcancel] at hmul
  exact hmul

end CenteredMaximal.Ball.DirichletSobolev
