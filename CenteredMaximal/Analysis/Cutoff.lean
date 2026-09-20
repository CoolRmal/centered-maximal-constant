/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.BoundedFunctional
public import CenteredMaximal.Analysis.JumpGenerator
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Integral.Lebesgue.Norm

/-!
# Smooth cutoffs exhausting the plane

On `ℝ² = Fin 2 → ℝ` with the sup norm `‖x‖ = max |x 0| |x 1|` we build a family of test
functions `cutoff l` (`l > 0`) equal to `1` on the ball of radius `l`, vanishing outside the ball
of radius `2 l`, with values in `[0, 1]`, whose Cauchy jump generators tend to zero uniformly at
the rate `1 / l`. The family is a dilate `cutoff l x = cutoffBase (l⁻¹ • x)` of a single base
cutoff, which is the product `b (x 0) * b (x 1)` of a one-dimensional `ContDiffBump` `b` with
inner radius `1` and outer radius `2`.

## Main results

* `isTestFunction_cutoffBase`, `cutoffBase_nonneg`, `cutoffBase_le_one`, `cutoffBase_eq_one`,
  `cutoffBase_eq_zero`: the base cutoff is a test function with values in `[0, 1]`, equal to `1`
  on `{‖x‖ ≤ 1}` and vanishing on `{2 ≤ ‖x‖}`;
* `isTestFunction_cutoff`, `cutoff_nonneg`, `cutoff_le_one`, `cutoff_eq_one_of_norm_le`,
  `cutoff_eq_zero_of_le`: the same properties for the dilates, at scales `l` and `2 l`;
* `exists_abs_jumpGen_cutoff_le`: the uniform decay `|jumpGen 1 (cutoff l) x| ≤ C / l` with a
  constant `C` independent of `l > 0` and `x`, from the scaling law
  `JumpGenerator.jumpGen_comp_smul_inv` together with the uniform bound `abs_jumpGen_le`;
  `tendsto_abs_jumpGen_cutoff` restates it for `l ≥ 1`;
* `lintegral_le_of_setLIntegral_le`, `integrable_of_setLIntegral_le`,
  `integral_le_of_setLIntegral_le`: a monotone-limit lemma, unrelated to the cutoffs, letting a
  bound for the integrals of a nonnegative function over all the balls `closedBall 0 n`, `n : ℕ`,
  be passed to the integral over the whole plane.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace CenteredMaximal

/-! ### The sup norm on the plane -/

/-- The sup norm on `ℝ²`: `‖x‖ = max |x 0| |x 1|`. -/
theorem norm_fin_two_eq_max (x : Fin 2 → ℝ) : ‖x‖ = max |x 0| |x 1| := by
  refine le_antisymm ?_ (max_le (by simpa using norm_le_pi_norm x 0)
    (by simpa using norm_le_pi_norm x 1))
  rw [pi_norm_le_iff_of_nonneg (by positivity), Fin.forall_fin_two]
  exact ⟨by simp, by simp⟩

/-! ### The base cutoff -/

/-- The one-dimensional smooth bump used to build the cutoffs: it equals `1` on `[-1, 1]` and
vanishes outside `(-2, 2)`. -/
def cutoffBump : ContDiffBump (0 : ℝ) where
  rIn := 1
  rOut := 2
  rIn_pos := one_pos
  rIn_lt_rOut := one_lt_two

/-- The base cutoff on the plane: the product of the one-dimensional bump `cutoffBump` in each
coordinate. It equals `1` on the closed unit ball of the sup norm and vanishes outside the ball
of radius `2`. -/
def cutoffBase (x : Fin 2 → ℝ) : ℝ := cutoffBump (x 0) * cutoffBump (x 1)

/-- The base cutoff is nonnegative. -/
theorem cutoffBase_nonneg (x : Fin 2 → ℝ) : 0 ≤ cutoffBase x :=
  mul_nonneg cutoffBump.nonneg cutoffBump.nonneg

/-- The base cutoff is at most `1`. -/
theorem cutoffBase_le_one (x : Fin 2 → ℝ) : cutoffBase x ≤ 1 := by
  have h := mul_le_mul (cutoffBump.le_one (x := x 0)) (cutoffBump.le_one (x := x 1))
    cutoffBump.nonneg zero_le_one
  simpa [cutoffBase] using h

/-- The base cutoff equals `1` on the closed unit ball of the sup norm. -/
theorem cutoffBase_eq_one {x : Fin 2 → ℝ} (hx : ‖x‖ ≤ 1) : cutoffBase x = 1 := by
  have key : ∀ j : Fin 2, cutoffBump (x j) = 1 := fun j =>
    cutoffBump.one_of_mem_closedBall (by
      have hj : |x j| ≤ ‖x‖ := by simpa using norm_le_pi_norm x j
      simpa [cutoffBump, Real.dist_eq] using hj.trans hx)
  simp [cutoffBase, key 0, key 1]

/-- The base cutoff vanishes outside the ball of radius `2`: a product vanishes as soon as one of
its factors does, and `2 ≤ ‖x‖` forces `2 ≤ |x j|` for some coordinate `j`. -/
theorem cutoffBase_eq_zero {x : Fin 2 → ℝ} (hx : 2 ≤ ‖x‖) : cutoffBase x = 0 := by
  have key : ∀ j : Fin 2, 2 ≤ |x j| → cutoffBump (x j) = 0 := fun j hj =>
    cutoffBump.zero_of_le_dist (by simpa [cutoffBump, Real.dist_eq] using hj)
  rw [norm_fin_two_eq_max, le_max_iff] at hx
  rcases hx with h | h
  · simp [cutoffBase, key 0 h]
  · simp [cutoffBase, key 1 h]

/-- The base cutoff is a test function: it is smooth as a product of compositions of the bump
with the coordinate projections, and supported in the closed ball of radius `2`. -/
theorem isTestFunction_cutoffBase : IsTestFunction cutoffBase := by
  refine ⟨(cutoffBump.contDiff.comp (contDiff_apply ℝ ℝ 0)).mul
    (cutoffBump.contDiff.comp (contDiff_apply ℝ ℝ 1)), ?_⟩
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 2 → ℝ) 2) fun x hx => ?_
  refine cutoffBase_eq_zero (le_of_lt ?_)
  simpa [mem_closedBall, dist_zero_right] using hx

/-! ### The family of cutoffs -/

/-- The cutoff at scale `l`: the dilate `x ↦ cutoffBase (l⁻¹ • x)` of the base cutoff, written in
this shape so that `jumpGen_comp_smul_inv` applies to it verbatim. -/
def cutoff (l : ℝ) (x : Fin 2 → ℝ) : ℝ := cutoffBase (l⁻¹ • x)

/-- The cutoff at scale `l` is literally the dilate `cutoffBase (l⁻¹ • ·)`. -/
theorem cutoff_eq (l : ℝ) : cutoff l = fun y : Fin 2 → ℝ => cutoffBase (l⁻¹ • y) := rfl

/-- The sup norm of a positive dilate. -/
theorem norm_inv_smul {l : ℝ} (hl : 0 < l) (x : Fin 2 → ℝ) : ‖l⁻¹ • x‖ = l⁻¹ * ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hl)]

/-- The cutoffs are nonnegative. -/
theorem cutoff_nonneg (l : ℝ) (x : Fin 2 → ℝ) : 0 ≤ cutoff l x := cutoffBase_nonneg _

/-- The cutoffs are at most `1`. -/
theorem cutoff_le_one (l : ℝ) (x : Fin 2 → ℝ) : cutoff l x ≤ 1 := cutoffBase_le_one _

/-- The cutoff at scale `l` equals `1` on the closed ball of radius `l`. -/
theorem cutoff_eq_one_of_norm_le {l : ℝ} (hl : 0 < l) {x : Fin 2 → ℝ} (hx : ‖x‖ ≤ l) :
    cutoff l x = 1 := by
  refine cutoffBase_eq_one ?_
  rw [norm_inv_smul hl]
  calc l⁻¹ * ‖x‖ ≤ l⁻¹ * l := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hl.le)
    _ = 1 := inv_mul_cancel₀ hl.ne'

/-- The cutoff at scale `l` vanishes outside the ball of radius `2 l`. -/
theorem cutoff_eq_zero_of_le {l : ℝ} (hl : 0 < l) {x : Fin 2 → ℝ} (hx : 2 * l ≤ ‖x‖) :
    cutoff l x = 0 := by
  refine cutoffBase_eq_zero ?_
  rw [norm_inv_smul hl]
  calc (2 : ℝ) = l⁻¹ * (2 * l) := by field_simp
    _ ≤ l⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left hx (inv_nonneg.2 hl.le)

/-- Each cutoff is a test function, supported in the closed ball of radius `2 l`. -/
theorem isTestFunction_cutoff {l : ℝ} (hl : 0 < l) : IsTestFunction (cutoff l) := by
  refine ⟨isTestFunction_cutoffBase.1.comp (contDiff_id.const_smul l⁻¹), ?_⟩
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 2 → ℝ) (2 * l)) fun x hx => ?_
  refine cutoff_eq_zero_of_le hl (le_of_lt ?_)
  simpa [mem_closedBall, dist_zero_right] using hx

/-! ### Uniform decay of the jump generators -/

/-- The uniform decay of the jump generators of the cutoffs: there is a constant `C ≥ 0` with
`|jumpGen 1 (cutoff l) x| ≤ C / l` for every `l > 0` and every `x`.

The scaling law `jumpGen_comp_smul_inv` turns the generator of `cutoff l` into
`l^{-1}` times the generator of `cutoffBase` at `l⁻¹ • x`, and `abs_jumpGen_le` bounds the latter
uniformly in terms of bounds for `cutoffBase` and its second derivative, which exist because
`cutoffBase` is smooth with compact support. -/
theorem exists_abs_jumpGen_cutoff_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℝ, 0 < l → ∀ x, |jumpGen 1 (cutoff l) x| ≤ C / l := by
  have hC2 : ContDiff ℝ 2 cutoffBase := isTestFunction_cutoffBase.1.of_le (by norm_cast)
  obtain ⟨M₀, M₂, h₀, h₂⟩ := exists_bounds_of_hasCompactSupport hC2 isTestFunction_cutoffBase.2
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ 0)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h₂ 0)
  refine ⟨2 * (2 * M₂ / (2 - 1) + 8 * M₀ / 1), ?_, fun l hl x => ?_⟩
  · have h21 : (2 : ℝ) - 1 = 1 := by norm_num
    rw [h21, div_one, div_one]
    linarith
  · have h := abs_jumpGen_comp_smul_inv_le (α := 1) one_pos one_lt_two hC2 h₀ h₂ hl x
    rw [Real.rpow_neg_one, ← div_eq_inv_mul] at h
    rw [cutoff_eq]
    exact h

/-- The uniform decay of `exists_abs_jumpGen_cutoff_le`, restated for `l ≥ 1`. -/
theorem tendsto_abs_jumpGen_cutoff :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l : ℝ, 1 ≤ l → ∀ x, |jumpGen 1 (cutoff l) x| ≤ C / l :=
  let ⟨C, hC, h⟩ := exists_abs_jumpGen_cutoff_le
  ⟨C, hC, fun l hl x => h l (one_pos.trans_le hl) x⟩

/-! ### A monotone-limit lemma for lower integrals -/

/-- If the lower integrals of `ENNReal.ofReal ∘ g` over all the balls `closedBall 0 n`, `n : ℕ`,
are at most `ENNReal.ofReal a`, then so is the lower integral over the whole plane.

The indicators of the balls increase to the constant function `1`, so monotone convergence
(`lintegral_iSup`) identifies the integral over the plane with the supremum of the integrals over
the balls. -/
theorem lintegral_le_of_setLIntegral_le {g : (Fin 2 → ℝ) → ℝ} (hg : Measurable g) {a : ℝ}
    (h : ∀ n : ℕ, (∫⁻ x in closedBall 0 (n : ℝ), ENNReal.ofReal (g x)) ≤ ENNReal.ofReal a) :
    (∫⁻ x, ENNReal.ofReal (g x)) ≤ ENNReal.ofReal a := by
  have hmeas : ∀ n : ℕ, Measurable ((closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
      fun x => ENNReal.ofReal (g x)) := fun n =>
    hg.ennreal_ofReal.indicator measurableSet_closedBall
  have hmono : Monotone fun n : ℕ => (closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
      fun x => ENNReal.ofReal (g x) := fun m n hmn x =>
    indicator_le_indicator_of_subset
      (closedBall_subset_closedBall (by exact_mod_cast hmn)) (fun _ => zero_le) x
  have hsup : ∀ x, ⨆ n : ℕ, (closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
      (fun y => ENNReal.ofReal (g y)) x = ENNReal.ofReal (g x) := fun x => by
    refine le_antisymm (iSup_le fun n =>
      indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le) ?_
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    have hmem : x ∈ closedBall (0 : Fin 2 → ℝ) (N : ℝ) := by
      simpa [mem_closedBall, dist_zero_right] using hN
    exact le_iSup_of_le N
      (le_of_eq (indicator_of_mem hmem fun y => ENNReal.ofReal (g y)).symm)
  calc (∫⁻ x, ENNReal.ofReal (g x))
      = ∫⁻ x, ⨆ n : ℕ, (closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
          (fun y => ENNReal.ofReal (g y)) x := by simp_rw [hsup]
    _ = ⨆ n : ℕ, ∫⁻ x, (closedBall (0 : Fin 2 → ℝ) (n : ℝ)).indicator
          (fun y => ENNReal.ofReal (g y)) x := lintegral_iSup hmeas hmono
    _ ≤ ENNReal.ofReal a := iSup_le fun n => by
        rw [lintegral_indicator measurableSet_closedBall]
        exact h n

/-- A nonnegative measurable function whose integrals over all the balls `closedBall 0 n`,
`n : ℕ`, are bounded by `ENNReal.ofReal a` is integrable. -/
theorem integrable_of_setLIntegral_le {g : (Fin 2 → ℝ) → ℝ} (hg : Measurable g)
    (hg₀ : 0 ≤ᵐ[volume] g) {a : ℝ}
    (h : ∀ n : ℕ, (∫⁻ x in closedBall 0 (n : ℝ), ENNReal.ofReal (g x)) ≤ ENNReal.ofReal a) :
    Integrable g := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal hg₀]
  exact (lintegral_le_of_setLIntegral_le hg h).trans_lt ENNReal.ofReal_lt_top

/-- The Bochner integral of a nonnegative measurable function is at most `a ≥ 0` as soon as its
integrals over all the balls `closedBall 0 n`, `n : ℕ`, are at most `ENNReal.ofReal a`. -/
theorem integral_le_of_setLIntegral_le {g : (Fin 2 → ℝ) → ℝ} (hg : Measurable g)
    (hg₀ : 0 ≤ᵐ[volume] g) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ n : ℕ, (∫⁻ x in closedBall 0 (n : ℝ), ENNReal.ofReal (g x)) ≤ ENNReal.ofReal a) :
    ∫ x, g x ≤ a := by
  rw [integral_eq_lintegral_of_nonneg_ae hg₀ hg.aestronglyMeasurable]
  calc (∫⁻ x, ENNReal.ofReal (g x)).toReal ≤ (ENNReal.ofReal a).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top (lintegral_le_of_setLIntegral_le hg h)
    _ = a := ENNReal.toReal_ofReal ha

end CenteredMaximal

end
