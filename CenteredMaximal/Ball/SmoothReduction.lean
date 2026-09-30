/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.Basic
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Smooth reduction for the centred ball maximal operator

Nonnegative smooth compactly supported functions are dense in the nonnegative cone of `L¹`.
The key construction approximates the square root of a nonnegative function in `L²` and then
squares the smooth approximant.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal NNReal ContDiff

namespace CenteredMaximal.Ball

variable {d : ℕ}

private theorem memLp_sqrt_abs_of_integrable
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Integrable f) :
    MemLp (fun x ↦ Real.sqrt |f x|) 2
      (volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  have h := (memLp_one_iff_integrable.mpr hf).norm_rpow_div (1 / 2 : ℝ≥0∞)
  convert h using 1
  · ext x
    simp only [Real.norm_eq_abs, ENNReal.toReal_div]
    rw [Real.sqrt_eq_rpow]
    norm_num
  · norm_num

private theorem eLpNorm_square_sub_square_le
    {u g : EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : MemLp u 2 (volume : Measure (EuclideanSpace ℝ (Fin d))))
    (hg : MemLp g 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    eLpNorm (fun x ↦ u x ^ 2 - g x ^ 2) 1 volume ≤
      eLpNorm (u - g) 2 volume * eLpNorm (u + g) 2 volume := by
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
    (hu.aestronglyMeasurable.sub hg.aestronglyMeasurable)
    (hu.aestronglyMeasurable.add hg.aestronglyMeasurable)
    (fun a b : ℝ ↦ a * b) 1
    (Filter.Eventually.of_forall fun x ↦ by simp [nnnorm_mul])
    (p := 2) (q := 2) (r := 1)
  convert h using 1
  · congr 1
    ext x
    dsimp
    ring
  · simp

/-- Nonnegative smooth compactly supported functions approximate the absolute value of an
integrable function in `L¹`. -/
theorem exists_smooth_nonneg_approx
    {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Integrable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : EuclideanSpace ℝ (Fin d) → ℝ,
      HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ (∀ x, 0 ≤ g x) ∧
        eLpNorm ((fun x ↦ |f x|) - g) 1 volume < ENNReal.ofReal ε := by
  let u : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦ Real.sqrt |f x|
  have hu : MemLp u 2 volume := memLp_sqrt_abs_of_integrable hf
  let U : ℝ≥0∞ := eLpNorm u 2 volume
  have hU : U ≠ (⊤ : ℝ≥0∞) := hu.2.ne
  have hA : 2 * U + 1 ≠ (⊤ : ℝ≥0∞) := by finiteness
  have hε₀ : ENNReal.ofReal ε ≠ 0 := by positivity
  obtain ⟨δ, hδ₀, hδ⟩ := ENNReal.exists_nnreal_pos_mul_lt hA hε₀
  let η : ℝ≥0 := min δ (1 : ℝ≥0)
  have hη₀ : 0 < η := lt_min hδ₀ zero_lt_one
  have hη₁ : (η : ℝ≥0∞) ≤ 1 := by exact_mod_cast min_le_right δ 1
  have hηδ : (η : ℝ≥0∞) ≤ δ := by exact_mod_cast min_le_left δ 1
  obtain ⟨v, hvcompact, hvsmooth, hvclose⟩ :=
    hu.exist_eLpNorm_sub_le (by simp) (by norm_num) (show (0 : ℝ) < η from hη₀)
  have hvclose' : eLpNorm (u - v) 2 volume ≤ (η : ℝ≥0∞) := by
    simpa using hvclose
  have hv : MemLp v 2 volume := hvsmooth.continuous.memLp_of_hasCompactSupport hvcompact
  let g : EuclideanSpace ℝ (Fin d) → ℝ := fun x ↦ v x ^ 2
  have hgcompact : HasCompactSupport g := by
    apply hvcompact.mono
    intro x hx
    by_contra hvx
    have hvx' : v x = 0 := by simpa [Function.mem_support] using hvx
    simp [g, hvx'] at hx
  have hgsmooth : ContDiff ℝ ∞ g := hvsmooth.pow 2
  have hgnonneg : ∀ x, 0 ≤ g x := fun x ↦ sq_nonneg _
  refine ⟨g, hgcompact, hgsmooth, hgnonneg, ?_⟩
  have hsq : (fun x ↦ |f x|) = fun x ↦ u x ^ 2 := by
    funext x
    exact (Real.sq_sqrt (abs_nonneg (f x))).symm
  rw [hsq]
  have hvnorm : eLpNorm v 2 volume ≤ U + (η : ℝ≥0∞) := by
    calc
      eLpNorm v 2 volume = eLpNorm ((v - u) + u) 2 volume := by simp
      _ ≤ eLpNorm (v - u) 2 volume + eLpNorm u 2 volume :=
        eLpNorm_add_le (hv.aestronglyMeasurable.sub hu.aestronglyMeasurable)
          hu.aestronglyMeasurable (by norm_num)
      _ ≤ U + (η : ℝ≥0∞) := by
        rw [eLpNorm_sub_comm]
        calc
          eLpNorm (u - v) 2 volume + eLpNorm u 2 volume ≤
              (η : ℝ≥0∞) + U := add_le_add_left hvclose' _
          _ = U + (η : ℝ≥0∞) := add_comm _ _
  have hsum : eLpNorm (u + v) 2 volume ≤ 2 * U + (η : ℝ≥0∞) := by
    calc
      _ ≤ eLpNorm u 2 volume + eLpNorm v 2 volume :=
        eLpNorm_add_le hu.aestronglyMeasurable hv.aestronglyMeasurable (by norm_num)
      _ ≤ 2 * U + (η : ℝ≥0∞) := by
        calc
          eLpNorm u 2 volume + eLpNorm v 2 volume ≤ U + (U + (η : ℝ≥0∞)) :=
            add_le_add_right hvnorm U
          _ = 2 * U + (η : ℝ≥0∞) := by rw [two_mul, add_assoc]
  calc
    eLpNorm (fun x ↦ u x ^ 2 - v x ^ 2) 1 volume
        ≤ eLpNorm (u - v) 2 volume * eLpNorm (u + v) 2 volume :=
          eLpNorm_square_sub_square_le hu hv
    _ ≤ (η : ℝ≥0∞) * (2 * U + η) := by gcongr
    _ ≤ (η : ℝ≥0∞) * (2 * U + 1) := by gcongr
    _ ≤ (δ : ℝ≥0∞) * (2 * U + 1) := by gcongr
    _ < ENNReal.ofReal ε := hδ

end CenteredMaximal.Ball
