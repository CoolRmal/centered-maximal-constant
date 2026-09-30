/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.CompactSupportIBP
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth approximations to Euclidean ball indicators

The cutoff is identically one in a closed ball, vanishes beyond a slightly larger ball,
and is smooth even at its center because it uses the squared norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology

namespace CenteredMaximal.Ball

/-- A smooth cutoff which transitions from one to zero in the shell of width `δ`. -/
noncomputable def smoothBallCutoff (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (R δ : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.smoothTransition (((R + δ) ^ 2 - ‖y - x‖ ^ 2) / ((R + δ) ^ 2 - R ^ 2))

/-- The denominator in the cutoff formula is positive for positive radius and shell width. -/
theorem smoothBallCutoff_gap_pos {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    0 < (R + δ) ^ 2 - R ^ 2 := by
  nlinarith [mul_pos hR hδ, sq_pos_of_pos hδ]

/-- The squared-norm cutoff is twice continuously differentiable everywhere. -/
theorem smoothBallCutoff_contDiff (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (R δ : ℝ) :
    ContDiff ℝ 2 (smoothBallCutoff n x R δ) := by
  unfold smoothBallCutoff
  have hsub : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => y - x) := by
    fun_prop
  have hq : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ‖y - x‖ ^ 2) :=
    hsub.norm_sq ℝ
  have hinner : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) =>
      ((R + δ) ^ 2 - ‖y - x‖ ^ 2) / ((R + δ) ^ 2 - R ^ 2)) := by
    fun_prop
  exact Real.smoothTransition.contDiff.comp hinner

/-- The cutoff is one on the original closed ball. -/
theorem smoothBallCutoff_one (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hy : y ∈ closedBall x R) : smoothBallCutoff n x R δ y = 1 := by
  unfold smoothBallCutoff
  have hnorm : ‖y - x‖ ≤ R := by
    simpa only [mem_closedBall, dist_eq_norm] using hy
  have hsq : ‖y - x‖ ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hnorm
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (smoothBallCutoff_gap_pos hR hδ)).mpr
  nlinarith

/-- The cutoff vanishes outside the enlarged ball. -/
theorem smoothBallCutoff_zero (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hy : R + δ ≤ ‖y - x‖) : smoothBallCutoff n x R δ y = 0 := by
  unfold smoothBallCutoff
  have houter : 0 ≤ R + δ := by linarith
  have hsq : (R + δ) ^ 2 ≤ ‖y - x‖ ^ 2 :=
    (sq_le_sq₀ houter (norm_nonneg _)).mpr hy
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (smoothBallCutoff_gap_pos hR hδ).le

/-- The cutoff has compact support in the enlarged closed ball. -/
theorem smoothBallCutoff_hasCompactSupport (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    HasCompactSupport (smoothBallCutoff n x R δ) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x (R + δ))
  intro y hy
  by_contra hball
  have hnorm : R + δ ≤ ‖y - x‖ := by
    exact le_of_lt (by simpa only [mem_closedBall, dist_eq_norm, not_le] using hball)
  exact hy (smoothBallCutoff_zero n x y hR hδ hnorm)

/-- The directional derivative of the smooth ball cutoff. The derivative is radial and
contains no singular factor at the center. -/
theorem smoothBallCutoff_fderiv (n : ℕ)
    (x y v : EuclideanSpace ℝ (Fin n)) (R δ : ℝ) :
    fderiv ℝ (smoothBallCutoff n x R δ) y v =
      -(deriv Real.smoothTransition
        (((R + δ) ^ 2 - ‖y - x‖ ^ 2) / ((R + δ) ^ 2 - R ^ 2))) *
        (2 * inner ℝ (y - x) v) / ((R + δ) ^ 2 - R ^ 2) := by
  let gap : ℝ := (R + δ) ^ 2 - R ^ 2
  let q : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => ((R + δ) ^ 2 - ‖z - x‖ ^ 2) / gap
  have hsub : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => z - x)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
    (hasFDerivAt_id y).sub_const x
  have hsq := hsub.norm_sq
  have hnum := hsq.const_sub ((R + δ) ^ 2)
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    gap⁻¹ • (-(2 • ((innerSL ℝ (y - x)).comp
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))))))
  have hq : HasFDerivAt q L y := by
    simpa only [q, div_eq_mul_inv, mul_comm] using hnum.mul_const gap⁻¹
  have htrans : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (q y)) (q y) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ 1 Real.smoothTransition).differentiable
      (by norm_num) (q y)).hasDerivAt
  have h := (htrans.comp_hasFDerivAt y hq).fderiv
  have hs : fderiv ℝ (smoothBallCutoff n x R δ) y =
      (deriv Real.smoothTransition (q y)) •
        (gap⁻¹ • (-(2 • ((innerSL ℝ (y - x)).comp
          (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))))))) := by
    change fderiv ℝ (Real.smoothTransition ∘ q) y = _
    simpa only [L] using h
  rw [hs]
  simp only [smul_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, nsmul_eq_mul]
  change (deriv Real.smoothTransition (q y)) *
    (gap⁻¹ * (-(2 * inner ℝ (y - x) v))) = _
  ring

end CenteredMaximal.Ball
