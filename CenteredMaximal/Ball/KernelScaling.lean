/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.Comparison
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Mass of normalized Euclidean kernel dilates

The normalization in `kernelMaximal` divides by the volume of a ball of radius `r`. The mass of
each dilated kernel is consequently its mass divided by the volume of the unit ball, independent
of the center and radius. This applies to the singular Green kernels as well as bounded kernels.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace CenteredMaximal.Ball

variable {n : ℕ}

/-- Change of variables under scalar dilation in Euclidean space. -/
theorem lintegral_comp_smul_euclidean (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ z, K (r • z)) = ENNReal.ofReal ((r ^ n)⁻¹) * ∫⁻ z, K z := by
  have he : (∫⁻ z, K (r • z)) =
      ∫⁻ z, K z ∂(Measure.map (fun z : EuclideanSpace ℝ (Fin n) => r • z) volume) :=
    (lintegral_map_equiv K
      (Homeomorph.smul (isUnit_iff_ne_zero.2 hr.ne').unit).toMeasurableEquiv).symm
  rw [he, Measure.map_addHaar_smul volume hr.ne', lintegral_smul_measure]
  congr 2
  rw [finrank_euclideanSpace, Fintype.card_fin,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (r ^ n)⁻¹)]

/-- Translation and reflection do not change the mass of a kernel. -/
theorem lintegral_comp_sub_euclidean (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫⁻ y, K (x - y)) = ∫⁻ z, K z := by
  calc
    (∫⁻ y, K (x - y)) = ∫⁻ z, K (x + z) := by
      simpa only [sub_eq_add_neg] using
        (lintegral_neg_eq_self (fun z : EuclideanSpace ℝ (Fin n) => K (x + z)))
    _ = ∫⁻ z, K z := lintegral_add_left_eq_self K x

/-- The mass of a translated, scaled Euclidean kernel. -/
theorem lintegral_comp_inv_smul_sub_euclidean
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ y, K (r⁻¹ • (x - y))) = ENNReal.ofReal (r ^ n) * ∫⁻ z, K z := by
  rw [lintegral_comp_sub_euclidean (fun z => K (r⁻¹ • z)) x,
    lintegral_comp_smul_euclidean K (inv_pos.mpr hr), inv_pow, inv_inv]

/-- Euclidean ball volume scales by the `n`th power of the radius. -/
theorem volume_ball_eq_radius_pow_mul_unit (n : ℕ) (hn : 0 < n)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 ≤ r) :
    volume (ball x r) = ENNReal.ofReal (r ^ n) *
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  rw [EuclideanSpace.volume_ball, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
  rw [ENNReal.ofReal_pow hr]

/-- The mass of a normalized Euclidean kernel is independent of its center and radius. -/
theorem lintegral_normalized_kernel_eq_unit_mass (n : ℕ) (hn : 0 < n)
    (K : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))) =
      (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * ∫⁻ z, K z := by
  have hvol0 : volume (ball x r) ≠ 0 := (measure_ball_pos volume x hr).ne'
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.mpr hvol0),
    lintegral_comp_inv_smul_sub_euclidean K x hr,
    volume_ball_eq_radius_pow_mul_unit n hn x hr.le]
  have ha0 : ENNReal.ofReal (r ^ n) ≠ 0 := by positivity
  have hat : ENNReal.ofReal (r ^ n) ≠ ∞ := ENNReal.ofReal_ne_top
  rw [ENNReal.mul_inv (Or.inl ha0) (Or.inl hat)]
  calc
    (ENNReal.ofReal (r ^ n))⁻¹ *
        (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        (ENNReal.ofReal (r ^ n) * ∫⁻ z, K z) =
        ((ENNReal.ofReal (r ^ n))⁻¹ * ENNReal.ofReal (r ^ n)) *
          ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ * ∫⁻ z, K z) := by
            ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel ha0 hat, one_mul]

end CenteredMaximal.Ball
