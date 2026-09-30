/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.GreenKernel
public import CenteredMaximal.Ball.KernelScaling
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Mass of the Newtonian comparison kernel

In dimension at least three, layer cake gives the mass of the truncated Newtonian kernel as
the volume of its support ball. Its volume relative to the unit ball is `greenBound n`.
-/

@[expose] public section

open MeasureTheory Metric Set Filter
open scoped ENNReal

noncomputable section

namespace CenteredMaximal.Ball

private def newtonianRealKernel (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max (((n : ℝ) * ‖z‖ ^ ((2 : ℝ) - (n : ℝ)) - 2) / ((n : ℝ) - 2)) 0

private def levelRadius (n : ℕ) (t : ℝ) : ℝ :=
  ((n : ℝ) / (2 + ((n : ℝ) - 2) * t)) ^ (((n : ℝ) - 2)⁻¹)

private theorem level_set (n : ℕ) (hn : 3 ≤ n) (t : ℝ) (ht : 0 < t) :
    volume {z : EuclideanSpace ℝ (Fin n) | t < newtonianRealKernel n z} =
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) (levelRadius n t)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  apply measure_congr
  filter_upwards [(volume : Measure (EuclideanSpace ℝ (Fin n))).ae_ne 0] with z hz
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 2 := by linarith
  have hden : 0 < 2 + ((n : ℝ) - 2) * t := by positivity
  have hbase : 0 < (n : ℝ) / (2 + ((n : ℝ) - 2) * t) := by positivity
  have hnorm : 0 ≤ ‖z‖ := norm_nonneg _
  change (t < newtonianRealKernel n z) = (z ∈ ball _ (levelRadius n t))
  apply propext
  simp only [newtonianRealKernel, lt_max_iff, not_lt.mpr ht.le, or_false,
    mem_ball_zero_iff, levelRadius]
  have hnorm₀ : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [lt_div_iff₀ hd]
  have hpow : ‖z‖ ^ ((2 : ℝ) - (n : ℝ)) =
      (‖z‖ ^ ((n : ℝ) - 2))⁻¹ := by
    rw [show (2 : ℝ) - (n : ℝ) = -((n : ℝ) - 2) by ring]
    exact Real.rpow_neg hnorm₀.le _
  rw [hpow]
  have hpowpos : 0 < ‖z‖ ^ ((n : ℝ) - 2) := Real.rpow_pos_of_pos hnorm₀ _
  constructor
  · intro h
    apply (Real.lt_rpow_inv_iff_of_pos hnorm hbase.le hd).2
    apply (lt_div_iff₀ hden).2
    have h' : 2 + ((n : ℝ) - 2) * t <
        (n : ℝ) / (‖z‖ ^ ((n : ℝ) - 2)) := by
      rw [div_eq_mul_inv]
      linarith
    nlinarith [(lt_div_iff₀ hpowpos).1 h']
  · intro h
    have h' : ‖z‖ ^ ((n : ℝ) - 2) <
        (n : ℝ) / (2 + ((n : ℝ) - 2) * t) :=
      (Real.lt_rpow_inv_iff_of_pos hnorm hbase.le hd).1 h
    have h'' := (lt_div_iff₀ hden).1 h'
    have h''' : 2 + ((n : ℝ) - 2) * t <
        (n : ℝ) / (‖z‖ ^ ((n : ℝ) - 2)) :=
      (lt_div_iff₀ hpowpos).2 (by nlinarith)
    rw [div_eq_mul_inv] at h'''
    linarith

private theorem lintegral_scale_power (n : ℕ) (hn : 3 ≤ n) :
    (∫⁻ t in Ioi (0 : ℝ),
      ENNReal.ofReal ((1 + (((n : ℝ) - 2) / 2) * t) ^
        (-(n : ℝ) / ((n : ℝ) - 2)))) = 1 := by
  let a : ℝ := ((n : ℝ) - 2) / 2
  let q : ℝ := 2 / ((n : ℝ) - 2)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 2 := by linarith
  have ha : 0 < a := by dsimp [a]; positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have haq : a * q = 1 := by dsimp [a, q]; field_simp
  have hexp : -q - 1 = -(n : ℝ) / ((n : ℝ) - 2) := by
    dsimp [q]
    field_simp
    ring
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ ↦ -(1 + a * t) ^ (-q))
        ((1 + a * t) ^ (-q - 1)) t := by
    intro t ht
    have hbase : 0 < 1 + a * t := by
      have ht' : 0 ≤ t := mem_Ici.mp ht
      positivity
    have hinner : HasDerivAt (fun s : ℝ ↦ 1 + a * s) a t := by
      convert! ((hasDerivAt_id t).const_mul a).const_add 1 using 1
      simp only [mul_one]
    have hpow : HasDerivAt (fun s : ℝ ↦ (1 + a * s) ^ (-q))
        (a * (-q) * (1 + a * t) ^ (-q - 1)) t := by
      simpa only using hinner.rpow_const (p := -q) (Or.inl hbase.ne')
    convert! hpow.neg using 1
    simp only [mul_neg, neg_mul, neg_neg, haq, one_mul]
  have hlim : Tendsto (fun t : ℝ ↦ -(1 + a * t) ^ (-q)) atTop
      (nhds (0 : ℝ)) := by
    have hbase : Tendsto (fun t : ℝ ↦ 1 + a * t) atTop atTop := by
      simpa only [id_eq, mul_comm] using tendsto_atTop_add_const_left _ 1
        (Filter.Tendsto.atTop_mul_const ha tendsto_id)
    have hpow : Tendsto (fun t : ℝ ↦ (1 + a * t) ^ (-q)) atTop (nhds (0 : ℝ)) :=
      (tendsto_rpow_neg_atTop hq).comp hbase
    simpa using hpow.neg
  have hnonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ (1 + a * t) ^ (-q - 1) := by
    intro t ht
    have ht' : 0 < t := mem_Ioi.mp ht
    exact Real.rpow_nonneg (by positivity) _
  have hint : IntegrableOn (fun t : ℝ ↦ (1 + a * t) ^ (-q - 1)) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonneg' hderiv hnonneg hlim
  have hreal : (∫ t in Ioi (0 : ℝ), (1 + a * t) ^ (-q - 1)) = 1 := by
    rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
    simp
  have hae : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun t : ℝ ↦ (1 + a * t) ^ (-q - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hnonneg t ht
  have hlin :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((1 + a * t) ^ (-q - 1))) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint hae, hreal]
    norm_num
  simpa only [a, hexp] using hlin

private theorem levelRadius_pow (n : ℕ) (hn : 3 ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    (levelRadius n t) ^ n =
      greenBound n *
        (1 + (((n : ℝ) - 2) / 2) * t) ^ (-(n : ℝ) / ((n : ℝ) - 2)) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 2 := by linarith
  have hbase : 0 < 1 + (((n : ℝ) - 2) / 2) * t := by positivity
  have hden : 0 < 2 + ((n : ℝ) - 2) * t := by positivity
  have hratio : (n : ℝ) / (2 + ((n : ℝ) - 2) * t) =
      ((n : ℝ) / 2) * (1 + (((n : ℝ) - 2) / 2) * t)⁻¹ := by
    field_simp
  have hq : 0 ≤ (n : ℝ) / 2 := by positivity
  have hpowbase : 0 ≤ (n : ℝ) / (2 + ((n : ℝ) - 2) * t) := by positivity
  unfold levelRadius greenBound
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpowbase]
  have hexp : (((n : ℝ) - 2)⁻¹ * (n : ℝ)) =
      (n : ℝ) / ((n : ℝ) - 2) := by ring
  rw [hexp, hratio, Real.mul_rpow hq (inv_nonneg.mpr hbase.le)]
  rw [Real.inv_rpow hbase.le]
  rw [← Real.rpow_neg hbase.le]
  congr 1
  ring_nf

private theorem level_measure_scaled (n : ℕ) (hn : 3 ≤ n) (t : ℝ) (ht : 0 < t) :
    volume {z : EuclideanSpace ℝ (Fin n) | t < newtonianRealKernel n z} =
      ENNReal.ofReal
        ((1 + (((n : ℝ) - 2) / 2) * t) ^ (-(n : ℝ) / ((n : ℝ) - 2))) *
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) (greenRadius n)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 2 := by linarith
  have hbase : 0 < 1 + (((n : ℝ) - 2) / 2) * t := by positivity
  have hr : 0 ≤ levelRadius n t := by unfold levelRadius; positivity
  have hR : 0 ≤ greenRadius n := (greenRadius_pos n hn).le
  rw [level_set n hn t ht]
  simp only [EuclideanSpace.volume_ball, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_pow hR]
  rw [levelRadius_pow n hn t ht.le]
  rw [ENNReal.ofReal_mul (by unfold greenBound; positivity : 0 ≤ greenBound n)]
  have hRpow : greenRadius n ^ n = greenBound n := by
    simpa only [Real.rpow_natCast] using greenRadius_rpow_dim n hn
  rw [hRpow]
  ac_rfl

/-- The truncated Newtonian kernel has exactly the mass of its support ball. -/
theorem newtonianKernel_mass (n : ℕ) (hn : 3 ≤ n) :
    (∫⁻ z : EuclideanSpace ℝ (Fin n), newtonianKernel n z) =
      volume (ball (0 : EuclideanSpace ℝ (Fin n)) (greenRadius n)) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hAE : ∀ᵐ z ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      newtonianKernel n z = ENNReal.ofReal (newtonianRealKernel n z) := by
    filter_upwards [(volume : Measure (EuclideanSpace ℝ (Fin n))).ae_ne 0] with z hz
    simp [newtonianKernel, newtonianRealKernel, hz, ENNReal.ofReal_max]
  rw [lintegral_congr_ae hAE]
  have hnonneg : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin n)))]
      newtonianRealKernel n :=
    Filter.Eventually.of_forall fun z ↦ le_max_right _ _
  have hmeas : AEMeasurable (newtonianRealKernel n)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    unfold newtonianRealKernel
    fun_prop
  rw [lintegral_eq_lintegral_meas_lt volume hnonneg hmeas]
  calc
    (∫⁻ t in Ioi (0 : ℝ),
      volume {z : EuclideanSpace ℝ (Fin n) | t < newtonianRealKernel n z}) =
        ∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal
            ((1 + (((n : ℝ) - 2) / 2) * t) ^ (-(n : ℝ) / ((n : ℝ) - 2))) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) (greenRadius n)) := by
        refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
        exact level_measure_scaled n hn t ht
    _ = (∫⁻ t in Ioi (0 : ℝ),
          ENNReal.ofReal
            ((1 + (((n : ℝ) - 2) / 2) * t) ^ (-(n : ℝ) / ((n : ℝ) - 2)))) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) (greenRadius n)) := by
        rw [lintegral_mul_const]
        fun_prop
    _ = _ := by rw [lintegral_scale_power n hn, one_mul]

/-- The mass of the Newtonian kernel is `greenBound n` times the unit-ball volume. -/
theorem newtonianKernel_mass_eq_greenBound_mul_unitBall (n : ℕ) (hn : 3 ≤ n) :
    (∫⁻ z : EuclideanSpace ℝ (Fin n), newtonianKernel n z) =
      ENNReal.ofReal (greenBound n) *
        volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  rw [newtonianKernel_mass n hn]
  simpa only [mul_one] using volume_ball_greenRadius_mul n hn
    (0 : EuclideanSpace ℝ (Fin n)) 1

/-- Every normalized dilate of the Newtonian kernel has mass `greenBound n`. -/
theorem lintegral_normalized_newtonianKernel (n : ℕ) (hn : 3 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y, (volume (ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))) =
      ENNReal.ofReal (greenBound n) := by
  rw [lintegral_normalized_kernel_eq_unit_mass n (by omega) (newtonianKernel n) x hr,
    newtonianKernel_mass_eq_greenBound_mul_unitBall n hn]
  have hvol0 : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ 0 :=
    (measure_ball_pos volume 0 (by norm_num)).ne'
  have hvoltop : volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1) ≠ ∞ :=
    measure_ball_lt_top.ne
  calc
    (volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
        (ENNReal.ofReal (greenBound n) *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) =
      ENNReal.ofReal (greenBound n) *
        ((volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1))⁻¹ *
          volume (ball (0 : EuclideanSpace ℝ (Fin n)) 1)) := by ac_rfl
    _ = _ := by rw [ENNReal.inv_mul_cancel hvol0 hvoltop, mul_one]

end CenteredMaximal.Ball
