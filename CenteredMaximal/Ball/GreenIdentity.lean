/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.PlanarNormalized
public import CenteredMaximal.Ball.NewtonianMass
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Radial identities for the Green comparison kernels

The logarithmic and Newtonian profiles vanish at their support radii. Their radial derivatives
have constant flux, the scalar identity behind the Green pairing with the Laplacian.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace CenteredMaximal.Ball

/-- A finite-mass extended kernel has an integrable real representative almost everywhere. -/
theorem real_representative_of_finite_lintegral {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (Q : E → ℝ≥0∞) (hQ : AEMeasurable Q μ)
    (hfin : (∫⁻ y, Q y ∂μ) ≠ ∞) :
    Integrable (fun y ↦ (Q y).toReal) μ ∧
      ∀ᵐ y ∂μ, Q y = ENNReal.ofReal ((Q y).toReal) := by
  refine ⟨integrable_toReal_of_lintegral_ne_top hQ hfin, ?_⟩
  filter_upwards [ae_lt_top' hQ hfin] with y hy
  exact (ENNReal.ofReal_toReal hy.ne).symm

/-- The normalized planar kernel has an integrable real representative at every positive scale. -/
theorem normalized_planarKernel_real_representative
    (x : EuclideanSpace ℝ (Fin 2)) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : EuclideanSpace ℝ (Fin 2) ↦
      ((MeasureTheory.volume (Metric.ball x r))⁻¹ *
        planarKernel (r⁻¹ • (x - y))).toReal) ∧
    ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 2))),
      (MeasureTheory.volume (Metric.ball x r))⁻¹ *
        planarKernel (r⁻¹ • (x - y)) =
      ENNReal.ofReal (((MeasureTheory.volume (Metric.ball x r))⁻¹ *
        planarKernel (r⁻¹ • (x - y))).toReal) := by
  apply real_representative_of_finite_lintegral volume
  · exact (measurable_planarKernel.comp (by fun_prop)).const_mul _ |>.aemeasurable
  · rw [planarKernel_normalized_mass x hr]
    exact ENNReal.ofReal_ne_top

/-- The normalized Newtonian kernel has an integrable real representative in dimension `n ≥ 3`. -/
theorem normalized_newtonianKernel_real_representative (n : ℕ) (hn : 3 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) ↦
      ((MeasureTheory.volume (Metric.ball x r))⁻¹ *
        newtonianKernel n (r⁻¹ • (x - y))).toReal) ∧
    ∀ᵐ y ∂(MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin n))),
      (MeasureTheory.volume (Metric.ball x r))⁻¹ *
        newtonianKernel n (r⁻¹ • (x - y)) =
      ENNReal.ofReal (((MeasureTheory.volume (Metric.ball x r))⁻¹ *
        newtonianKernel n (r⁻¹ • (x - y))).toReal) := by
  apply real_representative_of_finite_lintegral volume
  · exact (measurable_newtonianKernel n |>.comp (by fun_prop)).const_mul _ |>.aemeasurable
  · rw [lintegral_normalized_newtonianKernel n hn x hr]
    exact ENNReal.ofReal_ne_top

/-- The untruncated radial logarithmic profile in dimension two. -/
def planarGreenProfile (s : ℝ) : ℝ := 1 - 2 * Real.log s

/-- The untruncated radial Newtonian profile in dimension at least three. -/
def newtonianGreenProfile (n : ℕ) (s : ℝ) : ℝ :=
  ((n : ℝ) * s ^ ((2 : ℝ) - (n : ℝ)) - 2) / ((n : ℝ) - 2)

/-- Away from the origin, the planar kernel is the positive part of the radial profile. -/
theorem planarKernel_eq_profile (z : EuclideanSpace ℝ (Fin 2)) (hz : z ≠ 0) :
    planarKernel z = ENNReal.ofReal (planarGreenProfile ‖z‖) := by
  simp [planarKernel, planarGreenProfile, hz]

/-- Away from the origin, the Newtonian kernel is the positive part of the radial profile. -/
theorem newtonianKernel_eq_profile (n : ℕ) (z : EuclideanSpace ℝ (Fin n)) (hz : z ≠ 0) :
    newtonianKernel n z = ENNReal.ofReal (newtonianGreenProfile n ‖z‖) := by
  simp [newtonianKernel, newtonianGreenProfile, hz]

/-- The logarithmic profile vanishes at its support radius. -/
theorem planarGreenProfile_at_radius : planarGreenProfile planarGreenRadius = 0 := by
  have hlog : Real.log planarGreenRadius = 1 / 2 := by
    simp [planarGreenRadius, Real.log_sqrt (Real.exp_pos 1).le]
  simp [planarGreenProfile, hlog]

/-- The Newtonian profile vanishes at its support radius. -/
theorem newtonianGreenProfile_at_radius (n : ℕ) (hn : 3 ≤ n) :
    newtonianGreenProfile n (greenRadius n) = 0 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hR : 0 < greenRadius n := greenRadius_pos n hn
  have hpow : greenRadius n ^ ((2 : ℝ) - (n : ℝ)) = 2 / (n : ℝ) := by
    calc
      _ = (greenRadius n ^ ((n : ℝ) - 2))⁻¹ := by
        rw [show (2 : ℝ) - (n : ℝ) = -((n : ℝ) - 2) by ring]
        exact Real.rpow_neg hR.le _
      _ = ((n : ℝ) / 2)⁻¹ := by rw [greenRadius_rpow_sub_two n hn]
      _ = 2 / (n : ℝ) := by field_simp
  have hnum : (n : ℝ) * (2 / (n : ℝ)) - 2 = 0 := by
    field_simp
    ring
  simp [newtonianGreenProfile, hpow, hnum]

/-- The radial derivative of the planar logarithmic Green profile. -/
theorem hasDerivAt_planarGreenProfile {s : ℝ} (hs : 0 < s) :
    HasDerivAt planarGreenProfile (-2 / s) s := by
  have hlog := Real.hasDerivAt_log hs.ne'
  unfold planarGreenProfile
  convert! (hasDerivAt_const s (1 : ℝ)).sub (hlog.const_mul 2) using 1
  ring

/-- The radial derivative of the Newtonian Green profile. -/
theorem hasDerivAt_newtonianGreenProfile (n : ℕ) (hn : 3 ≤ n)
    {s : ℝ} (hs : 0 < s) :
    HasDerivAt (newtonianGreenProfile n)
      (-(n : ℝ) * s ^ ((1 : ℝ) - (n : ℝ))) s := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hden : (n : ℝ) - 2 ≠ 0 := by linarith
  have hpow : HasDerivAt (fun t : ℝ ↦ t ^ ((2 : ℝ) - (n : ℝ)))
      (((2 : ℝ) - (n : ℝ)) * s ^ ((1 : ℝ) - (n : ℝ))) s := by
    simpa only [show (2 : ℝ) - (n : ℝ) - 1 = 1 - n by ring] using
      Real.hasDerivAt_rpow_const (p := (2 : ℝ) - (n : ℝ)) (Or.inl hs.ne')
  unfold newtonianGreenProfile
  convert! ((hpow.const_mul (n : ℝ)).sub_const 2).div_const ((n : ℝ) - 2) using 1
  field_simp
  ring

/-- The planar radial flux is constant on the punctured plane. -/
theorem planarGreenProfile_flux {s : ℝ} (hs : 0 < s) :
    s * deriv planarGreenProfile s = -2 := by
  rw [(hasDerivAt_planarGreenProfile hs).deriv]
  field_simp

/-- The Newtonian radial flux is constant on the punctured space. -/
theorem newtonianGreenProfile_flux (n : ℕ) (hn : 3 ≤ n)
    {s : ℝ} (hs : 0 < s) :
    s ^ (n - 1) * deriv (newtonianGreenProfile n) s = -(n : ℝ) := by
  rw [(hasDerivAt_newtonianGreenProfile n hn hs).deriv]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hne : (n : ℕ) ≠ 0 := by omega
  have hpow : s ^ (n - 1) * s ^ ((1 : ℝ) - (n : ℝ)) = 1 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs]
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]
      norm_num
    rw [hcast]
    convert Real.rpow_zero s using 1
    ring_nf
  calc
    s ^ (n - 1) * (-(n : ℝ) * s ^ ((1 : ℝ) - (n : ℝ))) =
        -(n : ℝ) * (s ^ (n - 1) * s ^ ((1 : ℝ) - (n : ℝ))) := by ring
    _ = -(n : ℝ) := by rw [hpow, mul_one]

end CenteredMaximal.Ball
