/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.RadialGreenCalculus
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Center limits in the Green pairing

The radial Green formula is first proved on a finite annulus. These lemmas control its
inner boundary as the annulus shrinks to the center.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise ENNReal

namespace CenteredMaximal.Ball

/-- Spherical integrals of a continuous function vary continuously with radius. -/
theorem continuous_sphereIntegral (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Continuous w)
    (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun r : ℝ ↦
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (x + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) := by
  let S := Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1
  let ν : Measure S := volume.toSphere
  have hf : Continuous (fun p : ℝ × S ↦ w (x + p.1 • (p.2 : EuclideanSpace ℝ (Fin n)))) := by
    fun_prop
  have h := continuous_parametric_integral_of_continuous
    (μ := ν) (s := (Set.univ : Set S))
    (f := fun r (ω : S) ↦ w (x + r • (ω : EuclideanSpace ℝ (Fin n)))) hf isCompact_univ
  simpa [ν, S] using h

/-- If a continuous function vanishes at the center, its unnormalized spherical integral
vanishes as the radius tends to zero. -/
theorem tendsto_sphereIntegral_zero (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : Continuous w)
    (x : EuclideanSpace ℝ (Fin n)) (hx : w x = 0) :
    Tendsto (fun r : ℝ ↦
      ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        w (x + r • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere))
      (𝓝 0) (𝓝 0) := by
  have h := ((continuous_sphereIntegral n w hw x).continuousAt (x := (0 : ℝ))).tendsto
  simpa [hx] using h

/-- The logarithmic Green profile is integrably small after multiplication by planar ball
volume at the center. -/
theorem tendsto_planarGreenProfile_mul_sq :
    Tendsto (fun r : ℝ ↦ planarGreenProfile r * r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpow : Tendsto (fun r : ℝ ↦ r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.pow 2
  have hlog : Tendsto (fun r : ℝ ↦ Real.log r * r ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Real.rpow_two] using
      (tendsto_log_mul_rpow_nhdsGT_zero (by norm_num : (0 : ℝ) < 2))
  have h := hpow.sub (hlog.const_mul 2)
  simpa [planarGreenProfile, sub_mul, mul_assoc] using h

/-- The Newtonian Green profile is integrably small after multiplication by the volume
scaling factor of an `n`-dimensional ball. -/
theorem tendsto_newtonianGreenProfile_mul_pow (n : ℕ) (hn : 3 ≤ n) :
    Tendsto (fun r : ℝ ↦ newtonianGreenProfile n r * r ^ n)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hid : Tendsto (fun r : ℝ ↦ r) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hpow2 : Tendsto (fun r : ℝ ↦ r ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.pow 2
  have hpowN : Tendsto (fun r : ℝ ↦ r ^ n) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hn0 : n ≠ 0 := by omega
    simpa [hn0] using hid.pow n
  have hlim : Tendsto (fun r : ℝ ↦
      ((n : ℝ) * r ^ 2 - 2 * r ^ n) / ((n : ℝ) - 2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (((hpow2.const_mul (n : ℝ)).sub (hpowN.const_mul 2)).div_const
      ((n : ℝ) - 2))
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hpow : r ^ ((2 : ℝ) - (n : ℝ)) * r ^ n = r ^ 2 := by
    have h := Real.rpow_add_natCast hr.ne' ((2 : ℝ) - (n : ℝ)) n
    have hexp : (2 : ℝ) - (n : ℝ) + (n : ℝ) = 2 := by ring
    rw [hexp, Real.rpow_two] at h
    exact h.symm
  symm
  unfold newtonianGreenProfile
  calc
    ((n : ℝ) * r ^ ((2 : ℝ) - (n : ℝ)) - 2) / ((n : ℝ) - 2) * r ^ n =
        (((n : ℝ) * r ^ ((2 : ℝ) - (n : ℝ)) - 2) * r ^ n) /
          ((n : ℝ) - 2) := by ring
    _ = ((n : ℝ) * r ^ 2 - 2 * r ^ n) / ((n : ℝ) - 2) := by
      congr 1
      calc
        ((n : ℝ) * r ^ ((2 : ℝ) - (n : ℝ)) - 2) * r ^ n =
            (n : ℝ) * (r ^ ((2 : ℝ) - (n : ℝ)) * r ^ n) - 2 * r ^ n := by ring
        _ = _ := by rw [hpow]

/-- A globally bounded function has ball integrals of order `r ^ n` at every center. -/
theorem norm_integral_ball_le_const_mul_pow (n : ℕ) [NeZero n]
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B) {r : ℝ} (hr : 0 ≤ r) :
    ‖∫ y in Metric.ball x r, g y‖ ≤
      (B * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) * r ^ n := by
  have hball : volume (Metric.ball x r) < ∞ := measure_ball_lt_top
  have hbound := norm_setIntegral_le_of_norm_le_const hball (fun y _ ↦ hB y)
  have hvol : (volume (Metric.ball x r)).toReal =
      r ^ n * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal := by
    rw [Measure.addHaar_ball volume x hr, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (pow_nonneg hr _), finrank_euclideanSpace_fin]
  calc
    ‖∫ y in Metric.ball x r, g y‖ ≤
        B * (volume (Metric.ball x r)).toReal := hbound
    _ = (B * (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal) *
        r ^ n := by rw [hvol]; ring

private theorem tendsto_profile_mul_integral_ball_zero (n : ℕ) [NeZero n]
    (ψ : ℝ → ℝ)
    (hψ : Tendsto (fun r : ℝ ↦ ψ r * r ^ n) (𝓝[>] (0 : ℝ)) (𝓝 0))
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B) :
    Tendsto (fun r : ℝ ↦ ψ r * ∫ y in Metric.ball x r, g y)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal
  have hlim : Tendsto (fun r : ℝ ↦ (B * V) * ‖ψ r * r ^ n‖)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hψ.norm.const_mul (B * V)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine squeeze_zero' (Eventually.of_forall fun r ↦ norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hF := norm_integral_ball_le_const_mul_pow n g x B hB hr.le
  have hpow : 0 ≤ r ^ n := pow_nonneg hr.le _
  calc
    ‖ψ r * ∫ y in Metric.ball x r, g y‖ =
        ‖ψ r‖ * ‖∫ y in Metric.ball x r, g y‖ := norm_mul _ _
    _ ≤ ‖ψ r‖ * ((B * V) * r ^ n) :=
      mul_le_mul_of_nonneg_left hF (norm_nonneg _)
    _ = (B * V) * ‖ψ r * r ^ n‖ := by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hpow]
      ring

/-- A bounded Laplacian contributes no inner boundary term to the planar Green formula. -/
theorem tendsto_planarGreenProfile_mul_integral_ball_zero
    (g : EuclideanSpace ℝ (Fin 2) → ℝ) (x : EuclideanSpace ℝ (Fin 2))
    (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B) :
    Tendsto (fun r : ℝ ↦
      planarGreenProfile r * ∫ y in Metric.ball x r, g y)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  tendsto_profile_mul_integral_ball_zero 2 planarGreenProfile
    tendsto_planarGreenProfile_mul_sq g x B hB

/-- A bounded Laplacian contributes no inner boundary term to the Newtonian Green formula. -/
theorem tendsto_newtonianGreenProfile_mul_integral_ball_zero
    (n : ℕ) (hn : 3 ≤ n)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (B : ℝ) (hB : ∀ y, ‖g y‖ ≤ B) :
    Tendsto (fun r : ℝ ↦
      newtonianGreenProfile n r * ∫ y in Metric.ball x r, g y)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  letI : NeZero n := ⟨by omega⟩
  exact tendsto_profile_mul_integral_ball_zero n (newtonianGreenProfile n)
    (tendsto_newtonianGreenProfile_mul_pow n hn) g x B hB

end CenteredMaximal.Ball
