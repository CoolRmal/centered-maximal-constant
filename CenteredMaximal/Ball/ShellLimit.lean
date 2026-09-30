/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.SmoothBallCutoff

/-!
# Concentration of smooth radial shells

A nonnegative density integrated over a shrinking interval, with total mass one, averages a
continuous function to its value at the center. We apply this to the derivative of the smooth
ball cutoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped Interval

namespace CenteredMaximal.Ball

/-- A unit-mass nonnegative shrinking shell samples a continuous function at its center. -/
theorem shell_average_tendsto (R : ℝ)
    (ρ : ℝ → ℝ → ℝ) (H : ℝ → ℝ)
    (hρcont : ∀ δ > 0, Continuous (ρ δ))
    (hρnonneg : ∀ δ > 0, ∀ s ∈ Icc R (R + δ), 0 ≤ ρ δ s)
    (hρmass : ∀ δ > 0, (∫ s in R..(R + δ), ρ δ s) = 1)
    (hH : Continuous H) :
    Tendsto (fun δ => ∫ s in R..(R + δ), ρ δ s * H s)
      (𝓝[>] (0 : ℝ)) (𝓝 (H R)) := by
  apply Metric.tendsto_nhdsWithin_nhds.mpr
  intro ε hε
  obtain ⟨η, hη, hnear⟩ := (Metric.continuousAt_iff.mp hH.continuousAt) (ε / 2)
    (by linarith)
  refine ⟨η, hη, ?_⟩
  intro δ hδ hδnear
  have hδpos : 0 < δ := hδ
  have hδsmall : δ < η := by
    simpa only [Real.dist_eq, sub_zero, abs_of_pos hδpos] using hδnear
  have hab : R ≤ R + δ := by linarith
  have hcρ := hρcont δ hδpos
  have hIρH : IntervalIntegrable (fun s => ρ δ s * H s) volume R (R + δ) :=
    (hcρ.mul hH).intervalIntegrable _ _
  have hIρc : IntervalIntegrable (fun s => ρ δ s * H R) volume R (R + δ) :=
    (hcρ.mul continuous_const).intervalIntegrable _ _
  have hIε : IntervalIntegrable (fun s => (ε / 2) * ρ δ s) volume R (R + δ) :=
    (continuous_const.mul hcρ).intervalIntegrable _ _
  have hpoint : ∀ᵐ s ∂(volume : Measure ℝ),
      s ∈ Ioc R (R + δ) →
      ‖ρ δ s * (H s - H R)‖ ≤ (ε / 2) * ρ δ s := by
    filter_upwards with s hs
    have hsIcc : s ∈ Icc R (R + δ) := ⟨hs.1.le, hs.2⟩
    have hρ0 := hρnonneg δ hδpos s hsIcc
    have hsnear : dist s R < η := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hs.1.le)]
      linarith [hs.2]
    have hHnear : ‖H s - H R‖ ≤ ε / 2 := by
      simpa only [Real.norm_eq_abs, Real.dist_eq] using le_of_lt (hnear hsnear)
    calc
      ‖ρ δ s * (H s - H R)‖ = ρ δ s * ‖H s - H R‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hρ0]
      _ ≤ ρ δ s * (ε / 2) := mul_le_mul_of_nonneg_left hHnear hρ0
      _ = (ε / 2) * ρ δ s := mul_comm _ _
  have hbound := intervalIntegral.norm_integral_le_of_norm_le hab hpoint hIε
  have hdiffInt :
      (∫ s in R..(R + δ), ρ δ s * H s) - H R =
      (∫ s in R..(R + δ), ρ δ s * (H s - H R)) := by
    calc
      (∫ s in R..(R + δ), ρ δ s * H s) - H R =
          (∫ s in R..(R + δ), ρ δ s * H s) -
            (∫ s in R..(R + δ), ρ δ s * H R) := by
        rw [intervalIntegral.integral_mul_const, hρmass δ hδpos, one_mul]
      _ = ∫ s in R..(R + δ), (ρ δ s * H s - ρ δ s * H R) :=
        (intervalIntegral.integral_sub hIρH hIρc).symm
      _ = _ := by congr 1; ext s; ring
  have hmassε : (∫ s in R..(R + δ), (ε / 2) * ρ δ s) = ε / 2 := by
    rw [intervalIntegral.integral_const_mul, hρmass δ hδpos, mul_one]
  rw [hmassε] at hbound
  rw [Real.dist_eq, hdiffInt]
  exact lt_of_le_of_lt hbound (by linarith)
/-- The negative derivative of the smooth ball cutoff concentrates at its inner radius. -/
theorem radialBallCutoff_shell_tendsto {R : ℝ} (hR : 0 < R)
    (H : ℝ → ℝ) (hH : Continuous H) :
    Tendsto (fun δ => ∫ s in R..(R + δ),
      -(deriv (radialBallCutoff R δ) s) * H s)
      (𝓝[>] (0 : ℝ)) (𝓝 (H R)) := by
  apply shell_average_tendsto R
    (fun δ s => -(deriv (radialBallCutoff R δ) s)) H
  · intro δ hδ
    exact ((radialBallCutoff_contDiff R δ).continuous_deriv (by norm_num)).neg
  · intro δ hδ s hs
    exact neg_nonneg.mpr (radialBallCutoff_deriv_nonpos hR hδ hs.1)
  · intro δ hδ
    exact radialBallCutoff_deriv_mass hR hδ
  · exact hH

end CenteredMaximal.Ball
