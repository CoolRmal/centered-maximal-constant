/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.ShellLimit
public import CenteredMaximal.Ball.PolarSwap

/-!
# Flux across Euclidean balls

The smooth cutoff identity tends to the ordinary ball integral on its Laplacian side. The
radial side will be identified with spherical flux using polar integration.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped Interval

namespace CenteredMaximal.Ball

/-- Pairing the Laplacian with shrinking smooth ball cutoffs tends to its integral over the ball. -/
theorem integral_laplacian_mul_smoothBallCutoff_tendsto (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hw : ContDiff ℝ 2 w) (hsw : HasCompactSupport w)
    (x : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    Tendsto (fun δ => ∫ y, Laplacian.laplacian w y * smoothBallCutoff n x R δ y)
      (𝓝[>] (0 : ℝ))
      (𝓝 (∫ y in ball x R, Laplacian.laplacian w y)) := by
  let F : ℝ → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun δ y => Laplacian.laplacian w y * smoothBallCutoff n x R δ y
  let f : EuclideanSpace ℝ (Fin n) → ℝ :=
    (ball x R).indicator (Laplacian.laplacian w)
  have hΔcont := continuous_laplacian n w hw
  have hΔint : Integrable (Laplacian.laplacian w) :=
    hΔcont.integrable_of_hasCompactSupport (hasCompactSupport_laplacian n w hsw)
  have hmeas : ∀ᶠ δ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (F δ) volume := by
    filter_upwards with δ
    exact (hΔcont.mul (smoothBallCutoff_contDiff n x R δ).continuous).aestronglyMeasurable
  have hbound : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ‖F δ y‖ ≤ ‖Laplacian.laplacian w y‖ := by
    filter_upwards with δ
    filter_upwards with y
    dsimp [F, smoothBallCutoff]
    rw [abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _)]
    calc
      |Laplacian.laplacian w y| * Real.smoothTransition _ ≤
          |Laplacian.laplacian w y| * 1 :=
        mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one _) (abs_nonneg _)
      _ = |Laplacian.laplacian w y| := mul_one _
  have hsphere : volume (sphere x R) = 0 :=
    volume.addHaar_sphere_of_ne_zero x hR.ne'
  have hlim : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun δ => F δ y) (𝓝[>] (0 : ℝ)) (𝓝 (f y)) := by
    have hae : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        y ∉ sphere x R := by
      apply ae_iff.mpr
      have hset : {y | ¬ y ∉ sphere x R} = sphere x R := by
        ext z
        simp
      rw [hset]
      exact hsphere
    filter_upwards [hae] with y hySphere
    by_cases hy : y ∈ ball x R
    · have hval : (fun δ => F δ y) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => f y) := by
        filter_upwards [self_mem_nhdsWithin] with δ hδ
        simp only [F, f, Set.indicator_of_mem hy,
          smoothBallCutoff_one n x y hR hδ (ball_subset_closedBall hy), mul_one]
      exact tendsto_const_nhds.congr' hval.symm
    · have hge : R ≤ ‖y-x‖ := by
        simpa only [mem_ball, dist_eq_norm, not_lt] using hy
      have hne : ‖y-x‖ ≠ R := by
        intro heq
        exact hySphere (by simpa only [mem_sphere, dist_eq_norm] using heq)
      have hgt : R < ‖y-x‖ := lt_of_le_of_ne hge (Ne.symm hne)
      have hsmall : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < ‖y-x‖ - R :=
        (eventually_lt_nhds (by linarith)).filter_mono nhdsWithin_le_nhds
      have hval : (fun δ => F δ y) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => f y) := by
        filter_upwards [self_mem_nhdsWithin, hsmall] with δ hδ hd
        simp only [F, f, Set.indicator_of_notMem hy,
          smoothBallCutoff_zero n x y hR hδ (by linarith), mul_zero]
      exact tendsto_const_nhds.congr' hval.symm
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (l := 𝓝[>] (0 : ℝ))
    (F := F) (f := f) (fun y => ‖Laplacian.laplacian w y‖)
    hmeas hbound hΔint.norm hlim
  simpa only [F, f, integral_indicator measurableSet_ball] using h

/-- The sphere integral of the radial directional derivative is continuous in the radius. -/
theorem continuous_sphereFlux (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hw : ContDiff ℝ 2 w) (hsw : HasCompactSupport w)
    (x : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun s : ℝ =>
      ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
        fderiv ℝ w (x + s • (ω : EuclideanSpace ℝ (Fin n)))
          (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere)) := by
  let E := EuclideanSpace ℝ (Fin n)
  let S := sphere (0 : E) 1
  let ν : Measure S := volume.toSphere
  obtain ⟨C, hC⟩ := (hsw.fderiv ℝ).exists_bound_of_continuous
    (hw.continuous_fderiv (by norm_num))
  have hfw : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by norm_num)
  apply continuous_iff_continuousAt.mpr
  intro s₀
  have hmeas : ∀ᶠ s in 𝓝 s₀,
      AEStronglyMeasurable
        (fun ω : S => fderiv ℝ w (x + s • (ω : E)) (ω : E)) ν := by
    filter_upwards with s
    exact (by fun_prop : Continuous (fun ω : S =>
      fderiv ℝ w (x + s • (ω : E)) (ω : E))).aestronglyMeasurable
  have hbound : ∀ᶠ s in 𝓝 s₀, ∀ᵐ (ω : S) ∂ν,
      ‖fderiv ℝ w (x + s • (ω : E)) (ω : E)‖ ≤ C := by
    filter_upwards with s
    filter_upwards with ω
    have hω : ‖(ω : E)‖ = 1 := by
      have h := ω.property
      simpa only [S, mem_sphere, dist_zero_right] using h
    calc
      ‖fderiv ℝ w (x + s • (ω : E)) (ω : E)‖ ≤
          ‖fderiv ℝ w (x + s • (ω : E))‖ * ‖(ω : E)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ w (x + s • (ω : E))‖ := by rw [hω, mul_one]
      _ ≤ C := hC _
  have hlim : ∀ᵐ (ω : S) ∂ν, Tendsto
      (fun s : ℝ => fderiv ℝ w (x + s • (ω : E)) (ω : E))
      (𝓝 s₀) (𝓝 (fderiv ℝ w (x + s₀ • (ω : E)) (ω : E))) := by
    filter_upwards with ω
    exact (by fun_prop : Continuous (fun s : ℝ =>
      fderiv ℝ w (x + s • (ω : E)) (ω : E))).continuousAt
  exact tendsto_integral_filter_of_dominated_convergence
    (μ := ν) (l := 𝓝 s₀) (F := fun s (ω : S) =>
      fderiv ℝ w (x + s • (ω : E)) (ω : E))
    (fun _ => C) hmeas hbound (integrable_const C) hlim


end CenteredMaximal.Ball
