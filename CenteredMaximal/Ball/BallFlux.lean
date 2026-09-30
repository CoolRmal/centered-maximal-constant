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

/-- The finite shell identity in polar coordinates. -/
theorem integral_laplacian_mul_smoothBallCutoff_eq_shell (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hw : ContDiff ℝ 2 w) (hsw : HasCompactSupport w)
    (x : EuclideanSpace ℝ (Fin n)) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    (∫ y, Laplacian.laplacian w y * smoothBallCutoff n x R δ y) =
      ∫ s in R..(R + δ), -(deriv (radialBallCutoff R δ) s) *
        (s ^ (n - 1) *
          (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            fderiv ℝ w (x + s • (ω : EuclideanSpace ℝ (Fin n)))
              (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere))) := by
  let E := EuclideanSpace ℝ (Fin n)
  let φ : ℝ → ℝ := fun s =>
    deriv Real.smoothTransition
      (((R + δ) ^ 2 - s ^ 2) / ((R + δ) ^ 2 - R ^ 2)) * 2 /
      ((R + δ) ^ 2 - R ^ 2)
  let g : E → ℝ := fun y => fderiv ℝ w y (y - x)
  have hφ : Continuous φ := by
    have hderiv : Continuous (deriv Real.smoothTransition) :=
      (Real.smoothTransition.contDiff : ContDiff ℝ 2 Real.smoothTransition).continuous_deriv
        (by norm_num)
    dsimp [φ]
    fun_prop
  have hgcont : Continuous g := by
    have hf : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by norm_num)
    fun_prop
  have hgsupp : HasCompactSupport g := by
    apply (hsw.fderiv ℝ).mono'
    intro y hy
    apply subset_tsupport
    intro hz
    exact hy (by simp [g, hz])
  have hcont : Continuous (fun y : E => φ ‖y - x‖ * g y) := by
    fun_prop
  have hint : Integrable (fun y : E => φ ‖y - x‖ * g y) :=
    hcont.integrable_of_hasCompactSupport (hgsupp.mul_left)
  rw [integral_laplacian_mul_smoothBallCutoff n w hw hsw x hR hδ]
  change (∫ y : E, φ ‖y - x‖ * g y) = _
  rw [integral_radial_mul_polar_swapped n x φ g hint]
  let H : ℝ → ℝ := fun s => s ^ (n - 1) *
    (∫ ω : sphere (0 : E) 1,
      fderiv ℝ w (x + s • (ω : E)) (ω : E) ∂(volume.toSphere))
  have hinner (s : ℝ) :
      (∫ ω : sphere (0 : E) 1, g (x + s • (ω : E)) ∂(volume.toSphere)) =
        s * (∫ ω : sphere (0 : E) 1,
          fderiv ℝ w (x + s • (ω : E)) (ω : E) ∂(volume.toSphere)) := by
    have heq (ω : sphere (0 : E) 1) :
        g (x + s • (ω : E)) =
          s * fderiv ℝ w (x + s • (ω : E)) (ω : E) := by
      simp only [g, add_sub_cancel_left, map_smul, smul_eq_mul]
    simp_rw [heq, integral_const_mul]
  have hrad (s : ℝ) :
      s ^ (n - 1) * φ s *
        (∫ ω : sphere (0 : E) 1,
          g (x + s • (ω : E)) ∂(volume.toSphere)) =
        -(deriv (radialBallCutoff R δ) s) * H s := by
    rw [hinner, radialBallCutoff_deriv]
    dsimp [φ, H]
    ring
  simp_rw [hrad]
  change (∫ s in Ioi (0 : ℝ), -(deriv (radialBallCutoff R δ) s) * H s) =
    ∫ s in R..(R + δ), -(deriv (radialBallCutoff R δ) s) * H s
  let F : ℝ → ℝ := fun s => -(deriv (radialBallCutoff R δ) s) * H s
  change (∫ s in Ioi (0 : ℝ), F s) = ∫ s in R..(R + δ), F s
  calc
    (∫ s in Ioi (0 : ℝ), F s) =
        ∫ s in Ioi (0 : ℝ), (Ioc R (R + δ)).indicator F s := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro s hs
      by_cases hsR : R < s
      · by_cases hsδ : s ≤ R + δ
        · simp only [Set.indicator_of_mem (show s ∈ Ioc R (R + δ) from ⟨hsR, hsδ⟩)]
        · have hz : F s = 0 := by
            simp [F, radialBallCutoff_deriv_eq_zero_outer_closed hR hδ (le_of_not_ge hsδ)]
          simp [Set.indicator_of_notMem (show s ∉ Ioc R (R + δ) from by simp [hsδ]), hz]
      · have hz : F s = 0 := by
          simp [F, radialBallCutoff_deriv_eq_zero_inner_closed hR hδ hs.out.le (le_of_not_gt hsR)]
        simp [Set.indicator_of_notMem (show s ∉ Ioc R (R + δ) from by simp [hsR]), hz]
    _ = ∫ s in Ioc R (R + δ), F s := by
      rw [setIntegral_indicator measurableSet_Ioc]
      have hset : Ioi (0 : ℝ) ∩ Ioc R (R + δ) = Ioc R (R + δ) := by
        ext s
        change (0 < s ∧ R < s ∧ s ≤ R + δ) ↔ R < s ∧ s ≤ R + δ
        constructor
        · intro hs; exact hs.2
        · intro hs; exact ⟨lt_trans hR hs.1, hs⟩
      rw [hset]
    _ = ∫ s in R..(R + δ), F s := by
      rw [intervalIntegral.integral_of_le (by linarith : R ≤ R + δ)]

/-- The integral of the Laplacian over a ball equals the flux of the gradient through its
boundary sphere, in every positive dimension. -/
theorem integral_laplacian_ball_eq_sphere_flux (n : ℕ) [NeZero n]
    (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hw : ContDiff ℝ 2 w) (hsw : HasCompactSupport w)
    (x : EuclideanSpace ℝ (Fin n)) {R : ℝ} (hR : 0 < R) :
    (∫ y in ball x R, Laplacian.laplacian w y) =
      R ^ (n - 1) *
        (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          fderiv ℝ w (x + R • (ω : EuclideanSpace ℝ (Fin n)))
            (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere)) := by
  let H : ℝ → ℝ := fun s => s ^ (n - 1) *
    (∫ ω : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      fderiv ℝ w (x + s • (ω : EuclideanSpace ℝ (Fin n)))
        (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere))
  have hH : Continuous H :=
    (continuous_id.pow (n - 1)).mul (continuous_sphereFlux n w hw hsw x)
  have hleft := integral_laplacian_mul_smoothBallCutoff_tendsto n w hw hsw x hR
  have hright := radialBallCutoff_shell_tendsto hR H hH
  have heq : (fun δ => ∫ y, Laplacian.laplacian w y *
        smoothBallCutoff n x R δ y) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ => ∫ s in R..(R + δ),
        -(deriv (radialBallCutoff R δ) s) * H s) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    exact integral_laplacian_mul_smoothBallCutoff_eq_shell n w hw hsw x hR hδ
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)


end CenteredMaximal.Ball
