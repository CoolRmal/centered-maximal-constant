/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.WeakLaplacianTests

/-!
# Local weak convergence against Green kernels

The ball obstacle lives on a bounded domain. A zero extension can have a boundary
Laplacian that is not bounded, although the Laplacian is uniformly bounded in the
interior. A smooth cutoff equal to one on a Green kernel's support turns local
weak convergence and local bounds into the global hypotheses of `WeakPairingDensity`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace CenteredMaximal.Ball

/-- The ball cutoff used for localizing Green kernels has all finite derivatives. -/
theorem smoothBallCutoff_contDiff_smooth (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (R δ : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (smoothBallCutoff n x R δ) := by
  unfold smoothBallCutoff
  have hsub : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : EuclideanSpace ℝ (Fin n) ↦ y - x) := by fun_prop
  have hq : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : EuclideanSpace ℝ (Fin n) ↦ ‖y - x‖ ^ 2) := hsub.norm_sq ℝ
  have hinner : ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun y : EuclideanSpace ℝ (Fin n) ↦
        ((R + δ) ^ 2 - ‖y - x‖ ^ 2) / ((R + δ) ^ 2 - R ^ 2)) := by fun_prop
  exact (Real.smoothTransition.contDiff (n := ⊤)).comp hinner

/-- The localizing cutoff is bounded by one in absolute value. -/
theorem smoothBallCutoff_norm_le_one (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (R δ : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    ‖smoothBallCutoff n x R δ y‖ ≤ 1 := by
  unfold smoothBallCutoff
  rw [Real.norm_eq_abs]
  let a : ℝ := ((R + δ) ^ 2 - ‖y - x‖ ^ 2) / ((R + δ) ^ 2 - R ^ 2)
  have hn : 0 ≤ Real.smoothTransition a := Real.smoothTransition.nonneg a
  have hle : Real.smoothTransition a ≤ 1 := Real.smoothTransition.le_one a
  exact abs_le.mpr ⟨by dsimp [a] at hn; linarith, by dsimp [a] at hle; exact hle⟩

/-- A local distributional Laplacian on `D`, tested only by smooth compact
functions whose closed support lies in `D`. -/
def HasLocalDistributionalLaplacian (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (w g : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
    HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
    tsupport φ ⊆ D →
      (∫ y, φ y * g y) = (∫ y, w y * Laplacian.laplacian φ y)

/-- The local distributional equation supplies local smooth-test convergence.
Only an interior bound on the approximating obstacles is used, since the
Laplacian of a test supported in `D` vanishes outside `D`. -/
theorem local_weak_test_convergence_of_distributional_laplacian (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (w g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hlimw : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun k ↦ wₖ k y) atTop (𝓝 (w y)))
    (B : ℝ) (hB : ∀ k y, y ∈ D → ‖wₖ k y‖ ≤ B)
    (hdistribution : HasLocalDistributionalLaplacian n D w g) :
    ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      tsupport φ ⊆ D →
        Tendsto (fun k ↦ ∫ y, φ y * Laplacian.laplacian (wₖ k) y)
          atTop (𝓝 (∫ y, φ y * g y)) := by
  intro φ hφsupp hφsmooth hφD
  have hφtwo : ContDiff ℝ 2 φ := hφsmooth.of_le (by
    change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  have hΔφcont : Continuous (Laplacian.laplacian φ) :=
    continuous_laplacian n φ hφtwo
  have hΔφint : Integrable (Laplacian.laplacian φ) :=
    hΔφcont.integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian n φ hφsupp)
  have hΔφzero (y : EuclideanSpace ℝ (Fin n)) (hyD : y ∉ D) :
      Laplacian.laplacian φ y = 0 := by
    have hnot : y ∉ tsupport φ := fun hy ↦ hyD (hφD hy)
    have hzero : φ =ᶠ[𝓝 y] (0 : EuclideanSpace ℝ (Fin n) → ℝ) :=
      notMem_tsupport_iff_eventuallyEq.mp hnot
    have hΔzero := (InnerProductSpace.laplacian_congr_nhds hzero).eq_of_nhds
    simpa [Pi.zero_def] using hΔzero
  have hlim : Tendsto
      (fun k ↦ ∫ y, wₖ k y * Laplacian.laplacian φ y) atTop
      (𝓝 (∫ y, w y * Laplacian.laplacian φ y)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun y ↦ B * ‖Laplacian.laplacian φ y‖)
    · intro k
      exact (hwₖ k).continuous.aestronglyMeasurable.mul
        hΔφcont.aestronglyMeasurable
    · exact hΔφint.norm.const_mul B
    · intro k
      filter_upwards with y
      by_cases hyD : y ∈ D
      · calc
          ‖wₖ k y * Laplacian.laplacian φ y‖ =
              ‖wₖ k y‖ * ‖Laplacian.laplacian φ y‖ := norm_mul _ _
          _ ≤ B * ‖Laplacian.laplacian φ y‖ :=
            mul_le_mul_of_nonneg_right (hB k y hyD) (norm_nonneg _)
      · simp [hΔφzero y hyD]
    · filter_upwards [hlimw] with y hy
      exact hy.mul tendsto_const_nhds
  have hsym (k : ℕ) :
      (∫ y, φ y * Laplacian.laplacian (wₖ k) y) =
        (∫ y, wₖ k y * Laplacian.laplacian φ y) := by
    convert integral_laplacian_mul_eq_integral_mul_laplacian n
      (wₖ k) φ (hwₖ k) hφtwo (hsuppₖ k) hφsupp using 1
    · congr 1
      funext y
      ring
  simpa only [hsym, (hdistribution φ hφsupp hφsmooth hφD).symm] using hlim

/-- Local weak convergence of bounded densities extends from smooth compact tests
supported in an interior set `D` to an integrable kernel supported where the
cutoff `χ` equals one. The density bounds are required only in `D`. -/
theorem tendsto_integral_mul_of_local_weak_test_convergence (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχsupp : HasCompactSupport χ)
    (hχsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hχD : tsupport χ ⊆ D)
    (hχbound : ∀ y, ‖χ y‖ ≤ 1)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (gₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : AEStronglyMeasurable g volume)
    (hgₖ : ∀ k, AEStronglyMeasurable (gₖ k) volume)
    (B : ℝ) (hB₀ : 0 ≤ B)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ D → ‖g y‖ ≤ B)
    (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ D → ‖gₖ k y‖ ≤ B)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      tsupport φ ⊆ D →
        Tendsto (fun k ↦ ∫ y, φ y * gₖ k y) atTop (𝓝 (∫ y, φ y * g y)))
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (hKχ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      K y * χ y = K y) :
    Tendsto (fun k ↦ ∫ y, K y * gₖ k y) atTop (𝓝 (∫ y, K y * g y)) := by
  have hχmeas : AEStronglyMeasurable χ volume := hχsmooth.continuous.aestronglyMeasurable
  have hbound (v : EuclideanSpace ℝ (Fin n) → ℝ)
      (hv : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        y ∈ D → ‖v y‖ ≤ B) :
      ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        ‖χ y * v y‖ ≤ B := by
    filter_upwards [hv] with y hy
    by_cases hzero : χ y = 0
    · simp [hzero, hB₀]
    · calc
        ‖χ y * v y‖ = ‖χ y‖ * ‖v y‖ := norm_mul _ _
        _ ≤ ‖χ y‖ * B :=
          mul_le_mul_of_nonneg_left
            (hy (hχD (subset_tsupport χ (by simpa [Function.mem_support] using hzero))))
            (norm_nonneg _)
        _ ≤ 1 * B := mul_le_mul_of_nonneg_right (hχbound y) hB₀
        _ = B := one_mul _
  have hweak' : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
        Tendsto (fun k ↦ ∫ y, φ y * (χ y * gₖ k y)) atTop
          (𝓝 (∫ y, φ y * (χ y * g y))) := by
    intro φ hφsupp hφsmooth
    have hφχsupp : HasCompactSupport (fun y ↦ φ y * χ y) := hχsupp.mul_left
    have hφχsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y ↦ φ y * χ y) :=
      hφsmooth.mul hχsmooth
    have hφχD : tsupport (fun y ↦ φ y * χ y) ⊆ D :=
      (tsupport_mul_subset_right (f := φ) (g := χ)).trans hχD
    simpa only [mul_assoc] using hweak (fun y ↦ φ y * χ y)
      hφχsupp hφχsmooth hφχD
  have hlim := tendsto_integral_mul_of_weak_test_convergence n
    (fun y ↦ χ y * g y) (fun k y ↦ χ y * gₖ k y)
    (hχmeas.mul hg) (fun k ↦ hχmeas.mul (hgₖ k)) B hB₀
    (hbound g hBg) (fun k ↦ hbound (gₖ k) (hBgₖ k)) hweak' K hK
  have hpair (v : EuclideanSpace ℝ (Fin n) → ℝ) :
      (∫ y, K y * (χ y * v y)) = (∫ y, K y * v y) := by
    apply integral_congr_ae
    filter_upwards [hKχ] with y hy
    calc
      K y * (χ y * v y) = (K y * χ y) * v y := by ring
      _ = K y * v y := by rw [hy]
  simpa only [hpair] using hlim

/-- If bounded local densities converge almost everywhere in the interior,
their pairings with any integrable kernel supported there converge directly by
dominated convergence. This avoids an a priori pointwise bound on the obstacle. -/
theorem tendsto_integral_mul_of_local_ae_convergence (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (hKzero : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∉ D → K y = 0)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (gₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hgₖ : ∀ k, AEStronglyMeasurable (gₖ k) volume)
    (B : ℝ) (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ D → ‖gₖ k y‖ ≤ B)
    (hlim : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ D → Tendsto (fun k ↦ gₖ k y) atTop (𝓝 (g y))) :
    Tendsto (fun k ↦ ∫ y, K y * gₖ k y) atTop (𝓝 (∫ y, K y * g y)) := by
  apply tendsto_integral_of_dominated_convergence (fun y ↦ B * ‖K y‖)
  · intro k
    exact hK.aestronglyMeasurable.mul (hgₖ k)
  · exact hK.norm.const_mul B
  · intro k
    filter_upwards [hKzero, hBgₖ k] with y hKy hBy
    by_cases hy : y ∈ D
    · calc
        ‖K y * gₖ k y‖ = ‖K y‖ * ‖gₖ k y‖ := norm_mul _ _
        _ ≤ ‖K y‖ * B := mul_le_mul_of_nonneg_left (hBy hy) (norm_nonneg _)
        _ = B * ‖K y‖ := mul_comm _ _
    · simp [hKy hy]
  · filter_upwards [hKzero, hlim] with y hKy hy
    by_cases hyD : y ∈ D
    · exact tendsto_const_nhds.mul (hy hyD)
    · simp [hKy hyD]

/-- A kernel unchanged by a cutoff supported in `D` vanishes almost everywhere
outside `D`. -/
theorem kernel_zero_outside_of_mul_cutoff_eq_self (n : ℕ)
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (χ K : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχD : tsupport χ ⊆ D)
    (hKχ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      K y * χ y = K y) :
    ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∉ D → K y = 0 := by
  filter_upwards [hKχ] with y hy
  intro hyD
  have hχzero : χ y = 0 := by
    by_contra hχ
    exact hyD (hχD (subset_tsupport χ (by simpa [Function.mem_support] using hχ)))
  rw [hχzero, mul_zero] at hy
  exact hy.symm

/-- Direct a.e. convergence of locally bounded Laplacians gives the limiting
nonnegative Green pairing at a center where the smooth obstacles tend to zero. -/
theorem nonneg_green_pairing_of_local_ae_convergence (n : ℕ) [NeZero n]
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (hKzero : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∉ D → K y = 0)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ gₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (hgₖ : ∀ k, AEStronglyMeasurable (gₖ k) volume)
    (B : ℝ) (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ D → ‖gₖ k y‖ ≤ B)
    (hlim : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ D → Tendsto (fun k ↦ gₖ k y) atTop (𝓝 (g y)))
    (x : EuclideanSpace ℝ (Fin n))
    (hcenter : Tendsto (fun k ↦ wₖ k x) atTop (𝓝 0))
    (ρ c : ℝ) (hc : 0 ≤ c)
    (hpair : ∀ k,
      (∫ y, K y * gₖ k y) = c *
        ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          wₖ k (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) -
         (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          wₖ k x ∂(volume.toSphere)))) :
    0 ≤ ∫ y, K y * g y := by
  apply nonneg_green_pairing_of_integral_convergence n K g wₖ gₖ hwₖ_nonneg
    (tendsto_integral_mul_of_local_ae_convergence n D K hK hKzero g gₖ
      hgₖ B hBgₖ hlim) x hcenter ρ c hc hpair

/-- Local boundedness and local weak convergence suffice for the Green comparison
at a center where nonnegative smooth approximants tend to zero. -/
theorem nonneg_green_pairing_of_local_weak_tests (n : ℕ) [NeZero n]
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχsupp : HasCompactSupport χ)
    (hχsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hχD : tsupport χ ⊆ D)
    (hχbound : ∀ y, ‖χ y‖ ≤ 1)
    (K : EuclideanSpace ℝ (Fin n) → ℝ) (hK : Integrable K)
    (hKχ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      K y * χ y = K y)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ gₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (hg : AEStronglyMeasurable g volume)
    (hgₖ : ∀ k, AEStronglyMeasurable (gₖ k) volume)
    (B : ℝ) (hB₀ : 0 ≤ B)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ D → ‖g y‖ ≤ B)
    (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ D → ‖gₖ k y‖ ≤ B)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      tsupport φ ⊆ D →
        Tendsto (fun k ↦ ∫ y, φ y * gₖ k y) atTop (𝓝 (∫ y, φ y * g y)))
    (x : EuclideanSpace ℝ (Fin n))
    (hcenter : Tendsto (fun k ↦ wₖ k x) atTop (𝓝 0))
    (ρ c : ℝ) (hc : 0 ≤ c)
    (hpair : ∀ k,
      (∫ y, K y * gₖ k y) = c *
        ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          wₖ k (x + ρ • (ω : EuclideanSpace ℝ (Fin n))) ∂(volume.toSphere)) -
         (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          wₖ k x ∂(volume.toSphere)))) :
    0 ≤ ∫ y, K y * g y := by
  apply nonneg_green_pairing_of_integral_convergence n K g wₖ gₖ hwₖ_nonneg
    (tendsto_integral_mul_of_local_weak_test_convergence n D χ
      hχsupp hχsmooth hχD hχbound g gₖ hg hgₖ B hB₀ hBg hBgₖ
      hweak K hK hKχ) x hcenter ρ c hc hpair

/-- Planar Green comparison needs bounds and the distributional equation only
inside a region containing the kernel support. -/
theorem integral_normalized_planarKernel_mul_local_weakLaplacian_nonneg
    (D : Set (EuclideanSpace ℝ (Fin 2)))
    (χ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hχsupp : HasCompactSupport χ)
    (hχsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hχD : tsupport χ ⊆ D)
    (hχbound : ∀ y, ‖χ y‖ ≤ 1)
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (hg : AEStronglyMeasurable g volume)
    (B : ℝ) (hB₀ : 0 ≤ B)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      y ∈ D → ‖g y‖ ≤ B)
    (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      y ∈ D → ‖Laplacian.laplacian (wₖ k) y‖ ≤ B)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin 2) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      tsupport φ ⊆ D →
        Tendsto (fun k ↦ ∫ y, φ y * Laplacian.laplacian (wₖ k) y)
          atTop (𝓝 (∫ y, φ y * g y)))
    (x : EuclideanSpace ℝ (Fin 2))
    (hcenter : Tendsto (fun k ↦ wₖ k x) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r)
    (hKχ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal * χ y =
        ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal) :
    0 ≤ (∫ y : EuclideanSpace ℝ (Fin 2),
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal * g y) := by
  let K : EuclideanSpace ℝ (Fin 2) → ℝ := fun y ↦
    ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal
  have hK : Integrable K := (normalized_planarKernel_real_representative x hr).1
  apply nonneg_green_pairing_of_local_weak_tests 2 D χ hχsupp hχsmooth
    hχD hχbound K hK hKχ g wₖ (fun k ↦ Laplacian.laplacian (wₖ k))
    hwₖ_nonneg hg
    (fun k ↦ (continuous_laplacian 2 (wₖ k) (hwₖ k)).aestronglyMeasurable)
    B hB₀ hBg hBgₖ hweak x hcenter (r * planarGreenRadius)
    (((volume (Metric.ball x r))⁻¹).toReal * 2)
    (mul_nonneg ENNReal.toReal_nonneg (by norm_num))
  intro k
  have h := integral_normalized_planarKernel_mul_laplacian_general
    (wₖ k) (hwₖ k) (hsuppₖ k) x hr
  simpa only [K, mul_assoc, smul_smul, mul_comm r planarGreenRadius] using h

/-- Newtonian Green comparison with only interior Laplacian bounds. -/
theorem integral_normalized_newtonianKernel_mul_local_weakLaplacian_nonneg
    (n : ℕ) (hn : 3 ≤ n)
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (χ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hχsupp : HasCompactSupport χ)
    (hχsmooth : ContDiff ℝ (↑(⊤ : ℕ∞)) χ)
    (hχD : tsupport χ ⊆ D)
    (hχbound : ∀ y, ‖χ y‖ ≤ 1)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (hg : AEStronglyMeasurable g volume)
    (B : ℝ) (hB₀ : 0 ≤ B)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ D → ‖g y‖ ≤ B)
    (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ D → ‖Laplacian.laplacian (wₖ k) y‖ ≤ B)
    (hweak : ∀ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      HasCompactSupport φ → ContDiff ℝ (↑(⊤ : ℕ∞)) φ →
      tsupport φ ⊆ D →
        Tendsto (fun k ↦ ∫ y, φ y * Laplacian.laplacian (wₖ k) y)
          atTop (𝓝 (∫ y, φ y * g y)))
    (x : EuclideanSpace ℝ (Fin n))
    (hcenter : Tendsto (fun k ↦ wₖ k x) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r)
    (hKχ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal * χ y =
        ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal) :
    0 ≤ (∫ y : EuclideanSpace ℝ (Fin n),
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
        g y) := by
  letI : NeZero n := ⟨by omega⟩
  let K : EuclideanSpace ℝ (Fin n) → ℝ := fun y ↦
    ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal
  have hK : Integrable K := (normalized_newtonianKernel_real_representative n hn x hr).1
  apply nonneg_green_pairing_of_local_weak_tests n D χ hχsupp hχsmooth
    hχD hχbound K hK hKχ g wₖ (fun k ↦ Laplacian.laplacian (wₖ k))
    hwₖ_nonneg hg
    (fun k ↦ (continuous_laplacian n (wₖ k) (hwₖ k)).aestronglyMeasurable)
    B hB₀ hBg hBgₖ hweak x hcenter (r * greenRadius n)
    (((volume (Metric.ball x r))⁻¹).toReal * r ^ (n - 2) * (n : ℝ))
    (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hr.le _))
      (Nat.cast_nonneg _))
  intro k
  have h := integral_normalized_newtonianKernel_mul_laplacian_general
    n hn (wₖ k) (hwₖ k) (hsuppₖ k) x hr
  simpa only [K, mul_assoc, smul_smul, mul_comm r (greenRadius n)] using h

/-- A.e. convergence of locally capped Laplacians gives planar Green comparison
at a zero approached by nonnegative smooth obstacles. -/
theorem integral_normalized_planarKernel_mul_local_aeLaplacian_nonneg
    (D : Set (EuclideanSpace ℝ (Fin 2)))
    (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (B : ℝ)
    (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      y ∈ D → ‖Laplacian.laplacian (wₖ k) y‖ ≤ B)
    (hlimΔ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      y ∈ D → Tendsto (fun k ↦ Laplacian.laplacian (wₖ k) y) atTop (𝓝 (g y)))
    (x : EuclideanSpace ℝ (Fin 2))
    (hcenter : Tendsto (fun k ↦ wₖ k x) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r)
    (hKzero : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      y ∉ D →
        ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal = 0) :
    0 ≤ (∫ y : EuclideanSpace ℝ (Fin 2),
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal * g y) := by
  let K : EuclideanSpace ℝ (Fin 2) → ℝ := fun y ↦
    ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal
  have hK : Integrable K := (normalized_planarKernel_real_representative x hr).1
  apply nonneg_green_pairing_of_local_ae_convergence 2 D K hK hKzero g wₖ
    (fun k ↦ Laplacian.laplacian (wₖ k)) hwₖ_nonneg
    (fun k ↦ (continuous_laplacian 2 (wₖ k) (hwₖ k)).aestronglyMeasurable)
    B hBgₖ hlimΔ x hcenter (r * planarGreenRadius)
    (((volume (Metric.ball x r))⁻¹).toReal * 2)
    (mul_nonneg ENNReal.toReal_nonneg (by norm_num))
  intro k
  have h := integral_normalized_planarKernel_mul_laplacian_general
    (wₖ k) (hwₖ k) (hsuppₖ k) x hr
  simpa only [K, mul_assoc, smul_smul, mul_comm r planarGreenRadius] using h

/-- The corresponding Newtonian comparison using a.e. interior convergence of
the smooth Laplacians. -/
theorem integral_normalized_newtonianKernel_mul_local_aeLaplacian_nonneg
    (n : ℕ) (hn : 3 ≤ n)
    (D : Set (EuclideanSpace ℝ (Fin n)))
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (B : ℝ)
    (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ D → ‖Laplacian.laplacian (wₖ k) y‖ ≤ B)
    (hlimΔ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ D → Tendsto (fun k ↦ Laplacian.laplacian (wₖ k) y) atTop (𝓝 (g y)))
    (x : EuclideanSpace ℝ (Fin n))
    (hcenter : Tendsto (fun k ↦ wₖ k x) atTop (𝓝 0))
    {r : ℝ} (hr : 0 < r)
    (hKzero : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∉ D →
        ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal = 0) :
    0 ≤ (∫ y : EuclideanSpace ℝ (Fin n),
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
        g y) := by
  letI : NeZero n := ⟨by omega⟩
  let K : EuclideanSpace ℝ (Fin n) → ℝ := fun y ↦
    ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal
  have hK : Integrable K := (normalized_newtonianKernel_real_representative n hn x hr).1
  apply nonneg_green_pairing_of_local_ae_convergence n D K hK hKzero g wₖ
    (fun k ↦ Laplacian.laplacian (wₖ k)) hwₖ_nonneg
    (fun k ↦ (continuous_laplacian n (wₖ k) (hwₖ k)).aestronglyMeasurable)
    B hBgₖ hlimΔ x hcenter (r * greenRadius n)
    (((volume (Metric.ball x r))⁻¹).toReal * r ^ (n - 2) * (n : ℝ))
    (mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hr.le _))
      (Nat.cast_nonneg _))
  intro k
  have h := integral_normalized_newtonianKernel_mul_laplacian_general
    n hn (wₖ k) (hwₖ k) (hsuppₖ k) x hr
  simpa only [K, mul_assoc, smul_smul, mul_comm r (greenRadius n)] using h

end CenteredMaximal.Ball
