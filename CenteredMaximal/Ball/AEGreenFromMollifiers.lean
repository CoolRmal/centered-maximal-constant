/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.BallKernelSupport

/-!
# Almost-everywhere Green comparisons from local smooth approximants

The center set where nonnegative mollifiers converge to a zero of the obstacle
is independent of the radius. A single interior cutoff contains all Green
supports in the maximal-function transfer region.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Filter
open scoped ENNReal Topology

namespace CenteredMaximal.Ball

/-- The planar Green pairing is nonnegative for almost every center outside
the obstacle's contact set and for every radius in the transfer range. -/
theorem ae_planar_green_pairing_nonneg_of_local_mollifiers
    (R r₀ : ℝ) (hr₀ : 0 < r₀)
    (Ω : Set (EuclideanSpace ℝ (Fin 2)))
    (u g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin 2) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (hlimw : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      Tendsto (fun k ↦ wₖ k x) atTop (𝓝 (u x)))
    (hzero : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      x ∉ Ω → u x = 0)
    (B : ℝ)
    (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      y ∈ greenCutoffDomain 2 R r₀ planarGreenRadius →
        ‖Laplacian.laplacian (wₖ k) y‖ ≤ B)
    (hlimΔ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      y ∈ greenCutoffDomain 2 R r₀ planarGreenRadius →
        Tendsto (fun k ↦ Laplacian.laplacian (wₖ k) y) atTop (𝓝 (g y))) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      x ∉ Ω → ‖x‖ < R + r₀ → ∀ r : ℝ, 0 < r → r < r₀ →
        0 ≤ (∫ y : EuclideanSpace ℝ (Fin 2),
          ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal *
            g y) := by
  have hG : 0 ≤ planarGreenRadius := by unfold planarGreenRadius; positivity
  filter_upwards [hlimw, hzero] with x hxlim hxzero
  intro hxΩ hxR r hr hrr₀
  let D := greenCutoffDomain 2 R r₀ planarGreenRadius
  let χ := greenCutoff 2 R r₀ planarGreenRadius
  let K : EuclideanSpace ℝ (Fin 2) → ℝ := fun y ↦
    ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal
  have hχD : tsupport χ ⊆ D :=
    greenCutoff_tsupport_subset_domain 2 hr₀ hG
  have hKχ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      K y * χ y = K y := by
    filter_upwards with y
    exact normalized_planarKernel_mul_greenCutoff hr₀ x hxR hr hrr₀ y
  have hKzero : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      y ∉ D → K y = 0 :=
    kernel_zero_outside_of_mul_cutoff_eq_self 2 D χ K hχD hKχ
  exact integral_normalized_planarKernel_mul_local_aeLaplacian_nonneg D g wₖ
    hwₖ hsuppₖ hwₖ_nonneg B hBgₖ hlimΔ x
    (by simpa only [hxzero hxΩ] using hxlim) hr hKzero

/-- The same conclusion for the Newtonian kernel in dimensions at least three. -/
theorem ae_newtonian_green_pairing_nonneg_of_local_mollifiers
    (n : ℕ) (hn : 3 ≤ n)
    (R r₀ : ℝ) (hr₀ : 0 < r₀)
    (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (u g : EuclideanSpace ℝ (Fin n) → ℝ)
    (wₖ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ)
    (hwₖ : ∀ k, ContDiff ℝ 2 (wₖ k))
    (hsuppₖ : ∀ k, HasCompactSupport (wₖ k))
    (hwₖ_nonneg : ∀ k y, 0 ≤ wₖ k y)
    (hlimw : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun k ↦ wₖ k x) atTop (𝓝 (u x)))
    (hzero : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∉ Ω → u x = 0)
    (B : ℝ)
    (hBgₖ : ∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ greenCutoffDomain n R r₀ (greenRadius n) →
        ‖Laplacian.laplacian (wₖ k) y‖ ≤ B)
    (hlimΔ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ greenCutoffDomain n R r₀ (greenRadius n) →
        Tendsto (fun k ↦ Laplacian.laplacian (wₖ k) y) atTop (𝓝 (g y))) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      x ∉ Ω → ‖x‖ < R + r₀ → ∀ r : ℝ, 0 < r → r < r₀ →
        0 ≤ (∫ y : EuclideanSpace ℝ (Fin n),
          ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
            g y) := by
  have hG : 0 ≤ greenRadius n := (greenRadius_pos n hn).le
  filter_upwards [hlimw, hzero] with x hxlim hxzero
  intro hxΩ hxR r hr hrr₀
  let D := greenCutoffDomain n R r₀ (greenRadius n)
  let χ := greenCutoff n R r₀ (greenRadius n)
  let K : EuclideanSpace ℝ (Fin n) → ℝ := fun y ↦
    ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal
  have hχD : tsupport χ ⊆ D :=
    greenCutoff_tsupport_subset_domain n hr₀ hG
  have hKχ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      K y * χ y = K y := by
    filter_upwards with y
    exact normalized_newtonianKernel_mul_greenCutoff n hn hr₀ x hxR hr hrr₀ y
  have hKzero : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∉ D → K y = 0 :=
    kernel_zero_outside_of_mul_cutoff_eq_self n D χ K hχD hKχ
  exact integral_normalized_newtonianKernel_mul_local_aeLaplacian_nonneg n hn D g wₖ
    hwₖ hsuppₖ hwₖ_nonneg B hBgₖ hlimΔ x
    (by simpa only [hxzero hxΩ] using hxlim) hr hKzero

end CenteredMaximal.Ball
