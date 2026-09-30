/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.GreenPairing
public import CenteredMaximal.Ball.BallFlux

/-!
# Green pairing at an arbitrary scale

This file transfers the unit-scale Green identities to normalized kernels at every
positive radius.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace CenteredMaximal.Ball

private theorem laplacian_comp_add_smul (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (x z : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    Laplacian.laplacian (fun v ↦ w (x + r • v)) z =
      r ^ 2 * Laplacian.laplacian w (x + r • z) := by
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun v ↦ w (x + v)
  have hf : ContDiff ℝ 2 f := hw.comp ((contDiff_const.add contDiff_id))
  have hscale := iteratedFDeriv_comp_const_smul r hf
  have htrans := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := w) 2 x
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  change (∑ i, iteratedFDeriv ℝ 2 (fun v ↦ f (r • v)) z
    ![(stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i,
      (stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i]) = _
  rw [congrArg (fun g ↦ g z) hscale]
  simp only [smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [show iteratedFDeriv ℝ 2 f (r • z) =
      iteratedFDeriv ℝ 2 w (x + r • z) from htrans (r • z)]

private theorem contDiff_comp_add_smul (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    ContDiff ℝ 2 (fun z ↦ w (x + r • z)) := by
  fun_prop

private theorem hasCompactSupport_comp_add_smul (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : HasCompactSupport w)
    (x : EuclideanSpace ℝ (Fin n)) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (fun z ↦ w (x + r • z)) := by
  convert hw.comp_homeomorph
      ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft x)) using 1
  funext z
  simp

/-- The signed radial pairing scales by `r^(n−2)` under an affine dilation. This
form with `r²` on the left avoids division and works in every dimension. -/
private theorem integral_scaled_radial_mul_laplacian (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (x : EuclideanSpace ℝ (Fin n)) (φ : ℝ → ℝ)
    {r : ℝ} (hr : 0 < r) :
    r ^ 2 * (∫ y : EuclideanSpace ℝ (Fin n),
        φ (‖y - x‖ / r) * Laplacian.laplacian w y) =
      r ^ n * (∫ z : EuclideanSpace ℝ (Fin n),
        φ ‖z‖ * Laplacian.laplacian (fun v ↦ w (x + r • v)) z) := by
  let v : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦ w (x + r • z)
  let H : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦
    φ ‖z‖ * Laplacian.laplacian v z
  have hchange : (∫ y : EuclideanSpace ℝ (Fin n), H (r⁻¹ • (y - x))) =
      r ^ n * ∫ z, H z := by
    calc
      (∫ y : EuclideanSpace ℝ (Fin n), H (r⁻¹ • (y - x))) =
          ∫ y, H (r⁻¹ • y) := by
        exact integral_sub_right_eq_self (fun y ↦ H (r⁻¹ • y)) x
      _ = r ^ n * ∫ z, H z := by
        simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using
          Measure.integral_comp_inv_smul_of_nonneg (μ := volume) H hr.le
  calc
    r ^ 2 * (∫ y : EuclideanSpace ℝ (Fin n),
        φ (‖y - x‖ / r) * Laplacian.laplacian w y) =
        ∫ y : EuclideanSpace ℝ (Fin n), H (r⁻¹ • (y - x)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      have hnorm : ‖r⁻¹ • (y - x)‖ = ‖y - x‖ / r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
        rw [inv_mul_eq_div]
      simp only [H, v, hnorm, laplacian_comp_add_smul n w hw x]
      rw [smul_inv_smul₀ hr.ne']
      have hxy : x + (y - x) = y := by abel
      rw [hxy]
      ring
    _ = r ^ n * (∫ z : EuclideanSpace ℝ (Fin n),
        φ ‖z‖ * Laplacian.laplacian (fun v ↦ w (x + r • v)) z) := hchange

/-- The normalized planar kernel has a nonnegative Green pairing at every radius,
expressed exactly as a positive multiple of the spherical value. The geometric
ball flux formula is the only remaining premise. -/
theorem integral_normalized_planarKernel_mul_laplacian_of_ball_flux_general
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 < r)
    (hflux : ∀ s ∈ Set.Ioc (0 : ℝ) planarGreenRadius,
      (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) s,
        Laplacian.laplacian (fun z ↦ w (x + r • z)) y) =
        s * (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          fderiv ℝ (fun z ↦ w (x + r • z))
            (s • (ω : EuclideanSpace ℝ (Fin 2)))
            (ω : EuclideanSpace ℝ (Fin 2)) ∂(volume.toSphere))) :
    (∫ y : EuclideanSpace ℝ (Fin 2),
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) =
      ((volume (Metric.ball x r))⁻¹).toReal *
        (2 * ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          w (x + r • (planarGreenRadius • (ω : EuclideanSpace ℝ (Fin 2))))
            ∂(volume.toSphere)) -
          (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
            w x ∂(volume.toSphere)))) := by
  let v : EuclideanSpace ℝ (Fin 2) → ℝ := fun z ↦ w (x + r • z)
  have hv : ContDiff ℝ 2 v := contDiff_comp_add_smul 2 w hw x r
  have hvsupp : HasCompactSupport v := hasCompactSupport_comp_add_smul 2 w hsupp x hr
  have hunit := integral_planarGreenProfile_posPart_mul_laplacian_of_ball_flux_general
    v hv hvsupp 0 (by simpa only [zero_add, v] using hflux)
  simp only [sub_zero, zero_add, v, smul_zero, add_zero] at hunit
  have hscale := integral_scaled_radial_mul_laplacian 2 w hw x
    (fun t ↦ max (planarGreenProfile t) 0) hr
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
  have hprofile :
      (∫ y : EuclideanSpace ℝ (Fin 2),
        max (planarGreenProfile (‖y - x‖ / r)) 0 *
          Laplacian.laplacian w y) =
        2 * ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          w (x + r • (planarGreenRadius • (ω : EuclideanSpace ℝ (Fin 2))))
            ∂(volume.toSphere)) -
          (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
            w x ∂(volume.toSphere))) := by
    have hbase := (mul_left_cancel₀ hr2 hscale)
    rw [hbase]
    exact hunit
  calc
    (∫ y : EuclideanSpace ℝ (Fin 2),
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) =
      ∫ y : EuclideanSpace ℝ (Fin 2),
        ((volume (Metric.ball x r))⁻¹).toReal *
          (max (planarGreenProfile (‖y - x‖ / r)) 0 *
            Laplacian.laplacian w y) := by
        apply integral_congr_ae
        filter_upwards [normalized_planarKernel_toReal_ae_eq_profile x hr] with y hy
        rw [hy]
        ring
    _ = _ := by rw [integral_const_mul, hprofile]

/-- At a zero of the obstacle, the normalized planar Green pairing is its positive
spherical value. -/
theorem integral_normalized_planarKernel_mul_laplacian_of_ball_flux
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin 2))
    (hx : w x = 0) {r : ℝ} (hr : 0 < r)
    (hflux : ∀ s ∈ Set.Ioc (0 : ℝ) planarGreenRadius,
      (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) s,
        Laplacian.laplacian (fun z ↦ w (x + r • z)) y) =
        s * (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          fderiv ℝ (fun z ↦ w (x + r • z))
            (s • (ω : EuclideanSpace ℝ (Fin 2)))
            (ω : EuclideanSpace ℝ (Fin 2)) ∂(volume.toSphere))) :
    (∫ y : EuclideanSpace ℝ (Fin 2),
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) =
      ((volume (Metric.ball x r))⁻¹).toReal *
        (2 * (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          w (x + r • (planarGreenRadius • (ω : EuclideanSpace ℝ (Fin 2))))
            ∂(volume.toSphere))) := by
  simpa only [hx, integral_zero, sub_zero] using
    integral_normalized_planarKernel_mul_laplacian_of_ball_flux_general
      w hw hsupp x hr hflux

/-- The arbitrary-radius Newtonian pairing. Its coefficient is the dilation
factor `r^(n−2)` times the normalized kernel density. -/
theorem integral_normalized_newtonianKernel_mul_laplacian_of_ball_flux_general
    (n : ℕ) (hn : 3 ≤ n)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r)
    (hflux : ∀ s ∈ Set.Ioc (0 : ℝ) (greenRadius n),
      (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        Laplacian.laplacian (fun z ↦ w (x + r • z)) y) =
        s ^ (n - 1) *
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            fderiv ℝ (fun z ↦ w (x + r • z))
              (s • (ω : EuclideanSpace ℝ (Fin n)))
              (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere))) :
    (∫ y : EuclideanSpace ℝ (Fin n),
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) =
      ((volume (Metric.ball x r))⁻¹).toReal * r ^ (n - 2) *
        ((n : ℝ) * ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          w (x + r • (greenRadius n • (ω : EuclideanSpace ℝ (Fin n))))
            ∂(volume.toSphere)) -
          (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            w x ∂(volume.toSphere)))) := by
  letI : NeZero n := ⟨by omega⟩
  let v : EuclideanSpace ℝ (Fin n) → ℝ := fun z ↦ w (x + r • z)
  have hv : ContDiff ℝ 2 v := contDiff_comp_add_smul n w hw x r
  have hvsupp : HasCompactSupport v := hasCompactSupport_comp_add_smul n w hsupp x hr
  have hunit := integral_newtonianGreenProfile_posPart_mul_laplacian_of_ball_flux_general
    n hn v hv hvsupp 0 (by simpa only [zero_add, v] using hflux)
  simp only [sub_zero, zero_add, v, smul_zero, add_zero] at hunit
  have hscale := integral_scaled_radial_mul_laplacian n w hw x
    (fun t ↦ max (newtonianGreenProfile n t) 0) hr
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr.ne'
  have hpow : r ^ n = r ^ 2 * r ^ (n - 2) := by
    rw [← pow_add]
    congr 1
    omega
  have hprofile :
      (∫ y : EuclideanSpace ℝ (Fin n),
        max (newtonianGreenProfile n (‖y - x‖ / r)) 0 *
          Laplacian.laplacian w y) =
        r ^ (n - 2) * ((n : ℝ) *
          ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            w (x + r • (greenRadius n • (ω : EuclideanSpace ℝ (Fin n))))
              ∂(volume.toSphere)) -
            (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
              w x ∂(volume.toSphere)))) := by
    rw [hpow, mul_assoc] at hscale
    have hbase := (mul_left_cancel₀ hr2 hscale)
    rw [hbase]
    rw [hunit]
  calc
    (∫ y : EuclideanSpace ℝ (Fin n),
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) =
      ∫ y : EuclideanSpace ℝ (Fin n),
        ((volume (Metric.ball x r))⁻¹).toReal *
          (max (newtonianGreenProfile n (‖y - x‖ / r)) 0 *
            Laplacian.laplacian w y) := by
        apply integral_congr_ae
        filter_upwards [normalized_newtonianKernel_toReal_ae_eq_profile n hn x hr]
          with y hy
        rw [hy]
        ring
    _ = _ := by rw [integral_const_mul, hprofile]; ring

/-- At a zero of the obstacle, the normalized Newtonian Green pairing is its
positive spherical value. -/
theorem integral_normalized_newtonianKernel_mul_laplacian_of_ball_flux
    (n : ℕ) (hn : 3 ≤ n)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin n))
    (hx : w x = 0) {r : ℝ} (hr : 0 < r)
    (hflux : ∀ s ∈ Set.Ioc (0 : ℝ) (greenRadius n),
      (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        Laplacian.laplacian (fun z ↦ w (x + r • z)) y) =
        s ^ (n - 1) *
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            fderiv ℝ (fun z ↦ w (x + r • z))
              (s • (ω : EuclideanSpace ℝ (Fin n)))
              (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere))) :
    (∫ y : EuclideanSpace ℝ (Fin n),
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) =
      ((volume (Metric.ball x r))⁻¹).toReal * r ^ (n - 2) *
        ((n : ℝ) * (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          w (x + r • (greenRadius n • (ω : EuclideanSpace ℝ (Fin n))))
            ∂(volume.toSphere))) := by
  simpa only [hx, integral_zero, sub_zero] using
    integral_normalized_newtonianKernel_mul_laplacian_of_ball_flux_general
      n hn w hw hsupp x hr hflux

/-- A nonnegative obstacle vanishing at the center has nonnegative planar
Green pairing at every scale. -/
theorem integral_normalized_planarKernel_mul_laplacian_nonneg_of_ball_flux
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hw₀ : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : w x = 0)
    {r : ℝ} (hr : 0 < r)
    (hflux : ∀ s ∈ Set.Ioc (0 : ℝ) planarGreenRadius,
      (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) s,
        Laplacian.laplacian (fun z ↦ w (x + r • z)) y) =
        s * (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          fderiv ℝ (fun z ↦ w (x + r • z))
            (s • (ω : EuclideanSpace ℝ (Fin 2)))
            (ω : EuclideanSpace ℝ (Fin 2)) ∂(volume.toSphere))) :
    0 ≤ (∫ y : EuclideanSpace ℝ (Fin 2),
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) := by
  rw [integral_normalized_planarKernel_mul_laplacian_of_ball_flux
    w hw hsupp x hx hr hflux]
  exact mul_nonneg ENNReal.toReal_nonneg
    (mul_nonneg (by norm_num) (integral_nonneg fun ω ↦ hw₀ _))

/-- A nonnegative obstacle vanishing at the center has nonnegative Newtonian
Green pairing at every scale. -/
theorem integral_normalized_newtonianKernel_mul_laplacian_nonneg_of_ball_flux
    (n : ℕ) (hn : 3 ≤ n)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hw₀ : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin n)) (hx : w x = 0)
    {r : ℝ} (hr : 0 < r)
    (hflux : ∀ s ∈ Set.Ioc (0 : ℝ) (greenRadius n),
      (∫ y in Metric.ball (0 : EuclideanSpace ℝ (Fin n)) s,
        Laplacian.laplacian (fun z ↦ w (x + r • z)) y) =
        s ^ (n - 1) *
          (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            fderiv ℝ (fun z ↦ w (x + r • z))
              (s • (ω : EuclideanSpace ℝ (Fin n)))
              (ω : EuclideanSpace ℝ (Fin n)) ∂(volume.toSphere))) :
    0 ≤ (∫ y : EuclideanSpace ℝ (Fin n),
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) := by
  rw [integral_normalized_newtonianKernel_mul_laplacian_of_ball_flux
    n hn w hw hsupp x hx hr hflux]
  exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hr.le _))
    (mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun ω ↦ hw₀ _))

/-- The exact planar Green pairing at any radius, with the Euclidean ball flux
identity discharged. -/
theorem integral_normalized_planarKernel_mul_laplacian_general
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin 2))
    {r : ℝ} (hr : 0 < r) :
    (∫ y : EuclideanSpace ℝ (Fin 2),
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) =
      ((volume (Metric.ball x r))⁻¹).toReal *
        (2 * ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
          w (x + r • (planarGreenRadius • (ω : EuclideanSpace ℝ (Fin 2))))
            ∂(volume.toSphere)) -
          (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
            w x ∂(volume.toSphere)))) := by
  apply integral_normalized_planarKernel_mul_laplacian_of_ball_flux_general
    w hw hsupp x hr
  intro s hs
  have hv : ContDiff ℝ 2 (fun z ↦ w (x + r • z)) :=
    contDiff_comp_add_smul 2 w hw x r
  have hvsupp : HasCompactSupport (fun z ↦ w (x + r • z)) :=
    hasCompactSupport_comp_add_smul 2 w hsupp x hr
  simpa only [Nat.reduceSub, pow_one, zero_add] using
    integral_laplacian_ball_eq_sphere_flux 2 _ hv hvsupp 0 hs.1

/-- The exact Newtonian Green pairing at any radius, with ball flux discharged. -/
theorem integral_normalized_newtonianKernel_mul_laplacian_general
    (n : ℕ) (hn : 3 ≤ n)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (x : EuclideanSpace ℝ (Fin n))
    {r : ℝ} (hr : 0 < r) :
    (∫ y : EuclideanSpace ℝ (Fin n),
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) =
      ((volume (Metric.ball x r))⁻¹).toReal * r ^ (n - 2) *
        ((n : ℝ) * ((∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
          w (x + r • (greenRadius n • (ω : EuclideanSpace ℝ (Fin n))))
            ∂(volume.toSphere)) -
          (∫ _ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
            w x ∂(volume.toSphere)))) := by
  letI : NeZero n := ⟨by omega⟩
  apply integral_normalized_newtonianKernel_mul_laplacian_of_ball_flux_general
    n hn w hw hsupp x hr
  intro s hs
  have hv : ContDiff ℝ 2 (fun z ↦ w (x + r • z)) :=
    contDiff_comp_add_smul n w hw x r
  have hvsupp : HasCompactSupport (fun z ↦ w (x + r • z)) :=
    hasCompactSupport_comp_add_smul n w hsupp x hr
  simpa only [zero_add] using
    integral_laplacian_ball_eq_sphere_flux n _ hv hvsupp 0 hs.1

/-- At a zero of a nonnegative smooth obstacle, every normalized planar Green
pairing with its Laplacian is nonnegative. -/
theorem integral_normalized_planarKernel_mul_laplacian_nonneg
    (w : EuclideanSpace ℝ (Fin 2) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hw₀ : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : w x = 0)
    {r : ℝ} (hr : 0 < r) :
    0 ≤ (∫ y : EuclideanSpace ℝ (Fin 2),
      ((volume (Metric.ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) := by
  rw [integral_normalized_planarKernel_mul_laplacian_general w hw hsupp x hr]
  simp only [hx, integral_zero, sub_zero]
  exact mul_nonneg ENNReal.toReal_nonneg
    (mul_nonneg (by norm_num) (integral_nonneg fun ω ↦ hw₀ _))

/-- At a zero of a nonnegative smooth obstacle, every normalized Newtonian
Green pairing with its Laplacian is nonnegative. -/
theorem integral_normalized_newtonianKernel_mul_laplacian_nonneg
    (n : ℕ) (hn : 3 ≤ n)
    (w : EuclideanSpace ℝ (Fin n) → ℝ) (hw : ContDiff ℝ 2 w)
    (hsupp : HasCompactSupport w) (hw₀ : ∀ y, 0 ≤ w y)
    (x : EuclideanSpace ℝ (Fin n)) (hx : w x = 0)
    {r : ℝ} (hr : 0 < r) :
    0 ≤ (∫ y : EuclideanSpace ℝ (Fin n),
      ((volume (Metric.ball x r))⁻¹ * newtonianKernel n (r⁻¹ • (x - y))).toReal *
        Laplacian.laplacian w y) := by
  rw [integral_normalized_newtonianKernel_mul_laplacian_general n hn w hw hsupp x hr]
  simp only [hx, integral_zero, sub_zero]
  exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg (pow_nonneg hr.le _))
    (mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun ω ↦ hw₀ _))

end CenteredMaximal.Ball
