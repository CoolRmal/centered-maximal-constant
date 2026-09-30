/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.CompactSupportIBP
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth approximations to Euclidean ball indicators

The cutoff is identically one in a closed ball, vanishes beyond a slightly larger ball,
and is smooth even at its center because it uses the squared norm.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology

namespace CenteredMaximal.Ball

/-- A smooth cutoff which transitions from one to zero in the shell of width `δ`. -/
noncomputable def smoothBallCutoff (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (R δ : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.smoothTransition (((R + δ) ^ 2 - ‖y - x‖ ^ 2) / ((R + δ) ^ 2 - R ^ 2))

/-- The denominator in the cutoff formula is positive for positive radius and shell width. -/
theorem smoothBallCutoff_gap_pos {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    0 < (R + δ) ^ 2 - R ^ 2 := by
  nlinarith [mul_pos hR hδ, sq_pos_of_pos hδ]

/-- The squared-norm cutoff is twice continuously differentiable everywhere. -/
theorem smoothBallCutoff_contDiff (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) (R δ : ℝ) :
    ContDiff ℝ 2 (smoothBallCutoff n x R δ) := by
  unfold smoothBallCutoff
  have hsub : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => y - x) := by
    fun_prop
  have hq : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) => ‖y - x‖ ^ 2) :=
    hsub.norm_sq ℝ
  have hinner : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin n) =>
      ((R + δ) ^ 2 - ‖y - x‖ ^ 2) / ((R + δ) ^ 2 - R ^ 2)) := by
    fun_prop
  exact Real.smoothTransition.contDiff.comp hinner

/-- The cutoff is one on the original closed ball. -/
theorem smoothBallCutoff_one (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hy : y ∈ closedBall x R) : smoothBallCutoff n x R δ y = 1 := by
  unfold smoothBallCutoff
  have hnorm : ‖y - x‖ ≤ R := by
    simpa only [mem_closedBall, dist_eq_norm] using hy
  have hsq : ‖y - x‖ ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hR.le).mpr hnorm
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (smoothBallCutoff_gap_pos hR hδ)).mpr
  nlinarith

/-- The cutoff vanishes outside the enlarged ball. -/
theorem smoothBallCutoff_zero (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ)
    (hy : R + δ ≤ ‖y - x‖) : smoothBallCutoff n x R δ y = 0 := by
  unfold smoothBallCutoff
  have houter : 0 ≤ R + δ := by linarith
  have hsq : (R + δ) ^ 2 ≤ ‖y - x‖ ^ 2 :=
    (sq_le_sq₀ houter (norm_nonneg _)).mpr hy
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (smoothBallCutoff_gap_pos hR hδ).le

/-- The cutoff has compact support in the enlarged closed ball. -/
theorem smoothBallCutoff_hasCompactSupport (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    HasCompactSupport (smoothBallCutoff n x R δ) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall x (R + δ))
  intro y hy
  by_contra hball
  have hnorm : R + δ ≤ ‖y - x‖ := by
    exact le_of_lt (by simpa only [mem_closedBall, dist_eq_norm, not_le] using hball)
  exact hy (smoothBallCutoff_zero n x y hR hδ hnorm)

/-- The directional derivative of the smooth ball cutoff. The derivative is radial and
contains no singular factor at the center. -/
theorem smoothBallCutoff_fderiv (n : ℕ)
    (x y v : EuclideanSpace ℝ (Fin n)) (R δ : ℝ) :
    fderiv ℝ (smoothBallCutoff n x R δ) y v =
      -(deriv Real.smoothTransition
        (((R + δ) ^ 2 - ‖y - x‖ ^ 2) / ((R + δ) ^ 2 - R ^ 2))) *
        (2 * inner ℝ (y - x) v) / ((R + δ) ^ 2 - R ^ 2) := by
  let gap : ℝ := (R + δ) ^ 2 - R ^ 2
  let q : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun z => ((R + δ) ^ 2 - ‖z - x‖ ^ 2) / gap
  have hsub : HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => z - x)
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) y :=
    (hasFDerivAt_id y).sub_const x
  have hsq := hsub.norm_sq
  have hnum := hsq.const_sub ((R + δ) ^ 2)
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    gap⁻¹ • (-(2 • ((innerSL ℝ (y - x)).comp
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))))))
  have hq : HasFDerivAt q L y := by
    simpa only [q, div_eq_mul_inv, mul_comm] using hnum.mul_const gap⁻¹
  have htrans : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (q y)) (q y) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ 1 Real.smoothTransition).differentiable
      (by norm_num) (q y)).hasDerivAt
  have h := (htrans.comp_hasFDerivAt y hq).fderiv
  have hs : fderiv ℝ (smoothBallCutoff n x R δ) y =
      (deriv Real.smoothTransition (q y)) •
        (gap⁻¹ • (-(2 • ((innerSL ℝ (y - x)).comp
          (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))))))) := by
    change fderiv ℝ (Real.smoothTransition ∘ q) y = _
    simpa only [L] using h
  rw [hs]
  simp only [smul_apply, neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, nsmul_eq_mul]
  change (deriv Real.smoothTransition (q y)) *
    (gap⁻¹ * (-(2 * inner ℝ (y - x) v))) = _
  ring

/-- Reconstruct a directional derivative from its orthonormal coordinate derivatives. -/
theorem sum_partial_mul_inner (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (y z : EuclideanSpace ℝ (Fin n)) :
    (∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
      fderiv ℝ w y ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i) *
      inner ℝ z ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i)) =
    fderiv ℝ w y z := by
  let b := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))
  have h := congrArg (fderiv ℝ w y) (b.sum_repr' z)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  change (∑ i, fderiv ℝ w y (b i) * inner ℝ z (b i)) = _
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  simp only [real_inner_comm]
  ring

/-- The coordinate pairing with the cutoff gradient is a radial directional derivative. -/
theorem smoothBallCutoff_gradient_pair (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) (R δ : ℝ) :
    (∑ i : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
      fderiv ℝ w y ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i) *
      fderiv ℝ (smoothBallCutoff n x R δ) y
        ((stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))) i)) =
      (-(deriv Real.smoothTransition
        (((R + δ) ^ 2 - ‖y - x‖ ^ 2) / ((R + δ) ^ 2 - R ^ 2))) * 2 /
          ((R + δ) ^ 2 - R ^ 2)) *
        fderiv ℝ w y (y - x) := by
  let b := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n))
  let a : ℝ := -(deriv Real.smoothTransition
    (((R + δ) ^ 2 - ‖y - x‖ ^ 2) / ((R + δ) ^ 2 - R ^ 2))) * 2 /
      ((R + δ) ^ 2 - R ^ 2)
  simp_rw [smoothBallCutoff_fderiv]
  change (∑ i, fderiv ℝ w y (b i) *
    (-(deriv Real.smoothTransition
      (((R + δ) ^ 2 - ‖y - x‖ ^ 2) / ((R + δ) ^ 2 - R ^ 2))) *
      (2 * inner ℝ (y - x) (b i)) / ((R + δ) ^ 2 - R ^ 2))) =
    a * fderiv ℝ w y (y - x)
  rw [← sum_partial_mul_inner n w y (y - x), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [a]
  ring

/-- The finite-shell Green identity: integration of `Δw` against the smooth cutoff equals a
radial weighted integral of the derivative of `w`. Letting the shell width tend to zero gives
the Euclidean ball flux identity. -/
theorem integral_laplacian_mul_smoothBallCutoff (n : ℕ)
    (w : EuclideanSpace ℝ (Fin n) → ℝ)
    (hw : ContDiff ℝ 2 w) (hsw : HasCompactSupport w)
    (x : EuclideanSpace ℝ (Fin n)) {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    (∫ y, Laplacian.laplacian w y * smoothBallCutoff n x R δ y) =
      ∫ y, ((deriv Real.smoothTransition
        (((R + δ) ^ 2 - ‖y - x‖ ^ 2) / ((R + δ) ^ 2 - R ^ 2))) * 2 /
        ((R + δ) ^ 2 - R ^ 2)) * fderiv ℝ w y (y - x) := by
  have h := integral_laplacian_mul_eq_neg_gradient n w
    (smoothBallCutoff n x R δ) hw
    ((smoothBallCutoff_contDiff n x R δ).of_le (by norm_num))
    hsw (smoothBallCutoff_hasCompactSupport n x hR hδ)
  simp_rw [smoothBallCutoff_gradient_pair] at h
  rw [← integral_neg] at h
  apply h.trans
  apply integral_congr_ae
  filter_upwards with y
  ring

/-- The one-dimensional radial profile of `smoothBallCutoff`. -/
noncomputable def radialBallCutoff (R δ s : ℝ) : ℝ :=
  Real.smoothTransition (((R + δ) ^ 2 - s ^ 2) / ((R + δ) ^ 2 - R ^ 2))

theorem smoothBallCutoff_eq_radial (n : ℕ)
    (x y : EuclideanSpace ℝ (Fin n)) (R δ : ℝ) :
    smoothBallCutoff n x R δ y = radialBallCutoff R δ ‖y - x‖ := rfl

/-- Derivative of the radial cutoff profile. -/
theorem radialBallCutoff_hasDerivAt (R δ s : ℝ) :
    HasDerivAt (radialBallCutoff R δ)
      ((deriv Real.smoothTransition
        (((R + δ) ^ 2 - s ^ 2) / ((R + δ) ^ 2 - R ^ 2))) *
        (-(2 * s) / ((R + δ) ^ 2 - R ^ 2))) s := by
  let q : ℝ → ℝ := fun t => ((R + δ) ^ 2 - t ^ 2) / ((R + δ) ^ 2 - R ^ 2)
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * s) s := by
    simpa only [Nat.reduceSub, pow_one, Nat.cast_ofNat] using hasDerivAt_pow 2 s
  have hnum : HasDerivAt (fun t : ℝ => (R + δ) ^ 2 - t ^ 2) (-(2 * s)) s :=
    hpow.const_sub ((R + δ) ^ 2)
  have hq : HasDerivAt q (-(2 * s) / ((R + δ) ^ 2 - R ^ 2)) s :=
    hnum.div_const _
  have htrans : HasDerivAt Real.smoothTransition
      (deriv Real.smoothTransition (q s)) (q s) :=
    ((Real.smoothTransition.contDiff : ContDiff ℝ 1 Real.smoothTransition).differentiable
      (by norm_num) (q s)).hasDerivAt
  change HasDerivAt (Real.smoothTransition ∘ q) _ s
  exact htrans.comp s hq

theorem radialBallCutoff_deriv (R δ s : ℝ) :
    deriv (radialBallCutoff R δ) s =
      -(deriv Real.smoothTransition
        (((R + δ) ^ 2 - s ^ 2) / ((R + δ) ^ 2 - R ^ 2))) *
        (2 * s) / ((R + δ) ^ 2 - R ^ 2) := by
  have h := (radialBallCutoff_hasDerivAt R δ s).deriv
  convert h using 1
  ring

theorem radialBallCutoff_contDiff (R δ : ℝ) :
    ContDiff ℝ 1 (radialBallCutoff R δ) := by
  unfold radialBallCutoff
  have hinner : ContDiff ℝ 1
      (fun s : ℝ => ((R + δ) ^ 2 - s ^ 2) / ((R + δ) ^ 2 - R ^ 2)) := by
    fun_prop
  exact Real.smoothTransition.contDiff.comp hinner

theorem radialBallCutoff_inner {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    radialBallCutoff R δ R = 1 := by
  have hgap := smoothBallCutoff_gap_pos hR hδ
  simp only [radialBallCutoff, div_self hgap.ne', Real.smoothTransition.one]

theorem radialBallCutoff_outer (R δ : ℝ) :
    radialBallCutoff R δ (R + δ) = 0 := by
  simp [radialBallCutoff, Real.smoothTransition.zero]

/-- The negative derivative of the profile has total mass one in the transition shell. -/
theorem radialBallCutoff_deriv_mass {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) :
    (∫ s in R..(R + δ), -(deriv (radialBallCutoff R δ) s)) = 1 := by
  have hc := radialBallCutoff_contDiff R δ
  have hFTC : (∫ s in R..(R + δ), deriv (radialBallCutoff R δ) s) =
      radialBallCutoff R δ (R + δ) - radialBallCutoff R δ R :=
    intervalIntegral.integral_deriv_eq_sub
      (fun s _ => hc.differentiable (by norm_num) s)
      ((hc.continuous_deriv (by norm_num)).intervalIntegrable R (R + δ))
  rw [intervalIntegral.integral_neg, hFTC]
  rw [radialBallCutoff_outer, radialBallCutoff_inner hR hδ]
  ring

theorem radialBallCutoff_deriv_nonpos {R δ s : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hs : R ≤ s) :
    deriv (radialBallCutoff R δ) s ≤ 0 := by
  rw [radialBallCutoff_deriv]
  have htrans : 0 ≤ deriv Real.smoothTransition
      (((R + δ) ^ 2 - s ^ 2) / ((R + δ) ^ 2 - R ^ 2)) :=
    Real.smoothTransition.monotone.deriv_nonneg
  have hs0 : 0 ≤ s := le_trans hR.le hs
  have hgap := smoothBallCutoff_gap_pos hR hδ
  exact div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr htrans)
      (mul_nonneg (by norm_num) hs0)) hgap.le

/-- The radial profile is one up to the inner radius. -/
theorem radialBallCutoff_one_of_nonneg_le {R δ s : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hs0 : 0 ≤ s) (hsR : s ≤ R) :
    radialBallCutoff R δ s = 1 := by
  unfold radialBallCutoff
  have hsq : s^2 ≤ R^2 := (sq_le_sq₀ hs0 hR.le).mpr hsR
  apply Real.smoothTransition.one_of_one_le
  apply (one_le_div (smoothBallCutoff_gap_pos hR hδ)).mpr
  nlinarith

/-- The radial profile vanishes beyond the outer radius. -/
theorem radialBallCutoff_zero_of_outer_le {R δ s : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hs : R + δ ≤ s) :
    radialBallCutoff R δ s = 0 := by
  unfold radialBallCutoff
  have houter : 0 ≤ R + δ := by linarith
  have hsq : (R+δ)^2 ≤ s^2 := (sq_le_sq₀ houter (by linarith)).mpr hs
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (by linarith)
    (smoothBallCutoff_gap_pos hR hδ).le

/-- The radial profile has zero derivative strictly inside the ball. -/
theorem radialBallCutoff_deriv_eq_zero_inner {R δ s : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hs0 : 0 < s) (hsR : s < R) :
    deriv (radialBallCutoff R δ) s = 0 := by
  have heq : radialBallCutoff R δ =ᶠ[𝓝 s] (fun _ => 1) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hs0, hsR⟩] with t ht
    exact radialBallCutoff_one_of_nonneg_le hR hδ ht.1.le ht.2.le
  rw [heq.deriv_eq, deriv_const]

/-- The radial profile has zero derivative strictly outside the enlarged ball. -/
theorem radialBallCutoff_deriv_eq_zero_outer {R δ s : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hs : R + δ < s) :
    deriv (radialBallCutoff R δ) s = 0 := by
  have heq : radialBallCutoff R δ =ᶠ[𝓝 s] (fun _ => 0) := by
    filter_upwards [isOpen_Ioi.mem_nhds (show s ∈ Ioi (R+δ) from hs)] with t ht
    exact radialBallCutoff_zero_of_outer_le hR hδ ht.le
  rw [heq.deriv_eq, deriv_const]


/-- The smooth transition has zero derivative after reaching one. -/
theorem transition_deriv_zero_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  rcases ht.eq_or_lt with heq | hgt
  · subst t
    have hmax : IsLocalMax Real.smoothTransition 1 := by
      change ∀ᶠ s in 𝓝 (1 : ℝ), Real.smoothTransition s ≤ Real.smoothTransition 1
      filter_upwards with s
      simpa only [Real.smoothTransition.one] using Real.smoothTransition.le_one s
    exact hmax.deriv_eq_zero
  · have heq : Real.smoothTransition =ᶠ[𝓝 t] (fun _ => 1) := by
      filter_upwards [isOpen_Ioi.mem_nhds (show t ∈ Ioi (1:ℝ) from hgt)] with s hs
      exact Real.smoothTransition.one_of_one_le hs.le
    rw [heq.deriv_eq, deriv_const]

/-- The smooth transition has zero derivative before leaving zero. -/
theorem transition_deriv_zero_of_le_zero {t : ℝ} (ht : t ≤ 0) :
    deriv Real.smoothTransition t = 0 := by
  rcases ht.eq_or_lt with heq | hlt
  · subst t
    have hmin : IsLocalMin Real.smoothTransition 0 := by
      change ∀ᶠ s in 𝓝 (0 : ℝ), Real.smoothTransition 0 ≤ Real.smoothTransition s
      filter_upwards with s
      simpa only [Real.smoothTransition.zero] using Real.smoothTransition.nonneg s
    exact hmin.deriv_eq_zero
  · have heq : Real.smoothTransition =ᶠ[𝓝 t] (fun _ => 0) := by
      filter_upwards [isOpen_Iio.mem_nhds (show t ∈ Iio (0:ℝ) from hlt)] with s hs
      exact Real.smoothTransition.zero_of_nonpos hs.le
    rw [heq.deriv_eq, deriv_const]


/-- The radial cutoff derivative vanishes through the inner boundary. -/
theorem radialBallCutoff_deriv_eq_zero_inner_closed {R δ s : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hs0 : 0 ≤ s) (hsR : s ≤ R) :
    deriv (radialBallCutoff R δ) s = 0 := by
  have hsq : s^2 ≤ R^2 := (sq_le_sq₀ hs0 hR.le).mpr hsR
  have hq : 1 ≤ ((R+δ)^2-s^2)/((R+δ)^2-R^2) := by
    apply (one_le_div (smoothBallCutoff_gap_pos hR hδ)).mpr
    nlinarith
  rw [radialBallCutoff_deriv, transition_deriv_zero_of_one_le hq]
  ring

/-- The radial cutoff derivative vanishes from the outer boundary onward. -/
theorem radialBallCutoff_deriv_eq_zero_outer_closed {R δ s : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) (hs : R + δ ≤ s) :
    deriv (radialBallCutoff R δ) s = 0 := by
  have houter : 0 ≤ R + δ := by linarith
  have hsq : (R+δ)^2 ≤ s^2 := (sq_le_sq₀ houter (by linarith)).mpr hs
  have hq : ((R+δ)^2-s^2)/((R+δ)^2-R^2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith)
      (smoothBallCutoff_gap_pos hR hδ).le
  rw [radialBallCutoff_deriv, transition_deriv_zero_of_le_zero hq]
  ring


end CenteredMaximal.Ball
