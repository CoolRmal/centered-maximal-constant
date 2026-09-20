/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.JumpGenerator
public import CenteredMaximal.Cauchy.LooseKernel
public import Mathlib.Analysis.Convex.Mul
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The generator density of the truncated Cauchy potential inside its support

Fix `R > 1` (the project uses `R = looseRadius = 3797/2000`). Truncating the potential of the
coordinate Cauchy generator at the diamond of radius `R` leaves the *exterior tail*

`tail R z = (1 − R / r(z))₊ / (R − 1)`,   `r = diamondNorm`,

which vanishes on the closed diamond `{r ≤ R}` and equals `(1 − R/r)/(R − 1)` outside it. This
file computes the jump generator `jumpGen 1 (tail R)` of the tail *inside* the open diamond, where
`tail R z = 0`, so that the second difference is a sum of two nonnegative boundary terms.

Writing `u = |z 0|`, `v = |z 1|`, `r = u + v` and `d = u − v`, substituting the diamond radius
`q = r(z ± s e_j)` of the displaced point for the step `s` turns the four one-dimensional
integrals into half-line integrals of the radial profile against an inverse square. With

`tailF R c = ∫_R^∞ (1 − R/q) (q − c)^{−2} dq`

the outcome is the exact identity `jumpGen_tail_eq`,

`jumpGen 1 (tail R) z = 2 (2 tailF R r + tailF R d + tailF R (−d)) / (R − 1)`,

each of the two "outward" directions contributing `tailF R r` and the two "inward" ones
`tailF R d` and `tailF R (−d)`.

The scalar integral is elementary: by partial fractions
`(q − R) / (q (q − c)²) = −(R/c²)/q + (R/c²)/(q − c) + ((c − R)/c)/(q − c)²`, so
`(R/c²) log(1 − c/q) + ((R − c)/c) (q − c)⁻¹` is an antiderivative, and since the integrand is
nonnegative on `(R, ∞)` the improper fundamental theorem of calculus supplies both integrability
and the value: `integral_Ioi_tail_div_sq` gives `tailF R c = −(R/c²) log(1 − c/R) − 1/c` for
`c ≠ 0`, and `integral_Ioi_tail_div_sq_zero` gives `tailF R 0 = 1/(2R)`. The inward pair is
minimised at `d = 0`, because `2/q² ≤ (q − d)^{−2} + (q + d)^{−2}` for `|d| < q`; together with
`tailF R r ≥ 0` this yields the lower bound

`jumpGen_tail_ge_sharp : jumpGen 1 (tail R) z ≥ 4 ((−(R/r²) log(1 − r/R) − 1/r) + 1/(2R))/(R − 1)`

Nothing but the inward pair is estimated there, so the bound is attained whenever `|z 0| = |z 1|`;
`jumpGen_tail_ge`, half of it, is kept for the callers using that normalisation. In the
scale-invariant variable `s = 2r/R` the sharp bound reads `(4/(R (R − 1))) J(s)` with
`J s = 1/2 − 2/s − (4/s²) log(1 − s/2)`, by `jumpGen_tail_ge_Jfun_sharp` through the algebraic
identity `jumpGen_tail_ge_Jfun`. Since all terms of the power series of `−log(1 − s/2)` are
nonnegative, its first two already give `one_le_Jfun : 1 ≤ J s` on `(0, 2)`; discarding those two
and dividing by `(s/2)²` expands `J` itself as a series with positive coefficients,
`Jfun_eq_tsum : J s = 1 + ∑_k s^{k+1} / (2^{k+1} (k + 3))`, from which
`Jfun_convexOn : ConvexOn ℝ (Ioo 0 2) J` follows term by term out of the convexity of
`t ↦ t^{k+1}` on `[0, ∞)`.

At the origin Lean evaluates `R / 0 = 0`, so `tail R 0 = 1/(R − 1)` although the tail is meant to
vanish there; the pointwise lemmas therefore assume `0 < diamondNorm z`, exactly as in
`LooseKernel`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set

open scoped Topology

namespace CenteredMaximal.Cauchy

variable {R : ℝ}

/-- The radial profile `(1 − R/q)₊ / (R − 1)` of the exterior tail. -/
def tailProfile (R q : ℝ) : ℝ := max (1 - R / q) 0 / (R - 1)

/-- The exterior tail of the potential truncated at radius `R`: it vanishes on the closed diamond
`{r ≤ R}` and equals `(1 − R/r)/(R − 1)` outside it. At `z = 0` Lean evaluates `R / 0 = 0`, so the
value is `1/(R − 1)`; the origin is a null set, so nothing is lost in the integrals. -/
def tail (R : ℝ) (z : Fin 2 → ℝ) : ℝ := max (1 - R / diamondNorm z) 0 / (R - 1)

/-- The scalar half-line integral `∫_R^∞ (1 − R/q) (q − c)^{−2} dq`. -/
def tailF (R c : ℝ) : ℝ := ∫ q in Ioi R, (1 - R / q) / (q - c) ^ 2

/-- The shape function `J(s) = 1/2 − 2/s − (4/s²) log(1 − s/2)` of the generator density. -/
def Jfun (s : ℝ) : ℝ := 1 / 2 - 2 / s - 4 / s ^ 2 * Real.log (1 - s / 2)

/-! ### The radial profile of the tail -/

theorem tail_eq (R : ℝ) (z : Fin 2 → ℝ) : tail R z = tailProfile R (diamondNorm z) := rfl

theorem tailProfile_nonneg (hR : 1 < R) (q : ℝ) : 0 ≤ tailProfile R q :=
  div_nonneg (le_max_right _ _) (sub_nonneg.2 hR.le)

/-- The profile vanishes on `(0, R]`. -/
theorem tailProfile_eq_zero {q : ℝ} (hq : 0 < q) (hqR : q ≤ R) :
    tailProfile R q = 0 := by
  rw [tailProfile, max_eq_right (by rw [sub_nonpos, le_div_iff₀ hq, one_mul]; exact hqR), zero_div]

/-- Outside the diamond the profile is `(1 − R/q)/(R − 1)`. -/
theorem tailProfile_of_lt (hR : 1 < R) {q : ℝ} (hqR : R < q) :
    tailProfile R q = (1 - R / q) / (R - 1) := by
  have hq : 0 < q := by linarith
  rw [tailProfile, max_eq_left (by rw [sub_nonneg, div_le_one hq]; exact hqR.le)]

theorem measurable_tailProfile (R : ℝ) : Measurable (tailProfile R) := by
  unfold tailProfile
  fun_prop

/-- The tail vanishes on the punctured closed diamond. -/
theorem tail_eq_zero {z : Fin 2 → ℝ} (hz : 0 < diamondNorm z)
    (hzR : diamondNorm z ≤ R) : tail R z = 0 :=
  tailProfile_eq_zero hz hzR

/-! ### The scalar half-line integral -/

/-- The integrand of `tailF` has a nonnegative numerator on `(R, ∞)`. -/
private theorem one_sub_div_nonneg (hR : 1 < R) {q : ℝ} (hq : R < q) : 0 ≤ 1 - R / q := by
  rw [sub_nonneg, div_le_one (by linarith : (0 : ℝ) < q)]
  exact hq.le

/-- `(R/c²) log(1 − c/q) + ((R − c)/c) (q − c)⁻¹` is an antiderivative of `(1 − R/q)(q − c)^{−2}`
on `[R, ∞)`. -/
private theorem hasDerivAt_tailAnti (hR : 1 < R) {c : ℝ} (hc : |c| < R) (hc0 : c ≠ 0) {q : ℝ}
    (hq : R ≤ q) :
    HasDerivAt (fun p : ℝ => R / c ^ 2 * Real.log (1 - c / p) + (R - c) / c * (p - c)⁻¹)
      ((1 - R / q) / (q - c) ^ 2) q := by
  obtain ⟨hc₁, hc₂⟩ := abs_lt.1 hc
  have hq0 : 0 < q := lt_of_lt_of_le (by linarith) hq
  have hqc : 0 < q - c := by linarith
  have hq0' : q ≠ 0 := hq0.ne'
  have hqc' : q - c ≠ 0 := hqc.ne'
  have hu : 1 - c / q = (q - c) / q := by field_simp
  have hu0 : 1 - c / q ≠ 0 := by rw [hu]; exact div_ne_zero hqc' hq0'
  have hd : HasDerivAt (fun p : ℝ => 1 - c / p) (c / q ^ 2) q :=
    (((hasDerivAt_const q c).div (hasDerivAt_id q) hq0').const_sub 1).congr_deriv
      (by simp only [id_eq]; ring)
  have h1 : HasDerivAt (fun p : ℝ => Real.log (1 - c / p)) (c / q ^ 2 / (1 - c / q)) q :=
    hd.log hu0
  have h2 : HasDerivAt (fun p : ℝ => (p - c)⁻¹) (-1 / (q - c) ^ 2) q :=
    ((hasDerivAt_id q).sub_const c).inv hqc'
  refine ((h1.const_mul (R / c ^ 2)).add (h2.const_mul ((R - c) / c))).congr_deriv ?_
  rw [hu]
  field_simp
  ring

/-- The antiderivative of `hasDerivAt_tailAnti` tends to `0` at infinity. -/
private theorem tendsto_tailAnti {c : ℝ} :
    Tendsto (fun p : ℝ => R / c ^ 2 * Real.log (1 - c / p) + (R - c) / c * (p - c)⁻¹) atTop
      (𝓝 0) := by
  have hinv : Tendsto (fun p : ℝ => p⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h₀ : Tendsto (fun p : ℝ => 1 - c / p) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_id.const_div_atTop c)
  have h₁ : Tendsto (fun p : ℝ => Real.log (1 - c / p)) atTop (𝓝 0) := by
    simpa using h₀.log one_ne_zero
  have hsub : Tendsto (fun p : ℝ => p - c) atTop atTop := by
    simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-c) tendsto_id
  have h₂ : Tendsto (fun p : ℝ => (p - c)⁻¹) atTop (𝓝 0) := hsub.inv_tendsto_atTop
  simpa using (h₁.const_mul (R / c ^ 2)).add (h₂.const_mul ((R - c) / c))

/-- `−p⁻¹ + (R/2) p⁻¹ p⁻¹` is an antiderivative of `(1 − R/q) q^{−2}` on `[R, ∞)`. -/
private theorem hasDerivAt_tailAntiZero (hR : 1 < R) {q : ℝ} (hq : R ≤ q) :
    HasDerivAt (fun p : ℝ => -p⁻¹ + R / 2 * (p⁻¹ * p⁻¹)) ((1 - R / q) / q ^ 2) q := by
  have hq0 : 0 < q := lt_of_lt_of_le (by linarith) hq
  have hq0' : q ≠ 0 := hq0.ne'
  have h1 : HasDerivAt (fun p : ℝ => -p⁻¹) (-(-(q ^ 2)⁻¹)) q := (hasDerivAt_inv hq0').neg
  have h2 : HasDerivAt (fun p : ℝ => p⁻¹ * p⁻¹)
      (-(q ^ 2)⁻¹ * q⁻¹ + q⁻¹ * -(q ^ 2)⁻¹) q :=
    (hasDerivAt_inv hq0').mul (hasDerivAt_inv hq0')
  refine (h1.add (h2.const_mul (R / 2))).congr_deriv ?_
  field_simp
  ring

/-- The antiderivative of `hasDerivAt_tailAntiZero` tends to `0` at infinity. -/
private theorem tendsto_tailAntiZero :
    Tendsto (fun p : ℝ => -p⁻¹ + R / 2 * (p⁻¹ * p⁻¹)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun p : ℝ => p⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h1 : Tendsto (fun p : ℝ => -p⁻¹) atTop (𝓝 0) := by simpa using hinv.neg
  have h2 : Tendsto (fun p : ℝ => p⁻¹ * p⁻¹) atTop (𝓝 0) := by simpa using hinv.mul hinv
  simpa using h1.add (h2.const_mul (R / 2))

/-- The integrand of `tailF` is integrable on the half-line `(R, ∞)`. -/
theorem integrableOn_tail_div_sq (hR : 1 < R) {c : ℝ} (hc : |c| < R) :
    IntegrableOn (fun q => (1 - R / q) / (q - c) ^ 2) (Ioi R) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · have h := integrableOn_Ioi_deriv_of_nonneg' (fun q hq => hasDerivAt_tailAntiZero hR hq)
      (fun q hq => div_nonneg (one_sub_div_nonneg hR hq) (sq_nonneg _)) tendsto_tailAntiZero
    simpa using h
  · exact integrableOn_Ioi_deriv_of_nonneg' (fun q hq => hasDerivAt_tailAnti hR hc hc0 hq)
      (fun q hq => div_nonneg (one_sub_div_nonneg hR hq) (sq_nonneg _)) tendsto_tailAnti

/-- **The scalar integral.** For `c ≠ 0` with `|c| < R`,
`∫_R^∞ (1 − R/q)(q − c)^{−2} dq = −(R/c²) log(1 − c/R) − 1/c`. -/
theorem integral_Ioi_tail_div_sq (hR : 1 < R) {c : ℝ} (hc : |c| < R) (hc0 : c ≠ 0) :
    ∫ q in Ioi R, (1 - R / q) / (q - c) ^ 2 = -(R / c ^ 2) * Real.log (1 - c / R) - 1 / c := by
  obtain ⟨hc₁, hc₂⟩ := abs_lt.1 hc
  have hRc : R - c ≠ 0 := sub_ne_zero_of_ne hc₂.ne'
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun q hq => hasDerivAt_tailAnti hR hc hc0 hq)
    (fun q hq => div_nonneg (one_sub_div_nonneg hR hq) (sq_nonneg _)) tendsto_tailAnti]
  field_simp
  ring

/-- **The scalar integral, degenerate case.** `∫_R^∞ (1 − R/q) q^{−2} dq = 1/(2R)`. -/
theorem integral_Ioi_tail_div_sq_zero (hR : 1 < R) :
    ∫ q in Ioi R, (1 - R / q) / q ^ 2 = 1 / (2 * R) := by
  have hR0 : R ≠ 0 := (by linarith : (0 : ℝ) < R).ne'
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun q hq => hasDerivAt_tailAntiZero hR hq)
    (fun q hq => div_nonneg (one_sub_div_nonneg hR hq) (sq_nonneg _)) tendsto_tailAntiZero]
  field_simp
  ring

theorem tailF_eq (hR : 1 < R) {c : ℝ} (hc : |c| < R) (hc0 : c ≠ 0) :
    tailF R c = -(R / c ^ 2) * Real.log (1 - c / R) - 1 / c :=
  integral_Ioi_tail_div_sq hR hc hc0

theorem tailF_zero (hR : 1 < R) : tailF R 0 = 1 / (2 * R) := by
  rw [tailF]
  simp only [sub_zero]
  exact integral_Ioi_tail_div_sq_zero hR

theorem tailF_nonneg (hR : 1 < R) (c : ℝ) : 0 ≤ tailF R c := by
  rw [tailF]
  exact setIntegral_nonneg measurableSet_Ioi fun _ hq =>
    div_nonneg (one_sub_div_nonneg hR hq) (sq_nonneg _)

/-- The elementary inequality `2/q² ≤ (q − d)^{−2} + (q + d)^{−2}` for `|d| < q`. -/
private theorem two_div_sq_le {d q : ℝ} (hd : |d| < q) :
    2 / q ^ 2 ≤ 1 / (q - d) ^ 2 + 1 / (q + d) ^ 2 := by
  obtain ⟨hd₁, hd₂⟩ := abs_lt.1 hd
  have hq : 0 < q := lt_of_le_of_lt (abs_nonneg d) hd
  have h₁ : 0 < q - d := by linarith
  have h₂ : 0 < q + d := by linarith
  have hq' : q ≠ 0 := hq.ne'
  have h₁' : q - d ≠ 0 := h₁.ne'
  have h₂' : q + d ≠ 0 := h₂.ne'
  have hd2 : d ^ 2 < q ^ 2 := by nlinarith
  have key : 0 ≤ 2 * d ^ 2 * (3 * q ^ 2 - d ^ 2) := by nlinarith [sq_nonneg d]
  have hpos : 0 < q ^ 2 * (q - d) ^ 2 * (q + d) ^ 2 := by positivity
  have e : 1 / (q - d) ^ 2 + 1 / (q + d) ^ 2 - 2 / q ^ 2
      = 2 * d ^ 2 * (3 * q ^ 2 - d ^ 2) / (q ^ 2 * (q - d) ^ 2 * (q + d) ^ 2) := by
    field_simp
    ring
  linarith [div_nonneg key hpos.le, e]

/-- The two inward directions are minimised at `d = 0`. -/
private theorem two_tailF_zero_le (hR : 1 < R) {d : ℝ} (hd : |d| < R) :
    2 * tailF R 0 ≤ tailF R d + tailF R (-d) := by
  have h0 : |(0 : ℝ)| < R := by rw [abs_zero]; linarith
  have hd' : |(-d)| < R := by rwa [abs_neg]
  have hi0 := integrableOn_tail_div_sq hR h0
  have hi1 := integrableOn_tail_div_sq hR hd
  have hi2 := integrableOn_tail_div_sq hR hd'
  rw [tailF, tailF, tailF, ← integral_add hi1 hi2, ← integral_const_mul]
  refine setIntegral_mono_on (hi0.const_mul 2) (hi1.add hi2) measurableSet_Ioi fun q hq => ?_
  have hq' : R < q := hq
  have hqd : |d| < q := lt_trans hd hq'
  have hT : 0 ≤ 1 - R / q := one_sub_div_nonneg hR hq'
  calc 2 * ((1 - R / q) / (q - 0) ^ 2) = (1 - R / q) * (2 / q ^ 2) := by rw [sub_zero]; ring
    _ ≤ (1 - R / q) * (1 / (q - d) ^ 2 + 1 / (q + d) ^ 2) :=
        mul_le_mul_of_nonneg_left (two_div_sq_le hqd) hT
    _ = (1 - R / q) / (q - d) ^ 2 + (1 - R / q) / (q - -d) ^ 2 := by rw [sub_neg_eq_add]; ring

/-! ### Translating and reflecting the half-line -/

private theorem indicator_Ioi_comp_add (G : ℝ → ℝ) (v : ℝ) :
    ((Ioi (0 : ℝ)).indicator fun w => G (w + v)) = fun w => (Ioi v).indicator G (w + v) := by
  funext w
  simp only [indicator_apply, mem_Ioi]
  rcases lt_or_ge 0 w with hw | hw
  · simp [hw, show v < w + v by linarith]
  · simp [show ¬(0 : ℝ) < w by linarith, show ¬v < w + v by linarith]

private theorem setIntegral_Ioi_comp_add (G : ℝ → ℝ) (v : ℝ) :
    ∫ w in Ioi (0 : ℝ), G (w + v) = ∫ q in Ioi v, G q := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi,
    indicator_Ioi_comp_add G v]
  exact integral_add_right_eq_self ((Ioi v).indicator G) v

private theorem integrableOn_Ioi_comp_add {G : ℝ → ℝ} {v : ℝ} (h : IntegrableOn G (Ioi v)) :
    IntegrableOn (fun w => G (w + v)) (Ioi 0) := by
  rw [← integrable_indicator_iff measurableSet_Ioi] at h ⊢
  rw [indicator_Ioi_comp_add G v]
  exact h.comp_add_right v

private theorem integrableOn_Iio_of_comp_neg {g : ℝ → ℝ}
    (h : IntegrableOn (fun w => g (-w)) (Ioi 0)) : IntegrableOn g (Iio 0) := by
  rw [← integrable_indicator_iff measurableSet_Ioi] at h
  rw [← integrable_indicator_iff measurableSet_Iio]
  refine h.comp_neg.congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [indicator_apply, mem_Ioi, mem_Iio]
  rcases lt_or_ge w 0 with hw | hw
  · simp [show (0 : ℝ) < -w by linarith, hw]
  · simp [show ¬(0 : ℝ) < -w by linarith, show ¬w < 0 by linarith]

/-! ### The profile against an inverse square on a half-line -/

private theorem integrableOn_Ioi_tailProfile_div_sq (hR : 1 < R) {v c : ℝ} (hv : 0 ≤ v)
    (hvR : v < R) (hc : |c| < R) :
    IntegrableOn (fun q => tailProfile R q / (q - c) ^ 2) (Ioi v) := by
  rw [← Ioc_union_Ioi_eq_Ioi hvR.le, integrableOn_union]
  refine ⟨?_, ?_⟩
  · refine (integrable_zero ℝ ℝ (volume.restrict (Ioc v R))).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with q hq
    simp [tailProfile_eq_zero (hv.trans_lt hq.1) hq.2]
  · refine IntegrableOn.congr_fun ((integrableOn_tail_div_sq hR hc).div_const (R - 1))
      (fun q hq => ?_) measurableSet_Ioi
    rw [tailProfile_of_lt hR hq]
    ring

private theorem integral_Ioi_tailProfile_div_sq (hR : 1 < R) {v c : ℝ} (hv : 0 ≤ v)
    (hvR : v < R) (hc : |c| < R) :
    ∫ q in Ioi v, tailProfile R q / (q - c) ^ 2 = tailF R c / (R - 1) := by
  have hall := integrableOn_Ioi_tailProfile_div_sq hR hv hvR hc
  have hi1 : IntegrableOn (fun q => tailProfile R q / (q - c) ^ 2) (Ioc v R) :=
    hall.mono_set Ioc_subset_Ioi_self
  have hi2 : IntegrableOn (fun q => tailProfile R q / (q - c) ^ 2) (Ioi R) :=
    hall.mono_set (Ioi_subset_Ioi hvR.le)
  have hzero : ∫ q in Ioc v R, tailProfile R q / (q - c) ^ 2 = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun q hq => by
      rw [tailProfile_eq_zero (hv.trans_lt hq.1) hq.2, zero_div]
  have hmain : ∫ q in Ioi R, tailProfile R q / (q - c) ^ 2 = tailF R c / (R - 1) := by
    rw [tailF, ← integral_div]
    exact setIntegral_congr_fun measurableSet_Ioi fun q hq => by
      rw [tailProfile_of_lt hR hq]; ring
  rw [← Ioc_union_Ioi_eq_Ioi hvR.le,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hi1 hi2, hzero, hmain, zero_add]

/-! ### The tail along a coordinate line -/

private theorem integrable_tailProfile_abs (hR : 1 < R) {a v : ℝ} (hv : 0 ≤ v)
    (hav : |a| + v < R) : Integrable fun w : ℝ => tailProfile R (|w| + v) / (w - a) ^ 2 := by
  have habs := abs_nonneg a
  have hle := le_abs_self a
  have hle' := neg_abs_le a
  have hvR : v < R := by linarith
  have hc1 : |v + a| < R := by rw [abs_lt]; constructor <;> linarith
  have hc2 : |v - a| < R := by rw [abs_lt]; constructor <;> linarith
  have hIoi : IntegrableOn (fun w : ℝ => tailProfile R (|w| + v) / (w - a) ^ 2) (Ioi 0) := by
    refine IntegrableOn.congr_fun
      (integrableOn_Ioi_comp_add (G := fun q : ℝ => tailProfile R q / (q - (v + a)) ^ 2)
      (v := v) (integrableOn_Ioi_tailProfile_div_sq hR hv hvR hc1))
      (fun w hw => ?_) measurableSet_Ioi
    have hw' : (0 : ℝ) < w := hw
    simp only [abs_of_pos hw', show w + v - (v + a) = w - a from by ring]
  have hIio : IntegrableOn (fun w : ℝ => tailProfile R (|w| + v) / (w - a) ^ 2) (Iio 0) := by
    refine integrableOn_Iio_of_comp_neg ?_
    refine IntegrableOn.congr_fun
      (integrableOn_Ioi_comp_add (G := fun q : ℝ => tailProfile R q / (q - (v - a)) ^ 2)
      (v := v) (integrableOn_Ioi_tailProfile_div_sq hR hv hvR hc2))
      (fun w hw => ?_) measurableSet_Ioi
    have hw' : (0 : ℝ) < w := hw
    simp only [abs_neg, abs_of_pos hw',
      show (w + v - (v - a)) ^ 2 = (-w - a) ^ 2 from by ring]
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0 : ℝ)), integrableOn_union]
  exact ⟨hIio, (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).2 hIoi⟩

private theorem integral_tailProfile_abs (hR : 1 < R) {a v : ℝ} (hv : 0 ≤ v)
    (hav : |a| + v < R) :
    ∫ w : ℝ, tailProfile R (|w| + v) / (w - a) ^ 2
      = (tailF R (v + a) + tailF R (v - a)) / (R - 1) := by
  have habs := abs_nonneg a
  have hle := le_abs_self a
  have hle' := neg_abs_le a
  have hvR : v < R := by linarith
  have hc1 : |v + a| < R := by rw [abs_lt]; constructor <;> linarith
  have hc2 : |v - a| < R := by rw [abs_lt]; constructor <;> linarith
  have e1 : ∫ w in Ioi (0 : ℝ), tailProfile R (|w| + v) / (w - a) ^ 2
      = tailF R (v + a) / (R - 1) :=
    calc ∫ w in Ioi (0 : ℝ), tailProfile R (|w| + v) / (w - a) ^ 2
        = ∫ w in Ioi (0 : ℝ), tailProfile R (w + v) / (w + v - (v + a)) ^ 2 :=
          setIntegral_congr_fun measurableSet_Ioi fun w hw => by
            rw [abs_of_pos hw, show w + v - (v + a) = w - a from by ring]
      _ = ∫ q in Ioi v, tailProfile R q / (q - (v + a)) ^ 2 :=
          setIntegral_Ioi_comp_add (fun q => tailProfile R q / (q - (v + a)) ^ 2) v
      _ = tailF R (v + a) / (R - 1) := integral_Ioi_tailProfile_div_sq hR hv hvR hc1
  have hneg := integral_comp_neg_Ioi (0 : ℝ) fun w : ℝ => tailProfile R (|w| + v) / (w - a) ^ 2
  rw [neg_zero] at hneg
  have e2 : ∫ w in Iio (0 : ℝ), tailProfile R (|w| + v) / (w - a) ^ 2
      = tailF R (v - a) / (R - 1) :=
    calc ∫ w in Iio (0 : ℝ), tailProfile R (|w| + v) / (w - a) ^ 2
        = ∫ w in Iic (0 : ℝ), tailProfile R (|w| + v) / (w - a) ^ 2 :=
          integral_Iic_eq_integral_Iio.symm
      _ = ∫ w in Ioi (0 : ℝ), tailProfile R (|(-w)| + v) / (-w - a) ^ 2 := hneg.symm
      _ = ∫ w in Ioi (0 : ℝ), tailProfile R (w + v) / (w + v - (v - a)) ^ 2 :=
          setIntegral_congr_fun measurableSet_Ioi fun w hw => by
            rw [abs_neg, abs_of_pos hw, show (-w - a) ^ 2 = (w + v - (v - a)) ^ 2 from by ring]
      _ = ∫ q in Ioi v, tailProfile R q / (q - (v - a)) ^ 2 :=
          setIntegral_Ioi_comp_add (fun q => tailProfile R q / (q - (v - a)) ^ 2) v
      _ = tailF R (v - a) / (R - 1) := integral_Ioi_tailProfile_div_sq hR hv hvR hc2
  rw [← integral_add_compl measurableSet_Iio (integrable_tailProfile_abs hR hv hav), compl_Iio,
    integral_Ici_eq_integral_Ioi, e1, e2]
  ring

private theorem integrable_tailProfile_line (hR : 1 < R) {a v : ℝ} (hv : 0 ≤ v)
    (hav : |a| + v < R) : Integrable fun t : ℝ => tailProfile R (|a + t| + v) / t ^ 2 := by
  refine Integrable.congr ((integrable_tailProfile_abs hR hv hav).comp_add_right a)
    (Filter.Eventually.of_forall fun t => ?_)
  show tailProfile R (|t + a| + v) / (t + a - a) ^ 2 = tailProfile R (|a + t| + v) / t ^ 2
  rw [add_comm t a, add_sub_cancel_left]

private theorem integral_tailProfile_line (hR : 1 < R) {a v : ℝ} (hv : 0 ≤ v)
    (hav : |a| + v < R) :
    ∫ t : ℝ, tailProfile R (|a + t| + v) / t ^ 2
      = (tailF R (v + a) + tailF R (v - a)) / (R - 1) := by
  rw [← integral_tailProfile_abs hR hv hav,
    ← integral_add_right_eq_self (fun w : ℝ => tailProfile R (|w| + v) / (w - a) ^ 2) a]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show tailProfile R (|a + t| + v) / t ^ 2 = tailProfile R (|t + a| + v) / (t + a - a) ^ 2
  rw [add_comm t a, add_sub_cancel_left]

/-! ### The generator of the tail inside the diamond -/

private theorem abs_rpow_neg_two (t : ℝ) : |t| ^ (-(1 + 1) : ℝ) = 1 / t ^ 2 := by
  rcases eq_or_ne t 0 with rfl | ht
  · rw [abs_zero, Real.zero_rpow (by norm_num)]
    norm_num
  · rw [show (-(1 + 1) : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (abs_nonneg t),
      Real.rpow_natCast, sq_abs, one_div]

private theorem diamondNorm_eq_abs_add (z : Fin 2 → ℝ) (j : Fin 2) :
    diamondNorm z = |z j| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem diamondNorm_add_single (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z + s • Pi.single j 1) = |z j + s| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

/-- One coordinate direction contributes `tailF R (v + a) + tailF R (v − a)`, twice. -/
private theorem integral_secondDiff_tail (hR : 1 < R) {z : Fin 2 → ℝ} {a v : ℝ} (j : Fin 2)
    (hz : 0 < diamondNorm z) (hzR : diamondNorm z < R) (ha : z j = a) (hv : |z (j + 1)| = v) :
    ∫ t : ℝ, secondDiff (tail R) j z t * |t| ^ (-(1 + 1) : ℝ)
      = 2 * ((tailF R (v + a) + tailF R (v - a)) / (R - 1)) := by
  have hv0 : 0 ≤ v := by rw [← hv]; exact abs_nonneg _
  have hr : |a| + v = diamondNorm z := by rw [← ha, ← hv, ← diamondNorm_eq_abs_add]
  have hav : |a| + v < R := by rw [hr]; exact hzR
  have hz0 : tail R z = 0 := tail_eq_zero hz hzR.le
  have hg := integrable_tailProfile_line hR hv0 hav
  have key : ∀ t : ℝ, secondDiff (tail R) j z t * |t| ^ (-(1 + 1) : ℝ)
      = tailProfile R (|a + t| + v) / t ^ 2 + tailProfile R (|a + -t| + v) / (-t) ^ 2 := by
    intro t
    have h1 : tail R (z + t • Pi.single j 1) = tailProfile R (|a + t| + v) := by
      rw [tail_eq, diamondNorm_add_single, ha, hv]
    have h2 : tail R (z - t • Pi.single j 1) = tailProfile R (|a + -t| + v) := by
      rw [sub_eq_add_neg, ← neg_smul, tail_eq, diamondNorm_add_single, ha, hv]
    rw [secondDiff, h1, h2, hz0, abs_rpow_neg_two, neg_sq]
    ring
  calc ∫ t : ℝ, secondDiff (tail R) j z t * |t| ^ (-(1 + 1) : ℝ)
      = ∫ t : ℝ, (tailProfile R (|a + t| + v) / t ^ 2
          + tailProfile R (|a + -t| + v) / (-t) ^ 2) :=
        integral_congr_ae (Filter.Eventually.of_forall key)
    _ = (∫ t : ℝ, tailProfile R (|a + t| + v) / t ^ 2)
          + ∫ t : ℝ, tailProfile R (|a + -t| + v) / (-t) ^ 2 := integral_add hg hg.comp_neg
    _ = 2 * ∫ t : ℝ, tailProfile R (|a + t| + v) / t ^ 2 := by
        rw [show (∫ t : ℝ, tailProfile R (|a + -t| + v) / (-t) ^ 2)
          = ∫ t : ℝ, tailProfile R (|a + t| + v) / t ^ 2 from
            integral_neg_eq_self (fun s : ℝ => tailProfile R (|a + s| + v) / s ^ 2) volume]
        ring
    _ = 2 * ((tailF R (v + a) + tailF R (v - a)) / (R - 1)) := by
        rw [integral_tailProfile_line hR hv0 hav]

/-- **The integrand of the generator of the tail is integrable** inside the open diamond: the tail
vanishes at `z`, so along each coordinate line the second difference collapses to the two boundary
terms of `integrable_tailProfile_line`. -/
theorem integrable_secondDiff_tail (hR : 1 < R) {z : Fin 2 → ℝ} (j : Fin 2)
    (hz : 0 < diamondNorm z) (hzR : diamondNorm z < R) :
    Integrable fun t : ℝ => secondDiff (tail R) j z t * |t| ^ (-(1 + 1) : ℝ) := by
  have hv0 : (0 : ℝ) ≤ |z (j + 1)| := abs_nonneg _
  have hav : |z j| + |z (j + 1)| < R := by rw [← diamondNorm_eq_abs_add]; exact hzR
  have hz0 : tail R z = 0 := tail_eq_zero hz hzR.le
  have hg := integrable_tailProfile_line hR hv0 hav
  refine (hg.add hg.comp_neg).congr (Filter.Eventually.of_forall fun t => ?_)
  have h1 : tail R (z + t • Pi.single j 1) = tailProfile R (|z j + t| + |z (j + 1)|) := by
    rw [tail_eq, diamondNorm_add_single]
  have h2 : tail R (z - t • Pi.single j 1) = tailProfile R (|z j + -t| + |z (j + 1)|) := by
    rw [sub_eq_add_neg, ← neg_smul, tail_eq, diamondNorm_add_single]
  show tailProfile R (|z j + t| + |z (j + 1)|) / t ^ 2
      + tailProfile R (|z j + -t| + |z (j + 1)|) / (-t) ^ 2
      = secondDiff (tail R) j z t * |t| ^ (-(1 + 1) : ℝ)
  rw [secondDiff, h1, h2, hz0, abs_rpow_neg_two, neg_sq]
  ring

private theorem tailF_add_tailF (R x y : ℝ) :
    tailF R (|y| + x) + tailF R (|y| - x) = tailF R (|x| + |y|) + tailF R (|y| - |x|) := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx, add_comm x |y|]
  · rw [abs_of_neg hx, show -x + |y| = |y| - x from by ring, show |y| - -x = |y| + x from by ring,
      add_comm]

/-- **The four-term identity.** Inside the open diamond the generator of the tail is a sum of four
half-line integrals: two "outward" ones at distance `r` and two "inward" ones at distances `±d`
with `d = |z 0| − |z 1|`. -/
theorem jumpGen_tail_eq (hR : 1 < R) {z : Fin 2 → ℝ} (hz : 0 < diamondNorm z)
    (hzR : diamondNorm z < R) :
    jumpGen 1 (tail R) z = 2 * (2 * tailF R (diamondNorm z)
      + tailF R (|z 0| - |z 1|) + tailF R (|z 1| - |z 0|)) / (R - 1) := by
  have h0 := integral_secondDiff_tail hR (z := z) (a := z 0) (v := |z 1|) 0 hz hzR rfl
    (by rw [show (0 : Fin 2) + 1 = 1 from by decide])
  have h1 := integral_secondDiff_tail hR (z := z) (a := z 1) (v := |z 0|) 1 hz hzR rfl
    (by rw [show (1 : Fin 2) + 1 = 0 from by decide])
  have hdn : diamondNorm z = |z 0| + |z 1| := rfl
  unfold jumpGen
  rw [Fin.sum_univ_two, h0, h1, tailF_add_tailF R (z 0) (z 1), tailF_add_tailF R (z 1) (z 0),
    hdn, show |z 1| + |z 0| = |z 0| + |z 1| from add_comm _ _]
  ring

/-- **The four-term lower bound.** With `r = diamondNorm z`, the outward pair of half-line
integrals is evaluated exactly and the inward pair is bounded below by its value at `d = 0`; the
resulting bound is `2 ((−(R/r²) log(1 − r/R) − 1/r) + 1/(2R)) / (R − 1)`, at most half of the
exact value of `jumpGen_tail_eq`. -/
theorem jumpGen_tail_ge (hR : 1 < R) {z : Fin 2 → ℝ} (hz : 0 < diamondNorm z)
    (hzR : diamondNorm z < R) :
    jumpGen 1 (tail R) z ≥ 2 * ((-(R / diamondNorm z ^ 2) *
      Real.log (1 - diamondNorm z / R) - 1 / diamondNorm z) + 1 / (2 * R)) / (R - 1) := by
  have hR0 : (0 : ℝ) < R := by linarith
  have hzR' : |z 0| + |z 1| < R := hzR
  have hr : tailF R (diamondNorm z) =
      -(R / diamondNorm z ^ 2) * Real.log (1 - diamondNorm z / R) - 1 / diamondNorm z :=
    tailF_eq hR (by rwa [abs_of_pos hz]) hz.ne'
  have hd : |(|z 0| - |z 1|)| < R :=
    abs_lt.2 ⟨by linarith [abs_nonneg (z 0)], by linarith [abs_nonneg (z 1)]⟩
  have hdd := two_tailF_zero_le hR hd
  rw [neg_sub, tailF_zero hR] at hdd
  have hX : (0 : ℝ) ≤ 1 / (2 * R) := by positivity
  have hnn := tailF_nonneg hR (diamondNorm z)
  have hkey : 2 * (tailF R (diamondNorm z) + 1 / (2 * R))
      ≤ 2 * (2 * tailF R (diamondNorm z) + tailF R (|z 0| - |z 1|)
        + tailF R (|z 1| - |z 0|)) := by linarith
  rw [jumpGen_tail_eq hR hz hzR, ge_iff_le, ← hr]
  calc 2 * (tailF R (diamondNorm z) + 1 / (2 * R)) / (R - 1)
      = (R - 1)⁻¹ * (2 * (tailF R (diamondNorm z) + 1 / (2 * R))) := by ring
    _ ≤ (R - 1)⁻¹ * (2 * (2 * tailF R (diamondNorm z) + tailF R (|z 0| - |z 1|)
          + tailF R (|z 1| - |z 0|))) :=
        mul_le_mul_of_nonneg_left hkey (inv_nonneg.2 (by linarith))
    _ = 2 * (2 * tailF R (diamondNorm z) + tailF R (|z 0| - |z 1|)
          + tailF R (|z 1| - |z 0|)) / (R - 1) := by ring

/-- **The sharp four-term lower bound.** The outward pair of half-line integrals is evaluated
exactly and the inward pair is replaced by its minimum, at `d = 0`; nothing else is discarded, so
the bound is attained whenever `|z 0| = |z 1|` and is exactly twice `jumpGen_tail_ge`. -/
theorem jumpGen_tail_ge_sharp (hR : 1 < R) {z : Fin 2 → ℝ} (hz : 0 < diamondNorm z)
    (hzR : diamondNorm z < R) :
    jumpGen 1 (tail R) z ≥ 4 * ((-(R / diamondNorm z ^ 2) *
      Real.log (1 - diamondNorm z / R) - 1 / diamondNorm z) + 1 / (2 * R)) / (R - 1) := by
  have hzR' : |z 0| + |z 1| < R := hzR
  have hr : tailF R (diamondNorm z) =
      -(R / diamondNorm z ^ 2) * Real.log (1 - diamondNorm z / R) - 1 / diamondNorm z :=
    tailF_eq hR (by rwa [abs_of_pos hz]) hz.ne'
  have hd : |(|z 0| - |z 1|)| < R :=
    abs_lt.2 ⟨by linarith [abs_nonneg (z 0)], by linarith [abs_nonneg (z 1)]⟩
  have hdd := two_tailF_zero_le hR hd
  rw [neg_sub, tailF_zero hR] at hdd
  have hkey : 4 * (tailF R (diamondNorm z) + 1 / (2 * R))
      ≤ 2 * (2 * tailF R (diamondNorm z) + tailF R (|z 0| - |z 1|)
        + tailF R (|z 1| - |z 0|)) := by linarith
  rw [jumpGen_tail_eq hR hz hzR, ge_iff_le, ← hr]
  calc 4 * (tailF R (diamondNorm z) + 1 / (2 * R)) / (R - 1)
      = (R - 1)⁻¹ * (4 * (tailF R (diamondNorm z) + 1 / (2 * R))) := by ring
    _ ≤ (R - 1)⁻¹ * (2 * (2 * tailF R (diamondNorm z) + tailF R (|z 0| - |z 1|)
          + tailF R (|z 1| - |z 0|))) :=
        mul_le_mul_of_nonneg_left hkey (inv_nonneg.2 (by linarith))
    _ = 2 * (2 * tailF R (diamondNorm z) + tailF R (|z 0| - |z 1|)
          + tailF R (|z 1| - |z 0|)) / (R - 1) := by ring

/-! ### The shape function `J` -/

/-- The bound of `jumpGen_tail_ge` in the scale-invariant variable `s = 2r/R`. -/
theorem jumpGen_tail_ge_Jfun (hR : 1 < R) {r : ℝ} (hr : 0 < r) :
    2 * ((-(R / r ^ 2) * Real.log (1 - r / R) - 1 / r) + 1 / (2 * R)) / (R - 1)
      = 2 / (R * (R - 1)) * Jfun (2 * r / R) := by
  have hR0 : R ≠ 0 := (by linarith : (0 : ℝ) < R).ne'
  have hR1 : R - 1 ≠ 0 := sub_ne_zero_of_ne hR.ne'
  have hr0 : r ≠ 0 := hr.ne'
  have hs : 1 - 2 * r / R / 2 = 1 - r / R := by field_simp
  rw [Jfun, hs]
  field_simp
  ring

/-- **The sharp bound in the scale-invariant variable** `s = 2r/R`: the generator density of the
tail inside the diamond is at least `(4/(R (R − 1))) J(2r/R)`, with equality on the diagonals. -/
theorem jumpGen_tail_ge_Jfun_sharp (hR : 1 < R) {z : Fin 2 → ℝ} (hz : 0 < diamondNorm z)
    (hzR : diamondNorm z < R) :
    jumpGen 1 (tail R) z ≥ 4 / (R * (R - 1)) * Jfun (2 * diamondNorm z / R) := by
  have key : 4 / (R * (R - 1)) * Jfun (2 * diamondNorm z / R)
      = 4 * ((-(R / diamondNorm z ^ 2) * Real.log (1 - diamondNorm z / R)
        - 1 / diamondNorm z) + 1 / (2 * R)) / (R - 1) := by
    rw [show 4 / (R * (R - 1)) * Jfun (2 * diamondNorm z / R)
      = 2 * (2 / (R * (R - 1)) * Jfun (2 * diamondNorm z / R)) from by ring,
      ← jumpGen_tail_ge_Jfun hR hz]
    ring
  rw [key]
  exact jumpGen_tail_ge_sharp hR hz hzR

/-- `x + x²/2 ≤ −log(1 − x)` for `0 ≤ x < 1`: the first two terms of the power series of
`−log(1 − x)`, all of whose terms are nonnegative. -/
private theorem add_sq_div_two_le_neg_log {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) :
    x + x ^ 2 / 2 ≤ -Real.log (1 - x) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := x) (by rwa [abs_of_nonneg hx])
  have h2 := sum_le_hasSum (Finset.range 2)
    (fun n _ => div_nonneg (pow_nonneg hx _) (by positivity)) h
  norm_num [Finset.sum_range_succ] at h2
  linarith

/-- **`J ≥ 1` on `(0, 2)`.** -/
theorem one_le_Jfun {s : ℝ} (hs : 0 < s) (hs' : s < 2) : 1 ≤ Jfun s := by
  have hx : (0 : ℝ) ≤ s / 2 := by linarith
  have hx' : s / 2 < 1 := by linarith
  have h := add_sq_div_two_le_neg_log hx hx'
  have hs0 : s ≠ 0 := hs.ne'
  have hL : 2 / s + 1 / 2 ≤ -(4 / s ^ 2 * Real.log (1 - s / 2)) :=
    calc 2 / s + 1 / 2 = 4 / s ^ 2 * (s / 2 + (s / 2) ^ 2 / 2) := by field_simp; ring
      _ ≤ 4 / s ^ 2 * -Real.log (1 - s / 2) := mul_le_mul_of_nonneg_left h (by positivity)
      _ = -(4 / s ^ 2 * Real.log (1 - s / 2)) := by ring
  unfold Jfun
  linarith

/-- **The power series of `J`.** For `0 < s < 2` the shape function is
`J s = 1 + ∑_k s^{k+1} / (2^{k+1} (k + 3))`, obtained from the series of `−log(1 − s/2)` by
discarding its first two terms and dividing by `(s/2)²`. -/
theorem hasSum_Jfun {s : ℝ} (hs : 0 < s) (hs' : s < 2) :
    HasSum (fun k : ℕ => s ^ (k + 1) / (2 ^ (k + 1) * ((k : ℝ) + 3))) (Jfun s - 1) := by
  have hs0 : s ≠ 0 := hs.ne'
  have habs : |s / 2| < 1 := by
    rw [abs_of_pos (by linarith : (0 : ℝ) < s / 2)]
    linarith
  have h := Real.hasSum_pow_div_log_of_abs_lt_one habs
  have hsum : ∑ i ∈ Finset.range 2, (s / 2) ^ (i + 1) / ((i : ℝ) + 1)
      = s / 2 + (s / 2) ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    push_cast
    ring
  have key := (hasSum_nat_add_iff (f := fun n : ℕ => (s / 2) ^ (n + 1) / ((n : ℝ) + 1))
    (g := -Real.log (1 - s / 2) - (s / 2 + (s / 2) ^ 2 / 2)) 2).2 (by
      rw [hsum, show -Real.log (1 - s / 2) - (s / 2 + (s / 2) ^ 2 / 2) + (s / 2 + (s / 2) ^ 2 / 2)
        = -Real.log (1 - s / 2) from by ring]
      exact h)
  have hfun : (fun k : ℕ => s ^ (k + 1) / (2 ^ (k + 1) * ((k : ℝ) + 3)))
      = fun n : ℕ => 4 / s ^ 2 * ((s / 2) ^ (n + 2 + 1) / (((n + 2 : ℕ) : ℝ) + 1)) := by
    funext k
    have h2 : ((2 : ℝ)) ^ (k + 1) ≠ 0 := by positivity
    have h3 : ((k : ℝ) + 3) ≠ 0 := by positivity
    rw [show k + 2 + 1 = k + 1 + 2 from by omega,
      show (s / 2) ^ (k + 1 + 2) = (s / 2) ^ (k + 1) * (s / 2) ^ 2 from pow_add _ _ _,
      show (s / 2) ^ (k + 1) = s ^ (k + 1) / 2 ^ (k + 1) from div_pow _ _ _]
    push_cast
    field_simp
    ring
  have hval : 4 / s ^ 2 * (-Real.log (1 - s / 2) - (s / 2 + (s / 2) ^ 2 / 2)) = Jfun s - 1 := by
    rw [Jfun]
    field_simp
    ring
  rw [hfun, ← hval]
  exact key.mul_left (4 / s ^ 2)

theorem Jfun_eq_tsum {s : ℝ} (hs : 0 < s) (hs' : s < 2) :
    Jfun s = 1 + ∑' k : ℕ, s ^ (k + 1) / (2 ^ (k + 1) * ((k : ℝ) + 3)) := by
  rw [(hasSum_Jfun hs hs').tsum_eq]
  ring

/-- **`J` is convex on `(0, 2)`**: each term of its power series is a positive multiple of a
monomial, hence convex on `[0, ∞)`. -/
theorem Jfun_convexOn : ConvexOn ℝ (Ioo 0 2) Jfun := by
  refine ⟨convex_Ioo 0 2, fun a ha b hb u v hu hv huv => ?_⟩
  have hm : u * a + v * b ∈ Ioo (0 : ℝ) 2 := by
    simpa using (convex_Ioo (0 : ℝ) 2) ha hb hu hv huv
  have Hm := hasSum_Jfun hm.1 hm.2
  have Ha := hasSum_Jfun ha.1 ha.2
  have Hb := hasSum_Jfun hb.1 hb.2
  have Hsum := (Ha.mul_left u).add (Hb.mul_left v)
  have hle : ∀ k : ℕ, (u * a + v * b) ^ (k + 1) / (2 ^ (k + 1) * ((k : ℝ) + 3))
      ≤ u * (a ^ (k + 1) / (2 ^ (k + 1) * ((k : ℝ) + 3)))
        + v * (b ^ (k + 1) / (2 ^ (k + 1) * ((k : ℝ) + 3))) := by
    intro k
    have h1 : (u * a + v * b) ^ (k + 1) ≤ u * a ^ (k + 1) + v * b ^ (k + 1) := by
      simpa using (convexOn_pow (k + 1)).2 (mem_Ici.2 ha.1.le) (mem_Ici.2 hb.1.le) hu hv huv
    have hC : (0 : ℝ) < 2 ^ (k + 1) * ((k : ℝ) + 3) := by positivity
    calc (u * a + v * b) ^ (k + 1) / (2 ^ (k + 1) * ((k : ℝ) + 3))
        = (2 ^ (k + 1) * ((k : ℝ) + 3))⁻¹ * (u * a + v * b) ^ (k + 1) := by ring
      _ ≤ (2 ^ (k + 1) * ((k : ℝ) + 3))⁻¹ * (u * a ^ (k + 1) + v * b ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hC.le)
      _ = u * (a ^ (k + 1) / (2 ^ (k + 1) * ((k : ℝ) + 3)))
            + v * (b ^ (k + 1) / (2 ^ (k + 1) * ((k : ℝ) + 3))) := by ring
  have hfinal := hasSum_le hle Hm Hsum
  simp only [smul_eq_mul]
  linarith

end CenteredMaximal.Cauchy

end

end
