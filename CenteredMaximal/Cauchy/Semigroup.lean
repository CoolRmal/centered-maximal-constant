/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Cauchy.Symbol
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The coordinate Cauchy semigroup solves the fractional heat equation

The coordinate Cauchy generator `A = −|D_u| − |D_v|` is the `α = 1` jump generator of
`CenteredMaximal.Analysis.JumpGenerator`, normalised by `c_1 / 2 = 1 / (2π)`. This file proves that
the semigroup density `heatKernel` of `CenteredMaximal.Cauchy.Potential` solves `A p_t = ∂_t p_t`:

`(1 / (2π)) * jumpGen 1 (heatKernel t) z = ∂_t (heatKernel t z)`,

which is `jumpGen_heatKernel`, together with its one-dimensional core `jumpGen1_cauchyDensity`

`(1 / (2π)) * jumpGen1 1 (cauchyDensity t) x = (x² − t²) / (π (t² + x²)²)`,

where `jumpGen1 α φ x = ∫_ℝ (φ(x + s) + φ(x − s) − 2 φ(x)) |s|^{−(1+α)} ds` is the one-dimensional
jump operator.

## The one-dimensional identity

The proof is a Fubini computation against the cosine representation of the Cauchy density. Writing
`a = 2π t` and `b = 2π y`, the elementary half-line Laplace transforms

`∫₀^∞ e^{−a s} cos (b s) ds = a / (a² + b²)`, `∫₀^∞ s e^{−a s} cos (b s) ds = (a² − b²)/(a² + b²)²`

(`Symbol.integral_Ioi_exp_neg_mul_cos` and `integral_Ioi_mul_exp_neg_mul_cos`, the latter proved
here as the real part of `∫₀^∞ s e^{z s} ds = 1/z²` for `z = −a + i b` by the fundamental theorem of
calculus with the antiderivative `(s/z − 1/z²) e^{z s}`) give the two whole-line integrals

`∫_ℝ cos (2π y ξ) e^{−2π t |ξ|} dξ = q_t(y)`,
`∫_ℝ |ξ| e^{−2π t |ξ|} cos (2π y ξ) dξ = 2 (a² − b²)/(a² + b²)²`.

The first identity turns the second difference of `q_t` into
`Δ_s q_t (x) = ∫_ℝ cos (2π x ξ) (2 cos (2π ξ s) − 2) e^{−2π t |ξ|} dξ` — the product-to-sum formula
`2 cos A cos B = cos (A + B) + cos (A − B)` is all that is needed — so that
`jumpGen1 1 q_t x = ∫_ℝ ∫_ℝ jumpKernel` for the kernel
`jumpKernel t x s ξ = cos (2π x ξ) e^{−2π t |ξ|} (2 cos (2π ξ s) − 2)/s²`.

The double integral is absolutely convergent: the inner `s`-integral of `‖jumpKernel‖` is
*exactly* `|cos (2π x ξ)| e^{−2π t |ξ|} · 2π |2π ξ|` by the jump integral
`Symbol.integral_one_sub_cos_div_sq_eq`, and that is dominated by `4π² |ξ| e^{−2π t |ξ|}`, which is
integrable. So `integral_integral_swap` applies, and the `s`-integral of the kernel is
`−2π |2π ξ|` times `cos (2π x ξ) e^{−2π t |ξ|}`; the second whole-line integral then evaluates
`jumpGen1 1 q_t x = 2 (x² − t²)/(t² + x²)²`. Dividing by `2π` gives exactly `∂_t q_t (x)`, computed
directly in `hasDerivAt_cauchyDensity`, so the constant `c_1 / 2 = 1/(2π)` is confirmed.

## The Fourier symbols

For the record the file also identifies the two Fourier transforms behind the identity, in
Mathlib's normalisation `𝓕 f ξ = ∫ e^{−2πi x ξ} f x dx`:

* `fourierIntegral_deriv_cauchyDensity`: `𝓕 (∂_t q_t) ξ = −2π |ξ| e^{−2π t |ξ|}`, by Fourier
  inversion (`Continuous.fourier_fourierInv_eq`) from the cosine transform of the symbol;
* `fourierIntegral_jumpGen1_cauchyDensity`: `𝓕 (jumpGen1 1 q_t) ξ = −2π |2π ξ| e^{−2π t |ξ|}`,
  the symbol `−2π |2π ξ|` of the jump operator times `𝓕 q_t`.

## The two-dimensional identity

`heatKernel t z = q_t(z_0) q_t(z_1)`, and the second difference in the `j`-th coordinate only moves
the `j`-th factor, so `jumpGen 1 (heatKernel t) z` splits as
`jumpGen1 1 q_t (z_0) q_t(z_1) + q_t(z_0) jumpGen1 1 q_t (z_1)`. The one-dimensional identity and
the product rule (`hasDerivAt_heatKernel`) finish the proof.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform Topology

namespace CenteredMaximal

/-- The one-dimensional jump generator of order `α`, the unnormalised operator
`∫_ℝ (φ(x + s) + φ(x − s) − 2 φ(x)) |s|^{−(1+α)} ds` (a Bochner integral; the constant `c_α / 2` is
not included). It is the one-coordinate analogue of `jumpGen`. -/
def jumpGen1 (α : ℝ) (φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ s : ℝ, (φ (x + s) + φ (x - s) - 2 * φ x) * |s| ^ (-(1 + α))

/-- The jump weight of order `α = 1` is `s^{-2}`. -/
theorem abs_rpow_neg_two (s : ℝ) : |s| ^ (-(1 + (1 : ℝ))) = (s ^ 2)⁻¹ := by
  rw [show -(1 + (1 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, zpow_neg,
    show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, sq_abs]

namespace Cauchy

/-! ### The weighted half-line Laplace transform -/

/-- `u ↦ (u/z − 1/z²) e^{z u}` is an antiderivative of `u ↦ u e^{z u}`. -/
private theorem hasDerivAt_weightedExp {z : ℂ} (hz : z ≠ 0) (y : ℝ) :
    HasDerivAt (fun u : ℝ => ((u : ℂ) / z - 1 / z ^ 2) * Complex.exp (z * u))
      ((y : ℂ) * Complex.exp (z * y)) y := by
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 y := by simpa using (hasDerivAt_id y).ofReal_comp
  have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) / z - 1 / z ^ 2) (1 / z) y := by
    simpa [one_div] using (h1.div_const z).sub_const (1 / z ^ 2)
  have h3 : HasDerivAt (fun u : ℝ => Complex.exp (z * u)) (Complex.exp (z * y) * z) y := by
    simpa using (h1.const_mul z).cexp
  refine (h2.mul h3).congr_deriv ?_
  field_simp
  ring

/-- The antiderivative `(u/z − 1/z²) e^{z u}` tends to `0` at infinity when `Re z < 0`. -/
private theorem tendsto_weightedExp {z : ℂ} (hz : z.re < 0) :
    Tendsto (fun u : ℝ => ((u : ℂ) / z - 1 / z ^ 2) * Complex.exp (z * u)) atTop (𝓝 0) := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hnz : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz0
  set c : ℝ := -z.re with hc
  have hc0 : 0 < c := by rw [hc]; linarith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbound : ∀ u : ℝ, 0 ≤ u →
      ‖((u : ℂ) / z - 1 / z ^ 2) * Complex.exp (z * u)‖
        ≤ (u / ‖z‖ + 1 / ‖z‖ ^ 2) * Real.exp (-(c * u)) := by
    intro u hu
    have hre : (z * (u : ℂ)).re = -(c * u) := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hc]; ring
    rw [norm_mul, Complex.norm_exp, hre]
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    calc ‖(u : ℂ) / z - 1 / z ^ 2‖ ≤ ‖(u : ℂ) / z‖ + ‖1 / z ^ 2‖ := norm_sub_le _ _
      _ = u / ‖z‖ + 1 / ‖z‖ ^ 2 := by
          rw [norm_div, norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hu, norm_one]
  have h1 : Tendsto (fun u : ℝ => c * u) atTop atTop := tendsto_id.const_mul_atTop hc0
  have hB : Tendsto (fun u : ℝ => Real.exp (-(c * u))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
  have hA : Tendsto (fun u : ℝ => u * Real.exp (-(c * u))) atTop (𝓝 0) := by
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp h1).const_mul c⁻¹
    rw [mul_zero] at h
    refine h.congr fun u => ?_
    simp only [Function.comp_apply, pow_one]
    field_simp
  have hsum := (hA.const_mul ‖z‖⁻¹).add (hB.const_mul ((‖z‖ ^ 2)⁻¹))
  rw [mul_zero, mul_zero, add_zero] at hsum
  have hlim : Tendsto (fun u : ℝ => (u / ‖z‖ + 1 / ‖z‖ ^ 2) * Real.exp (-(c * u)))
      atTop (𝓝 0) := hsum.congr fun u => by rw [div_eq_mul_inv, one_div]; ring
  exact squeeze_zero' ((eventually_ge_atTop (0 : ℝ)).mono fun u _ => norm_nonneg _)
    ((eventually_ge_atTop (0 : ℝ)).mono fun u hu => hbound u hu) hlim

/-- The weighted half-line exponential integral `∫₀^∞ y e^{z y} dy = 1/z²` for `Re z < 0`. -/
theorem integral_Ioi_mul_exp_mul_complex {z : ℂ} (hz : z.re < 0) :
    ∫ y in Ioi (0 : ℝ), (y : ℂ) * Complex.exp (z * y) = 1 / z ^ 2 := by
  have hz0 : z ≠ 0 := by intro h; rw [h] at hz; simp at hz
  have hint : IntegrableOn (fun y : ℝ => (y : ℂ) * Complex.exp (z * y)) (Ioi 0) := by
    have hdom : IntegrableOn (fun y : ℝ => y * Real.exp (-(y * -z.re))) (Ioi 0) :=
      integrableOn_Ioi_mul_exp_neg_mul (by linarith)
    refine Integrable.mono' hdom (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Ioi
      fun y hy => ?_)
    have hy' : (0 : ℝ) < y := hy
    have hre : (z * (y : ℂ)).re = -(y * -z.re) := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring
    rw [norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy']
  have key := integral_Ioi_of_hasDerivAt_of_tendsto' (fun y _ => hasDerivAt_weightedExp hz0 y)
    hint (tendsto_weightedExp hz)
  rw [key]
  simp

/-- The **weighted half-line Laplace transform of a cosine**,
`∫₀^∞ y e^{−a y} cos (b y) dy = (a² − b²)/(a² + b²)²` for `a > 0`: the real part of
`∫₀^∞ y e^{(−a + i b) y} dy = 1/(−a + i b)²`. -/
theorem integral_Ioi_mul_exp_neg_mul_cos {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫ y in Ioi (0 : ℝ), y * Real.exp (-(a * y)) * Real.cos (b * y)
      = (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2) ^ 2 := by
  set z : ℂ := -(a : ℂ) + (b : ℂ) * Complex.I with hzdef
  have hzre : z.re = -a := by simp [hzdef]
  have hzim : z.im = b := by simp [hzdef]
  have hlt : z.re < 0 := by rw [hzre]; linarith
  have hint : IntegrableOn (fun y : ℝ => (y : ℂ) * Complex.exp (z * y)) (Ioi 0) := by
    have hdom : IntegrableOn (fun y : ℝ => y * Real.exp (-(y * a))) (Ioi 0) :=
      integrableOn_Ioi_mul_exp_neg_mul ha
    refine Integrable.mono' hdom (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Ioi
      fun y hy => ?_)
    have hy' : (0 : ℝ) < y := hy
    have hre : (z * (y : ℂ)).re = -(y * a) := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hzre, hzim]; ring
    rw [norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy']
  have hsq : z ^ 2 = ((a ^ 2 - b ^ 2 : ℝ) : ℂ) - ((2 * a * b : ℝ) : ℂ) * Complex.I := by
    rw [hzdef]; push_cast; linear_combination ((b : ℂ) ^ 2) * Complex.I_sq
  have hre2 : (z ^ 2).re = a ^ 2 - b ^ 2 := by
    rw [hsq]
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  have him2 : (z ^ 2).im = -(2 * a * b) := by
    rw [hsq]
    simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  calc ∫ y in Ioi (0 : ℝ), y * Real.exp (-(a * y)) * Real.cos (b * y)
      = ∫ y in Ioi (0 : ℝ), ((y : ℂ) * Complex.exp (z * y)).re := by
        refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
        have hmre : (z * (y : ℂ)).re = -(a * y) := by
          rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hzre, hzim]; ring
        have hmim : (z * (y : ℂ)).im = b * y := by
          rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzre, hzim]; ring
        rw [Complex.re_ofReal_mul, Complex.exp_re, hmre, hmim, mul_assoc]
    _ = (∫ y in Ioi (0 : ℝ), (y : ℂ) * Complex.exp (z * y)).re := by simpa using integral_re hint
    _ = (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2) ^ 2 := by
        rw [integral_Ioi_mul_exp_mul_complex hlt, one_div, Complex.inv_re, Complex.normSq_apply,
          hre2, him2]
        congr 1
        ring

/-! ### The cosine representation of the Cauchy density -/

/-- The weight `|ξ| e^{−a |ξ|}` is integrable on the line for `a > 0`. -/
theorem integrable_abs_mul_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable fun ξ : ℝ => |ξ| * Real.exp (-(a * |ξ|)) := by
  refine integrable_of_even (fun ξ => by rw [abs_neg]) ?_
  refine (integrableOn_Ioi_mul_exp_neg_mul ha).congr_fun (fun ξ hξ => ?_) measurableSet_Ioi
  show ξ * Real.exp (-(ξ * a)) = |ξ| * Real.exp (-(a * |ξ|))
  rw [abs_of_pos (mem_Ioi.mp hξ), mul_comm ξ a]

/-- The cosine transform of the symbol is integrable on the line for `a > 0`. -/
theorem integrable_cos_mul_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Integrable fun ξ : ℝ => Real.cos (b * ξ) * Real.exp (-(a * |ξ|)) := by
  refine Integrable.mono' (integrable_exp_neg_mul_abs ha) (by fun_prop)
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.abs_cos_le_one _)

/-- The whole-line cosine transform of the symbol, `∫_ℝ cos (b ξ) e^{−a |ξ|} dξ =
2a/(a² + b²)`. -/
theorem integral_cos_mul_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫ ξ : ℝ, Real.cos (b * ξ) * Real.exp (-(a * |ξ|)) = 2 * a / (a ^ 2 + b ^ 2) := by
  have hcongr : EqOn (fun ξ : ℝ => Real.cos (b * ξ) * Real.exp (-(a * |ξ|)))
      (fun ξ : ℝ => Real.exp (-(a * ξ)) * Real.cos (b * ξ)) (Ioi 0) := fun ξ hξ => by
    show Real.cos (b * ξ) * Real.exp (-(a * |ξ|)) = Real.exp (-(a * ξ)) * Real.cos (b * ξ)
    rw [abs_of_pos (mem_Ioi.mp hξ), mul_comm]
  have hIoi : IntegrableOn (fun ξ : ℝ => Real.cos (b * ξ) * Real.exp (-(a * |ξ|))) (Ioi 0) :=
    (integrableOn_Ioi_exp_neg_mul_cos ha b).congr_fun hcongr.symm measurableSet_Ioi
  rw [integral_of_even (fun ξ => by rw [abs_neg, mul_neg, Real.cos_neg]) hIoi,
    setIntegral_congr_fun measurableSet_Ioi hcongr, integral_Ioi_exp_neg_mul_cos ha b]
  ring

/-- The **cosine representation of the Cauchy density**,
`∫_ℝ cos (2π y ξ) e^{−2π t |ξ|} dξ = q_t(y)`, the inverse form of
`Symbol.fourierIntegral_cauchyDensity`. -/
theorem integral_cos_mul_exp_neg_mul_abs_eq_cauchyDensity {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ∫ ξ : ℝ, Real.cos (2 * Real.pi * y * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|))
      = cauchyDensity t y := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [integral_cos_mul_exp_neg_mul_abs (a := 2 * Real.pi * t) (by positivity) (2 * Real.pi * y),
    cauchyDensity]
  have h : t ^ 2 + y ^ 2 ≠ 0 := by positivity
  field_simp

/-- The whole-line weighted cosine transform of the symbol,
`∫_ℝ |ξ| e^{−a |ξ|} cos (b ξ) dξ = 2 (a² − b²)/(a² + b²)²`. -/
theorem integral_abs_mul_exp_neg_mul_abs_mul_cos {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫ ξ : ℝ, |ξ| * Real.exp (-(a * |ξ|)) * Real.cos (b * ξ)
      = 2 * ((a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2) ^ 2) := by
  have hcongr : EqOn (fun ξ : ℝ => |ξ| * Real.exp (-(a * |ξ|)) * Real.cos (b * ξ))
      (fun ξ : ℝ => ξ * Real.exp (-(a * ξ)) * Real.cos (b * ξ)) (Ioi 0) := fun ξ hξ => by
    show |ξ| * Real.exp (-(a * |ξ|)) * Real.cos (b * ξ)
      = ξ * Real.exp (-(a * ξ)) * Real.cos (b * ξ)
    rw [abs_of_pos (mem_Ioi.mp hξ)]
  have hIoi : IntegrableOn
      (fun ξ : ℝ => |ξ| * Real.exp (-(a * |ξ|)) * Real.cos (b * ξ)) (Ioi 0) := by
    refine ((integrable_abs_mul_exp_neg_mul_abs ha).integrableOn (s := Ioi 0)).mono'
      (by fun_prop) (ae_restrict_of_forall_mem measurableSet_Ioi fun ξ _ => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_abs, abs_of_pos (Real.exp_pos _)]
    exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
  rw [integral_of_even (fun ξ => by rw [abs_neg, mul_neg, Real.cos_neg]) hIoi,
    setIntegral_congr_fun measurableSet_Ioi hcongr, integral_Ioi_mul_exp_neg_mul_cos ha b]

/-! ### The Fubini kernel of the one-dimensional jump integral -/

/-- The integrand of the double integral computing `jumpGen1 1 (cauchyDensity t)`: the second
difference of the cosine representation, `cos (2π x ξ) e^{−2π t |ξ|} (2 cos (2π ξ s) − 2)/s²`. -/
private def jumpKernel (t x s ξ : ℝ) : ℝ :=
  Real.cos (2 * Real.pi * x * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|))
    * ((2 * Real.cos (2 * Real.pi * ξ * s) - 2) / s ^ 2)

/-- The jump integrand at frequency `c` is integrable, by the scaling `s ↦ c s`. -/
theorem integrable_one_sub_cos_mul_div_sq (c : ℝ) :
    Integrable fun s : ℝ => (1 - Real.cos (c * s)) / s ^ 2 := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · have h := (integrable_comp_mul_left_iff (fun y : ℝ => (1 - Real.cos y) / y ^ 2) hc).2
      integrable_one_sub_cos_div_sq
    refine (h.const_mul (c ^ 2)).congr (Eventually.of_forall fun s => ?_)
    show c ^ 2 * ((1 - Real.cos (c * s)) / (c * s) ^ 2) = (1 - Real.cos (c * s)) / s ^ 2
    rcases eq_or_ne s 0 with rfl | hs
    · simp
    · field_simp

/-- Integrating the kernel in the frequency reproduces the second difference of the Cauchy
density, by the product-to-sum formula and the cosine representation. -/
private theorem jumpKernel_integral_freq {t : ℝ} (ht : 0 < t) (x s : ℝ) :
    ∫ ξ : ℝ, jumpKernel t x s ξ
      = (cauchyDensity t (x + s) + cauchyDensity t (x - s) - 2 * cauchyDensity t x) / s ^ 2 := by
  have hpos : (0 : ℝ) < 2 * Real.pi * t := by positivity
  have hid : ∀ ξ : ℝ, jumpKernel t x s ξ
      = (s ^ 2)⁻¹ * (Real.cos (2 * Real.pi * (x + s) * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|))
          + Real.cos (2 * Real.pi * (x - s) * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|))
          - 2 * (Real.cos (2 * Real.pi * x * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|)))) :=
    fun ξ => by
      rw [jumpKernel,
        show 2 * Real.pi * (x + s) * ξ = 2 * Real.pi * x * ξ + 2 * Real.pi * ξ * s from by ring,
        show 2 * Real.pi * (x - s) * ξ = 2 * Real.pi * x * ξ - 2 * Real.pi * ξ * s from by ring,
        Real.cos_add, Real.cos_sub]
      ring
  have hA : Integrable fun ξ : ℝ =>
      Real.cos (2 * Real.pi * (x + s) * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|)) :=
    integrable_cos_mul_exp_neg_mul_abs hpos _
  have hB : Integrable fun ξ : ℝ =>
      Real.cos (2 * Real.pi * (x - s) * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|)) :=
    integrable_cos_mul_exp_neg_mul_abs hpos _
  have hC : Integrable fun ξ : ℝ =>
      Real.cos (2 * Real.pi * x * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|)) :=
    integrable_cos_mul_exp_neg_mul_abs hpos _
  have hsum : Integrable fun ξ : ℝ =>
      Real.cos (2 * Real.pi * (x + s) * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|))
        + Real.cos (2 * Real.pi * (x - s) * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|)) := hA.add hB
  simp only [hid]
  rw [integral_const_mul, integral_sub hsum (hC.const_mul 2), integral_add hA hB,
    integral_const_mul, integral_cos_mul_exp_neg_mul_abs_eq_cauchyDensity ht (x + s),
    integral_cos_mul_exp_neg_mul_abs_eq_cauchyDensity ht (x - s),
    integral_cos_mul_exp_neg_mul_abs_eq_cauchyDensity ht x]
  ring

/-- Integrating the kernel in the step gives the symbol `−2π |2π ξ|` of the jump operator. -/
private theorem jumpKernel_integral_step (t x ξ : ℝ) :
    ∫ s : ℝ, jumpKernel t x s ξ
      = -(Real.cos (2 * Real.pi * x * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|))
        * (2 * Real.pi * |2 * Real.pi * ξ|)) := by
  have hneg : ∀ s : ℝ, (2 * Real.cos (2 * Real.pi * ξ * s) - 2) / s ^ 2
      = -((2 - 2 * Real.cos (2 * Real.pi * ξ * s)) / s ^ 2) := fun s => by ring
  simp only [jumpKernel, hneg, mul_neg]
  rw [integral_neg, integral_const_mul, integral_one_sub_cos_div_sq_eq]

/-- The norm of the kernel: the second difference of a cosine is nonpositive. -/
private theorem norm_jumpKernel (t x s ξ : ℝ) :
    ‖jumpKernel t x s ξ‖ = |Real.cos (2 * Real.pi * x * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|))|
      * ((2 - 2 * Real.cos (2 * Real.pi * ξ * s)) / s ^ 2) := by
  have hle : 2 * Real.cos (2 * Real.pi * ξ * s) - 2 ≤ 0 := by
    linarith [Real.cos_le_one (2 * Real.pi * ξ * s)]
  rw [jumpKernel, Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg (sq_nonneg s),
    abs_of_nonpos hle]
  ring_nf

/-- The exact inner integral of the norm of the kernel, by the jump integral. -/
private theorem integral_norm_jumpKernel (t x ξ : ℝ) :
    ∫ s : ℝ, ‖jumpKernel t x s ξ‖
      = |Real.cos (2 * Real.pi * x * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|))|
        * (2 * Real.pi * |2 * Real.pi * ξ|) := by
  simp only [norm_jumpKernel]
  rw [integral_const_mul, integral_one_sub_cos_div_sq_eq]

/-- The double integral is absolutely convergent: the inner integral of the norm is dominated by
`4π² |ξ| e^{−2π t |ξ|}`. -/
private theorem integrable_jumpKernel {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable (Function.uncurry (jumpKernel t x)) (volume.prod volume) := by
  have hpos : (0 : ℝ) < 2 * Real.pi * t := by positivity
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hmeas : AEStronglyMeasurable (Function.uncurry (jumpKernel t x)) (volume.prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    unfold Function.uncurry jumpKernel
    fun_prop
  refine (integrable_prod_iff' hmeas).2 ⟨Eventually.of_forall fun ξ => ?_, ?_⟩
  · show Integrable fun s : ℝ => jumpKernel t x s ξ
    refine ((integrable_one_sub_cos_mul_div_sq (2 * Real.pi * ξ)).const_mul
      (-2 * (Real.cos (2 * Real.pi * x * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|))))).congr
      (Eventually.of_forall fun s => ?_)
    simp only [jumpKernel]
    ring
  · have hfun : (fun ξ : ℝ => ∫ s : ℝ, ‖Function.uncurry (jumpKernel t x) (s, ξ)‖)
        = fun ξ : ℝ => |Real.cos (2 * Real.pi * x * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|))|
          * (2 * Real.pi * |2 * Real.pi * ξ|) := funext fun ξ => integral_norm_jumpKernel t x ξ
    rw [hfun]
    refine Integrable.mono' ((integrable_abs_mul_exp_neg_mul_abs hpos).const_mul
      (4 * Real.pi ^ 2)) (by fun_prop) (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤
      |Real.cos (2 * Real.pi * x * ξ) * Real.exp (-(2 * Real.pi * t * |ξ|))|
        * (2 * Real.pi * |2 * Real.pi * ξ|)), abs_mul, abs_of_pos (Real.exp_pos _), abs_mul,
      abs_of_pos hpi]
    calc |Real.cos (2 * Real.pi * x * ξ)| * Real.exp (-(2 * Real.pi * t * |ξ|))
          * (2 * Real.pi * (2 * Real.pi * |ξ|))
        ≤ 1 * Real.exp (-(2 * Real.pi * t * |ξ|)) * (2 * Real.pi * (2 * Real.pi * |ξ|)) := by
          gcongr
          exact Real.abs_cos_le_one _
      _ = 4 * Real.pi ^ 2 * (|ξ| * Real.exp (-(2 * Real.pi * t * |ξ|))) := by ring

/-! ### The one-dimensional semigroup identity -/

/-- The integrand of `jumpGen1 1 (cauchyDensity t)` is integrable: it is the inner integral of the
absolutely convergent double integral of `jumpKernel`. -/
theorem integrable_secondDiff_cauchyDensity {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Integrable fun s : ℝ => (cauchyDensity t (x + s) + cauchyDensity t (x - s)
      - 2 * cauchyDensity t x) * |s| ^ (-(1 + (1 : ℝ))) := by
  refine (integrable_jumpKernel ht x).integral_prod_left.congr
    (Eventually.of_forall fun s => ?_)
  show (∫ ξ : ℝ, jumpKernel t x s ξ)
    = (cauchyDensity t (x + s) + cauchyDensity t (x - s) - 2 * cauchyDensity t x)
      * |s| ^ (-(1 + (1 : ℝ)))
  rw [jumpKernel_integral_freq ht x s, abs_rpow_neg_two]
  ring

/-- The unnormalised one-dimensional jump integral of the Cauchy density. -/
theorem jumpGen1_cauchyDensity_eq {t : ℝ} (ht : 0 < t) (x : ℝ) :
    jumpGen1 1 (cauchyDensity t) x = 2 * (x ^ 2 - t ^ 2) / (t ^ 2 + x ^ 2) ^ 2 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hstep1 : jumpGen1 1 (cauchyDensity t) x = ∫ s : ℝ, ∫ ξ : ℝ, jumpKernel t x s ξ := by
    rw [jumpGen1]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [jumpKernel_integral_freq ht x s, abs_rpow_neg_two]
    ring
  have hstep2 : ∫ ξ : ℝ, (∫ s : ℝ, jumpKernel t x s ξ)
      = ∫ ξ : ℝ, -(4 * Real.pi ^ 2)
        * (|ξ| * Real.exp (-(2 * Real.pi * t * |ξ|)) * Real.cos (2 * Real.pi * x * ξ)) := by
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    have habs : |2 * Real.pi * ξ| = 2 * Real.pi * |ξ| := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    simp only [jumpKernel_integral_step, habs]
    ring
  rw [hstep1, integral_integral_swap (integrable_jumpKernel ht x), hstep2, integral_const_mul,
    integral_abs_mul_exp_neg_mul_abs_mul_cos (a := 2 * Real.pi * t) (by positivity)
      (2 * Real.pi * x)]
  have h : t ^ 2 + x ^ 2 ≠ 0 := by positivity
  field_simp
  ring

/-- The time derivative of the Cauchy density, `∂_t q_t (x) = (x² − t²)/(π (t² + x²)²)`. -/
theorem hasDerivAt_cauchyDensity (x : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => cauchyDensity t x) ((x ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + x ^ 2) ^ 2)) t
    := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hden : (0 : ℝ) < Real.pi * (t ^ 2 + x ^ 2) := by positivity
  have hd : HasDerivAt (fun s : ℝ => Real.pi * (s ^ 2 + x ^ 2)) (Real.pi * (2 * t)) t := by
    simpa using ((hasDerivAt_pow 2 t).add_const (x ^ 2)).const_mul Real.pi
  simp only [cauchyDensity]
  refine ((hasDerivAt_id' (x := t)).fun_div hd hden.ne').congr_deriv ?_
  field_simp
  ring

/-- **The one-dimensional Cauchy semigroup identity.** The normalised jump generator of order
`α = 1`, with the constant `c_1 / 2 = 1 / (2π)`, applied to the Cauchy density is its time
derivative. -/
theorem jumpGen1_cauchyDensity {t : ℝ} (ht : 0 < t) (x : ℝ) :
    (1 / (2 * Real.pi)) * jumpGen1 1 (cauchyDensity t) x
      = (x ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + x ^ 2) ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have h : t ^ 2 + x ^ 2 ≠ 0 := by positivity
  rw [jumpGen1_cauchyDensity_eq ht x]
  field_simp

/-! ### The Fourier symbols -/

/-- The Fourier transform of an even real integrable function is its cosine transform. -/
private theorem fourierIntegral_ofReal_of_even {G : ℝ → ℝ} (hG : Integrable G)
    (heven : ∀ ξ : ℝ, G (-ξ) = G ξ) (x : ℝ) :
    𝓕 (fun ξ : ℝ => (G ξ : ℂ)) x
      = ((∫ ξ : ℝ, Real.cos (2 * Real.pi * x * ξ) * G ξ : ℝ) : ℂ) := by
  have hcosint : Integrable fun ξ : ℝ => Real.cos (2 * Real.pi * x * ξ) * G ξ := by
    refine Integrable.mono' hG.norm (by fun_prop) (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_cos_le_one _)
  have hsinint : Integrable fun ξ : ℝ => Real.sin (2 * Real.pi * x * ξ) * G ξ := by
    refine Integrable.mono' hG.norm (by fun_prop) (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) (Real.abs_sin_le_one _)
  have hsin : ∫ ξ : ℝ, Real.sin (2 * Real.pi * x * ξ) * G ξ = 0 := by
    have h := integral_neg_eq_self (fun ξ : ℝ => Real.sin (2 * Real.pi * x * ξ) * G ξ) volume
    have h2 : ∀ ξ : ℝ, Real.sin (2 * Real.pi * x * -ξ) * G (-ξ)
        = -(Real.sin (2 * Real.pi * x * ξ) * G ξ) := fun ξ => by
      rw [mul_neg, Real.sin_neg, heven, neg_mul]
    simp only [h2] at h
    rw [integral_neg] at h
    linarith
  have hsplit : ∀ ξ : ℝ, Complex.exp (((-2 * Real.pi * ξ * x : ℝ) : ℂ) * Complex.I) * (G ξ : ℂ)
      = ((Real.cos (2 * Real.pi * x * ξ) * G ξ : ℝ) : ℂ)
        + ((-(Real.sin (2 * Real.pi * x * ξ) * G ξ) : ℝ) : ℂ) * Complex.I := fun ξ => by
    rw [Complex.exp_mul_I]
    have hph : ((-2 * Real.pi * ξ * x : ℝ) : ℂ) = ((-(2 * Real.pi * x * ξ) : ℝ) : ℂ) := by
      norm_num; ring_nf
    rw [hph, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  have hsin2 : Integrable fun ξ : ℝ => -(Real.sin (2 * Real.pi * x * ξ) * G ξ) := hsinint.neg
  have hadd : ∫ v : ℝ, (((Real.cos (2 * Real.pi * x * v) * G v : ℝ) : ℂ)
        + ((-(Real.sin (2 * Real.pi * x * v) * G v) : ℝ) : ℂ) * Complex.I)
      = (∫ v : ℝ, ((Real.cos (2 * Real.pi * x * v) * G v : ℝ) : ℂ))
        + ∫ v : ℝ, ((-(Real.sin (2 * Real.pi * x * v) * G v) : ℝ) : ℂ) * Complex.I :=
    integral_add hcosint.ofReal (hsin2.ofReal.mul_const Complex.I)
  have hmulc : ∫ v : ℝ, ((-(Real.sin (2 * Real.pi * x * v) * G v) : ℝ) : ℂ) * Complex.I
      = (∫ v : ℝ, ((-(Real.sin (2 * Real.pi * x * v) * G v) : ℝ) : ℂ)) * Complex.I :=
    integral_mul_const _ _
  have hre : ∫ v : ℝ, ((Real.cos (2 * Real.pi * x * v) * G v : ℝ) : ℂ)
      = ((∫ v : ℝ, Real.cos (2 * Real.pi * x * v) * G v : ℝ) : ℂ) := integral_ofReal
  have him : ∫ v : ℝ, ((-(Real.sin (2 * Real.pi * x * v) * G v) : ℝ) : ℂ)
      = ((∫ v : ℝ, -(Real.sin (2 * Real.pi * x * v) * G v) : ℝ) : ℂ) := integral_ofReal
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul, hsplit]
  rw [hadd, hmulc, hre, him, integral_neg, hsin]
  simp

/-- The Fourier transform is homogeneous. -/
private theorem fourierIntegral_const_mul (c : ℂ) (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x : ℝ => c * f x) ξ = c * 𝓕 f ξ := by
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
    ← integral_const_mul]
  simp only [smul_eq_mul]
  exact integral_congr_ae (Eventually.of_forall fun v => by ring)

/-- The time derivative of the Cauchy density is integrable: it is dominated by `q_t / t`. -/
theorem integrable_deriv_cauchyDensity {t : ℝ} (ht : 0 < t) :
    Integrable fun x : ℝ => (x ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + x ^ 2) ^ 2) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hcont : Continuous fun x : ℝ => (x ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + x ^ 2) ^ 2) :=
    Continuous.div (by fun_prop : Continuous fun x : ℝ => x ^ 2 - t ^ 2)
      (by fun_prop : Continuous fun x : ℝ => Real.pi * (t ^ 2 + x ^ 2) ^ 2)
      fun x => by positivity
  refine Integrable.mono' ((integrable_cauchyDensity ht).div_const t)
    hcont.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hd : (0 : ℝ) < Real.pi * (t ^ 2 + x ^ 2) ^ 2 := by positivity
  have hnum : |x ^ 2 - t ^ 2| ≤ t ^ 2 + x ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg t]
  have hq : cauchyDensity t x / t = 1 / (Real.pi * (t ^ 2 + x ^ 2)) := by
    rw [cauchyDensity]
    field_simp
  show ‖(x ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + x ^ 2) ^ 2)‖ ≤ cauchyDensity t x / t
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hd, hq, div_le_div_iff₀ hd (by positivity)]
  calc |x ^ 2 - t ^ 2| * (Real.pi * (t ^ 2 + x ^ 2))
      ≤ (t ^ 2 + x ^ 2) * (Real.pi * (t ^ 2 + x ^ 2)) := by gcongr
    _ = 1 * (Real.pi * (t ^ 2 + x ^ 2) ^ 2) := by ring

/-- **The Fourier transform of the time derivative of the Cauchy density.** With Mathlib's
normalisation, `𝓕 (∂_t q_t) ξ = −2π |ξ| e^{−2π t |ξ|}`, by Fourier inversion from the weighted
cosine transform of the symbol. -/
theorem fourierIntegral_deriv_cauchyDensity {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (((x ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + x ^ 2) ^ 2) : ℝ) : ℂ)) ξ
      = ((-(2 * Real.pi * |ξ|) * Real.exp (-(2 * Real.pi * t * |ξ|)) : ℝ) : ℂ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpos : (0 : ℝ) < 2 * Real.pi * t := by positivity
  have hGint : Integrable fun ζ : ℝ => -(2 * Real.pi * |ζ|)
      * Real.exp (-(2 * Real.pi * t * |ζ|)) := by
    refine ((integrable_abs_mul_exp_neg_mul_abs hpos).const_mul (-(2 * Real.pi))).congr
      (Eventually.of_forall fun ζ => by ring)
  have hGcont : Continuous fun ζ : ℝ =>
      ((-(2 * Real.pi * |ζ|) * Real.exp (-(2 * Real.pi * t * |ζ|)) : ℝ) : ℂ) := by fun_prop
  have hFG : 𝓕 (fun ζ : ℝ => ((-(2 * Real.pi * |ζ|)
        * Real.exp (-(2 * Real.pi * t * |ζ|)) : ℝ) : ℂ))
      = fun y : ℝ => (((y ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + y ^ 2) ^ 2) : ℝ) : ℂ) := by
    funext y
    rw [fourierIntegral_ofReal_of_even hGint (fun ζ => by rw [abs_neg]) y]
    congr 1
    have hcongr : ∀ ζ : ℝ, Real.cos (2 * Real.pi * y * ζ)
        * (-(2 * Real.pi * |ζ|) * Real.exp (-(2 * Real.pi * t * |ζ|)))
        = -(2 * Real.pi) * (|ζ| * Real.exp (-(2 * Real.pi * t * |ζ|))
          * Real.cos (2 * Real.pi * y * ζ)) := fun ζ => by ring
    simp only [hcongr]
    rw [integral_const_mul, integral_abs_mul_exp_neg_mul_abs_mul_cos (a := 2 * Real.pi * t)
      (by positivity) (2 * Real.pi * y)]
    have h : t ^ 2 + y ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  have hFGint : Integrable (𝓕 fun ζ : ℝ =>
      ((-(2 * Real.pi * |ζ|) * Real.exp (-(2 * Real.pi * t * |ζ|)) : ℝ) : ℂ)) := by
    rw [hFG]
    exact (integrable_deriv_cauchyDensity ht).ofReal
  have hinv : 𝓕⁻ (fun ζ : ℝ => ((-(2 * Real.pi * |ζ|)
        * Real.exp (-(2 * Real.pi * t * |ζ|)) : ℝ) : ℂ))
      = fun y : ℝ => (((y ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + y ^ 2) ^ 2) : ℝ) : ℂ) := by
    funext y
    rw [Real.fourierInv_eq_fourier_neg, hFG]
    norm_num
  have hmain := hGcont.fourier_fourierInv_eq hGint.ofReal hFGint
  rw [hinv] at hmain
  exact congrFun hmain ξ

/-- **The Fourier transform of the one-dimensional jump integral of the Cauchy density.** The
symbol of the unnormalised jump operator of order `α = 1` is `−2π |2π ξ|`, so
`𝓕 (jumpGen1 1 q_t) ξ = −2π |2π ξ| e^{−2π t |ξ|}` — which is `2π` times
`fourierIntegral_deriv_cauchyDensity`, the analytic form of `jumpGen1_cauchyDensity`. -/
theorem fourierIntegral_jumpGen1_cauchyDensity {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    𝓕 (fun x : ℝ => ((jumpGen1 1 (cauchyDensity t) x : ℝ) : ℂ)) ξ
      = ((-(2 * Real.pi * |2 * Real.pi * ξ|)
        * Real.exp (-(2 * Real.pi * t * |ξ|)) : ℝ) : ℂ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hfun : (fun x : ℝ => ((jumpGen1 1 (cauchyDensity t) x : ℝ) : ℂ))
      = fun x : ℝ => ((2 * Real.pi : ℝ) : ℂ)
        * (((x ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + x ^ 2) ^ 2) : ℝ) : ℂ) := by
    funext x
    have h : t ^ 2 + x ^ 2 ≠ 0 := by positivity
    rw [jumpGen1_cauchyDensity_eq ht x, ← Complex.ofReal_mul]
    congr 1
    field_simp
  have habs : |2 * Real.pi * ξ| = 2 * Real.pi * |ξ| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  rw [hfun, fourierIntegral_const_mul, fourierIntegral_deriv_cauchyDensity ht, habs,
    ← Complex.ofReal_mul]
  congr 1
  ring

/-! ### The two-dimensional semigroup identity -/

/-- The second difference of the product kernel in the first coordinate moves only the first
factor. -/
private theorem secondDiff_heatKernel_zero (t : ℝ) (z : Fin 2 → ℝ) (s : ℝ) :
    secondDiff (heatKernel t) 0 z s
      = (cauchyDensity t (z 0 + s) + cauchyDensity t (z 0 - s) - 2 * cauchyDensity t (z 0))
        * cauchyDensity t (z 1) := by
  simp only [secondDiff, heatKernel, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  norm_num
  ring

/-- The second difference of the product kernel in the second coordinate moves only the second
factor. -/
private theorem secondDiff_heatKernel_one (t : ℝ) (z : Fin 2 → ℝ) (s : ℝ) :
    secondDiff (heatKernel t) 1 z s
      = cauchyDensity t (z 0)
        * (cauchyDensity t (z 1 + s) + cauchyDensity t (z 1 - s) - 2 * cauchyDensity t (z 1)) := by
  simp only [secondDiff, heatKernel, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Pi.single_apply]
  norm_num
  ring

/-- The two-dimensional jump integral of the product kernel splits into its two coordinate jump
integrals. -/
theorem jumpGen_heatKernel_eq (t : ℝ) (z : Fin 2 → ℝ) :
    jumpGen 1 (heatKernel t) z
      = jumpGen1 1 (cauchyDensity t) (z 0) * cauchyDensity t (z 1)
        + cauchyDensity t (z 0) * jumpGen1 1 (cauchyDensity t) (z 1) := by
  rw [jumpGen, Fin.sum_univ_two]
  congr 1
  · rw [jumpGen1, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [secondDiff_heatKernel_zero]
    ring
  · rw [jumpGen1, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [secondDiff_heatKernel_one]
    ring

/-- The time derivative of the two-dimensional semigroup density, by the product rule. -/
theorem hasDerivAt_heatKernel (z : Fin 2 → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => heatKernel t z)
      ((z 0 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 0 ^ 2) ^ 2) * cauchyDensity t (z 1)
        + cauchyDensity t (z 0) * ((z 1 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 1 ^ 2) ^ 2))) t := by
  have h : (fun t : ℝ => heatKernel t z)
      = fun t : ℝ => cauchyDensity t (z 0) * cauchyDensity t (z 1) := rfl
  rw [h]
  exact (hasDerivAt_cauchyDensity (z 0) ht).mul (hasDerivAt_cauchyDensity (z 1) ht)

/-- **The coordinate Cauchy semigroup solves the fractional heat equation.** The normalised jump
generator of order `α = 1`, with the constant `c_1 / 2 = 1 / (2π)`, applied to the semigroup
density is its time derivative. -/
theorem jumpGen_heatKernel {t : ℝ} (ht : 0 < t) (z : Fin 2 → ℝ) :
    (1 / (2 * Real.pi)) * jumpGen 1 (heatKernel t) z
      = (z 0 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 0 ^ 2) ^ 2) * cauchyDensity t (z 1)
        + cauchyDensity t (z 0) * ((z 1 ^ 2 - t ^ 2) / (Real.pi * (t ^ 2 + z 1 ^ 2) ^ 2)) := by
  rw [jumpGen_heatKernel_eq t z,
    show (1 / (2 * Real.pi)) * (jumpGen1 1 (cauchyDensity t) (z 0) * cauchyDensity t (z 1)
        + cauchyDensity t (z 0) * jumpGen1 1 (cauchyDensity t) (z 1))
      = (1 / (2 * Real.pi)) * jumpGen1 1 (cauchyDensity t) (z 0) * cauchyDensity t (z 1)
        + cauchyDensity t (z 0) * ((1 / (2 * Real.pi)) * jumpGen1 1 (cauchyDensity t) (z 1))
      from by ring,
    jumpGen1_cauchyDensity ht (z 0), jumpGen1_cauchyDensity ht (z 1)]

/-- The semigroup identity in the form `A p_t = ∂_t p_t`. -/
theorem jumpGen_heatKernel_deriv {t : ℝ} (ht : 0 < t) (z : Fin 2 → ℝ) :
    (1 / (2 * Real.pi)) * jumpGen 1 (heatKernel t) z = deriv (fun t => heatKernel t z) t := by
  rw [jumpGen_heatKernel ht z, (hasDerivAt_heatKernel z ht).deriv]

end Cauchy

end CenteredMaximal
