/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.JumpGenerator
public import CenteredMaximal.Cauchy.Potential
public import Mathlib.Analysis.Fourier.Inversion
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The symbol of the one-dimensional Cauchy generator

The one-dimensional fractional Laplacian `−|D|` acts on a function through the second difference
`φ(x + s) + φ(x − s) − 2 φ(x)` integrated against `s^{-2}`, and its convolution semigroup is the
Cauchy density `cauchyDensity` of `CenteredMaximal.Cauchy.Potential`. This file proves the two
elementary Fourier-analytic identities that identify the symbol of the generator with `−2π|ξ|`.

* `integral_one_sub_cos_div_sq`: the **jump integral**
  `∫_ℝ (1 − cos (c s)) / s² ds = π |c|`, together with the doubled form
  `integral_one_sub_cos_div_sq_eq`. This is the Fourier side of the second difference: the symbol
  of `s ↦ φ(x + s) + φ(x − s) − 2 φ(x)` is `2 cos (c s) − 2`.
* `fourierIntegral_cauchyDensity`: the **Fourier transform of the Cauchy density**,
  `𝓕 q_t (ξ) = e^{−2π t |ξ|}` for Mathlib's normalisation `𝓕 f ξ = ∫ e^{−2πi x ξ} f x dx`, with the
  real-valued corollary `integral_cos_mul_cauchyDensity`.

## The jump integral

Mathlib has no Dirichlet integral `∫₀^∞ sin y / y dy` — and indeed the Bochner integral of
`sin y / y` over `(0, ∞)` is `0` by convention, since the integrand is not absolutely integrable —
so the usual integration by parts is unavailable. Instead the half-line integral is computed by an
absolutely convergent Fubini argument against the Laplace kernel: `1 / y² = ∫₀^∞ t e^{−t y} dt`
(`integral_Ioi_mul_exp_neg_mul`) turns

`∫₀^∞ (1 − cos y) / y² dy = ∫₀^∞ ∫₀^∞ (1 − cos y) t e^{−t y} dt dy`,

a double integral which is absolutely convergent because the inner integral in `t` reproduces
`(1 − cos y) / y² ≤ 4 / (y² + 1)` (`one_sub_cos_div_sq_le`). Swapping the order and using the
elementary Laplace transforms `∫₀^∞ e^{−a y} dy = 1/a` and `∫₀^∞ e^{−a y} cos (b y) dy =
a / (a² + b²)` (`integral_Ioi_exp_neg_mul_cos`, the real part of `∫₀^∞ e^{(−a + i b) y} dy`) leaves
`∫₀^∞ dt / (t² + 1) = π / 2`, which is `integral_Ioi_one_div_sq_add_sq`. Evenness and the scaling
`s ↦ c s` then give the whole-line statement.

## The Fourier transform of the Cauchy density

The transform is computed in the easy direction and inverted. The two half-line integrals
`∫₀^∞ e^{z ξ} dξ` of `integral_exp_mul_complex_Ioi` and `integral_exp_mul_complex_Iic` give

`𝓕 (ξ ↦ e^{−2π t |ξ|}) (x) = 1/(2πt − 2πi x) + 1/(2πt + 2πi x) = t / (π (t² + x²)) = q_t(x)`

(`fourierIntegral_exp_neg_mul_abs`). Both `ξ ↦ e^{−2π t |ξ|}` and `q_t` are integrable
(`integrable_exp_neg_mul_abs`, `integrable_cauchyDensity`) and the first is continuous, and the
symbol is even, so its inverse transform is also `q_t`; Mathlib's inversion theorem
`Continuous.fourier_fourierInv_eq` therefore returns `𝓕 q_t = e^{−2π t |·|}`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped FourierTransform Topology

namespace CenteredMaximal.Cauchy

/-! ### Elementary half-line Laplace transforms -/

/-- The half-line Laplace transform of a cosine, `∫₀^∞ e^{−a y} cos (b y) dy = a / (a² + b²)`
for `a > 0`: the real part of `∫₀^∞ e^{(−a + i b) y} dy = 1 / (a − i b)`. -/
theorem integral_Ioi_exp_neg_mul_cos {a : ℝ} (ha : 0 < a) (b : ℝ) :
    ∫ y in Ioi (0 : ℝ), Real.exp (-(a * y)) * Real.cos (b * y) = a / (a ^ 2 + b ^ 2) := by
  set z : ℂ := -(a : ℂ) + (b : ℂ) * Complex.I with hzdef
  have hzre : z.re = -a := by simp [hzdef]
  have hzim : z.im = b := by simp [hzdef]
  have hlt : z.re < 0 := by rw [hzre]; linarith
  have hint : IntegrableOn (fun y : ℝ => Complex.exp (z * y)) (Ioi 0) :=
    integrableOn_exp_mul_complex_Ioi hlt 0
  have hmre : ∀ y : ℝ, (z * (y : ℂ)).re = -(a * y) := fun y => by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hzre, hzim]
    ring
  have hmim : ∀ y : ℝ, (z * (y : ℂ)).im = b * y := fun y => by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzre, hzim]
    ring
  have hI : ∫ y in Ioi (0 : ℝ), Complex.exp (z * y) = -1 / z := by
    rw [integral_exp_mul_complex_Ioi hlt 0]
    norm_num
  calc ∫ y in Ioi (0 : ℝ), Real.exp (-(a * y)) * Real.cos (b * y)
      = ∫ y in Ioi (0 : ℝ), (Complex.exp (z * y)).re := by
        refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
        rw [Complex.exp_re, hmre, hmim]
    _ = (∫ y in Ioi (0 : ℝ), Complex.exp (z * y)).re := by simpa using integral_re hint
    _ = a / (a ^ 2 + b ^ 2) := by
        rw [hI, neg_div, one_div, Complex.neg_re, Complex.inv_re, Complex.normSq_apply, hzre,
          hzim]
        ring

/-- The integrand of `integral_Ioi_exp_neg_mul_cos` is integrable on the half-line, being dominated
by `e^{−a y}`. -/
theorem integrableOn_Ioi_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => Real.exp (-(a * y))) (Ioi 0) := by
  simpa only [neg_mul] using integrableOn_exp_mul_Ioi (a := -a) (by linarith) 0

/-- The half-line Laplace transform of the constant function, `∫₀^∞ e^{−a y} dy = 1 / a`. -/
theorem integral_Ioi_exp_neg_mul {a : ℝ} (ha : 0 < a) :
    ∫ y in Ioi (0 : ℝ), Real.exp (-(a * y)) = 1 / a := by
  have h : ∫ y in Ioi (0 : ℝ), Real.exp (-a * y) = -Real.exp (-a * 0) / -a :=
    integral_exp_mul_Ioi (by linarith) 0
  simp only [neg_mul, mul_zero, Real.exp_zero] at h
  rw [h, neg_div_neg_eq]

/-- The integrand of `integral_Ioi_exp_neg_mul_cos` is integrable on the half-line. -/
theorem integrableOn_Ioi_exp_neg_mul_cos {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IntegrableOn (fun y : ℝ => Real.exp (-(a * y)) * Real.cos (b * y)) (Ioi 0) := by
  refine Integrable.mono' (integrableOn_Ioi_exp_neg_mul ha) (by fun_prop)
    (Eventually.of_forall fun y => ?_)
  refine le_of_eq_of_le ?_ (mul_le_of_le_one_right (Real.exp_pos (-(a * y))).le
    (Real.abs_cos_le_one (b * y)))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-! ### The Laplace kernel `1 / y² = ∫₀^∞ t e^{−t y} dt` -/

/-- `s ↦ −(s y + 1) e^{−s y} / y²` is an antiderivative of `s ↦ s e^{−s y}`. -/
private theorem hasDerivAt_laplaceProfile {y : ℝ} (hy : 0 < y) (t : ℝ) :
    HasDerivAt (fun s : ℝ => -((s * y + 1) * Real.exp (-(s * y))) / y ^ 2)
      (t * Real.exp (-(t * y))) t := by
  have hy' : y ≠ 0 := hy.ne'
  have hu : HasDerivAt (fun s : ℝ => s * y + 1) y t := by
    simpa using ((hasDerivAt_id t).mul_const y).add_const 1
  have hv : HasDerivAt (fun s : ℝ => Real.exp (-(s * y))) (Real.exp (-(t * y)) * -y) t := by
    have h₁ : HasDerivAt (fun s : ℝ => -(s * y)) (-y) t := by
      simpa only [id_eq, mul_neg, one_mul] using (hasDerivAt_id t).mul_const (-y)
    exact h₁.exp
  refine (((hu.mul hv).neg).div_const (y ^ 2)).congr_deriv ?_
  field_simp
  ring

/-- The antiderivative `−(s y + 1) e^{−s y} / y²` tends to `0` at infinity. -/
private theorem tendsto_laplaceProfile {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s : ℝ => -((s * y + 1) * Real.exp (-(s * y))) / y ^ 2) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun s : ℝ => s * y) atTop atTop := tendsto_id.atTop_mul_const hy
  have hu : Tendsto (fun u : ℝ => u ^ 1 * Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have he : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have hsum : Tendsto (fun u : ℝ => (u + 1) * Real.exp (-u)) atTop (𝓝 0) := by
    simpa [add_mul, pow_one] using hu.add he
  have h₂ : Tendsto (fun u : ℝ => -((u + 1) * Real.exp (-u)) / y ^ 2) atTop (𝓝 0) := by
    simpa using hsum.neg.div_const (y ^ 2)
  simpa [Function.comp_def] using h₂.comp h₁

/-- The Laplace representation of the inverse square, `∫₀^∞ t e^{−t y} dt = 1 / y²` for `y > 0`. -/
theorem integral_Ioi_mul_exp_neg_mul {y : ℝ} (hy : 0 < y) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-(t * y)) = 1 / y ^ 2 := by
  have key : ∫ t in Ioi (0 : ℝ), t * Real.exp (-(t * y))
      = 0 - -((0 * y + 1) * Real.exp (-(0 * y))) / y ^ 2 :=
    integral_Ioi_of_hasDerivAt_of_nonneg' (fun s _ => hasDerivAt_laplaceProfile hy s)
      (fun _ ht => mul_nonneg (mem_Ioi.mp ht).le (Real.exp_pos _).le) (tendsto_laplaceProfile hy)
  rw [key]
  simp only [zero_mul, zero_add, neg_zero, Real.exp_zero, mul_one]
  ring

/-- The integrand of `integral_Ioi_mul_exp_neg_mul` is integrable on the half-line. -/
theorem integrableOn_Ioi_mul_exp_neg_mul {y : ℝ} (hy : 0 < y) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(t * y))) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun s _ => hasDerivAt_laplaceProfile hy s)
    (fun _ ht => mul_nonneg (mem_Ioi.mp ht).le (Real.exp_pos _).le) (tendsto_laplaceProfile hy)

/-! ### The jump integral -/

/-- The pointwise bound `(1 − cos y) / y² ≤ 4 / (y² + 1)`: near the origin the numerator is at most
`y² / 2`, away from it the numerator is at most `2` and `y² + 1 ≤ 2 y²`. -/
private theorem one_sub_cos_div_sq_le (y : ℝ) :
    (1 - Real.cos y) / y ^ 2 ≤ 4 / (y ^ 2 + 1) := by
  rcases eq_or_ne y 0 with rfl | hy
  · norm_num
  have hy2 : 0 < y ^ 2 := by positivity
  have hcos : 0 ≤ 1 - Real.cos y := by linarith [Real.cos_le_one y]
  have h₁ : 1 - Real.cos y ≤ y ^ 2 / 2 := by linarith [Real.one_sub_sq_div_two_le_cos (x := y)]
  have h₂ : 1 - Real.cos y ≤ 2 := by linarith [Real.neg_one_le_cos y]
  rw [div_le_div_iff₀ hy2 (by positivity)]
  rcases le_or_gt (y ^ 2) 1 with h | h
  · nlinarith
  · nlinarith

/-- The integrand of the jump integral at frequency one is integrable on the line. -/
theorem integrable_one_sub_cos_div_sq :
    Integrable fun y : ℝ => (1 - Real.cos y) / y ^ 2 := by
  have hg : Integrable fun y : ℝ => 4 / (y ^ 2 + 1) := by
    refine (integrable_inv_one_add_sq.const_mul (4 : ℝ)).congr
      (Eventually.of_forall fun y => ?_)
    show 4 * (1 + y ^ 2)⁻¹ = 4 / (y ^ 2 + 1)
    rw [add_comm (1 : ℝ) (y ^ 2), ← div_eq_mul_inv]
  have hmeas : Measurable fun y : ℝ => (1 - Real.cos y) / y ^ 2 := by fun_prop
  refine Integrable.mono' hg hmeas.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (by linarith [Real.cos_le_one y]) (sq_nonneg y))]
  exact one_sub_cos_div_sq_le y

/-- The time slice of the Laplace double integral: integrating in `t` recovers the jump
integrand. -/
private theorem integral_Ioi_laplaceSlice_time {y : ℝ} (hy : 0 < y) :
    ∫ t in Ioi (0 : ℝ), (1 - Real.cos y) * (t * Real.exp (-(t * y)))
      = (1 - Real.cos y) / y ^ 2 := by
  rw [integral_const_mul, integral_Ioi_mul_exp_neg_mul hy, mul_one_div]

/-- The frequency slice of the Laplace double integral: integrating in `y` gives the Cauchy
profile `1 / (t² + 1)`. -/
private theorem integral_Ioi_laplaceSlice_freq {t : ℝ} (ht : 0 < t) :
    ∫ y in Ioi (0 : ℝ), (1 - Real.cos y) * (t * Real.exp (-(t * y)))
      = 1 / (t ^ 2 + 1 ^ 2) := by
  have ht' : t ≠ 0 := ht.ne'
  have hd : t ^ 2 + 1 ^ 2 ≠ 0 := by positivity
  have hsplit : ∀ y : ℝ, (1 - Real.cos y) * (t * Real.exp (-(t * y)))
      = t * Real.exp (-(t * y)) - t * (Real.exp (-(t * y)) * Real.cos (1 * y)) := fun y => by
    rw [one_mul]; ring
  simp only [hsplit]
  rw [integral_sub ((integrableOn_Ioi_exp_neg_mul ht).const_mul t)
      ((integrableOn_Ioi_exp_neg_mul_cos ht 1).const_mul t), integral_const_mul,
    integral_const_mul, integral_Ioi_exp_neg_mul ht, integral_Ioi_exp_neg_mul_cos ht 1]
  field_simp
  ring

/-- The Laplace double integral is absolutely convergent on the quadrant: its slice norms
reproduce the integrable jump integrand. -/
private theorem integrable_laplaceKernel :
    Integrable (Function.uncurry fun y t : ℝ => (1 - Real.cos y) * (t * Real.exp (-(t * y))))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hcont : Continuous fun p : ℝ × ℝ =>
      (1 - Real.cos p.1) * (p.2 * Real.exp (-(p.2 * p.1))) := by fun_prop
  refine (integrable_prod_iff hcont.aestronglyMeasurable).2 ⟨?_, ?_⟩
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_)
    exact (integrableOn_Ioi_mul_exp_neg_mul (mem_Ioi.mp hy)).const_mul (1 - Real.cos y)
  · have heq : EqOn (fun y : ℝ => (1 - Real.cos y) / y ^ 2)
        (fun y : ℝ => ∫ t in Ioi (0 : ℝ), ‖(1 - Real.cos y) * (t * Real.exp (-(t * y)))‖)
        (Ioi 0) := by
      intro y hy
      have hy' : (0 : ℝ) < y := mem_Ioi.mp hy
      have hn : EqOn (fun t : ℝ => ‖(1 - Real.cos y) * (t * Real.exp (-(t * y)))‖)
          (fun t : ℝ => (1 - Real.cos y) * (t * Real.exp (-(t * y)))) (Ioi 0) := by
        intro t ht
        have h0 : 0 ≤ (1 - Real.cos y) * (t * Real.exp (-(t * y))) :=
          mul_nonneg (by linarith [Real.cos_le_one y])
            (mul_nonneg (mem_Ioi.mp ht).le (Real.exp_pos _).le)
        show ‖(1 - Real.cos y) * (t * Real.exp (-(t * y)))‖ = _
        rw [Real.norm_eq_abs, abs_of_nonneg h0]
      show (1 - Real.cos y) / y ^ 2
        = ∫ t in Ioi (0 : ℝ), ‖(1 - Real.cos y) * (t * Real.exp (-(t * y)))‖
      rw [setIntegral_congr_fun measurableSet_Ioi hn, integral_Ioi_laplaceSlice_time hy']
    exact integrable_one_sub_cos_div_sq.integrableOn.congr_fun heq measurableSet_Ioi

/-- **The half-line jump integral** `∫₀^∞ (1 − cos y) / y² dy = π / 2`, by Fubini against the
Laplace kernel `1 / y² = ∫₀^∞ t e^{−t y} dt`. -/
theorem integral_Ioi_one_sub_cos_div_sq :
    ∫ y in Ioi (0 : ℝ), (1 - Real.cos y) / y ^ 2 = Real.pi / 2 := by
  have hleft : ∫ y in Ioi (0 : ℝ), (1 - Real.cos y) / y ^ 2
      = ∫ y in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), (1 - Real.cos y) * (t * Real.exp (-(t * y))) :=
    setIntegral_congr_fun measurableSet_Ioi fun y hy =>
      (integral_Ioi_laplaceSlice_time (mem_Ioi.mp hy)).symm
  have hswap : (∫ y in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ),
        (1 - Real.cos y) * (t * Real.exp (-(t * y))))
      = ∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
        (1 - Real.cos y) * (t * Real.exp (-(t * y))) :=
    integral_integral_swap integrable_laplaceKernel
  have hright : (∫ t in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
      (1 - Real.cos y) * (t * Real.exp (-(t * y)))) = Real.pi / 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioi fun t ht =>
      integral_Ioi_laplaceSlice_freq (mem_Ioi.mp ht), integral_Ioi_one_div_sq_add_sq one_pos]
    norm_num
  rw [hleft, hswap, hright]

/-- The whole-line jump integral at frequency one, `∫_ℝ (1 − cos y) / y² dy = π`. -/
theorem integral_one_sub_cos_div_sq_pi : ∫ y : ℝ, (1 - Real.cos y) / y ^ 2 = Real.pi := by
  rw [integral_of_even (fun y => by simp only [Real.cos_neg, neg_sq])
      integrable_one_sub_cos_div_sq.integrableOn, integral_Ioi_one_sub_cos_div_sq]
  ring

/-- The jump integral at a positive frequency, by the scaling `s ↦ a s`. -/
private theorem integral_one_sub_cos_div_sq_of_pos {a : ℝ} (ha : 0 < a) :
    ∫ s : ℝ, (1 - Real.cos (a * s)) / s ^ 2 = Real.pi * a := by
  have ha' : a ≠ 0 := ha.ne'
  have key : (∫ x : ℝ, (1 - Real.cos (a * x)) / x ^ 2) / a ^ 2 = a⁻¹ * Real.pi := by
    rw [← integral_div]
    have h := Measure.integral_comp_mul_left (fun y : ℝ => (1 - Real.cos y) / y ^ 2) a
    rw [integral_one_sub_cos_div_sq_pi, smul_eq_mul, abs_inv, abs_of_pos ha] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show (1 - Real.cos (a * x)) / x ^ 2 / a ^ 2 = (1 - Real.cos (a * x)) / (a * x) ^ 2
    rw [mul_pow, div_div, mul_comm (x ^ 2) (a ^ 2)]
  rw [div_eq_iff (by positivity : a ^ 2 ≠ 0)] at key
  rw [key]
  linear_combination (Real.pi * a) * inv_mul_cancel₀ ha'

/-- **The jump integral.** `∫_ℝ (1 − cos (c s)) / s² ds = π |c|`: the Fourier symbol of the
one-dimensional second difference against the jump measure `s^{-2} ds`. -/
theorem integral_one_sub_cos_div_sq (c : ℝ) :
    ∫ s : ℝ, (1 - Real.cos (c * s)) / s ^ 2 = Real.pi * |c| := by
  have habs : ∀ s : ℝ, (1 - Real.cos (c * s)) / s ^ 2 = (1 - Real.cos (|c| * s)) / s ^ 2 := by
    intro s
    rcases abs_cases c with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, neg_mul, Real.cos_neg]
  simp only [habs]
  rcases (abs_nonneg c).eq_or_lt with h0 | h0
  · rw [← h0]
    simp
  · exact integral_one_sub_cos_div_sq_of_pos h0

/-- The doubled jump integral `∫_ℝ (2 − 2 cos (c s)) / s² ds = 2 π |c|`, the form in which the
symbol of the second difference appears. -/
theorem integral_one_sub_cos_div_sq_eq (c : ℝ) :
    ∫ s : ℝ, (2 - 2 * Real.cos (c * s)) / s ^ 2 = 2 * Real.pi * |c| := by
  have h : ∀ s : ℝ, (2 - 2 * Real.cos (c * s)) / s ^ 2
      = 2 * ((1 - Real.cos (c * s)) / s ^ 2) := fun s => by ring
  simp only [h]
  rw [integral_const_mul, integral_one_sub_cos_div_sq]
  ring

/-! ### The Fourier transform of the Cauchy density -/

/-- The Cauchy density of positive scale is integrable: it is a rescaling of `(1 + y²)⁻¹`. -/
theorem integrable_cauchyDensity {t : ℝ} (ht : 0 < t) : Integrable (cauchyDensity t) := by
  have ht' : t ≠ 0 := ht.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hkey : cauchyDensity t = fun x : ℝ => 1 / (Real.pi * t) * (1 + (t⁻¹ * x) ^ 2)⁻¹ := by
    funext x
    have h₁ : t ^ 2 + x ^ 2 ≠ 0 := by positivity
    rw [cauchyDensity]
    field_simp
  rw [hkey]
  exact ((integrable_comp_mul_left_iff (fun y : ℝ => (1 + y ^ 2)⁻¹)
    (inv_ne_zero ht')).2 integrable_inv_one_add_sq).const_mul _

/-- The symbol `ξ ↦ e^{−a |ξ|}` is integrable on the line for `a > 0`. -/
theorem integrable_exp_neg_mul_abs {a : ℝ} (ha : 0 < a) :
    Integrable fun ξ : ℝ => Real.exp (-(a * |ξ|)) := by
  refine integrable_of_even (fun ξ => by rw [abs_neg]) ?_
  refine (integrableOn_Ioi_exp_neg_mul ha).congr_fun (fun ξ hξ => ?_) measurableSet_Ioi
  rw [abs_of_pos (mem_Ioi.mp hξ)]

/-- The partial fraction identity `1/(A − iB) + 1/(A + iB) = 2A/(A² + B²)` for real `A > 0`. -/
private theorem inv_add_inv_ofReal_mul_I {A B : ℝ} (hA : 0 < A) :
    1 / ((A : ℂ) - (B : ℂ) * Complex.I) + 1 / ((A : ℂ) + (B : ℂ) * Complex.I)
      = ((2 * A / (A ^ 2 + B ^ 2) : ℝ) : ℂ) := by
  have hre₁ : ((A : ℂ) + (B : ℂ) * Complex.I).re = A := by simp
  have hre₂ : ((A : ℂ) - (B : ℂ) * Complex.I).re = A := by simp
  have h₁ : (A : ℂ) + (B : ℂ) * Complex.I ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre₁
    exact hA.ne hre₁
  have h₂ : (A : ℂ) - (B : ℂ) * Complex.I ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre₂
    exact hA.ne hre₂
  have hmul : ((A : ℂ) - (B : ℂ) * Complex.I) * ((A : ℂ) + (B : ℂ) * Complex.I)
      = ((A ^ 2 + B ^ 2 : ℝ) : ℂ) := by
    push_cast
    linear_combination (-((B : ℂ) ^ 2)) * Complex.I_sq
  have hadd : (1 : ℂ) * ((A : ℂ) + (B : ℂ) * Complex.I)
      + ((A : ℂ) - (B : ℂ) * Complex.I) * 1 = ((2 * A : ℝ) : ℂ) := by
    push_cast
    ring
  rw [div_add_div _ _ h₂ h₁, hadd, hmul, ← Complex.ofReal_div]

/-- The two half-line exponential integrals that compute the transform of the symbol. -/
private theorem integral_exp_neg_mul_abs_mul_exp {A B : ℝ} (hA : 0 < A) :
    ∫ v : ℝ, Complex.exp (((-(B * v) : ℝ) : ℂ) * Complex.I)
        * ((Real.exp (-(A * |v|)) : ℝ) : ℂ)
      = ((2 * A / (A ^ 2 + B ^ 2) : ℝ) : ℂ) := by
  have hz₁re : (-((A : ℂ) + (B : ℂ) * Complex.I)).re = -A := by simp
  have hz₂re : ((A : ℂ) - (B : ℂ) * Complex.I).re = A := by simp
  have hlt : (-((A : ℂ) + (B : ℂ) * Complex.I)).re < 0 := by rw [hz₁re]; linarith
  have hgt : (0 : ℝ) < ((A : ℂ) - (B : ℂ) * Complex.I).re := by rw [hz₂re]; exact hA
  have hIoi : EqOn (fun v : ℝ => Complex.exp (((-(B * v) : ℝ) : ℂ) * Complex.I)
      * ((Real.exp (-(A * |v|)) : ℝ) : ℂ))
      (fun v : ℝ => Complex.exp ((-((A : ℂ) + (B : ℂ) * Complex.I)) * v)) (Ioi 0) := by
    intro v hv
    show Complex.exp (((-(B * v) : ℝ) : ℂ) * Complex.I) * ((Real.exp (-(A * |v|)) : ℝ) : ℂ)
      = Complex.exp ((-((A : ℂ) + (B : ℂ) * Complex.I)) * v)
    rw [Complex.ofReal_exp, ← Complex.exp_add, abs_of_pos (mem_Ioi.mp hv)]
    congr 1
    push_cast
    ring
  have hIic : EqOn (fun v : ℝ => Complex.exp (((-(B * v) : ℝ) : ℂ) * Complex.I)
      * ((Real.exp (-(A * |v|)) : ℝ) : ℂ))
      (fun v : ℝ => Complex.exp (((A : ℂ) - (B : ℂ) * Complex.I) * v)) (Iic 0) := by
    intro v hv
    show Complex.exp (((-(B * v) : ℝ) : ℂ) * Complex.I) * ((Real.exp (-(A * |v|)) : ℝ) : ℂ)
      = Complex.exp (((A : ℂ) - (B : ℂ) * Complex.I) * v)
    rw [Complex.ofReal_exp, ← Complex.exp_add, abs_of_nonpos (mem_Iic.mp hv)]
    congr 1
    push_cast
    ring
  have hintIoi : IntegrableOn (fun v : ℝ => Complex.exp (((-(B * v) : ℝ) : ℂ) * Complex.I)
      * ((Real.exp (-(A * |v|)) : ℝ) : ℂ)) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi hlt 0).congr_fun hIoi.symm measurableSet_Ioi
  have hintIic : IntegrableOn (fun v : ℝ => Complex.exp (((-(B * v) : ℝ) : ℂ) * Complex.I)
      * ((Real.exp (-(A * |v|)) : ℝ) : ℂ)) (Iic 0) :=
    (integrableOn_exp_mul_complex_Iic hgt 0).congr_fun hIic.symm measurableSet_Iic
  rw [← intervalIntegral.integral_Iic_add_Ioi hintIic hintIoi,
    setIntegral_congr_fun measurableSet_Iic hIic,
    setIntegral_congr_fun measurableSet_Ioi hIoi,
    integral_exp_mul_complex_Iic hgt 0, integral_exp_mul_complex_Ioi hlt 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, neg_div_neg_eq]
  exact inv_add_inv_ofReal_mul_I hA

/-- The Fourier transform of the symbol `e^{−2π t |ξ|}` is the Cauchy density of scale `t`. -/
theorem fourierIntegral_exp_neg_mul_abs {t : ℝ} (ht : 0 < t) (x : ℝ) :
    𝓕 (fun ξ : ℝ => ((Real.exp (-(2 * Real.pi * t * |ξ|)) : ℝ) : ℂ)) x
      = (cauchyDensity t x : ℂ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hA : (0 : ℝ) < 2 * Real.pi * t := by positivity
  have hcongr : ∀ v : ℝ, (-2 * Real.pi * v * x : ℝ) = -(2 * Real.pi * x * v) := fun v => by ring
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [hcongr, smul_eq_mul]
  rw [integral_exp_neg_mul_abs_mul_exp hA]
  congr 1
  have h₁ : t ^ 2 + x ^ 2 ≠ 0 := by positivity
  rw [cauchyDensity]
  field_simp

/-- **The Fourier transform of the Cauchy density.** With Mathlib's normalisation
`𝓕 f ξ = ∫ e^{−2πi x ξ} f x dx`, the Cauchy density of scale `t > 0` transforms to the symbol
`e^{−2π t |ξ|}` of the one-dimensional generator `−|D|`. -/
theorem fourierIntegral_cauchyDensity {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (cauchyDensity t x : ℂ)) ξ
      = (Real.exp (-(2 * Real.pi * t * |ξ|)) : ℂ) := by
  have hA : (0 : ℝ) < 2 * Real.pi * t := by positivity
  have hcont : Continuous fun ζ : ℝ => ((Real.exp (-(2 * Real.pi * t * |ζ|)) : ℝ) : ℂ) := by
    fun_prop
  have hgint : Integrable fun ζ : ℝ => ((Real.exp (-(2 * Real.pi * t * |ζ|)) : ℝ) : ℂ) :=
    (integrable_exp_neg_mul_abs hA).ofReal
  have hFg : 𝓕 (fun ζ : ℝ => ((Real.exp (-(2 * Real.pi * t * |ζ|)) : ℝ) : ℂ))
      = fun y : ℝ => (cauchyDensity t y : ℂ) :=
    funext fun y => fourierIntegral_exp_neg_mul_abs ht y
  have hFgint : Integrable
      (𝓕 fun ζ : ℝ => ((Real.exp (-(2 * Real.pi * t * |ζ|)) : ℝ) : ℂ)) := by
    rw [hFg]
    exact (integrable_cauchyDensity ht).ofReal
  have hinv : 𝓕⁻ (fun ζ : ℝ => ((Real.exp (-(2 * Real.pi * t * |ζ|)) : ℝ) : ℂ))
      = fun y : ℝ => (cauchyDensity t y : ℂ) := by
    funext y
    rw [Real.fourierInv_eq_fourier_neg, hFg]
    simp [cauchyDensity_neg]
  have hmain := hcont.fourier_fourierInv_eq hgint hFgint
  rw [hinv] at hmain
  exact congrFun hmain ξ

/-- The real form of `fourierIntegral_cauchyDensity`: the cosine transform of the Cauchy density
is the symbol `e^{−2π t |ξ|}`. The sine part vanishes because the density is even. -/
theorem integral_cos_mul_cauchyDensity {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    ∫ x : ℝ, Real.cos (2 * Real.pi * x * ξ) * cauchyDensity t x
      = Real.exp (-(2 * Real.pi * t * |ξ|)) := by
  have hcont : Continuous fun x : ℝ =>
      Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) * (cauchyDensity t x : ℂ) := by
    have h₁ : Continuous fun x : ℝ =>
        Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) := by fun_prop
    exact h₁.mul (Complex.continuous_ofReal.comp (continuous_cauchyDensity ht))
  have hint : Integrable fun x : ℝ =>
      Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I) * (cauchyDensity t x : ℂ) := by
    refine Integrable.mono' (integrable_cauchyDensity ht) hcont.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    refine le_of_eq ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cauchyDensity_nonneg ht.le x)]
  have hre : ∀ x : ℝ, (Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)
      * (cauchyDensity t x : ℂ)).re = Real.cos (2 * Real.pi * x * ξ) * cauchyDensity t x := by
    intro x
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.exp_ofReal_mul_I_re,
      show (-2 * Real.pi * x * ξ : ℝ) = -(2 * Real.pi * x * ξ) by ring, Real.cos_neg]
  have hF : 𝓕 (fun x : ℝ => (cauchyDensity t x : ℂ)) ξ
      = ∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)
        * (cauchyDensity t x : ℂ) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
  calc ∫ x : ℝ, Real.cos (2 * Real.pi * x * ξ) * cauchyDensity t x
      = ∫ x : ℝ, (Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)
          * (cauchyDensity t x : ℂ)).re :=
        integral_congr_ae (Eventually.of_forall fun x => (hre x).symm)
    _ = (∫ x : ℝ, Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)
          * (cauchyDensity t x : ℂ)).re := by simpa using integral_re hint
    _ = Real.exp (-(2 * Real.pi * t * |ξ|)) := by
        rw [← hF, fourierIntegral_cauchyDensity ht ξ, Complex.ofReal_re]

end CenteredMaximal.Cauchy
