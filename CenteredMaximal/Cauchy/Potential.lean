/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Cauchy.LooseKernel
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The coordinate Cauchy semigroup and its potential kernel

The symmetric coordinate Cauchy generator `A = −|D_u| − |D_v|` of the diamond coordinates is the
sum of two one-dimensional fractional Laplacians, one in each coordinate, so its convolution
semigroup is the product of two one-dimensional Cauchy densities:

`heatKernel t (u, v) = t² / (π² (t² + u²) (t² + v²))`.

It is a probability density for every `t > 0` (`integral_heatKernel`), and its potential kernel is
the time integral

`potential (u, v) = ∫₀^∞ heatKernel t (u, v) dt = 1 / (2π (|u| + |v|))`,

so the level sets of the potential are exactly the diamonds of `LooseKernel`, whose radius is
`diamondNorm`. This is `integral_Ioi_heatKernel`, the main result of this file.

The time integral is computed by partial fractions. Writing `a = |u|` and `b = |v|`, the integrand
is `t² / (π² (t² + a²) (t² + b²))`, and for `a ≠ b`

`t² / ((t² + a²) (t² + b²)) = (b² / (t² + b²) − a² / (t² + a²)) / (b² − a²)`,

whose half-line integral is `(b² · π/(2b) − a² · π/(2a)) / (b² − a²) = π / (2 (a + b))`. The two
half-line integrals used are `integral_Ioi_one_div_sq_add_sq` and, in the degenerate case `a = b`,
`integral_Ioi_sq_div_sq_add_sq_sq`; both come from the fundamental theorem of calculus with the
antiderivatives `arctan (t/a) / a` and `arctan (t/a) / (2a) − t / (2 (t² + a²))`. Their derivatives
are nonnegative, so `integral_Ioi_of_hasDerivAt_of_nonneg'` supplies the integrability for free.
The remaining case, one of `a` and `b` zero, is a single arctangent integral; it is here that
`z ≠ 0` is needed.

Finally the potential is locally integrable: the radial formula `lintegral_comp_diamondNorm` turns
its integral over the diamond `{r ≤ R}` into `∫₀^R 4t / (2πt) dt = 2R/π`, which is
`lintegral_potential_diamond`. Sup balls are not diamonds, but `‖z‖ ≤ diamondNorm z ≤ 2 ‖z‖`, so
the ball version `integrableOn_potential_closedBall` follows by monotonicity.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace CenteredMaximal.Cauchy

/-- The one-dimensional Cauchy density of scale `t`. -/
def cauchyDensity (t x : ℝ) : ℝ := t / (Real.pi * (t ^ 2 + x ^ 2))

/-- The two-dimensional coordinate-Cauchy semigroup density. -/
def heatKernel (t : ℝ) (z : Fin 2 → ℝ) : ℝ := cauchyDensity t (z 0) * cauchyDensity t (z 1)

/-- The potential kernel `1 / (2π r)` of the coordinate Cauchy generator, `r` the diamond radius. -/
def potential (z : Fin 2 → ℝ) : ℝ := 1 / (2 * Real.pi * diamondNorm z)

/-! ### Two arctangent integrals -/

/-- `t ↦ arctan (t / a) / a` is an antiderivative of `t ↦ 1 / (t² + a²)`. -/
private theorem hasDerivAt_arctanScale {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.arctan (s / a) / a) (1 / (t ^ 2 + a ^ 2)) t := by
  have ha' : a ≠ 0 := ha.ne'
  have h₁ : (1 : ℝ) + (t / a) ^ 2 ≠ 0 := by positivity
  have h₂ : t ^ 2 + a ^ 2 ≠ 0 := by positivity
  refine (((hasDerivAt_id' (x := t)).div_const a).arctan.div_const a).congr_deriv ?_
  field_simp
  ring

/-- The antiderivative `arctan (t / a) / a` tends to `π / 2 / a` at infinity. -/
private theorem tendsto_arctanScale {a : ℝ} (ha : 0 < a) :
    Tendsto (fun s : ℝ => Real.arctan (s / a) / a) atTop (𝓝 (Real.pi / 2 / a)) :=
  Tendsto.div_const ((tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
    (tendsto_id.atTop_div_const ha)) a

/-- The half-line Cauchy integral `∫₀^∞ dt / (t² + a²) = π / (2a)`. -/
theorem integral_Ioi_one_div_sq_add_sq {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ in Ioi 0, 1 / (t ^ 2 + a ^ 2) = Real.pi / (2 * a) := by
  have key : ∫ t : ℝ in Ioi (0 : ℝ), 1 / (t ^ 2 + a ^ 2)
      = Real.pi / 2 / a - Real.arctan (0 / a) / a :=
    integral_Ioi_of_hasDerivAt_of_nonneg' (fun s _ => hasDerivAt_arctanScale ha s)
      (fun t _ => by positivity) (tendsto_arctanScale ha)
  rw [key, zero_div, Real.arctan_zero, zero_div, sub_zero, div_div]

/-- The integrand of `integral_Ioi_one_div_sq_add_sq` is integrable on the half-line. -/
theorem integrableOn_Ioi_one_div_sq_add_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => 1 / (t ^ 2 + a ^ 2)) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun s _ => hasDerivAt_arctanScale ha s)
    (fun t _ => by positivity) (tendsto_arctanScale ha)

/-- The whole-line Cauchy integral `∫ dt / (t² + a²) = π / a`, by the scaling `t = a s`. -/
theorem integral_one_div_sq_add_sq {a : ℝ} (ha : 0 < a) :
    ∫ x : ℝ, 1 / (x ^ 2 + a ^ 2) = Real.pi / a := by
  have ha' : a ≠ 0 := ha.ne'
  have key := Measure.integral_comp_div (fun y : ℝ => (1 + y ^ 2)⁻¹) a
  rw [integral_univ_inv_one_add_sq, smul_eq_mul, abs_of_pos ha] at key
  have h : ∀ x : ℝ, (1 + (x / a) ^ 2)⁻¹ = a ^ 2 * (1 / (x ^ 2 + a ^ 2)) := fun x => by
    have h₁ : x ^ 2 + a ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  simp_rw [h] at key
  rw [integral_const_mul] at key
  refine mul_left_cancel₀ (pow_ne_zero 2 ha') ?_
  rw [key]
  field_simp

/-- `t ↦ arctan (t / a) / a / 2 − t / (2 (t² + a²))` is an antiderivative of
`t ↦ t² / (t² + a²)²`. -/
private theorem hasDerivAt_sqScale {a : ℝ} (ha : 0 < a) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.arctan (s / a) / a / 2 - s / (2 * (s ^ 2 + a ^ 2)))
      (t ^ 2 / (t ^ 2 + a ^ 2) ^ 2) t := by
  have hden : t ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hpos : (0 : ℝ) < 2 * (t ^ 2 + a ^ 2) := by positivity
  have hd : HasDerivAt (fun s : ℝ => 2 * (s ^ 2 + a ^ 2)) (4 * t) t :=
    (((hasDerivAt_pow 2 t).add_const (a ^ 2)).const_mul (2 : ℝ)).congr_deriv (by push_cast; ring)
  refine (((hasDerivAt_arctanScale ha t).div_const 2).sub
    ((hasDerivAt_id' (x := t)).fun_div hd hpos.ne')).congr_deriv ?_
  field_simp
  ring

/-- The antiderivative `arctan (t / a) / a / 2 − t / (2 (t² + a²))` tends to `π / 2 / a / 2` at
infinity: the rational part is squeezed between `0` and `t⁻¹`. -/
private theorem tendsto_sqScale {a : ℝ} (ha : 0 < a) :
    Tendsto (fun s : ℝ => Real.arctan (s / a) / a / 2 - s / (2 * (s ^ 2 + a ^ 2)))
      atTop (𝓝 (Real.pi / 2 / a / 2)) := by
  have hzero : Tendsto (fun s : ℝ => s / (2 * (s ^ 2 + a ^ 2))) atTop (𝓝 0) := by
    refine squeeze_zero' ((eventually_gt_atTop (0 : ℝ)).mono fun s hs => by positivity)
      ((eventually_gt_atTop (0 : ℝ)).mono fun s hs => ?_) tendsto_inv_atTop_zero
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (s ^ 2 + a ^ 2)), inv_mul_eq_div,
      le_div_iff₀ hs]
    nlinarith [sq_nonneg a, sq_nonneg s]
  simpa using ((tendsto_arctanScale ha).div_const 2).sub hzero

/-- The half-line integral `∫₀^∞ t² dt / (t² + a²)² = π / (4a)`, the degenerate case of the
partial fraction decomposition. -/
theorem integral_Ioi_sq_div_sq_add_sq_sq {a : ℝ} (ha : 0 < a) :
    ∫ t : ℝ in Ioi 0, t ^ 2 / (t ^ 2 + a ^ 2) ^ 2 = Real.pi / (4 * a) := by
  have key : ∫ t : ℝ in Ioi (0 : ℝ), t ^ 2 / (t ^ 2 + a ^ 2) ^ 2
      = Real.pi / 2 / a / 2
        - (Real.arctan (0 / a) / a / 2 - 0 / (2 * (0 ^ 2 + a ^ 2))) :=
    integral_Ioi_of_hasDerivAt_of_nonneg' (fun s _ => hasDerivAt_sqScale ha s)
      (fun t _ => by positivity) (tendsto_sqScale ha)
  rw [key]
  simp only [Real.arctan_zero, zero_div, sub_zero]
  rw [div_div, div_div, show (2 : ℝ) * (a * 2) = 4 * a by ring]

/-- The integrand of `integral_Ioi_sq_div_sq_add_sq_sq` is integrable on the half-line. -/
theorem integrableOn_Ioi_sq_div_sq_add_sq_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ 2 / (t ^ 2 + a ^ 2) ^ 2) (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun s _ => hasDerivAt_sqScale ha s)
    (fun t _ => by positivity) (tendsto_sqScale ha)

/-! ### The one-dimensional Cauchy density -/

theorem cauchyDensity_nonneg {t : ℝ} (ht : 0 ≤ t) (x : ℝ) : 0 ≤ cauchyDensity t x :=
  div_nonneg ht (by positivity)

/-- The Cauchy density is even. -/
theorem cauchyDensity_neg (t x : ℝ) : cauchyDensity t (-x) = cauchyDensity t x := by
  simp only [cauchyDensity, neg_sq]

theorem continuous_cauchyDensity {t : ℝ} (ht : 0 < t) : Continuous (cauchyDensity t) := by
  unfold cauchyDensity
  exact continuous_const.div₀ (by fun_prop) fun x => by positivity

/-- The Cauchy density of scale `t > 0` is a probability density. -/
theorem integral_cauchyDensity {t : ℝ} (ht : 0 < t) : ∫ x : ℝ, cauchyDensity t x = 1 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have h : ∀ x : ℝ, cauchyDensity t x = t / Real.pi * (1 / (x ^ 2 + t ^ 2)) := fun x => by
    rw [cauchyDensity, add_comm (t ^ 2) (x ^ 2), div_mul_div_comm, mul_one]
  simp_rw [h]
  rw [integral_const_mul, integral_one_div_sq_add_sq ht]
  field_simp

/-! ### The semigroup density -/

theorem heatKernel_nonneg {t : ℝ} (ht : 0 ≤ t) (z : Fin 2 → ℝ) : 0 ≤ heatKernel t z :=
  mul_nonneg (cauchyDensity_nonneg ht _) (cauchyDensity_nonneg ht _)

/-- The semigroup density is even. -/
theorem heatKernel_neg (t : ℝ) (z : Fin 2 → ℝ) : heatKernel t (-z) = heatKernel t z := by
  simp only [heatKernel, Pi.neg_apply, cauchyDensity_neg]

theorem continuous_heatKernel {t : ℝ} (ht : 0 < t) : Continuous (heatKernel t) := by
  unfold heatKernel
  exact ((continuous_cauchyDensity ht).comp' (continuous_apply 0)).mul
    ((continuous_cauchyDensity ht).comp' (continuous_apply 1))

/-- The semigroup density of scale `t > 0` is a probability density on the plane: the product
structure and Fubini reduce it to `integral_cauchyDensity`. -/
theorem integral_heatKernel {t : ℝ} (ht : 0 < t) : ∫ z : Fin 2 → ℝ, heatKernel t z = 1 := by
  have h : ∫ z : Fin 2 → ℝ, heatKernel t z
      = ∫ p : ℝ × ℝ, cauchyDensity t p.1 * cauchyDensity t p.2 := by
    rw [← (volume_preserving_finTwoArrow ℝ).map_eq, integral_map_equiv]
    rfl
  rw [h, Measure.volume_eq_prod, integral_prod_mul, integral_cauchyDensity ht, mul_one]

/-! ### The time integral of the semigroup density -/

/-- The radial form of the time integral: `∫₀^∞ t² dt / ((t² + a²) (t² + b²)) = π / (2 (a + b))`
for nonnegative `a` and `b`, not both zero. The three cases are `a = 0` or `b = 0`, where the
integrand collapses to a single Cauchy density, `a = b`, where the partial fraction decomposition
degenerates, and the generic case `0 < a ≠ b`, where it applies. -/
private theorem integral_Ioi_profile {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    ∫ t : ℝ in Ioi 0, t ^ 2 / ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)) = Real.pi / (2 * (a + b)) := by
  rcases ha.eq_or_lt with rfl | ha'
  · have hb' : 0 < b := by linarith
    have hcongr : EqOn (fun t : ℝ => t ^ 2 / ((t ^ 2 + 0 ^ 2) * (t ^ 2 + b ^ 2)))
        (fun t : ℝ => 1 / (t ^ 2 + b ^ 2)) (Ioi 0) := fun t ht => by
      have ht' : (0 : ℝ) < t := ht
      have h₁ : t ^ 2 ≠ 0 := by positivity
      have h₂ : t ^ 2 + b ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_Ioi_one_div_sq_add_sq hb',
      zero_add]
  rcases hb.eq_or_lt with rfl | hb'
  · have hcongr : EqOn (fun t : ℝ => t ^ 2 / ((t ^ 2 + a ^ 2) * (t ^ 2 + 0 ^ 2)))
        (fun t : ℝ => 1 / (t ^ 2 + a ^ 2)) (Ioi 0) := fun t ht => by
      have ht' : (0 : ℝ) < t := ht
      have h₁ : t ^ 2 ≠ 0 := by positivity
      have h₂ : t ^ 2 + a ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_Ioi_one_div_sq_add_sq ha',
      add_zero]
  rcases eq_or_ne a b with rfl | hne
  · have hcongr : EqOn (fun t : ℝ => t ^ 2 / ((t ^ 2 + a ^ 2) * (t ^ 2 + a ^ 2)))
        (fun t : ℝ => t ^ 2 / (t ^ 2 + a ^ 2) ^ 2) (Ioi 0) := fun t _ => by
      show t ^ 2 / ((t ^ 2 + a ^ 2) * (t ^ 2 + a ^ 2)) = t ^ 2 / (t ^ 2 + a ^ 2) ^ 2
      rw [pow_two (t ^ 2 + a ^ 2)]
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_Ioi_sq_div_sq_add_sq_sq ha']
    congr 1
    ring
  · have ha0 : a ≠ 0 := ha'.ne'
    have hb0 : b ≠ 0 := hb'.ne'
    have hab0 : a + b ≠ 0 := hab.ne'
    have hne2 : b ^ 2 - a ^ 2 ≠ 0 := by
      have h : b ^ 2 - a ^ 2 = (b - a) * (b + a) := by ring
      rw [h]
      exact mul_ne_zero (sub_ne_zero.2 (Ne.symm hne)) (by positivity)
    have hcongr : EqOn (fun t : ℝ => t ^ 2 / ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))
        (fun t : ℝ => b ^ 2 / (b ^ 2 - a ^ 2) * (1 / (t ^ 2 + b ^ 2))
          - a ^ 2 / (b ^ 2 - a ^ 2) * (1 / (t ^ 2 + a ^ 2))) (Ioi 0) := fun t _ => by
      have h₁ : t ^ 2 + a ^ 2 ≠ 0 := by positivity
      have h₂ : t ^ 2 + b ^ 2 ≠ 0 := by positivity
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      integral_sub ((integrableOn_Ioi_one_div_sq_add_sq hb').const_mul _)
        ((integrableOn_Ioi_one_div_sq_add_sq ha').const_mul _),
      integral_const_mul, integral_const_mul, integral_Ioi_one_div_sq_add_sq ha',
      integral_Ioi_one_div_sq_add_sq hb']
    field_simp
    ring

/-- **The potential kernel of the coordinate Cauchy generator.** The time integral of the
semigroup density away from the origin is `1 / (2π (|u| + |v|))`. -/
theorem integral_Ioi_heatKernel {z : Fin 2 → ℝ} (hz : z ≠ 0) :
    ∫ t : ℝ in Ioi 0, heatKernel t z = potential z := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hd : 0 < |z 0| + |z 1| := diamondNorm_pos hz
  have hd' : |z 0| + |z 1| ≠ 0 := hd.ne'
  have hcongr : EqOn (fun t : ℝ => heatKernel t z)
      (fun t : ℝ => (Real.pi ^ 2)⁻¹ *
        (t ^ 2 / ((t ^ 2 + |z 0| ^ 2) * (t ^ 2 + |z 1| ^ 2)))) (Ioi 0) := fun t ht => by
    have ht' : (0 : ℝ) < t := ht
    have h₁ : t ^ 2 + z 0 ^ 2 ≠ 0 := by positivity
    have h₂ : t ^ 2 + z 1 ^ 2 ≠ 0 := by positivity
    simp only [heatKernel, cauchyDensity, sq_abs]
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    integral_Ioi_profile (abs_nonneg _) (abs_nonneg _) hd, potential, diamondNorm]
  field_simp

/-! ### The potential kernel -/

theorem potential_nonneg (z : Fin 2 → ℝ) : 0 ≤ potential z :=
  div_nonneg zero_le_one (mul_nonneg (by positivity) (diamondNorm_nonneg z))

theorem potential_pos {z : Fin 2 → ℝ} (hz : z ≠ 0) : 0 < potential z :=
  div_pos one_pos (mul_pos (by positivity) (diamondNorm_pos hz))

/-- The potential kernel is even. -/
theorem potential_neg (z : Fin 2 → ℝ) : potential (-z) = potential z := by
  rw [potential, potential, diamondNorm_neg]

/-- The potential kernel is homogeneous of degree `-1`. -/
theorem potential_smul {c : ℝ} (hc : c ≠ 0) (z : Fin 2 → ℝ) :
    potential (c • z) = |c|⁻¹ * potential z := by
  rcases eq_or_ne z 0 with rfl | hz
  · have h₀ : diamondNorm (0 : Fin 2 → ℝ) = 0 := diamondNorm_eq_zero_iff.2 rfl
    rw [smul_zero, potential, h₀, mul_zero, div_zero, mul_zero]
  · have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    have hdz : diamondNorm z ≠ 0 := (diamondNorm_pos hz).ne'
    have hc' : |c| ≠ 0 := abs_ne_zero.2 hc
    rw [potential, potential, diamondNorm_smul]
    field_simp

theorem measurable_potential : Measurable potential := by
  unfold potential diamondNorm
  fun_prop

/-- The sup norm is at most the diamond radius. -/
theorem norm_le_diamondNorm (z : Fin 2 → ℝ) : ‖z‖ ≤ diamondNorm z := by
  refine (pi_norm_le_iff_of_nonneg (diamondNorm_nonneg z)).2 fun i => ?_
  fin_cases i <;> simp [diamondNorm]

/-- The diamond radius is at most twice the sup norm, so diamonds and sup balls are comparable. -/
theorem diamondNorm_le_two_mul_norm (z : Fin 2 → ℝ) : diamondNorm z ≤ 2 * ‖z‖ := by
  have h₀ : |z 0| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm z 0
  have h₁ : |z 1| ≤ ‖z‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm z 1
  rw [diamondNorm]
  linarith

/-- The mass of the potential kernel on the diamond of radius `R ≥ 0` is `2R/π`: by the radial
formula the integral is `∫₀^R 4t / (2πt) dt`. -/
theorem lintegral_potential_diamond {R : ℝ} (hR : 0 ≤ R) :
    ∫⁻ z in {z : Fin 2 → ℝ | diamondNorm z ≤ R}, ENNReal.ofReal (potential z)
      = ENNReal.ofReal (2 * R / Real.pi) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hS : MeasurableSet {z : Fin 2 → ℝ | diamondNorm z ≤ R} :=
    measurableSet_le measurable_diamondNorm measurable_const
  have hg : Measurable fun t : ℝ =>
      if t ≤ R then ENNReal.ofReal (1 / (2 * Real.pi * t)) else 0 :=
    Measurable.ite (measurableSet_le measurable_id measurable_const)
      (ENNReal.measurable_ofReal.comp (by fun_prop)) measurable_const
  calc ∫⁻ z in {z : Fin 2 → ℝ | diamondNorm z ≤ R}, ENNReal.ofReal (potential z)
      = ∫⁻ z : Fin 2 → ℝ,
          if diamondNorm z ≤ R then ENNReal.ofReal (1 / (2 * Real.pi * diamondNorm z)) else 0 := by
        rw [← lintegral_indicator hS]
        refine lintegral_congr fun z => ?_
        by_cases h : diamondNorm z ≤ R
        · have hmem : z ∈ {z : Fin 2 → ℝ | diamondNorm z ≤ R} := h
          rw [Set.indicator_of_mem hmem, potential, if_pos h]
        · have hmem : z ∉ {z : Fin 2 → ℝ | diamondNorm z ≤ R} := h
          rw [Set.indicator_of_notMem hmem, if_neg h]
    _ = ∫⁻ t in Ioi 0, 4 * ENNReal.ofReal t *
          (if t ≤ R then ENNReal.ofReal (1 / (2 * Real.pi * t)) else 0) :=
        lintegral_comp_diamondNorm hg
    _ = ∫⁻ t in Ioc 0 R, 4 * ENNReal.ofReal t *
          (if t ≤ R then ENNReal.ofReal (1 / (2 * Real.pi * t)) else 0) := by
        have htail : ∫⁻ t in Ioi R, 4 * ENNReal.ofReal t *
            (if t ≤ R then ENNReal.ofReal (1 / (2 * Real.pi * t)) else 0) = 0 :=
          setLIntegral_eq_zero measurableSet_Ioi fun t ht => by
            have ht' : R < t := ht
            simp [not_le.2 ht']
        rw [← Ioc_union_Ioi_eq_Ioi hR, lintegral_union measurableSet_Ioi Ioc_disjoint_Ioi_same,
          htail, add_zero]
    _ = ∫⁻ _ in Ioc (0 : ℝ) R, ENNReal.ofReal (2 / Real.pi) := by
        refine setLIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
        have ht0 : (0 : ℝ) < t := ht.1
        rw [if_pos ht.2, show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by simp,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * t)]
        congr 1
        field_simp
        ring
    _ = ENNReal.ofReal (2 * R / Real.pi) := by
        rw [setLIntegral_const, Real.volume_Ioc, sub_zero,
          ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 / Real.pi)]
        congr 1
        ring

/-- The potential kernel is integrable on every diamond. -/
theorem integrableOn_potential_diamond {R : ℝ} (hR : 0 ≤ R) :
    IntegrableOn potential {z : Fin 2 → ℝ | diamondNorm z ≤ R} := by
  refine ⟨measurable_potential.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall potential_nonneg),
    lintegral_potential_diamond hR]
  exact ENNReal.ofReal_lt_top

/-- The potential kernel is locally integrable: the sup ball of radius `R` sits inside the diamond
of radius `2R`. -/
theorem integrableOn_potential_closedBall (R : ℝ) :
    IntegrableOn potential (Metric.closedBall (0 : Fin 2 → ℝ) R) := by
  rcases le_or_gt 0 R with hR | hR
  · refine (integrableOn_potential_diamond (by linarith : (0 : ℝ) ≤ 2 * R)).mono_set fun z hz => ?_
    have h : ‖z‖ ≤ R := mem_closedBall_zero_iff.1 hz
    exact (diamondNorm_le_two_mul_norm z).trans (by linarith)
  · rw [Metric.closedBall_eq_empty.2 hR]
    exact integrableOn_empty

end CenteredMaximal.Cauchy
