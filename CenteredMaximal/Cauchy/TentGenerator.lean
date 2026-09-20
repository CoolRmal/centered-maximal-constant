/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Cauchy.Semigroup
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The Cauchy jump generator of the squared tent

The bump subtracted from the loose comparison kernel of `CenteredMaximal.Cauchy.LooseKernel` is
`ψ (u, v) = (1 − |u| − |v|)₊²`, whose one-dimensional slices are dilates of the **squared tent**

`tentSq x = ((1 − |x|)₊)²`.

This file computes the one-dimensional Cauchy jump integral of the squared tent in closed form: for
`t > 0`,

`jumpGen1 1 tentSq t = 4 * Ffun t`,
`Ffun t = 2 − (1 − t) log |1 − t| − (1 + t) log (1 + t) + 2 log t`,

which is `jumpGen1_tentSq`, the main result. The removable singularity at `t = 1` is automatic:
`Real.log` is even and `Real.log 0 = 0`, so `Ffun 1 = 2 − 2 log 2` on the nose.

## The second difference

The second difference `tentSqDiff t s = tentSq (t + s) + tentSq (t − s) − 2 tentSq t` is even in
each variable. The squared tent is *not* `C^{1,1}`: at the origin `(1 − |x|)² = 1 − 2|x| + x²` has a
downward corner, so `|tentSqDiff t s| ≤ 2 s²` **fails** (at `t = 0` the second difference is
`2 s² − 4 |s|`). The corner is invisible as long as `t + s` and `t − s` lie on the same side of the
origin, which is `abs_tentSqDiff_le`: `|s| ≤ |t|` implies `|tentSqDiff t s| ≤ 2 s²`. Together with
the crude bound `|tentSqDiff t s| ≤ 4` this gives `integrable_tentSqDiff_div_sq`, integrability of
`tentSqDiff t s / s²` for every `t ≠ 0`; the restriction is sharp, since `Ffun t → −∞` as `t → 0⁺`.

## The closed form

By evenness the jump integral is twice the half-line integral, which is split at the finitely many
breakpoints where `t ± s` crosses `±1`. On each piece the integrand is a rational function with
denominator `s²`, so `s ↦ p s + q log s − r / s` is an antiderivative
(`integral_Ioc_quad_div_sq`), and the unbounded tail is `integral_Ioi_const_div_sq`. The
breakpoints are `t − 1 < t < t + 1` for `t ≥ 1` (`integral_Ioi_tentSqDiff_of_one_le`) and
`min (t, 1 − t) < max (t, 1 − t) < 1 + t` for `0 < t < 1`, where the two orderings of `t` and
`1 − t` are treated separately (`integral_Ioi_tentSqDiff_of_le_half`,
`integral_Ioi_tentSqDiff_of_half_le`). In all three cases the rational parts of the pieces telescope
to `4` and the logarithmic parts to `2 (2 log t − (1 − t) log |1 − t| − (1 + t) log (1 + t))`.

## Properties of the closed form

The certificate downstream needs `Ffun_one`, the derivative `hasDerivAt_Ffun`

`Ffun' t = log |1 − t| − log (1 + t) + 2 / t`,

the second derivative `deriv2_Ffun`, `Ffun'' t = −2 / (t² (1 − t²))` on `(0, 1)`, hence
`strictConcaveOn_Ffun`, and the two sign facts `Ffun_nonpos_of_le_third` (`Ffun ≤ 0` on `(0, 1/3]`,
since `Ffun` increases there and `Ffun (1/3) = 2 − (10/3) log 2 < 0`) and `Ffun_le_of_one_le`
(`Ffun ≤ 2 − 2 log 2` on `[1, ∞)`, since `Ffun' < 0` there by `2 / t < log (1 + t) − log (t − 1)`).
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace CenteredMaximal.Cauchy

/-- The squared tent `((1 − |x|)₊)²` on the line. -/
def tentSq (x : ℝ) : ℝ := (max (1 - |x|) 0) ^ 2

/-- The symmetric second difference `ψ (t + s) + ψ (t − s) − 2 ψ (t)` of the squared tent. -/
def tentSqDiff (t s : ℝ) : ℝ := tentSq (t + s) + tentSq (t - s) - 2 * tentSq t

/-- The closed form of the Cauchy jump generator of the squared tent, up to the factor `4`:
`Ffun t = 2 − (1 − t) log |1 − t| − (1 + t) log (1 + t) + 2 log t`. -/
def Ffun (t : ℝ) : ℝ :=
  2 - (1 - t) * Real.log |1 - t| - (1 + t) * Real.log (1 + t) + 2 * Real.log t

/-! ### Elementary properties of the squared tent -/

theorem tentSq_nonneg (x : ℝ) : 0 ≤ tentSq x := sq_nonneg _

/-- The squared tent is even. -/
theorem tentSq_neg (x : ℝ) : tentSq (-x) = tentSq x := by rw [tentSq, tentSq, abs_neg]

/-- The squared tent vanishes off the unit interval. -/
theorem tentSq_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) : tentSq x = 0 := by
  rw [tentSq, max_eq_right (by linarith : 1 - |x| ≤ 0), zero_pow two_ne_zero]

theorem tentSq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) : tentSq x = (1 - |x|) ^ 2 := by
  rw [tentSq, max_eq_left (by linarith : (0 : ℝ) ≤ 1 - |x|)]

theorem tentSq_of_one_le {x : ℝ} (hx : 1 ≤ x) : tentSq x = 0 :=
  tentSq_of_one_le_abs (by rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ x)])

/-- On `[0, 1]` the squared tent is `(1 − x)²`. -/
theorem tentSq_of_nonneg_of_le_one {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 1) :
    tentSq x = (1 - x) ^ 2 := by
  rw [tentSq_of_abs_le_one (by rwa [abs_of_nonneg hx]), abs_of_nonneg hx]

/-- On `[−1, 0]` the squared tent is `(1 + x)²`. -/
theorem tentSq_of_nonpos_of_neg_one_le {x : ℝ} (hx : x ≤ 0) (hx' : -1 ≤ x) :
    tentSq x = (1 + x) ^ 2 := by
  rw [tentSq_of_abs_le_one (by rw [abs_of_nonpos hx]; linarith), abs_of_nonpos hx]
  ring

theorem tentSq_le_one (x : ℝ) : tentSq x ≤ 1 := by
  rcases le_or_gt |x| 1 with h | h
  · rw [tentSq_of_abs_le_one h]
    nlinarith [abs_nonneg x]
  · rw [tentSq_of_one_le_abs h.le]
    norm_num

theorem continuous_tentSq : Continuous tentSq :=
  ((continuous_const.sub continuous_abs).max continuous_const).pow 2

/-! ### The second difference -/

/-- The second difference is even in the step. -/
theorem tentSqDiff_neg_right (t s : ℝ) : tentSqDiff t (-s) = tentSqDiff t s := by
  rw [tentSqDiff, tentSqDiff, ← sub_eq_add_neg, sub_neg_eq_add]
  ring

/-- The second difference is even in the base point. -/
theorem tentSqDiff_neg_left (t s : ℝ) : tentSqDiff (-t) s = tentSqDiff t s := by
  have h1 : tentSq (-t + s) = tentSq (t - s) := by
    rw [show -t + s = -(t - s) by ring, tentSq_neg]
  have h2 : tentSq (-t - s) = tentSq (t + s) := by
    rw [show -t - s = -(t + s) by ring, tentSq_neg]
  rw [tentSqDiff, tentSqDiff, h1, h2, tentSq_neg]
  ring

/-- The crude bound on the second difference, from `0 ≤ tentSq ≤ 1`. -/
theorem abs_tentSqDiff_le_four (t s : ℝ) : |tentSqDiff t s| ≤ 4 := by
  have h1 := tentSq_nonneg (t + s)
  have h2 := tentSq_nonneg (t - s)
  have h3 := tentSq_nonneg t
  have h4 := tentSq_le_one (t + s)
  have h5 := tentSq_le_one (t - s)
  have h6 := tentSq_le_one t
  rw [tentSqDiff, abs_le]
  constructor <;> linarith

/-- The quadratic bound on the second difference for `0 ≤ s ≤ t`: all three sample points are
then nonnegative, and on `[0, ∞)` the squared tent has the `2`-Lipschitz derivative
`x ↦ −2 (1 − x)₊`. The four cases are `t + s ≤ 1` (where the second difference is exactly `2 s²`),
`t + s > 1 ≥ t`, `t > 1 ≥ t − s` and `t − s > 1`. -/
private theorem abs_tentSqDiff_le_aux {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    |tentSqDiff t s| ≤ 2 * s ^ 2 := by
  have hu : (0 : ℝ) ≤ t - s := by linarith
  have hv : (0 : ℝ) ≤ t + s := by linarith
  have ht : (0 : ℝ) ≤ t := by linarith
  rcases le_or_gt (t + s) 1 with hv1 | hv1
  · rw [tentSqDiff, tentSq_of_nonneg_of_le_one hv hv1,
      tentSq_of_nonneg_of_le_one hu (by linarith), tentSq_of_nonneg_of_le_one ht (by linarith),
      show (1 - (t + s)) ^ 2 + (1 - (t - s)) ^ 2 - 2 * (1 - t) ^ 2 = 2 * s ^ 2 by ring,
      abs_of_nonneg (by positivity)]
  · rcases le_or_gt t 1 with ht1 | ht1
    · rw [tentSqDiff, tentSq_of_one_le hv1.le, tentSq_of_nonneg_of_le_one hu (by linarith),
        tentSq_of_nonneg_of_le_one ht ht1, abs_le]
      refine ⟨?_, ?_⟩
      · nlinarith [mul_nonneg hs (by linarith : (0 : ℝ) ≤ 1 - t)]
      · nlinarith [sq_nonneg (s - (1 - t))]
    · rw [tentSqDiff, tentSq_of_one_le (by linarith), tentSq_of_one_le ht1.le]
      rcases le_or_gt (t - s) 1 with hu1 | hu1
      · rw [tentSq_of_nonneg_of_le_one hu hu1, abs_le]
        refine ⟨by nlinarith, ?_⟩
        nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ t - 1)
          (by linarith : (0 : ℝ) ≤ 1 - t + 2 * s)]
      · rw [tentSq_of_one_le hu1.le, abs_le]
        constructor <;> nlinarith

/-- **The quadratic bound on the second difference.** As long as the step does not reach past the
corner of the squared tent at the origin, `|tentSqDiff t s| ≤ 2 s²`. -/
theorem abs_tentSqDiff_le {t s : ℝ} (hst : |s| ≤ |t|) : |tentSqDiff t s| ≤ 2 * s ^ 2 := by
  rw [← sq_abs s]
  have h : tentSqDiff t s = tentSqDiff |t| |s| := by
    rcases abs_cases t with ⟨ht, _⟩ | ⟨ht, _⟩ <;> rcases abs_cases s with ⟨hs, _⟩ | ⟨hs, _⟩ <;>
      rw [ht, hs] <;> simp only [tentSqDiff_neg_left, tentSqDiff_neg_right]
  rw [h]
  exact abs_tentSqDiff_le_aux (abs_nonneg s) hst

/-! ### Two half-line integrals of `s⁻²` -/

private theorem hasDerivAt_neg_one_div {s : ℝ} (hs : s ≠ 0) :
    HasDerivAt (fun y : ℝ => -1 / y) ((s ^ 2)⁻¹) s := by
  refine ((hasDerivAt_const s (-1 : ℝ)).div (hasDerivAt_id' (x := s)) hs).congr_deriv ?_
  field_simp
  ring

private theorem tendsto_neg_one_div : Tendsto (fun y : ℝ => -1 / y) atTop (𝓝 0) := by
  have h : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero
  have h' := h.neg
  rw [neg_zero] at h'
  exact h'.congr fun y => by simp [neg_div]

private theorem integrableOn_Ioi_inv_sq {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun s : ℝ => (s ^ 2)⁻¹) (Ioi a) :=
  integrableOn_Ioi_deriv_of_nonneg'
    (fun s hs => hasDerivAt_neg_one_div (ne_of_gt (lt_of_lt_of_le ha hs)))
    (fun s _ => by positivity) tendsto_neg_one_div

private theorem integral_Ioi_inv_sq {a : ℝ} (ha : 0 < a) : ∫ s in Ioi a, (s ^ 2)⁻¹ = a⁻¹ := by
  have hderiv : ∀ s ∈ Ici a, HasDerivAt (fun y : ℝ => -1 / y) ((s ^ 2)⁻¹) s :=
    fun s hs => hasDerivAt_neg_one_div (ne_of_gt (lt_of_lt_of_le ha hs))
  have hpos : ∀ s ∈ Ioi a, (0 : ℝ) ≤ (s ^ 2)⁻¹ := fun s _ => by positivity
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos tendsto_neg_one_div]
  ring

/-- The tail piece of the computation, `∫_a^∞ r / s² ds = r / a`. -/
private theorem integral_Ioi_const_div_sq {a : ℝ} (ha : 0 < a) (r : ℝ) :
    ∫ s in Ioi a, r * (s ^ 2)⁻¹ = r * a⁻¹ := by
  rw [integral_const_mul, integral_Ioi_inv_sq ha]

/-! ### The bounded pieces of the computation -/

/-- A bounded piece with a constant integrand: `∫_a^b p s² / s² ds = p (b − a)`. The endpoint
`a = 0` is allowed, the integrand being `p` off the origin. -/
private theorem integral_Ioc_sq_div_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (p : ℝ) :
    ∫ s in Ioc a b, p * s ^ 2 * (s ^ 2)⁻¹ = p * (b - a) := by
  have hcongr : EqOn (fun s : ℝ => p * s ^ 2 * (s ^ 2)⁻¹) (fun _ => p) (Ioc a b) := fun s hs => by
    have hs0 : s ≠ 0 := (lt_of_le_of_lt ha hs.1).ne'
    field_simp
  rw [setIntegral_congr_fun measurableSet_Ioc hcongr, setIntegral_const,
    Real.volume_real_Ioc_of_le hab, smul_eq_mul, mul_comm]

/-- **The bounded pieces.** The antiderivative `p s + q log s − r / s` of `(p s² + q s + r) / s²`
evaluates every bounded piece of the half-line computation. -/
private theorem integral_Ioc_quad_div_sq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (p q r : ℝ) :
    ∫ s in Ioc a b, (p * s ^ 2 + q * s + r) * (s ^ 2)⁻¹
      = p * (b - a) + q * (Real.log b - Real.log a) + r * (a⁻¹ - b⁻¹) := by
  have hpos : ∀ s ∈ uIcc a b, 0 < s := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact ha.trans_le hs.1
  have hderiv : ∀ s ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => p * y + q * Real.log y - r * y⁻¹)
        ((p * s ^ 2 + q * s + r) * (s ^ 2)⁻¹) s := by
    intro s hs
    have hs0 : s ≠ 0 := (hpos s hs).ne'
    refine ((((hasDerivAt_id' (x := s)).const_mul p).add
      ((Real.hasDerivAt_log hs0).const_mul q)).sub
        ((hasDerivAt_inv hs0).const_mul r)).congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun s : ℝ => (p * s ^ 2 + q * s + r) * (s ^ 2)⁻¹) (uIcc a b) := by
    refine (by fun_prop : Continuous fun s : ℝ => p * s ^ 2 + q * s + r).continuousOn.mul ?_
    exact (continuous_pow 2).continuousOn.inv₀ fun s hs => pow_ne_zero 2 (hpos s hs).ne'
  rw [← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]
  ring

/-- The piece `∫_a^b (s − a)² / s² ds`, with the endpoint `a = 0` allowed: both sides are then `b`,
since `Real.log 0 = 0`. -/
private theorem integral_Ioc_sub_sq_div_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
    ∫ s in Ioc a b, (s - a) ^ 2 * (s ^ 2)⁻¹
      = b - a ^ 2 / b - 2 * a * (Real.log b - Real.log a) := by
  rcases ha.eq_or_lt with rfl | ha'
  · have hcongr : ∀ s : ℝ, (s - 0) ^ 2 * (s ^ 2)⁻¹ = 1 * s ^ 2 * (s ^ 2)⁻¹ := fun s => by ring
    simp_rw [hcongr]
    rw [integral_Ioc_sq_div_sq le_rfl hab 1]
    norm_num
  · have hcongr : EqOn (fun s : ℝ => (s - a) ^ 2 * (s ^ 2)⁻¹)
        (fun s : ℝ => (1 * s ^ 2 + -(2 * a) * s + a ^ 2) * (s ^ 2)⁻¹) (Ioc a b) := fun s _ => by
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
      integral_Ioc_quad_div_sq ha' hab 1 (-(2 * a)) (a ^ 2)]
    have ha0 : a ≠ 0 := ha'.ne'
    have hb0 : b ≠ 0 := hb.ne'
    field_simp
    ring

/-! ### Integrability of the integrand -/

private theorem measurable_tentSqDiff_div_sq (t : ℝ) :
    Measurable fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹ := by
  have h : Continuous fun s : ℝ => tentSqDiff t s := by
    unfold tentSqDiff
    exact ((continuous_tentSq.comp' (continuous_const.add continuous_id)).add
      (continuous_tentSq.comp' (continuous_const.sub continuous_id))).sub continuous_const
  exact h.measurable.mul (by fun_prop)

/-- **The integrand of the jump integral is integrable** for every `t ≠ 0`: near the origin the
quadratic bound `abs_tentSqDiff_le` applies and the integrand is bounded by `2`, while past `|t|`
the crude bound `abs_tentSqDiff_le_four` dominates it by `4 / s²`. -/
theorem integrable_tentSqDiff_div_sq {t : ℝ} (ht : t ≠ 0) :
    Integrable fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹ := by
  have hmeas := measurable_tentSqDiff_div_sq t
  have ha : 0 < |t| := abs_pos.2 ht
  refine CenteredMaximal.integrable_of_even (fun s => by rw [tentSqDiff_neg_right, neg_sq]) ?_
  rw [← Ioc_union_Ioi_eq_Ioi ha.le, integrableOn_union]
  constructor
  · refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hmeas.aestronglyMeasurable
      (M := 2) (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs => ?_)
    have hs0 : (0 : ℝ) < s := hs.1
    have hst : |s| ≤ |t| := by rw [abs_of_pos hs0]; exact hs.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s ^ 2)⁻¹)]
    calc |tentSqDiff t s| * (s ^ 2)⁻¹ ≤ 2 * s ^ 2 * (s ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (abs_tentSqDiff_le hst) (by positivity)
      _ = 2 := by field_simp
  · refine ((integrableOn_Ioi_inv_sq ha).const_mul 4).mono' hmeas.aestronglyMeasurable
      (ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_)
    have hs0 : (0 : ℝ) < s := ha.trans hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s ^ 2)⁻¹)]
    exact mul_le_mul_of_nonneg_right (abs_tentSqDiff_le_four t s) (by positivity)

/-! ### The half-line integral -/

/-- Splitting the half-line at three points. -/
private theorem integral_Ioi_eq_sum_of_split {f : ℝ → ℝ} (hf : Integrable f) {a b c : ℝ}
    (h0 : 0 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) :
    ∫ s in Ioi (0 : ℝ), f s = (∫ s in Ioc 0 a, f s) + (∫ s in Ioc a b, f s)
      + (∫ s in Ioc b c, f s) + ∫ s in Ioi c, f s := by
  have e1 : ∫ s in Ioi (0 : ℝ), f s = (∫ s in Ioc 0 c, f s) + ∫ s in Ioi c, f s := by
    rw [← Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ c),
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hf.integrableOn
        hf.integrableOn]
  have e2 : ∫ s in Ioc (0 : ℝ) c, f s = (∫ s in Ioc 0 b, f s) + ∫ s in Ioc b c, f s := by
    rw [← Ioc_union_Ioc_eq_Ioc (by linarith : (0 : ℝ) ≤ b) hbc,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hf.integrableOn
        hf.integrableOn]
  have e3 : ∫ s in Ioc (0 : ℝ) b, f s = (∫ s in Ioc 0 a, f s) + ∫ s in Ioc a b, f s := by
    rw [← Ioc_union_Ioc_eq_Ioc h0 hab,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc hf.integrableOn
        hf.integrableOn]
  rw [e1, e2, e3]

theorem Ffun_eq (t : ℝ) :
    Ffun t = 2 - (1 - t) * Real.log (1 - t) - (1 + t) * Real.log (1 + t) + 2 * Real.log t := by
  simp only [Ffun, Real.log_abs]

/-- The half-line integral for `1 ≤ t`. The squared tent vanishes at `t` and at every `t + s` with
`s > 0`, so only the two pieces on which `t − s` lies in `[−1, 1]` contribute. -/
private theorem integral_Ioi_tentSqDiff_of_one_le {t : ℝ} (ht : 1 ≤ t) :
    ∫ s in Ioi (0 : ℝ), tentSqDiff t s * (s ^ 2)⁻¹ = 2 * Ffun t := by
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hint : Integrable fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹ :=
    integrable_tentSqDiff_div_sq ht0.ne'
  have htent : tentSq t = 0 := tentSq_of_one_le ht
  have e1 : ∫ s in Ioc (0 : ℝ) (t - 1), tentSqDiff t s * (s ^ 2)⁻¹ = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
    simp only [tentSqDiff]
    rw [htent, tentSq_of_one_le (by linarith [hs.1] : (1 : ℝ) ≤ t + s),
      tentSq_of_one_le (by linarith [hs.2] : (1 : ℝ) ≤ t - s)]
    ring
  have e2 : ∫ s in Ioc (t - 1) t, tentSqDiff t s * (s ^ 2)⁻¹
      = t - (t - 1) ^ 2 / t - 2 * (t - 1) * (Real.log t - Real.log (t - 1)) := by
    have hcongr : EqOn (fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹)
        (fun s : ℝ => (s - (t - 1)) ^ 2 * (s ^ 2)⁻¹) (Ioc (t - 1) t) := fun s hs => by
      simp only [tentSqDiff]
      rw [htent, tentSq_of_one_le (by linarith [hs.1] : (1 : ℝ) ≤ t + s),
        tentSq_of_nonneg_of_le_one (by linarith [hs.2] : (0 : ℝ) ≤ t - s)
          (by linarith [hs.1] : t - s ≤ 1)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
      integral_Ioc_sub_sq_div_sq (by linarith) (by linarith) ht0]
  have e3 : ∫ s in Ioc t (t + 1), tentSqDiff t s * (s ^ 2)⁻¹
      = 1 * (t + 1 - t) + -(2 * (t + 1)) * (Real.log (t + 1) - Real.log t)
        + (t + 1) ^ 2 * (t⁻¹ - (t + 1)⁻¹) := by
    have hcongr : EqOn (fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹)
        (fun s : ℝ => (1 * s ^ 2 + -(2 * (t + 1)) * s + (t + 1) ^ 2) * (s ^ 2)⁻¹)
        (Ioc t (t + 1)) := fun s hs => by
      simp only [tentSqDiff]
      rw [htent, tentSq_of_one_le (by linarith [hs.1] : (1 : ℝ) ≤ t + s),
        tentSq_of_nonpos_of_neg_one_le (by linarith [hs.1] : t - s ≤ 0)
          (by linarith [hs.2] : (-1 : ℝ) ≤ t - s)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
      integral_Ioc_quad_div_sq ht0 (by linarith) 1 (-(2 * (t + 1))) ((t + 1) ^ 2)]
  have e4 : ∫ s in Ioi (t + 1), tentSqDiff t s * (s ^ 2)⁻¹ = 0 := by
    refine setIntegral_eq_zero_of_forall_eq_zero fun s hs => ?_
    have hs' : t + 1 < s := hs
    simp only [tentSqDiff]
    rw [htent, tentSq_of_one_le (by linarith : (1 : ℝ) ≤ t + s),
      tentSq_of_one_le_abs (by rw [abs_of_nonpos (by linarith : t - s ≤ 0)]; linarith)]
    ring
  rw [integral_Ioi_eq_sum_of_split hint (by linarith : (0 : ℝ) ≤ t - 1)
    (by linarith : t - 1 ≤ t) (show t ≤ t + 1 by linarith), e1, e2, e3, e4, Ffun_eq]
  rw [show Real.log (1 - t) = Real.log (t - 1) by
    rw [show (1 : ℝ) - t = -(t - 1) by ring, Real.log_neg_eq_log],
    show Real.log (t + 1) = Real.log (1 + t) by rw [add_comm]]
  have h0 : t ≠ 0 := ht0.ne'
  have h1 : t + 1 ≠ 0 := by positivity
  field_simp
  ring

/-- The half-line integral for `0 < t ≤ 1/2`, where the breakpoints are `t < 1 − t < 1 + t`. -/
private theorem integral_Ioi_tentSqDiff_of_le_half {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 - t) :
    ∫ s in Ioi (0 : ℝ), tentSqDiff t s * (s ^ 2)⁻¹ = 2 * Ffun t := by
  have hc : (0 : ℝ) < 1 - t := by linarith
  have hint : Integrable fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹ :=
    integrable_tentSqDiff_div_sq ht.ne'
  have htent : tentSq t = (1 - t) ^ 2 := tentSq_of_nonneg_of_le_one ht.le (by linarith)
  have e1 : ∫ s in Ioc (0 : ℝ) t, tentSqDiff t s * (s ^ 2)⁻¹ = 2 * (t - 0) := by
    have hcongr : EqOn (fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹)
        (fun s : ℝ => 2 * s ^ 2 * (s ^ 2)⁻¹) (Ioc 0 t) := fun s hs => by
      simp only [tentSqDiff]
      rw [htent, tentSq_of_nonneg_of_le_one (by linarith [hs.1] : (0 : ℝ) ≤ t + s)
          (by linarith [hs.2] : t + s ≤ 1),
        tentSq_of_nonneg_of_le_one (by linarith [hs.2] : (0 : ℝ) ≤ t - s)
          (by linarith [hs.1] : t - s ≤ 1)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_Ioc_sq_div_sq le_rfl ht.le 2]
  have e2 : ∫ s in Ioc t (1 - t), tentSqDiff t s * (s ^ 2)⁻¹
      = 2 * (1 - t - t) + -4 * (Real.log (1 - t) - Real.log t) + 4 * t * (t⁻¹ - (1 - t)⁻¹) := by
    have hcongr : EqOn (fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹)
        (fun s : ℝ => (2 * s ^ 2 + -4 * s + 4 * t) * (s ^ 2)⁻¹) (Ioc t (1 - t)) := fun s hs => by
      simp only [tentSqDiff]
      rw [htent, tentSq_of_nonneg_of_le_one (by linarith [hs.1] : (0 : ℝ) ≤ t + s)
          (by linarith [hs.2] : t + s ≤ 1),
        tentSq_of_nonpos_of_neg_one_le (by linarith [hs.1] : t - s ≤ 0)
          (by linarith [hs.2] : (-1 : ℝ) ≤ t - s)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
      integral_Ioc_quad_div_sq ht ht' 2 (-4) (4 * t)]
  have e3 : ∫ s in Ioc (1 - t) (1 + t), tentSqDiff t s * (s ^ 2)⁻¹
      = 1 * (1 + t - (1 - t)) + -(2 * (1 + t)) * (Real.log (1 + t) - Real.log (1 - t))
        + ((1 + t) ^ 2 - 2 * (1 - t) ^ 2) * ((1 - t)⁻¹ - (1 + t)⁻¹) := by
    have hcongr : EqOn (fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹)
        (fun s : ℝ => (1 * s ^ 2 + -(2 * (1 + t)) * s + ((1 + t) ^ 2 - 2 * (1 - t) ^ 2))
          * (s ^ 2)⁻¹) (Ioc (1 - t) (1 + t)) := fun s hs => by
      simp only [tentSqDiff]
      rw [htent, tentSq_of_one_le (by linarith [hs.1] : (1 : ℝ) ≤ t + s),
        tentSq_of_nonpos_of_neg_one_le (by linarith [hs.1] : t - s ≤ 0)
          (by linarith [hs.2] : (-1 : ℝ) ≤ t - s)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
      integral_Ioc_quad_div_sq hc (by linarith) 1 (-(2 * (1 + t)))
        ((1 + t) ^ 2 - 2 * (1 - t) ^ 2)]
  have e4 : ∫ s in Ioi (1 + t), tentSqDiff t s * (s ^ 2)⁻¹
      = -(2 * (1 - t) ^ 2) * (1 + t)⁻¹ := by
    have hcongr : EqOn (fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹)
        (fun s : ℝ => -(2 * (1 - t) ^ 2) * (s ^ 2)⁻¹) (Ioi (1 + t)) := fun s hs => by
      have hs' : 1 + t < s := hs
      simp only [tentSqDiff]
      rw [htent, tentSq_of_one_le (by linarith : (1 : ℝ) ≤ t + s),
        tentSq_of_one_le_abs (by rw [abs_of_nonpos (by linarith : t - s ≤ 0)]; linarith)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      integral_Ioi_const_div_sq (by linarith) (-(2 * (1 - t) ^ 2))]
  rw [integral_Ioi_eq_sum_of_split hint ht.le ht' (show (1 : ℝ) - t ≤ 1 + t by linarith),
    e1, e2, e3, e4, Ffun_eq]
  have h0 : t ≠ 0 := ht.ne'
  have h1 : (1 : ℝ) - t ≠ 0 := hc.ne'
  have h2 : (1 : ℝ) + t ≠ 0 := by positivity
  field_simp
  ring

/-- The half-line integral for `1/2 ≤ t < 1`, where the breakpoints are `1 − t < t < 1 + t`. -/
private theorem integral_Ioi_tentSqDiff_of_half_le {t : ℝ} (ht1 : t < 1) (ht' : 1 - t ≤ t) :
    ∫ s in Ioi (0 : ℝ), tentSqDiff t s * (s ^ 2)⁻¹ = 2 * Ffun t := by
  have ht : (0 : ℝ) < t := by linarith
  have hc : (0 : ℝ) < 1 - t := by linarith
  have hint : Integrable fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹ :=
    integrable_tentSqDiff_div_sq ht.ne'
  have htent : tentSq t = (1 - t) ^ 2 := tentSq_of_nonneg_of_le_one ht.le ht1.le
  have e1 : ∫ s in Ioc (0 : ℝ) (1 - t), tentSqDiff t s * (s ^ 2)⁻¹ = 2 * (1 - t - 0) := by
    have hcongr : EqOn (fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹)
        (fun s : ℝ => 2 * s ^ 2 * (s ^ 2)⁻¹) (Ioc 0 (1 - t)) := fun s hs => by
      simp only [tentSqDiff]
      rw [htent, tentSq_of_nonneg_of_le_one (by linarith [hs.1] : (0 : ℝ) ≤ t + s)
          (by linarith [hs.2] : t + s ≤ 1),
        tentSq_of_nonneg_of_le_one (by linarith [hs.2] : (0 : ℝ) ≤ t - s)
          (by linarith [hs.1] : t - s ≤ 1)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr, integral_Ioc_sq_div_sq le_rfl hc.le 2]
  have e2 : ∫ s in Ioc (1 - t) t, tentSqDiff t s * (s ^ 2)⁻¹
      = 1 * (t - (1 - t)) + 2 * (1 - t) * (Real.log t - Real.log (1 - t))
        + -((1 - t) ^ 2) * ((1 - t)⁻¹ - t⁻¹) := by
    have hcongr : EqOn (fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹)
        (fun s : ℝ => (1 * s ^ 2 + 2 * (1 - t) * s + -((1 - t) ^ 2)) * (s ^ 2)⁻¹)
        (Ioc (1 - t) t) := fun s hs => by
      simp only [tentSqDiff]
      rw [htent, tentSq_of_one_le (by linarith [hs.1] : (1 : ℝ) ≤ t + s),
        tentSq_of_nonneg_of_le_one (by linarith [hs.2] : (0 : ℝ) ≤ t - s)
          (by linarith [hs.1] : t - s ≤ 1)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
      integral_Ioc_quad_div_sq hc ht' 1 (2 * (1 - t)) (-((1 - t) ^ 2))]
  have e3 : ∫ s in Ioc t (1 + t), tentSqDiff t s * (s ^ 2)⁻¹
      = 1 * (1 + t - t) + -(2 * (1 + t)) * (Real.log (1 + t) - Real.log t)
        + ((1 + t) ^ 2 - 2 * (1 - t) ^ 2) * (t⁻¹ - (1 + t)⁻¹) := by
    have hcongr : EqOn (fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹)
        (fun s : ℝ => (1 * s ^ 2 + -(2 * (1 + t)) * s + ((1 + t) ^ 2 - 2 * (1 - t) ^ 2))
          * (s ^ 2)⁻¹) (Ioc t (1 + t)) := fun s hs => by
      simp only [tentSqDiff]
      rw [htent, tentSq_of_one_le (by linarith [hs.1] : (1 : ℝ) ≤ t + s),
        tentSq_of_nonpos_of_neg_one_le (by linarith [hs.1] : t - s ≤ 0)
          (by linarith [hs.2] : (-1 : ℝ) ≤ t - s)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioc hcongr,
      integral_Ioc_quad_div_sq ht (by linarith) 1 (-(2 * (1 + t)))
        ((1 + t) ^ 2 - 2 * (1 - t) ^ 2)]
  have e4 : ∫ s in Ioi (1 + t), tentSqDiff t s * (s ^ 2)⁻¹
      = -(2 * (1 - t) ^ 2) * (1 + t)⁻¹ := by
    have hcongr : EqOn (fun s : ℝ => tentSqDiff t s * (s ^ 2)⁻¹)
        (fun s : ℝ => -(2 * (1 - t) ^ 2) * (s ^ 2)⁻¹) (Ioi (1 + t)) := fun s hs => by
      have hs' : 1 + t < s := hs
      simp only [tentSqDiff]
      rw [htent, tentSq_of_one_le (by linarith : (1 : ℝ) ≤ t + s),
        tentSq_of_one_le_abs (by rw [abs_of_nonpos (by linarith : t - s ≤ 0)]; linarith)]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hcongr,
      integral_Ioi_const_div_sq (by linarith) (-(2 * (1 - t) ^ 2))]
  rw [integral_Ioi_eq_sum_of_split hint hc.le ht' (show t ≤ 1 + t by linarith),
    e1, e2, e3, e4, Ffun_eq]
  have h0 : t ≠ 0 := ht.ne'
  have h1 : (1 : ℝ) - t ≠ 0 := hc.ne'
  have h2 : (1 : ℝ) + t ≠ 0 := by positivity
  field_simp
  ring

/-- The half-line integral of the second difference is `2 Ffun t`. -/
private theorem integral_Ioi_tentSqDiff {t : ℝ} (ht : 0 < t) :
    ∫ s in Ioi (0 : ℝ), tentSqDiff t s * (s ^ 2)⁻¹ = 2 * Ffun t := by
  rcases le_or_gt 1 t with h | h
  · exact integral_Ioi_tentSqDiff_of_one_le h
  · rcases le_or_gt t (1 - t) with h' | h'
    · exact integral_Ioi_tentSqDiff_of_le_half ht h'
    · exact integral_Ioi_tentSqDiff_of_half_le h h'.le

/-- **The Cauchy jump generator of the squared tent in closed form.** For `t > 0`,
`jumpGen1 1 tentSq t = 4 (2 − (1 − t) log |1 − t| − (1 + t) log (1 + t) + 2 log t)`. -/
theorem jumpGen1_tentSq {t : ℝ} (ht : 0 < t) : jumpGen1 1 tentSq t = 4 * Ffun t := by
  have hform : jumpGen1 1 tentSq t = ∫ s : ℝ, tentSqDiff t s * (s ^ 2)⁻¹ := by
    simp only [jumpGen1, CenteredMaximal.abs_rpow_neg_two, tentSqDiff]
  rw [hform, CenteredMaximal.integral_of_even
      (fun s => by rw [tentSqDiff_neg_right, neg_sq])
      (integrable_tentSqDiff_div_sq ht.ne').integrableOn,
    integral_Ioi_tentSqDiff ht]
  ring

/-! ### Properties of the closed form -/

theorem Ffun_one : Ffun 1 = 2 - 2 * Real.log 2 := by
  simp only [Ffun]
  norm_num

theorem continuousOn_Ffun : ContinuousOn Ffun (Ioi 0) := by
  have h1 : Continuous fun x : ℝ => (1 - x) * Real.log |1 - x| := by
    simp only [Real.log_abs]
    exact Real.continuous_mul_log.comp' (by fun_prop)
  have h2 : Continuous fun x : ℝ => (1 + x) * Real.log (1 + x) :=
    Real.continuous_mul_log.comp' (by fun_prop)
  have h3 : ContinuousOn (fun x : ℝ => 2 * Real.log x) (Ioi 0) :=
    continuousOn_const.mul (Real.continuousOn_log.mono fun x hx =>
      ne_of_gt (Set.mem_Ioi.1 hx))
  unfold Ffun
  exact ((continuousOn_const.sub h1.continuousOn).sub h2.continuousOn).add h3

/-- The derivative of the closed form, `log |1 − t| − log (1 + t) + 2 / t`. -/
theorem hasDerivAt_Ffun {t : ℝ} (ht : 0 < t) (ht' : t ≠ 1) :
    HasDerivAt Ffun (Real.log |1 - t| - Real.log (1 + t) + 2 / t) t := by
  have h0 : t ≠ 0 := ht.ne'
  have h1 : (1 : ℝ) - t ≠ 0 := fun h => ht' (by linarith)
  have h2 : (1 : ℝ) + t ≠ 0 := by positivity
  have hu : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := (hasDerivAt_id' (x := t)).const_sub 1
  have hv : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id' (x := t)).const_add 1
  have hA : HasDerivAt (fun x : ℝ => (1 - x) * Real.log (1 - x))
      (-1 * Real.log (1 - t) + (1 - t) * (-1 / (1 - t))) t := hu.mul (hu.log h1)
  have hB : HasDerivAt (fun x : ℝ => (1 + x) * Real.log (1 + x))
      (1 * Real.log (1 + t) + (1 + t) * (1 / (1 + t))) t := hv.mul (hv.log h2)
  have hC : HasDerivAt (fun x : ℝ => 2 * Real.log x) (2 * t⁻¹) t :=
    (Real.hasDerivAt_log h0).const_mul 2
  rw [show Ffun = fun x : ℝ => 2 - (1 - x) * Real.log (1 - x) - (1 + x) * Real.log (1 + x)
      + 2 * Real.log x from funext Ffun_eq, Real.log_abs]
  refine ((((hasDerivAt_const t (2 : ℝ)).sub hA).sub hB).add hC).congr_deriv ?_
  field_simp
  ring

theorem deriv_Ffun {t : ℝ} (ht : 0 < t) (ht' : t ≠ 1) :
    deriv Ffun t = Real.log |1 - t| - Real.log (1 + t) + 2 / t :=
  (hasDerivAt_Ffun ht ht').deriv

/-- The second derivative of the closed form on `(0, 1)`, `−2 / (t² (1 − t²))`. -/
theorem hasDerivAt_deriv_Ffun {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    HasDerivAt (deriv Ffun) (-2 / (t ^ 2 * (1 - t ^ 2))) t := by
  have h0 : t ≠ 0 := ht.ne'
  have h1 : (1 : ℝ) - t ≠ 0 := by intro h; linarith
  have h2 : (1 : ℝ) + t ≠ 0 := by positivity
  have h3 : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  have heq : ∀ᶠ x in 𝓝 t, deriv Ffun x = Real.log (1 - x) - Real.log (1 + x) + 2 / x := by
    filter_upwards [Ioo_mem_nhds ht ht'] with x hx
    rw [deriv_Ffun hx.1 (ne_of_lt hx.2), Real.log_abs]
  refine (Filter.EventuallyEq.hasDerivAt_iff heq).2 ?_
  have hu : HasDerivAt (fun x : ℝ => 1 - x) (-1) t := (hasDerivAt_id' (x := t)).const_sub 1
  have hv : HasDerivAt (fun x : ℝ => 1 + x) 1 t := (hasDerivAt_id' (x := t)).const_add 1
  have hC : HasDerivAt (fun x : ℝ => 2 / x) ((0 * t - 2 * 1) / t ^ 2) t :=
    (hasDerivAt_const t (2 : ℝ)).div (hasDerivAt_id' (x := t)) h0
  refine (((hu.log h1).sub (hv.log h2)).add hC).congr_deriv ?_
  have h4 : (1 : ℝ) - t ^ 2 ≠ 0 := h3.ne'
  field_simp
  ring

theorem deriv2_Ffun {t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    deriv^[2] Ffun t = -2 / (t ^ 2 * (1 - t ^ 2)) := by
  rw [show deriv^[2] Ffun t = deriv (deriv Ffun) t by
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq],
    (hasDerivAt_deriv_Ffun ht ht').deriv]

theorem deriv2_Ffun_neg {t : ℝ} (ht : 0 < t) (ht' : t < 1) : deriv^[2] Ffun t < 0 := by
  rw [deriv2_Ffun ht ht']
  exact div_neg_of_neg_of_pos (by norm_num) (mul_pos (pow_pos ht 2) (by nlinarith))

/-- The closed form is strictly concave on the unit interval. -/
theorem strictConcaveOn_Ffun : StrictConcaveOn ℝ (Ioo 0 1) Ffun :=
  strictConcaveOn_of_deriv2_neg (convex_Ioo 0 1)
    (continuousOn_Ffun.mono fun _ hx => Set.mem_Ioi.2 hx.1) fun x hx => by
      rw [interior_Ioo] at hx
      exact deriv2_Ffun_neg hx.1 hx.2

theorem concaveOn_Ffun : ConcaveOn ℝ (Ioo 0 1) Ffun := strictConcaveOn_Ffun.concaveOn

/-- The elementary inequality `2 u < log (1 + u) − log (1 − u)` on `(0, 1)`: both sides vanish at
`u = 0` and the derivative of the difference is `2 / (1 − u²) − 2 > 0`. -/
private theorem two_mul_lt_log_sub_log {u : ℝ} (hu : 0 < u) (hu' : u < 1) :
    2 * u < Real.log (1 + u) - Real.log (1 - u) := by
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => Real.log (1 + y) - Real.log (1 - y) - 2 * y)
        (1 / (1 + x) + 1 / (1 - x) - 2) x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have hx1 : x < 1 := hx.2
    have h1 : (1 : ℝ) + x ≠ 0 := by positivity
    have h2 : (1 : ℝ) - x ≠ 0 := by intro h; linarith
    have hv : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id' (x := x)).const_add 1
    have hw : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := (hasDerivAt_id' (x := x)).const_sub 1
    refine (((hv.log h1).sub (hw.log h2)).sub
      ((hasDerivAt_id' (x := x)).const_mul (2 : ℝ))).congr_deriv ?_
    field_simp
    ring
  have hcont : ContinuousOn (fun y : ℝ => Real.log (1 + y) - Real.log (1 - y) - 2 * y)
      (Ico (0 : ℝ) 1) := by
    refine ContinuousOn.sub (ContinuousOn.sub ?_ ?_) (by fun_prop)
    · refine Real.continuousOn_log.comp (by fun_prop) fun x hx => ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have hx0 : (0 : ℝ) ≤ x := hx.1
      intro h
      linarith
    · refine Real.continuousOn_log.comp (by fun_prop) fun x hx => ?_
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have hx1 : x < 1 := hx.2
      intro h
      linarith
  have hpos : ∀ x ∈ interior (Ico (0 : ℝ) 1),
      0 < deriv (fun y : ℝ => Real.log (1 + y) - Real.log (1 - y) - 2 * y) x := by
    rw [interior_Ico]
    intro x hx
    have hx0 : (0 : ℝ) < x := hx.1
    have h1 : (0 : ℝ) < 1 + x := by linarith
    have h2 : (0 : ℝ) < 1 - x := by have := hx.2; linarith
    rw [(hderiv x hx).deriv, show 1 / (1 + x) + 1 / (1 - x) - 2
      = 2 * x ^ 2 / ((1 + x) * (1 - x)) by field_simp; ring]
    exact div_pos (by nlinarith) (mul_pos h1 h2)
  have h := strictMonoOn_of_deriv_pos (convex_Ico (0 : ℝ) 1) hcont hpos
    (left_mem_Ico.2 one_pos) ⟨hu.le, hu'⟩ hu
  norm_num at h
  linarith

/-- For `t > 1` the derivative of the closed form is negative: `2 / t < log (1 + t) − log (t − 1)`,
which is the previous inequality at `u = 1 / t`. -/
private theorem two_div_lt_log_sub_log {t : ℝ} (ht : 1 < t) :
    2 / t < Real.log (1 + t) - Real.log (t - 1) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have key := two_mul_lt_log_sub_log (u := 1 / t) (by positivity)
    (by rw [div_lt_one ht0]; exact ht)
  have e1 : (1 : ℝ) + 1 / t = (1 + t) / t := by field_simp; ring
  have e2 : (1 : ℝ) - 1 / t = (t - 1) / t := by field_simp
  rw [e1, e2, Real.log_div (by positivity) ht0.ne', Real.log_div (by linarith) ht0.ne',
    mul_one_div] at key
  linarith

/-- The closed form is at most `Ffun 1 = 2 − 2 log 2` on `[1, ∞)`. -/
theorem Ffun_le_of_one_le {t : ℝ} (ht : 1 ≤ t) : Ffun t ≤ 2 - 2 * Real.log 2 := by
  have hanti : AntitoneOn Ffun (Ici 1) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 1)
      (continuousOn_Ffun.mono fun x hx =>
        Set.mem_Ioi.2 (lt_of_lt_of_le one_pos (Set.mem_Ici.1 hx))) ?_ ?_
    · rw [interior_Ici]
      intro x hx
      have hx1 : (1 : ℝ) < x := hx
      exact (hasDerivAt_Ffun (by linarith)
        (ne_of_gt hx1)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro x hx
      have hx1 : (1 : ℝ) < x := hx
      rw [deriv_Ffun (by linarith) (ne_of_gt hx1),
        show |1 - x| = x - 1 by rw [abs_of_nonpos (by linarith : (1 : ℝ) - x ≤ 0)]; ring]
      have h := two_div_lt_log_sub_log hx1
      linarith
  have h := hanti Set.self_mem_Ici ht ht
  rwa [Ffun_one] at h

private theorem Ffun_one_third : Ffun (1 / 3) = 2 - 10 / 3 * Real.log 2 := by
  have l23 : Real.log (2 / 3 : ℝ) = Real.log 2 - Real.log 3 :=
    Real.log_div two_ne_zero (by norm_num)
  have l43 : Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.log_pow]
    push_cast
    ring
  have l13 : Real.log (1 / 3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  simp only [Ffun]
  rw [show |1 - (1 : ℝ) / 3| = 2 / 3 by rw [abs_of_nonneg (by norm_num)]; norm_num,
    show (1 : ℝ) + 1 / 3 = 4 / 3 by norm_num, l23, l43, l13]
  ring

/-- The closed form is nonpositive on `(0, 1/3]`: it increases there, and
`Ffun (1/3) = 2 − (10/3) log 2 < 0`. -/
theorem Ffun_nonpos_of_le_third {t : ℝ} (ht : 0 < t) (ht' : t ≤ 1 / 3) : Ffun t ≤ 0 := by
  have hmono : MonotoneOn Ffun (Ioc 0 (1 / 3)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ioc 0 (1 / 3))
      (continuousOn_Ffun.mono fun x hx => Set.mem_Ioi.2 hx.1) ?_ ?_
    · rw [interior_Ioc]
      intro x hx
      have hx1 : x < 1 / 3 := hx.2
      have hne : x ≠ 1 := by
        intro h
        rw [h] at hx1
        norm_num at hx1
      exact (hasDerivAt_Ffun hx.1 hne).differentiableAt.differentiableWithinAt
    · rw [interior_Ioc]
      intro x hx
      have hx0 : (0 : ℝ) < x := hx.1
      have hx1 : x < 1 / 3 := hx.2
      have h1x : (0 : ℝ) < 1 - x := by linarith
      have hne : x ≠ 1 := by
        intro h
        rw [h] at hx1
        norm_num at hx1
      rw [deriv_Ffun hx0 hne, show |1 - x| = 1 - x from abs_of_nonneg h1x.le]
      have hlow : 1 - (1 - x)⁻¹ ≤ Real.log (1 - x) := by
        have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (1 - x)⁻¹ by positivity)
        rw [Real.log_inv] at h
        linarith
      have hup : Real.log (1 + x) ≤ x := by
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + x by linarith)
        linarith
      have key : (0 : ℝ) ≤ 1 - (1 - x)⁻¹ - x + 2 / x := by
        rw [show 1 - (1 - x)⁻¹ - x + 2 / x
            = (2 * (1 - x) - x ^ 2 * (1 - x) - x ^ 2) / (x * (1 - x)) by field_simp; ring]
        exact div_nonneg (by nlinarith) (by positivity)
      linarith
  have h := hmono ⟨ht, ht'⟩ (⟨by norm_num, le_refl _⟩ : (1 : ℝ) / 3 ∈ Ioc (0 : ℝ) (1 / 3)) ht'
  rw [Ffun_one_third] at h
  linarith [Real.log_two_gt_d9]

end CenteredMaximal.Cauchy

end

end
