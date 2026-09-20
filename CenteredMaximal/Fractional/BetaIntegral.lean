/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# The real Beta integral in its two classical forms

Mathlib knows the Beta function as a complex-valued integral, `Complex.betaIntegral`, and
identifies it with a quotient of Gamma values in `Complex.betaIntegral_eq_Gamma_mul_div`.  The
fractional (order `6/5`) layer of the planar centred maximal bound needs the **real** statements,
and in particular the **type-2** (half-line) form, which Mathlib does not have at all.  This file
supplies both, together with the matching integrability statements.

Write `Β (a, b) = Γ a * Γ b / Γ (a + b)`; this is `betaFun`.  The two classical integral
representations proved here are

* type 1: `∫ x in (0:ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) = Β (a, b)`;
* type 2: `∫ t in Ioi (0:ℝ), t ^ (a - 1) * (1 + t) ^ (-a - b) = Β (a, b)`,

both for `0 < a` and `0 < b`, with `^` the real power `Real.rpow` throughout.  Note that the
type-1 integrand is genuinely unbounded near an endpoint as soon as `a < 1` or `b < 1`; the
integrals below are honest convergent improper integrals, not integrals of bounded functions.

## Main results

* `betaFun`: the Gamma quotient `Γ a * Γ b / Γ (a + b)`, with `betaFun_comm` and `betaFun_pos`.
* `intervalIntegrable_rpow_mul_one_sub_rpow`, `integral_rpow_mul_one_sub_rpow`: the type-1 Beta
  integral and its convergence.  The proof transfers `Complex.betaIntegral` along `Complex.ofReal`,
  which is legitimate pointwise on all of `[0, 1]` (not merely almost everywhere) because
  `Complex.ofReal_cpow` only asks for a nonnegative base.
* `integrableOn_Ioi_rpow_mul_one_add_rpow`, `integral_Ioi_rpow_mul_one_add_rpow`: the type-2 Beta
  integral and its convergence, obtained from the type-1 form by the Möbius substitution
  `t = u / (1 - u)`.
* `betaFun_eq_integral`, `betaFun_eq_integral_Ioi`: the same two identities phrased as formulas
  for `betaFun`.
* `betaFun_one_sub_left`, `betaFun_one_sub_right`, `integral_Ioi_rpow_mul_one_add_inv`: the
  reflection-formula degeneration `Β (1 - α, α) = π / sin (π α)`.

## The substitution

The change of variables behind the type-2 form is the Möbius map `u ↦ u / (1 - u)`, a bijection
`(0, 1) → (0, ∞)` with inverse `t ↦ t / (1 + t)`.  Along it `1 + t = (1 - u)⁻¹` and
`dt = du / (1 - u) ^ 2`, so

`t ^ (a - 1) (1 + t) ^ (-a - b) dt`
`  = u ^ (a - 1) (1 - u) ^ (1 - a) (1 - u) ^ (a + b) (1 - u) ^ (-2) du`
`  = u ^ (a - 1) (1 - u) ^ (b - 1) du`,

which is exactly the type-1 integrand.  Because Mathlib's one-dimensional Jacobian lemmas
(`MeasureTheory.integral_image_eq_integral_abs_deriv_smul` and its integrability companion
`MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul`) need no integrability
hypothesis, the equality of the two integrals and the equivalence of the two integrability
statements both come out of a single application, and the convergence statement for the half-line
is a consequence rather than a prerequisite.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

open scoped Real

namespace CenteredMaximal.Fractional

/-! ## The Beta function as a quotient of Gamma values -/

/-- The **Beta function** `Β (a, b) = Γ a * Γ b / Γ (a + b)`.  For `0 < a` and `0 < b` it is the
value of both classical Beta integrals, `integral_rpow_mul_one_sub_rpow` and
`integral_Ioi_rpow_mul_one_add_rpow`. -/
def betaFun (a b : ℝ) : ℝ := Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)

theorem betaFun_comm (a b : ℝ) : betaFun a b = betaFun b a := by
  rw [betaFun, betaFun, mul_comm, add_comm]

theorem betaFun_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 < betaFun a b :=
  div_pos (mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos hb))
    (Real.Gamma_pos_of_pos (add_pos ha hb))

/-! ## Type 1: the Beta integral over the unit interval -/

/-- The type-1 Beta integrand is interval integrable on `[0, 1]`.  Both endpoints are singular
when the corresponding exponent is negative, so the two halves are treated separately. -/
theorem intervalIntegrable_rpow_mul_one_sub_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1)) volume 0 1 := by
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have left : IntervalIntegrable (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1))
      volume 0 (1 / 2) := by
    refine (intervalIntegral.intervalIntegrable_rpow'
      (by linarith : -1 < a - 1)).mul_continuousOn ?_
    refine ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl ?_
    rw [uIcc_of_le hhalf] at hx
    exact ne_of_gt (by linarith [hx.2] : (0 : ℝ) < 1 - x)
  have right : IntervalIntegrable (fun x : ℝ => x ^ (a - 1) * (1 - x) ^ (b - 1))
      volume (1 / 2) 1 := by
    have hsing : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (b - 1)) volume (1 / 2) 1 := by
      have h := (intervalIntegral.intervalIntegrable_rpow' (r := b - 1) (a := 1 / 2) (b := 0)
        (by linarith)).comp_sub_left 1
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num, sub_zero] at h
      exact h
    refine hsing.continuousOn_mul ?_
    refine ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl ?_
    rw [uIcc_of_le (by norm_num : (1 : ℝ) / 2 ≤ 1)] at hx
    exact ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x)
  exact left.trans right

/-- **The classical (type-1) Beta integral**, in real form:
`∫₀¹ x ^ (a - 1) * (1 - x) ^ (b - 1) = Γ a * Γ b / Γ (a + b)` for `0 < a` and `0 < b`. -/
theorem integral_rpow_mul_one_sub_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ x in (0:ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1)
      = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have bridge : Complex.betaIntegral a b
      = ((∫ x in (0:ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal, Complex.betaIntegral]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hx
    have h0 : (0 : ℝ) ≤ x := hx.1
    have h1 : (0 : ℝ) ≤ 1 - x := by linarith [hx.2]
    rw [Complex.ofReal_mul, Complex.ofReal_cpow h0, Complex.ofReal_cpow h1]
    push_cast
    ring
  rw [Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha) (by simpa using hb),
    ← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_div, Complex.ofReal_inj] at bridge
  exact bridge.symm

/-- `betaFun` as the type-1 Beta integral. -/
theorem betaFun_eq_integral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    betaFun a b = ∫ x in (0:ℝ)..1, x ^ (a - 1) * (1 - x) ^ (b - 1) :=
  (integral_rpow_mul_one_sub_rpow ha hb).symm

/-! ## The Möbius substitution `t = u / (1 - u)` -/

/-- The Möbius map `u ↦ u / (1 - u)` sends `(0, 1)` onto `(0, ∞)`; the inverse is
`t ↦ t / (1 + t)`. -/
theorem image_div_one_sub_Ioo : (fun u : ℝ => u / (1 - u)) '' Ioo 0 1 = Ioi 0 := by
  ext t
  simp only [mem_image, mem_Ioo, mem_Ioi]
  constructor
  · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
    exact div_pos hu0 (by linarith)
  · intro ht
    have hden : (1 : ℝ) + t ≠ 0 := by positivity
    refine ⟨t / (1 + t), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one (by linarith)]; linarith
    · rw [show (1 : ℝ) - t / (1 + t) = (1 + t)⁻¹ by field_simp; ring]
      field_simp

/-- The Möbius map `u ↦ u / (1 - u)` is injective on `(0, 1)`. -/
theorem injOn_div_one_sub : InjOn (fun u : ℝ => u / (1 - u)) (Ioo 0 1) := by
  intro u hu v hv huv
  have hu' : (1 : ℝ) - u ≠ 0 := ne_of_gt (by linarith [hu.2] : (0 : ℝ) < 1 - u)
  have hv' : (1 : ℝ) - v ≠ 0 := ne_of_gt (by linarith [hv.2] : (0 : ℝ) < 1 - v)
  field_simp at huv
  linarith

/-- The derivative of the Möbius map `u ↦ u / (1 - u)` is `((1 - u) ^ 2)⁻¹`. -/
theorem hasDerivAt_div_one_sub {u : ℝ} (hu : u ≠ 1) :
    HasDerivAt (fun x : ℝ => x / (1 - x)) (((1 - u) ^ 2)⁻¹) u := by
  have h : (1 : ℝ) - u ≠ 0 := sub_ne_zero.2 (Ne.symm hu)
  have hd : HasDerivAt (fun x : ℝ => 1 - x) (-1) u := by
    simpa using HasDerivAt.const_sub (1 : ℝ) (hasDerivAt_id' u)
  have key := (hasDerivAt_id' u).fun_div hd h
  have e : (1 * (1 - u) - u * -1) / (1 - u) ^ 2 = ((1 - u) ^ 2)⁻¹ := by
    rw [show 1 * (1 - u) - u * -1 = (1 : ℝ) from by ring, one_div]
  rw [← e]
  exact key

/-- The substitution `t = u / (1 - u)` carries the type-2 Beta integrand, weighted by the
Jacobian, exactly to the type-1 Beta integrand. -/
theorem abs_deriv_smul_rpow_mul_one_add_rpow (a b : ℝ) :
    EqOn (fun u : ℝ => |((1 - u) ^ 2)⁻¹| •
        ((u / (1 - u)) ^ (a - 1) * (1 + u / (1 - u)) ^ (-a - b)))
      (fun u : ℝ => u ^ (a - 1) * (1 - u) ^ (b - 1)) (Ioo 0 1) := by
  intro u hu
  obtain ⟨hu0, hu1⟩ := hu
  have hv : (0 : ℝ) < 1 - u := by linarith
  have e1 : (1 : ℝ) + u / (1 - u) = (1 - u)⁻¹ := by field_simp; ring
  have e2 : (u / (1 - u)) ^ (a - 1) = u ^ (a - 1) * (1 - u) ^ (1 - a) := by
    rw [Real.div_rpow hu0.le hv.le, div_eq_mul_inv, ← Real.rpow_neg hv.le, neg_sub]
  have e3 : ((1 - u)⁻¹ : ℝ) ^ (-a - b) = (1 - u) ^ (a + b) := by
    rw [Real.inv_rpow hv.le, ← Real.rpow_neg hv.le]
    congr 1
    ring
  have e4 : (((1 - u) ^ 2)⁻¹ : ℝ) = (1 - u) ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hv.le, Real.rpow_two]
  simp only [smul_eq_mul]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((1 - u) ^ 2)⁻¹), e1, e2, e3, e4,
    show (1 - u) ^ (-2 : ℝ) * (u ^ (a - 1) * (1 - u) ^ (1 - a) * (1 - u) ^ (a + b))
      = u ^ (a - 1) * ((1 - u) ^ (-2 : ℝ) * (1 - u) ^ (1 - a) * (1 - u) ^ (a + b)) from by ring,
    ← Real.rpow_add hv, ← Real.rpow_add hv]
  congr 2
  ring

/-! ## Type 2: the Beta integral over the half line -/

/-- The type-2 Beta integrand is integrable on `(0, ∞)` under the same hypotheses that make the
type-1 integrand integrable: it behaves like `t ^ (a - 1)` at the origin and like `t ^ (-b - 1)`
at infinity, so `0 < a` and `0 < b` are exactly what convergence needs. -/
theorem integrableOn_Ioi_rpow_mul_one_add_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * (1 + t) ^ (-a - b)) (Ioi 0) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul (f := fun u : ℝ => u / (1 - u))
    (f' := fun u : ℝ => ((1 - u) ^ 2)⁻¹) (s := Ioo (0:ℝ) 1) measurableSet_Ioo
    (fun u hu => (hasDerivAt_div_one_sub (ne_of_lt hu.2)).hasDerivWithinAt) injOn_div_one_sub
    (fun t : ℝ => t ^ (a - 1) * (1 + t) ^ (-a - b))
  rw [image_div_one_sub_Ioo] at h
  refine h.2 ((integrableOn_congr_fun (abs_deriv_smul_rpow_mul_one_add_rpow a b)
    measurableSet_Ioo).2 ?_)
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one]
  exact intervalIntegrable_rpow_mul_one_sub_rpow ha hb

/-- **The type-2 Beta integral**, in real form:
`∫₀^∞ t ^ (a - 1) * (1 + t) ^ (-a - b) = Γ a * Γ b / Γ (a + b)` for `0 < a` and `0 < b`. -/
theorem integral_Ioi_rpow_mul_one_add_rpow {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Ioi (0:ℝ), t ^ (a - 1) * (1 + t) ^ (-a - b)
      = Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  have h := integral_image_eq_integral_abs_deriv_smul (f := fun u : ℝ => u / (1 - u))
    (f' := fun u : ℝ => ((1 - u) ^ 2)⁻¹) (s := Ioo (0:ℝ) 1) measurableSet_Ioo
    (fun u hu => (hasDerivAt_div_one_sub (ne_of_lt hu.2)).hasDerivWithinAt) injOn_div_one_sub
    (fun t : ℝ => t ^ (a - 1) * (1 + t) ^ (-a - b))
  rw [image_div_one_sub_Ioo] at h
  rw [h, setIntegral_congr_fun measurableSet_Ioo (abs_deriv_smul_rpow_mul_one_add_rpow a b),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow_mul_one_sub_rpow ha hb]

/-- `betaFun` as the type-2 Beta integral. -/
theorem betaFun_eq_integral_Ioi {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    betaFun a b = ∫ t in Ioi (0:ℝ), t ^ (a - 1) * (1 + t) ^ (-a - b) :=
  (integral_Ioi_rpow_mul_one_add_rpow ha hb).symm

/-! ## Degeneration to Euler's reflection formula -/

/-- Euler's reflection formula, read off the Beta function: `Β (1 - α, α) = π / sin (π α)`. -/
theorem betaFun_one_sub_left (α : ℝ) : betaFun (1 - α) α = π / Real.sin (π * α) := by
  rw [betaFun, show (1 : ℝ) - α + α = 1 from by ring, Real.Gamma_one, div_one, mul_comm,
    Real.Gamma_mul_Gamma_one_sub]

/-- Euler's reflection formula, read off the Beta function: `Β (α, 1 - α) = π / sin (π α)`. -/
theorem betaFun_one_sub_right (α : ℝ) : betaFun α (1 - α) = π / Real.sin (π * α) := by
  rw [betaFun_comm, betaFun_one_sub_left]

/-- The type-2 Beta integral at `(a, b) = (1 - α, α)` is the reflection-formula integral
`∫₀^∞ t ^ (-α) / (1 + t) = π / sin (π α)` for `0 < α < 1`. -/
theorem integral_Ioi_rpow_mul_one_add_inv {α : ℝ} (h0 : 0 < α) (h1 : α < 1) :
    ∫ t in Ioi (0:ℝ), t ^ (-α) * (1 + t) ^ (-1 : ℝ) = π / Real.sin (π * α) := by
  have h := integral_Ioi_rpow_mul_one_add_rpow (a := 1 - α) (b := α) (by linarith) h0
  rw [show (1 : ℝ) - α - 1 = -α from by ring,
    show -(1 - α) - α = (-1 : ℝ) from by ring] at h
  rw [h, ← betaFun, betaFun_one_sub_left]

end CenteredMaximal.Fractional

end

end
