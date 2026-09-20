/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# The one-simplex Bernstein bound for a cubic on an interval

A leaf of the majorization certificate needs, over and over, a bound on a cubic polynomial over a
dyadic interval.  The polynomial arrives in the *centred monomial* basis: the caller has the four
coefficients `a 0, a 1, a 2, a 3` of the map `x ↦ ∑_{m<4} a m * x ^ m`, where `x` is the deviation
from the centre of an interval of half-width `δ`, so the domain is `|x| ≤ δ`.

The **Bernstein test** on an interval is the one-dimensional case of the barycentric test of
`CenteredMaximal.Fractional.MajorPoly`.  Write the two barycentric coordinates of the interval,
`λ = (δ - x) / (2δ)` and `μ = (δ + x) / (2δ)`; these are nonnegative exactly on `|x| ≤ δ` and they
sum to `1`.  The four cubic Bernstein basis polynomials `λ³, 3λ²μ, 3λμ², μ³` are then nonnegative
and sum to `(λ + μ)³ = 1`, i.e. they are a *partition of unity* on the interval, so any polynomial
written against them is a convex combination of the four coefficients and is squeezed between the
least and the greatest of them.  In particular its absolute value is at most the greatest absolute
value.

All of the content is therefore the change of basis.  Eliminating `x` through `x = δ (μ - λ)` turns
the change of basis into a polynomial identity in `λ` and `μ`, which is `centredCubic_eq_bernstein`;
everything else in this file is bookkeeping around it.  The coefficients of the new basis are
`bernCoef`: with the scaled coefficients `A m = a m * δ ^ m`, they are

```
b 0 = A 0 - A 1 + A 2 - A 3,      b 1 = A 0 - A 1 / 3 - A 2 / 3 + A 3,
b 2 = A 0 + A 1 / 3 - A 2 / 3 - A 3,      b 3 = A 0 + A 1 + A 2 + A 3.
```

The outer two are the endpoint values `p (-δ)` and `p δ`, and the inner two are the endpoint values
corrected by a third of the endpoint derivatives — the usual de Casteljau data of the cubic.

## Why the crude bound is not enough

The naive alternative is the triangle inequality on the monomials, `|p x| ≤ ∑_m |a m| δ ^ m`, which
is what `CenteredMaximal.Fractional.centeredPoly_ge` uses in two variables.  It is strictly weaker,
and here the difference decides the certificate.  Measured in exact rational arithmetic against the
`4582`-rectangle certificate this development formalises: the crude bound **loses `25` of the `4582`
rectangles**, with worst deficit `-6.06` in the author's normalisation, whereas the Bernstein bound
of this file **reproduces the search program's own `pbound` exactly on all `18119` row cubics of the
certificate**.  So the Bernstein coefficients are not an optimisation, they are what makes the leaf
inequalities true at the certificate's subdivision depth.

## Main results

* `bernCoef`, `bernMax`: the four Bernstein coefficients of the centred cubic on `[-δ, δ]`, and the
  largest of their absolute values.  Both are plain computable `ℚ` functions built from `+`, `*`,
  `/` and `max`, with no `Finset.sup` and no decidable-instance detour, because they are consumed by
  `decide +kernel` inside a certificate check and the kernel has to unfold them.
* `centredCubic_eq_bernstein`: **the Bernstein identity**, the change of basis from centred
  monomials to the cubic Bernstein basis of the interval.  This is the reusable content.
* `abs_centredCubic_le_bernMax`: **the one-simplex Bernstein bound.**  A cubic in the deviation from
  the centre of an interval of half-width `δ` is bounded in absolute value, on that interval, by the
  largest absolute value of its four Bernstein coefficients.
-/

@[expose] public section

namespace CenteredMaximal.Fractional

/-! ### The Bernstein coefficients of a centred cubic -/

/-- **The four Bernstein coefficients** of the centred cubic `x ↦ ∑_{m<4} a m * x ^ m` on the
interval `[-δ, δ]`, indexed `0, 1, 2, 3` from the left endpoint to the right one and extended by
zero past `3`.  They are written out in the scaled coefficients `a m * δ ^ m` rather than through an
auxiliary definition so that the kernel unfolds one of them in a fixed, small number of steps. -/
def bernCoef (a : ℕ → ℚ) (δ : ℚ) : ℕ → ℚ
  | 0 => a 0 - a 1 * δ + a 2 * δ ^ 2 - a 3 * δ ^ 3
  | 1 => a 0 - a 1 * δ / 3 - a 2 * δ ^ 2 / 3 + a 3 * δ ^ 3
  | 2 => a 0 + a 1 * δ / 3 - a 2 * δ ^ 2 / 3 - a 3 * δ ^ 3
  | 3 => a 0 + a 1 * δ + a 2 * δ ^ 2 + a 3 * δ ^ 3
  | _ + 4 => 0

/-- **The Bernstein bound** of a centred cubic on `[-δ, δ]`: the largest absolute value of its four
Bernstein coefficients.  A balanced `max (max _ _) (max _ _)` is used instead of `Finset.sup` or
`Finset.max'` so that the kernel sees four rational comparisons and nothing else. -/
def bernMax (a : ℕ → ℚ) (δ : ℚ) : ℚ :=
  max (max |bernCoef a δ 0| |bernCoef a δ 1|) (max |bernCoef a δ 2| |bernCoef a δ 3|)

/-- The Bernstein bound is nonnegative, being a maximum of absolute values. -/
theorem bernMax_nonneg (a : ℕ → ℚ) (δ : ℚ) : 0 ≤ bernMax a δ :=
  (abs_nonneg (bernCoef a δ 0)).trans ((le_max_left _ _).trans (le_max_left _ _))

/-- Each of the four Bernstein coefficients is dominated in absolute value by `bernMax`. -/
theorem abs_bernCoef_le_bernMax (a : ℕ → ℚ) (δ : ℚ) {m : ℕ} (hm : m < 4) :
    |bernCoef a δ m| ≤ bernMax a δ := by
  match m, hm with
  | 0, _ => exact (le_max_left _ _).trans (le_max_left _ _)
  | 1, _ => exact (le_max_right _ _).trans (le_max_left _ _)
  | 2, _ => exact (le_max_left _ _).trans (le_max_right _ _)
  | 3, _ => exact (le_max_right _ _).trans (le_max_right _ _)

/-! ### The Bernstein identity -/

/-- **The Bernstein identity for a centred cubic.**  On an interval of half-width `δ > 0` centred at
the origin, with barycentric coordinates `λ = (δ - x) / (2δ)` and `μ = (δ + x) / (2δ)`, the centred
cubic `∑_{m<4} a m * x ^ m` equals `b₀ λ³ + 3 b₁ λ² μ + 3 b₂ λ μ² + b₃ μ³`.

No inequality is involved and `x` is unrestricted: this is a polynomial identity in `x` once the
denominators `2δ` are cleared, and it is the whole mathematical content of the file. -/
theorem centredCubic_eq_bernstein (a : ℕ → ℚ) {δ : ℚ} (hδ : 0 < δ) (x : ℝ) :
    ∑ m ∈ Finset.range 4, (a m : ℝ) * x ^ m
      = (bernCoef a δ 0 : ℝ) * (((δ : ℝ) - x) / (2 * (δ : ℝ))) ^ 3
        + 3 * (bernCoef a δ 1 : ℝ) * (((δ : ℝ) - x) / (2 * (δ : ℝ))) ^ 2
            * (((δ : ℝ) + x) / (2 * (δ : ℝ)))
        + 3 * (bernCoef a δ 2 : ℝ) * (((δ : ℝ) - x) / (2 * (δ : ℝ)))
            * (((δ : ℝ) + x) / (2 * (δ : ℝ))) ^ 2
        + (bernCoef a δ 3 : ℝ) * (((δ : ℝ) + x) / (2 * (δ : ℝ))) ^ 3 := by
  have hδ0 : (δ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hδ)
  simp only [bernCoef, Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  field_simp
  ring

/-! ### The bound -/

/-- **The one-simplex Bernstein bound.**  A cubic in the deviation from the centre of an interval of
half-width `δ` is bounded in absolute value by the largest absolute value of its four Bernstein
coefficients on that interval.

The proof is the partition-of-unity argument: `centredCubic_eq_bernstein` writes the cubic against
the four Bernstein basis polynomials, which are nonnegative on `|x| ≤ δ` and sum to `(λ + μ)³ = 1`,
so replacing each coefficient by `bernMax a δ` can only increase the value and collapses the sum to
`bernMax a δ` itself. -/
theorem abs_centredCubic_le_bernMax {a : ℕ → ℚ} {δ : ℚ} (hδ : 0 < δ) {x : ℝ}
    (hx : |x| ≤ (δ : ℝ)) :
    |∑ m ∈ Finset.range 4, (a m : ℝ) * x ^ m| ≤ ((bernMax a δ : ℚ) : ℝ) := by
  obtain ⟨hxl, hxr⟩ := abs_le.mp hx
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  set M : ℝ := ((bernMax a δ : ℚ) : ℝ) with hM
  set lam : ℝ := ((δ : ℝ) - x) / (2 * (δ : ℝ)) with hlamDef
  set mu : ℝ := ((δ : ℝ) + x) / (2 * (δ : ℝ)) with hmuDef
  have hlam : 0 ≤ lam := div_nonneg (by linarith) (by linarith)
  have hmu : 0 ≤ mu := div_nonneg (by linarith) (by linarith)
  have hone : lam + mu = 1 := by
    rw [hlamDef, hmuDef]
    field_simp
    ring
  -- the four basis polynomials, as nonnegative weights summing to one
  have hw0 : (0 : ℝ) ≤ lam ^ 3 := pow_nonneg hlam 3
  have hw1 : (0 : ℝ) ≤ 3 * lam ^ 2 * mu :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hlam 2)) hmu
  have hw2 : (0 : ℝ) ≤ 3 * lam * mu ^ 2 :=
    mul_nonneg (mul_nonneg (by norm_num) hlam) (pow_nonneg hmu 2)
  have hw3 : (0 : ℝ) ≤ mu ^ 3 := pow_nonneg hmu 3
  have hpart : lam ^ 3 + 3 * lam ^ 2 * mu + (3 * lam * mu ^ 2 + mu ^ 3) = 1 := by
    have h : (lam + mu) ^ 3 = 1 := by rw [hone]; norm_num
    linear_combination h
  -- each coefficient, cast to `ℝ`, is dominated by `M`
  have hcoef : ∀ m : ℕ, m < 4 → |((bernCoef a δ m : ℚ) : ℝ)| ≤ M := by
    intro m hm
    rw [hM, ← Rat.cast_abs]
    exact_mod_cast abs_bernCoef_le_bernMax a δ hm
  -- the single estimate `|c * w| ≤ M * w` for a nonnegative weight `w`
  have hstep : ∀ c w : ℝ, |c| ≤ M → 0 ≤ w → |c * w| ≤ M * w := by
    intro c w hc hw
    rw [abs_mul, abs_of_nonneg hw]
    exact mul_le_mul_of_nonneg_right hc hw
  have e0 := abs_le.mp (hstep _ _ (hcoef 0 (by norm_num)) hw0)
  have e1 := abs_le.mp (hstep _ _ (hcoef 1 (by norm_num)) hw1)
  have e2 := abs_le.mp (hstep _ _ (hcoef 2 (by norm_num)) hw2)
  have e3 := abs_le.mp (hstep _ _ (hcoef 3 (by norm_num)) hw3)
  have hMsum : M * lam ^ 3 + M * (3 * lam ^ 2 * mu) + M * (3 * lam * mu ^ 2) + M * mu ^ 3 = M := by
    linear_combination M * hpart
  have hrep : ∑ m ∈ Finset.range 4, (a m : ℝ) * x ^ m
      = ((bernCoef a δ 0 : ℚ) : ℝ) * lam ^ 3 + ((bernCoef a δ 1 : ℚ) : ℝ) * (3 * lam ^ 2 * mu)
        + ((bernCoef a δ 2 : ℚ) : ℝ) * (3 * lam * mu ^ 2)
        + ((bernCoef a δ 3 : ℚ) : ℝ) * mu ^ 3 := by
    rw [centredCubic_eq_bernstein a hδ x]; ring
  rw [hrep, abs_le]
  constructor <;> linarith [e0.1, e0.2, e1.1, e1.2, e2.1, e2.2, e3.1, e3.2]

end CenteredMaximal.Fractional

end
