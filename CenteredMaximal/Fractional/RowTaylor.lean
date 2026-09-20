/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.CentredCubic
public import CenteredMaximal.Fractional.RowCollapse

/-!
# The centred bicubic model of one row of the collapsed spline generator

`CenteredMaximal.Fractional.splineGen_eq_rowSum` writes the spline half of the generator of the
comparison kernel as `53` rows in each of two coordinate directions, a row being

`P(v) · |u − k| ^ (9/5)`,

with `P` the column profile of `CenteredMaximal.Fractional.colProfile_eq_cubic` — a cubic on each
unit cell — and `k` the row index.  This file replaces that product, on a dyadic rectangle
`|u − u_c| ≤ δ`, `|v − v_c| ≤ δ`, by a **centred bicubic plus an explicit error**, which is the
form a certificate leaf adds up.

## The two factors

The elementary factor is expanded by `CenteredMaximal.Fractional.abs_rpow_nine_fifths_taylor` at
the centre `c = u_c − k`, giving the cubic `nineFifthsTaylor c` in the deviation `s = u − u_c` and
a remainder `(9/625) δ⁴ (|c| − δ)^{−11/5}`.  `nineFifthsTaylor_eq_sum` rewrites that cubic in the
four exponents the enclosure table carries: its coefficient of `sᵃ` is

`ρ(a) · |c| ^ ((9 − 5a)/5)`,      `ρ = (1, ±9/5, 18/25, ∓6/125)`,

with the two odd coefficients carrying the sign of `c`.  So every coefficient of the model is a
rational times *one* power of *one* positive rational — the shape
`CenteredMaximal.Fractional.encItv` reads.

The profile factor is a cubic in `t = v − v_c` with rational coefficients, and it multiplies the
remainder, so it needs a *sup* bound on the rectangle.  That bound is
`CenteredMaximal.Fractional.bernMax`, and it must be the genuine Bernstein bound: measured in exact
rational arithmetic at the table's precision `12`, the crude bound `∑ |coefficient| δ^degree` loses
`25` of the certificate's `4582` rectangles, while `bernMax` reproduces the search program's own
`pbound` exactly on all `18119` row cubics.

## Main results

* `taylorExp`, `taylorRhoQ`: the four exponent numerators `9, 4, −1, −6` and the four rational
  prefactors of the cubic Taylor model, the odd ones signed.
* `nineFifthsTaylor_eq_sum`: **the Taylor model as a centred cubic** in those four powers.
* `rowProduct_bound`: **the model of one row.**  The product of a rational cubic profile with
  `|u − k| ^ (9/5)` differs from the centred bicubic `∑_{a,b} ρ(a) p(b) |c|^{(9−5a)/5} sᵃ tᵇ` by at
  most `bernMax · (9/625) δ⁴ (|c| − δ)^{−11/5}`.
-/

@[expose] public section

noncomputable section

namespace CenteredMaximal.Fractional

/-! ### The four powers of the cubic Taylor model -/

/-- The numerator, over `5`, of the exponent of `|c|` in the `a`-th coefficient of the cubic Taylor
model of `|·| ^ (9/5)`: the four values `9, 4, −1, −6`. -/
def taylorExp (a : ℕ) : ℤ := 9 - 5 * (a : ℤ)

/-- The rational prefactor of the `a`-th coefficient of the cubic Taylor model of `|·| ^ (9/5)`.
The two odd coefficients carry the sign of the centre, which `pos` records. -/
def taylorRhoQ (pos : Bool) (a : ℕ) : ℚ :=
  match a with
  | 0 => 1
  | 1 => if pos then 9 / 5 else -(9 / 5)
  | 2 => 18 / 25
  | 3 => if pos then -(6 / 125) else 6 / 125
  | _ + 4 => 0

/-- **The cubic Taylor model as a centred cubic in the four tabulated powers.**  This is
`nineFifthsTaylor_of_pos` and `nineFifthsTaylor_of_neg` written as a single sum, so that a model
fold reads one rational prefactor and one exponent per degree. -/
theorem nineFifthsTaylor_eq_sum {c : ℝ} {m : ℚ} (hm : (m : ℝ) = |c|) {pos : Bool}
    (hpos : if pos then 0 < c else c < 0) (x : ℝ) :
    nineFifthsTaylor c x
      = ∑ a ∈ Finset.range 4, ((taylorRhoQ pos a : ℚ) : ℝ) *
          (m : ℝ) ^ (((taylorExp a : ℤ) : ℝ) / 5) * (x - c) ^ a := by
  have he0 : (((taylorExp 0 : ℤ) : ℝ) / 5) = 9 / 5 := by rw [taylorExp]; norm_num
  have he1 : (((taylorExp 1 : ℤ) : ℝ) / 5) = 4 / 5 := by rw [taylorExp]; norm_num
  have he2 : (((taylorExp 2 : ℤ) : ℝ) / 5) = -(1 / 5) := by rw [taylorExp]; norm_num
  have he3 : (((taylorExp 3 : ℤ) : ℝ) / 5) = -(6 / 5) := by rw [taylorExp]; norm_num
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    he0, he1, he2, he3]
  cases pos with
  | false =>
      have hc : c < 0 := by simpa using hpos
      rw [nineFifthsTaylor_of_neg hc, hm]
      simp only [taylorRhoQ, Bool.false_eq_true, if_false]
      push_cast
      ring
  | true =>
      have hc : 0 < c := by simpa using hpos
      have habs : (m : ℝ) = c := by rw [hm, abs_of_pos hc]
      rw [nineFifthsTaylor_of_pos hc, habs]
      simp only [taylorRhoQ, if_true]
      push_cast
      ring

/-! ### The model of one row -/

/-- **The centred bicubic model of one row of the collapsed spline generator.**  On the rectangle
`|s| ≤ δ`, `|t| ≤ δ` the product of the rational cubic profile `∑_b p(b) tᵇ` with the elementary
function `|c + s| ^ (9/5)` is the centred bicubic whose `(a, b)` coefficient is
`ρ(a) p(b) · m ^ ((9 − 5a)/5)`, up to the profile's Bernstein sup bound times the Taylor remainder.

The hypothesis `δ < m` is what keeps the interval `[c − δ, c + δ]` away from the origin, where
`|·| ^ (9/5)` is not four times differentiable. -/
theorem rowProduct_bound {c s t : ℝ} {m δ : ℚ} (hδ : 0 < δ) (hmδ : δ < m)
    (hm : (m : ℝ) = |c|) {pos : Bool} (hpos : if pos then 0 < c else c < 0)
    (hs : |s| ≤ (δ : ℝ)) (ht : |t| ≤ (δ : ℝ)) (p : ℕ → ℚ) :
    |(∑ b ∈ Finset.range 4, (p b : ℝ) * t ^ b) * |c + s| ^ (9 / 5 : ℝ)
        - ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
            ((taylorRhoQ pos a * p b : ℚ) : ℝ) * (m : ℝ) ^ (((taylorExp a : ℤ) : ℝ) / 5)
              * s ^ a * t ^ b|
      ≤ ((bernMax p δ : ℚ) : ℝ) *
          (9 / 625 * (δ : ℝ) ^ 4 * (((m - δ : ℚ)) : ℝ) ^ (-(11 / 5) : ℝ)) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hmR : (δ : ℝ) < (m : ℝ) := by exact_mod_cast hmδ
  have hcabs : (δ : ℝ) < |c| := by rwa [hm] at hmR
  have hxc : |c + s - c| ≤ (δ : ℝ) := by rwa [add_sub_cancel_left]
  -- the Taylor model of the elementary factor
  have htay := abs_rpow_nine_fifths_taylor (c := c) (δ := (δ : ℝ)) (x := c + s) hδR hcabs hxc
  rw [← hm] at htay
  have hsub : (((m - δ : ℚ)) : ℝ) = (m : ℝ) - (δ : ℝ) := by push_cast; ring
  rw [hsub]
  -- the profile factor and its Bernstein sup bound
  have hbern := abs_centredCubic_le_bernMax (a := p) hδ ht
  -- the bicubic is the product of the two cubics
  have hprod : (∑ b ∈ Finset.range 4, (p b : ℝ) * t ^ b) * nineFifthsTaylor c (c + s)
      = ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
          ((taylorRhoQ pos a * p b : ℚ) : ℝ) * (m : ℝ) ^ (((taylorExp a : ℤ) : ℝ) / 5)
            * s ^ a * t ^ b := by
    rw [nineFifthsTaylor_eq_sum hm hpos, add_sub_cancel_left, mul_comm, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  -- the difference is the profile times the Taylor remainder
  have hsplit : (∑ b ∈ Finset.range 4, (p b : ℝ) * t ^ b) * |c + s| ^ (9 / 5 : ℝ)
      - ∑ a ∈ Finset.range 4, ∑ b ∈ Finset.range 4,
          ((taylorRhoQ pos a * p b : ℚ) : ℝ) * (m : ℝ) ^ (((taylorExp a : ℤ) : ℝ) / 5)
            * s ^ a * t ^ b
      = (∑ b ∈ Finset.range 4, (p b : ℝ) * t ^ b) *
          ((|c + s| ^ (9 / 5 : ℝ)) - nineFifthsTaylor c (c + s)) := by
    rw [← hprod]
    ring
  rw [hsplit, abs_mul]
  refine mul_le_mul hbern htay (abs_nonneg _) ?_
  have := bernMax_nonneg p δ
  exact_mod_cast this

end CenteredMaximal.Fractional

end

end
