/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.RadialTangent
public import CenteredMaximal.Fractional.RowTaylor

/-!
# The affine model of `|x| ^ (9/5)` on an interval that touches the origin

`CenteredMaximal.Fractional.abs_rpow_nine_fifths_taylor` expands the elementary factor
`F x = |x| ^ (9/5)` of the `α = 6/5` spline generator into a cubic with Lagrange remainder
`(9/625) δ⁴ (|c| − δ) ^ (−11/5)` on `[c − δ, c + δ]`.  That bound is only available under the
hypothesis `δ < |c|`: the fourth derivative `(216/625) x ^ (−11/5)` blows up at the origin, and the
remainder written above blows up with it as `δ ↑ |c|`.  **A leaf whose interval reaches `0` gets no
cubic model at all**, and the certificate has many such leaves.

## The measurement

Of the `4582` rectangles of the `α = 6/5` generator certificate, `2644` — `57.7%` — have at least
one row whose interval touches the origin, that is, has `|c| = δ` exactly; `3424` of the `363487`
row evaluations are of that kind.  No row ever straddles the origin (`|c| < δ` never happens) and no
row is centred on it (`c = 0` never happens).  So the degenerate case is exactly the boundary case
`|c| = δ`, and it is the majority of the certificate rather than a rare exception.

## The model and its sharp constant

On `|c| = δ` the interval is `[0, 2δ]` (for `c = δ > 0`; the other sign is the reflection
`x ↦ −x`), and the model drops from the cubic to its **affine part**, the tangent line of `F` at
`c`,

`L(x) = δ ^ (9/5) + (9/5) δ ^ (4/5) (x − δ) = −(4/5) δ ^ (9/5) + (9/5) δ ^ (4/5) x`.

Two elementary facts bracket `F − L` on the interval.  Below, `L ≤ F` because `t ↦ t ^ (9/5)` is
convex on `[0, ∞)` and a convex function lies above its tangent (`tangent_le_of_convexOn`).  Above,
`F − L ≤ (4/5) δ ^ (9/5)` reduces, after the substitution `x = δ y` with `y ∈ [0, 2]`, to
`y ^ (9/5) ≤ (9/5) y`, which holds because `y ^ (9/5) = y · y ^ (4/5) ≤ y · 2 ^ (4/5)` and
`2 ^ (4/5) ≤ 9/5`, the latter because `2 ⁴ = 16 ≤ (9/5) ⁵ = 59049/3125 = 18.89…`.

**The constant `4/5` is sharp, and is attained at the endpoint nearest the origin.**  At `x = 0` the
tangent line takes the value `−(4/5) δ ^ (9/5)` while `F` vanishes, so the error is exactly
`(4/5) δ ^ (9/5)` there.  At the far endpoint `x = 2δ` the error is only
`(2 ^ (9/5) − 1 − 9/5) δ ^ (9/5) ≈ 0.682 δ ^ (9/5)`, so no improvement is available by trimming the
far end.  The error is `O(δ ^ (9/5))` rather than `O(δ⁴)`, which is why these leaves are the ones
that force the certificate's subdivision depth.

## Main results

* `nineFifthsAffine`: the tangent line of `|·| ^ (9/5)` at `c`, written — as in
  `CenteredMaximal.Fractional.nineFifthsTaylor` — with the sign of `c` carried by the factor `c`
  against a power of `|c|` rather than by a case split.
* `nineFifthsAffine_of_pos`, `nineFifthsAffine_of_neg`: the same line with the sign of `c` resolved,
  in the two exponents `9/5` and `4/5` of the enclosure table.
* `rpow_nine_fifths_affine_of_pos`: the model on `[0, 2δ]`.
* `abs_rpow_nine_fifths_affine`: **the model a touching leaf uses**, for either sign of `c`.
* `nineFifthsAffine_eq_sum`: the model as a centred *linear* polynomial in the tabulated powers,
  the form a model fold consumes.  It is `nineFifthsTaylor_eq_sum` with the range cut from `4`
  to `2`.
-/

@[expose] public section

noncomputable section

open Set

namespace CenteredMaximal.Fractional

/-! ### The affine part of the cubic model -/

/-- **The tangent line of `x ↦ |x| ^ (9/5)` at `c ≠ 0`**, in the increment `x - c`.  This is the
affine part of `CenteredMaximal.Fractional.nineFifthsTaylor`, and the sign of `c` is carried by the
factor `c` against a power of `|c|`, so that the line is a single rational expression in enclosed
powers of `|c|`. -/
def nineFifthsAffine (c x : ℝ) : ℝ :=
  |c| ^ (9 / 5 : ℝ) + 9 / 5 * c * |c| ^ (-(1 / 5) : ℝ) * (x - c)

/-- `a * a ^ q = a ^ (1 + q)` for `a > 0`, the one power identity the sign bookkeeping needs. -/
private theorem rpow_self_mul_aux {a : ℝ} (ha : 0 < a) (q : ℝ) : a * a ^ q = a ^ (1 + q) := by
  rw [Real.rpow_add ha, Real.rpow_one]

/-- **The model at a positive centre**, in the two exponents `9/5` and `4/5` of the enclosure
table. -/
theorem nineFifthsAffine_of_pos {c : ℝ} (hc : 0 < c) (x : ℝ) :
    nineFifthsAffine c x = c ^ (9 / 5 : ℝ) + 9 / 5 * c ^ (4 / 5 : ℝ) * (x - c) := by
  have h1 : c * c ^ (-(1 / 5) : ℝ) = c ^ (4 / 5 : ℝ) := by
    rw [rpow_self_mul_aux hc]
    norm_num
  rw [nineFifthsAffine, abs_of_pos hc]
  linear_combination (9 / 5 * (x - c)) * h1

/-- **The model at a negative centre**: the odd coefficient flips sign. -/
theorem nineFifthsAffine_of_neg {c : ℝ} (hc : c < 0) (x : ℝ) :
    nineFifthsAffine c x = |c| ^ (9 / 5 : ℝ) - 9 / 5 * |c| ^ (4 / 5 : ℝ) * (x - c) := by
  have habs : |c| = -c := abs_of_neg hc
  have ha : 0 < |c| := abs_pos.2 hc.ne
  have e1 : |c| * |c| ^ (-(1 / 5) : ℝ) = |c| ^ (4 / 5 : ℝ) := by
    rw [rpow_self_mul_aux ha]
    norm_num
  have h1 : c * |c| ^ (-(1 / 5) : ℝ) = -|c| ^ (4 / 5 : ℝ) := by
    linear_combination (|c| ^ (-(1 / 5) : ℝ)) * habs - e1
  rw [nineFifthsAffine]
  linear_combination (9 / 5 * (x - c)) * h1

/-- The line is invariant under reflecting both the centre and the point, which is what reduces a
negative centre to a positive one. -/
theorem nineFifthsAffine_neg (c x : ℝ) : nineFifthsAffine (-c) (-x) = nineFifthsAffine c x := by
  rw [nineFifthsAffine, nineFifthsAffine, abs_neg]
  ring

/-- At the centre the line reproduces the function. -/
theorem nineFifthsAffine_self (c : ℝ) : nineFifthsAffine c c = |c| ^ (9 / 5 : ℝ) := by
  rw [nineFifthsAffine]
  ring

/-! ### The numerical fact behind the constant -/

/-- `2 ^ (4/5) ≤ 9/5`, because `2 ⁴ = 16 ≤ (9/5) ⁵ = 59049/3125`.  Raising an `rpow` to the fifth
natural power clears the fractional exponent, after which the comparison is rational. -/
private theorem two_rpow_four_fifths_le : (2 : ℝ) ^ (4 / 5 : ℝ) ≤ 9 / 5 := by
  have h5 : ((2 : ℝ) ^ (4 / 5 : ℝ)) ^ (5 : ℕ) = 16 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (4 / 5 : ℝ)) 5, ← Real.rpow_mul (by norm_num)]
    rw [show (4 / 5 : ℝ) * (5 : ℕ) = ((4 : ℕ) : ℝ) from by push_cast; ring, Real.rpow_natCast]
    norm_num
  by_contra hcon
  have hgt : (9 / 5 : ℝ) < (2 : ℝ) ^ (4 / 5 : ℝ) := not_le.1 hcon
  have hlt : (9 / 5 : ℝ) ^ (5 : ℕ) < ((2 : ℝ) ^ (4 / 5 : ℝ)) ^ (5 : ℕ) := by gcongr
  rw [h5] at hlt
  norm_num at hlt

/-! ### The model on the interval `[0, 2δ]` -/

/-- **The affine model of `t ↦ t ^ (9/5)` on `[0, 2δ]`**, the interval whose left endpoint is the
origin.  The lower bound is convexity — the tangent line lies below the graph — and the upper bound
is the inequality `t ^ (9/5) ≤ (9/5) δ ^ (4/5) t`, which is `t ^ (4/5) ≤ 2 ^ (4/5) δ ^ (4/5)`
multiplied by `t`.  Equality holds at `t = 0`. -/
theorem rpow_nine_fifths_affine_of_pos {δ x : ℝ} (hδ : 0 < δ) (hx : |x - δ| ≤ δ) :
    |x ^ (9 / 5 : ℝ) - nineFifthsAffine δ x| ≤ 4 / 5 * δ ^ (9 / 5 : ℝ) := by
  obtain ⟨h1, h2⟩ := abs_le.1 hx
  have hx0 : 0 ≤ x := by linarith
  have hx2 : x ≤ 2 * δ := by linarith
  have hnn : (0 : ℝ) ≤ δ ^ (9 / 5 : ℝ) := (Real.rpow_pos_of_pos hδ _).le
  have hA : δ * δ ^ (-(1 / 5) : ℝ) = δ ^ (4 / 5 : ℝ) := by
    rw [rpow_self_mul_aux hδ]
    norm_num
  have hB : δ * δ ^ (4 / 5 : ℝ) = δ ^ (9 / 5 : ℝ) := by
    rw [rpow_self_mul_aux hδ]
    norm_num
  -- the tangent line, with the constant term made explicit
  have hL : nineFifthsAffine δ x = -(4 / 5) * δ ^ (9 / 5 : ℝ) + 9 / 5 * δ ^ (4 / 5 : ℝ) * x := by
    rw [nineFifthsAffine, abs_of_pos hδ]
    linear_combination (9 / 5 * (x - δ)) * hA - 9 / 5 * hB
  -- the derivative of `t ^ (9/5)` at the centre
  have hder : HasDerivAt (fun t : ℝ => t ^ (9 / 5 : ℝ)) (9 / 5 * δ ^ (4 / 5 : ℝ)) δ := by
    have h := Real.hasDerivAt_rpow_const (x := δ) (p := (9 / 5 : ℝ)) (Or.inl hδ.ne')
    rwa [show (9 / 5 : ℝ) - 1 = 4 / 5 from by norm_num] at h
  -- lower bound: a convex function lies above its tangent line
  have hlow : -(4 / 5) * δ ^ (9 / 5 : ℝ) + 9 / 5 * δ ^ (4 / 5 : ℝ) * x ≤ x ^ (9 / 5 : ℝ) := by
    have h := tangent_le_of_convexOn (_root_.convexOn_rpow (p := (9 / 5 : ℝ)) (by norm_num))
      (mem_Ici.2 hδ.le) (mem_Ici.2 hx0) hder
    calc -(4 / 5) * δ ^ (9 / 5 : ℝ) + 9 / 5 * δ ^ (4 / 5 : ℝ) * x
        = δ ^ (9 / 5 : ℝ) + 9 / 5 * δ ^ (4 / 5 : ℝ) * (x - δ) := by linear_combination 9 / 5 * hB
      _ ≤ x ^ (9 / 5 : ℝ) := h
  -- upper bound: `x ^ (9/5) = x ^ (4/5) · x`, and `x ^ (4/5) ≤ 2 ^ (4/5) δ ^ (4/5)`, which
  -- `two_rpow_four_fifths_le` relaxes to `(9/5) δ ^ (4/5)`
  have hupp : x ^ (9 / 5 : ℝ) ≤ 9 / 5 * δ ^ (4 / 5 : ℝ) * x := by
    rcases eq_or_lt_of_le hx0 with h0 | hxpos
    · rw [← h0, Real.zero_rpow (by norm_num)]
      simp
    · have hx95 : x ^ (9 / 5 : ℝ) = x ^ (4 / 5 : ℝ) * x := by
        rw [show (9 / 5 : ℝ) = 4 / 5 + 1 from by norm_num, Real.rpow_add hxpos, Real.rpow_one]
      have h45 : x ^ (4 / 5 : ℝ) ≤ 9 / 5 * δ ^ (4 / 5 : ℝ) := by
        calc x ^ (4 / 5 : ℝ) ≤ (2 * δ) ^ (4 / 5 : ℝ) := Real.rpow_le_rpow hx0 hx2 (by norm_num)
          _ = 2 ^ (4 / 5 : ℝ) * δ ^ (4 / 5 : ℝ) := Real.mul_rpow (by norm_num) hδ.le
          _ ≤ 9 / 5 * δ ^ (4 / 5 : ℝ) := by gcongr; exact two_rpow_four_fifths_le
      rw [hx95]
      exact mul_le_mul_of_nonneg_right h45 hx0
  rw [abs_le, hL]
  constructor <;> linarith

/-! ### The model at either sign of the centre -/

/-- **The affine model of `x ↦ |x| ^ (9/5)` on an interval whose closure touches the origin**, the
form a certificate leaf consumes when the cubic model of
`CenteredMaximal.Fractional.abs_rpow_nine_fifths_taylor` is unavailable.  The hypothesis
`|c| = δ > 0` says the interval is exactly `[0, 2δ]` or `[-2δ, 0]`; in particular it rules out
`c = 0`.  A negative centre reduces to a positive one by the reflection `nineFifthsAffine_neg`,
under which the hypotheses and the bound are invariant.

The constant `4/5` cannot be lowered: the error equals `(4/5) δ ^ (9/5)` at the endpoint `x = 0`. -/
theorem abs_rpow_nine_fifths_affine {c δ x : ℝ} (hδ : 0 < δ) (hc : |c| = δ) (hx : |x - c| ≤ δ) :
    |(|x| ^ (9 / 5 : ℝ)) - nineFifthsAffine c x| ≤ 4 / 5 * δ ^ (9 / 5 : ℝ) := by
  obtain ⟨hlo, hhi⟩ := abs_le.1 hx
  rcases lt_trichotomy c 0 with hneg | hzero | hpos
  · have hcδ : -c = δ := by rw [← abs_of_neg hneg, hc]
    have hxneg : x ≤ 0 := by linarith
    have hx' : |(-x) - δ| ≤ δ := by
      rw [show -x - δ = -(x - c) from by linarith]
      rwa [abs_neg]
    have heq : nineFifthsAffine δ (-x) = nineFifthsAffine c x := by
      rw [← hcδ, nineFifthsAffine_neg]
    rw [abs_of_nonpos hxneg, ← heq]
    exact rpow_nine_fifths_affine_of_pos hδ hx'
  · rw [hzero, abs_zero] at hc
    linarith
  · have hcδ : c = δ := by rw [← abs_of_pos hpos, hc]
    have hx0 : 0 ≤ x := by linarith
    have hx' : |x - δ| ≤ δ := by rwa [hcδ] at hx
    rw [abs_of_nonneg hx0, hcδ]
    exact rpow_nine_fifths_affine_of_pos hδ hx'

/-! ### The model as a centred linear polynomial -/

/-- **The affine model as a centred linear polynomial in the tabulated powers.**  This is
`nineFifthsAffine_of_pos` and `nineFifthsAffine_of_neg` written as a single sum, in exactly the
shape of `CenteredMaximal.Fractional.nineFifthsTaylor_eq_sum` — same `taylorExp`, same
`taylorRhoQ` — but over `Finset.range 2` instead of `Finset.range 4`, so that a model fold can
consume a touching leaf and a separated leaf through the same code path, with only the degree
bound changing. -/
theorem nineFifthsAffine_eq_sum {c : ℝ} {m : ℚ} (hm : (m : ℝ) = |c|) {pos : Bool}
    (hpos : if pos then 0 < c else c < 0) (x : ℝ) :
    nineFifthsAffine c x
      = ∑ a ∈ Finset.range 2, ((taylorRhoQ pos a : ℚ) : ℝ) *
          (m : ℝ) ^ (((taylorExp a : ℤ) : ℝ) / 5) * (x - c) ^ a := by
  have he0 : (((taylorExp 0 : ℤ) : ℝ) / 5) = 9 / 5 := by rw [taylorExp]; norm_num
  have he1 : (((taylorExp 1 : ℤ) : ℝ) / 5) = 4 / 5 := by rw [taylorExp]; norm_num
  rw [Finset.sum_range_succ, Finset.sum_range_one, he0, he1]
  cases pos with
  | false =>
      have hc : c < 0 := by simpa using hpos
      rw [nineFifthsAffine_of_neg hc, hm]
      simp only [taylorRhoQ, Bool.false_eq_true, if_false]
      push_cast
      ring
  | true =>
      have hc : 0 < c := by simpa using hpos
      have habs : (m : ℝ) = c := by rw [hm, abs_of_pos hc]
      rw [nineFifthsAffine_of_pos hc, habs]
      simp only [taylorRhoQ, if_true]
      push_cast
      ring

end CenteredMaximal.Fractional

end

end
