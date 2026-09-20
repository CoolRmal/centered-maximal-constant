/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pochhammer

/-!
# The cubic Taylor model of `|x| ^ (9/5)`

`CenteredMaximal.Fractional.jumpGen1_bspline` expresses the fractional generator of the cardinal
cubic B-spline at order `α = 6/5` through the single elementary function

`F x = |x| ^ (3 - α) = |x| ^ (9/5)`.

A certificate leaf needs `F` on a dyadic interval `[c - δ, c + δ]` as a *polynomial plus an
explicit error*, because only then can the generator of the whole spline sum be collected into one
bivariate polynomial whose coefficients are rational multiples of enclosed fifth roots.  This file
supplies that model, at the sharp Lagrange constant.

## The constant

`d⁴/dx⁴ x ^ (9/5) = (9/5)(4/5)(-1/5)(-6/5) x ^ (-11/5) = (216/625) x ^ (-11/5)`, and
`(216/625) / 4! = 9/625`, whence the remainder bound

`|F x - P₃(x)| ≤ (9/625) δ⁴ (|c| - δ) ^ (-11/5)`,      `|x - c| ≤ δ < |c|`.

The hypothesis `δ < |c|` is what keeps the interval away from `0`, where `F` is not four times
differentiable.  The certificate's leaves that *touch* `0` use an affine model with an `O(δ^{9/5})`
remainder instead; that case is not in this file.

## Main results

* `iteratedDeriv_rpow`: `iteratedDeriv n (· ^ p) x = (descPochhammer ℝ n).eval p * x ^ (p - n)`,
  a restatement of `Real.iter_deriv_rpow_const` through `iteratedDeriv_eq_iterate`.
* `nineFifthsTaylor`: the cubic Taylor polynomial of `|·| ^ (9/5)` at `c`, in the increment `x - c`.
* `nineFifthsTaylor_of_pos`, `nineFifthsTaylor_of_neg`: the same polynomial with the sign of `c`
  resolved, in terms of the four exponents `9/5`, `4/5`, `-1/5`, `-6/5` that the enclosure table
  carries.
* `rpow_nine_fifths_taylor_of_pos`: the model on an interval of the positive half-line.
* `abs_rpow_nine_fifths_taylor`: **the model a leaf uses**, for either sign of `c`.

## The fourth difference does *not* make the remainders cancel

`jumpGen1_bspline` sums five values of `F` against the fourth-difference weights
`(-1)^q C(4,q)`, and `CenteredMaximal.Fractional.sum_alt_choose_cubic` says that a *single* cubic is
annihilated by those weights.  It is tempting to conclude that the five cubic Taylor polynomials
cancel and only the five remainders survive.  **They do not cancel.**  The five expansion centres
`c + 2 - q` are five *different* points, so the five Taylor polynomials have five different
coefficient vectors, and their weighted sum reproduces the fourth difference itself rather than
zero — numerically, at `c = 3.3`, `x = c + 0.01` the weighted sum of the five cubics is
`2.797787e-02` and the exact fourth difference is `2.797787e-02`, agreeing to the size of the
remainder instead of cancelling.  What makes the leaf bound small is not cancellation but that each
remainder is `O(δ⁴)` with `δ ≤ 1/32` at the depths the certificate reaches.
-/

@[expose] public section

noncomputable section

open Set

namespace CenteredMaximal.Fractional

/-! ### Iterated derivatives of a real power -/

/-- **Every iterated derivative of `x ↦ x ^ p` is again a power**, with the descending Pochhammer
symbol as coefficient.  Valid at every real `x`, including `0`, because `Real.deriv_rpow_const`
is unconditional. -/
theorem iteratedDeriv_rpow (p : ℝ) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun t : ℝ => t ^ p) x = (descPochhammer ℝ n).eval p * x ^ (p - n) := by
  rw [iteratedDeriv_eq_iterate, Real.iter_deriv_rpow_const]

/-- The four Pochhammer values the cubic model of `|·| ^ (9/5)` consumes, and the fifth one that
bounds its remainder. -/
private theorem descPochhammer_eval_nineFifths :
    (descPochhammer ℝ 0).eval (9 / 5 : ℝ) = 1 ∧ (descPochhammer ℝ 1).eval (9 / 5 : ℝ) = 9 / 5 ∧
      (descPochhammer ℝ 2).eval (9 / 5 : ℝ) = 36 / 25 ∧
      (descPochhammer ℝ 3).eval (9 / 5 : ℝ) = -36 / 125 ∧
      (descPochhammer ℝ 4).eval (9 / 5 : ℝ) = 216 / 625 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [descPochhammer_eval_eq_prod_range, Finset.prod_range_succ,
      Finset.prod_range_zero] <;> norm_num

/-! ### The cubic Taylor polynomial -/

/-- **The cubic Taylor polynomial of `x ↦ |x| ^ (9/5)` at `c ≠ 0`**, in the increment `x - c`.  The
two odd coefficients carry the sign of `c`; that sign is written as the factor `c` against a power
of `|c|` rather than as a case split, so that the polynomial is a single rational expression in
enclosed powers of `|c|`. -/
def nineFifthsTaylor (c x : ℝ) : ℝ :=
  |c| ^ (9 / 5 : ℝ) + 9 / 5 * c * |c| ^ (-(1 / 5) : ℝ) * (x - c)
    + 18 / 25 * |c| ^ (-(1 / 5) : ℝ) * (x - c) ^ 2
    - 6 / 125 * c * |c| ^ (-(11 / 5) : ℝ) * (x - c) ^ 3

/-- `a * a ^ q = a ^ (1 + q)` for `a > 0`, the one power identity the sign bookkeeping needs. -/
private theorem rpow_self_mul {a : ℝ} (ha : 0 < a) (q : ℝ) : a * a ^ q = a ^ (1 + q) := by
  rw [Real.rpow_add ha, Real.rpow_one]

/-- **The model at a positive centre**, in the four exponents `9/5`, `4/5`, `-1/5`, `-6/5` of the
enclosure table. -/
theorem nineFifthsTaylor_of_pos {c : ℝ} (hc : 0 < c) (x : ℝ) :
    nineFifthsTaylor c x = c ^ (9 / 5 : ℝ) + 9 / 5 * c ^ (4 / 5 : ℝ) * (x - c)
      + 18 / 25 * c ^ (-(1 / 5) : ℝ) * (x - c) ^ 2
      - 6 / 125 * c ^ (-(6 / 5) : ℝ) * (x - c) ^ 3 := by
  have h1 : c * c ^ (-(1 / 5) : ℝ) = c ^ (4 / 5 : ℝ) := by
    rw [rpow_self_mul hc]
    norm_num
  have h2 : c * c ^ (-(11 / 5) : ℝ) = c ^ (-(6 / 5) : ℝ) := by
    rw [rpow_self_mul hc]
    norm_num
  rw [nineFifthsTaylor, abs_of_pos hc]
  linear_combination (9 / 5 * (x - c)) * h1 - (6 / 125 * (x - c) ^ 3) * h2

/-- **The model at a negative centre**: the two odd coefficients flip sign. -/
theorem nineFifthsTaylor_of_neg {c : ℝ} (hc : c < 0) (x : ℝ) :
    nineFifthsTaylor c x = |c| ^ (9 / 5 : ℝ) - 9 / 5 * |c| ^ (4 / 5 : ℝ) * (x - c)
      + 18 / 25 * |c| ^ (-(1 / 5) : ℝ) * (x - c) ^ 2
      + 6 / 125 * |c| ^ (-(6 / 5) : ℝ) * (x - c) ^ 3 := by
  have habs : |c| = -c := abs_of_neg hc
  have ha : 0 < |c| := abs_pos.2 hc.ne
  have e1 : |c| * |c| ^ (-(1 / 5) : ℝ) = |c| ^ (4 / 5 : ℝ) := by
    rw [rpow_self_mul ha]
    norm_num
  have e2 : |c| * |c| ^ (-(11 / 5) : ℝ) = |c| ^ (-(6 / 5) : ℝ) := by
    rw [rpow_self_mul ha]
    norm_num
  have h1 : c * |c| ^ (-(1 / 5) : ℝ) = -|c| ^ (4 / 5 : ℝ) := by
    linear_combination (|c| ^ (-(1 / 5) : ℝ)) * habs - e1
  have h2 : c * |c| ^ (-(11 / 5) : ℝ) = -|c| ^ (-(6 / 5) : ℝ) := by
    linear_combination (|c| ^ (-(11 / 5) : ℝ)) * habs - e2
  rw [nineFifthsTaylor]
  linear_combination (9 / 5 * (x - c)) * h1 - (6 / 125 * (x - c) ^ 3) * h2

/-- The model is invariant under reflecting both the centre and the point, which is what reduces a
negative centre to a positive one. -/
theorem nineFifthsTaylor_neg (c x : ℝ) : nineFifthsTaylor (-c) (-x) = nineFifthsTaylor c x := by
  rw [nineFifthsTaylor, nineFifthsTaylor, abs_neg]
  ring

/-- At the centre the model reproduces the function. -/
theorem nineFifthsTaylor_self (c : ℝ) : nineFifthsTaylor c c = |c| ^ (9 / 5 : ℝ) := by
  rw [nineFifthsTaylor]
  ring

/-! ### The Taylor polynomial of Mathlib is this polynomial -/

/-- On an interval of the positive half-line the third-order Taylor polynomial of `t ↦ t ^ (9/5)`
computed by `taylorWithinEval` is `nineFifthsTaylor`. -/
private theorem taylorWithinEval_nine_fifths {c x : ℝ} (hc : 0 < c) (hne : c ≠ x) :
    taylorWithinEval (fun t : ℝ => t ^ (9 / 5 : ℝ)) 3 (uIcc c x) c x = nineFifthsTaylor c x := by
  obtain ⟨p0, p1, p2, p3, -⟩ := descPochhammer_eval_nineFifths
  have hu : UniqueDiffOn ℝ (uIcc c x) := uniqueDiffOn_Icc (inf_lt_sup.2 hne)
  have hmem : c ∈ uIcc c x := left_mem_uIcc
  have hk : ∀ k : ℕ, iteratedDerivWithin k (fun t : ℝ => t ^ (9 / 5 : ℝ)) (uIcc c x) c
      = (descPochhammer ℝ k).eval (9 / 5 : ℝ) * c ^ ((9 / 5 : ℝ) - k) := by
    intro k
    rw [iteratedDerivWithin_eq_iteratedDeriv hu (Real.contDiffAt_rpow_const_of_ne hc.ne') hmem,
      iteratedDeriv_rpow]
  rw [taylor_within_apply]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, hk, smul_eq_mul, Nat.factorial]
  rw [p0, p1, p2, p3, nineFifthsTaylor_of_pos hc]
  push_cast
  rw [show (9 : ℝ) / 5 - 0 = 9 / 5 from by ring, show (9 : ℝ) / 5 - 1 = 4 / 5 from by ring,
    show (9 : ℝ) / 5 - 2 = -(1 / 5) from by ring, show (9 : ℝ) / 5 - 3 = -(6 / 5) from by ring]
  ring

/-! ### The model on the positive half-line -/

/-- **The cubic Taylor model of `t ↦ t ^ (9/5)` on an interval of the positive half-line.**  The
Lagrange remainder of `taylor_mean_remainder_lagrange_iteratedDeriv` at order `3` is
`(216/625) x' ^ (-11/5) (x - c) ^ 4 / 4!` for an interior point `x'`, and both factors are
monotone: `x' ≥ c - δ` and `|x - c| ≤ δ`. -/
theorem rpow_nine_fifths_taylor_of_pos {c δ x : ℝ} (hδ : 0 < δ) (hc : δ < c) (hx : |x - c| ≤ δ) :
    |x ^ (9 / 5 : ℝ) - nineFifthsTaylor c x| ≤ 9 / 625 * δ ^ 4 * (c - δ) ^ (-(11 / 5) : ℝ) := by
  obtain ⟨-, -, -, -, p4⟩ := descPochhammer_eval_nineFifths
  have hc0 : 0 < c := lt_trans hδ hc
  have hlo : 0 < c - δ := by linarith
  have hbnd := abs_le.1 hx
  have hxlo : c - δ ≤ x := by linarith [hbnd.1]
  have hxhi : x ≤ c + δ := by linarith [hbnd.2]
  have hpow : (0 : ℝ) < (c - δ) ^ (-(11 / 5) : ℝ) := Real.rpow_pos_of_pos hlo _
  rcases eq_or_ne c x with rfl | hne
  · rw [nineFifthsTaylor_self, abs_of_pos hc0, sub_self, abs_zero]
    positivity
  -- every point of the interval is at least `c - δ`, hence positive
  have hmem : ∀ y ∈ uIcc c x, c - δ ≤ y := by
    intro y hy
    rcases mem_uIcc.1 hy with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
  have hposy : ∀ y ∈ uIcc c x, 0 < y := fun y hy => lt_of_lt_of_le hlo (hmem y hy)
  have hcd : ContDiffOn ℝ (3 + 1 : ℕ) (fun t : ℝ => t ^ (9 / 5 : ℝ)) (uIcc c x) := fun y hy =>
    (Real.contDiffAt_rpow_const_of_ne (hposy y hy).ne').contDiffWithinAt
  obtain ⟨x', hx', hrem⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 3) hne hcd
  -- the interior point is also at least `c - δ`
  have hmin : c - δ ≤ c ⊓ x := le_inf (by linarith) hxlo
  have hx'pos : 0 < x' := lt_of_lt_of_le hlo (le_of_lt (lt_of_le_of_lt hmin hx'.1))
  have hx'lo : c - δ ≤ x' := le_of_lt (lt_of_le_of_lt hmin hx'.1)
  -- the fourth iterated derivative at the interior point
  have hder : iteratedDeriv 4 (fun t : ℝ => t ^ (9 / 5 : ℝ)) x'
      = 216 / 625 * x' ^ (-(11 / 5) : ℝ) := by
    rw [iteratedDeriv_rpow, p4]
    norm_num
  rw [taylorWithinEval_nine_fifths hc0 hne, hder] at hrem
  have hval : x ^ (9 / 5 : ℝ) - nineFifthsTaylor c x
      = 9 / 625 * x' ^ (-(11 / 5) : ℝ) * (x - c) ^ 4 := by
    rw [hrem]
    norm_num [Nat.factorial]
    ring
  have hrp : x' ^ (-(11 / 5) : ℝ) ≤ (c - δ) ^ (-(11 / 5) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hlo hx'lo (by norm_num)
  have h4 : (x - c) ^ 4 ≤ δ ^ 4 := by
    calc (x - c) ^ 4 = |x - c| ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      _ ≤ δ ^ 4 := by gcongr
  rw [hval, abs_of_nonneg (by positivity)]
  calc 9 / 625 * x' ^ (-(11 / 5) : ℝ) * (x - c) ^ 4
      ≤ 9 / 625 * (c - δ) ^ (-(11 / 5) : ℝ) * δ ^ 4 := by gcongr
    _ = 9 / 625 * δ ^ 4 * (c - δ) ^ (-(11 / 5) : ℝ) := by ring

/-! ### The model at either sign of the centre -/

/-- **The cubic Taylor model of `x ↦ |x| ^ (9/5)` on a dyadic interval away from the origin**, the
form a certificate leaf consumes.  A negative centre reduces to a positive one by the reflection
`nineFifthsTaylor_neg`, under which the hypotheses and the bound are invariant. -/
theorem abs_rpow_nine_fifths_taylor {c δ x : ℝ} (hδ : 0 < δ) (hc : δ < |c|) (hx : |x - c| ≤ δ) :
    |(|x| ^ (9 / 5 : ℝ)) - nineFifthsTaylor c x|
      ≤ 9 / 625 * δ ^ 4 * (|c| - δ) ^ (-(11 / 5) : ℝ) := by
  rcases lt_trichotomy c 0 with hneg | hzero | hpos
  · have habs : |c| = -c := abs_of_neg hneg
    have hbnd := abs_le.1 hx
    have hxneg : x < 0 := by
      rw [habs] at hc
      linarith [hbnd.2]
    have hx' : |(-x) - (-c)| ≤ δ := by rwa [show -x - -c = -(x - c) from by ring, abs_neg]
    have h := rpow_nine_fifths_taylor_of_pos (c := -c) (δ := δ) (x := -x) hδ
      (by rwa [habs] at hc) hx'
    rw [nineFifthsTaylor_neg, show -x = |x| from (abs_of_neg hxneg).symm,
      show -c = |c| from habs.symm] at h
    exact h
  · rw [hzero, abs_zero] at hc
    linarith
  · have habs : |c| = c := abs_of_pos hpos
    have hbnd := abs_le.1 hx
    have hxpos : 0 < x := by
      rw [habs] at hc
      linarith [hbnd.1]
    have h := rpow_nine_fifths_taylor_of_pos (c := c) (δ := δ) (x := x) hδ
      (by rwa [habs] at hc) hx
    rwa [show |x| = x from abs_of_pos hxpos, habs]

end CenteredMaximal.Fractional

end

end
