/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.BaseMoment
public import CenteredMaximal.Fractional.KernelPositivity
public import CenteredMaximal.Fractional.MajorBase
public import CenteredMaximal.Fractional.SplineTaylor

/-!
# The pointwise majorant of the comparison density

The generator density `fracDensity = jumpGen (6/5) fracKernel` of the `α = 6/5` comparison kernel is
majorised here by

`|fracDensity z| ≤ A (r^{-12/5} + r^{-11/5} + r^{-11/5} m^{-1/5} + |r − 7/4|^{-1/5})`,
`r = diamondNorm z`,  `m = min(|z₀|, |z₁|)`,

off the two coordinate axes and off the support boundary `r = 7/4` — that is, almost everywhere.
`CenteredMaximal.Fractional.DensityMoment` turns this into the weighted `L²` moment the `α = 6/5`
assembly consumes.

## The spline half

By `CenteredMaximal.Fractional.jumpGen_fracKernel_sub_base` the generator of the spline part of the
kernel is a finite sum of products `jumpGen1 (6/5) β (16 z₀ − i) · β (16 z₁ − j)` and their
transposes. Two facts about the one-dimensional generator `J = jumpGen1 (6/5) β` are needed, and
both come from the closed form `J x = (625/108) ∑_q (−1)^q C(4,q) |x + 2 − q|^{9/5}`:

* `abs_jumpGen1_bspline_le`: `|J| ≤ 20000` everywhere;
* `abs_jumpGen1_bspline_le_rpow`: `|J x| ≤ 20000 |x|^{-11/5}` for `|x| ≥ 4`.

The second is the *fourth difference* of `|·|^{9/5}`: expanding all five values at the common centre
`x` kills the cubic part (`sum_alt_choose_cubic` applied to the Taylor polynomial
`nineFifthsTaylor x`), and what is left is the sum of the five Lagrange remainders of
`abs_rpow_nine_fifths_taylor`, each `O(δ⁴ (|x| − δ)^{-11/5})` with `δ = 2`. Since each spline cell
carries a factor supported in a strip, the two bounds combine into one cell estimate
`|J (16 z₀ − i) β (16 z₁ − j)| ≤ cellBound i j · r^{-11/5}`, and the cell sum is finite because the
cell set is.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### The one-dimensional spline generator -/

/-- **The fractional generator of the cardinal cubic B-spline at order `6/5`.** The prefactor
`2 / (−(α(1−α)(2−α)(3−α)))` of `jumpGen1_bspline` is `625/108` and the exponent `3 − α` is `9/5`. -/
private theorem jumpGen1_bspline_six_fifths (x : ℝ) :
    jumpGen1 (6 / 5) bspline x
      = 625 / 108 * ∑ q ∈ Finset.range 5,
          (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - q| ^ (9 / 5 : ℝ) := by
  rw [jumpGen1_bspline (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- The five binomial coefficients of the fourth difference are at most `6`. -/
private theorem choose_four_le {q : ℕ} (hq : q ∈ Finset.range 5) : (Nat.choose 4 q : ℝ) ≤ 6 := by
  have h : q < 5 := Finset.mem_range.1 hq
  interval_cases q <;> norm_num [Nat.choose]

/-- **The near-field bound on the spline generator.** For `|x| ≤ 4` all five arguments of the
closed form are at most `6` in absolute value, and `6^{9/5} ≤ 36`. -/
private theorem abs_jumpGen1_bspline_le_near {x : ℝ} (hx : |x| ≤ 4) :
    |jumpGen1 (6 / 5) bspline x| ≤ 20000 := by
  have hterm : ∀ q ∈ Finset.range 5,
      |(-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - q| ^ (9 / 5 : ℝ)| ≤ 6 * 36 := by
    intro q hq
    have hq4 : (q : ℝ) ≤ 4 := by
      have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
      exact_mod_cast this
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hbnd : |x + 2 - (q : ℝ)| ≤ 6 := by
      have h1 := abs_le.1 hx
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2]
    have hpow : |x + 2 - (q : ℝ)| ^ (9 / 5 : ℝ) ≤ 36 := by
      calc |x + 2 - (q : ℝ)| ^ (9 / 5 : ℝ) ≤ (6 : ℝ) ^ (9 / 5 : ℝ) :=
            Real.rpow_le_rpow (abs_nonneg _) hbnd (by norm_num)
        _ ≤ (6 : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 36 := by
            rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
            norm_num
    have hnn : (0 : ℝ) ≤ |x + 2 - (q : ℝ)| ^ (9 / 5 : ℝ) := Real.rpow_nonneg (abs_nonneg _) _
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast,
      abs_of_nonneg hnn]
    exact mul_le_mul (choose_four_le hq) hpow hnn (by norm_num)
  rw [jumpGen1_bspline_six_fifths, abs_mul, show |(625 : ℝ) / 108| = 625 / 108 from
    abs_of_pos (by norm_num)]
  have hsum : |∑ q ∈ Finset.range 5,
      (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - q| ^ (9 / 5 : ℝ)| ≤ 5 * (6 * 36) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ q ∈ Finset.range 5, |(-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - q| ^ (9 / 5 : ℝ)|
        ≤ ∑ _q ∈ Finset.range 5, (6 : ℝ) * 36 := Finset.sum_le_sum hterm
      _ = 5 * (6 * 36) := by simp
  nlinarith [hsum]

/-! ### The fourth difference kills the Taylor polynomial -/

/-- **The fourth difference of the cubic Taylor model vanishes.** `nineFifthsTaylor c` is a cubic in
its second argument, and the alternating binomial weights annihilate every cubic. -/
private theorem sum_alt_nineFifthsTaylor (c x : ℝ) :
    ∑ q ∈ Finset.range 5,
      (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * nineFifthsTaylor c (x + 2 - q) = 0 := by
  set P : ℝ := |c| ^ (9 / 5 : ℝ) with hP
  set Q : ℝ := 9 / 5 * c * |c| ^ (-(1 / 5) : ℝ) with hQ
  set S : ℝ := 18 / 25 * |c| ^ (-(1 / 5) : ℝ) with hS
  set U : ℝ := -(6 / 125) * c * |c| ^ (-(11 / 5) : ℝ) with hU
  have key : ∀ q ∈ Finset.range 5,
      (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * nineFifthsTaylor c (x + 2 - q)
        = (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
          (U * (x + 2 - q) ^ 3 + (S - 3 * U * c) * (x + 2 - q) ^ 2
            + (Q - 2 * S * c + 3 * U * c ^ 2) * (x + 2 - q)
            + (P - Q * c + S * c ^ 2 - U * c ^ 3)) := by
    intro q _
    rw [nineFifthsTaylor, hP, hQ, hS, hU]
    ring
  rw [Finset.sum_congr rfl key, sum_alt_choose_cubic]

/-! ### The far-field bound on the spline generator -/

/-- **The far-field bound on the spline generator.** For `|x| ≥ 4` the five values of `|·|^{9/5}`
are expanded at the common centre `x` with half-width `δ = 2`; the cubic parts cancel and the five
Lagrange remainders leave `O((|x| − 2)^{-11/5}) = O(|x|^{-11/5})`. -/
private theorem abs_jumpGen1_bspline_le_far {x : ℝ} (hx : 4 ≤ |x|) :
    |jumpGen1 (6 / 5) bspline x| ≤ 20000 * |x| ^ (-(11 / 5) : ℝ) := by
  have hx0 : (0 : ℝ) < |x| := by linarith
  have hδ : (2 : ℝ) < |x| := by linarith
  have hhalf : |x| / 2 ≤ |x| - 2 := by linarith
  have hhalf0 : (0 : ℝ) < |x| / 2 := by linarith
  have hrem : ∀ q ∈ Finset.range 5,
      |(-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
          (|x + 2 - q| ^ (9 / 5 : ℝ) - nineFifthsTaylor x (x + 2 - q))|
        ≤ 6 * (9 / 625 * 2 ^ 4 * (|x| - 2) ^ (-(11 / 5) : ℝ)) := by
    intro q hq
    have hq4 : (q : ℝ) ≤ 4 := by
      have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
      exact_mod_cast this
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hdist : |x + 2 - (q : ℝ) - x| ≤ 2 := by
      rw [show x + 2 - (q : ℝ) - x = 2 - (q : ℝ) from by ring, abs_le]
      constructor <;> linarith
    have hstep := abs_rpow_nine_fifths_taylor (c := x) (δ := 2) (x := x + 2 - q)
      (by norm_num) hδ hdist
    have hnn : (0 : ℝ) ≤ 9 / 625 * 2 ^ 4 * (|x| - 2) ^ (-(11 / 5) : ℝ) := by
      have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ |x| - 2) (-(11 / 5) : ℝ)
      positivity
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    exact mul_le_mul (choose_four_le hq) hstep (abs_nonneg _) (by norm_num)
  have hrw : ∑ q ∈ Finset.range 5,
      (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - q| ^ (9 / 5 : ℝ)
      = ∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
          (|x + 2 - q| ^ (9 / 5 : ℝ) - nineFifthsTaylor x (x + 2 - q)) := by
    have hsplit : ∀ q ∈ Finset.range 5,
        (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
            (|x + 2 - q| ^ (9 / 5 : ℝ) - nineFifthsTaylor x (x + 2 - q))
          = (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - q| ^ (9 / 5 : ℝ)
            - (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * nineFifthsTaylor x (x + 2 - q) :=
      fun q _ => by ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, sum_alt_nineFifthsTaylor, sub_zero]
  have hsum : |∑ q ∈ Finset.range 5,
      (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - q| ^ (9 / 5 : ℝ)|
      ≤ 5 * (6 * (9 / 625 * 2 ^ 4 * (|x| - 2) ^ (-(11 / 5) : ℝ))) := by
    rw [hrw]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ q ∈ Finset.range 5, |(-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
            (|x + 2 - q| ^ (9 / 5 : ℝ) - nineFifthsTaylor x (x + 2 - q))|
        ≤ ∑ _q ∈ Finset.range 5, (6 : ℝ) * (9 / 625 * 2 ^ 4 * (|x| - 2) ^ (-(11 / 5) : ℝ)) :=
          Finset.sum_le_sum hrem
      _ = _ := by simp
  have htail : (|x| - 2) ^ (-(11 / 5) : ℝ) ≤ 8 * |x| ^ (-(11 / 5) : ℝ) := by
    have h1 : (|x| - 2) ^ (-(11 / 5) : ℝ) ≤ (|x| / 2) ^ (-(11 / 5) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos hhalf0 hhalf (by norm_num)
    have h2 : (|x| / 2) ^ (-(11 / 5) : ℝ) = |x| ^ (-(11 / 5) : ℝ) * 2 ^ (11 / 5 : ℝ) := by
      rw [Real.div_rpow hx0.le (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        div_eq_mul_inv, inv_inv]
    have h3 : (2 : ℝ) ^ (11 / 5 : ℝ) ≤ 8 := by
      calc (2 : ℝ) ^ (11 / 5 : ℝ) ≤ (2 : ℝ) ^ (3 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 8 := by
            rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
            norm_num
    have h4 : (0 : ℝ) ≤ |x| ^ (-(11 / 5) : ℝ) := Real.rpow_nonneg hx0.le _
    calc (|x| - 2) ^ (-(11 / 5) : ℝ) ≤ |x| ^ (-(11 / 5) : ℝ) * 2 ^ (11 / 5 : ℝ) := h1.trans_eq h2
      _ ≤ |x| ^ (-(11 / 5) : ℝ) * 8 := mul_le_mul_of_nonneg_left h3 h4
      _ = 8 * |x| ^ (-(11 / 5) : ℝ) := by ring
  have hnn : (0 : ℝ) ≤ |x| ^ (-(11 / 5) : ℝ) := Real.rpow_nonneg hx0.le _
  rw [jumpGen1_bspline_six_fifths, abs_mul, show |(625 : ℝ) / 108| = 625 / 108 from
    abs_of_pos (by norm_num)]
  nlinarith [hsum, htail]

/-- **The two bounds on the spline generator, together.** -/
private theorem abs_jumpGen1_bspline_le (x : ℝ) : |jumpGen1 (6 / 5) bspline x| ≤ 20000 := by
  rcases le_total |x| 4 with hx | hx
  · exact abs_jumpGen1_bspline_le_near hx
  · have hx0 : (0 : ℝ) < |x| := by linarith
    have h1 : |x| ^ (-(11 / 5) : ℝ) ≤ 1 := by
      have := Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1) (by linarith : (1 : ℝ) ≤ |x|)
        (by norm_num : (-(11 / 5) : ℝ) ≤ 0)
      simpa using this
    have h2 := abs_jumpGen1_bspline_le_far hx
    nlinarith

/-! ### The B-spline itself -/

/-- The B-spline is bounded: outside `[−2, 2]` it vanishes, and inside each of the five truncated
cubes is at most `4³ = 64`. -/
private theorem abs_bspline_le (y : ℝ) : |bspline y| ≤ 320 := by
  rcases le_or_gt 2 |y| with hy | hy
  · rw [bspline_eq_zero_of_two_le hy, abs_zero]
    norm_num
  · have hy' := abs_lt.1 hy
    have hterm : ∀ q ∈ Finset.range 5,
        |(-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (y + 2 - q)| ≤ 6 * 64 := by
      intro q hq
      have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      have hcube : |truncCube (y + 2 - (q : ℝ))| ≤ 64 := by
        rw [truncCube, abs_of_nonneg (by positivity : (0 : ℝ) ≤ max (y + 2 - (q : ℝ)) 0 ^ 3)]
        have hmax : max (y + 2 - (q : ℝ)) 0 ≤ 4 := max_le (by linarith [hy'.2]) (by norm_num)
        have hmax0 : (0 : ℝ) ≤ max (y + 2 - (q : ℝ)) 0 := le_max_right _ _
        calc max (y + 2 - (q : ℝ)) 0 ^ 3 ≤ (4 : ℝ) ^ 3 := by gcongr
          _ = 64 := by norm_num
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
      exact mul_le_mul (choose_four_le hq) hcube (abs_nonneg _) (by norm_num)
    have hsum : |∑ q ∈ Finset.range 5,
        (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (y + 2 - q)| ≤ 5 * (6 * 64) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ q ∈ Finset.range 5, |(-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (y + 2 - q)|
          ≤ ∑ _q ∈ Finset.range 5, (6 : ℝ) * 64 := Finset.sum_le_sum hterm
        _ = 5 * (6 * 64) := by simp
    rw [bspline, abs_mul, show |(1 : ℝ) / 6| = 1 / 6 from abs_of_pos (by norm_num)]
    nlinarith [hsum]

/-! ### One cell of the spline generator -/

/-- The radius beyond which one spline cell is in the far field of its own generator: the second
factor confines `|v|` to the strip `|v| < (2 + |j|)/16`, so past this radius the first argument
`16 u − i` is at least `4 (|u| + |v|)` in absolute value. -/
private def cellRadius (i j : ℤ) : ℝ := 1 + (2 + |(j : ℝ)|) / 8 + |(i : ℝ)| / 4

private theorem one_le_cellRadius (i j : ℤ) : 1 ≤ cellRadius i j := by
  have h1 : (0 : ℝ) ≤ (2 + |(j : ℝ)|) / 8 := by positivity
  have h2 : (0 : ℝ) ≤ |(i : ℝ)| / 4 := by positivity
  rw [cellRadius]
  linarith

/-- The constant of one cell of the spline generator. -/
private def cellBound (i j : ℤ) : ℝ :=
  20000 * 320 * cellRadius i j ^ (11 / 5 : ℝ) + 20000 * 320

private theorem cellBound_nonneg (i j : ℤ) : 0 ≤ cellBound i j := by
  have h : (0 : ℝ) ≤ cellRadius i j ^ (11 / 5 : ℝ) :=
    Real.rpow_nonneg (by linarith [one_le_cellRadius i j]) _
  rw [cellBound]
  linarith

/-- **One cell of the spline generator decays like `r^{-11/5}`.** Inside the cell radius the two
factors are simply bounded; outside it the strip support of the second factor forces
`|16 u − i| ≥ 4 (|u| + |v|) ≥ 4`, where the far-field bound applies. -/
private theorem abs_cell_term_le (i j : ℤ) {u v : ℝ} (huv : 0 < |u| + |v|) :
    |jumpGen1 (6 / 5) bspline (16 * u - (i : ℝ)) * bspline (16 * v - (j : ℝ))|
      ≤ cellBound i j * (|u| + |v|) ^ (-(11 / 5) : ℝ) := by
  set r : ℝ := |u| + |v| with hrdef
  set ρ : ℝ := cellRadius i j with hρdef
  have hρ1 : 1 ≤ ρ := one_le_cellRadius i j
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hA : (0 : ℝ) ≤ 20000 * 320 * ρ ^ (11 / 5 : ℝ) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hρ0.le _)
  have hrpow : (0 : ℝ) < r ^ (-(11 / 5) : ℝ) := Real.rpow_pos_of_pos huv _
  have hnear : |jumpGen1 (6 / 5) bspline (16 * u - (i : ℝ)) * bspline (16 * v - (j : ℝ))|
      ≤ 20000 * 320 := by
    rw [abs_mul]
    exact mul_le_mul (abs_jumpGen1_bspline_le _) (abs_bspline_le _) (abs_nonneg _) (by norm_num)
  rcases le_total r ρ with hcase | hcase
  · have hmono : ρ ^ (-(11 / 5) : ℝ) ≤ r ^ (-(11 / 5) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos huv hcase (by norm_num)
    have hcancel : ρ ^ (11 / 5 : ℝ) * ρ ^ (-(11 / 5) : ℝ) = 1 := by
      rw [← Real.rpow_add hρ0]
      norm_num
    calc |jumpGen1 (6 / 5) bspline (16 * u - (i : ℝ)) * bspline (16 * v - (j : ℝ))|
        ≤ 20000 * 320 := hnear
      _ = (20000 * 320 * ρ ^ (11 / 5 : ℝ)) * ρ ^ (-(11 / 5) : ℝ) := by
          rw [mul_assoc, hcancel, mul_one]
      _ ≤ (20000 * 320 * ρ ^ (11 / 5 : ℝ)) * r ^ (-(11 / 5) : ℝ) :=
          mul_le_mul_of_nonneg_left hmono hA
      _ ≤ cellBound i j * r ^ (-(11 / 5) : ℝ) := by
          rw [cellBound]
          have : (0 : ℝ) ≤ 20000 * 320 * r ^ (-(11 / 5) : ℝ) := by positivity
          nlinarith
  · by_cases hB : bspline (16 * v - (j : ℝ)) = 0
    · rw [hB, mul_zero, abs_zero]
      exact mul_nonneg (cellBound_nonneg i j) hrpow.le
    · have hstrip : |16 * v - (j : ℝ)| < 2 := by
        by_contra hcon
        exact hB (bspline_eq_zero_of_two_le (not_lt.1 hcon))
      have hv : 16 * |v| < 2 + |(j : ℝ)| := by
        have h1 : |16 * v| - |(j : ℝ)| ≤ |16 * v - (j : ℝ)| :=
          abs_sub_abs_le_abs_sub (16 * v) ((j : ℝ))
        have h2 : |16 * v| = 16 * |v| := by
          rw [abs_mul, show |(16 : ℝ)| = 16 from abs_of_pos (by norm_num)]
        linarith
      have hcell : 1 + (2 + |(j : ℝ)|) / 8 + |(i : ℝ)| / 4 ≤ r := by
        rw [hρdef, cellRadius] at hcase
        exact hcase
      have hj0 : (0 : ℝ) ≤ (2 + |(j : ℝ)|) / 8 := by positivity
      have hi0 : (0 : ℝ) ≤ |(i : ℝ)| / 4 := by positivity
      have hi : |(i : ℝ)| < 4 * r := by linarith
      have hr1 : 1 ≤ r := by linarith
      have hu : r / 2 < |u| := by
        have h3 : |v| < (2 + |(j : ℝ)|) / 16 := by linarith
        have h4 : (2 + |(j : ℝ)|) / 16 ≤ r / 2 := by linarith
        have h5 : r = |u| + |v| := hrdef
        linarith
      have hfar : 4 * r ≤ |16 * u - (i : ℝ)| := by
        have h1 : |16 * u| - |(i : ℝ)| ≤ |16 * u - (i : ℝ)| :=
          abs_sub_abs_le_abs_sub (16 * u) ((i : ℝ))
        have h2 : |16 * u| = 16 * |u| := by
          rw [abs_mul, show |(16 : ℝ)| = 16 from abs_of_pos (by norm_num)]
        have h3 : 8 * r < 16 * |u| := by linarith
        linarith
      have hfar4 : (4 : ℝ) ≤ |16 * u - (i : ℝ)| := le_trans (by linarith) hfar
      have hJ := abs_jumpGen1_bspline_le_far hfar4
      have hmono : |16 * u - (i : ℝ)| ^ (-(11 / 5) : ℝ) ≤ r ^ (-(11 / 5) : ℝ) := by
        refine Real.rpow_le_rpow_of_nonpos huv ?_ (by norm_num)
        linarith
      calc |jumpGen1 (6 / 5) bspline (16 * u - (i : ℝ)) * bspline (16 * v - (j : ℝ))|
          = |jumpGen1 (6 / 5) bspline (16 * u - (i : ℝ))| * |bspline (16 * v - (j : ℝ))| := abs_mul _ _
        _ ≤ (20000 * |16 * u - (i : ℝ)| ^ (-(11 / 5) : ℝ)) * 320 :=
            mul_le_mul hJ (abs_bspline_le _) (abs_nonneg _) (by positivity)
        _ ≤ (20000 * r ^ (-(11 / 5) : ℝ)) * 320 := by
            have : (0 : ℝ) ≤ (320 : ℝ) := by norm_num
            nlinarith [hmono]
        _ ≤ cellBound i j * r ^ (-(11 / 5) : ℝ) := by
            rw [cellBound]
            nlinarith [hA, hrpow]

/-! ### The spline part of the generator -/

/-- The total constant of the spline part of the generator: a finite sum over the `1201` cells of
the certificate, each with its own cell constant. -/
private def splineC : ℝ :=
  ∑ ij ∈ fracCellFinset, |fracCoeff (fracCellCoeff ij)| * (16 : ℝ) ^ (6 / 5 : ℝ)
    * (cellBound ij.1 ij.2 + cellBound ij.2 ij.1)

/-- **The spline part of the generator decays like `r^{-11/5}`.** Each of the `1201` cells
contributes two products of a one-dimensional generator and a B-spline value, and each such product
is `O(r^{-11/5})` by `abs_cell_term_le`. -/
private theorem abs_jumpGen_spline_le {z : Fin 2 → ℝ} (hz : z ≠ 0) :
    |jumpGen (6 / 5) (fun w => fracKernel w - fracBaseCoeff * truncBase (6 / 5) (7 / 4) w) z|
      ≤ splineC * diamondNorm z ^ (-(11 / 5) : ℝ) := by
  have hr : 0 < diamondNorm z := diamondNorm_pos hz
  have hrd : diamondNorm z = |z 0| + |z 1| := rfl
  have hrpow : (0 : ℝ) < diamondNorm z ^ (-(11 / 5) : ℝ) := Real.rpow_pos_of_pos hr _
  have h16 : (0 : ℝ) < (16 : ℝ) ^ (6 / 5 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  rw [jumpGen_fracKernel_sub_base, splineC, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ij _ => ?_)
  have hA : |jumpGen1 (6 / 5) bspline (16 * z 0 - (ij.1 : ℝ)) * bspline (16 * z 1 - (ij.2 : ℝ))|
      ≤ cellBound ij.1 ij.2 * diamondNorm z ^ (-(11 / 5) : ℝ) := by
    have h := abs_cell_term_le ij.1 ij.2 (u := z 0) (v := z 1) (hrd ▸ hr)
    rwa [← hrd] at h
  have hB : |bspline (16 * z 0 - (ij.1 : ℝ)) * jumpGen1 (6 / 5) bspline (16 * z 1 - (ij.2 : ℝ))|
      ≤ cellBound ij.2 ij.1 * diamondNorm z ^ (-(11 / 5) : ℝ) := by
    have hswap : |z 1| + |z 0| = diamondNorm z := by rw [hrd]; ring
    have h := abs_cell_term_le ij.2 ij.1 (u := z 1) (v := z 0) (hswap ▸ hr)
    rw [hswap] at h
    rwa [mul_comm (bspline (16 * z 0 - (ij.1 : ℝ)))]
  have habs : |fracCoeff (fracCellCoeff ij) *
      ((16 : ℝ) ^ (6 / 5 : ℝ) *
        (jumpGen1 (6 / 5) bspline (16 * z 0 - (ij.1 : ℝ)) * bspline (16 * z 1 - (ij.2 : ℝ))
          + bspline (16 * z 0 - (ij.1 : ℝ)) * jumpGen1 (6 / 5) bspline (16 * z 1 - (ij.2 : ℝ))))|
      = |fracCoeff (fracCellCoeff ij)| * (16 : ℝ) ^ (6 / 5 : ℝ) *
        |jumpGen1 (6 / 5) bspline (16 * z 0 - (ij.1 : ℝ)) * bspline (16 * z 1 - (ij.2 : ℝ))
          + bspline (16 * z 0 - (ij.1 : ℝ)) * jumpGen1 (6 / 5) bspline (16 * z 1 - (ij.2 : ℝ))| := by
    rw [abs_mul, abs_mul, abs_of_pos h16, mul_assoc]
  rw [habs]
  have hsplit := abs_add_le
    (jumpGen1 (6 / 5) bspline (16 * z 0 - (ij.1 : ℝ)) * bspline (16 * z 1 - (ij.2 : ℝ)))
    (bspline (16 * z 0 - (ij.1 : ℝ)) * jumpGen1 (6 / 5) bspline (16 * z 1 - (ij.2 : ℝ)))
  have hc : (0 : ℝ) ≤ |fracCoeff (fracCellCoeff ij)| * (16 : ℝ) ^ (6 / 5 : ℝ) :=
    mul_nonneg (abs_nonneg _) h16.le
  calc |fracCoeff (fracCellCoeff ij)| * (16 : ℝ) ^ (6 / 5 : ℝ) *
        |jumpGen1 (6 / 5) bspline (16 * z 0 - (ij.1 : ℝ)) * bspline (16 * z 1 - (ij.2 : ℝ))
          + bspline (16 * z 0 - (ij.1 : ℝ)) * jumpGen1 (6 / 5) bspline (16 * z 1 - (ij.2 : ℝ))|
      ≤ |fracCoeff (fracCellCoeff ij)| * (16 : ℝ) ^ (6 / 5 : ℝ) *
          ((cellBound ij.1 ij.2 + cellBound ij.2 ij.1) * diamondNorm z ^ (-(11 / 5) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (hsplit.trans ?_) hc
        calc |jumpGen1 (6 / 5) bspline (16 * z 0 - (ij.1 : ℝ)) * bspline (16 * z 1 - (ij.2 : ℝ))|
              + |bspline (16 * z 0 - (ij.1 : ℝ))
                * jumpGen1 (6 / 5) bspline (16 * z 1 - (ij.2 : ℝ))|
            ≤ cellBound ij.1 ij.2 * diamondNorm z ^ (-(11 / 5) : ℝ)
              + cellBound ij.2 ij.1 * diamondNorm z ^ (-(11 / 5) : ℝ) := add_le_add hA hB
          _ = _ := by ring
    _ = _ := by ring

/-! ### Two one-dimensional weights

Both halves of the base estimate integrate the weight `|t|^{-11/5}` against a bound on the second
difference of the truncated base. Two profiles arise: the *tail* weight, for a second difference
that vanishes below a threshold and grows linearly above it, and the *cut* profile, which carries
the `L¹` mass of the kernel along a line at distance `b` from the origin. -/

/-- `∫_c^∞ t^{-6/5} dt = 5 c^{-1/5}`. -/
private theorem integral_Ioi_rpow_six_fifths {c : ℝ} (hc : 0 < c) :
    ∫ t in Ioi c, t ^ (-(6 / 5) : ℝ) = 5 * c ^ (-(1 / 5) : ℝ) := by
  have h : (-(6 / 5) : ℝ) + 1 = -(1 / 5) := by norm_num
  rw [integral_Ioi_rpow_of_lt (by norm_num : (-(6 / 5) : ℝ) < -1) hc, h]
  ring

private theorem integrableOn_Ioi_rpow_six_fifths {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (-(6 / 5) : ℝ)) (Ioi c) :=
  integrableOn_Ioi_rpow_of_lt (by norm_num) hc

/-- The tail weight `|t|^{-6/5}` outside the window `|t| ≤ δ`. -/
private def tailWeight (δ t : ℝ) : ℝ := if δ < |t| then |t| ^ (-(6 / 5) : ℝ) else 0

private theorem tailWeight_nonneg (δ t : ℝ) : 0 ≤ tailWeight δ t := by
  rw [tailWeight]
  split
  · exact Real.rpow_nonneg (abs_nonneg _) _
  · exact le_rfl

private theorem tailWeight_neg (δ t : ℝ) : tailWeight δ (-t) = tailWeight δ t := by
  rw [tailWeight, tailWeight, abs_neg]

private theorem measurable_tailWeight (δ : ℝ) : Measurable (tailWeight δ) := by
  refine Measurable.ite ?_ (continuous_abs.measurable.pow_const _) measurable_const
  exact measurableSet_lt measurable_const continuous_abs.measurable

private theorem integrableOn_tailWeight {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (tailWeight δ) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi hδ.le, integrableOn_union]
  refine ⟨(integrable_zero ℝ ℝ _).integrableOn.congr_fun (fun t ht => ?_) measurableSet_Ioc,
    (integrableOn_Ioi_rpow_six_fifths hδ).congr_fun (fun t ht => ?_) measurableSet_Ioi⟩
  · show (0 : ℝ) = tailWeight δ t
    rw [tailWeight, if_neg (by rw [abs_of_pos ht.1]; exact not_lt.2 ht.2)]
  · show t ^ (-(6 / 5) : ℝ) = tailWeight δ t
    rw [tailWeight, if_pos (by rw [abs_of_pos (hδ.trans ht)]; exact ht),
      abs_of_pos (hδ.trans ht)]

private theorem integrable_tailWeight {δ : ℝ} (hδ : 0 < δ) : Integrable (tailWeight δ) :=
  CenteredMaximal.integrable_of_even (tailWeight_neg δ) (integrableOn_tailWeight hδ)

/-- **The tail weight has mass `10 δ^{-1/5}`.** -/
private theorem integral_tailWeight {δ : ℝ} (hδ : 0 < δ) :
    ∫ t, tailWeight δ t = 10 * δ ^ (-(1 / 5) : ℝ) := by
  have hzero : ∫ t in Ioc (0 : ℝ) δ, tailWeight δ t = 0 := by
    rw [setIntegral_congr_fun (g := fun _ => (0 : ℝ)) measurableSet_Ioc fun t ht => ?_,
      integral_zero]
    rw [tailWeight, if_neg (by rw [abs_of_pos ht.1]; exact not_lt.2 ht.2)]
  have htail : ∫ t in Ioi δ, tailWeight δ t = 5 * δ ^ (-(1 / 5) : ℝ) := by
    rw [setIntegral_congr_fun (g := fun t : ℝ => t ^ (-(6 / 5) : ℝ)) measurableSet_Ioi
      fun t ht => ?_, integral_Ioi_rpow_six_fifths hδ]
    rw [tailWeight, if_pos (by rw [abs_of_pos (hδ.trans ht)]; exact ht),
      abs_of_pos (hδ.trans ht)]
  have hIoc : IntegrableOn (tailWeight δ) (Ioc 0 δ) :=
    (integrableOn_tailWeight hδ).mono_set (Ioc_subset_Ioi_self)
  have hIoi : IntegrableOn (tailWeight δ) (Ioi δ) :=
    (integrableOn_tailWeight hδ).mono_set (fun t ht => hδ.trans ht)
  rw [CenteredMaximal.integral_of_even (tailWeight_neg δ) (integrableOn_tailWeight hδ),
    ← Ioc_union_Ioi_eq_Ioi hδ.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hIoc hIoi, hzero, htail]
  ring

/-- The line profile of the kernel at distance `b` from the origin: the constant `b^{-6/5}` on the
window `|t| < b` and `|t|^{-6/5}` beyond. -/
private def cutProfile (b t : ℝ) : ℝ :=
  if |t| < b then b ^ (-(6 / 5) : ℝ) else |t| ^ (-(6 / 5) : ℝ)

private theorem cutProfile_nonneg {b : ℝ} (hb : 0 ≤ b) (t : ℝ) : 0 ≤ cutProfile b t := by
  rw [cutProfile]
  split
  · exact Real.rpow_nonneg hb _
  · exact Real.rpow_nonneg (abs_nonneg _) _

private theorem cutProfile_neg (b t : ℝ) : cutProfile b (-t) = cutProfile b t := by
  rw [cutProfile, cutProfile, abs_neg]

private theorem measurable_cutProfile (b : ℝ) : Measurable (cutProfile b) := by
  refine Measurable.ite ?_ measurable_const (continuous_abs.measurable.pow_const _)
  exact measurableSet_lt continuous_abs.measurable measurable_const

/-- **The line profile dominates the kernel's radial power along a line at distance `b`.** -/
private theorem rpow_add_le_cutProfile {b : ℝ} (hb : 0 < b) (u : ℝ) :
    (|u| + b) ^ (-(6 / 5) : ℝ) ≤ cutProfile b u := by
  rw [cutProfile]
  split
  · exact Real.rpow_le_rpow_of_nonpos hb (by linarith [abs_nonneg u]) (by norm_num)
  · rename_i hcase
    have hu : 0 < |u| := lt_of_lt_of_le hb (not_lt.1 hcase)
    exact Real.rpow_le_rpow_of_nonpos hu (by linarith) (by norm_num)

private theorem integrableOn_cutProfile {b : ℝ} (hb : 0 < b) :
    IntegrableOn (cutProfile b) (Ioi 0) := by
  rw [← Ioc_union_Ioi_eq_Ioi hb.le, integrableOn_union]
  refine ⟨(integrableOn_const (C := b ^ (-(6 / 5) : ℝ)) (by
      rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).congr_fun (fun t ht => ?_)
      measurableSet_Ioc,
    (integrableOn_Ioi_rpow_six_fifths hb).congr_fun (fun t ht => ?_) measurableSet_Ioi⟩
  · show b ^ (-(6 / 5) : ℝ) = cutProfile b t
    rcases lt_or_ge t b with hlt | hge
    · rw [cutProfile, if_pos (by rwa [abs_of_pos ht.1])]
    · have ht' : t = b := le_antisymm ht.2 hge
      rw [cutProfile, if_neg (by rw [abs_of_pos ht.1, ht']; exact lt_irrefl b), ht',
        abs_of_pos hb]
  · show t ^ (-(6 / 5) : ℝ) = cutProfile b t
    rw [cutProfile, if_neg (by rw [abs_of_pos (hb.trans ht)]; exact not_lt.2 ht.le),
      abs_of_pos (hb.trans ht)]

private theorem integrable_cutProfile {b : ℝ} (hb : 0 < b) : Integrable (cutProfile b) :=
  CenteredMaximal.integrable_of_even (cutProfile_neg b) (integrableOn_cutProfile hb)

/-- **The line profile has mass `12 b^{-1/5}`.** -/
private theorem integral_cutProfile {b : ℝ} (hb : 0 < b) :
    ∫ t, cutProfile b t = 12 * b ^ (-(1 / 5) : ℝ) := by
  have hb1 : b * b ^ (-(6 / 5) : ℝ) = b ^ (-(1 / 5) : ℝ) := by
    rw [show (-(1 / 5) : ℝ) = 1 + -(6 / 5) from by norm_num, Real.rpow_add hb, Real.rpow_one]
  have hhead : ∫ t in Ioc (0 : ℝ) b, cutProfile b t = b ^ (-(1 / 5) : ℝ) := by
    rw [setIntegral_congr_fun (g := fun _ => b ^ (-(6 / 5) : ℝ)) measurableSet_Ioc fun t ht => ?_,
      setIntegral_const, Real.volume_real_Ioc_of_le hb.le, sub_zero, smul_eq_mul, hb1]
    rcases lt_or_ge t b with hlt | hge
    · rw [cutProfile, if_pos (by rwa [abs_of_pos ht.1])]
    · have ht' : t = b := le_antisymm ht.2 hge
      rw [cutProfile, if_neg (by rw [abs_of_pos ht.1, ht']; exact lt_irrefl b), ht',
        abs_of_pos hb]
  have htail : ∫ t in Ioi b, cutProfile b t = 5 * b ^ (-(1 / 5) : ℝ) := by
    rw [setIntegral_congr_fun (g := fun t : ℝ => t ^ (-(6 / 5) : ℝ)) measurableSet_Ioi
      fun t ht => ?_, integral_Ioi_rpow_six_fifths hb]
    rw [cutProfile, if_neg (by rw [abs_of_pos (hb.trans ht)]; exact not_lt.2 ht.le),
      abs_of_pos (hb.trans ht)]
  have hIoc : IntegrableOn (cutProfile b) (Ioc 0 b) :=
    (integrableOn_cutProfile hb).mono_set Ioc_subset_Ioi_self
  have hIoi : IntegrableOn (cutProfile b) (Ioi b) :=
    (integrableOn_cutProfile hb).mono_set fun t ht => hb.trans ht
  rw [CenteredMaximal.integral_of_even (cutProfile_neg b) (integrableOn_cutProfile hb),
    ← Ioc_union_Ioi_eq_Ioi hb.le,
    setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hIoc hIoi, hhead, htail]
  ring

/-- The translate of the line profile has the same mass. -/
private theorem integral_cutProfile_add {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ∫ t, cutProfile b (t + c) = 12 * b ^ (-(1 / 5) : ℝ) := by
  rw [integral_add_right_eq_self (fun u : ℝ => cutProfile b u) c, integral_cutProfile hb]

private theorem integrable_cutProfile_add {b : ℝ} (hb : 0 < b) (c : ℝ) :
    Integrable fun t : ℝ => cutProfile b (t + c) :=
  (integrable_cutProfile hb).comp_add_right c

/-! ### Coordinates along a line

The displacement in direction `j` moves the coordinate `z j` and leaves `z (j+1)` alone, so the
diamond radius along the line is `|z j ± t| + |z (j+1)|`. These four facts are `private` in
`CenteredMaximal.Fractional.TruncatedBase` and are reproved here. -/

private theorem dnorm_eq_add (z : Fin 2 → ℝ) (j : Fin 2) :
    diamondNorm z = |z j| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem dnorm_add_single (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z + s • Pi.single j 1) = |z j + s| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem dnorm_sub_single (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z - s • Pi.single j 1) = |z j - s| + |z (j + 1)| := by
  rw [sub_eq_add_neg, ← neg_smul, dnorm_add_single, ← sub_eq_add_neg]

private theorem coord_succ_pos {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2) :
    0 < |z (j + 1)| := by
  fin_cases j
  · simpa using abs_pos.2 h1
  · simpa using abs_pos.2 h0

/-- The radius of a displaced point is at least the untouched coordinate. -/
private theorem coord_le_dnorm_add (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    |z (j + 1)| ≤ diamondNorm (z + t • Pi.single j 1) := by
  rw [dnorm_add_single]
  linarith [abs_nonneg (z j + t)]

private theorem coord_le_dnorm_sub (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    |z (j + 1)| ≤ diamondNorm (z - t • Pi.single j 1) := by
  rw [dnorm_sub_single]
  linarith [abs_nonneg (z j - t)]

/-- The radius of a displaced point grows by at most the step. -/
private theorem dnorm_add_le (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    diamondNorm (z + t • Pi.single j 1) ≤ diamondNorm z + |t| := by
  rw [dnorm_add_single, dnorm_eq_add z j]
  linarith [abs_add_le (z j) t]

private theorem dnorm_sub_le (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    diamondNorm (z - t • Pi.single j 1) ≤ diamondNorm z + |t| := by
  have h : |z j - t| ≤ |z j| + |t| := by
    rw [sub_eq_add_neg]
    calc |z j + -t| ≤ |z j| + |-t| := abs_add_le _ _
      _ = |z j| + |t| := by rw [abs_neg]
  rw [dnorm_sub_single, dnorm_eq_add z j]
  linarith

/-- The radius of a displaced point shrinks by at most the step. -/
private theorem le_dnorm_add (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    diamondNorm z - |t| ≤ diamondNorm (z + t • Pi.single j 1) := by
  have h : |z j| ≤ |z j + t| + |t| := by
    calc |z j| = |(z j + t) + -t| := by congr 1; ring
      _ ≤ |z j + t| + |-t| := abs_add_le _ _
      _ = |z j + t| + |t| := by rw [abs_neg]
  rw [dnorm_add_single, dnorm_eq_add z j]
  linarith

private theorem le_dnorm_sub (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    diamondNorm z - |t| ≤ diamondNorm (z - t • Pi.single j 1) := by
  rw [dnorm_sub_single, dnorm_eq_add z j]
  linarith [abs_sub_abs_le_abs_sub (z j) t]

/-! ### The two tangent-line bounds

Both the truncated base and its exterior complement are controlled by the tangent line of
`u ↦ u^{-6/5}`, which is `CenteredMaximal.Fractional.rpow_neg_tangent`. -/

/-- **The exterior tail grows at most linearly past the truncation radius.** -/
private theorem truncTail_le_lin {w : Fin 2 → ℝ} (hw : 0 < diamondNorm w) :
    truncTail (6 / 5) (7 / 4) w
      ≤ 6 / 5 * (7 / 4 : ℝ) ^ (-(11 / 5) : ℝ) * max (diamondNorm w - 7 / 4) 0 := by
  have htan := rpow_neg_tangent (α := 6 / 5) (by norm_num) (q := (7 / 4 : ℝ)) (r := diamondNorm w)
    (by norm_num) hw
  have hexp : ((7 : ℝ) / 4) ^ (-(6 / 5 : ℝ) - 1) = ((7 : ℝ) / 4) ^ (-(11 / 5) : ℝ) := by
    norm_num
  rw [hexp] at htan
  have hcoef : (0 : ℝ) ≤ 6 / 5 * (7 / 4 : ℝ) ^ (-(11 / 5) : ℝ) := by
    have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 4) (-(11 / 5) : ℝ)
    positivity
  have hmax : diamondNorm w - 7 / 4 ≤ max (diamondNorm w - 7 / 4) 0 := le_max_left _ _
  refine max_le ?_ (by positivity)
  nlinarith [htan, hmax, hcoef]

/-- **The truncated base vanishes at the truncation radius at least linearly.** -/
private theorem truncBase_le_lin {β : ℝ} (hβ : 0 < β) {w : Fin 2 → ℝ}
    (hw : β ≤ diamondNorm w) :
    truncBase (6 / 5) (7 / 4) w
      ≤ 6 / 5 * β ^ (-(11 / 5) : ℝ) * max (7 / 4 - diamondNorm w) 0 := by
  have hw0 : 0 < diamondNorm w := lt_of_lt_of_le hβ hw
  have htan := rpow_neg_tangent (α := 6 / 5) (by norm_num) (q := diamondNorm w)
    (r := (7 / 4 : ℝ)) hw0 (by norm_num)
  have hexp : diamondNorm w ^ (-(6 / 5 : ℝ) - 1) = diamondNorm w ^ (-(11 / 5) : ℝ) := by
    norm_num
  rw [hexp] at htan
  have hmono : diamondNorm w ^ (-(11 / 5) : ℝ) ≤ β ^ (-(11 / 5) : ℝ) :=
    Real.rpow_le_rpow_of_nonpos hβ hw (by norm_num)
  have hβpow : (0 : ℝ) < β ^ (-(11 / 5) : ℝ) := Real.rpow_pos_of_pos hβ _
  have hwpow : (0 : ℝ) < diamondNorm w ^ (-(11 / 5) : ℝ) := Real.rpow_pos_of_pos hw0 _
  refine max_le ?_ (by positivity)
  rcases le_total (diamondNorm w) (7 / 4 : ℝ) with hcase | hcase
  · have hmax : max (7 / 4 - diamondNorm w) 0 = 7 / 4 - diamondNorm w :=
      max_eq_left (by linarith)
    rw [hmax]
    nlinarith [htan, hmono]
  · have hle : diamondNorm w ^ (-(6 / 5) : ℝ) ≤ ((7 : ℝ) / 4) ^ (-(6 / 5) : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hcase (by norm_num)
    have hmax : (0 : ℝ) ≤ max (7 / 4 - diamondNorm w) 0 := le_max_right _ _
    nlinarith [hle, hmax, hβpow]

/-- The truncated base is below the bare radial power. -/
private theorem truncBase_le_rpow (w : Fin 2 → ℝ) :
    truncBase (6 / 5) (7 / 4) w ≤ diamondNorm w ^ (-(6 / 5) : ℝ) := by
  refine max_le (by linarith [Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 7/4) (-(6/5) : ℝ)]) ?_
  exact Real.rpow_nonneg (diamondNorm_nonneg w) _

/-- **The weight lemma.** A second difference that vanishes below `δ` and grows linearly above it
contributes at most the tail weight against `|t|^{-11/5}`. -/
private theorem max_sub_mul_rpow_le_tailWeight {δ : ℝ} (hδ : 0 ≤ δ) (t : ℝ) :
    max (|t| - δ) 0 * |t| ^ (-(1 + 6 / 5) : ℝ) ≤ tailWeight δ t := by
  rcases le_or_gt |t| δ with hcase | hcase
  · rw [max_eq_right (by linarith), zero_mul]
    exact tailWeight_nonneg δ t
  · have ht : 0 < |t| := lt_of_le_of_lt hδ hcase
    have hpow : (0 : ℝ) ≤ |t| ^ (-(1 + 6 / 5) : ℝ) := Real.rpow_nonneg ht.le _
    have hid : |t| * |t| ^ (-(1 + 6 / 5) : ℝ) = |t| ^ (-(6 / 5) : ℝ) := by
      rw [show (-(6 / 5) : ℝ) = 1 + -(1 + 6 / 5) from by norm_num, Real.rpow_add ht,
        Real.rpow_one]
    rw [tailWeight, if_pos hcase, max_eq_left (by linarith), ← hid]
    exact mul_le_mul_of_nonneg_right (by linarith) hpow

/-! ### One direction of the generator -/

/-- Bounding one direction of the generator by an integrable majorant of its integrand. -/
private theorem abs_integral_dir_le {φ : (Fin 2 → ℝ) → ℝ} (j : Fin 2) (z : Fin 2 → ℝ) {G : ℝ → ℝ}
    (hG : Integrable G)
    (hb : ∀ t : ℝ, |secondDiff φ j z t| * |t| ^ (-(1 + 6 / 5) : ℝ) ≤ G t) :
    |∫ t : ℝ, secondDiff φ j z t * |t| ^ (-(1 + 6 / 5) : ℝ)| ≤ ∫ t : ℝ, G t := by
  have h : ∀ᵐ t : ℝ, ‖secondDiff φ j z t * |t| ^ (-(1 + 6 / 5) : ℝ)‖ ≤ G t := by
    refine .of_forall fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
    exact hb t
  have hle := norm_integral_le_of_norm_le hG h
  rwa [Real.norm_eq_abs] at hle

/-! ### The interior: the generator of the exterior tail

Inside the diamond the truncated base is the diamond power up to a constant — that is
`CenteredMaximal.Fractional.jumpGen_truncBase`, whose closed form is exactly `r^{-12/5}` — plus the
generator of the exterior tail, which is what is estimated here. The tail vanishes at `z` and
grows at most linearly past the truncation radius, so its second difference vanishes for
`|t| ≤ 7/4 − r` and is `O(|t| − (7/4 − r))` beyond: the tail weight with `δ = 7/4 − r`. -/

/-- **The generator of the exterior tail, inside the diamond.** -/
private theorem abs_jumpGen_truncTail_le {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0)
    (hz : diamondNorm z < 7 / 4) :
    |jumpGen (6 / 5) (truncTail (6 / 5) (7 / 4)) z|
      ≤ 48 * (7 / 4 - diamondNorm z) ^ (-(1 / 5) : ℝ) := by
  set δ : ℝ := 7 / 4 - diamondNorm z with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hz0 : z ≠ 0 := fun h => h0 (by simp [h])
  have hTz : truncTail (6 / 5) (7 / 4) z = 0 := truncTail_eq_zero (by norm_num) hz0 hz.le
  set K : ℝ := 6 / 5 * (7 / 4 : ℝ) ^ (-(11 / 5) : ℝ) with hK
  have hKpow : (0 : ℝ) < (7 / 4 : ℝ) ^ (-(11 / 5) : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hK0 : 0 < K := by rw [hK]; positivity
  have hK1 : K ≤ 6 / 5 := by
    have h : (7 / 4 : ℝ) ^ (-(11 / 5) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
    rw [hK]
    nlinarith
  have hδpow : (0 : ℝ) < δ ^ (-(1 / 5) : ℝ) := Real.rpow_pos_of_pos hδ _
  have hdir : ∀ j : Fin 2,
      |∫ t : ℝ, secondDiff (truncTail (6 / 5) (7 / 4)) j z t * |t| ^ (-(1 + 6 / 5) : ℝ)|
        ≤ 24 * δ ^ (-(1 / 5) : ℝ) := by
    intro j
    have hbpos : 0 < |z (j + 1)| := coord_succ_pos h0 h1 j
    have hb : ∀ t : ℝ, |secondDiff (truncTail (6 / 5) (7 / 4)) j z t| * |t| ^ (-(1 + 6 / 5) : ℝ)
        ≤ (2 * K) * tailWeight δ t := by
      intro t
      have hp0 : 0 < diamondNorm (z + t • Pi.single j 1) :=
        lt_of_lt_of_le hbpos (coord_le_dnorm_add z j t)
      have hm0 : 0 < diamondNorm (z - t • Pi.single j 1) :=
        lt_of_lt_of_le hbpos (coord_le_dnorm_sub z j t)
      have hp := truncTail_le_lin hp0
      have hm := truncTail_le_lin hm0
      rw [← hK] at hp hm
      have hmaxp : max (diamondNorm (z + t • Pi.single j 1) - 7 / 4) 0 ≤ max (|t| - δ) 0 :=
        max_le_max (by rw [hδdef]; linarith [dnorm_add_le z j t]) le_rfl
      have hmaxm : max (diamondNorm (z - t • Pi.single j 1) - 7 / 4) 0 ≤ max (|t| - δ) 0 :=
        max_le_max (by rw [hδdef]; linarith [dnorm_sub_le z j t]) le_rfl
      have hnnp : 0 ≤ truncTail (6 / 5) (7 / 4) (z + t • Pi.single j 1) := truncTail_nonneg _ _ _
      have hnnm : 0 ≤ truncTail (6 / 5) (7 / 4) (z - t • Pi.single j 1) := truncTail_nonneg _ _ _
      have hsd : |secondDiff (truncTail (6 / 5) (7 / 4)) j z t| ≤ 2 * K * max (|t| - δ) 0 := by
        rw [secondDiff, hTz, abs_of_nonneg (by linarith : (0 : ℝ) ≤
          truncTail (6 / 5) (7 / 4) (z + t • Pi.single j 1)
            + truncTail (6 / 5) (7 / 4) (z - t • Pi.single j 1) - 2 * 0)]
        nlinarith [hp, hm, hmaxp, hmaxm, hK0]
      have hwt := max_sub_mul_rpow_le_tailWeight hδ.le t
      have hK2 : (0 : ℝ) ≤ 2 * K := by linarith
      have hw0 : (0 : ℝ) ≤ |t| ^ (-(1 + 6 / 5) : ℝ) := Real.rpow_nonneg (abs_nonneg t) _
      calc |secondDiff (truncTail (6 / 5) (7 / 4)) j z t| * |t| ^ (-(1 + 6 / 5) : ℝ)
          ≤ (2 * K * max (|t| - δ) 0) * |t| ^ (-(1 + 6 / 5) : ℝ) :=
            mul_le_mul_of_nonneg_right hsd hw0
        _ = (2 * K) * (max (|t| - δ) 0 * |t| ^ (-(1 + 6 / 5) : ℝ)) := by ring
        _ ≤ (2 * K) * tailWeight δ t := mul_le_mul_of_nonneg_left hwt hK2
    have hint := abs_integral_dir_le j z ((integrable_tailWeight hδ).const_mul (2 * K)) hb
    rw [integral_const_mul, integral_tailWeight hδ] at hint
    calc |∫ t : ℝ, secondDiff (truncTail (6 / 5) (7 / 4)) j z t * |t| ^ (-(1 + 6 / 5) : ℝ)|
        ≤ 2 * K * (10 * δ ^ (-(1 / 5) : ℝ)) := hint
      _ ≤ 24 * δ ^ (-(1 / 5) : ℝ) := by nlinarith [hK1, hδpow]
  rw [jumpGen, Fin.sum_univ_two]
  calc |(∫ t : ℝ, secondDiff (truncTail (6 / 5) (7 / 4)) 0 z t * |t| ^ (-(1 + 6 / 5) : ℝ))
        + ∫ t : ℝ, secondDiff (truncTail (6 / 5) (7 / 4)) 1 z t * |t| ^ (-(1 + 6 / 5) : ℝ)|
      ≤ |∫ t : ℝ, secondDiff (truncTail (6 / 5) (7 / 4)) 0 z t * |t| ^ (-(1 + 6 / 5) : ℝ)|
        + |∫ t : ℝ, secondDiff (truncTail (6 / 5) (7 / 4)) 1 z t * |t| ^ (-(1 + 6 / 5) : ℝ)| :=
        abs_add_le _ _
    _ ≤ 24 * δ ^ (-(1 / 5) : ℝ) + 24 * δ ^ (-(1 / 5) : ℝ) := add_le_add (hdir 0) (hdir 1)
    _ = 48 * δ ^ (-(1 / 5) : ℝ) := by ring

/-! ### The exterior: the generator of the truncated base past the support

Outside the closed diamond the base vanishes at `z`, so the second difference is the sum of the two
displaced values, both nonnegative. Two mechanisms bound them. If the *untouched* coordinate `b` is
the larger one, the whole line stays at radius at least `b ≥ r/2`, and the tangent-line bound gives
`O((|t| − δ)₊)` with `δ = r − 7/4` throughout. If instead the *moved* coordinate `a` is the larger
one, that argument only survives for `|t| ≤ a/2`; past it the line sweeps across the kernel's own
`r^{-6/5}` singularity at distance `b` from the origin, and only the `L¹` mass `12 b^{-1/5}` of the
cut profile is available — which is exactly where the factor `m^{-1/5}` of the majorant comes from.
-/

/-- The truncated base vanishes outside the closed diamond of radius `7/4`. -/
private theorem truncBase_eq_zero_ext {w : Fin 2 → ℝ} (hw : 7 / 4 ≤ diamondNorm w) :
    truncBase (6 / 5) (7 / 4) w = 0 :=
  max_eq_right (by
    linarith [Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 7 / 4) hw
      (by norm_num : (-(6 / 5) : ℝ) ≤ 0)])

private theorem integral_cutProfile_sub {b : ℝ} (hb : 0 < b) (c : ℝ) :
    ∫ t, cutProfile b (t - c) = 12 * b ^ (-(1 / 5) : ℝ) := by
  rw [integral_sub_right_eq_self (fun u : ℝ => cutProfile b u) c, integral_cutProfile hb]

private theorem integrable_cutProfile_sub {b : ℝ} (hb : 0 < b) (c : ℝ) :
    Integrable fun t : ℝ => cutProfile b (t - c) :=
  (integrable_cutProfile hb).comp_sub_right c

/-- `k^{11/5} ≤ k³` for `k ≥ 1`. -/
private theorem rpow_eleven_fifths_le {k K : ℝ} (hk : 1 ≤ k) (hK : k ^ 3 ≤ K) :
    k ^ (11 / 5 : ℝ) ≤ K := by
  calc k ^ (11 / 5 : ℝ) ≤ k ^ (3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hk (by norm_num)
    _ = k ^ 3 := by
        rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    _ ≤ K := hK

/-- Scaling the radius down by `k` costs a factor `k^{11/5}`. -/
private theorem rpow_neg_div_le {r k K : ℝ} (hr : 0 < r) (hk : 0 < k)
    (hK : k ^ (11 / 5 : ℝ) ≤ K) :
    (r / k) ^ (-(11 / 5) : ℝ) ≤ K * r ^ (-(11 / 5) : ℝ) := by
  have h1 : (r / k) ^ (-(11 / 5) : ℝ) = r ^ (-(11 / 5) : ℝ) * k ^ (11 / 5 : ℝ) := by
    rw [Real.div_rpow hr.le hk.le, Real.rpow_neg hk.le, div_eq_mul_inv, inv_inv]
  have h2 : (0 : ℝ) ≤ r ^ (-(11 / 5) : ℝ) := Real.rpow_nonneg hr.le _
  rw [h1]
  nlinarith

/-- The arithmetic that closes both branches of the exterior estimate. -/
private theorem final_arith {rp dp mp : ℝ} (h1 : 0 ≤ rp) (h2 : 0 ≤ dp) (hm : 0 ≤ mp) :
    192 * (rp * dp) + 1536 * (rp * mp) ≤ 1536 * rp * (dp + mp) := by
  have h3 : 0 ≤ rp * dp := mul_nonneg h1 h2
  have h4 : 0 ≤ rp * mp := mul_nonneg h1 hm
  nlinarith [h3, h4]

/-- Outside the diamond the second difference of the base is the sum of its two displaced values. -/
private theorem abs_secondDiff_ext_eq {z : Fin 2 → ℝ} (hz : 7 / 4 ≤ diamondNorm z) (j : Fin 2)
    (t : ℝ) : |secondDiff (truncBase (6 / 5) (7 / 4)) j z t|
      = truncBase (6 / 5) (7 / 4) (z + t • Pi.single j 1)
        + truncBase (6 / 5) (7 / 4) (z - t • Pi.single j 1) := by
  have hp := truncBase_nonneg (6 / 5) (7 / 4) (z + t • Pi.single j 1)
  have hm := truncBase_nonneg (6 / 5) (7 / 4) (z - t • Pi.single j 1)
  rw [secondDiff, truncBase_eq_zero_ext hz, abs_of_nonneg (by linarith)]
  ring

/-- The gap to the truncation radius at a displaced point is at most `|t| − δ`. -/
private theorem max_gap_add_le (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    max (7 / 4 - diamondNorm (z + t • Pi.single j 1)) 0
      ≤ max (|t| - (diamondNorm z - 7 / 4)) 0 :=
  max_le_max (by linarith [le_dnorm_add z j t]) le_rfl

private theorem max_gap_sub_le (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    max (7 / 4 - diamondNorm (z - t • Pi.single j 1)) 0
      ≤ max (|t| - (diamondNorm z - 7 / 4)) 0 :=
  max_le_max (by linarith [le_dnorm_sub z j t]) le_rfl

/-- The tangent-line bound at both displaced points, integrated against the weight: if the whole
segment stays at radius at least `β`, the weighted second difference is at most
`(12/5) β^{-11/5}` times the tail weight. -/
private theorem secondDiff_ext_le_tailWeight {z : Fin 2 → ℝ} (hz : 7 / 4 ≤ diamondNorm z)
    (j : Fin 2) {β : ℝ} (hβ : 0 < β) {t : ℝ}
    (hp : β ≤ diamondNorm (z + t • Pi.single j 1))
    (hm : β ≤ diamondNorm (z - t • Pi.single j 1)) (hδ : 0 ≤ diamondNorm z - 7 / 4) :
    |secondDiff (truncBase (6 / 5) (7 / 4)) j z t| * |t| ^ (-(1 + 6 / 5) : ℝ)
      ≤ (2 * (6 / 5 * β ^ (-(11 / 5) : ℝ))) * tailWeight (diamondNorm z - 7 / 4) t := by
  set K : ℝ := 6 / 5 * β ^ (-(11 / 5) : ℝ) with hK
  have hK0 : 0 < K := by
    have := Real.rpow_pos_of_pos hβ (-(11 / 5) : ℝ)
    rw [hK]; positivity
  have hbp := truncBase_le_lin hβ hp
  have hbm := truncBase_le_lin hβ hm
  rw [← hK] at hbp hbm
  have h1 : K * max (7 / 4 - diamondNorm (z + t • Pi.single j 1)) 0
      ≤ K * max (|t| - (diamondNorm z - 7 / 4)) 0 :=
    mul_le_mul_of_nonneg_left (max_gap_add_le z j t) hK0.le
  have h2 : K * max (7 / 4 - diamondNorm (z - t • Pi.single j 1)) 0
      ≤ K * max (|t| - (diamondNorm z - 7 / 4)) 0 :=
    mul_le_mul_of_nonneg_left (max_gap_sub_le z j t) hK0.le
  have hstep : |secondDiff (truncBase (6 / 5) (7 / 4)) j z t|
      ≤ 2 * K * max (|t| - (diamondNorm z - 7 / 4)) 0 := by
    rw [abs_secondDiff_ext_eq hz j t]
    linarith
  have hw0 : (0 : ℝ) ≤ |t| ^ (-(1 + 6 / 5) : ℝ) := Real.rpow_nonneg (abs_nonneg t) _
  calc |secondDiff (truncBase (6 / 5) (7 / 4)) j z t| * |t| ^ (-(1 + 6 / 5) : ℝ)
      ≤ (2 * K * max (|t| - (diamondNorm z - 7 / 4)) 0) * |t| ^ (-(1 + 6 / 5) : ℝ) :=
        mul_le_mul_of_nonneg_right hstep hw0
    _ = (2 * K) * (max (|t| - (diamondNorm z - 7 / 4)) 0 * |t| ^ (-(1 + 6 / 5) : ℝ)) := by ring
    _ ≤ (2 * K) * tailWeight (diamondNorm z - 7 / 4) t :=
        mul_le_mul_of_nonneg_left (max_sub_mul_rpow_le_tailWeight hδ t) (by linarith)

/-- **One direction of the base generator outside the diamond, when the untouched coordinate is the
larger one.** The whole line then stays at radius at least `r/2`, so the tangent-line bound applies
for every step. -/
private theorem abs_integral_dir_ext_of_le {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0)
    (hz : 7 / 4 < diamondNorm z) (j : Fin 2) (hcase : |z j| ≤ |z (j + 1)|) :
    |∫ t : ℝ, secondDiff (truncBase (6 / 5) (7 / 4)) j z t * |t| ^ (-(1 + 6 / 5) : ℝ)|
      ≤ 1536 * diamondNorm z ^ (-(11 / 5) : ℝ)
        * ((diamondNorm z - 7 / 4) ^ (-(1 / 5) : ℝ)
          + (min |z j| |z (j + 1)|) ^ (-(1 / 5) : ℝ)) := by
  have hb : 0 < |z (j + 1)| := coord_succ_pos h0 h1 j
  have ha : 0 < |z j| := by
    fin_cases j
    · simpa using abs_pos.2 h0
    · simpa using abs_pos.2 h1
  have hr : diamondNorm z = |z j| + |z (j + 1)| := dnorm_eq_add z j
  have hrpos : 0 < diamondNorm z := by rw [hr]; linarith
  have hδ : 0 < diamondNorm z - 7 / 4 := by linarith
  have hδpow : (0 : ℝ) < (diamondNorm z - 7 / 4) ^ (-(1 / 5) : ℝ) := Real.rpow_pos_of_pos hδ _
  have hrpow : (0 : ℝ) < diamondNorm z ^ (-(11 / 5) : ℝ) := Real.rpow_pos_of_pos hrpos _
  have hmpow : (0 : ℝ) < (min |z j| |z (j + 1)|) ^ (-(1 / 5) : ℝ) :=
    Real.rpow_pos_of_pos (lt_min ha hb) _
  have hbnd : ∀ t : ℝ, |secondDiff (truncBase (6 / 5) (7 / 4)) j z t|
      * |t| ^ (-(1 + 6 / 5) : ℝ)
      ≤ (2 * (6 / 5 * |z (j + 1)| ^ (-(11 / 5) : ℝ)))
        * tailWeight (diamondNorm z - 7 / 4) t := fun t =>
    secondDiff_ext_le_tailWeight hz.le j hb (coord_le_dnorm_add z j t)
      (coord_le_dnorm_sub z j t) hδ.le
  have hint := abs_integral_dir_le j z
    ((integrable_tailWeight hδ).const_mul (2 * (6 / 5 * |z (j + 1)| ^ (-(11 / 5) : ℝ)))) hbnd
  rw [integral_const_mul, integral_tailWeight hδ] at hint
  have hbr : diamondNorm z / 2 ≤ |z (j + 1)| := by rw [hr]; linarith
  have hbpow : |z (j + 1)| ^ (-(11 / 5) : ℝ) ≤ 8 * diamondNorm z ^ (-(11 / 5) : ℝ) := by
    refine le_trans (Real.rpow_le_rpow_of_nonpos (by positivity) hbr (by norm_num)) ?_
    exact rpow_neg_div_le hrpos (by norm_num)
      (rpow_eleven_fifths_le (by norm_num) (by norm_num))
  have hmul : |z (j + 1)| ^ (-(11 / 5) : ℝ) * (diamondNorm z - 7 / 4) ^ (-(1 / 5) : ℝ)
      ≤ (8 * diamondNorm z ^ (-(11 / 5) : ℝ)) * (diamondNorm z - 7 / 4) ^ (-(1 / 5) : ℝ) :=
    mul_le_mul_of_nonneg_right hbpow hδpow.le
  refine hint.trans (le_trans ?_ (final_arith hrpow.le hδpow.le hmpow.le))
  have hnn : (0 : ℝ) ≤ diamondNorm z ^ (-(11 / 5) : ℝ)
      * (min |z j| |z (j + 1)|) ^ (-(1 / 5) : ℝ) := by positivity
  linarith

/-- **One direction of the base generator outside the diamond, when the moved coordinate is the
larger one.** The tangent-line bound survives only for `|t| ≤ a/2`; past it the line sweeps across
the kernel's own singularity, and the cut profile's mass `12 b^{-1/5}` takes over. -/
private theorem abs_integral_dir_ext_of_ge {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0)
    (hz : 7 / 4 < diamondNorm z) (j : Fin 2) (hcase : |z (j + 1)| ≤ |z j|) :
    |∫ t : ℝ, secondDiff (truncBase (6 / 5) (7 / 4)) j z t * |t| ^ (-(1 + 6 / 5) : ℝ)|
      ≤ 1536 * diamondNorm z ^ (-(11 / 5) : ℝ)
        * ((diamondNorm z - 7 / 4) ^ (-(1 / 5) : ℝ)
          + (min |z j| |z (j + 1)|) ^ (-(1 / 5) : ℝ)) := by
  have hb : 0 < |z (j + 1)| := coord_succ_pos h0 h1 j
  have ha : 0 < |z j| := by
    fin_cases j
    · simpa using abs_pos.2 h0
    · simpa using abs_pos.2 h1
  have hr : diamondNorm z = |z j| + |z (j + 1)| := dnorm_eq_add z j
  have hrpos : 0 < diamondNorm z := by rw [hr]; linarith
  have hδ : 0 < diamondNorm z - 7 / 4 := by linarith
  have hδpow : (0 : ℝ) < (diamondNorm z - 7 / 4) ^ (-(1 / 5) : ℝ) := Real.rpow_pos_of_pos hδ _
  have hrpow : (0 : ℝ) < diamondNorm z ^ (-(11 / 5) : ℝ) := Real.rpow_pos_of_pos hrpos _
  have har : diamondNorm z / 2 ≤ |z j| := by rw [hr]; linarith
  have ha2 : (0 : ℝ) < |z j| / 2 := by linarith
  have hhalf : (0 : ℝ) < diamondNorm z / 2 := by linarith
  set K : ℝ := 2 * (6 / 5 * (diamondNorm z / 2) ^ (-(11 / 5) : ℝ)) with hK
  have hKpow : (0 : ℝ) < (diamondNorm z / 2) ^ (-(11 / 5) : ℝ) :=
    Real.rpow_pos_of_pos hhalf _
  have hK0 : 0 < K := by rw [hK]; positivity
  set C : ℝ := (|z j| / 2) ^ (-(11 / 5) : ℝ) with hC
  have hC0 : 0 < C := Real.rpow_pos_of_pos ha2 _
  set G : ℝ → ℝ := fun t => K * tailWeight (diamondNorm z - 7 / 4) t
    + C * (cutProfile |z (j + 1)| (t + z j) + cutProfile |z (j + 1)| (t - z j)) with hG
  have hGtail : Integrable fun t : ℝ => K * tailWeight (diamondNorm z - 7 / 4) t :=
    (integrable_tailWeight hδ).const_mul K
  have hGcut : Integrable fun t : ℝ =>
      C * (cutProfile |z (j + 1)| (t + z j) + cutProfile |z (j + 1)| (t - z j)) :=
    ((integrable_cutProfile_add hb (z j)).add (integrable_cutProfile_sub hb (z j))).const_mul C
  have hbnd : ∀ t : ℝ, |secondDiff (truncBase (6 / 5) (7 / 4)) j z t|
      * |t| ^ (-(1 + 6 / 5) : ℝ) ≤ G t := by
    intro t
    have hcut0 : (0 : ℝ)
        ≤ cutProfile |z (j + 1)| (t + z j) + cutProfile |z (j + 1)| (t - z j) :=
      add_nonneg (cutProfile_nonneg hb.le _) (cutProfile_nonneg hb.le _)
    rcases le_or_gt |t| (|z j| / 2) with hsmall | hbig
    · have h2p : |z j| - |t| ≤ |z j + t| := by
        have hh : |z j| ≤ |z j + t| + |t| := by
          calc |z j| = |(z j + t) + -t| := by congr 1; ring
            _ ≤ |z j + t| + |-t| := abs_add_le _ _
            _ = |z j + t| + |t| := by rw [abs_neg]
        linarith
      have h2m : |z j| - |t| ≤ |z j - t| := abs_sub_abs_le_abs_sub (z j) t
      have hrp : diamondNorm z / 2 ≤ diamondNorm (z + t • Pi.single j 1) := by
        rw [dnorm_add_single]
        linarith
      have hrm : diamondNorm z / 2 ≤ diamondNorm (z - t • Pi.single j 1) := by
        rw [dnorm_sub_single]
        linarith
      have hstep := secondDiff_ext_le_tailWeight hz.le j hhalf hrp hrm hδ.le
      rw [← hK] at hstep
      have hcnn : (0 : ℝ)
          ≤ C * (cutProfile |z (j + 1)| (t + z j) + cutProfile |z (j + 1)| (t - z j)) :=
        mul_nonneg hC0.le hcut0
      rw [hG]
      linarith
    · have hwbig : |t| ^ (-(1 + 6 / 5) : ℝ) ≤ C := by
        rw [hC]
        have h := Real.rpow_le_rpow_of_nonpos ha2 hbig.le (by norm_num : (-(11 / 5) : ℝ) ≤ 0)
        calc |t| ^ (-(1 + 6 / 5) : ℝ) = |t| ^ (-(11 / 5) : ℝ) := by norm_num
          _ ≤ (|z j| / 2) ^ (-(11 / 5) : ℝ) := h
      have hpcut : truncBase (6 / 5) (7 / 4) (z + t • Pi.single j 1)
          ≤ cutProfile |z (j + 1)| (t + z j) := by
        refine le_trans (truncBase_le_rpow _) ?_
        rw [dnorm_add_single]
        refine le_trans (le_of_eq ?_) (rpow_add_le_cutProfile hb (t + z j))
        rw [show |t + z j| = |z j + t| from by rw [add_comm]]
      have hmcut : truncBase (6 / 5) (7 / 4) (z - t • Pi.single j 1)
          ≤ cutProfile |z (j + 1)| (t - z j) := by
        refine le_trans (truncBase_le_rpow _) ?_
        rw [dnorm_sub_single]
        refine le_trans (le_of_eq ?_) (rpow_add_le_cutProfile hb (t - z j))
        rw [show |t - z j| = |z j - t| from by rw [abs_sub_comm]]
      have hsum : |secondDiff (truncBase (6 / 5) (7 / 4)) j z t|
          ≤ cutProfile |z (j + 1)| (t + z j) + cutProfile |z (j + 1)| (t - z j) := by
        rw [abs_secondDiff_ext_eq hz.le j t]
        linarith
      have hmul : |secondDiff (truncBase (6 / 5) (7 / 4)) j z t| * |t| ^ (-(1 + 6 / 5) : ℝ)
          ≤ (cutProfile |z (j + 1)| (t + z j) + cutProfile |z (j + 1)| (t - z j)) * C :=
        mul_le_mul hsum hwbig (Real.rpow_nonneg (abs_nonneg t) _) hcut0
      have htnn : (0 : ℝ) ≤ K * tailWeight (diamondNorm z - 7 / 4) t :=
        mul_nonneg hK0.le (tailWeight_nonneg _ t)
      rw [hG]
      linarith
  have hGint : Integrable G := by
    rw [hG]
    exact hGtail.add hGcut
  have hGval : ∫ t : ℝ, G t
      = K * (10 * (diamondNorm z - 7 / 4) ^ (-(1 / 5) : ℝ))
        + C * (12 * |z (j + 1)| ^ (-(1 / 5) : ℝ) + 12 * |z (j + 1)| ^ (-(1 / 5) : ℝ)) := by
    simp only [hG]
    rw [integral_add hGtail hGcut, integral_const_mul, integral_tailWeight hδ, integral_const_mul,
      integral_add (integrable_cutProfile_add hb (z j)) (integrable_cutProfile_sub hb (z j)),
      integral_cutProfile_add hb, integral_cutProfile_sub hb]
  have hint := (abs_integral_dir_le j z hGint hbnd).trans_eq hGval
  have hmeq : min |z j| |z (j + 1)| = |z (j + 1)| := min_eq_right hcase
  have hbp : (0 : ℝ) < |z (j + 1)| ^ (-(1 / 5) : ℝ) := Real.rpow_pos_of_pos hb _
  rw [hmeq]
  refine hint.trans (le_trans ?_ (final_arith hrpow.le hδpow.le hbp.le))
  have hKr : K ≤ 96 / 5 * diamondNorm z ^ (-(11 / 5) : ℝ) := by
    have h := rpow_neg_div_le hrpos (by norm_num : (0 : ℝ) < 2)
      (rpow_eleven_fifths_le (by norm_num) (by norm_num) : (2 : ℝ) ^ (11 / 5 : ℝ) ≤ 8)
    rw [hK]
    linarith
  have hCr : C ≤ 64 * diamondNorm z ^ (-(11 / 5) : ℝ) := by
    rw [hC]
    refine le_trans (Real.rpow_le_rpow_of_nonpos
      (show (0 : ℝ) < diamondNorm z / 4 by linarith)
      (show diamondNorm z / 4 ≤ |z j| / 2 by linarith) (by norm_num)) ?_
    exact rpow_neg_div_le hrpos (by norm_num : (0 : ℝ) < 4)
      (rpow_eleven_fifths_le (by norm_num) (by norm_num))
  have hfirst : K * (10 * (diamondNorm z - 7 / 4) ^ (-(1 / 5) : ℝ))
      ≤ 192 * (diamondNorm z ^ (-(11 / 5) : ℝ)
        * (diamondNorm z - 7 / 4) ^ (-(1 / 5) : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hKr hδpow.le
    linarith
  have hsecond : C * (12 * |z (j + 1)| ^ (-(1 / 5) : ℝ) + 12 * |z (j + 1)| ^ (-(1 / 5) : ℝ))
      ≤ 1536 * (diamondNorm z ^ (-(11 / 5) : ℝ) * |z (j + 1)| ^ (-(1 / 5) : ℝ)) := by
    have h := mul_le_mul_of_nonneg_right hCr hbp.le
    linarith
  linarith

/-- **One direction of the base generator outside the diamond.** -/
private theorem abs_integral_dir_truncBase_ext {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0)
    (hz : 7 / 4 < diamondNorm z) (j : Fin 2) :
    |∫ t : ℝ, secondDiff (truncBase (6 / 5) (7 / 4)) j z t * |t| ^ (-(1 + 6 / 5) : ℝ)|
      ≤ 1536 * diamondNorm z ^ (-(11 / 5) : ℝ)
        * ((diamondNorm z - 7 / 4) ^ (-(1 / 5) : ℝ)
          + (min |z j| |z (j + 1)|) ^ (-(1 / 5) : ℝ)) := by
  rcases le_total |z j| |z (j + 1)| with hcase | hcase
  · exact abs_integral_dir_ext_of_le h0 h1 hz j hcase
  · exact abs_integral_dir_ext_of_ge h0 h1 hz j hcase

end CenteredMaximal.Fractional

end

end
