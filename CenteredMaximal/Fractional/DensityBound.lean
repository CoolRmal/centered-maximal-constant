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

end CenteredMaximal.Fractional

end

end
