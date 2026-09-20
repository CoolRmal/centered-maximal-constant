/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.BetaIntegral
public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A rational lower bound for the six-fifths reserve constant

The order `α = 6/5` generator certificate divides out a positive constant and is left with the
positive intrinsic reserve

`S α = -2 * π * cot (π * α / 2) / (α * Β (α, α))`,

whose value at `α = 6/5` is `sixFifthsConst`.  Since `cot (3 * π / 5) = -tan (π / 10)` this is
`2 * π * tan (π / 10) / ((6/5) * Β (6/5, 6/5))`, and the certificate needs the explicit rational
lower bound `125337337 / 50000000 < sixFifthsConst`.  The true value is `2.50674674862…`, so the
margin is `8.6 * 10 ^ (-9)`: every ingredient has to be enclosed to a relative accuracy of about
`10 ^ (-10)`.

## Main results

* `lt_sixFifths_const`: `125337337 / 50000000 < sixFifthsConst`, the bound the certificate uses.
* `betaFun_sixFifths_lt`: `Β (6/5, 6/5) < 678678670710 / 1000000000000`, an overestimate by
  `4 * 10 ^ (-12)`.
* `tan_pi_div_ten_sq`, `lt_tan_pi_div_ten`: `tan (π / 10) ^ 2 = 1 - 2 * √5 / 5` and the resulting
  rational lower bound.
* `sixFifthsConst_eq_cot`: the cotangent form of the constant, which is the form the generator
  identity produces.

## The Beta enclosure

Mathlib has no numerical evaluation of `Real.Gamma`, so `Β (6/5, 6/5)` has to be bounded through
its Euler integral `∫₀¹ (x (1 - x)) ^ (1/5)`.  Expanding `(1 - x) ^ (1/5)` at `x = 0` and
integrating termwise is useless on all of `[0, 1]` — the binomial coefficients decay like
`n ^ (-6/5)`, so the truncation error decays like `N ^ (-11/5)` and `10 ^ 7` terms would be needed.
Folding the integral at `1/2` first, which the reflection `x ↦ 1 - x` does for free, restricts the
expansion point to `x ≤ 1/2` and makes the truncation error decay like `2 ^ (-N)`.

Only an *upper* bound on `Β` is needed, since `Β` sits in a denominator, and that direction needs
no tail estimate at all: writing `(1 - x) ^ (1/5) = ∑ n, c n * x ^ n` with
`c n = (-1) ^ n * (1/5 choose n)`, every coefficient after the first is *nonpositive*, so *every*
truncation of the series is an upper bound for the function (`rpow_one_sub_le_sum`).  Hence

`Β (6/5, 6/5) = 2 * ∫₀^{1/2} x ^ (1/5) * (1 - x) ^ (1/5)`
`            ≤ 2 * ∑_{n < 28} c n * ∫₀^{1/2} x ^ (n + 1/5)`
`            = (1/2) ^ (1/5) * ∑_{n < 28} c n * 2 ^ (-n) / (n + 6/5)`,

a rational multiple of `(1/2) ^ (1/5)`.  With `28` terms the overshoot is `3.7 * 10 ^ (-12)`, which
costs only `4 * 10 ^ (-11)` of the `8.6 * 10 ^ (-9)` margin.  The convergence of the binomial series
comes from `Real.one_add_rpow_hasFPowerSeriesOnBall_zero`; the coefficients are repackaged as
`fifthCoeff`, whose multiplicative recursion is `ringChoose_succ_mul`.

The remaining irrationalities are `(1/2) ^ (1/5)`, bounded by a fifth-power comparison, `√5`,
bounded by a square comparison, and `π`, bounded by `Real.pi_gt_d20`.
-/

@[expose] public section

noncomputable section

namespace CenteredMaximal.Fractional

open MeasureTheory

open scoped Real

/-! ## The algebraic value of `tan (π / 10)` -/

/-- `tan (π / 10)` is algebraic: its square is `1 - 2 / √5`.  This comes from the half-angle
identities at `π / 5` together with `Real.cos_pi_div_five`. -/
theorem tan_pi_div_ten_sq : Real.tan (π / 10) ^ 2 = 1 - 2 * √5 / 5 := by
  have h5 : (0 : ℝ) ≤ 5 := by norm_num
  have hsq : √5 ^ 2 = 5 := Real.sq_sqrt h5
  have hlt : √5 < 3 := by
    rw [show (3 : ℝ) = √9 from by rw [show (9 : ℝ) = 3 ^ 2 from by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt h5 (by norm_num)
  have hpos : (0 : ℝ) < √5 := Real.sqrt_pos.2 (by norm_num)
  have hdouble : (2 : ℝ) * (π / 10) = π / 5 := by ring
  have hcos : Real.cos (π / 5) = (1 + √5) / 4 := Real.cos_pi_div_five
  have hc : Real.cos (π / 10) ^ 2 = (5 + √5) / 8 := by
    have h := Real.cos_two_mul (π / 10)
    rw [hdouble, hcos] at h
    linarith
  have hs : Real.sin (π / 10) ^ 2 = (3 - √5) / 8 := by
    have h := Real.cos_two_mul_eq_one_sub (π / 10)
    rw [hdouble, hcos] at h
    linarith
  have hcpos : 0 < Real.cos (π / 10) := by
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [Real.tan_eq_sin_div_cos, div_pow, hs, hc]
  rw [div_eq_iff (by nlinarith)]
  nlinarith [hsq]

/-- A rational lower bound for `tan (π / 10) = 0.3249196962329…`, accurate to `10 ^ (-11)`. -/
theorem lt_tan_pi_div_ten : (32491969623 / 100000000000 : ℝ) < Real.tan (π / 10) := by
  have h5 : √5 < 22360679775 / 10000000000 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  have hpos : 0 < Real.tan (π / 10) := by
    refine Real.tan_pos_of_pos_of_lt_pi_div_two (by linarith [Real.pi_pos]) ?_
    linarith [Real.pi_pos]
  nlinarith [tan_pi_div_ten_sq, hpos, h5]

/-! ## The constant -/

/-- The positive intrinsic reserve of the order `6/5` generator,
`S (6/5) = 2 π tan (π / 10) / ((6/5) Β (6/5, 6/5)) = 2.50674674862…`. -/
def sixFifthsConst : ℝ := 2 * π * Real.tan (π / 10) / (6 / 5 * betaFun (6 / 5) (6 / 5))

/-- `cot (3 π / 5) = -tan (π / 10)`, because `3 π / 5 = π / 2 + π / 10`. -/
theorem cot_pi_mul_sixFifths_div_two : Real.cot (π * (6 / 5) / 2) = -Real.tan (π / 10) := by
  rw [show π * (6 / 5) / 2 = π / 2 + π / 10 from by ring, Real.cot_eq_cos_div_sin, Real.cos_add,
    Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.tan_eq_sin_div_cos]
  ring

/-- `sixFifthsConst` is the value at `α = 6/5` of the reserve constant
`S α = -2 π cot (π α / 2) / (α Β (α, α))`. -/
theorem sixFifthsConst_eq_cot :
    sixFifthsConst =
      -2 * π * Real.cot (π * (6 / 5) / 2) / (6 / 5 * betaFun (6 / 5) (6 / 5)) := by
  rw [sixFifthsConst, cot_pi_mul_sixFifths_div_two]
  ring

/-! ## The binomial coefficients of `(1 - t) ^ (1/5)` -/

/-- The coefficients of the binomial series of `(1 - t) ^ (1/5 : ℝ)`, that is
`fifthCoeff n = (-1) ^ n * (1/5 choose n)`, given by their multiplicative recursion. -/
def fifthCoeff : ℕ → ℝ
  | 0 => 1
  | n + 1 => fifthCoeff n * ((n : ℝ) - 1 / 5) / ((n : ℝ) + 1)

@[simp] theorem fifthCoeff_zero : fifthCoeff 0 = 1 := rfl

theorem fifthCoeff_succ (n : ℕ) :
    fifthCoeff (n + 1) = fifthCoeff n * ((n : ℝ) - 1 / 5) / ((n : ℝ) + 1) := rfl

/-- The multiplicative recursion of the generalized binomial coefficient. -/
theorem ringChoose_succ_mul (a : ℝ) (n : ℕ) :
    Ring.choose a (n + 1) * ((n : ℝ) + 1) = Ring.choose a n * (a - n) := by
  have hn : (n.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hfac : (((n + 1).factorial : ℕ) : ℝ) = ((n : ℝ) + 1) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [Ring.choose_eq_smul, Ring.choose_eq_smul, descPochhammer_succ_right, Polynomial.smeval_mul,
    Polynomial.smeval_sub, Polynomial.smeval_X, Polynomial.smeval_natCast, smul_eq_mul,
    smul_eq_mul, hfac]
  field_simp
  ring

theorem fifthCoeff_eq_choose (n : ℕ) :
    fifthCoeff n = Ring.choose (1 / 5 : ℝ) n * (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [fifthCoeff_succ, ih, div_eq_iff hn1, pow_succ]
    linear_combination ((-1 : ℝ) ^ n) * ringChoose_succ_mul (1 / 5 : ℝ) n

/-- Every coefficient of the binomial series of `(1 - t) ^ (1/5)` after the constant term is
nonpositive.  This is what makes each truncation an upper bound for the function. -/
theorem fifthCoeff_nonpos {n : ℕ} (hn : 1 ≤ n) : fifthCoeff n ≤ 0 := by
  induction n with
  | zero => omega
  | succ m ih =>
    have hm2 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [fifthCoeff_succ]
      norm_num
    · have hm' : fifthCoeff m ≤ 0 := ih hm
      have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      rw [fifthCoeff_succ, div_le_iff₀ hm2]
      nlinarith

/-- The binomial series of `(1 - t) ^ (1/5 : ℝ)`, from
`Real.one_add_rpow_hasFPowerSeriesOnBall_zero` at the point `-t`. -/
theorem hasSum_fifthCoeff {t : ℝ} (ht : |t| < 1) :
    HasSum (fun n => fifthCoeff n * t ^ n) ((1 - t) ^ (1 / 5 : ℝ)) := by
  have hmem : (-t) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [mem_eball_zero_iff, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_lt_one, abs_neg]
    exact ht
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := 1 / 5)).hasSum hmem
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    zero_add] at h
  rw [show (1 : ℝ) + -t = 1 - t from by ring] at h
  refine h.congr_fun fun n => ?_
  rw [fifthCoeff_eq_choose, neg_pow]
  ring

/-- **Every truncation of the binomial series overestimates `(1 - t) ^ (1/5)`** on `[0, 1)`:
the omitted tail has only nonpositive terms. -/
theorem rpow_one_sub_le_sum {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) {N : ℕ} (hN : 1 ≤ N) :
    (1 - t) ^ (1 / 5 : ℝ) ≤ ∑ n ∈ Finset.range N, fifthCoeff n * t ^ n := by
  have habs : |t| < 1 := by rwa [abs_of_nonneg ht0]
  have hsum := hasSum_fifthCoeff habs
  have hsplit := hsum.summable.sum_add_tsum_nat_add N
  rw [hsum.tsum_eq] at hsplit
  have htail : ∑' i : ℕ, fifthCoeff (i + N) * t ^ (i + N) ≤ 0 := by
    refine tsum_nonpos fun i => ?_
    have h1 : fifthCoeff (i + N) ≤ 0 := fifthCoeff_nonpos (le_trans hN (Nat.le_add_left N i))
    have h2 : (0 : ℝ) ≤ t ^ (i + N) := pow_nonneg ht0 _
    nlinarith
  linarith

/-! ## The Beta integral -/

/-- The pointwise bound that is integrated: on `[0, 1/2]` the Beta integrand is dominated by a
finite sum of pure powers. -/
theorem rpow_mul_le_sum {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) {N : ℕ} (hN : 1 ≤ N) :
    x ^ (1 / 5 : ℝ) * (1 - x) ^ (1 / 5 : ℝ)
      ≤ ∑ n ∈ Finset.range N, fifthCoeff n * x ^ ((n : ℝ) + 1 / 5) := by
  have hkey := rpow_one_sub_le_sum hx0 (by linarith : x < 1) hN
  have hxp : (0 : ℝ) ≤ x ^ (1 / 5 : ℝ) := Real.rpow_nonneg hx0 _
  calc x ^ (1 / 5 : ℝ) * (1 - x) ^ (1 / 5 : ℝ)
      ≤ x ^ (1 / 5 : ℝ) * ∑ n ∈ Finset.range N, fifthCoeff n * x ^ n :=
        mul_le_mul_of_nonneg_left hkey hxp
    _ = ∑ n ∈ Finset.range N, fifthCoeff n * x ^ ((n : ℝ) + 1 / 5) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Real.rpow_add' hx0 (by positivity), Real.rpow_natCast]
        ring

/-- The Beta integrand is interval integrable on the left half of the unit interval. -/
theorem intervalIntegrable_betaIntegrand :
    IntervalIntegrable (fun x : ℝ => x ^ (1 / 5 : ℝ) * (1 - x) ^ (1 / 5 : ℝ)) volume 0 (1 / 2) := by
  refine (intervalIntegral.intervalIntegrable_rpow'
    (by norm_num : (-1 : ℝ) < 1 / 5)).mul_continuousOn ?_
  refine ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl ?_
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hx
  exact ne_of_gt (by linarith [hx.2] : (0 : ℝ) < 1 - x)

/-- The Beta integrand is interval integrable on the right half of the unit interval. -/
theorem intervalIntegrable_betaIntegrand' :
    IntervalIntegrable (fun x : ℝ => x ^ (1 / 5 : ℝ) * (1 - x) ^ (1 / 5 : ℝ))
      volume (1 / 2) 1 := by
  have hsing : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (1 / 5 : ℝ)) volume (1 / 2) 1 := by
    have h := (intervalIntegral.intervalIntegrable_rpow' (r := 1 / 5) (a := 1 / 2) (b := 0)
      (by norm_num)).comp_sub_left 1
    rw [show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num, sub_zero] at h
    exact h
  refine hsing.continuousOn_mul ?_
  refine ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl ?_
  rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) / 2 ≤ 1)] at hx
  exact ne_of_gt (by linarith [hx.1] : (0 : ℝ) < x)

/-- The dominating finite sum is interval integrable on `[0, 1/2]`. -/
theorem intervalIntegrable_sum (N : ℕ) :
    IntervalIntegrable (fun x : ℝ => ∑ n ∈ Finset.range N, fifthCoeff n * x ^ ((n : ℝ) + 1 / 5))
      volume 0 (1 / 2) := by
  have h : ∀ n ∈ Finset.range N,
      IntervalIntegrable (fun x : ℝ => fifthCoeff n * x ^ ((n : ℝ) + 1 / 5)) volume 0 (1 / 2) := by
    intro n _
    have hr : (-1 : ℝ) < (n : ℝ) + 1 / 5 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact (intervalIntegral.intervalIntegrable_rpow' hr).const_mul _
  have heq : (fun x : ℝ => ∑ n ∈ Finset.range N, fifthCoeff n * x ^ ((n : ℝ) + 1 / 5))
      = ∑ n ∈ Finset.range N, fun x : ℝ => fifthCoeff n * x ^ ((n : ℝ) + 1 / 5) := by
    funext x
    rw [Finset.sum_apply]
  rw [heq]
  exact IntervalIntegrable.sum (μ := volume) (a := 0) (b := 1 / 2) (Finset.range N) h

/-- Folding the Euler integral at `1/2`: the reflection `x ↦ 1 - x` fixes the integrand. -/
theorem betaFun_sixFifths_eq :
    betaFun (6 / 5) (6 / 5)
      = 2 * ∫ x in (0:ℝ)..(1 / 2), x ^ (1 / 5 : ℝ) * (1 - x) ^ (1 / 5 : ℝ) := by
  have hb := betaFun_eq_integral (a := 6 / 5) (b := 6 / 5) (by norm_num) (by norm_num)
  rw [show (6 / 5 - 1 : ℝ) = 1 / 5 from by norm_num] at hb
  have hsym : ∫ x in (1 / 2:ℝ)..1, x ^ (1 / 5 : ℝ) * (1 - x) ^ (1 / 5 : ℝ)
      = ∫ x in (0:ℝ)..(1 / 2), x ^ (1 / 5 : ℝ) * (1 - x) ^ (1 / 5 : ℝ) := by
    have h := intervalIntegral.integral_comp_sub_left (a := 1 / 2) (b := 1)
      (fun x : ℝ => x ^ (1 / 5 : ℝ) * (1 - x) ^ (1 / 5 : ℝ)) 1
    rw [show (1 : ℝ) - 1 = 0 from by norm_num, show (1 : ℝ) - 1 / 2 = 1 / 2 from by norm_num] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [sub_sub_cancel]
    ring
  rw [hb, ← intervalIntegral.integral_add_adjacent_intervals intervalIntegrable_betaIntegrand
    intervalIntegrable_betaIntegrand', hsym]
  ring

/-- Termwise integration of the dominating sum. -/
theorem integral_sum_eq (N : ℕ) :
    (∫ x in (0:ℝ)..(1 / 2), ∑ n ∈ Finset.range N, fifthCoeff n * x ^ ((n : ℝ) + 1 / 5))
      = (1 / 2 : ℝ) ^ (1 / 5 : ℝ) *
        ∑ n ∈ Finset.range N, fifthCoeff n * ((1 / 2 : ℝ) ^ (n + 1) / ((n : ℝ) + 6 / 5)) := by
  have h : ∀ n ∈ Finset.range N,
      IntervalIntegrable (fun x : ℝ => fifthCoeff n * x ^ ((n : ℝ) + 1 / 5)) volume 0 (1 / 2) := by
    intro n _
    have hr : (-1 : ℝ) < (n : ℝ) + 1 / 5 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    exact (intervalIntegral.intervalIntegrable_rpow' hr).const_mul _
  rw [intervalIntegral.integral_finsetSum h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hr : (-1 : ℝ) < (n : ℝ) + 1 / 5 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hn6 : (0 : ℝ) < (n : ℝ) + 6 / 5 := by positivity
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith), sub_zero,
    show (n : ℝ) + 1 / 5 + 1 = ((n + 1 : ℕ) : ℝ) + 1 / 5 from by push_cast; ring,
    Real.rpow_add (by norm_num : (0:ℝ) < 1 / 2), Real.rpow_natCast,
    show ((n + 1 : ℕ) : ℝ) + 1 / 5 = (n : ℝ) + 6 / 5 from by push_cast; ring]
  field_simp

/-- The `28`-term truncation, as an exact rational bound. -/
theorem sum_range_twentyEight_le :
    ∑ n ∈ Finset.range 28, fifthCoeff n * ((1 / 2 : ℝ) ^ (n + 1) / ((n : ℝ) + 6 / 5))
      ≤ 77959707261234050183 / 200000000000000000000 := by
  norm_num [Finset.sum_range_succ, fifthCoeff]

/-- The `28`-term truncation is positive; needed to multiply the two upper bounds. -/
theorem sum_range_twentyEight_nonneg :
    (0 : ℝ) ≤ ∑ n ∈ Finset.range 28,
      fifthCoeff n * ((1 / 2 : ℝ) ^ (n + 1) / ((n : ℝ) + 6 / 5)) := by
  norm_num [Finset.sum_range_succ, fifthCoeff]

/-- A rational upper bound for `(1/2) ^ (1/5) = 0.87055056329…`, by a fifth-power comparison. -/
theorem half_rpow_fifth_le : (1 / 2 : ℝ) ^ (1 / 5 : ℝ) ≤ 8705505633 / 10000000000 := by
  have h5 : ((1 / 2 : ℝ) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) = 1 / 2 := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ (1 / 5 : ℝ)) 5, ← Real.rpow_mul (by norm_num)]
    norm_num
  refine le_of_pow_le_pow_left₀ (n := 5) (by norm_num) (by norm_num) ?_
  rw [h5]
  norm_num

/-- **A rational upper bound for `Β (6/5, 6/5) = 0.678678670706026…`**, an overestimate by
`4 * 10 ^ (-12)`, of which `3.7 * 10 ^ (-12)` is the series truncation. -/
theorem betaFun_sixFifths_lt :
    betaFun (6 / 5) (6 / 5) < 678678670710 / 1000000000000 := by
  have hmono : (∫ x in (0:ℝ)..(1 / 2), x ^ (1 / 5 : ℝ) * (1 - x) ^ (1 / 5 : ℝ))
      ≤ ∫ x in (0:ℝ)..(1 / 2), ∑ n ∈ Finset.range 28, fifthCoeff n * x ^ ((n : ℝ) + 1 / 5) :=
    intervalIntegral.integral_mono_on (by norm_num) intervalIntegrable_betaIntegrand
      (intervalIntegrable_sum 28) fun x hx => rpow_mul_le_sum hx.1 hx.2 (by norm_num)
  rw [integral_sum_eq 28] at hmono
  have hprod := mul_le_mul half_rpow_fifth_le sum_range_twentyEight_le
    sum_range_twentyEight_nonneg (by norm_num : (0 : ℝ) ≤ 8705505633 / 10000000000)
  have hnum : (8705505633 / 10000000000 : ℝ) * (77959707261234050183 / 200000000000000000000)
      < 678678670710 / 2000000000000 := by norm_num
  rw [betaFun_sixFifths_eq]
  linarith

/-! ## The certified lower bound -/

/-- **The rational lower bound the `α = 6/5` certificate uses**:
`2.50674674 < S (6/5) = 2.5067467486246187…`. -/
theorem lt_sixFifths_const : (125337337 / 50000000 : ℝ) < sixFifthsConst := by
  have hB : 0 < betaFun (6 / 5) (6 / 5) := betaFun_pos (by norm_num) (by norm_num)
  have hden : (0 : ℝ) < 6 / 5 * betaFun (6 / 5) (6 / 5) := by positivity
  rw [sixFifthsConst, lt_div_iff₀ hden]
  have htan : (0 : ℝ) < Real.tan (π / 10) := by linarith [lt_tan_pi_div_ten]
  calc (125337337 / 50000000 : ℝ) * (6 / 5 * betaFun (6 / 5) (6 / 5))
      ≤ 125337337 / 50000000 * (6 / 5 * (678678670710 / 1000000000000)) := by
        nlinarith [betaFun_sixFifths_lt]
    _ < 2 * (314159265358979323846 / 100000000000000000000)
        * (32491969623 / 100000000000) := by norm_num
    _ ≤ 2 * π * Real.tan (π / 10) := by
        nlinarith [Real.pi_gt_d20, lt_tan_pi_div_ten, htan, Real.pi_pos]

end CenteredMaximal.Fractional

end

end
