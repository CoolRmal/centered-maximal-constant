/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.TailRadial
public import CenteredMaximal.Fractional.SixFifthsArith

/-!
# The tail series: an explicit lower bound for the radial reserve

`CenteredMaximal.Fractional.jumpGen_truncBase_ge_radial` bounds the generator of the truncated
diamond base below by the intrinsic power term plus the *radial reserve*

`2 ∫ t : ℝ, tailRadial α R r t * |t| ^ (-(1 + α))`,     `r = diamondNorm z`,

where `tailRadial α R r t = (R ^ (-α) - (r + |t|) ^ (-α))₊`.  The leaf checks of the `α = 6/5`
comparison certificate read that reserve as a *number*, so it has to be minorised by something
rationally computable.  This file does that.

## The identity behind the bound

The positive part is supported on `|t| > R - r`, so by symmetry the reserve integral is
`2 ∫_{R-r}^∞ (R ^ (-α) - (r + t) ^ (-α)) t ^ (-1-α) dt`; substituting `q = r + t` turns it into
`2 ∫_R^∞ (R ^ (-α) - q ^ (-α)) (q - r) ^ (-1-α) dq`; expanding
`(q - r) ^ (-1-α) = q ^ (-1-α) ∑ n, binomCoeff α n * (r / q) ^ n` (legitimate since `q ≥ R > r`)
and integrating termwise against `∫_R^∞ q ^ (-1-α-n) dq = R ^ (-α-n) / (α + n)` and
`∫_R^∞ q ^ (-1-2α-n) dq = R ^ (-2α-n) / (2α + n)` gives

`∫ t : ℝ, tailRadial α R r t * |t| ^ (-(1+α)) = 2 * R ^ (-2*α) * ∑' n, tailCoeff α n * (r/R) ^ n`,

`tailCoeff α n = binomCoeff α n * α / ((α + n) * (2 * α + n))`, `binomCoeff α n = (1+α)_n / n!`.

At `α = 6/5`, `R = 7/4`, `r = 1.7` both sides are `2.081869857336553…`.

## Only the lower bound is proved, and it needs no remainder estimate

Every `tailCoeff α n` is *positive*, so any partial sum is already a lower bound and the closed
form, the convergence and the tail estimate are all unnecessary.  Accordingly the proof never
forms the infinite series: it dominates the integrand pointwise by the *finite* sum
`∑_{n < K} binomCoeff α n * r ^ n * (R ^ (-α) * (r+q) ^ (-(α+n)-1) - (r+q) ^ (-(2α+n)-1))`
— using only the finite binomial domination `∑_{n < K} binomCoeff α n * x ^ n ≤ (1-x) ^ (-(1+α))`,
which holds because the omitted terms are nonnegative — and integrates that finite sum termwise.

## Main results

* `binomCoeff`, `binomCoeff_pos`, `sum_le_one_sub_rpow`: the coefficients of `(1-x) ^ (-(1+α))`
  and the finite domination they satisfy, in the style of `fifthCoeff` and `rpow_one_sub_le_sum`.
* `tailCoeff`, `tailCoeff_pos`, `tailCoeff_succ`: the tail coefficients and their recursion.
* `integral_tailRadial_ge`: **the bound the leaf checks use**, that every partial sum
  `2 * R ^ (-2*α) * ∑_{n < K} tailCoeff α n * (r/R) ^ n` minorises the reserve integral.
* `tailCoeffQ`, `tailCoeffQ_eq`, `tailCoeffQ_le`: the coefficients at `α = 6/5` are *exactly*
  rational, given by a multiplicative recursion rather than by (rapidly growing) literals.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter

open scoped Topology

namespace CenteredMaximal.Fractional

/-! ### The binomial coefficients of `(1 - x) ^ (-(1 + α))` -/

/-- The coefficients of the binomial series of `(1 - x) ^ (-(1 + α))`, that is the rising
factorial quotient `binomCoeff α n = (1 + α)_n / n!`, given by its multiplicative recursion. -/
def binomCoeff (α : ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => binomCoeff α n * (1 + α + n) / ((n : ℝ) + 1)

@[simp] theorem binomCoeff_zero (α : ℝ) : binomCoeff α 0 = 1 := rfl

theorem binomCoeff_succ (α : ℝ) (n : ℕ) :
    binomCoeff α (n + 1) = binomCoeff α n * (1 + α + n) / ((n : ℝ) + 1) := rfl

/-- Every coefficient is positive: the recursion multiplies by `(1 + α + n) / (n + 1) > 0`. -/
theorem binomCoeff_pos {α : ℝ} (hα : 0 < α) (n : ℕ) : 0 < binomCoeff α n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    rw [binomCoeff_succ]
    exact div_pos (mul_pos ih (by linarith)) (by linarith)

theorem binomCoeff_nonneg {α : ℝ} (hα : 0 < α) (n : ℕ) : 0 ≤ binomCoeff α n :=
  (binomCoeff_pos hα n).le

/-- `binomCoeff α n` is the `n`-th generalised binomial coefficient of `-(1 + α)`, up to sign.
The recursion `ringChoose_succ_mul` at `a = -(1 + α)` reads `d (n+1) = d n * (1+α+n) / (n+1)`. -/
theorem binomCoeff_eq_choose (α : ℝ) (n : ℕ) :
    binomCoeff α n = Ring.choose (-(1 + α)) n * (-1) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    rw [binomCoeff_succ, ih, div_eq_iff hn1, pow_succ]
    linear_combination ((-1 : ℝ) ^ n) * ringChoose_succ_mul (-(1 + α)) n

/-- The binomial series of `(1 - x) ^ (-(1 + α))`, from
`Real.one_add_rpow_hasFPowerSeriesOnBall_zero` at the point `-x`. -/
theorem hasSum_binomCoeff (α : ℝ) {x : ℝ} (hx : |x| < 1) :
    HasSum (fun n => binomCoeff α n * x ^ n) ((1 - x) ^ (-(1 + α))) := by
  have hmem : (-x) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [mem_eball_zero_iff, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_lt_one, abs_neg]
    exact hx
  have h := (Real.one_add_rpow_hasFPowerSeriesOnBall_zero (a := -(1 + α))).hasSum hmem
  simp only [binomialSeries, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    zero_add] at h
  rw [show (1 : ℝ) + -x = 1 - x from by ring] at h
  refine h.congr_fun fun n => ?_
  rw [binomCoeff_eq_choose, neg_pow]
  ring

/-- **Every truncation of the binomial series underestimates `(1 - x) ^ (-(1 + α))`** on `[0, 1)`:
the omitted tail has only nonnegative terms.  This is the only analytic input to the reserve
bound — no remainder estimate is needed, because the bound goes the easy way. -/
theorem sum_le_one_sub_rpow {α x : ℝ} (hα : 0 < α) (hx0 : 0 ≤ x) (hx1 : x < 1) (K : ℕ) :
    ∑ n ∈ Finset.range K, binomCoeff α n * x ^ n ≤ (1 - x) ^ (-(1 + α)) := by
  have habs : |x| < 1 := by rwa [abs_of_nonneg hx0]
  have hsum := hasSum_binomCoeff α habs
  have hsplit := hsum.summable.sum_add_tsum_nat_add K
  rw [hsum.tsum_eq] at hsplit
  have htail : (0 : ℝ) ≤ ∑' i : ℕ, binomCoeff α (i + K) * x ^ (i + K) :=
    tsum_nonneg fun i => mul_nonneg (binomCoeff_nonneg hα _) (pow_nonneg hx0 _)
  linarith

/-! ### The tail coefficients -/

/-- The `n`-th coefficient of the tail series,
`tailCoeff α n = ((1 + α)_n / n!) * α / ((α + n) * (2 * α + n))`. -/
def tailCoeff (α : ℝ) (n : ℕ) : ℝ := binomCoeff α n * α / ((α + n) * (2 * α + n))

/-- **Every tail coefficient is positive**, which is why a partial sum already bounds the
reserve integral below. -/
theorem tailCoeff_pos {α : ℝ} (hα : 0 < α) (n : ℕ) : 0 < tailCoeff α n := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact div_pos (mul_pos (binomCoeff_pos hα n) hα) (by positivity)

theorem tailCoeff_zero {α : ℝ} (hα : α ≠ 0) : tailCoeff α 0 = 1 / (2 * α) := by
  have h2 : (2 : ℝ) * α ≠ 0 := by simpa using hα
  rw [tailCoeff, binomCoeff_zero, Nat.cast_zero, add_zero, add_zero, one_mul,
    div_eq_div_iff (mul_ne_zero hα h2) h2]
  ring

/-- The multiplicative recursion of the tail coefficients:
`a (n+1) = a n * (1+α+n)/(n+1) * ((α+n)(2α+n))/((α+n+1)(2α+n+1))`. -/
theorem tailCoeff_succ {α : ℝ} (hα : 0 < α) (n : ℕ) :
    tailCoeff α (n + 1) = tailCoeff α n * (1 + α + n) / ((n : ℝ) + 1) *
      (((α + n) * (2 * α + n)) / ((α + n + 1) * (2 * α + n + 1))) := by
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have h1 : (0 : ℝ) < α + n := by positivity
  have h2 : (0 : ℝ) < 2 * α + n := by positivity
  rw [tailCoeff, tailCoeff, binomCoeff_succ]
  push_cast
  field_simp
  ring

/-! ### Shifted half-line power integrals -/

/-- `t ↦ -((r + t) ^ (-p) / p)` is a primitive of `t ↦ (r + t) ^ (-p - 1)`. -/
theorem hasDerivAt_shift_rpow {r p x : ℝ} (hp : p ≠ 0) (hx : 0 < r + x) :
    HasDerivAt (fun t : ℝ => -((r + t) ^ (-p) / p)) ((r + x) ^ (-p - 1)) x := by
  have h1 : HasDerivAt (fun t : ℝ => r + t) 1 x := (hasDerivAt_id x).const_add r
  have h2 := h1.rpow_const (p := -p) (Or.inl hx.ne')
  have h3 : HasDerivAt (fun t : ℝ => -((r + t) ^ (-p) / p))
      (-(1 * -p * (r + x) ^ (-p - 1) / p)) x := (h2.div_const p).neg
  have hval : -(1 * -p * (r + x) ^ (-p - 1) / p) = (r + x) ^ (-p - 1) := by
    field_simp
  rwa [hval] at h3

/-- The primitive tends to `0` at `+∞`. -/
theorem tendsto_shift_rpow {r p : ℝ} (hp : 0 < p) :
    Tendsto (fun t : ℝ => -((r + t) ^ (-p) / p)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => r + t) atTop atTop :=
    tendsto_atTop_add_const_left atTop r tendsto_id
  have h2 := (tendsto_rpow_neg_atTop hp).comp h1
  simpa using (h2.div_const p).neg

/-- The shifted power `t ↦ (r + t) ^ (-p - 1)` is integrable on `(b, ∞)` as soon as `r + b > 0`
and `p > 0`: it is the derivative of a bounded monotone primitive. -/
theorem integrableOn_Ioi_shift_rpow {r b p : ℝ} (hp : 0 < p) (hb : 0 < r + b) :
    IntegrableOn (fun t : ℝ => (r + t) ^ (-p - 1)) (Ioi b) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x hx => hasDerivAt_shift_rpow hp.ne' (by
    have : b ≤ x := hx
    linarith)) (fun x hx => Real.rpow_nonneg (by
      have : b < x := hx
      linarith) _) (tendsto_shift_rpow hp)

/-- **The shifted half-line power integral**, `∫_b^∞ (r + t) ^ (-p-1) dt = (r + b) ^ (-p) / p`. -/
theorem integral_Ioi_shift_rpow {r b p : ℝ} (hp : 0 < p) (hb : 0 < r + b) :
    (∫ t in Ioi b, (r + t) ^ (-p - 1)) = (r + b) ^ (-p) / p := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (g := fun t : ℝ => -((r + t) ^ (-p) / p)) (g' := fun t : ℝ => (r + t) ^ (-p - 1)) (l := 0)
    (fun x hx => hasDerivAt_shift_rpow hp.ne' (by
      have : b ≤ x := hx
      linarith))
    (fun x hx => Real.rpow_nonneg (by
      have : b < x := hx
      linarith) _) (tendsto_shift_rpow hp)
  rw [h]
  ring

/-! ### The radial integrand -/

/-- The radial profile of the reserve integrand: the integrand of the reserve is
`t ↦ tailIntegrand α R r |t|`. -/
def tailIntegrand (α R r q : ℝ) : ℝ := tailRadial α R r q * q ^ (-(1 + α))

theorem tailIntegrand_abs (α R r t : ℝ) :
    tailIntegrand α R r |t| = tailRadial α R r t * |t| ^ (-(1 + α)) := by
  rw [tailIntegrand, tailRadial, tailRadial, abs_abs]

theorem tailIntegrand_nonneg (α R r q : ℝ) (hq : 0 ≤ q) : 0 ≤ tailIntegrand α R r q :=
  mul_nonneg (tailRadial_nonneg _ _ _ _) (Real.rpow_nonneg hq _)

/-- **The reserve integral is twice a half-line integral**, the integrand being even. -/
theorem integral_tailRadial_eq (α R r : ℝ) :
    (∫ t : ℝ, tailRadial α R r t * |t| ^ (-(1 + α)))
      = 2 * ∫ q in Ioi (0 : ℝ), tailIntegrand α R r q := by
  rw [← integral_comp_abs (f := tailIntegrand α R r)]
  simp only [tailIntegrand_abs]

/-- The radial integrand vanishes where the tail does, namely on `r + q ≤ R`. -/
theorem tailIntegrand_eq_zero {α R r q : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hq : 0 < q)
    (hqR : r + q ≤ R) : tailIntegrand α R r q = 0 := by
  have habs : |q| = q := abs_of_pos hq
  have hpos : 0 < r + |q| := by rw [habs]; linarith
  have hleR : r + |q| ≤ R := by rw [habs]; exact hqR
  have hle : R ^ (-α) - (r + |q|) ^ (-α) ≤ 0 := by
    have := Real.rpow_le_rpow_of_nonpos hpos hleR (neg_nonpos.2 hα.le)
    linarith
  rw [tailIntegrand, tailRadial, max_eq_right hle, zero_mul]

/-- Since the integrand vanishes on `(0, R - r]`, the half-line integral may be taken from
`R - r` instead of from `0`.  Comparing indicators avoids any integrability hypothesis. -/
theorem integral_Ioi_tailIntegrand {α R r : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hrR : r < R) :
    (∫ q in Ioi (0 : ℝ), tailIntegrand α R r q)
      = ∫ q in Ioi (R - r), tailIntegrand α R r q := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only [indicator_apply, mem_Ioi]
  rcases lt_or_ge (R - r) q with h | h
  · rw [if_pos (by linarith : (0 : ℝ) < q), if_pos h]
  · rw [if_neg (by linarith : ¬R - r < q)]
    rcases le_or_gt q 0 with h0 | h0
    · rw [if_neg (by linarith : ¬(0 : ℝ) < q)]
    · rw [if_pos h0, tailIntegrand_eq_zero hα hr h0 (by linarith)]

/-! ### The pointwise domination by a finite sum -/

/-- **The pointwise domination**, in the form in which the shifted variable `u = r + q` is free.
The finite binomial sum is dominated by the tail integrand because
`∑_{n < K} binomCoeff α n * (r/u) ^ n ≤ (1 - r/u) ^ (-(1+α))` and `u * (1 - r/u) = u - r`. -/
theorem tailSum_le_aux {α R r u : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hru : r < u) (K : ℕ) :
    ∑ n ∈ Finset.range K, binomCoeff α n * r ^ n *
        (R ^ (-α) * u ^ (-(α + (n : ℝ)) - 1) - u ^ (-(2 * α + (n : ℝ)) - 1))
      ≤ max (R ^ (-α) - u ^ (-α)) 0 * (u - r) ^ (-(1 + α)) := by
  have hu : 0 < u := lt_of_le_of_lt hr hru
  have hx0 : 0 ≤ r / u := div_nonneg hr hu.le
  have hx1 : r / u < 1 := (div_lt_one hu).2 hru
  have hup : (0 : ℝ) < u ^ (-(1 + α)) := Real.rpow_pos_of_pos hu _
  have hS0 : 0 ≤ ∑ n ∈ Finset.range K, binomCoeff α n * (r / u) ^ n :=
    Finset.sum_nonneg fun n _ => mul_nonneg (binomCoeff_nonneg hα n) (pow_nonneg hx0 n)
  have hfac : (u - r) ^ (-(1 + α)) = u ^ (-(1 + α)) * (1 - r / u) ^ (-(1 + α)) := by
    rw [← Real.mul_rpow hu.le (by linarith : (0 : ℝ) ≤ 1 - r / u)]
    congr 1
    field_simp
  have hSle : u ^ (-(1 + α)) * ∑ n ∈ Finset.range K, binomCoeff α n * (r / u) ^ n
      ≤ (u - r) ^ (-(1 + α)) := by
    rw [hfac]
    exact mul_le_mul_of_nonneg_left (sum_le_one_sub_rpow hα hx0 hx1 K) hup.le
  have hsum : ∑ n ∈ Finset.range K, binomCoeff α n * r ^ n *
      (R ^ (-α) * u ^ (-(α + (n : ℝ)) - 1) - u ^ (-(2 * α + (n : ℝ)) - 1))
      = (R ^ (-α) - u ^ (-α)) *
        (u ^ (-(1 + α)) * ∑ n ∈ Finset.range K, binomCoeff α n * (r / u) ^ n) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hun : (u : ℝ) ^ n ≠ 0 := by positivity
    have e1 : u ^ (-(2 * α + (n : ℝ)) - 1) = u ^ (-α) * u ^ (-(α + (n : ℝ)) - 1) := by
      rw [← Real.rpow_add hu]
      congr 1
      ring
    have e2 : u ^ (-(α + (n : ℝ)) - 1) = u ^ (-(1 + α)) * (u ^ n)⁻¹ := by
      rw [← Real.rpow_natCast u n, ← Real.rpow_neg hu.le, ← Real.rpow_add hu]
      congr 1
      ring
    rw [e1, e2, div_pow]
    field_simp
  rw [hsum]
  rcases le_or_gt 0 (R ^ (-α) - u ^ (-α)) with h | h
  · rw [max_eq_left h]
    exact mul_le_mul_of_nonneg_left hSle h
  · rw [max_eq_right h.le, zero_mul]
    nlinarith [mul_nonneg hup.le hS0]

/-- The pointwise domination of the radial integrand by the finite tail sum. -/
theorem tailSum_le_tailIntegrand {α R r q : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hq : 0 < q) (K : ℕ) :
    ∑ n ∈ Finset.range K, binomCoeff α n * r ^ n *
        (R ^ (-α) * (r + q) ^ (-(α + (n : ℝ)) - 1) - (r + q) ^ (-(2 * α + (n : ℝ)) - 1))
      ≤ tailIntegrand α R r q := by
  have h := tailSum_le_aux (R := R) hα hr (by linarith : r < r + q) K
  rw [show r + q - r = q from by ring] at h
  rw [tailIntegrand, tailRadial, abs_of_pos hq]
  exact h

/-! ### Integrability -/

/-- The radial integrand is integrable on `(R - r, ∞)`: it is nonnegative, continuous there, and
dominated by `R ^ (-α) * q ^ (-(1 + α))`. -/
theorem integrableOn_tailIntegrand {α R r : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (hrR : r < R) :
    IntegrableOn (tailIntegrand α R r) (Ioi (R - r)) := by
  have hpos : 0 < R - r := by linarith
  have hq0 : ∀ q ∈ Ioi (R - r), (0 : ℝ) < q := fun q hq => lt_trans hpos hq
  have hg : IntegrableOn (fun q : ℝ => R ^ (-α) * q ^ (-(1 + α))) (Ioi (R - r)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + α) < -1) hpos).const_mul _
  have h1 : ContinuousOn (fun q : ℝ => r + |q|) (Ioi (R - r)) :=
    continuousOn_const.add continuous_abs.continuousOn
  have h2 : ContinuousOn (fun q : ℝ => (r + |q|) ^ (-α)) (Ioi (R - r)) :=
    h1.rpow_const fun q hq => Or.inl (by
      have habs : |q| = q := abs_of_pos (hq0 q hq)
      have hq1 : R - r < q := hq
      simp only [habs]
      exact ne_of_gt (by linarith))
  have h3 : ContinuousOn (fun q : ℝ => q ^ (-(1 + α))) (Ioi (R - r)) :=
    continuousOn_id.rpow_const fun q hq => Or.inl (hq0 q hq).ne'
  have hcont : ContinuousOn
      (fun q : ℝ => max (R ^ (-α) - (r + |q|) ^ (-α)) 0 * q ^ (-(1 + α))) (Ioi (R - r)) :=
    ((continuousOn_const.sub h2).sup continuousOn_const).mul h3
  refine hg.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun q hq => ?_))
  have hq' : R - r < q := hq
  have hq0 : 0 < q := by linarith
  have hqp : (0 : ℝ) ≤ q ^ (-(1 + α)) := Real.rpow_nonneg hq0.le _
  have hmax : max (R ^ (-α) - (r + |q|) ^ (-α)) 0 ≤ R ^ (-α) := by
    refine max_le (by linarith [Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ r + |q|) (-α)])
      (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ R) _)
  rw [Real.norm_eq_abs, abs_of_nonneg (tailIntegrand_nonneg α R r q hq0.le), tailIntegrand,
    tailRadial]
  exact mul_le_mul_of_nonneg_right hmax hqp

/-- The finite tail sum is integrable on `(R - r, ∞)`. -/
theorem integrableOn_tailSum {α R r : ℝ} (hα : 0 < α) (hR : 0 < R) (K : ℕ) :
    IntegrableOn (fun q : ℝ => ∑ n ∈ Finset.range K, binomCoeff α n * r ^ n *
      (R ^ (-α) * (r + q) ^ (-(α + (n : ℝ)) - 1) - (r + q) ^ (-(2 * α + (n : ℝ)) - 1)))
      (Ioi (R - r)) := by
  have hb : (0 : ℝ) < r + (R - r) := by linarith
  refine integrable_finsetSum _ fun n _ => ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  exact (((integrableOn_Ioi_shift_rpow (p := α + n) (by positivity) hb).const_mul
    (R ^ (-α))).sub (integrableOn_Ioi_shift_rpow (p := 2 * α + n) (by positivity) hb)).const_mul _

/-! ### Termwise integration -/

/-- **Termwise integration of the finite tail sum.**  Each of the two shifted powers integrates to
an explicit power of `R`, and their difference produces exactly `tailCoeff α n`. -/
theorem integral_Ioi_tailSum {α R r : ℝ} (hα : 0 < α) (hR : 0 < R) (K : ℕ) :
    (∫ q in Ioi (R - r), ∑ n ∈ Finset.range K, binomCoeff α n * r ^ n *
        (R ^ (-α) * (r + q) ^ (-(α + (n : ℝ)) - 1) - (r + q) ^ (-(2 * α + (n : ℝ)) - 1)))
      = R ^ (-2 * α) * ∑ n ∈ Finset.range K, tailCoeff α n * (r / R) ^ n := by
  have hb : (0 : ℝ) < r + (R - r) := by linarith
  have hRr : r + (R - r) = R := by ring
  have hterm : ∀ n : ℕ, (∫ q in Ioi (R - r), binomCoeff α n * r ^ n *
      (R ^ (-α) * (r + q) ^ (-(α + (n : ℝ)) - 1) - (r + q) ^ (-(2 * α + (n : ℝ)) - 1)))
      = R ^ (-2 * α) * (tailCoeff α n * (r / R) ^ n) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp1 : (0 : ℝ) < α + n := by positivity
    have hp2 : (0 : ℝ) < 2 * α + n := by positivity
    have hRn : (R : ℝ) ^ n ≠ 0 := by positivity
    rw [integral_const_mul,
      integral_sub ((integrableOn_Ioi_shift_rpow hp1 hb).const_mul _)
        (integrableOn_Ioi_shift_rpow hp2 hb),
      integral_const_mul, integral_Ioi_shift_rpow hp1 hb, integral_Ioi_shift_rpow hp2 hb, hRr]
    have hA : R ^ (-(α + (n : ℝ))) = R ^ (-α) * (R ^ n)⁻¹ := by
      rw [← Real.rpow_natCast R n, ← Real.rpow_neg hR.le, ← Real.rpow_add hR]
      congr 1
      ring
    have hB : R ^ (-(2 * α + (n : ℝ))) = R ^ (-2 * α) * (R ^ n)⁻¹ := by
      rw [← Real.rpow_natCast R n, ← Real.rpow_neg hR.le, ← Real.rpow_add hR]
      congr 1
      ring
    have hC : R ^ (-α) * R ^ (-α) = R ^ (-2 * α) := by
      rw [← Real.rpow_add hR]
      congr 1
      ring
    have key : R ^ (-α) * (R ^ (-α) * (R ^ n)⁻¹ / (α + n))
        = R ^ (-2 * α) * (R ^ n)⁻¹ / (α + n) := by
      rw [← hC]
      ring
    rw [hA, hB, key, tailCoeff, div_pow]
    field_simp
    ring
  rw [integral_finsetSum _ (fun n _ => by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exact (((integrableOn_Ioi_shift_rpow (p := α + n) (by positivity) hb).const_mul
      (R ^ (-α))).sub
      (integrableOn_Ioi_shift_rpow (p := 2 * α + n) (by positivity) hb)).const_mul _),
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => hterm n

/-! ### The reserve bound -/

/-- **Any partial sum of the tail series is a lower bound for the reserve integral.**  This is the
form in which the `α = 6/5` leaf checks consume the radial reserve of
`jumpGen_truncBase_ge_radial`: `K` is chosen per leaf, and the coefficients are rational
(`tailCoeffQ`). -/
theorem integral_tailRadial_ge {α R r : ℝ} (hα : 1 < α) (hα' : α < 2) (hR : 0 < R)
    (hr : 0 ≤ r) (hr' : r < R) (K : ℕ) :
    2 * R ^ (-2 * α) * ∑ n ∈ Finset.range K, tailCoeff α n * (r / R) ^ n
      ≤ ∫ t : ℝ, tailRadial α R r t * |t| ^ (-(1 + α)) := by
  have hα0 : 0 < α := by linarith
  have hα2 : α < 2 := hα'
  rw [integral_tailRadial_eq, integral_Ioi_tailIntegrand hα0 hr hr']
  have hmono := setIntegral_mono_on (integrableOn_tailSum hα0 hR K)
    (integrableOn_tailIntegrand hα0 hr hr') measurableSet_Ioi
    (fun q hq => tailSum_le_tailIntegrand hα0 hr (by
      have : R - r < q := hq
      linarith) K)
  rw [integral_Ioi_tailSum hα0 hR K] at hmono
  linarith

end CenteredMaximal.Fractional

end

/-! ### The rational coefficients at `α = 6/5` -/

namespace CenteredMaximal.Fractional

/-- The binomial coefficient `(11/5)_n / n!` at `α = 6/5`, *exactly*, as a rational.  Given by its
multiplicative recursion, not by literals: the numerator of `tailCoeffQ 64` has 134 digits. -/
def binomCoeffQ : ℕ → ℚ
  | 0 => 1
  | n + 1 => binomCoeffQ n * (11 / 5 + n) / ((n : ℚ) + 1)

@[simp] theorem binomCoeffQ_zero : binomCoeffQ 0 = 1 := rfl

theorem binomCoeffQ_succ (n : ℕ) :
    binomCoeffQ (n + 1) = binomCoeffQ n * (11 / 5 + n) / ((n : ℚ) + 1) := rfl

/-- **The tail coefficient at `α = 6/5`, exactly, as a rational.**  A certificate row evaluates
this by kernel reduction of the recursion. -/
def tailCoeffQ (n : ℕ) : ℚ := binomCoeffQ n * (6 / 5) / ((6 / 5 + n) * (12 / 5 + n))

theorem tailCoeffQ_zero : tailCoeffQ 0 = 5 / 12 := by
  rw [tailCoeffQ]
  norm_num

theorem binomCoeffQ_eq (n : ℕ) : ((binomCoeffQ n : ℚ) : ℝ) = binomCoeff (6 / 5) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [binomCoeffQ_succ, binomCoeff_succ, ← ih]
    push_cast
    ring

/-- **The coefficients at `α = 6/5` are exactly rational.**  Equality, not merely `≤`. -/
theorem tailCoeffQ_eq (n : ℕ) : ((tailCoeffQ n : ℚ) : ℝ) = tailCoeff (6 / 5) n := by
  rw [tailCoeffQ, tailCoeff, ← binomCoeffQ_eq]
  push_cast
  ring

/-- The rational minorant a certificate row uses; it is in fact an equality, `tailCoeffQ_eq`. -/
theorem tailCoeffQ_le (n : ℕ) : ((tailCoeffQ n : ℚ) : ℝ) ≤ tailCoeff (6 / 5) n :=
  (tailCoeffQ_eq n).le

theorem tailCoeffQ_pos (n : ℕ) : 0 < tailCoeffQ n := by
  have h : (0 : ℝ) < ((tailCoeffQ n : ℚ) : ℝ) := by
    rw [tailCoeffQ_eq]
    exact tailCoeff_pos (by norm_num) n
  exact_mod_cast h

end CenteredMaximal.Fractional

end
