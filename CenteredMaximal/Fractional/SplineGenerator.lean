/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Cauchy.Semigroup

/-!
# The fractional generator of the cardinal cubic B-spline

The sharper upper bound on the planar centred maximal constant replaces the Cauchy generator
`α = 1` by a generator of order `α = 6/5`. Its test function is the **centred cardinal cubic
B-spline**

`β y = (1/6) ∑_{q=0}^{4} (−1)^q C(4,q) ((y + 2 − q)₊)³`,

an even, compactly supported, piecewise cubic function. This file computes the one-dimensional
jump integral `jumpGen1 α β` of `CenteredMaximal.Cauchy.Semigroup` in closed form for every
`α ∈ (0, 2)` with `α ≠ 1`:

`jumpGen1 α β x = 2 / (−(α (1 − α) (2 − α) (3 − α))) ∑_{q=0}^{4} (−1)^q C(4,q) |x + 2 − q|^{3−α}`,

which is `jumpGen1_bspline`. At `α = 6/5` the prefactor is `625/108` and the exponent is `9/5`.
The hypothesis `α ≠ 1` is essential: both sides degenerate there, which is exactly why the Cauchy
case carries a logarithm instead (see `CenteredMaximal.Cauchy.TentGenerator`).

## Main results

* `bspline`, `truncCube`, `cubeDiff`: the B-spline, the truncated cube `(y₊)³` out of which it is
  built, and the symmetric second difference of the latter.
* `bspline_eq_zero_of_two_le`: `β` vanishes off `[−2, 2]`, because the fourth difference of a cubic
  vanishes identically.
* `integrableOn_cubeDiff`, `integral_Ioc_cubeDiff`: the single truncated cube is integrable against
  `s^{−(1+α)}` on every `(0, R]` and has an explicit primitive there.
* `jumpGen1_bspline`: the closed form of the jump integral.

## The finite-part argument

The obvious route fails: applying the operator to each truncated cube separately diverges at
infinity, since the second difference of `(·)₊³` grows like `s³` against a weight `s^{−1−α}`. The
cancellation inside the alternating sum is what makes the integral converge, so the bookkeeping is
done with a cutoff. Fix `x` and put `c_q = x + 2 − q`, `R = |x| + 3`, so that `|c_q| < R` and
`β (x ± s) = 0` for `s > R`. On `(0, R]` the integrand splits as a finite sum over `q`, and
`integral_Ioc_cubeDiff` evaluates each piece by splitting `(0, R]` at the single breakpoint `|c_q|`:
below it the second difference is exactly `6 (c_q)₊ s²`, above it exactly `(c_q + s)³ − 2 (c_q)₊³`,
and both are integrated by the primitive `cubicAntideriv`. Summing, the parts of the answer which
are polynomial in `c_q` of degree `≤ 3` are annihilated by `∑_q (−1)^q C(4,q)`
(`sum_alt_choose_cubic`), and the surviving `R`-dependent term `∑_q (−1)^q C(4,q) |c_q|³ R^{−α}/α`
equals `12 β(x) R^{−α}/α` because `|c|³ = 2 (c₊)³ − c³`. That is cancelled on the nose by the tail
`∫_{s > R} (−2 β(x)) s^{−1−α} ds`, so no limit `R → ∞` is needed and the closed form drops out.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology

namespace CenteredMaximal.Fractional

/-! ### The truncated cube and the B-spline -/

/-- The truncated cube `(y₊)³ = (max y 0)³`. -/
def truncCube (y : ℝ) : ℝ := max y 0 ^ 3

/-- The centred cardinal cubic B-spline
`β y = (1/6) ∑_{q=0}^{4} (−1)^q C(4,q) ((y + 2 − q)₊)³`, supported in `[−2, 2]`. -/
def bspline (y : ℝ) : ℝ :=
  1 / 6 * ∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (y + 2 - q)

/-- The symmetric second difference `(c + s)₊³ + (c − s)₊³ − 2 c₊³` of the truncated cube. -/
def cubeDiff (c s : ℝ) : ℝ := truncCube (c + s) + truncCube (c - s) - 2 * truncCube c

theorem truncCube_of_nonneg {y : ℝ} (hy : 0 ≤ y) : truncCube y = y ^ 3 := by
  rw [truncCube, max_eq_left hy]

theorem truncCube_of_nonpos {y : ℝ} (hy : y ≤ 0) : truncCube y = 0 := by
  rw [truncCube, max_eq_right hy, zero_pow three_ne_zero]

theorem continuous_truncCube : Continuous truncCube :=
  (continuous_id.max continuous_const).pow 3

/-- The absolute cube in terms of the truncated cube: `|y|³ = 2 (y₊)³ − y³`. -/
theorem abs_cube (y : ℝ) : |y| ^ 3 = 2 * truncCube y - y ^ 3 := by
  rcases le_total 0 y with hy | hy
  · rw [abs_of_nonneg hy, truncCube_of_nonneg hy]; ring
  · rw [abs_of_nonpos hy, truncCube_of_nonpos hy]; ring

/-- **The fourth difference kills cubics.** The alternating binomial sum
`∑_{q=0}^{4} (−1)^q C(4,q) p(x + 2 − q)` vanishes for every polynomial `p` of degree at most `3`. -/
theorem sum_alt_choose_cubic (x a₀ a₁ a₂ a₃ : ℝ) :
    ∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
      (a₃ * (x + 2 - q) ^ 3 + a₂ * (x + 2 - q) ^ 2 + a₁ * (x + 2 - q) + a₀) = 0 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose]
  norm_num
  ring

/-- The defining alternating sum of the B-spline. -/
theorem sum_alt_truncCube (y : ℝ) :
    ∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (y + 2 - q)
      = 6 * bspline y := by
  rw [bspline]; ring

theorem bspline_of_two_le {y : ℝ} (hy : 2 ≤ y) : bspline y = 0 := by
  have h : ∀ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (y + 2 - q)
      = (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
        (1 * (y + 2 - q) ^ 3 + 0 * (y + 2 - q) ^ 2 + 0 * (y + 2 - q) + 0) := by
    intro q hq
    have hq4 : (q : ℝ) ≤ 4 := by
      exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    rw [truncCube_of_nonneg (by linarith)]
    ring
  rw [bspline, Finset.sum_congr rfl h, sum_alt_choose_cubic, mul_zero]

theorem bspline_of_le_neg_two {y : ℝ} (hy : y ≤ -2) : bspline y = 0 := by
  have h : ∀ q ∈ Finset.range 5,
      (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (y + 2 - q) = 0 := by
    intro q _
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    rw [truncCube_of_nonpos (by linarith), mul_zero]
  rw [bspline, Finset.sum_congr rfl h, Finset.sum_const_zero, mul_zero]

/-- **The B-spline is supported in `[−2, 2]`.** -/
theorem bspline_eq_zero_of_two_le {y : ℝ} (hy : 2 ≤ |y|) : bspline y = 0 := by
  rcases le_abs.1 hy with h | h
  · exact bspline_of_two_le h
  · exact bspline_of_le_neg_two (by linarith)

/-! ### The second difference of the truncated cube -/

theorem continuous_cubeDiff (c : ℝ) : Continuous (cubeDiff c) := by
  unfold cubeDiff
  exact ((continuous_truncCube.comp' (continuous_const.add continuous_id)).add
    (continuous_truncCube.comp' (continuous_const.sub continuous_id))).sub continuous_const

/-- Below the breakpoint the second difference is exactly `6 c₊ s²`: no truncation is felt when
`c` and `c ± s` lie on the same side of the origin. -/
theorem cubeDiff_of_le_abs {c s : ℝ} (hs : 0 < s) (hsc : s ≤ |c|) :
    cubeDiff c s = 6 * max c 0 * s ^ 2 := by
  rcases le_or_gt 0 c with hc | hc
  · rw [abs_of_nonneg hc] at hsc
    rw [cubeDiff, truncCube_of_nonneg (by linarith), truncCube_of_nonneg (by linarith),
      truncCube_of_nonneg hc, max_eq_left hc]
    ring
  · rw [abs_of_neg hc] at hsc
    rw [cubeDiff, truncCube_of_nonpos (by linarith), truncCube_of_nonpos (by linarith),
      truncCube_of_nonpos hc.le, max_eq_right hc.le]
    ring

/-- Above the breakpoint only the forward cube survives. -/
theorem cubeDiff_of_abs_lt {c s : ℝ} (hsc : |c| < s) :
    cubeDiff c s = (c + s) ^ 3 - 2 * truncCube c := by
  have h1 : 0 ≤ c + s := by have := neg_abs_le c; linarith
  have h2 : c - s ≤ 0 := by have := le_abs_self c; linarith
  rw [cubeDiff, truncCube_of_nonneg h1, truncCube_of_nonpos h2, add_zero]

/-- The second difference of the B-spline is the alternating sum of the second differences of the
truncated cubes at the breakpoints `x + 2 − q`. -/
theorem bspline_secondDiff (x s : ℝ) :
    bspline (x + s) + bspline (x - s) - 2 * bspline x
      = 1 / 6 * ∑ q ∈ Finset.range 5,
          (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * cubeDiff (x + 2 - q) s := by
  have key : ∀ q ∈ Finset.range 5,
      (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * cubeDiff (x + 2 - q) s
        = (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (x + s + 2 - q)
          + (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (x - s + 2 - q)
          - 2 * ((-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (x + 2 - q)) := by
    intro q _
    rw [cubeDiff, show x + 2 - (q : ℝ) + s = x + s + 2 - q by ring,
      show x + 2 - (q : ℝ) - s = x - s + 2 - q by ring]
    ring
  rw [Finset.sum_congr rfl key, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  simp only [bspline]
  ring

/-! ### Powers -/

private theorem pow_mul_rpow {s : ℝ} (hs : 0 < s) (n : ℕ) (β : ℝ) :
    s ^ n * s ^ β = s ^ ((n : ℝ) + β) := by
  rw [← Real.rpow_natCast s n, ← Real.rpow_add hs]

private theorem cube_mul_rpow {s : ℝ} (hs : 0 < s) (α : ℝ) :
    s ^ 3 * s ^ (-(1 + α)) = s ^ (2 - α) := by
  rw [pow_mul_rpow hs 3, show ((3 : ℕ) : ℝ) + -(1 + α) = 2 - α by push_cast; ring]

private theorem sq_mul_rpow {s : ℝ} (hs : 0 < s) (α : ℝ) :
    s ^ 2 * s ^ (-(1 + α)) = s ^ (1 - α) := by
  rw [pow_mul_rpow hs 2, show ((2 : ℕ) : ℝ) + -(1 + α) = 1 - α by push_cast; ring]

private theorem self_mul_rpow {s : ℝ} (hs : 0 < s) (α : ℝ) :
    s * s ^ (-(1 + α)) = s ^ (-α) := by
  have h := pow_mul_rpow hs 1 (-(1 + α))
  rwa [pow_one, show ((1 : ℕ) : ℝ) + -(1 + α) = -α by push_cast; ring] at h

private theorem rpow_two_sub {d : ℝ} (hd : 0 < d) (α : ℝ) : d ^ (2 - α) = d ^ (3 - α) / d := by
  rw [show (3 : ℝ) - α = ((1 : ℕ) : ℝ) + (2 - α) by push_cast; ring, Real.rpow_add hd,
    Real.rpow_natCast, pow_one]
  field_simp

private theorem rpow_one_sub {d : ℝ} (hd : 0 < d) (α : ℝ) :
    d ^ (1 - α) = d ^ (3 - α) / d ^ 2 := by
  rw [show (3 : ℝ) - α = ((2 : ℕ) : ℝ) + (1 - α) by push_cast; ring, Real.rpow_add hd,
    Real.rpow_natCast]
  field_simp

private theorem rpow_neg_self {d : ℝ} (hd : 0 < d) (α : ℝ) :
    d ^ (-α) = d ^ (3 - α) / d ^ 3 := by
  rw [show (3 : ℝ) - α = ((3 : ℕ) : ℝ) + -α by push_cast; ring, Real.rpow_add hd,
    Real.rpow_natCast]
  field_simp

/-! ### The primitive of a cubic against `s^{−(1+α)}` -/

/-- The primitive `p t^{3−α}/(3−α) + q t^{2−α}/(2−α) + r t^{1−α}/(1−α) − w t^{−α}/α` of
`(p s³ + q s² + r s + w) s^{−(1+α)}` on the positive half-line. -/
private def cubicAntideriv (α p q r w t : ℝ) : ℝ :=
  p * t ^ (3 - α) / (3 - α) + q * t ^ (2 - α) / (2 - α) + r * t ^ (1 - α) / (1 - α)
    - w * t ^ (-α) / α

private theorem cubic_mul_rpow {s : ℝ} (hs : 0 < s) (α p q r w : ℝ) :
    (p * s ^ 3 + q * s ^ 2 + r * s + w) * s ^ (-(1 + α))
      = p * s ^ (2 - α) + q * s ^ (1 - α) + r * s ^ (-α) + w * s ^ (-(1 + α)) := by
  rw [← cube_mul_rpow hs α, ← sq_mul_rpow hs α, ← self_mul_rpow hs α]
  ring

private theorem hasDerivAt_cubicAntideriv {α : ℝ} (hα : 0 < α) (hα' : α < 2) (hα1 : α ≠ 1)
    (p q r w : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (cubicAntideriv α p q r w)
      (p * t ^ (2 - α) + q * t ^ (1 - α) + r * t ^ (-α) + w * t ^ (-(1 + α))) t := by
  have h3 : (3 : ℝ) - α ≠ 0 := by linarith
  have h2 : (2 : ℝ) - α ≠ 0 := by linarith
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα1)
  have h0 : α ≠ 0 := hα.ne'
  have d3 : HasDerivAt (fun t : ℝ => p * t ^ (3 - α) / (3 - α)) (p * t ^ (2 - α)) t := by
    have h := ((Real.hasDerivAt_rpow_const (x := t) (p := 3 - α)
      (Or.inl ht.ne')).const_mul p).div_const (3 - α)
    rw [show (3 : ℝ) - α - 1 = 2 - α by ring] at h
    exact h.congr_deriv (by field_simp)
  have d2 : HasDerivAt (fun t : ℝ => q * t ^ (2 - α) / (2 - α)) (q * t ^ (1 - α)) t := by
    have h := ((Real.hasDerivAt_rpow_const (x := t) (p := 2 - α)
      (Or.inl ht.ne')).const_mul q).div_const (2 - α)
    rw [show (2 : ℝ) - α - 1 = 1 - α by ring] at h
    exact h.congr_deriv (by field_simp)
  have d1 : HasDerivAt (fun t : ℝ => r * t ^ (1 - α) / (1 - α)) (r * t ^ (-α)) t := by
    have h := ((Real.hasDerivAt_rpow_const (x := t) (p := 1 - α)
      (Or.inl ht.ne')).const_mul r).div_const (1 - α)
    rw [show (1 : ℝ) - α - 1 = -α by ring] at h
    exact h.congr_deriv (by field_simp)
  have d0 : HasDerivAt (fun t : ℝ => w * t ^ (-α) / α) (-(w * t ^ (-(1 + α)))) t := by
    have h := ((Real.hasDerivAt_rpow_const (x := t) (p := -α)
      (Or.inl ht.ne')).const_mul w).div_const α
    rw [show -α - 1 = -(1 + α) by ring] at h
    exact h.congr_deriv (by field_simp)
  exact (((d3.add d2).add d1).sub d0).congr_deriv (by ring)

private theorem integral_Ioc_cubic_rpow {α : ℝ} (hα : 0 < α) (hα' : α < 2) (hα1 : α ≠ 1)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (p q r w : ℝ) :
    ∫ s in Ioc a b, (p * s ^ 3 + q * s ^ 2 + r * s + w) * s ^ (-(1 + α))
      = cubicAntideriv α p q r w b - cubicAntideriv α p q r w a := by
  have hpos : ∀ s ∈ uIcc a b, 0 < s := by
    intro s hs
    rw [uIcc_of_le hab] at hs
    exact ha.trans_le hs.1
  have hderiv : ∀ s ∈ uIcc a b, HasDerivAt (cubicAntideriv α p q r w)
      ((p * s ^ 3 + q * s ^ 2 + r * s + w) * s ^ (-(1 + α))) s := by
    intro s hs
    rw [cubic_mul_rpow (hpos s hs)]
    exact hasDerivAt_cubicAntideriv hα hα' hα1 p q r w (hpos s hs)
  have hcont : ContinuousOn (fun s : ℝ => (p * s ^ 3 + q * s ^ 2 + r * s + w) * s ^ (-(1 + α)))
      (uIcc a b) :=
    (by fun_prop : Continuous fun s : ℝ => p * s ^ 3 + q * s ^ 2 + r * s + w).continuousOn.mul
      (ContinuousOn.rpow_const continuousOn_id fun s hs => Or.inl (hpos s hs).ne')
  rw [← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable]

private theorem integral_Ioc_rpow_zero {r b : ℝ} (hr : -1 < r) (hb : 0 ≤ b) :
    ∫ s in Ioc (0 : ℝ) b, s ^ r = b ^ (r + 1) / (r + 1) := by
  rw [← intervalIntegral.integral_of_le hb, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith : r + 1 ≠ 0), sub_zero]

private theorem integral_Ioi_rpow_tail {α R : ℝ} (hα : 0 < α) (hR : 0 < R) :
    ∫ s in Ioi R, s ^ (-(1 + α)) = R ^ (-α) / α := by
  rw [integral_Ioi_rpow_of_lt (by linarith) hR, show -(1 + α) + 1 = -α by ring, neg_div_neg_eq]

/-! ### The single truncated cube against the fractional weight -/

/-- The integrand of the single cube is integrable on `(0, R]` whenever `α < 2`: below the
breakpoint it is a constant multiple of `s^{1−α}`, above it is continuous. -/
theorem integrableOn_cubeDiff {α : ℝ} (hα' : α < 2) (c : ℝ) {R : ℝ} (hR : |c| ≤ R) :
    IntegrableOn (fun s : ℝ => cubeDiff c s * s ^ (-(1 + α))) (Ioc 0 R) := by
  have hR0 : (0 : ℝ) ≤ R := (abs_nonneg c).trans hR
  rcases eq_or_ne c 0 with rfl | hc
  · have heq : EqOn (fun s : ℝ => s ^ (2 - α))
        (fun s : ℝ => cubeDiff 0 s * s ^ (-(1 + α))) (Ioc 0 R) := by
      intro s hs
      have hs0 : (0 : ℝ) < s := hs.1
      show s ^ (2 - α) = cubeDiff 0 s * s ^ (-(1 + α))
      rw [cubeDiff, zero_add, zero_sub, truncCube_of_nonneg hs0.le,
        truncCube_of_nonpos (by linarith), truncCube_of_nonpos le_rfl, add_zero, mul_zero,
        sub_zero, cube_mul_rpow hs0]
    refine IntegrableOn.congr_fun ?_ heq measurableSet_Ioc
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hR0).1
      (intervalIntegral.intervalIntegrable_rpow' (by linarith))
  · have hc0 : 0 < |c| := abs_pos.2 hc
    rw [← Ioc_union_Ioc_eq_Ioc hc0.le hR, integrableOn_union]
    constructor
    · have heq : EqOn (fun s : ℝ => 6 * max c 0 * s ^ (1 - α))
          (fun s : ℝ => cubeDiff c s * s ^ (-(1 + α))) (Ioc 0 |c|) := by
        intro s hs
        show 6 * max c 0 * s ^ (1 - α) = cubeDiff c s * s ^ (-(1 + α))
        rw [cubeDiff_of_le_abs hs.1 hs.2, mul_assoc (6 * max c 0), sq_mul_rpow hs.1]
      refine IntegrableOn.congr_fun ?_ heq measurableSet_Ioc
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hc0.le).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
    · have hcont : ContinuousOn (fun s : ℝ => cubeDiff c s * s ^ (-(1 + α))) (Icc |c| R) :=
        (continuous_cubeDiff c).continuousOn.mul
          (ContinuousOn.rpow_const continuousOn_id fun s hs => Or.inl (hc0.trans_le hs.1).ne')
      exact hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- **The single truncated cube.** For `|c| < R` the integral of `cubeDiff c · s^{−(1+α)}` over
`(0, R]` is an explicit sum of powers of `R` together with the single term `K |c|^{3−α}`, where
`K = 3/(2−α) − 1/(3−α) − 3/(1−α) − 1/α`. The `R`-part is polynomial in `c` of degree at most `3`
except for the term `|c|³ R^{−α}/α`, written here as `(2 c₊³ − c³) R^{−α}/α`. -/
theorem integral_Ioc_cubeDiff {α : ℝ} (hα : 0 < α) (hα' : α < 2) (hα1 : α ≠ 1) (c : ℝ) {R : ℝ}
    (hR : |c| < R) :
    ∫ s in Ioc (0 : ℝ) R, cubeDiff c s * s ^ (-(1 + α))
      = R ^ (3 - α) / (3 - α) + 3 * c * R ^ (2 - α) / (2 - α)
        + 3 * c ^ 2 * R ^ (1 - α) / (1 - α) + (2 * truncCube c - c ^ 3) * R ^ (-α) / α
        + (3 / (2 - α) - 1 / (3 - α) - 3 / (1 - α) - 1 / α) * |c| ^ (3 - α) := by
  have h3 : (3 : ℝ) - α ≠ 0 := by linarith
  have h2 : (2 : ℝ) - α ≠ 0 := by linarith
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα1)
  have h0 : α ≠ 0 := hα.ne'
  have hR0 : 0 < R := (abs_nonneg c).trans_lt hR
  rcases eq_or_ne c 0 with rfl | hc
  · have heq : EqOn (fun s : ℝ => cubeDiff 0 s * s ^ (-(1 + α)))
        (fun s : ℝ => s ^ (2 - α)) (Ioc 0 R) := by
      intro s hs
      have hs0 : (0 : ℝ) < s := hs.1
      show cubeDiff 0 s * s ^ (-(1 + α)) = s ^ (2 - α)
      rw [cubeDiff, zero_add, zero_sub, truncCube_of_nonneg hs0.le,
        truncCube_of_nonpos (by linarith), truncCube_of_nonpos le_rfl, add_zero, mul_zero,
        sub_zero, cube_mul_rpow hs0]
    rw [setIntegral_congr_fun measurableSet_Ioc heq,
      integral_Ioc_rpow_zero (by linarith) hR0.le, show (2 : ℝ) - α + 1 = 3 - α by ring,
      truncCube_of_nonpos le_rfl, abs_zero, Real.zero_rpow h3]
    ring
  · have hc0 : 0 < |c| := abs_pos.2 hc
    have hI1 : ∫ s in Ioc (0 : ℝ) |c|, cubeDiff c s * s ^ (-(1 + α))
        = 6 * max c 0 * (|c| ^ (2 - α) / (2 - α)) := by
      have heq : EqOn (fun s : ℝ => cubeDiff c s * s ^ (-(1 + α)))
          (fun s : ℝ => 6 * max c 0 * s ^ (1 - α)) (Ioc 0 |c|) := by
        intro s hs
        show cubeDiff c s * s ^ (-(1 + α)) = 6 * max c 0 * s ^ (1 - α)
        rw [cubeDiff_of_le_abs hs.1 hs.2, mul_assoc (6 * max c 0), sq_mul_rpow hs.1]
      rw [setIntegral_congr_fun measurableSet_Ioc heq, integral_const_mul,
        integral_Ioc_rpow_zero (by linarith) hc0.le, show (1 : ℝ) - α + 1 = 2 - α by ring]
    have hI2 : ∫ s in Ioc |c| R, cubeDiff c s * s ^ (-(1 + α))
        = cubicAntideriv α 1 (3 * c) (3 * c ^ 2) (c ^ 3 - 2 * truncCube c) R
          - cubicAntideriv α 1 (3 * c) (3 * c ^ 2) (c ^ 3 - 2 * truncCube c) |c| := by
      have heq : EqOn (fun s : ℝ => cubeDiff c s * s ^ (-(1 + α)))
          (fun s : ℝ => (1 * s ^ 3 + 3 * c * s ^ 2 + 3 * c ^ 2 * s
            + (c ^ 3 - 2 * truncCube c)) * s ^ (-(1 + α))) (Ioc |c| R) := by
        intro s hs
        show cubeDiff c s * s ^ (-(1 + α))
          = (1 * s ^ 3 + 3 * c * s ^ 2 + 3 * c ^ 2 * s
              + (c ^ 3 - 2 * truncCube c)) * s ^ (-(1 + α))
        rw [cubeDiff_of_abs_lt hs.1]
        ring
      rw [setIntegral_congr_fun measurableSet_Ioc heq,
        integral_Ioc_cubic_rpow hα hα' hα1 hc0 hR.le]
    have hAR : cubicAntideriv α 1 (3 * c) (3 * c ^ 2) (c ^ 3 - 2 * truncCube c) R
        = R ^ (3 - α) / (3 - α) + 3 * c * R ^ (2 - α) / (2 - α)
          + 3 * c ^ 2 * R ^ (1 - α) / (1 - α) + (2 * truncCube c - c ^ 3) * R ^ (-α) / α := by
      rw [cubicAntideriv]; ring
    have key : 6 * max c 0 * (|c| ^ (2 - α) / (2 - α))
        - cubicAntideriv α 1 (3 * c) (3 * c ^ 2) (c ^ 3 - 2 * truncCube c) |c|
        = (3 / (2 - α) - 1 / (3 - α) - 3 / (1 - α) - 1 / α) * |c| ^ (3 - α) := by
      rw [cubicAntideriv, rpow_two_sub hc0, rpow_one_sub hc0, rpow_neg_self hc0]
      rcases hc.lt_or_gt with hneg | hpos
      · rw [abs_of_neg hneg, max_eq_right hneg.le, truncCube_of_nonpos hneg.le]
        have hne : -c ≠ 0 := by linarith
        field_simp
        ring
      · rw [abs_of_pos hpos, max_eq_left hpos.le, truncCube_of_nonneg hpos.le]
        have hne : c ≠ 0 := hpos.ne'
        field_simp
        ring
    rw [← Ioc_union_Ioc_eq_Ioc hc0.le hR.le,
      setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
        (integrableOn_cubeDiff hα' c le_rfl)
        ((integrableOn_cubeDiff hα' c hR.le).mono_set (Ioc_subset_Ioc_left (abs_nonneg c))),
      hI1, hI2, hAR]
    linear_combination key

/-! ### The main identity -/

/-- **The fractional generator of the cardinal cubic B-spline.** For `0 < α < 2` with `α ≠ 1`,
`jumpGen1 α β x = 2/(−(α(1−α)(2−α)(3−α))) ∑_q (−1)^q C(4,q) |x + 2 − q|^{3−α}`. -/
theorem jumpGen1_bspline {α : ℝ} (hα : 0 < α) (hα' : α < 2) (hα1 : α ≠ 1) (x : ℝ) :
    jumpGen1 α bspline x
      = 2 / (-(α * (1 - α) * (2 - α) * (3 - α)))
          * ∑ q ∈ Finset.range 5, (-1) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - q| ^ (3 - α) := by
  have h3 : (3 : ℝ) - α ≠ 0 := by linarith
  have h2 : (2 : ℝ) - α ≠ 0 := by linarith
  have h1 : (1 : ℝ) - α ≠ 0 := sub_ne_zero.2 (Ne.symm hα1)
  have h0 : α ≠ 0 := hα.ne'
  have habs := abs_nonneg x
  set R : ℝ := |x| + 3 with hRdef
  have hR0 : 0 < R := by rw [hRdef]; linarith
  have hcR : ∀ q ∈ Finset.range 5, |x + 2 - (q : ℝ)| < R := by
    intro q hq
    have hq4 : (q : ℝ) ≤ 4 := by
      exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hb : |2 - (q : ℝ)| ≤ 2 := by rw [abs_le]; constructor <;> linarith
    calc |x + 2 - (q : ℝ)| ≤ |x| + |2 - (q : ℝ)| := by
          rw [show x + 2 - (q : ℝ) = x + (2 - q) by ring]; exact abs_add_le _ _
      _ ≤ |x| + 2 := by linarith
      _ < R := by rw [hRdef]; linarith
  -- the integrand is even
  have hFeven : ∀ s : ℝ,
      (bspline (x + -s) + bspline (x - -s) - 2 * bspline x) * |(-s)| ^ (-(1 + α))
        = (bspline (x + s) + bspline (x - s) - 2 * bspline x) * |s| ^ (-(1 + α)) := by
    intro s
    rw [abs_neg, show x + -s = x - s by ring, show x - -s = x + s by ring]
    ring
  -- the integrand on the bounded part
  have hfsum : EqOn (fun s : ℝ => (bspline (x + s) + bspline (x - s) - 2 * bspline x) *
        |s| ^ (-(1 + α)))
      (fun s : ℝ => ∑ q ∈ Finset.range 5, 1 / 6 * ((-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ)) *
        (cubeDiff (x + 2 - q) s * s ^ (-(1 + α)))) (Ioc 0 R) := by
    intro s hs
    simp only
    rw [bspline_secondDiff, abs_of_pos hs.1, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => by ring
  -- the integrand on the tail
  have hftail : EqOn (fun s : ℝ => (bspline (x + s) + bspline (x - s) - 2 * bspline x) *
        |s| ^ (-(1 + α)))
      (fun s : ℝ => -2 * bspline x * s ^ (-(1 + α))) (Ioi R) := by
    intro s hs
    have hs' : R < s := hs
    have hxa : -|x| ≤ x := neg_abs_le x
    have hxb : x ≤ |x| := le_abs_self x
    rw [hRdef] at hs'
    show (bspline (x + s) + bspline (x - s) - 2 * bspline x) * |s| ^ (-(1 + α))
      = -2 * bspline x * s ^ (-(1 + α))
    rw [bspline_of_two_le (by linarith : (2 : ℝ) ≤ x + s),
      bspline_of_le_neg_two (by linarith : x - s ≤ -2), abs_of_pos (hR0.trans hs)]
    ring
  have hint_bdd : IntegrableOn (fun s : ℝ => (bspline (x + s) + bspline (x - s) - 2 * bspline x) *
      |s| ^ (-(1 + α))) (Ioc 0 R) := by
    refine IntegrableOn.congr_fun ?_ (fun s hs => (hfsum hs).symm) measurableSet_Ioc
    exact integrable_finsetSum _ fun q hq =>
      (integrableOn_cubeDiff hα' _ (hcR q hq).le).const_mul _
  have hint_tail : IntegrableOn (fun s : ℝ => (bspline (x + s) + bspline (x - s) - 2 * bspline x) *
      |s| ^ (-(1 + α))) (Ioi R) := by
    refine IntegrableOn.congr_fun ?_ (fun s hs => (hftail hs).symm) measurableSet_Ioi
    exact (integrableOn_Ioi_rpow_of_lt (by linarith) hR0).const_mul _
  have hIoi : IntegrableOn (fun s : ℝ => (bspline (x + s) + bspline (x - s) - 2 * bspline x) *
      |s| ^ (-(1 + α))) (Ioi 0) := by
    rw [← Ioc_union_Ioi_eq_Ioi hR0.le, integrableOn_union]
    exact ⟨hint_bdd, hint_tail⟩
  -- the two pieces
  have htailval : ∫ s in Ioi R, (bspline (x + s) + bspline (x - s) - 2 * bspline x) *
      |s| ^ (-(1 + α)) = -2 * bspline x * (R ^ (-α) / α) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hftail, integral_const_mul,
      integral_Ioi_rpow_tail hα hR0]
  have hbddval : ∫ s in Ioc (0 : ℝ) R, (bspline (x + s) + bspline (x - s) - 2 * bspline x) *
      |s| ^ (-(1 + α))
      = ∑ q ∈ Finset.range 5, 1 / 6 * ((-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ)) *
          (R ^ (3 - α) / (3 - α) + 3 * (x + 2 - q) * R ^ (2 - α) / (2 - α)
            + 3 * (x + 2 - q) ^ 2 * R ^ (1 - α) / (1 - α)
            + (2 * truncCube (x + 2 - q) - (x + 2 - q) ^ 3) * R ^ (-α) / α
            + (3 / (2 - α) - 1 / (3 - α) - 3 / (1 - α) - 1 / α) * |x + 2 - q| ^ (3 - α)) := by
    rw [setIntegral_congr_fun measurableSet_Ioc hfsum,
      integral_finsetSum _ fun q hq => (integrableOn_cubeDiff hα' _ (hcR q hq).le).const_mul _]
    exact Finset.sum_congr rfl fun q hq => by
      rw [integral_const_mul, integral_Ioc_cubeDiff hα hα' hα1 _ (hcR q hq)]
  -- the alternating sum collapses
  have hsplit : ∀ q ∈ Finset.range 5,
      1 / 6 * ((-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ)) *
          (R ^ (3 - α) / (3 - α) + 3 * (x + 2 - q) * R ^ (2 - α) / (2 - α)
            + 3 * (x + 2 - q) ^ 2 * R ^ (1 - α) / (1 - α)
            + (2 * truncCube (x + 2 - q) - (x + 2 - q) ^ 3) * R ^ (-α) / α
            + (3 / (2 - α) - 1 / (3 - α) - 3 / (1 - α) - 1 / α) * |x + 2 - q| ^ (3 - α))
        = 1 / 6 * ((-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
              (-(R ^ (-α) / α) * (x + 2 - q) ^ 3 + 3 * R ^ (1 - α) / (1 - α) * (x + 2 - q) ^ 2
                + 3 * R ^ (2 - α) / (2 - α) * (x + 2 - q) + R ^ (3 - α) / (3 - α)))
          + 1 / 3 * (R ^ (-α) / α) *
              ((-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * truncCube (x + 2 - q))
          + 1 / 6 * (3 / (2 - α) - 1 / (3 - α) - 3 / (1 - α) - 1 / α) *
              ((-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - q| ^ (3 - α)) := by
    intro q _
    ring
  have hK : 2 * (1 / 6 * (3 / (2 - α) - 1 / (3 - α) - 3 / (1 - α) - 1 / α))
      = 2 / (-(α * (1 - α) * (2 - α) * (3 - α))) := by
    field_simp
    ring
  rw [jumpGen1, integral_of_even hFeven hIoi, ← Ioc_union_Ioi_eq_Ioi hR0.le,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint_bdd hint_tail,
    hbddval, htailval, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_alt_choose_cubic, sum_alt_truncCube]
  linear_combination (∑ q ∈ Finset.range 5,
    (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * |x + 2 - (q : ℝ)| ^ (3 - α)) * hK

end CenteredMaximal.Fractional

end

end
