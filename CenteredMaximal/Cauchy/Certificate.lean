/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Cauchy.BaseDensity
public import CenteredMaximal.Cauchy.BumpGenerator
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Convex.Deriv

/-!
# The one-variable certificate for the optimised Cauchy kernel

The two exact angular bounds of `CenteredMaximal.Cauchy.BaseDensity` and
`CenteredMaximal.Cauchy.BumpGenerator` reduce the sign of the generator of
`looseKernel = K_R − ε ψ` inside the open unit diamond to a single inequality in the diamond
radius. With `R = looseRadius = 3797/2000`, `ε = looseBump = 159411/200000` and

`γ = cauchyGamma = ε R (R − 1) = 1087694569899/800000000000`,

the base density is at least `2 J (2 r / R) / (R (R − 1))` while the bump generator is at most
`2 T r`, so the required sign is exactly `certificate`,

`γ T r ≤ J (2 r / R)`,   `0 < r < 1`,

equivalently `0 ≤ Qfun r` for the slack `Q r = J (2 r / R) − γ T r` (`Qfun_nonneg`).

## The two regimes

On `(0, 1/2]` there is nothing to do: `T ≤ 0` there (`Tfun_nonpos_of_le_half`) while `J ≥ 1`
(`one_le_Jfun`), so `Q ≥ 0` termwise (`Qfun_nonneg_of_le_half`).

On `[1/2, 1)` the inequality is genuinely tight — the slack at its minimum is about `5.96 · 10⁻⁷`
— and is certified by *strong convexity plus a single point evaluation*, with no sampling of the
interval. Since `J` is convex on `(0, 2)` (`Jfun_convexOn`) and the substitution `r ↦ 2 r / R` is
affine, the first summand of `Q` is convex (`convexOn_Jfun_comp`); since `T'' ≤ −27/2`
(`deriv2_Tfun_le`) and `γ > 4/3` (`gamma_gt`), the second summand satisfies `(−γ T)'' ≥ 18`, with
`18` to spare for a subtracted parabola (`convexOn_neg_gamma_Tfun`). Hence `Q` dominates its
tangent parabola at any sample point (`Qfun_ge_quadratic`),

`Q r ≥ Q r₀ + Q' r₀ (r − r₀) + 9 (r − r₀)² ≥ Q r₀ − (Q' r₀)² / 36`.

At `r₀ = 3457/4000`, where `2 r₀ / R = 3457/3797`, the rational logarithm enclosures below give
`Q r₀ > 1/2000000` (`Qfun_r0_gt`) and `|Q' r₀| < 1/10000` (`abs_deriv_Qfun_r0_lt`), so

`Q r > 1/2000000 − 1/3600000000 > 0`.

## The logarithm enclosures

The point evaluation needs `log 2` together with the three logarithms `log (4137/3797)`,
`log (3457/4000)` and `log (543/500)`, out of which the four logarithms actually occurring in
`Jfun` and `Tfun_eq` at `r₀` are recovered by halving and by `log 8 = 3 log 2`
(`log_4137_div_7594`, `log_543_div_4000`). Each of the three is a `log (1 − x)` with
`|x| ≤ 543/4000`, so `Real.abs_log_sub_add_sum_range_le` turns twelve or fourteen terms of the
power series into an enclosure of width `5 · 10⁻¹³` (`le_log_one_sub`, `log_one_sub_le`); `log 2`
comes from `Real.log_two_gt_d9`. Both point estimates are then linear inequalities in the four
logarithms with explicit rational coefficients, so `linarith` closes them.

The exterior companion `exterior_certificate`, `ε (2 − 2 log 2) ≤ 1 / (R (R − 1))`, needs no
series at all.
-/

@[expose] public section

noncomputable section

open Filter Set
open scoped Topology

namespace CenteredMaximal.Cauchy

/-- **A rational lower bound for `log (1 − x)`** out of an upper bound `S` for the first `n`
terms of its power series, plus the explicit tail `|x|ⁿ⁺¹ / (1 − |x|)`. -/
private theorem le_log_one_sub {n : ℕ} {x A S : ℝ} (hA : |x| = A) (hA1 : A < 1)
    (hS : ∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1) ≤ S) :
    -S - A ^ (n + 1) / (1 - A) ≤ Real.log (1 - x) := by
  have hx : |x| < 1 := by rw [hA]; exact hA1
  have h := (abs_le.1 (Real.abs_log_sub_add_sum_range_le hx n)).1
  rw [hA] at h
  linarith

/-- **A rational upper bound for `log (1 − x)`** out of a lower bound `S` for the first `n`
terms of its power series, plus the explicit tail `|x|ⁿ⁺¹ / (1 − |x|)`. -/
private theorem log_one_sub_le {n : ℕ} {x A S : ℝ} (hA : |x| = A) (hA1 : A < 1)
    (hS : S ≤ ∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) :
    Real.log (1 - x) ≤ -S + A ^ (n + 1) / (1 - A) := by
  have hx : |x| < 1 := by rw [hA]; exact hA1
  have h := (abs_le.1 (Real.abs_log_sub_add_sum_range_le hx n)).2
  rw [hA] at h
  linarith

/-- `log (4137/3797) > 0.0857596062295`, from twelve terms at `x = −340/3797`. -/
private theorem log_4137_gt : (857596062295 / 10 ^ 13 : ℝ) < Real.log (4137 / 3797) := by
  have h := le_log_one_sub (n := 12) (x := (-(340 : ℝ) / 3797)) (A := 340 / 3797)
    (S := -857596062296 / 10 ^ 13) (by rw [abs_of_nonpos (by norm_num)]; norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  rw [show (1 : ℝ) - -(340 : ℝ) / 3797 = 4137 / 3797 by norm_num] at h
  refine lt_of_lt_of_le ?_ h
  norm_num

/-- `log (4137/3797) < 0.0857596062298`. -/
private theorem log_4137_lt : Real.log (4137 / 3797) < 857596062298 / 10 ^ 13 := by
  have h := log_one_sub_le (n := 12) (x := (-(340 : ℝ) / 3797)) (A := 340 / 3797)
    (S := -857596062297 / 10 ^ 13) (by rw [abs_of_nonpos (by norm_num)]; norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  rw [show (1 : ℝ) - -(340 : ℝ) / 3797 = 4137 / 3797 by norm_num] at h
  refine lt_of_le_of_lt h ?_
  norm_num

/-- `log (3457/4000) > −0.1458932001806`, from fourteen terms at `x = 543/4000`. -/
private theorem log_3457_gt : (-1458932001806 / 10 ^ 13 : ℝ) < Real.log (3457 / 4000) := by
  have h := le_log_one_sub (n := 14) (x := ((543 : ℝ) / 4000)) (A := 543 / 4000)
    (S := 1458932001804 / 10 ^ 13) (abs_of_nonneg (by norm_num)) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  rw [show (1 : ℝ) - (543 : ℝ) / 4000 = 3457 / 4000 by norm_num] at h
  refine lt_of_lt_of_le ?_ h
  norm_num

/-- `log (3457/4000) < −0.1458932001801`. -/
private theorem log_3457_lt : Real.log (3457 / 4000) < -1458932001801 / 10 ^ 13 := by
  have h := log_one_sub_le (n := 14) (x := ((543 : ℝ) / 4000)) (A := 543 / 4000)
    (S := 1458932001803 / 10 ^ 13) (abs_of_nonneg (by norm_num)) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  rw [show (1 : ℝ) - (543 : ℝ) / 4000 = 3457 / 4000 by norm_num] at h
  refine lt_of_le_of_lt h ?_
  norm_num

/-- `log (543/500) > 0.0825012215116`, from twelve terms at `x = −43/500`. -/
private theorem log_543_gt : (825012215116 / 10 ^ 13 : ℝ) < Real.log (543 / 500) := by
  have h := le_log_one_sub (n := 12) (x := (-(43 : ℝ) / 500)) (A := 43 / 500)
    (S := -825012215117 / 10 ^ 13) (by rw [abs_of_nonpos (by norm_num)]; norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  rw [show (1 : ℝ) - -(43 : ℝ) / 500 = 543 / 500 by norm_num] at h
  refine lt_of_lt_of_le ?_ h
  norm_num

/-- `log (543/500) < 0.0825012215119`. -/
private theorem log_543_lt : Real.log (543 / 500) < 825012215119 / 10 ^ 13 := by
  have h := log_one_sub_le (n := 12) (x := (-(43 : ℝ) / 500)) (A := 43 / 500)
    (S := -825012215118 / 10 ^ 13) (by rw [abs_of_nonpos (by norm_num)]; norm_num) (by norm_num)
    (by norm_num [Finset.sum_range_succ])
  rw [show (1 : ℝ) - -(43 : ℝ) / 500 = 543 / 500 by norm_num] at h
  refine lt_of_le_of_lt h ?_
  norm_num


/-- The comparison constant `γ = ε R (R − 1)` between the two exact angular bounds. -/
def cauchyGamma : ℝ := looseBump * looseRadius * (looseRadius - 1)

/-- The one-variable slack `Q r = J (2 r / R) − γ T r` certifying the sign of the generator. -/
def Qfun (r : ℝ) : ℝ := Jfun (2 * r / looseRadius) - cauchyGamma * Tfun r

theorem cauchyGamma_eq : cauchyGamma = 1087694569899 / 800000000000 := by
  norm_num [cauchyGamma, looseBump, looseRadius]

theorem gamma_gt : (4 : ℝ) / 3 < cauchyGamma := by
  rw [cauchyGamma_eq]; norm_num

theorem cauchyGamma_pos : 0 < cauchyGamma := by
  rw [cauchyGamma_eq]; norm_num

/-- `log (1 − s₀/2) = log (4137/7594)` reduced to the enclosed logarithm and `log 2`. -/
private theorem log_4137_div_7594 :
    Real.log (4137 / 7594 : ℝ) = Real.log (4137 / 3797) - Real.log 2 := by
  rw [show (4137 : ℝ) / 7594 = 4137 / 3797 / 2 by norm_num,
    Real.log_div (by norm_num) (by norm_num)]

/-- `log (1 − r₀) = log (543/4000)` reduced to the enclosed logarithm and `log 2`. -/
private theorem log_543_div_4000 :
    Real.log (543 / 4000 : ℝ) = Real.log (543 / 500) - 3 * Real.log 2 := by
  rw [show (543 : ℝ) / 4000 = 543 / 500 / 2 ^ 3 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_pow]
  norm_num

/-- On `(0, 1/2]` the angular bound `T` is nonpositive while `J ≥ 1`, so `Q ≥ 0` outright. -/
theorem Qfun_nonneg_of_le_half {r : ℝ} (hr : 0 < r) (hr' : r ≤ 1 / 2) : 0 ≤ Qfun r := by
  have hR : (0 : ℝ) < looseRadius := looseRadius_pos
  have hs : 0 < 2 * r / looseRadius := by positivity
  have hs' : 2 * r / looseRadius < 2 := by
    rw [div_lt_iff₀ hR]
    have : (1 : ℝ) < looseRadius := one_lt_looseRadius
    linarith
  have h1 := one_le_Jfun hs hs'
  have h2 := Tfun_nonpos_of_le_half hr hr'
  simp only [Qfun]
  nlinarith [cauchyGamma_pos]

/-- **The point evaluation.** `Q (3457/4000) > 1/2000000`. -/
theorem Qfun_r0_gt : 1 / 2000000 < Qfun (3457 / 4000) := by
  have harg : 2 * (3457 / 4000 : ℝ) / looseRadius = 3457 / 3797 := by norm_num [looseRadius]
  have hval : Qfun (3457 / 4000) = 1 / 2 - 2 / (3457 / 3797 : ℝ)
      - 4 / (3457 / 3797 : ℝ) ^ 2 * (Real.log (4137 / 3797) - Real.log 2)
      - cauchyGamma * (2 * (2 - 3457 / 4000) * (1 - Real.log 2 + Real.log (3457 / 4000))
        - 2 * (1 - 3457 / 4000) * (Real.log (543 / 500) - 3 * Real.log 2)) := by
    simp only [Qfun, harg, Jfun,
      Tfun_eq (by norm_num : (0 : ℝ) < 3457 / 4000) (by norm_num : (3457 : ℝ) / 4000 < 1)]
    rw [show (1 : ℝ) - 3457 / 3797 / 2 = 4137 / 7594 by norm_num, log_4137_div_7594,
      show (1 : ℝ) - 3457 / 4000 = 543 / 4000 by norm_num, log_543_div_4000]
  rw [hval, cauchyGamma_eq]
  linarith [log_4137_gt, log_4137_lt, log_3457_gt, log_3457_lt, log_543_gt, log_543_lt,
    Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- **The derivative of the shape function.**
`J' s = 2/s² + (8/s³) log(1 − s/2) + 2/(s² (1 − s/2))` on `(0, 2)`. -/
theorem hasDerivAt_Jfun {s : ℝ} (hs : 0 < s) (hs' : s < 2) :
    HasDerivAt Jfun
      (2 / s ^ 2 + 8 / s ^ 3 * Real.log (1 - s / 2) + 2 / (s ^ 2 * (1 - s / 2))) s := by
  have hs0 : s ≠ 0 := hs.ne'
  have hh : (1 : ℝ) - s / 2 ≠ 0 := by intro h; nlinarith
  have hlin : HasDerivAt (fun x : ℝ => 1 - x / 2) (0 - 1 / 2) s :=
    (hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).div_const 2)
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 - x / 2)) ((0 - 1 / 2) / (1 - s / 2)) s :=
    hlin.log hh
  have hlin2 : HasDerivAt (fun x : ℝ => 2 / x) ((0 * s - 2 * 1) / s ^ 2) s :=
    (hasDerivAt_const s (2 : ℝ)).div (hasDerivAt_id s) hs0
  have hquot : HasDerivAt (fun x : ℝ => 4 / x ^ 2)
      ((0 * s ^ 2 - 4 * (2 * s ^ 1)) / (s ^ 2) ^ 2) s :=
    (hasDerivAt_const s (4 : ℝ)).div (hasDerivAt_pow 2 s) (pow_ne_zero 2 hs0)
  have h := ((hasDerivAt_const s (1 / 2 : ℝ)).sub hlin2).sub (hquot.mul hlog)
  have hJ : Jfun = fun x : ℝ => 1 / 2 - 2 / x - 4 / x ^ 2 * Real.log (1 - x / 2) := rfl
  have heq : 0 - (0 * s - 2 * 1) / s ^ 2
      - ((0 * s ^ 2 - 4 * (2 * s ^ 1)) / (s ^ 2) ^ 2 * Real.log (1 - s / 2)
        + 4 / s ^ 2 * ((0 - 1 / 2) / (1 - s / 2)))
      = 2 / s ^ 2 + 8 / s ^ 3 * Real.log (1 - s / 2) + 2 / (s ^ 2 * (1 - s / 2)) := by
    field_simp
    ring
  rw [hJ, ← heq]
  exact h

/-- **The derivative of the slack.** `Q' r = J' (2 r / R) · (2 / R) − γ T' r` on `(0, 1)`. -/
theorem hasDerivAt_Qfun {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    HasDerivAt Qfun
      ((2 / (2 * r / looseRadius) ^ 2
          + 8 / (2 * r / looseRadius) ^ 3 * Real.log (1 - 2 * r / looseRadius / 2)
          + 2 / ((2 * r / looseRadius) ^ 2 * (1 - 2 * r / looseRadius / 2))) * (2 / looseRadius)
        - cauchyGamma
          * (2 * Real.log 2 - 2 * Real.log r + 2 * Real.log (1 - r) + 4 / r - 2)) r := by
  have hR : (1 : ℝ) < looseRadius := one_lt_looseRadius
  have hs : 0 < 2 * r / looseRadius := div_pos (by linarith) (by linarith)
  have hs' : 2 * r / looseRadius < 2 := by
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < looseRadius)]
    nlinarith
  have hin : HasDerivAt (fun x : ℝ => 2 * x / looseRadius) (2 / looseRadius) r := by
    have := ((hasDerivAt_id r).const_mul (2 : ℝ)).div_const looseRadius
    simpa using this
  have h1 := (hasDerivAt_Jfun hs hs').comp r hin
  have h2 := (hasDerivAt_Tfun hr hr').const_mul cauchyGamma
  exact h1.sub h2

/-- **The derivative at the sample point** is smaller than `10⁻⁴` in absolute value. -/
private theorem exists_deriv_Qfun_r0 :
    ∃ D : ℝ, HasDerivAt Qfun D (3457 / 4000) ∧ |D| < 1 / 10000 := by
  refine ⟨_, hasDerivAt_Qfun (by norm_num) (by norm_num), ?_⟩
  rw [show 2 * (3457 / 4000 : ℝ) / looseRadius = 3457 / 3797 by norm_num [looseRadius],
    show (1 : ℝ) - 3457 / 3797 / 2 = 4137 / 7594 by norm_num, log_4137_div_7594,
    show (1 : ℝ) - 3457 / 4000 = 543 / 4000 by norm_num, log_543_div_4000, cauchyGamma_eq,
    show (2 : ℝ) / looseRadius = 4000 / 3797 by norm_num [looseRadius], abs_lt]
  constructor <;>
    linarith [log_4137_gt, log_4137_lt, log_3457_gt, log_3457_lt, log_543_gt, log_543_lt,
      Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- **The derivative at the sample point** is below `10⁻⁴` in absolute value. -/
theorem abs_deriv_Qfun_r0_lt : |deriv Qfun (3457 / 4000)| < 1 / 10000 := by
  obtain ⟨D, hD, hDlt⟩ := exists_deriv_Qfun_r0
  rwa [hD.deriv]

/-- The tangent line of a convex function at a sample point lies below its graph. -/
private theorem tangent_le {f : ℝ → ℝ} {S : Set ℝ} (hconv : ConvexOn ℝ S f) {x y D : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hD : HasDerivAt f D x) : f x + D * (y - x) ≤ f y := by
  rcases lt_trichotomy y x with h | h | h
  · have hs := hconv.slope_le_of_hasDerivAt hy hx h hD
    rw [slope_def_field] at hs
    have := (div_le_iff₀ (sub_pos.2 h)).1 hs
    linarith
  · subst h; simp
  · have hs := hconv.le_slope_of_hasDerivAt hx hy h hD
    rw [slope_def_field] at hs
    have := (le_div_iff₀ (sub_pos.2 h)).1 hs
    linarith

/-- `r ↦ J (2 r / R)` is convex on `(0, 1)`: `J` is convex on `(0, 2)` and the substitution is
affine with `2 r / R < 2` throughout. -/
private theorem convexOn_Jfun_comp :
    ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun r => Jfun (2 * r / looseRadius)) := by
  have hR : (1 : ℝ) < looseRadius := one_lt_looseRadius
  have hmem : ∀ t ∈ Ioo (0 : ℝ) 1, 2 * t / looseRadius ∈ Ioo (0 : ℝ) 2 := by
    intro t ht
    refine ⟨div_pos (by linarith [ht.1]) (by linarith), ?_⟩
    rw [div_lt_iff₀ (by linarith)]
    nlinarith [ht.2]
  refine ⟨convex_Ioo 0 1, fun a ha b hb u v hu hv huv => ?_⟩
  have key := Jfun_convexOn.2 (hmem a ha) (hmem b hb) hu hv huv
  simp only [smul_eq_mul] at key ⊢
  rw [show 2 * (u * a + v * b) / looseRadius
    = u * (2 * a / looseRadius) + v * (2 * b / looseRadius) by ring]
  exact key

/-- **Strong concavity of the bump bound.** Since `T'' ≤ −27/2` and `γ > 4/3`, the function
`−γ T − 9 (· − c)²` still has a nonnegative second derivative on `(0, 1)`. -/
private theorem convexOn_neg_gamma_Tfun (c : ℝ) :
    ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun r => -(cauchyGamma * Tfun r) - 9 * (r - c) ^ 2) := by
  have hint : interior (Ioo (0 : ℝ) 1) = Ioo (0 : ℝ) 1 := isOpen_Ioo.interior_eq
  have hquad : ∀ x : ℝ, HasDerivAt (fun r : ℝ => 9 * (r - c) ^ 2) (18 * (x - c)) x := fun x =>
    (HasDerivAt.const_mul (9 : ℝ) (((hasDerivAt_id x).sub_const c).fun_pow 2)).congr_deriv (by
      simp only [id_eq]; push_cast; ring)
  have hd : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun r => -(cauchyGamma * Tfun r) - 9 * (r - c) ^ 2)
      (-(cauchyGamma * deriv Tfun x) - 18 * (x - c)) x := by
    intro x hx
    have h1 : HasDerivAt Tfun (deriv Tfun x) x := by
      rw [deriv_Tfun hx.1 hx.2]; exact hasDerivAt_Tfun hx.1 hx.2
    exact ((h1.const_mul cauchyGamma).neg).sub (hquad x)
  have hd2 : ∀ x ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (deriv fun r => -(cauchyGamma * Tfun r) - 9 * (r - c) ^ 2)
        (-(cauchyGamma * (-2 * (2 - x) / (x ^ 2 * (1 - x)))) - 18) x := by
    intro x hx
    have hev : ∀ᶠ y in 𝓝 x, (deriv fun r => -(cauchyGamma * Tfun r) - 9 * (r - c) ^ 2) y
        = -(cauchyGamma * deriv Tfun y) - 18 * (y - c) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy using (hd y hy).deriv
    refine HasDerivAt.congr_of_eventuallyEq ?_ hev
    have h1 := (hasDerivAt_deriv_Tfun hx.1 hx.2).const_mul cauchyGamma
    have h2 : HasDerivAt (fun y : ℝ => 18 * (y - c)) 18 x :=
      (HasDerivAt.const_mul (18 : ℝ) ((hasDerivAt_id x).sub_const c)).congr_deriv (by ring)
    exact h1.neg.sub h2
  refine convexOn_of_deriv2_nonneg (convex_Ioo 0 1)
    (fun x hx => ((hd x hx).continuousAt).continuousWithinAt) ?_ ?_ ?_
  · rw [hint]; exact fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  · rw [hint]; exact fun x hx => (hd2 x hx).differentiableAt.differentiableWithinAt
  · rw [hint]
    intro x hx
    have hV : -2 * (2 - x) / (x ^ 2 * (1 - x)) ≤ -27 / 2 := by
      rw [← deriv2_Tfun hx.1 hx.2]; exact deriv2_Tfun_le hx.1 hx.2
    rw [show deriv^[2] (fun r => -(cauchyGamma * Tfun r) - 9 * (r - c) ^ 2) x
        = deriv (deriv fun r => -(cauchyGamma * Tfun r) - 9 * (r - c) ^ 2) x by
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq],
      (hd2 x hx).deriv, cauchyGamma_eq]
    linarith

/-- **The quadratic lower bound.** `Q'' ≥ 18` on `(0, 1)`, so `Q` dominates its tangent
parabola at any sample point of the interval. -/
theorem Qfun_ge_quadratic {r c D : ℝ} (hr : 0 < r) (hr' : r < 1) (hc : 0 < c) (hc' : c < 1)
    (hD : HasDerivAt Qfun D c) : Qfun c + D * (r - c) + 9 * (r - c) ^ 2 ≤ Qfun r := by
  have hconv : ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun x => Qfun x - 9 * (x - c) ^ 2) := by
    have h2 : ConvexOn ℝ (Ioo (0 : ℝ) 1)
        (fun x : ℝ => Jfun (2 * x / looseRadius) + (-(cauchyGamma * Tfun x) - 9 * (x - c) ^ 2)) :=
      convexOn_Jfun_comp.add (convexOn_neg_gamma_Tfun c)
    have hfe : (fun x : ℝ => Jfun (2 * x / looseRadius)
        + (-(cauchyGamma * Tfun x) - 9 * (x - c) ^ 2))
        = fun x : ℝ => Qfun x - 9 * (x - c) ^ 2 := by
      funext x; simp only [Qfun]; ring
    rwa [hfe] at h2
  have hz : HasDerivAt (fun x : ℝ => 9 * (x - c) ^ 2) 0 c :=
    (HasDerivAt.const_mul (9 : ℝ) (((hasDerivAt_id c).sub_const c).fun_pow 2)).congr_deriv (by simp)
  have hgD : HasDerivAt (fun x : ℝ => Qfun x - 9 * (x - c) ^ 2) D c :=
    (hD.sub hz).congr_deriv (by ring)
  have hmain := tangent_le hconv (mem_Ioo.2 ⟨hc, hc'⟩) (mem_Ioo.2 ⟨hr, hr'⟩) hgD
  linarith

/-- **The one-variable certificate.** `Q ≥ 0` on the whole of `(0, 1)`. -/
theorem Qfun_nonneg {r : ℝ} (hr : 0 < r) (hr' : r < 1) : 0 ≤ Qfun r := by
  rcases le_or_gt r (1 / 2) with h | h
  · exact Qfun_nonneg_of_le_half hr h
  obtain ⟨D, hD, hDlt⟩ := exists_deriv_Qfun_r0
  have key := Qfun_ge_quadratic hr hr' (by norm_num) (by norm_num) hD
  have hsq : D ^ 2 < (1 / 10000 : ℝ) ^ 2 := sq_lt_sq' (abs_lt.1 hDlt).1 (abs_lt.1 hDlt).2
  nlinarith [Qfun_r0_gt, sq_nonneg (3 * (r - 3457 / 4000) + D / 6)]

/-- **The certificate behind the generator sign inside the unit diamond.** -/
theorem certificate {r : ℝ} (hr : 0 < r) (hr' : r < 1) :
    looseBump * looseRadius * (looseRadius - 1) * Tfun r ≤ Jfun (2 * r / looseRadius) := by
  have h := Qfun_nonneg hr hr'
  simp only [Qfun, cauchyGamma] at h
  linarith

/-- **The companion bound outside the unit diamond**: `ε (2 − 2 log 2) ≤ 1 / (R (R − 1))`. -/
theorem exterior_certificate :
    looseBump * (2 - 2 * Real.log 2) ≤ 1 / (looseRadius * (looseRadius - 1)) := by
  rw [show (1 : ℝ) / (looseRadius * (looseRadius - 1)) = 4000000 / 6823209 by
    norm_num [looseRadius], looseBump]
  linarith [Real.log_two_gt_d9]

end CenteredMaximal.Cauchy

end

end
