/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.TailSeries

/-!
# The anti-radial reserve of the exterior tail's generator

`CenteredMaximal.Fractional.jumpGen_truncTail_ge_radial` keeps **two** of the four displaced points
of the two second differences of the exterior tail: in each coordinate direction one of the two
points has diamond radius exactly `r + |t|`, and the other is discarded as merely nonnegative.
**That is not affordable.**  The two discarded points carry a reserve of about `0.78` at the scale
of the `α = 6/5` comparison certificate, whose leaf margin is `1.4 · 10⁻⁴`; measured on the first
`400` of the certificate's `4582` rectangles, dropping them makes `299` of them fail, by as much as
`0.88`.  This file recovers them.

## The anti-radial minorant

Write `u = |z₀|`, `v = |z₁|`, `s = |t|`.  The two radii of the `j`-th second difference are
`u + s + v = r + s` and `|u − s| + v`, and the second one is at least `s − (u − v)`, because
`|u − s| ≥ s − u`.  Interchanging the two coordinates turns `u − v` into `v − u`, so the two
discarded points contribute the two *opposite* shifts `±d`, `d = u − v`, of the profile

`antiRadial α R w t = (R^{−α} − (|t| − w)^{−α})₊`,

written here as `(R^{−α} − max(|t| − w) R ^ {−α})₊` so that it is a composition of continuous
functions rather than a guarded expression: clamping the radius at `R` is invisible, since the
positive part vanishes below `R` anyway.

## The even series

Substituting `q = |t| − w` turns `∫ antiRadial α R w t |t|^{−(1+α)} dt` into
`2 ∫_R^∞ (R^{−α} − q^{−α}) (q + w)^{−1−α} dq`, the *same* integral as the radial reserve of
`CenteredMaximal.Fractional.TailSeries` with `r` replaced by `−w`.  A single such integral is
therefore an *alternating* series in `w`, whose partial sums are not lower bounds.  The **sum of
the two opposite shifts** is not:

`(q + w)^{−1−α} + (q − w)^{−1−α} = 2 q^{−1−α} ∑_n binomCoeff α n (w/q)^n [n even]`,

and every even-index term is nonnegative, so every partial sum minorises.  Integrating termwise
against `∫_R^∞ (R^{−α} − q^{−α}) q^{−(α+n)−1} dq` exactly as in `integral_Ioi_tailSum` gives

`4 R^{−2α} ∑_{n < K} evenTailCoeff α n (w/R)^n ≤ (the two anti-radial integrals)`,

with `evenTailCoeff α n = tailCoeff α n` for even `n` and `0` for odd `n`.  At `w = 0` the `K = 1`
truncation already gives `2 R^{−2α}/α`, which is the bulk of the missing reserve.

## Main results

* `evenBinom`, `evenTailCoeff`, `sum_evenBinom_le`: the even parts of the two coefficient
  sequences, and **the only analytic input**: `2 ∑_{n<K} evenBinom α n x^n ≤ (1−x)^{−(1+α)} +
  (1+x)^{−(1+α)}` for `|x| < 1`, from `hasSum_binomCoeff` at `x` and at `−x`.
* `antiRadial`, `antiRadial_of_le`, `antiRadial_of_lt`, `antiRadial_abs`: the minorant.
* `integral_antiRadial_eq_Ioi`: **the substitution.**  The whole-line integral of the minorant is
  `2 ∫_R^∞ (R^{−α} − p^{−α})₊ (p + w)^{−(1+α)} dp`.
* `integral_antiRadial_pair_ge`: **the reserve bound.**
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace CenteredMaximal.Fractional

/-! ### The even parts of the two coefficient sequences -/

/-- The even part of the binomial coefficient sequence of `(1 - x) ^ (-(1 + α))`. -/
def evenBinom (α : ℝ) (n : ℕ) : ℝ := if n % 2 = 0 then binomCoeff α n else 0

/-- The even part of the tail coefficient sequence. -/
def evenTailCoeff (α : ℝ) (n : ℕ) : ℝ := if n % 2 = 0 then tailCoeff α n else 0

theorem evenBinom_nonneg {α : ℝ} (hα : 0 < α) (n : ℕ) : 0 ≤ evenBinom α n := by
  rw [evenBinom]
  split
  · exact binomCoeff_nonneg hα n
  · exact le_refl 0

theorem evenTailCoeff_nonneg {α : ℝ} (hα : 0 < α) (n : ℕ) : 0 ≤ evenTailCoeff α n := by
  rw [evenTailCoeff]
  split
  · exact (tailCoeff_pos hα n).le
  · exact le_refl 0

/-- The even tail coefficient is the even binomial coefficient times the same rational factor that
relates `tailCoeff` to `binomCoeff`. -/
theorem evenTailCoeff_eq (α : ℝ) (n : ℕ) :
    evenTailCoeff α n = evenBinom α n * α / ((α + n) * (2 * α + n)) := by
  rw [evenTailCoeff, evenBinom]
  split
  · rw [tailCoeff]
  · rw [zero_mul, zero_div]

/-- **The two-sided binomial identity.**  Adding the series at `x` and at `-x` doubles the even
terms and kills the odd ones. -/
theorem binomCoeff_add_neg (α : ℝ) (n : ℕ) (x : ℝ) :
    binomCoeff α n * x ^ n + binomCoeff α n * (-x) ^ n = 2 * (evenBinom α n * x ^ n) := by
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_pow, evenBinom, if_pos (Nat.even_iff.1 he)]
    ring
  · have h1 : n % 2 = 1 := Nat.odd_iff.1 ho
    rw [ho.neg_pow, evenBinom, if_neg (by omega)]
    ring

/-- Every term of the even series is nonnegative: an even power of a real is. -/
theorem evenBinom_mul_pow_nonneg {α : ℝ} (hα : 0 < α) (n : ℕ) (x : ℝ) :
    0 ≤ evenBinom α n * x ^ n := by
  rcases Nat.even_or_odd n with he | ho
  · exact mul_nonneg (evenBinom_nonneg hα n) (he.pow_nonneg x)
  · have h1 : n % 2 = 1 := Nat.odd_iff.1 ho
    rw [evenBinom, if_neg (by omega), zero_mul]

/-- **Every truncation of the even binomial series underestimates the symmetrised power.**  This is
the one analytic input of the anti-radial reserve, and the reason the reserve is stated for the
*pair* of opposite shifts: a single shift gives an alternating series, whose partial sums are not
lower bounds. -/
theorem sum_evenBinom_le {α x : ℝ} (hα : 0 < α) (hx : |x| < 1) (K : ℕ) :
    2 * ∑ n ∈ Finset.range K, evenBinom α n * x ^ n
      ≤ (1 - x) ^ (-(1 + α)) + (1 + x) ^ (-(1 + α)) := by
  have hx' : |(-x)| < 1 := by rwa [abs_neg]
  have h1 := hasSum_binomCoeff α hx
  have h2 := hasSum_binomCoeff α hx'
  have h3 : HasSum (fun n => 2 * (evenBinom α n * x ^ n))
      ((1 - x) ^ (-(1 + α)) + (1 - -x) ^ (-(1 + α))) :=
    (h1.add h2).congr_fun fun n => (binomCoeff_add_neg α n x).symm
  rw [show (1 : ℝ) - -x = 1 + x from by ring] at h3
  have hle := sum_le_hasSum (Finset.range K)
    (fun n _ => by
      have := evenBinom_mul_pow_nonneg hα n x
      linarith) h3
  rw [← Finset.mul_sum] at hle
  exact hle

/-! ### The anti-radial minorant -/

/-- The anti-radial minorant `(R^{−α} − (|t| − w)^{−α})₊` of the *discarded* displaced point of a
second difference of the exterior tail.  The radius is clamped at `R` from below, which changes
nothing — the positive part vanishes at radius `R` — and makes the profile a composition of
continuous functions with no case split. -/
def antiRadial (α R w t : ℝ) : ℝ := max (R ^ (-α) - (max (|t| - w) R) ^ (-α)) 0

theorem antiRadial_nonneg (α R w t : ℝ) : 0 ≤ antiRadial α R w t := le_max_right _ _

theorem antiRadial_abs (α R w t : ℝ) : antiRadial α R w |t| = antiRadial α R w t := by
  rw [antiRadial, antiRadial, abs_abs]

/-- Below the truncation radius the minorant vanishes. -/
theorem antiRadial_of_le {α R w t : ℝ} (h : |t| - w ≤ R) : antiRadial α R w t = 0 := by
  rw [antiRadial, max_eq_right h, sub_self, max_self]

/-- Above the truncation radius the clamp is invisible. -/
theorem antiRadial_of_lt {α R w t : ℝ} (h : R < |t| - w) :
    antiRadial α R w t = max (R ^ (-α) - (|t| - w) ^ (-α)) 0 := by
  rw [antiRadial, max_eq_left h.le]

/-! ### The substitution -/

/-- The anti-radial integrand as a function of `|t|`. -/
def antiIntegrand (α R w q : ℝ) : ℝ := antiRadial α R w q * q ^ (-(1 + α))

/-- The anti-radial integrand after the substitution `p = |t| − w`, on `(R, ∞)`. -/
def antiShifted (α R w p : ℝ) : ℝ := max (R ^ (-α) - p ^ (-α)) 0 * (p + w) ^ (-(1 + α))

theorem antiIntegrand_abs (α R w t : ℝ) :
    antiIntegrand α R w |t| = antiRadial α R w t * |t| ^ (-(1 + α)) := by
  rw [antiIntegrand, antiRadial_abs]

theorem antiIntegrand_nonneg (α R w q : ℝ) (hq : 0 ≤ q) : 0 ≤ antiIntegrand α R w q :=
  mul_nonneg (antiRadial_nonneg _ _ _ _) (Real.rpow_nonneg hq _)

/-- **The whole-line integral is twice a half-line integral**, the integrand being even. -/
theorem integral_antiRadial_eq (α R w : ℝ) :
    (∫ t : ℝ, antiRadial α R w t * |t| ^ (-(1 + α)))
      = 2 * ∫ q in Ioi (0 : ℝ), antiIntegrand α R w q := by
  rw [← integral_comp_abs (f := antiIntegrand α R w)]
  simp only [antiIntegrand_abs]

/-- Translating a half-line integral by `w`. -/
private theorem integral_Ioi_comp_sub (f : ℝ → ℝ) (c w : ℝ) :
    (∫ q in Ioi c, f (q - w)) = ∫ p in Ioi (c - w), f p := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have h : (fun q : ℝ => (Ioi c).indicator (fun q => f (q - w)) q)
      = fun q : ℝ => (Ioi (c - w)).indicator f (q - w) := by
    funext q
    simp only [indicator_apply, mem_Ioi]
    by_cases hq : c < q
    · rw [if_pos hq, if_pos (by linarith)]
    · rw [if_neg hq, if_neg fun hcon => hq (by linarith)]
  rw [h]
  exact integral_sub_right_eq_self _ w

/-- **The substitution.**  The whole-line integral of the anti-radial minorant is twice the
integral of `antiShifted` over `(R, ∞)`. -/
theorem integral_antiRadial_eq_Ioi {α R w : ℝ} (hw : 0 ≤ R + w) :
    (∫ t : ℝ, antiRadial α R w t * |t| ^ (-(1 + α)))
      = 2 * ∫ p in Ioi R, antiShifted α R w p := by
  rw [integral_antiRadial_eq]
  congr 1
  -- cut the half-line down to `(R + w, ∞)`, where the minorant does not vanish
  have hcut : (∫ q in Ioi (0 : ℝ), antiIntegrand α R w q)
      = ∫ q in Ioi (R + w), antiIntegrand α R w q := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
    simp only [indicator_apply, mem_Ioi]
    rcases lt_or_ge (R + w) q with h | h
    · rw [if_pos (by linarith : (0 : ℝ) < q), if_pos h]
    · rw [if_neg (by linarith : ¬R + w < q)]
      rcases le_or_gt q 0 with h0 | h0
      · rw [if_neg (by linarith : ¬(0 : ℝ) < q)]
      · rw [if_pos h0, antiIntegrand,
          antiRadial_of_le (by rw [abs_of_pos h0]; linarith), zero_mul]
  rw [hcut]
  have hpt : ∀ q : ℝ, R + w < q → antiIntegrand α R w q = antiShifted α R w (q - w) := by
    intro q hq
    have hq0 : 0 < q := lt_of_le_of_lt hw hq
    rw [antiIntegrand, antiRadial_of_lt (by rw [abs_of_pos hq0]; linarith), abs_of_pos hq0,
      antiShifted, show q - w + w = q from by ring]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun q hq => hpt q hq),
    integral_Ioi_comp_sub (antiShifted α R w) (R + w) w, show R + w - w = R from by ring]

/-! ### Integrability -/

/-- `antiShifted` is integrable on `(R, ∞)`: it is continuous there, nonnegative, and dominated by
`R ^ (-α) * (p + w) ^ (-(1+α))`, a shifted power integrable because `R + w > 0`. -/
theorem integrableOn_antiShifted {α R w : ℝ} (hα : 0 < α) (hR : 0 < R) (hw : 0 < R + w) :
    IntegrableOn (antiShifted α R w) (Ioi R) := by
  have hp0 : ∀ p ∈ Ioi R, (0 : ℝ) < p := fun p hp => lt_trans hR hp
  have hg : IntegrableOn (fun p : ℝ => R ^ (-α) * (w + p) ^ (-α - 1)) (Ioi R) :=
    (integrableOn_Ioi_shift_rpow (r := w) (b := R) hα (by linarith)).const_mul _
  have h2 : ContinuousOn (fun p : ℝ => p ^ (-α)) (Ioi R) :=
    continuousOn_id.rpow_const fun p hp => Or.inl (hp0 p hp).ne'
  have hadd : Continuous fun p : ℝ => p + w := continuous_id.add continuous_const
  have h3 : ContinuousOn (fun p : ℝ => (p + w) ^ (-(1 + α))) (Ioi R) :=
    hadd.continuousOn.rpow_const fun p hp => Or.inl (by
      have hpR : R < p := hp
      exact ne_of_gt (by linarith))
  have hcont : ContinuousOn (antiShifted α R w) (Ioi R) :=
    ((continuousOn_const.sub h2).sup continuousOn_const).mul h3
  refine hg.mono' (hcont.aestronglyMeasurable measurableSet_Ioi)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun p hp => ?_))
  have hpR : R < p := hp
  have hppos : (0 : ℝ) < p + w := by linarith
  have hpp : (0 : ℝ) ≤ (p + w) ^ (-(1 + α)) := Real.rpow_nonneg hppos.le _
  have hmax : max (R ^ (-α) - p ^ (-α)) 0 ≤ R ^ (-α) :=
    max_le (by linarith [Real.rpow_nonneg (hp0 p hp).le (-α)])
      (Real.rpow_nonneg hR.le _)
  have hnn : 0 ≤ antiShifted α R w p := mul_nonneg (le_max_right _ _) hpp
  rw [Real.norm_eq_abs, abs_of_nonneg hnn, antiShifted,
    show w + p = p + w from by ring, show (-α : ℝ) - 1 = -(1 + α) from by ring]
  exact mul_le_mul_of_nonneg_right hmax hpp

/-! ### The finite even sum -/

/-- The finite even sum that dominates the pair of anti-radial integrands pointwise, and integrates
termwise to the even tail series. -/
def antiSumTerm (α R w : ℝ) (K : ℕ) (p : ℝ) : ℝ :=
  2 * ∑ n ∈ Finset.range K, evenBinom α n * w ^ n *
    (R ^ (-α) * p ^ (-(α + (n : ℝ)) - 1) - p ^ (-(2 * α + (n : ℝ)) - 1))

theorem integrableOn_antiSumTerm {α R w : ℝ} (hα : 0 < α) (hR : 0 < R) (K : ℕ) :
    IntegrableOn (antiSumTerm α R w K) (Ioi R) := by
  refine (integrable_finsetSum _ fun n _ => ?_).const_mul _
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have e1 : IntegrableOn (fun p : ℝ => p ^ (-(α + (n : ℝ)) - 1)) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hR
  have e2 : IntegrableOn (fun p : ℝ => p ^ (-(2 * α + (n : ℝ)) - 1)) (Ioi R) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hR
  exact ((e1.const_mul _).sub e2).const_mul _

/-- **The pointwise domination.**  Above the truncation radius the finite even sum is at most the
sum of the two oppositely shifted integrands. -/
theorem antiSumTerm_le {α R w p : ℝ} (hα : 0 < α) (hw : |w| < R) (hp : R < p) (K : ℕ) :
    antiSumTerm α R w K p ≤ antiShifted α R w p + antiShifted α R (-w) p := by
  have hR : 0 < R := lt_of_le_of_lt (abs_nonneg w) hw
  have hp0 : 0 < p := lt_trans hR hp
  have hwp : |w| < p := lt_trans hw hp
  have hwlo : -p < w := by linarith [neg_abs_le w]
  have hwhi : w < p := lt_of_le_of_lt (le_abs_self w) hwp
  have hpw : (0 : ℝ) < p + w := by linarith
  have hpm : (0 : ℝ) < p - w := by linarith
  have hx : |w / p| < 1 := by
    rw [abs_div, abs_of_pos hp0, div_lt_one hp0]
    exact hwp
  have hup : (0 : ℝ) < p ^ (-(1 + α)) := Real.rpow_pos_of_pos hp0 _
  have he1 : (1 : ℝ) + w / p = (p + w) / p := by field_simp
  have he2 : (1 : ℝ) - w / p = (p - w) / p := by field_simp
  -- the positive part is resolved above `R`
  have hanti : p ^ (-α) ≤ R ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos hR hp.le (neg_nonpos.2 hα.le)
  have hnn : (0 : ℝ) ≤ R ^ (-α) - p ^ (-α) := by linarith
  have hmax : max (R ^ (-α) - p ^ (-α)) 0 = R ^ (-α) - p ^ (-α) := max_eq_left hnn
  -- the two shifted powers, factored
  have hfacm : (p - w) ^ (-(1 + α)) = p ^ (-(1 + α)) * (1 - w / p) ^ (-(1 + α)) := by
    rw [← Real.mul_rpow hp0.le (by rw [he2]; exact (div_pos hpm hp0).le)]
    congr 1
    field_simp
  have hfacp : (p + w) ^ (-(1 + α)) = p ^ (-(1 + α)) * (1 + w / p) ^ (-(1 + α)) := by
    rw [← Real.mul_rpow hp0.le (by rw [he1]; exact (div_pos hpw hp0).le)]
    congr 1
    field_simp
  have hpair : 2 * (p ^ (-(1 + α)) * ∑ n ∈ Finset.range K, evenBinom α n * (w / p) ^ n)
      ≤ (p + w) ^ (-(1 + α)) + (p - w) ^ (-(1 + α)) := by
    have hstep := mul_le_mul_of_nonneg_left (sum_evenBinom_le hα hx K) hup.le
    rw [hfacp, hfacm]
    calc 2 * (p ^ (-(1 + α)) * ∑ n ∈ Finset.range K, evenBinom α n * (w / p) ^ n)
        = p ^ (-(1 + α)) * (2 * ∑ n ∈ Finset.range K, evenBinom α n * (w / p) ^ n) := by ring
      _ ≤ p ^ (-(1 + α)) * ((1 - w / p) ^ (-(1 + α)) + (1 + w / p) ^ (-(1 + α))) := hstep
      _ = p ^ (-(1 + α)) * (1 + w / p) ^ (-(1 + α))
            + p ^ (-(1 + α)) * (1 - w / p) ^ (-(1 + α)) := by ring
  -- the sum rewritten with the common factor pulled out
  have hsum : ∑ n ∈ Finset.range K, evenBinom α n * w ^ n *
      (R ^ (-α) * p ^ (-(α + (n : ℝ)) - 1) - p ^ (-(2 * α + (n : ℝ)) - 1))
      = (R ^ (-α) - p ^ (-α)) *
        (p ^ (-(1 + α)) * ∑ n ∈ Finset.range K, evenBinom α n * (w / p) ^ n) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    have hpn : (p : ℝ) ^ n ≠ 0 := by positivity
    have e1 : p ^ (-(2 * α + (n : ℝ)) - 1) = p ^ (-α) * p ^ (-(α + (n : ℝ)) - 1) := by
      rw [← Real.rpow_add hp0]
      congr 1
      ring
    have e2 : p ^ (-(α + (n : ℝ)) - 1) = p ^ (-(1 + α)) * (p ^ n)⁻¹ := by
      rw [← Real.rpow_natCast p n, ← Real.rpow_neg hp0.le, ← Real.rpow_add hp0]
      congr 1
      ring
    rw [e1, e2, div_pow]
    field_simp
  simp only [antiSumTerm, antiShifted, hsum, hmax, show p + -w = p - w from by ring]
  calc 2 * ((R ^ (-α) - p ^ (-α)) *
        (p ^ (-(1 + α)) * ∑ n ∈ Finset.range K, evenBinom α n * (w / p) ^ n))
      = (R ^ (-α) - p ^ (-α)) *
        (2 * (p ^ (-(1 + α)) * ∑ n ∈ Finset.range K, evenBinom α n * (w / p) ^ n)) := by ring
    _ ≤ (R ^ (-α) - p ^ (-α)) * ((p + w) ^ (-(1 + α)) + (p - w) ^ (-(1 + α))) :=
        mul_le_mul_of_nonneg_left hpair hnn
    _ = (R ^ (-α) - p ^ (-α)) * (p + w) ^ (-(1 + α))
          + (R ^ (-α) - p ^ (-α)) * (p - w) ^ (-(1 + α)) := by ring

/-! ### Termwise integration -/

/-- The half-line integral of a negative power, from `integral_Ioi_rpow_of_lt`. -/
private theorem integral_Ioi_rpow_neg {b P : ℝ} (hP : 0 < P) (hb : 0 < b) :
    (∫ t in Ioi b, t ^ (-P - 1)) = b ^ (-P) / P := by
  rw [integral_Ioi_rpow_of_lt (by linarith : -P - 1 < -1) hb,
    show -P - 1 + 1 = -P from by ring]
  field_simp

/-- **Termwise integration of the finite even sum.** -/
theorem integral_Ioi_antiSumTerm {α R w : ℝ} (hα : 0 < α) (hR : 0 < R) (K : ℕ) :
    (∫ p in Ioi R, antiSumTerm α R w K p)
      = 2 * R ^ (-2 * α) * ∑ n ∈ Finset.range K, evenTailCoeff α n * (w / R) ^ n := by
  have hterm : ∀ n : ℕ, (∫ p in Ioi R, evenBinom α n * w ^ n *
      (R ^ (-α) * p ^ (-(α + (n : ℝ)) - 1) - p ^ (-(2 * α + (n : ℝ)) - 1)))
      = R ^ (-2 * α) * (evenTailCoeff α n * (w / R) ^ n) := by
    intro n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp1 : (0 : ℝ) < α + n := by positivity
    have hp2 : (0 : ℝ) < 2 * α + n := by positivity
    have hRn : (R : ℝ) ^ n ≠ 0 := by positivity
    have e1 : IntegrableOn (fun p : ℝ => p ^ (-(α + (n : ℝ)) - 1)) (Ioi R) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hR
    have e2 : IntegrableOn (fun p : ℝ => p ^ (-(2 * α + (n : ℝ)) - 1)) (Ioi R) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hR
    rw [integral_const_mul, integral_sub (e1.const_mul _) e2, integral_const_mul,
      integral_Ioi_rpow_neg hp1 hR, integral_Ioi_rpow_neg hp2 hR]
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
    rw [hA, hB, key, evenTailCoeff_eq, div_pow]
    field_simp
    ring
  have hsum : (∫ p in Ioi R, ∑ n ∈ Finset.range K, evenBinom α n * w ^ n *
        (R ^ (-α) * p ^ (-(α + (n : ℝ)) - 1) - p ^ (-(2 * α + (n : ℝ)) - 1)))
      = R ^ (-2 * α) * ∑ n ∈ Finset.range K, evenTailCoeff α n * (w / R) ^ n := by
    rw [integral_finsetSum _ (fun n _ => by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      exact (((integrableOn_Ioi_rpow_of_lt
        (show -(α + (n : ℝ)) - 1 < -1 from by linarith) hR).const_mul _).sub
        (integrableOn_Ioi_rpow_of_lt (show -(2 * α + (n : ℝ)) - 1 < -1 from by linarith)
          hR)).const_mul _), Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => hterm n
  rw [show antiSumTerm α R w K = fun p : ℝ => 2 * ∑ n ∈ Finset.range K, evenBinom α n * w ^ n *
      (R ^ (-α) * p ^ (-(α + (n : ℝ)) - 1) - p ^ (-(2 * α + (n : ℝ)) - 1)) from rfl,
    integral_const_mul, hsum]
  ring

/-! ### The reserve bound -/

/-- **Any partial sum of the even tail series is a lower bound for the pair of anti-radial
integrals.**  This is the form the `α = 6/5` leaf checks consume: `K` is chosen per leaf, and
`evenTailCoeff (6/5) n` is exactly rational. -/
theorem integral_antiRadial_pair_ge {α R w : ℝ} (hα : 0 < α) (hw : |w| < R) (K : ℕ) :
    4 * R ^ (-2 * α) * ∑ n ∈ Finset.range K, evenTailCoeff α n * (w / R) ^ n
      ≤ (∫ t : ℝ, antiRadial α R w t * |t| ^ (-(1 + α)))
        + ∫ t : ℝ, antiRadial α R (-w) t * |t| ^ (-(1 + α)) := by
  have hR : 0 < R := lt_of_le_of_lt (abs_nonneg w) hw
  have hw1 : 0 < R + w := by linarith [neg_abs_le w]
  have hw2 : 0 < R + -w := by linarith [le_abs_self w]
  have hi1 : IntegrableOn (antiShifted α R w) (Ioi R) := integrableOn_antiShifted hα hR hw1
  have hi2 : IntegrableOn (antiShifted α R (-w)) (Ioi R) := integrableOn_antiShifted hα hR hw2
  have hbig : IntegrableOn
      (fun p : ℝ => antiShifted α R w p + antiShifted α R (-w) p) (Ioi R) := hi1.add hi2
  have hI := setIntegral_mono_on (integrableOn_antiSumTerm hα hR K) hbig measurableSet_Ioi
    (fun p hp => antiSumTerm_le hα hw hp K)
  rw [integral_Ioi_antiSumTerm hα hR K] at hI
  have hsplit : (∫ p in Ioi R, (antiShifted α R w p + antiShifted α R (-w) p))
      = (∫ p in Ioi R, antiShifted α R w p) + ∫ p in Ioi R, antiShifted α R (-w) p :=
    integral_add hi1 hi2
  rw [integral_antiRadial_eq_Ioi hw1.le, integral_antiRadial_eq_Ioi hw2.le,
    show (4 : ℝ) * R ^ (-2 * α) * ∑ n ∈ Finset.range K, evenTailCoeff α n * (w / R) ^ n
      = 2 * (2 * R ^ (-2 * α) * ∑ n ∈ Finset.range K, evenTailCoeff α n * (w / R) ^ n)
      from by ring]
  rw [hsplit] at hI
  linarith

end CenteredMaximal.Fractional

end

end
