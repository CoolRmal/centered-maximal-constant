/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.Pairing
public import CenteredMaximal.Cauchy.BaseDensity
public import CenteredMaximal.Cauchy.BumpGenerator

/-!
# The bounded part of the loose kernel satisfies the pairing hypothesis

The loose comparison kernel of `CenteredMaximal.Cauchy.LooseKernel` splits into the singular cusp
`(R/r − 1)₊/(R − 1)` inside the diamond of radius `R = looseRadius` and the *bounded part*
`g = tail R − ε ψ` with `ε = looseBump`, the exterior tail of
`CenteredMaximal.Cauchy.BaseDensity` minus the bump of `CenteredMaximal.Cauchy.BumpGenerator`.
This file verifies the hypothesis `hfin` of `CenteredMaximal.integral_mul_jumpGen_comm` for `g`, so
that a pointwise lower bound on `jumpGen 1 g` turns into the weak statement
`0 ≤ ∫ g · jumpGen 1 φ` for nonnegative test functions `φ`.

* `integral_jumpGen_eq_zero`: the independent observation that the generator of a test function
  integrates to zero, obtained from the easy direction of the pairing identity with `g = 1`,
  whose second differences vanish;
* `boundedPart`: the bounded part, written as `boundedProfile ∘ diamondNorm` for the radial profile
  `boundedProfile t = (t − R)₊/(t (R − 1)) − ε (1 − t)₊²`. The first summand is the tail profile
  `(1 − R/t)₊/(R − 1)` for `t > 0` (`cuspTail_eq_tailProfile`), but — unlike it — vanishes at
  `t = 0`, where Lean's `R / 0 = 0` would otherwise make the tail jump to `1/(R − 1)`. The two
  agree off the origin (`boundedPart_eq`), a null set;
* `lipschitzWith_boundedPart` and `abs_boundedPart_le`: `g` is `6`-Lipschitz and bounded by
  `C = 1/(R − 1) + ε`. The radial profile is `3`-Lipschitz on `[0, ∞)` — the cusp profile with
  constant `1/(R(R − 1)) ≤ 1` and the bump profile with constant `2ε ≤ 2` — and `diamondNorm` is
  `2`-Lipschitz;
* `abs_secondDiff_boundedPart_le`: at distance `kinkDist z` from the two axes and from the circle
  `{r = R}` the second difference of `g` is quadratically small,
  `|Δ_j^t g(z)| ≤ M₂ t²` for `|t| ≤ kinkDist z`, with `M₂ = 2/(R²(R − 1)) + 2ε`. For such a step
  the sign of `z j + t` is constant, so the diamond radius is affine in the step and the second
  difference collapses to the radial one, `P(r + u) + P(r − u) − 2P(r)` with `|u| = |t|`. On the
  cusp profile that second difference is computed exactly,
  `−2R u²/((R − 1) r (r² − u²))`, and `r(r² − u²) ≥ R³`; on the bump profile `(1 − t)₊²` it is
  bounded by `2u²` with no side condition;
* `integrableOn_log_kinkDist`: `log (1/kinkDist)` is integrable on every compact set, because it is
  dominated by `|log u| + |log v| + |log (r − R)|`, the first two integrable by Tonelli on
  `ℝ × ℝ` and the last by the radial formula `lintegral_comp_diamondNorm`;
* `integrable_uncurry_secondDiff_boundedPart`: the hypothesis `hfin` at `α = 1`, from
  `lintegral_secondDiff_mul_rpow_le_of_lipschitz_of_c2` at the scale `δ = kinkDist z`. Since
  `kinkDist` vanishes on the axes and on `{r = R}`, where the inner integral really is infinite,
  the bound is taken with values in `ℝ≥0∞` and is `⊤` there; the exceptional set is null, so the
  outer integral is unaffected (`integrable_uncurry_of_enorm_bound`);
* `nonneg_integral_boundedPart_mul_jumpGen`: the payoff.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace CenteredMaximal.Cauchy

/-! ### The generator of a test function has vanishing integral -/

/-- **The generator of a test function integrates to zero.** This is the easy direction of the
pairing identity with `g = 1`: the second difference of a constant vanishes. -/
theorem integral_jumpGen_eq_zero {α : ℝ} (hα : 0 < α) (hα' : α < 2)
    {φ : (Fin 2 → ℝ) → ℝ} (hφ : IsTestFunction φ) : ∫ z, jumpGen α φ z = 0 := by
  have h := integral_mul_jumpGen_eq_integral_integral (g := fun _ => (1 : ℝ)) hα hα'
    measurable_const (C := 1) (fun _ => by norm_num) hφ
  simp only [one_mul] at h
  rw [h]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hz : ∀ t : ℝ, (∫ z, secondDiff (fun _ => (1 : ℝ)) j z t * φ z) = 0 := by
    intro t
    have hs : ∀ z : Fin 2 → ℝ, secondDiff (fun _ => (1 : ℝ)) j z t * φ z = 0 := by
      intro z
      have h0 : secondDiff (fun _ => (1 : ℝ)) j z t = 0 := by
        rw [secondDiff]
        norm_num
      rw [h0, zero_mul]
    simp [hs]
  simp [hz]

/-! ### The bounded part of the loose kernel -/

/-- The radial profile `(t − R)₊ / (t (R − 1))` of the exterior tail. For `t > 0` this is the
profile `(1 − R/t)₊ / (R − 1)` of `tailProfile`, but it also vanishes at `t = 0`. -/
def cuspTail (t : ℝ) : ℝ := max (t - looseRadius) 0 / (t * (looseRadius - 1))

/-- The radial profile `(t − R)₊/(t (R − 1)) − ε (1 − t)₊²` of the bounded part of the loose
kernel. -/
def boundedProfile (t : ℝ) : ℝ := cuspTail t - looseBump * looseHump t

/-- The bounded part `g = tail R − ε ψ` of the loose comparison kernel, in the form that is
continuous also at the origin. -/
def boundedPart (z : Fin 2 → ℝ) : ℝ := boundedProfile (diamondNorm z)

/-- The distance from `z` to the kink set of the bounded part, capped at `1`: the two coordinate
axes, where the diamond radius is not smooth, and the circle `{r = R}`, where the exterior tail
starts. -/
def kinkDist (z : Fin 2 → ℝ) : ℝ :=
  min 1 (min |z 0| (min |z 1| |diamondNorm z - looseRadius|))

/-- The supremum bound `C = 1/(R − 1) + ε` of the bounded part. -/
def boundedC : ℝ := 1 / (looseRadius - 1) + looseBump

/-- The second-difference constant `M₂ = 2/(R²(R − 1)) + 2ε` of the bounded part. -/
def boundedM₂ : ℝ := 2 / (looseRadius ^ 2 * (looseRadius - 1)) + 2 * looseBump

/-! ### Elementary facts about the constants and the profiles -/

theorem looseRadius_sub_one_pos : (0 : ℝ) < looseRadius - 1 := by norm_num [looseRadius]

/-- `R(R − 1) ≥ 1`, which makes the cusp profile `1`-Lipschitz. -/
theorem one_le_looseRadius_mul_sub_one : (1 : ℝ) ≤ looseRadius * (looseRadius - 1) := by
  norm_num [looseRadius]

theorem looseRadius_sq_mul_sub_one_pos : (0 : ℝ) < looseRadius ^ 2 * (looseRadius - 1) := by
  norm_num [looseRadius]

theorem boundedM₂_nonneg : 0 ≤ boundedM₂ := by
  have h : (0 : ℝ) ≤ 2 / (looseRadius ^ 2 * (looseRadius - 1)) :=
    div_nonneg (by norm_num) looseRadius_sq_mul_sub_one_pos.le
  have h' := looseBump_pos
  rw [boundedM₂]
  linarith

private theorem fin_two_cases (j : Fin 2) : j = 0 ∨ j = 1 := by
  revert j
  decide

/-- The two coordinates of a point are at most its diamond radius. -/
theorem abs_le_diamondNorm (z : Fin 2 → ℝ) (j : Fin 2) : |z j| ≤ diamondNorm z := by
  rcases fin_two_cases j with rfl | rfl
  · exact le_add_of_nonneg_right (abs_nonneg _)
  · exact le_add_of_nonneg_left (abs_nonneg _)

theorem looseHump_le_one {t : ℝ} (ht : 0 ≤ t) : looseHump t ≤ 1 := by
  have h1 : max (1 - t) 0 ≤ 1 := max_le (by linarith) zero_le_one
  have h2 : (0 : ℝ) ≤ max (1 - t) 0 := le_max_right _ _
  rw [looseHump]
  nlinarith

theorem cuspTail_eq_zero {t : ℝ} (ht : t ≤ looseRadius) : cuspTail t = 0 := by
  rw [cuspTail, max_eq_right (by linarith), zero_div]

theorem cuspTail_of_le {t : ℝ} (ht : looseRadius ≤ t) :
    cuspTail t = (t - looseRadius) / (t * (looseRadius - 1)) := by
  rw [cuspTail, max_eq_left (by linarith)]

theorem cuspTail_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ cuspTail t :=
  div_nonneg (le_max_right _ _) (mul_nonneg ht looseRadius_sub_one_pos.le)

theorem cuspTail_le (t : ℝ) : cuspTail t ≤ 1 / (looseRadius - 1) := by
  have hR := looseRadius_sub_one_pos
  rcases le_or_gt t looseRadius with h | h
  · rw [cuspTail_eq_zero h]
    exact div_nonneg zero_le_one hR.le
  · have ht0 : 0 < t := looseRadius_pos.trans h
    rw [cuspTail_of_le h.le, div_le_div_iff₀ (mul_pos ht0 hR) hR]
    nlinarith [looseRadius_pos]

/-- Off the origin the profile `cuspTail` is the tail profile of `BaseDensity`. -/
theorem cuspTail_eq_tailProfile {t : ℝ} (ht : 0 < t) : cuspTail t = tailProfile looseRadius t := by
  rw [tailProfile]
  rcases le_or_gt t looseRadius with h | h
  · rw [cuspTail_eq_zero h, max_eq_right (by rw [sub_nonpos, le_div_iff₀ ht]; linarith), zero_div]
  · rw [cuspTail_of_le h.le, max_eq_left (by rw [sub_nonneg, div_le_one ht]; linarith)]
    rw [div_eq_div_iff (mul_pos ht looseRadius_sub_one_pos).ne' looseRadius_sub_one_pos.ne']
    field_simp

/-- Off the origin the bounded part is the exterior tail minus the bump. -/
theorem boundedPart_eq {z : Fin 2 → ℝ} (hz : z ≠ 0) :
    boundedPart z = tail looseRadius z - looseBump * bump z := by
  rw [boundedPart, boundedProfile, cuspTail_eq_tailProfile (diamondNorm_pos hz), tail_eq, bump]

/-! ### The bounded part is Lipschitz and bounded -/

/-- The diamond radius is `2`-Lipschitz for the supremum norm of the plane. -/
theorem lipschitzWith_diamondNorm : LipschitzWith 2 diamondNorm := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  have hc : ∀ i : Fin 2, |z i - w i| ≤ dist z w := by
    intro i
    rw [dist_eq_norm]
    have h := norm_le_pi_norm (z - w) i
    rwa [Pi.sub_apply, Real.norm_eq_abs] at h
  have e0 := abs_le.1 (abs_abs_sub_abs_le_abs_sub (z 0) (w 0))
  have e1 := abs_le.1 (abs_abs_sub_abs_le_abs_sub (z 1) (w 1))
  have h0 := hc 0
  have h1 := hc 1
  rw [Real.dist_eq, diamondNorm, diamondNorm, abs_le]
  constructor <;> push_cast <;> linarith [e0.1, e0.2, e1.1, e1.2]

/-- The cusp profile is `1`-Lipschitz: its derivative `R/(t²(R − 1))` is at most
`1/(R(R − 1)) ≤ 1` beyond `R`, and it vanishes before `R`. -/
theorem abs_cuspTail_sub_le (r s : ℝ) : |cuspTail r - cuspTail s| ≤ |r - s| := by
  have hR := looseRadius_sub_one_pos
  have hRR := one_le_looseRadius_mul_sub_one
  have key : ∀ a b : ℝ, a ≤ b → |cuspTail a - cuspTail b| ≤ |a - b| := by
    intro a b hab
    rcases le_or_gt b looseRadius with hb | hb
    · rw [cuspTail_eq_zero hb, cuspTail_eq_zero (hab.trans hb), sub_self, abs_zero]
      exact abs_nonneg _
    · have hb0 : 0 < b := looseRadius_pos.trans hb
      have hdb : 0 < b * (looseRadius - 1) := mul_pos hb0 hR
      have habs : |a - b| = b - a := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
      rcases le_or_gt a looseRadius with ha' | ha'
      · have hb1 : 1 ≤ b * (looseRadius - 1) := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ b - looseRadius) hR.le]
        rw [cuspTail_eq_zero ha', zero_sub, abs_neg, cuspTail_of_le hb.le,
          abs_of_nonneg (div_nonneg (by linarith) hdb.le), habs, div_le_iff₀ hdb]
        nlinarith [mul_le_mul_of_nonneg_left hb1 (by linarith : (0 : ℝ) ≤ b - looseRadius),
          mul_le_mul_of_nonneg_right (by linarith : b - looseRadius ≤ b - a) hdb.le]
      · have ha0 : 0 < a := looseRadius_pos.trans ha'
        have hda : 0 < a * (looseRadius - 1) := mul_pos ha0 hR
        have hmono : (a - looseRadius) / (a * (looseRadius - 1))
            ≤ (b - looseRadius) / (b * (looseRadius - 1)) := by
          rw [div_le_div_iff₀ hda hdb]
          nlinarith [mul_nonneg (mul_nonneg hR.le looseRadius_pos.le) (sub_nonneg.2 hab)]
        have hab2 : looseRadius * looseRadius ≤ a * b := by
          nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ a - looseRadius)
            (by linarith : (0 : ℝ) ≤ b - looseRadius)]
        have hstep : looseRadius ≤ a * b * (looseRadius - 1) := by
          nlinarith [mul_le_mul_of_nonneg_right hab2 hR.le,
            mul_le_mul_of_nonneg_left hRR looseRadius_pos.le]
        have hstep' : looseRadius * (looseRadius - 1)
            ≤ b * (looseRadius - 1) * (a * (looseRadius - 1)) := by
          nlinarith [mul_le_mul_of_nonneg_right hstep hR.le]
        rw [cuspTail_of_le ha'.le, cuspTail_of_le hb.le, habs, abs_sub_comm,
          abs_of_nonneg (sub_nonneg.2 hmono), div_sub_div _ _ hdb.ne' hda.ne',
          div_le_iff₀ (mul_pos hdb hda)]
        nlinarith [mul_le_mul_of_nonneg_left hstep' (sub_nonneg.2 hab)]
  rcases le_total r s with h | h
  · exact key r s h
  · rw [abs_sub_comm, abs_sub_comm r s]
    exact key s r h

/-- The bump profile `(1 − t)₊²` is `2`-Lipschitz on the half-line. -/
theorem abs_looseHump_sub_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |looseHump r - looseHump s| ≤ 2 * |r - s| := by
  have h1 : |max (1 - r) 0 - max (1 - s) 0| ≤ |r - s| := by
    refine (abs_max_sub_max_le_abs _ _ _).trans_eq ?_
    rw [show 1 - r - (1 - s) = -(r - s) by ring, abs_neg]
  have ha : (0 : ℝ) ≤ max (1 - r) 0 := le_max_right _ _
  have hb : (0 : ℝ) ≤ max (1 - s) 0 := le_max_right _ _
  have ha1 : max (1 - r) 0 ≤ 1 := max_le (by linarith) zero_le_one
  have hb1 : max (1 - s) 0 ≤ 1 := max_le (by linarith) zero_le_one
  calc |looseHump r - looseHump s|
      = |max (1 - r) 0 - max (1 - s) 0| * |max (1 - r) 0 + max (1 - s) 0| := by
        rw [looseHump, looseHump, ← abs_mul]
        congr 1
        ring
    _ ≤ |r - s| * 2 := by
        refine mul_le_mul h1 ?_ (abs_nonneg _) (abs_nonneg _)
        rw [abs_of_nonneg (by linarith)]
        linarith
    _ = 2 * |r - s| := by ring

/-- The triangle inequality in the form used for splitting a second difference. -/
private theorem abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  exact (abs_add_le a (-b)).trans_eq (by rw [abs_neg])

/-- The radial profile of the bounded part is `3`-Lipschitz on the half-line. -/
theorem abs_boundedProfile_sub_le {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |boundedProfile r - boundedProfile s| ≤ 3 * |r - s| := by
  have hc := abs_le.1 (abs_cuspTail_sub_le r s)
  have he : |looseBump * (looseHump r - looseHump s)| ≤ 2 * |r - s| := by
    rw [abs_mul, abs_of_nonneg looseBump_pos.le]
    calc looseBump * |looseHump r - looseHump s| ≤ 1 * (2 * |r - s|) :=
          mul_le_mul looseBump_lt_one.le (abs_looseHump_sub_le hr hs) (abs_nonneg _) zero_le_one
      _ = 2 * |r - s| := one_mul _
  have hh := abs_le.1 he
  have hsplit : boundedProfile r - boundedProfile s
      = cuspTail r - cuspTail s - looseBump * (looseHump r - looseHump s) := by
    simp only [boundedProfile]
    ring
  rw [hsplit, abs_le]
  constructor <;> linarith [hc.1, hc.2, hh.1, hh.2]

/-- **The bounded part is `6`-Lipschitz**: its `3`-Lipschitz radial profile composed with the
`2`-Lipschitz diamond radius. -/
theorem lipschitzWith_boundedPart : LipschitzWith 6 boundedPart := by
  refine LipschitzWith.of_dist_le_mul fun z w => ?_
  have h := abs_boundedProfile_sub_le (diamondNorm_nonneg z) (diamondNorm_nonneg w)
  have hd : |diamondNorm z - diamondNorm w| ≤ 2 * dist z w := by
    have := lipschitzWith_diamondNorm.dist_le_mul z w
    rwa [Real.dist_eq, show ((2 : ℝ≥0) : ℝ) = 2 by norm_num] at this
  rw [Real.dist_eq, boundedPart, boundedPart, show ((6 : ℝ≥0) : ℝ) = 6 by norm_num]
  linarith

theorem continuous_boundedPart : Continuous boundedPart :=
  lipschitzWith_boundedPart.continuous

theorem measurable_boundedPart : Measurable boundedPart :=
  continuous_boundedPart.measurable

/-- **The bounded part is bounded** by `C = 1/(R − 1) + ε`. -/
theorem abs_boundedPart_le (z : Fin 2 → ℝ) : |boundedPart z| ≤ boundedC := by
  have hr := diamondNorm_nonneg z
  have h1 := cuspTail_nonneg hr
  have h2 := cuspTail_le (diamondNorm z)
  have h3 := looseHump_nonneg (diamondNorm z)
  have h4 := looseHump_le_one hr
  have h5 := looseBump_pos
  have h6 : 0 ≤ 1 / (looseRadius - 1) := div_nonneg zero_le_one looseRadius_sub_one_pos.le
  rw [boundedPart, boundedProfile, boundedC, abs_le]
  constructor <;> nlinarith

/-! ### The second difference near the kink set -/

theorem kinkDist_nonneg (z : Fin 2 → ℝ) : 0 ≤ kinkDist z :=
  le_min zero_le_one (le_min (abs_nonneg _) (le_min (abs_nonneg _) (abs_nonneg _)))

theorem kinkDist_le_one (z : Fin 2 → ℝ) : kinkDist z ≤ 1 := min_le_left _ _

theorem kinkDist_le_abs (z : Fin 2 → ℝ) (j : Fin 2) : kinkDist z ≤ |z j| := by
  rcases fin_two_cases j with rfl | rfl
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))

theorem kinkDist_le_abs_sub (z : Fin 2 → ℝ) :
    kinkDist z ≤ |diamondNorm z - looseRadius| :=
  (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

theorem continuous_kinkDist : Continuous kinkDist :=
  continuous_const.min (((continuous_apply 0).abs).min
    (((continuous_apply 1).abs).min ((continuous_diamondNorm.sub continuous_const).abs)))

theorem measurable_kinkDist : Measurable kinkDist := continuous_kinkDist.measurable

private theorem diamondNorm_add_single_zero (z : Fin 2 → ℝ) (t : ℝ) :
    diamondNorm (z + t • Pi.single 0 1) = |z 0 + t| + |z 1| := by simp [diamondNorm]

private theorem diamondNorm_sub_single_zero (z : Fin 2 → ℝ) (t : ℝ) :
    diamondNorm (z - t • Pi.single 0 1) = |z 0 - t| + |z 1| := by simp [diamondNorm]

private theorem diamondNorm_add_single_one (z : Fin 2 → ℝ) (t : ℝ) :
    diamondNorm (z + t • Pi.single 1 1) = |z 1 + t| + |z 0| := by
  simp [diamondNorm, add_comm]

private theorem diamondNorm_sub_single_one (z : Fin 2 → ℝ) (t : ℝ) :
    diamondNorm (z - t • Pi.single 1 1) = |z 1 - t| + |z 0| := by
  simp [diamondNorm, add_comm]

/-- **For a step no longer than the coordinate `|z j|` the diamond radius is affine in the
step**: both shifted radii are `r ± u` for a step `u` of the same size as `t`, because the sign of
`z j + t` is that of `z j` throughout. -/
theorem exists_shift_diamondNorm {z : Fin 2 → ℝ} {j : Fin 2} {t : ℝ} (ht : |t| ≤ |z j|) :
    ∃ u : ℝ, |u| = |t| ∧ diamondNorm (z + t • Pi.single j 1) = diamondNorm z + u ∧
      diamondNorm (z - t • Pi.single j 1) = diamondNorm z - u := by
  have hlo : -|t| ≤ t := neg_abs_le t
  have hhi : t ≤ |t| := le_abs_self t
  have key : ∀ a : ℝ, |t| ≤ |a| → ∃ u : ℝ, |u| = |t| ∧
      |a + t| = |a| + u ∧ |a - t| = |a| - u := by
    intro a hab
    rcases le_or_gt 0 a with ha | ha
    · rw [abs_of_nonneg ha] at hab
      refine ⟨t, rfl, ?_, ?_⟩
      · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a + t), abs_of_nonneg ha]
      · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a - t), abs_of_nonneg ha]
    · rw [abs_of_neg ha] at hab
      refine ⟨-t, by rw [abs_neg], ?_, ?_⟩
      · rw [abs_of_nonpos (by linarith : a + t ≤ 0), abs_of_neg ha]; ring
      · rw [abs_of_nonpos (by linarith : a - t ≤ 0), abs_of_neg ha]; ring
  rcases fin_two_cases j with rfl | rfl
  · obtain ⟨u, hu, h1, h2⟩ := key (z 0) ht
    refine ⟨u, hu, ?_, ?_⟩
    · rw [diamondNorm_add_single_zero, diamondNorm, h1]; ring
    · rw [diamondNorm_sub_single_zero, diamondNorm, h2]; ring
  · obtain ⟨u, hu, h1, h2⟩ := key (z 1) ht
    refine ⟨u, hu, ?_, ?_⟩
    · rw [diamondNorm_add_single_one, diamondNorm, h1]; ring
    · rw [diamondNorm_sub_single_one, diamondNorm, h2]; ring

/-- **The second difference of the positive-part square** `(x)₊²` is at most `2u²`, with no side
condition: the function is `C^{1,1}` with second derivative `2` on `{x > 0}` and `0` elsewhere. -/
private theorem abs_secondDiff_posPart_sq (x u : ℝ) :
    |max (x + u) 0 ^ 2 + max (x - u) 0 ^ 2 - 2 * max x 0 ^ 2| ≤ 2 * u ^ 2 := by
  have key : ∀ v : ℝ, 0 ≤ v →
      |max (x + v) 0 ^ 2 + max (x - v) 0 ^ 2 - 2 * max x 0 ^ 2| ≤ 2 * v ^ 2 := by
    intro v hv
    rcases le_or_gt v x with h1 | h1
    · rw [max_eq_left (by linarith : (0 : ℝ) ≤ x + v), max_eq_left (by linarith : (0 : ℝ) ≤ x - v),
        max_eq_left (by linarith : (0 : ℝ) ≤ x)]
      rw [show (x + v) ^ 2 + (x - v) ^ 2 - 2 * x ^ 2 = 2 * v ^ 2 by ring, abs_of_nonneg (by
        positivity)]
    · rcases le_or_gt x (-v) with h2 | h2
      · have hzero : max (x + v) 0 ^ 2 + max (x - v) 0 ^ 2 - 2 * max x 0 ^ 2 = 0 := by
          rw [max_eq_right (by linarith : x + v ≤ 0), max_eq_right (by linarith : x - v ≤ 0),
            max_eq_right (by linarith : x ≤ 0)]
          ring
        rw [hzero, abs_zero]
        positivity
      · rw [max_eq_right (by linarith : x - v ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ x + v)]
        rcases le_or_gt 0 x with h3 | h3
        · rw [max_eq_left h3, abs_le]
          constructor <;> nlinarith
        · rw [max_eq_right h3.le, abs_le]
          constructor <;> nlinarith
  rcases le_or_gt 0 u with h | h
  · exact key u h
  · have h' := key (-u) (by linarith)
    rw [show x + -u = x - u by ring, show x - -u = x + u by ring] at h'
    calc |max (x + u) 0 ^ 2 + max (x - u) 0 ^ 2 - 2 * max x 0 ^ 2|
        = |max (x - u) 0 ^ 2 + max (x + u) 0 ^ 2 - 2 * max x 0 ^ 2| := by rw [add_comm]
      _ ≤ 2 * (-u) ^ 2 := h'
      _ = 2 * u ^ 2 := by ring

/-- **The radial second difference of the bump profile** is at most `2u²`. -/
theorem abs_secondDiff_looseHump_le (r u : ℝ) :
    |looseHump (r + u) + looseHump (r - u) - 2 * looseHump r| ≤ 2 * u ^ 2 := by
  have h := abs_secondDiff_posPart_sq (1 - r) u
  rw [looseHump, looseHump, looseHump, show 1 - (r + u) = 1 - r - u by ring,
    show 1 - (r - u) = 1 - r + u by ring, add_comm]
  exact h

/-- **The radial second difference of the cusp profile.** For a step that stays on one side of the
circle `{r = R}` and inside the disc of radius `r`, the second difference of `cuspTail` is exactly
`−2R u²/((R − 1) r (r² − u²))` beyond `R` and `0` before it, so it is at most
`2u²/(R²(R − 1))` in modulus, because `r (r² − u²) ≥ R³`. -/
theorem abs_secondDiff_cuspTail_le {r u : ℝ} (hu : |u| ≤ r)
    (huR : |u| ≤ |r - looseRadius|) :
    |cuspTail (r + u) + cuspTail (r - u) - 2 * cuspTail r|
      ≤ 2 / (looseRadius ^ 2 * (looseRadius - 1)) * u ^ 2 := by
  have hR := looseRadius_sub_one_pos
  have hR0 := looseRadius_pos
  have hlo : -|u| ≤ u := neg_abs_le u
  have hhi : u ≤ |u| := le_abs_self u
  have hRR := looseRadius_sq_mul_sub_one_pos
  have hnn : (0 : ℝ) ≤ 2 / (looseRadius ^ 2 * (looseRadius - 1)) * u ^ 2 :=
    mul_nonneg (div_nonneg (by norm_num) hRR.le) (sq_nonneg u)
  rcases lt_trichotomy r looseRadius with h | h | h
  · rw [abs_of_neg (by linarith : r - looseRadius < 0)] at huR
    rw [cuspTail_eq_zero (by linarith : r + u ≤ looseRadius),
      cuspTail_eq_zero (by linarith : r - u ≤ looseRadius), cuspTail_eq_zero h.le,
      show (0 : ℝ) + 0 - 2 * 0 = 0 by ring, abs_zero]
    exact hnn
  · rw [h, sub_self, abs_zero] at huR
    have hu0 : u = 0 := abs_eq_zero.1 (le_antisymm huR (abs_nonneg u))
    subst hu0
    rw [add_zero, sub_zero, show cuspTail r + cuspTail r - 2 * cuspTail r = 0 by ring, abs_zero]
    simp
  · rw [abs_of_pos (by linarith : 0 < r - looseRadius)] at huR
    have hr0 : 0 < r := hR0.trans h
    have hA : looseRadius ≤ r + u := by linarith
    have hB : looseRadius ≤ r - u := by linarith
    have hA0 : 0 < r + u := hR0.trans_le hA
    have hB0 : 0 < r - u := hR0.trans_le hB
    have hu2 : u ^ 2 ≤ (r - looseRadius) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have hcube : looseRadius ^ 3 ≤ r * ((r + u) * (r - u)) := by
      have h2 : looseRadius * (2 * r - looseRadius) ≤ (r + u) * (r - u) := by nlinarith
      calc looseRadius ^ 3 = looseRadius * (looseRadius * looseRadius) := by ring
        _ ≤ r * (looseRadius * (2 * r - looseRadius)) := by
            nlinarith [mul_nonneg (mul_nonneg hR0.le (sub_nonneg.2 h.le))
              (by linarith : (0 : ℝ) ≤ 2 * r + looseRadius)]
        _ ≤ r * ((r + u) * (r - u)) := mul_le_mul_of_nonneg_left h2 hr0.le
    have hd : 0 < (looseRadius - 1) * r * ((r + u) * (r - u)) :=
      mul_pos (mul_pos hR hr0) (mul_pos hA0 hB0)
    have key : cuspTail (r + u) + cuspTail (r - u) - 2 * cuspTail r
        = -(2 * looseRadius * u ^ 2) / ((looseRadius - 1) * r * ((r + u) * (r - u))) := by
      rw [cuspTail_of_le hA, cuspTail_of_le hB, cuspTail_of_le h.le]
      field_simp
      ring
    rw [key, abs_div, abs_neg,
      abs_of_nonneg (mul_nonneg (mul_nonneg (by norm_num) hR0.le) (sq_nonneg u)),
      abs_of_nonneg hd.le, div_mul_eq_mul_div, div_le_div_iff₀ hd hRR]
    nlinarith [mul_le_mul_of_nonneg_left hcube
      (mul_nonneg (mul_nonneg (by norm_num) hR.le) (sq_nonneg u) :
        (0 : ℝ) ≤ 2 * (looseRadius - 1) * u ^ 2)]

/-- **The second difference of the bounded part is quadratically small at the scale `kinkDist`.**
For a step `|t| ≤ kinkDist z` the diamond radius is affine in the step, so the second difference
collapses to the radial one, which is controlled by `abs_secondDiff_cuspTail_le` and
`abs_secondDiff_looseHump_le`. -/
theorem abs_secondDiff_boundedPart_le (z : Fin 2 → ℝ) (j : Fin 2) {t : ℝ}
    (ht : |t| ≤ kinkDist z) : |secondDiff boundedPart j z t| ≤ boundedM₂ * t ^ 2 := by
  have htj : |t| ≤ |z j| := ht.trans (kinkDist_le_abs z j)
  obtain ⟨u, hu, h1, h2⟩ := exists_shift_diamondNorm htj
  have hur : |u| ≤ diamondNorm z := by
    rw [hu]
    exact htj.trans (abs_le_diamondNorm z j)
  have huR : |u| ≤ |diamondNorm z - looseRadius| := by
    rw [hu]
    exact ht.trans (kinkDist_le_abs_sub z)
  have hu2 : u ^ 2 = t ^ 2 := by rw [← sq_abs u, hu, sq_abs]
  have hcusp := abs_secondDiff_cuspTail_le hur huR
  have hhump : |looseBump * (looseHump (diamondNorm z + u) + looseHump (diamondNorm z - u)
      - 2 * looseHump (diamondNorm z))| ≤ looseBump * (2 * u ^ 2) := by
    rw [abs_mul, abs_of_nonneg looseBump_pos.le]
    exact mul_le_mul_of_nonneg_left (abs_secondDiff_looseHump_le (diamondNorm z) u)
      looseBump_pos.le
  rw [secondDiff]
  simp only [boundedPart, h1, h2, boundedProfile]
  calc |cuspTail (diamondNorm z + u) - looseBump * looseHump (diamondNorm z + u)
        + (cuspTail (diamondNorm z - u) - looseBump * looseHump (diamondNorm z - u))
        - 2 * (cuspTail (diamondNorm z) - looseBump * looseHump (diamondNorm z))|
      = |cuspTail (diamondNorm z + u) + cuspTail (diamondNorm z - u)
            - 2 * cuspTail (diamondNorm z)
          - looseBump * (looseHump (diamondNorm z + u) + looseHump (diamondNorm z - u)
            - 2 * looseHump (diamondNorm z))| := by
        congr 1
        ring
    _ ≤ |cuspTail (diamondNorm z + u) + cuspTail (diamondNorm z - u)
            - 2 * cuspTail (diamondNorm z)|
          + |looseBump * (looseHump (diamondNorm z + u) + looseHump (diamondNorm z - u)
            - 2 * looseHump (diamondNorm z))| := abs_sub_le_abs_add_abs _ _
    _ ≤ 2 / (looseRadius ^ 2 * (looseRadius - 1)) * u ^ 2 + looseBump * (2 * u ^ 2) :=
        add_le_add hcusp hhump
    _ = boundedM₂ * u ^ 2 := by rw [boundedM₂]; ring
    _ = boundedM₂ * t ^ 2 := by rw [hu2]

/-! ### Local integrability of the logarithmic bound -/

/-- The logarithmic bound is nonnegative at every nonnegative distance. -/
private theorem log_one_div_min_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.log (1 / min 1 x) := by
  rcases eq_or_lt_of_le hx with rfl | hx'
  · simp
  · rcases le_total x 1 with h | h
    · rw [min_eq_right h]
      exact Real.log_nonneg ((one_le_div hx').2 h)
    · rw [min_eq_left h]
      simp

/-- The logarithmic bound at a nonnegative distance is at most `|log x|`. -/
private theorem log_one_div_min_le_abs {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 / min 1 x) ≤ |Real.log x| := by
  rcases eq_or_lt_of_le hx with rfl | hx'
  · simp
  · rcases le_total x 1 with h | h
    · rw [min_eq_right h, one_div, Real.log_inv]
      exact neg_le_abs _
    · rw [min_eq_left h]
      simp

/-- The logarithmic bound at the smaller of two nonnegative distances splits. -/
private theorem log_one_div_min_min_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.log (1 / min 1 (min x y)) ≤ Real.log (1 / min 1 x) + Real.log (1 / min 1 y) := by
  rcases le_total x y with h | h
  · rw [min_eq_left h]
    linarith [log_one_div_min_nonneg hy]
  · rw [min_eq_right h]
    linarith [log_one_div_min_nonneg hx]

theorem log_one_div_kinkDist_nonneg (z : Fin 2 → ℝ) : 0 ≤ Real.log (1 / kinkDist z) := by
  have h : kinkDist z = min 1 (min |z 0| (min |z 1| |diamondNorm z - looseRadius|)) := rfl
  rw [h]
  exact log_one_div_min_nonneg (le_min (abs_nonneg _) (le_min (abs_nonneg _) (abs_nonneg _)))

/-- **The logarithmic bound splits into three coordinate logarithms.** -/
theorem log_one_div_kinkDist_le (z : Fin 2 → ℝ) :
    Real.log (1 / kinkDist z) ≤ |Real.log (z 0)| + |Real.log (z 1)|
      + |Real.log (diamondNorm z - looseRadius)| := by
  have h0 : (0 : ℝ) ≤ |z 0| := abs_nonneg _
  have h1 : (0 : ℝ) ≤ |z 1| := abs_nonneg _
  have h2 : (0 : ℝ) ≤ |diamondNorm z - looseRadius| := abs_nonneg _
  have hk : kinkDist z = min 1 (min |z 0| (min |z 1| |diamondNorm z - looseRadius|)) := rfl
  have e0 := (log_one_div_min_le_abs h0).trans_eq (by rw [Real.log_abs])
  have e1 := (log_one_div_min_le_abs h1).trans_eq (by rw [Real.log_abs])
  have e2 := (log_one_div_min_le_abs h2).trans_eq (by rw [Real.log_abs])
  have hsplit1 := log_one_div_min_min_le h0 (le_min h1 h2)
  have hsplit2 := log_one_div_min_min_le h1 h2
  rw [hk]
  linarith

/-! ### The finiteness of the logarithmic integrals -/

private theorem lintegral_ofReal_abs {β : Type*} [MeasurableSpace β] {μ : Measure β}
    (f : β → ℝ) : (∫⁻ y, ENNReal.ofReal |f y| ∂μ) = ∫⁻ y, ‖f y‖ₑ ∂μ :=
  lintegral_congr fun _ => (Real.enorm_eq_ofReal_abs _).symm

private theorem integrableOn_of_lintegral_ne_top {f : (Fin 2 → ℝ) → ℝ} {K : Set (Fin 2 → ℝ)}
    (hf : Measurable f) (h : (∫⁻ z in K, ENNReal.ofReal |f z|) ≠ ⊤) : IntegrableOn f K :=
  ⟨hf.aestronglyMeasurable, by
    rw [hasFiniteIntegral_iff_enorm, ← lintegral_ofReal_abs]
    exact lt_top_iff_ne_top.2 h⟩

/-- The logarithm shifted by a constant has finite integral on every compact interval. -/
private theorem lintegral_Icc_abs_log_sub_ne_top (c a b : ℝ) :
    (∫⁻ x in Icc a b, ENNReal.ofReal |Real.log (x - c)|) ≠ ⊤ := by
  have h1 : IntervalIntegrable (fun x : ℝ => Real.log (x - c)) volume a b := by
    simpa using
      (intervalIntegral.intervalIntegrable_log' (a := a - c) (b := b - c)).comp_sub_right c
  have h2 : IntegrableOn (fun x : ℝ => Real.log (x - c)) (Icc a b) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact h1.1
  rw [lintegral_ofReal_abs]
  exact (hasFiniteIntegral_iff_enorm.1 h2.2).ne

/-- The coordinate box of radius `N`. -/
private def coordBox (N : ℝ) : Set (Fin 2 → ℝ) := {z | |z 0| ≤ N} ∩ {z | |z 1| ≤ N}

private theorem measurableSet_coordBox (N : ℝ) : MeasurableSet (coordBox N) :=
  (measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply (0 : Fin 2)))
    measurable_const).inter
    (measurableSet_le (continuous_abs.measurable.comp (measurable_pi_apply (1 : Fin 2)))
      measurable_const)

/-- Tonelli on the plane in the coordinates of `Fin 2 → ℝ`. -/
private theorem lintegral_finTwoArrow_mul {F G : ℝ → ℝ≥0∞} (hF : Measurable F)
    (hG : Measurable G) : (∫⁻ z : Fin 2 → ℝ, F (z 0) * G (z 1)) = (∫⁻ x, F x) * ∫⁻ y, G y := by
  have h : (∫⁻ p : ℝ × ℝ, F p.1 * G p.2) = ∫⁻ z : Fin 2 → ℝ, F (z 0) * G (z 1) := by
    rw [← (volume_preserving_finTwoArrow ℝ).map_eq, lintegral_map_equiv]
    rfl
  rw [← h]
  exact lintegral_prod_mul hF.aemeasurable hG.aemeasurable

/-- A function of one coordinate has finite integral over the box as soon as it has finite
integral over the corresponding interval. -/
private theorem lintegral_coordBox_ne_top {N : ℝ} {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ x in Icc (-N) N, f x) ≠ ⊤) (j : Fin 2) :
    (∫⁻ z in coordBox N, f (z j)) ≠ ⊤ := by
  have hFm : Measurable ((Icc (-N) N).indicator f) := hf.indicator measurableSet_Icc
  have hGm : Measurable ((Icc (-N) N).indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_one.indicator measurableSet_Icc
  have hF : (∫⁻ x, (Icc (-N) N).indicator f x) ≠ ⊤ := by
    rwa [lintegral_indicator measurableSet_Icc]
  have hG : (∫⁻ y, (Icc (-N) N).indicator (1 : ℝ → ℝ≥0∞) y) ≠ ⊤ := by
    rw [lintegral_indicator measurableSet_Icc]
    simp only [Pi.one_apply, lintegral_const, one_mul, Measure.restrict_apply_univ]
    exact measure_Icc_lt_top.ne
  have hmem : ∀ z ∈ coordBox N, z 0 ∈ Icc (-N) N ∧ z 1 ∈ Icc (-N) N := by
    intro z hz
    exact ⟨mem_Icc.2 (abs_le.1 hz.1), mem_Icc.2 (abs_le.1 hz.2)⟩
  rcases fin_two_cases j with rfl | rfl
  · refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hF hG) ?_
    calc (∫⁻ z in coordBox N, f (z 0))
        = ∫⁻ z, (coordBox N).indicator (fun z => f (z 0)) z :=
          (lintegral_indicator (measurableSet_coordBox N) _).symm
      _ ≤ ∫⁻ z : Fin 2 → ℝ, (Icc (-N) N).indicator f (z 0)
            * (Icc (-N) N).indicator (1 : ℝ → ℝ≥0∞) (z 1) := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ coordBox N
          · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hmem z hz).1,
              Set.indicator_of_mem (hmem z hz).2, Pi.one_apply, mul_one]
          · rw [Set.indicator_of_notMem hz]
            exact zero_le
      _ = _ := lintegral_finTwoArrow_mul hFm hGm
  · refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hG hF) ?_
    calc (∫⁻ z in coordBox N, f (z 1))
        = ∫⁻ z, (coordBox N).indicator (fun z => f (z 1)) z :=
          (lintegral_indicator (measurableSet_coordBox N) _).symm
      _ ≤ ∫⁻ z : Fin 2 → ℝ, (Icc (-N) N).indicator (1 : ℝ → ℝ≥0∞) (z 0)
            * (Icc (-N) N).indicator f (z 1) := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ coordBox N
          · rw [Set.indicator_of_mem hz, Set.indicator_of_mem (hmem z hz).1,
              Set.indicator_of_mem (hmem z hz).2, Pi.one_apply, one_mul]
          · rw [Set.indicator_of_notMem hz]
            exact zero_le
      _ = _ := lintegral_finTwoArrow_mul hGm hFm

/-- The logarithm of the distance to the circle `{r = R}` has finite integral over every disc,
by the radial formula. -/
private theorem lintegral_diamondNorm_log_ne_top (N : ℝ) :
    (∫⁻ z : Fin 2 → ℝ, (Iic N).indicator
        (fun t => ENNReal.ofReal |Real.log (t - looseRadius)|) (diamondNorm z)) ≠ ⊤ := by
  have hm : Measurable ((Iic N).indicator
      fun t : ℝ => ENNReal.ofReal |Real.log (t - looseRadius)|) :=
    Measurable.indicator (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
      (Real.measurable_log.comp (measurable_id.sub_const looseRadius)))) measurableSet_Iic
  have hbd : ∀ t ∈ Ioi (0 : ℝ), 4 * ENNReal.ofReal t * (Iic N).indicator
      (fun t : ℝ => ENNReal.ofReal |Real.log (t - looseRadius)|) t
      ≤ ENNReal.ofReal (4 * N) * (Icc 0 N).indicator
          (fun t : ℝ => ENNReal.ofReal |Real.log (t - looseRadius)|) t := by
    intro t ht
    by_cases h : t ≤ N
    · rw [Set.indicator_of_mem (mem_Iic.2 h), Set.indicator_of_mem (mem_Icc.2 ⟨ht.le, h⟩)]
      refine mul_le_mul_left ?_ _
      rw [show (4 : ℝ≥0∞) * ENNReal.ofReal t = ENNReal.ofReal (4 * t) by
        rw [ENNReal.ofReal_mul (by norm_num)]; norm_num]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · rw [Set.indicator_of_notMem (by simpa using h), mul_zero]
      exact zero_le
  rw [lintegral_comp_diamondNorm hm]
  refine ne_top_of_le_ne_top ?_
    (lintegral_mono_ae (ae_restrict_of_forall_mem measurableSet_Ioi hbd))
  refine ne_top_of_le_ne_top ?_ (setLIntegral_le_lintegral _ _)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_Icc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (lintegral_Icc_abs_log_sub_ne_top _ 0 N)

/-- **The logarithmic bound is locally integrable.** It is dominated by the three coordinate
logarithms of `log_one_div_kinkDist_le`, the first two integrable by Tonelli and the last by the
radial formula. -/
theorem integrableOn_log_kinkDist {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) :
    IntegrableOn (fun z => Real.log (1 / kinkDist z)) K := by
  obtain ⟨N₀, hN₀⟩ := hK.exists_bound_of_continuousOn continuous_diamondNorm.continuousOn
  obtain ⟨N, hKN⟩ : ∃ N : ℝ, ∀ z ∈ K, diamondNorm z ≤ N := by
    refine ⟨N₀, fun z hz => ?_⟩
    have h := hN₀ z hz
    rwa [Real.norm_eq_abs, abs_of_nonneg (diamondNorm_nonneg z)] at h
  have hKbox : K ⊆ coordBox N := fun z hz =>
    ⟨(abs_le_diamondNorm z 0).trans (hKN z hz), (abs_le_diamondNorm z 1).trans (hKN z hz)⟩
  have hl0 : Measurable fun z : Fin 2 → ℝ => |Real.log (z 0)| :=
    continuous_abs.measurable.comp
      (Real.measurable_log.comp (measurable_pi_apply (0 : Fin 2)))
  have hl1 : Measurable fun z : Fin 2 → ℝ => |Real.log (z 1)| :=
    continuous_abs.measurable.comp
      (Real.measurable_log.comp (measurable_pi_apply (1 : Fin 2)))
  have hl2 : Measurable fun z : Fin 2 → ℝ => |Real.log (diamondNorm z - looseRadius)| :=
    continuous_abs.measurable.comp
      (Real.measurable_log.comp (measurable_diamondNorm.sub measurable_const))
  have hm0 : Measurable fun z : Fin 2 → ℝ => ENNReal.ofReal |Real.log (z 0)| :=
    ENNReal.measurable_ofReal.comp hl0
  have hm1 : Measurable fun z : Fin 2 → ℝ => ENNReal.ofReal |Real.log (z 1)| :=
    ENNReal.measurable_ofReal.comp hl1
  have hD : IntegrableOn (fun z => |Real.log (z 0)| + |Real.log (z 1)|
      + |Real.log (diamondNorm z - looseRadius)|) K := by
    refine integrableOn_of_lintegral_ne_top ((hl0.add hl1).add hl2) ?_
    have hle : ∀ z : Fin 2 → ℝ, ENNReal.ofReal |(|Real.log (z 0)| + |Real.log (z 1)|
        + |Real.log (diamondNorm z - looseRadius)|)|
        = ENNReal.ofReal |Real.log (z 0)| + ENNReal.ofReal |Real.log (z 1)|
          + ENNReal.ofReal |Real.log (diamondNorm z - looseRadius)| := by
      intro z
      rw [abs_of_nonneg (by positivity), ENNReal.ofReal_add (by positivity) (abs_nonneg _),
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
    have hm01 : Measurable fun z : Fin 2 → ℝ => ENNReal.ofReal |Real.log (z 0)|
        + ENNReal.ofReal |Real.log (z 1)| := hm0.add hm1
    rw [lintegral_congr hle, lintegral_add_left hm01, lintegral_add_left hm0]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨?_, ?_⟩, ?_⟩
    · exact ne_top_of_le_ne_top
        (lintegral_coordBox_ne_top
          (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp Real.measurable_log))
          (by simpa using lintegral_Icc_abs_log_sub_ne_top 0 (-N) N) 0)
        (lintegral_mono' (Measure.restrict_mono hKbox le_rfl) le_rfl)
    · exact ne_top_of_le_ne_top
        (lintegral_coordBox_ne_top
          (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp Real.measurable_log))
          (by simpa using lintegral_Icc_abs_log_sub_ne_top 0 (-N) N) 1)
        (lintegral_mono' (Measure.restrict_mono hKbox le_rfl) le_rfl)
    · have heq : (∫⁻ z in K, ENNReal.ofReal |Real.log (diamondNorm z - looseRadius)|)
          = ∫⁻ z in K, (Iic N).indicator
              (fun t => ENNReal.ofReal |Real.log (t - looseRadius)|) (diamondNorm z) :=
        setLIntegral_congr_fun hK.measurableSet fun z hz =>
          (Set.indicator_of_mem (mem_Iic.2 (hKN z hz))
            (fun t : ℝ => ENNReal.ofReal |Real.log (t - looseRadius)|)).symm
      rw [heq]
      exact ne_top_of_le_ne_top (lintegral_diamondNorm_log_ne_top N)
        (setLIntegral_le_lintegral _ _)
  refine hD.mono' ?_ (ae_of_all _ fun z => ?_)
  · exact (Real.measurable_log.comp
      (measurable_const.div measurable_kinkDist)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (log_one_div_kinkDist_nonneg z)]
    exact log_one_div_kinkDist_le z

/-! ### The kink set is null -/

private theorem volume_diamondNorm_eq_looseRadius :
    volume {z : Fin 2 → ℝ | diamondNorm z = looseRadius} = 0 := by
  have hs : MeasurableSet {z : Fin 2 → ℝ | diamondNorm z = looseRadius} :=
    measurable_diamondNorm (measurableSet_singleton looseRadius)
  have hsing : ∀ᵐ t : ℝ, t ≠ looseRadius := by
    rw [ae_iff]
    convert measure_singleton (μ := (volume : Measure ℝ)) looseRadius using 2
    ext t
    simp
  calc volume {z : Fin 2 → ℝ | diamondNorm z = looseRadius}
      = ∫⁻ z : Fin 2 → ℝ, {z : Fin 2 → ℝ | diamondNorm z = looseRadius}.indicator 1 z :=
        (lintegral_indicator_one hs).symm
    _ = ∫⁻ z : Fin 2 → ℝ, ({looseRadius} : Set ℝ).indicator 1 (diamondNorm z) := by
        refine lintegral_congr fun z => ?_
        by_cases hz : diamondNorm z = looseRadius <;> simp [hz]
    _ = ∫⁻ t in Ioi 0, 4 * ENNReal.ofReal t * ({looseRadius} : Set ℝ).indicator 1 t :=
        lintegral_comp_diamondNorm (measurable_one.indicator (measurableSet_singleton _))
    _ = 0 := by
        refine (lintegral_eq_zero_iff' ?_).2 ?_
        · exact ((measurable_const.mul ENNReal.measurable_ofReal).mul
            (measurable_one.indicator (measurableSet_singleton _))).aemeasurable
        · refine ae_restrict_of_ae ?_
          filter_upwards [hsing] with t ht
          simp [ht]

/-- **The kink set is null**: it is contained in the union of the two coordinate axes and the
circle `{r = R}`. -/
theorem kinkDist_ne_zero_ae : ∀ᵐ z : Fin 2 → ℝ, kinkDist z ≠ 0 := by
  have h0 : ∀ᵐ z : Fin 2 → ℝ, z 0 ≠ 0 := by
    rw [MeasureTheory.volume_pi]
    exact Measure.ae_eval_ne _ 0 0
  have h1 : ∀ᵐ z : Fin 2 → ℝ, z 1 ≠ 0 := by
    rw [MeasureTheory.volume_pi]
    exact Measure.ae_eval_ne _ 1 0
  have h2 : ∀ᵐ z : Fin 2 → ℝ, diamondNorm z ≠ looseRadius := by
    rw [ae_iff]
    exact measure_mono_null (fun z hz => not_not.1 hz) volume_diamondNorm_eq_looseRadius
  filter_upwards [h0, h1, h2] with z hz0 hz1 hz2
  have hk : kinkDist z = min 1 (min |z 0| (min |z 1| |diamondNorm z - looseRadius|)) := rfl
  rw [hk]
  refine ne_of_gt (lt_min one_pos (lt_min (abs_pos.2 hz0) (lt_min (abs_pos.2 hz1) ?_)))
  exact abs_pos.2 (sub_ne_zero_of_ne hz2)

/-! ### The Fubini hypothesis for the bounded part -/

private theorem measurable_secondDiff_swap {g : (Fin 2 → ℝ) → ℝ} (hg : Measurable g)
    (j : Fin 2) : Measurable fun p : ℝ × (Fin 2 → ℝ) => secondDiff g j p.2 p.1 := by
  unfold secondDiff
  exact ((hg.comp (measurable_snd.add (measurable_fst.smul_const _))).add
    (hg.comp (measurable_snd.sub (measurable_fst.smul_const _)))).sub
    (measurable_const.mul (hg.comp measurable_snd))

/-- **A sufficient condition for the Fubini hypothesis of `integral_mul_jumpGen_comm` with an
extended-real bound.** This is `integrable_uncurry_of_bound` with `B` allowed to take the value
`⊤` on a null set, which is what a bound built from a distance to a kink set does. -/
theorem integrable_uncurry_of_enorm_bound {α : ℝ} {g φ : (Fin 2 → ℝ) → ℝ} (hgm : Measurable g)
    (hφ : IsTestFunction φ) {j : Fin 2} {B : (Fin 2 → ℝ) → ℝ≥0∞}
    (hB : ∀ z, (∫⁻ t : ℝ, ENNReal.ofReal (|secondDiff g j z t| * |t| ^ (-(1 + α)))) ≤ B z)
    (hBint : (∫⁻ z in tsupport φ, B z) ≠ ⊤) :
    Integrable (Function.uncurry fun (t : ℝ) (z : Fin 2 → ℝ) =>
        secondDiff g j z t * φ z * |t| ^ (-(1 + α)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) := by
  obtain ⟨M₀, h₀⟩ := hφ.continuous.bounded_above_of_compact_support hφ.2
  have hKm : MeasurableSet (tsupport φ) := (isClosed_tsupport φ).measurableSet
  have hm : Measurable fun p : ℝ × (Fin 2 → ℝ) =>
      secondDiff g j p.2 p.1 * φ p.2 * |p.1| ^ (-(1 + α)) :=
    ((measurable_secondDiff_swap hgm j).mul
      (hφ.continuous.measurable.comp measurable_snd)).mul
      ((continuous_abs.measurable.pow_const _).comp measurable_fst)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hinner : ∀ z : Fin 2 → ℝ,
      (∫⁻ t : ℝ, ‖secondDiff g j z t * φ z * |t| ^ (-(1 + α))‖ₑ)
        ≤ B z * ENNReal.ofReal |φ z| := by
    intro z
    have h1 : ∀ t : ℝ, ‖secondDiff g j z t * φ z * |t| ^ (-(1 + α))‖ₑ
        = ENNReal.ofReal (|secondDiff g j z t| * |t| ^ (-(1 + α))) * ENNReal.ofReal |φ z| := by
      intro t
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _)]
      ring
    rw [lintegral_congr h1, lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul_left (hB z) _
  have hpt : ∀ z : Fin 2 → ℝ, B z * ENNReal.ofReal |φ z|
      ≤ (tsupport φ).indicator (fun z => B z * ENNReal.ofReal M₀) z := by
    intro z
    by_cases hz : z ∈ tsupport φ
    · rw [Set.indicator_of_mem hz]
      exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (h₀ z)) _
    · rw [Set.indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz]
      simp
  calc (∫⁻ p, ‖secondDiff g j p.2 p.1 * φ p.2 * |p.1| ^ (-(1 + α))‖ₑ
        ∂((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))))
      = ∫⁻ z : Fin 2 → ℝ, ∫⁻ t : ℝ, ‖secondDiff g j z t * φ z * |t| ^ (-(1 + α))‖ₑ :=
        lintegral_prod_symm _ hm.enorm.aemeasurable
    _ ≤ ∫⁻ z : Fin 2 → ℝ, B z * ENNReal.ofReal |φ z| := lintegral_mono hinner
    _ ≤ ∫⁻ z : Fin 2 → ℝ,
          (tsupport φ).indicator (fun z => B z * ENNReal.ofReal M₀) z := lintegral_mono hpt
    _ = ∫⁻ z in tsupport φ, B z * ENNReal.ofReal M₀ := lintegral_indicator hKm _
    _ = (∫⁻ z in tsupport φ, B z) * ENNReal.ofReal M₀ :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hBint) ENNReal.ofReal_lt_top

/-- The pointwise bound `2 M₂ δ + 24 log(1/δ) + 8 C` on the inner step integral, at the scale
`δ = kinkDist z`. -/
def logBound (z : Fin 2 → ℝ) : ℝ :=
  2 * boundedM₂ * kinkDist z + 24 * Real.log (1 / kinkDist z) + 8 * boundedC

/-- The extended bound, `⊤` on the null kink set, where the inner integral diverges. -/
def logBoundTop (z : Fin 2 → ℝ) : ℝ≥0∞ :=
  if kinkDist z = 0 then ⊤ else ENNReal.ofReal (logBound z)

theorem integrableOn_logBound {K : Set (Fin 2 → ℝ)} (hK : IsCompact K) :
    IntegrableOn logBound K := by
  have h1 : IntegrableOn kinkDist K :=
    continuous_kinkDist.continuousOn.integrableOn_compact hK
  have h2 : IntegrableOn (fun z => Real.log (1 / kinkDist z)) K := integrableOn_log_kinkDist hK
  have h3 : IntegrableOn (fun _ : Fin 2 → ℝ => 8 * boundedC) K :=
    integrableOn_const hK.measure_lt_top.ne
  exact ((h1.const_mul (2 * boundedM₂)).add (h2.const_mul 24)).add h3

private theorem lintegral_logBoundTop_ne_top {φ : (Fin 2 → ℝ) → ℝ} (hφ : IsTestFunction φ) :
    (∫⁻ z in tsupport φ, logBoundTop z) ≠ ⊤ := by
  have heq : (∫⁻ z in tsupport φ, logBoundTop z)
      = ∫⁻ z in tsupport φ, ENNReal.ofReal (logBound z) := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [kinkDist_ne_zero_ae] with z hz
    rw [logBoundTop, if_neg hz]
  rw [heq]
  refine ne_top_of_le_ne_top
    (hasFiniteIntegral_iff_enorm.1 (integrableOn_logBound hφ.2).2).ne (lintegral_mono fun z => ?_)
  exact Real.ofReal_le_enorm (logBound z)

theorem lintegral_secondDiff_boundedPart_le (j : Fin 2) (z : Fin 2 → ℝ) :
    (∫⁻ t : ℝ, ENNReal.ofReal (|secondDiff boundedPart j z t| * |t| ^ (-(1 + (1 : ℝ)))))
      ≤ logBoundTop z := by
  by_cases hz : kinkDist z = 0
  · rw [logBoundTop, if_pos hz]
    exact le_top
  · have hpos : 0 < kinkDist z := (kinkDist_nonneg z).lt_of_ne (Ne.symm hz)
    rw [logBoundTop, if_neg hz]
    refine (lintegral_secondDiff_mul_rpow_le_of_lipschitz_of_c2 lipschitzWith_boundedPart
      abs_boundedPart_le hpos (kinkDist_le_one z) j z
      (fun t ht => abs_secondDiff_boundedPart_le z j ht)).trans_eq ?_
    congr 1
    rw [logBound, show ((6 : ℝ≥0) : ℝ) = 6 by norm_num]
    ring

/-- **The Fubini hypothesis of `integral_mul_jumpGen_comm` for the bounded part of the loose
kernel.** -/
theorem integrable_uncurry_secondDiff_boundedPart {φ : (Fin 2 → ℝ) → ℝ} (hφ : IsTestFunction φ)
    (j : Fin 2) :
    Integrable (Function.uncurry fun (t : ℝ) (z : Fin 2 → ℝ) =>
        secondDiff boundedPart j z t * φ z * |t| ^ (-(1 + (1 : ℝ))))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) :=
  integrable_uncurry_of_enorm_bound measurable_boundedPart hφ
    (lintegral_secondDiff_boundedPart_le j) (lintegral_logBoundTop_ne_top hφ)

/-- **Pointwise lower bounds on the generator of the bounded part become weak ones.** -/
theorem nonneg_integral_boundedPart_mul_jumpGen {φ : (Fin 2 → ℝ) → ℝ} (hφ : IsTestFunction φ)
    (hφ0 : ∀ z, 0 ≤ φ z) (hpt : ∀ᵐ z : Fin 2 → ℝ, 0 ≤ jumpGen 1 boundedPart z) :
    0 ≤ ∫ z, boundedPart z * jumpGen 1 φ z :=
  nonneg_integral_mul_jumpGen one_pos (by norm_num) measurable_boundedPart abs_boundedPart_le hφ
    (fun j => integrable_uncurry_secondDiff_boundedPart hφ j) hφ0 hpt

end CenteredMaximal.Cauchy

end

end
