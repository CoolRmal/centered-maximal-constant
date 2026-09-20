/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.DiamondReduction
public import CenteredMaximal.Fractional.DiamondValue

/-!
# The fractional generator of the diamond power

`CenteredMaximal.Fractional.DiamondReduction` collapses the jump generator of the diamond power
`z ↦ r(z)^{-α}` into two copies of a one-dimensional profile `P = diamondProfile`, and
`CenteredMaximal.Fractional.DiamondConstancy` together with
`CenteredMaximal.Fractional.DiamondValue` evaluate the first-order profile `Theta`. This file
supplies the missing link between the two — an integration by parts turning the *second*-difference
profile into the *first*-order one — and then reads off the closed form of the generator.

## Main results

* `diamondProfile_eq_byParts`: the integration by parts. For `0 < a < 1`,
  `P α a (1 - a) = -2 (∫_0^a diamondNear + ∫_a^∞ diamondFar + ∫_a^∞ diamondShift (1 - 2a))`.
* `integral_Ioi_diamondShift_pair`: the exact primitive
  `∫_c^∞ t^{-α}(t+δ)^{-α-1} + ∫_{c+δ}^∞ t^{-α}(t-δ)^{-α-1} = (1/α) (c (c + δ))^{-α}`.
* `Theta_eq_Theta_half'`: `Theta α` is constant on all of `(0, 1)`, not merely on `(0, 1/2]`.
* `diamondProfile_add_eq`: `P α p (1 - p) + P α (1 - p) p = -2 Theta α p`.
* `jumpGen_diamondPow_eq_const`: the generator of the diamond power is a constant multiple of
  `r^{-2α}`, with the constant `-4π Γ(2α) cos(πα/2) / (α Γ(α)^2 sin(πα/2))`.

## The integration by parts

Only the normalised case `a + b = 1` is needed, since `diamondProfile_eq_rpow_mul` reduces every
other case to it, and the normalisation is what makes the near branch of the by-parts identity
land exactly on `diamondNear`. Writing `N` for the second difference, the profile is
`2 ∫_0^∞ N t · t^{-1-α}` by evenness (`integral_of_even`), and `t ↦ -t^{-α}/α` is a primitive of
the weight. Mathlib has no by-parts lemma for a half line, and none is needed: the corner of `N`
at `t = a` splits the half line into `[0, a]` and `[a, ∞)`, and on each piece the product
`N t · (-t^{-α}/α)` — `diamondAntiNear` and `diamondAntiFar` — is differentiable with the right
derivative, so the fundamental theorem of calculus applies directly.

Both boundary terms vanish. At `t = 0` the primitive `diamondAntiNear` is *continuous*, with value
`0`: the second difference is `O(t²)` by `abs_diamondSecond_le`, which upgrades the first-order
bound `exists_nearBracket_bound` of `DiamondConstancy` by one mean value estimate, and `α < 2`
does the rest. So the near branch needs no limiting argument at all, only
`integral_eq_sub_of_hasDeriv_right_of_le`, whose continuity hypothesis is on the *closed*
interval. At `t = ∞` the second difference is bounded while `t^{-α} → 0`, and that limit is taken
in the usual way through `intervalIntegral_tendsto_integral_Ioi`. At the interior corner `t = a`
the two primitives agree, because `a + (1 - 2a) = 1 - a`, so nothing is left behind.

## The rearrangement

With `δ = 1 - 2p` the by-parts identity at `a = p` and at `a = 1 - p` produces, besides the
`diamondNear` and `diamondFar` integrals, the two shifted tails `∫_p^∞ t^{-α}(t+δ)^{-α-1}` and
`∫_{1-p}^∞ t^{-α}(t-δ)^{-α-1}`. Translating the second by `δ` — legitimate because
`1 - p - δ = p` — turns it into `∫_p^∞ (s+δ)^{-α} s^{-α-1}`, and the two together are the exact
derivative of `-(1/α) t^{-α}(t+δ)^{-α}`, whose only boundary value is `(1/α)(p(1-p))^{-α}`: that
is the fourth term of `Theta`. Of the rest, the `diamondNear` integrals over `[0, p]` and
`[0, 1-p]` and the `diamondFar` integrals over `[p, ∞)` and `[1-p, ∞)` differ by integrals over
the middle interval `[p, 1-p]`, and there
`diamondNear α t = diamondFar α t - diamondMid α t` identically, so the mismatch is exactly the
third term of `Theta`.

Finally the hypothesis `p ≤ 1/2` of `Theta_eq_Theta_half` is removed: `hasDerivAt_Theta` holds
throughout `(0, 1)`, so `Theta α` is constant there, and the left-hand side of the profile
identity is symmetric under `p ↦ 1 - p`.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open CenteredMaximal.Cauchy

open scoped Real Topology

namespace CenteredMaximal.Fractional

/-! ### The shifted tail kernels -/

/-- The shifted far integrand `t ^ (-α) * (t + δ) ^ (-α - 1)`. -/
def diamondShift (α δ t : ℝ) : ℝ := t ^ (-α) * (t + δ) ^ (-α - 1)

/-- The companion `t ^ (-α - 1) * (t + δ) ^ (-α)` of `diamondShift`, which together with it makes
up an exact derivative. -/
def diamondShiftAlt (α δ t : ℝ) : ℝ := t ^ (-α - 1) * (t + δ) ^ (-α)

theorem continuousAt_diamondShift {α δ t : ℝ} (ht : 0 < t) (htd : 0 < t + δ) :
    ContinuousAt (fun s : ℝ => diamondShift α δ s) t :=
  (Real.continuousAt_rpow_const t (-α) (.inl ht.ne')).mul
    (ContinuousAt.rpow_const (f := fun s : ℝ => s + δ) (by fun_prop) (.inl htd.ne'))

theorem continuousAt_diamondShiftAlt {α δ t : ℝ} (ht : 0 < t) (htd : 0 < t + δ) :
    ContinuousAt (fun s : ℝ => diamondShiftAlt α δ s) t :=
  (Real.continuousAt_rpow_const t (-α - 1) (.inl ht.ne')).mul
    (ContinuousAt.rpow_const (f := fun s : ℝ => s + δ) (by fun_prop) (.inl htd.ne'))

theorem continuousOn_diamondShift {α δ c : ℝ} (hc : 0 < c) (hcd : 0 < c + δ) :
    ContinuousOn (fun t : ℝ => diamondShift α δ t) (Ioi c) := by
  intro t ht
  have ht' : c < t := ht
  exact (continuousAt_diamondShift (hc.trans ht') (by linarith)).continuousWithinAt

theorem continuousOn_diamondShiftAlt {α δ c : ℝ} (hc : 0 < c) (hcd : 0 < c + δ) :
    ContinuousOn (fun t : ℝ => diamondShiftAlt α δ t) (Ioi c) := by
  intro t ht
  have ht' : c < t := ht
  exact (continuousAt_diamondShiftAlt (hc.trans ht') (by linarith)).continuousWithinAt

theorem intervalIntegrable_diamondShift {α δ a b : ℝ} (ha : 0 < a) (had : 0 < a + δ) (hb : 0 < b)
    (hbd : 0 < b + δ) : IntervalIntegrable (fun t : ℝ => diamondShift α δ t) volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  rw [mem_uIcc] at ht
  have h0 : 0 < t := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have h1 : 0 < t + δ := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  exact (continuousAt_diamondShift h0 h1).continuousWithinAt

/-- Past `c` the factor `(t + δ) ^ (-α - 1)` is bounded by its value at `c`, so `diamondShift` is
dominated by `t ^ (-α)`, integrable at infinity because `α > 1`. -/
theorem integrableOn_diamondShift {α δ c : ℝ} (hα : 1 < α) (hc : 0 < c) (hcd : 0 < c + δ) :
    IntegrableOn (fun t : ℝ => diamondShift α δ t) (Ioi c) := by
  have hg : IntegrableOn (fun t : ℝ => (c + δ) ^ (-α - 1) * t ^ (-α)) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hc).const_mul _
  refine hg.mono' ((continuousOn_diamondShift hc hcd).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : c < t := ht
  have ht0 : 0 < t := hc.trans ht'
  have htd : 0 < t + δ := by linarith
  rw [Real.norm_eq_abs, diamondShift,
    abs_of_pos (mul_pos (Real.rpow_pos_of_pos ht0 _) (Real.rpow_pos_of_pos htd _)),
    mul_comm ((c + δ) ^ (-α - 1))]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hcd (by linarith) (by linarith))
    (Real.rpow_pos_of_pos ht0 _).le

/-- The companion kernel is dominated by `t ^ (-α - 1)`, integrable at infinity for every
`α > 0`. -/
theorem integrableOn_diamondShiftAlt {α δ c : ℝ} (hα : 0 < α) (hc : 0 < c) (hcd : 0 < c + δ) :
    IntegrableOn (fun t : ℝ => diamondShiftAlt α δ t) (Ioi c) := by
  have hg : IntegrableOn (fun t : ℝ => (c + δ) ^ (-α) * t ^ (-α - 1)) (Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hc).const_mul _
  refine hg.mono' ((continuousOn_diamondShiftAlt hc hcd).aestronglyMeasurable
    measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : c < t := ht
  have ht0 : 0 < t := hc.trans ht'
  have htd : 0 < t + δ := by linarith
  rw [Real.norm_eq_abs, diamondShiftAlt,
    abs_of_pos (mul_pos (Real.rpow_pos_of_pos ht0 _) (Real.rpow_pos_of_pos htd _)),
    mul_comm ((c + δ) ^ (-α))]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hcd (by linarith) (by linarith))
    (Real.rpow_pos_of_pos ht0 _).le

/-! ### The exact primitive of the shifted pair -/

/-- `-(1/α) t^{-α}(t+δ)^{-α}` is a primitive of `diamondShift α δ + diamondShiftAlt α δ`: the two
terms appear with coefficient `1` each. -/
theorem hasDerivAt_shiftAnti {α δ t : ℝ} (hα : α ≠ 0) (ht : 0 < t) (htd : 0 < t + δ) :
    HasDerivAt (fun s : ℝ => -(1 / α) * (s ^ (-α) * (s + δ) ^ (-α)))
      (diamondShift α δ t + diamondShiftAlt α δ t) t := by
  have h₁ : HasDerivAt (fun s : ℝ => s ^ (-α)) (-α * t ^ (-α - 1)) t :=
    Real.hasDerivAt_rpow_const (.inl ht.ne')
  have h₂ : HasDerivAt (fun s : ℝ => (s + δ) ^ (-α)) (1 * (-α) * (t + δ) ^ (-α - 1)) t :=
    HasDerivAt.rpow_const (f := fun s : ℝ => s + δ) ((hasDerivAt_id' t).add_const δ)
      (.inl htd.ne')
  refine ((h₁.mul h₂).const_mul (-(1 / α))).congr_deriv ?_
  simp only [diamondShift, diamondShiftAlt]
  field_simp
  ring

/-- The boundary value of the primitive at infinity is `0`. -/
theorem tendsto_shiftAnti_atTop {α δ : ℝ} (hα : 0 < α) :
    Tendsto (fun R : ℝ => -(1 / α) * (R ^ (-α) * (R + δ) ^ (-α))) atTop (𝓝 0) := by
  have h₁ : Tendsto (fun R : ℝ => R ^ (-α)) atTop (𝓝 0) := tendsto_rpow_neg_atTop hα
  have h₂ : Tendsto (fun R : ℝ => (R + δ) ^ (-α)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hα).comp (tendsto_atTop_add_const_right atTop δ tendsto_id)
  simpa using (h₁.mul h₂).const_mul (-(1 / α))

/-- **Step B: the exact primitive.** For `1 < α` and `0 < c`, `0 < c + δ`,
`∫_c^∞ (t^{-α}(t+δ)^{-α-1} + t^{-α-1}(t+δ)^{-α}) = (1/α)(c(c+δ))^{-α}`. -/
theorem integral_Ioi_diamondShift_add {α δ c : ℝ} (hα : 1 < α) (hc : 0 < c) (hcd : 0 < c + δ) :
    (∫ t in Ioi c, diamondShift α δ t) + ∫ t in Ioi c, diamondShiftAlt α δ t
      = 1 / α * (c * (c + δ)) ^ (-α) := by
  have hα0 : (0:ℝ) < α := by linarith
  have hI₁ : IntegrableOn (fun t : ℝ => diamondShift α δ t) (Ioi c) :=
    integrableOn_diamondShift hα hc hcd
  have hI₂ : IntegrableOn (fun t : ℝ => diamondShiftAlt α δ t) (Ioi c) :=
    integrableOn_diamondShiftAlt hα0 hc hcd
  have t₁ : Tendsto (fun R : ℝ => ∫ t in c..R, diamondShift α δ t) atTop
      (𝓝 (∫ t in Ioi c, diamondShift α δ t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi c hI₁ tendsto_id
  have t₂ : Tendsto (fun R : ℝ => ∫ t in c..R, diamondShiftAlt α δ t) atTop
      (𝓝 (∫ t in Ioi c, diamondShiftAlt α δ t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi c hI₂ tendsto_id
  have key₂ := (tendsto_shiftAnti_atTop (δ := δ) hα0).sub_const
    (-(1 / α) * (c ^ (-α) * (c + δ) ^ (-α)))
  have heq : ∀ᶠ R : ℝ in atTop,
      -(1 / α) * (R ^ (-α) * (R + δ) ^ (-α)) - -(1 / α) * (c ^ (-α) * (c + δ) ^ (-α))
        = (∫ t in c..R, diamondShift α δ t) + ∫ t in c..R, diamondShiftAlt α δ t := by
    filter_upwards [eventually_ge_atTop c] with R hR
    have hR0 : 0 < R := hc.trans_le hR
    have hRd : 0 < R + δ := by linarith
    have hA : IntervalIntegrable (fun t : ℝ => diamondShift α δ t) volume c R :=
      intervalIntegrable_diamondShift hc hcd hR0 hRd
    have hB : IntervalIntegrable (fun t : ℝ => diamondShiftAlt α δ t) volume c R := by
      refine ContinuousOn.intervalIntegrable fun t ht => ?_
      rw [uIcc_of_le hR] at ht
      exact (continuousAt_diamondShiftAlt (by linarith [ht.1]) (by linarith [ht.1])
        ).continuousWithinAt
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => -(1 / α) * (s ^ (-α) * (s + δ) ^ (-α)))
      (f' := fun t : ℝ => diamondShift α δ t + diamondShiftAlt α δ t)
      (fun t ht => by
        rw [uIcc_of_le hR] at ht
        exact hasDerivAt_shiftAnti hα0.ne' (by linarith [ht.1]) (by linarith [ht.1]))
      (hA.add hB)
    rw [intervalIntegral.integral_add hA hB] at h
    exact h.symm
  have h := tendsto_nhds_unique (key₂.congr' heq) (t₁.add t₂)
  rw [← h, Real.mul_rpow hc.le hcd.le]
  ring

/-! ### The translation of the reflected tail -/

/-- Translating by `δ` identifies the reflected tail `∫_{c+δ}^∞ t^{-α}(t-δ)^{-α-1}` with the
companion kernel `∫_c^∞ s^{-α-1}(s+δ)^{-α}`. -/
theorem integral_Ioi_diamondShift_neg {α δ c : ℝ} (hα : 1 < α) (hc : 0 < c) (hcd : 0 < c + δ) :
    (∫ t in Ioi (c + δ), diamondShift α (-δ) t) = ∫ s in Ioi c, diamondShiftAlt α δ s := by
  have hα0 : (0:ℝ) < α := by linarith
  have hI₁ : IntegrableOn (fun t : ℝ => diamondShift α (-δ) t) (Ioi (c + δ)) :=
    integrableOn_diamondShift hα hcd (by linarith)
  have hI₂ : IntegrableOn (fun t : ℝ => diamondShiftAlt α δ t) (Ioi c) :=
    integrableOn_diamondShiftAlt hα0 hc hcd
  have t₁ : Tendsto (fun R : ℝ => ∫ t in (c + δ)..(R + δ), diamondShift α (-δ) t) atTop
      (𝓝 (∫ t in Ioi (c + δ), diamondShift α (-δ) t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi (c + δ) hI₁
      (tendsto_atTop_add_const_right atTop δ tendsto_id)
  have t₂ : Tendsto (fun R : ℝ => ∫ s in c..R, diamondShiftAlt α δ s) atTop
      (𝓝 (∫ s in Ioi c, diamondShiftAlt α δ s)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi c hI₂ tendsto_id
  refine tendsto_nhds_unique t₁ (t₂.congr fun R => ?_)
  rw [← intervalIntegral.integral_comp_add_right (fun t : ℝ => diamondShift α (-δ) t) δ]
  refine intervalIntegral.integral_congr fun s _ => ?_
  simp only [diamondShift, diamondShiftAlt, show ∀ x : ℝ, x + δ + -δ = x from fun x => by ring]
  ring

/-- **Step B, in the form the rearrangement needs.** The two shifted tails, one starting at `c`
and one at `c + δ`, add up to the single boundary value `(1/α)(c(c+δ))^{-α}`. -/
theorem integral_Ioi_diamondShift_pair {α δ c : ℝ} (hα : 1 < α) (hc : 0 < c) (hcd : 0 < c + δ) :
    (∫ t in Ioi c, diamondShift α δ t) + ∫ t in Ioi (c + δ), diamondShift α (-δ) t
      = 1 / α * (c * (c + δ)) ^ (-α) := by
  rw [integral_Ioi_diamondShift_neg hα hc hcd]
  exact integral_Ioi_diamondShift_add hα hc hcd

/-! ### The second difference at the origin -/

/-- **The second-order vanishing of `(1+t)^{-α} + (1-t)^{-α} - 2` at `t = 0`.** One mean value
estimate upgrades the first-order bound `exists_nearBracket_bound` on the derivative: on `[0, t]`
the derivative is at most `α C t` in absolute value, so the increment over that interval is at
most `α C t²`. -/
theorem abs_diamondSecond_le {α : ℝ} (hα : 0 < α) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) b,
      |(1 + t) ^ (-α) + (1 - t) ^ (-α) - 2| ≤ C * t ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_nearBracket_bound hα hb0 hb
  refine ⟨α * C, by positivity, fun t ht => ?_⟩
  obtain ⟨ht0, htb⟩ := ht
  have hsub : Icc (0:ℝ) t ⊆ Icc (0:ℝ) b := Icc_subset_Icc le_rfl htb
  have hderiv : ∀ s ∈ Icc (0:ℝ) t,
      HasDerivWithinAt (fun y : ℝ => (1 + y) ^ (-α) + (1 - y) ^ (-α) - 2)
        (-α * ((1 + s) ^ (-α - 1) - (1 - s) ^ (-α - 1))) (Icc (0:ℝ) t) s := by
    intro s hs
    have hs1 : (0:ℝ) < 1 + s := by linarith [hs.1]
    have hs2 : (0:ℝ) < 1 - s := by linarith [(hsub hs).2]
    have h₁ : HasDerivAt (fun y : ℝ => (1 + y) ^ (-α)) (1 * (-α) * (1 + s) ^ (-α - 1)) s :=
      HasDerivAt.rpow_const (f := fun y : ℝ => 1 + y) ((hasDerivAt_id' s).const_add 1)
        (.inl hs1.ne')
    have h₂ : HasDerivAt (fun y : ℝ => (1 - y) ^ (-α)) (-1 * (-α) * (1 - s) ^ (-α - 1)) s :=
      HasDerivAt.rpow_const (f := fun y : ℝ => 1 - y) ((hasDerivAt_id' s).const_sub 1)
        (.inl hs2.ne')
    exact (((h₁.add h₂).sub_const 2).congr_deriv (by ring)).hasDerivWithinAt
  have hbound : ∀ s ∈ Icc (0:ℝ) t,
      ‖-α * ((1 + s) ^ (-α - 1) - (1 - s) ^ (-α - 1))‖ ≤ α * C * t := by
    intro s hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_neg (by linarith : -α < 0)]
    have h := hC s (hsub hs)
    have : C * s ≤ C * t := mul_le_mul_of_nonneg_left hs.2 hC0
    calc -(-α) * |(1 + s) ^ (-α - 1) - (1 - s) ^ (-α - 1)| ≤ α * (C * t) := by
          have hle : |(1 + s) ^ (-α - 1) - (1 - s) ^ (-α - 1)| ≤ C * t := h.trans this
          nlinarith [abs_nonneg ((1 + s) ^ (-α - 1) - (1 - s) ^ (-α - 1))]
      _ = α * C * t := by ring
  have key := (convex_Icc (0:ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (left_mem_Icc.mpr ht0) (right_mem_Icc.mpr ht0)
  have h0 : (1 + (0:ℝ)) ^ (-α) + (1 - (0:ℝ)) ^ (-α) - 2 = 0 := by norm_num
  have hkey : |(1 + t) ^ (-α) + (1 - t) ^ (-α) - 2| ≤ α * C * t * ‖t - (0:ℝ)‖ :=
    calc |(1 + t) ^ (-α) + (1 - t) ^ (-α) - 2|
        = ‖((1 + t) ^ (-α) + (1 - t) ^ (-α) - 2)
            - ((1 + (0:ℝ)) ^ (-α) + (1 - (0:ℝ)) ^ (-α) - 2)‖ := by
          rw [h0, sub_zero, Real.norm_eq_abs]
      _ ≤ α * C * t * ‖t - (0:ℝ)‖ := key
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht0] at hkey
  calc |(1 + t) ^ (-α) + (1 - t) ^ (-α) - 2| ≤ α * C * t * t := hkey
    _ = α * C * t ^ 2 := by ring

/-! ### The two by-parts primitives -/

/-- The by-parts primitive on the near branch `0 ≤ t < 1`. -/
def diamondAntiNear (α t : ℝ) : ℝ := ((1 + t) ^ (-α) + (1 - t) ^ (-α) - 2) * (-(t ^ (-α)) / α)

/-- The by-parts primitive on the far branch. -/
def diamondAntiFar (α δ t : ℝ) : ℝ :=
  ((1 + t) ^ (-α) + (t + δ) ^ (-α) - 2) * (-(t ^ (-α)) / α)

@[simp]
theorem diamondAntiNear_zero (α : ℝ) : diamondAntiNear α 0 = 0 := by
  simp only [diamondAntiNear, add_zero, sub_zero, Real.one_rpow]
  ring

/-- At the corner `t = a` the two primitives agree, because `a + (1 - 2a) = 1 - a`. -/
theorem diamondAntiFar_eq_near (α a : ℝ) :
    diamondAntiFar α (1 - 2 * a) a = diamondAntiNear α a := by
  simp only [diamondAntiFar, diamondAntiNear, show a + (1 - 2 * a) = 1 - a from by ring]

theorem hasDerivAt_diamondAntiNear {α t : ℝ} (hα : α ≠ 0) (ht : 0 < t) (ht' : t < 1) :
    HasDerivAt (fun s : ℝ => diamondAntiNear α s)
      (diamondNear α t + ((1 + t) ^ (-α) + (1 - t) ^ (-α) - 2) * t ^ (-α - 1)) t := by
  have h₁ : HasDerivAt (fun s : ℝ => (1 + s) ^ (-α)) (1 * (-α) * (1 + t) ^ (-α - 1)) t :=
    HasDerivAt.rpow_const (f := fun s : ℝ => 1 + s) ((hasDerivAt_id' t).const_add 1)
      (.inl (by linarith : (0:ℝ) < 1 + t).ne')
  have h₂ : HasDerivAt (fun s : ℝ => (1 - s) ^ (-α)) (-1 * (-α) * (1 - t) ^ (-α - 1)) t :=
    HasDerivAt.rpow_const (f := fun s : ℝ => 1 - s) ((hasDerivAt_id' t).const_sub 1)
      (.inl (by linarith : (0:ℝ) < 1 - t).ne')
  have h₃ : HasDerivAt (fun s : ℝ => -(s ^ (-α)) / α) (t ^ (-α - 1)) t := by
    refine ((Real.hasDerivAt_rpow_const (p := -α) (.inl ht.ne')).neg.div_const α).congr_deriv ?_
    field_simp
  refine (((h₁.add h₂).sub_const 2).mul h₃).congr_deriv ?_
  simp only [diamondNear, Pi.add_apply]
  field_simp
  ring

theorem hasDerivAt_diamondAntiFar {α δ t : ℝ} (hα : α ≠ 0) (ht : 0 < t) (htd : 0 < t + δ) :
    HasDerivAt (fun s : ℝ => diamondAntiFar α δ s)
      (diamondFar α t + diamondShift α δ t
        + ((1 + t) ^ (-α) + (t + δ) ^ (-α) - 2) * t ^ (-α - 1)) t := by
  have h₁ : HasDerivAt (fun s : ℝ => (1 + s) ^ (-α)) (1 * (-α) * (1 + t) ^ (-α - 1)) t :=
    HasDerivAt.rpow_const (f := fun s : ℝ => 1 + s) ((hasDerivAt_id' t).const_add 1)
      (.inl (by linarith : (0:ℝ) < 1 + t).ne')
  have h₂ : HasDerivAt (fun s : ℝ => (s + δ) ^ (-α)) (1 * (-α) * (t + δ) ^ (-α - 1)) t :=
    HasDerivAt.rpow_const (f := fun s : ℝ => s + δ) ((hasDerivAt_id' t).add_const δ)
      (.inl htd.ne')
  have h₃ : HasDerivAt (fun s : ℝ => -(s ^ (-α)) / α) (t ^ (-α - 1)) t := by
    refine ((Real.hasDerivAt_rpow_const (p := -α) (.inl ht.ne')).neg.div_const α).congr_deriv ?_
    field_simp
  refine (((h₁.add h₂).sub_const 2).mul h₃).congr_deriv ?_
  simp only [diamondFar, diamondShift, Pi.add_apply]
  field_simp
  ring

theorem continuousAt_diamondAntiNear {α t : ℝ} (hα : α ≠ 0) (ht : 0 < t) (ht' : t < 1) :
    ContinuousAt (fun s : ℝ => diamondAntiNear α s) t :=
  (hasDerivAt_diamondAntiNear hα ht ht').continuousAt

/-- The near primitive is `O(t^{2-α})` at the origin, hence tends to `0` there: this is where
`α < 2` is spent, and it is what removes the boundary term at `0`. -/
theorem tendsto_diamondAntiNear_zero {α : ℝ} (hα : 1 < α) (hα' : α < 2) :
    Tendsto (fun t : ℝ => diamondAntiNear α t) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  have hα0 : (0:ℝ) < α := by linarith
  obtain ⟨C, hC0, hC⟩ := abs_diamondSecond_le (b := 1/2) hα0 (by norm_num) (by norm_num)
  have hpow : Tendsto (fun t : ℝ => C / α * t ^ (2 - α)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => t ^ (2 - α)) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ) ^ (2 - α))) :=
      Real.continuousAt_rpow_const 0 (2 - α) (.inr (by linarith))
    rw [Real.zero_rpow (by linarith : (0:ℝ) < 2 - α).ne'] at hc
    simpa using (hc.mono_left nhdsWithin_le_nhds).const_mul (C / α)
  refine squeeze_zero_norm' ?_ hpow
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1/2)] with t ht
  have ht0 : 0 < t := ht.1
  have hb := hC t ⟨ht0.le, ht.2.le⟩
  rw [Real.norm_eq_abs, diamondAntiNear, abs_mul, abs_div, abs_neg,
    abs_of_nonneg (Real.rpow_nonneg ht0.le _), abs_of_pos hα0]
  have hrw : t ^ (-α) / α * (C * t ^ 2) = C / α * t ^ (2 - α) := by
    rw [show (2:ℝ) - α = 2 + -α from by ring, Real.rpow_add ht0, Real.rpow_two]
    ring
  calc |(1 + t) ^ (-α) + (1 - t) ^ (-α) - 2| * (t ^ (-α) / α)
      ≤ C * t ^ 2 * (t ^ (-α) / α) :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = C / α * t ^ (2 - α) := by rw [← hrw]; ring

theorem continuousOn_diamondAntiNear {α a : ℝ} (hα : 1 < α) (hα' : α < 2) (ha' : a < 1) :
    ContinuousOn (fun s : ℝ => diamondAntiNear α s) (Icc 0 a) := by
  have hα0 : (0:ℝ) < α := by linarith
  intro x hx
  rcases eq_or_lt_of_le hx.1 with rfl | hx0
  · refine ContinuousWithinAt.mono ?_ Icc_subset_Ici_self
    rw [← continuousWithinAt_Ioi_iff_Ici]
    show Tendsto (fun s : ℝ => diamondAntiNear α s) (𝓝[>] (0:ℝ)) (𝓝 (diamondAntiNear α 0))
    rw [diamondAntiNear_zero]
    exact tendsto_diamondAntiNear_zero hα hα'
  · exact (continuousAt_diamondAntiNear hα0.ne' hx0
      (lt_of_le_of_lt hx.2 ha')).continuousWithinAt

/-! ### Identifying the profile integrand on each branch -/

theorem diamondDiff_eq_near {α a t : ℝ} (ht : 0 < t) (hta : t ≤ a) :
    diamondDiff α a (1 - a) t = ((1 + t) ^ (-α) + (1 - t) ^ (-α) - 2) * t ^ (-α - 1) := by
  have h1 : |a + t| + (1 - a) = 1 + t := by
    rw [abs_of_pos (by linarith : (0:ℝ) < a + t)]; ring
  have h2 : |a - t| + (1 - a) = 1 - t := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ a - t)]; ring
  rw [diamondDiff, h1, h2, show a + (1 - a) = (1:ℝ) from by ring, Real.one_rpow, mul_one,
    abs_of_pos ht, show -(1 + α) = -α - 1 from by ring]

theorem diamondDiff_eq_far {α a t : ℝ} (ha : 0 < a) (hat : a ≤ t) :
    diamondDiff α a (1 - a) t
      = ((1 + t) ^ (-α) + (t + (1 - 2 * a)) ^ (-α) - 2) * t ^ (-α - 1) := by
  have ht : 0 < t := ha.trans_le hat
  have h1 : |a + t| + (1 - a) = 1 + t := by
    rw [abs_of_pos (by linarith : (0:ℝ) < a + t)]; ring
  have h2 : |a - t| + (1 - a) = t + (1 - 2 * a) := by
    rw [abs_of_nonpos (by linarith : a - t ≤ 0)]; ring
  rw [diamondDiff, h1, h2, show a + (1 - a) = (1:ℝ) from by ring, Real.one_rpow, mul_one,
    abs_of_pos ht, show -(1 + α) = -α - 1 from by ring]

/-! ### The two halves of the integration by parts -/

/-- **The near branch.** The fundamental theorem of calculus on the *closed* interval `[0, a]`;
no limiting argument is needed, because `diamondAntiNear` is continuous at `0` with value `0`. -/
theorem integral_diamondDiff_near {α a : ℝ} (hα : 1 < α) (hα' : α < 2) (ha : 0 < a) (ha' : a < 1) :
    (∫ t in (0:ℝ)..a, diamondNear α t) + ∫ t in (0:ℝ)..a, diamondDiff α a (1 - a) t
      = diamondAntiNear α a := by
  have hα0 : (0:ℝ) < α := by linarith
  have hn : IntervalIntegrable (fun t : ℝ => diamondNear α t) volume 0 a :=
    intervalIntegrable_diamondNear hα0 hα' ha ha'
  have hd : IntervalIntegrable (fun t : ℝ => diamondDiff α a (1 - a) t) volume 0 a :=
    (integrable_diamondDiff hα0 hα' ha (by linarith)).intervalIntegrable
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    (f := fun s : ℝ => diamondAntiNear α s)
    (f' := fun t : ℝ => diamondNear α t + diamondDiff α a (1 - a) t) ha.le
    (continuousOn_diamondAntiNear hα hα' ha')
    (fun x hx => ((hasDerivAt_diamondAntiNear hα0.ne' hx.1 (hx.2.trans ha')).congr_deriv
      (by rw [diamondDiff_eq_near hx.1 hx.2.le])).hasDerivWithinAt) (hn.add hd)
  rwa [intervalIntegral.integral_add hn hd, diamondAntiNear_zero, sub_zero] at h

/-- **The far branch.** The fundamental theorem of calculus on `[a, R]` followed by `R → ∞`; the
boundary value at infinity vanishes because the second difference stays bounded while
`t^{-α} → 0`. -/
theorem integral_diamondDiff_far {α a : ℝ} (hα : 1 < α) (hα' : α < 2) (ha : 0 < a) (ha' : a < 1) :
    (∫ t in Ioi a, diamondFar α t) + (∫ t in Ioi a, diamondShift α (1 - 2 * a) t)
        + ∫ t in Ioi a, diamondDiff α a (1 - a) t
      = -diamondAntiFar α (1 - 2 * a) a := by
  have hα0 : (0:ℝ) < α := by linarith
  have had : (0:ℝ) < a + (1 - 2 * a) := by linarith
  have hIf : IntegrableOn (fun t : ℝ => diamondFar α t) (Ioi a) :=
    integrableOn_diamondFar hα0 ha ha'
  have hIs : IntegrableOn (fun t : ℝ => diamondShift α (1 - 2 * a) t) (Ioi a) :=
    integrableOn_diamondShift hα ha had
  have hId : IntegrableOn (fun t : ℝ => diamondDiff α a (1 - a) t) (Ioi a) :=
    (integrable_diamondDiff hα0 hα' ha (by linarith)).integrableOn
  have t₁ := MeasureTheory.intervalIntegral_tendsto_integral_Ioi a hIf tendsto_id
  have t₂ := MeasureTheory.intervalIntegral_tendsto_integral_Ioi a hIs tendsto_id
  have t₃ := MeasureTheory.intervalIntegral_tendsto_integral_Ioi a hId tendsto_id
  have hinf : Tendsto (fun R : ℝ => diamondAntiFar α (1 - 2 * a) R) atTop (𝓝 0) := by
    have e₁ : Tendsto (fun R : ℝ => (1 + R) ^ (-α)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hα0).comp (tendsto_atTop_add_const_left atTop 1 tendsto_id)
    have e₂ : Tendsto (fun R : ℝ => (R + (1 - 2 * a)) ^ (-α)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hα0).comp
        (tendsto_atTop_add_const_right atTop (1 - 2 * a) tendsto_id)
    have e₃ : Tendsto (fun R : ℝ => -(R ^ (-α)) / α) atTop (𝓝 0) := by
      simpa using ((tendsto_rpow_neg_atTop hα0).neg).div_const α
    have := ((e₁.add e₂).sub_const 2).mul e₃
    simpa [diamondAntiFar] using this
  have key := hinf.sub_const (diamondAntiFar α (1 - 2 * a) a)
  have heq : ∀ᶠ R : ℝ in atTop,
      diamondAntiFar α (1 - 2 * a) R - diamondAntiFar α (1 - 2 * a) a
        = (∫ t in a..R, diamondFar α t) + (∫ t in a..R, diamondShift α (1 - 2 * a) t)
          + ∫ t in a..R, diamondDiff α a (1 - a) t := by
    filter_upwards [eventually_ge_atTop a] with R hR
    have hR0 : 0 < R := ha.trans_le hR
    have hRd : (0:ℝ) < R + (1 - 2 * a) := by linarith
    have hA : IntervalIntegrable (fun t : ℝ => diamondFar α t) volume a R :=
      intervalIntegrable_diamondFar ha hR0
    have hB : IntervalIntegrable (fun t : ℝ => diamondShift α (1 - 2 * a) t) volume a R :=
      intervalIntegrable_diamondShift ha had hR0 hRd
    have hC : IntervalIntegrable (fun t : ℝ => diamondDiff α a (1 - a) t) volume a R :=
      (integrable_diamondDiff hα0 hα' ha (by linarith)).intervalIntegrable
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => diamondAntiFar α (1 - 2 * a) s)
      (f' := fun t : ℝ => diamondFar α t + diamondShift α (1 - 2 * a) t
        + diamondDiff α a (1 - a) t)
      (fun t ht => by
        rw [uIcc_of_le hR] at ht
        exact (hasDerivAt_diamondAntiFar hα0.ne' (by linarith [ht.1]) (by linarith [ht.1])
          ).congr_deriv (by rw [diamondDiff_eq_far ha ht.1]))
      ((hA.add hB).add hC)
    rw [intervalIntegral.integral_add (hA.add hB) hC, intervalIntegral.integral_add hA hB] at h
    exact h.symm
  have h := tendsto_nhds_unique (key.congr' heq) ((t₁.add t₂).add t₃)
  rw [← h, zero_sub]

/-! ### Step A: the integration by parts -/

/-- **Step A.** For `0 < a < 1` the second-difference profile on the unit diamond is `-2` times
the sum of three first-order integrals: the near integrand on `[0, a]`, the far integrand on
`[a, ∞)`, and the shifted tail `t^{-α}(t + 1 - 2a)^{-α-1}` on `[a, ∞)`.

Only the normalised case `a + b = 1` is stated, which is all `diamondProfile_eq_rpow_mul` leaves
to do; it is also what makes the near branch land exactly on `diamondNear`. -/
theorem diamondProfile_eq_byParts {α a : ℝ} (hα : 1 < α) (hα' : α < 2) (ha : 0 < a)
    (ha' : a < 1) :
    diamondProfile α a (1 - a)
      = -2 * ((∫ t in (0:ℝ)..a, diamondNear α t) + (∫ t in Ioi a, diamondFar α t)
          + ∫ t in Ioi a, diamondShift α (1 - 2 * a) t) := by
  have hα0 : (0:ℝ) < α := by linarith
  have hb : (0:ℝ) < 1 - a := by linarith
  have heven := integral_of_even (diamondDiff_neg α a (1 - a))
    (integrableOn_diamondDiff_Ioi_zero hα0 hα' ha hb)
  have hsplit : (∫ t in Ioi (0:ℝ), diamondDiff α a (1 - a) t)
      = (∫ t in (0:ℝ)..a, diamondDiff α a (1 - a) t)
        + ∫ t in Ioi a, diamondDiff α a (1 - a) t := by
    rw [← Ioc_union_Ioi_eq_Ioi ha.le,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp
          (integrable_diamondDiff hα0 hα' ha hb).intervalIntegrable)
        (integrable_diamondDiff hα0 hα' ha hb).integrableOn,
      intervalIntegral.integral_of_le ha.le]
  have hnear := integral_diamondDiff_near hα hα' ha ha'
  have hfar := integral_diamondDiff_far hα hα' ha ha'
  rw [diamondProfile_eq_integral, heven, hsplit, diamondAntiFar_eq_near] at *
  linarith

/-! ### Step C: the rearrangement -/

theorem intervalIntegrable_diamondNear_of_mem {α a b : ℝ} (ha : 0 < a) (ha' : a < 1) (hb : 0 < b)
    (hb' : b < 1) : IntervalIntegrable (fun t : ℝ => diamondNear α t) volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  rw [mem_uIcc] at ht
  have h0 : 0 < t := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have h1 : t < 1 := by rcases ht with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
  exact (continuousAt_diamondNear h0 h1).continuousWithinAt

/-- The profile identity on the first half of the diamond. -/
theorem diamondProfile_add_eq_of_le {α p : ℝ} (hα : 1 < α) (hα' : α < 2) (hp : 0 < p)
    (hp' : p ≤ 1/2) :
    diamondProfile α p (1 - p) + diamondProfile α (1 - p) p = -2 * Theta α p := by
  have hα0 : (0:ℝ) < α := by linarith
  have hp1 : p < 1 := by linarith
  have hq : (0:ℝ) < 1 - p := by linarith
  have hq1 : (1:ℝ) - p < 1 := by linarith
  have hpq : p ≤ 1 - p := by linarith
  -- the two by-parts identities
  have e₁ := diamondProfile_eq_byParts hα hα' hp hp1
  have e₂ := diamondProfile_eq_byParts hα hα' hq hq1
  rw [show (1:ℝ) - (1 - p) = p from by ring] at e₂
  -- the two shifted tails add up to the fourth term of `Theta`
  have hpair := integral_Ioi_diamondShift_pair (α := α) (δ := 1 - 2 * p) (c := p) hα hp
    (by linarith)
  rw [show p + (1 - 2 * p) = 1 - p from by ring,
    show -(1 - 2 * p) = 1 - 2 * (1 - p) from by ring] at hpair
  -- the near integrals differ by the integral over the middle interval
  have hadj : (∫ t in (0:ℝ)..p, diamondNear α t) + (∫ t in p..(1 - p), diamondNear α t)
      = ∫ t in (0:ℝ)..(1 - p), diamondNear α t :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_diamondNear hα0 hα' hp hp1)
      (intervalIntegrable_diamondNear_of_mem hp hp1 hq hq1)
  -- so do the far integrals
  have hfar : (∫ t in Ioi p, diamondFar α t)
      = (∫ t in p..(1 - p), diamondFar α t) + ∫ t in Ioi (1 - p), diamondFar α t := by
    rw [← Ioc_union_Ioi_eq_Ioi hpq,
      setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hpq).mp
          (intervalIntegrable_diamondFar hp hq))
        (integrableOn_diamondFar hα0 hq hq1),
      intervalIntegral.integral_of_le hpq]
  -- and the mismatch is the middle term of `Theta`, by the pointwise identity
  have hmid : (∫ t in p..(1 - p), diamondNear α t)
      = (∫ t in p..(1 - p), diamondFar α t) - ∫ t in p..(1 - p), diamondMid α t := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_diamondFar hp hq)
      (intervalIntegrable_diamondMid hp hp1 hq hq1)]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [diamondNear, diamondFar, diamondMid]
    ring
  rw [e₁, e₂]
  simp only [Theta]
  linarith

/-- **`Theta α` is constant on all of `(0, 1)`.** `hasDerivAt_Theta` holds throughout the open
interval, so the restriction `p ≤ 1/2` in `Theta_eq_Theta_half` can be dropped. -/
theorem Theta_eq_Theta_half' {α : ℝ} (hα : 1 < α) (hα' : α < 2) {p : ℝ} (hp : 0 < p)
    (hp' : p < 1) : Theta α p = Theta α (1/2) := by
  rcases le_or_gt p (1/2) with h | h
  · exact Theta_eq_Theta_half hα hα' hp h
  · refine constant_of_has_deriv_right_zero (f := Theta α) (a := 1/2) (b := p) ?_ ?_ p
      (right_mem_Icc.mpr h.le)
    · intro x hx
      exact (hasDerivAt_Theta hα hα' (by linarith [hx.1])
        (lt_of_le_of_lt hx.2 hp')).continuousAt.continuousWithinAt
    · intro x hx
      exact (hasDerivAt_Theta hα hα' (by linarith [hx.1])
        (hx.2.trans hp')).hasDerivWithinAt

/-- **The missing link.** For `1 < α < 2` and `0 < p < 1` the two second-difference profiles at
the point `p` of the unit diamond add up to `-2` times the first-order profile `Theta α p`. -/
theorem diamondProfile_add_eq {α p : ℝ} (hα : 1 < α) (hα' : α < 2) (hp : 0 < p) (hp' : p < 1) :
    diamondProfile α p (1 - p) + diamondProfile α (1 - p) p = -2 * Theta α p := by
  rcases le_or_gt p (1/2) with h | h
  · exact diamondProfile_add_eq_of_le hα hα' hp h
  · have hq : (0:ℝ) < 1 - p := by linarith
    have key := diamondProfile_add_eq_of_le hα hα' hq (by linarith)
    rw [show (1:ℝ) - (1 - p) = p from by ring] at key
    have hTh : Theta α p = Theta α (1 - p) := by
      rw [Theta_eq_Theta_half' hα hα' hp hp', Theta_eq_Theta_half' hα hα' hq (by linarith)]
    rw [hTh]
    linarith

/-! ### The generator of the diamond power -/

/-- **The fractional generator of the diamond power.** For `1 < α < 2` and `z` off the coordinate
axes,
`jumpGen α (r^{-α}) z = -4π Γ(2α) cos(πα/2) / (α Γ(α)^2 sin(πα/2)) · r(z)^{-2α}`,
with `r = diamondNorm` the diamond radius. The coefficient is positive on `1 < α < 2`, since
`cos(πα/2) < 0` there. -/
theorem jumpGen_diamondPow_eq_const {α : ℝ} (hα : 1 < α) (hα' : α < 2) {z : Fin 2 → ℝ}
    (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) :
    jumpGen α (diamondPow α) z
      = -4 * π * Real.Gamma (2*α) * Real.cos (π*α/2)
          / (α * Real.Gamma α ^ 2 * Real.sin (π*α/2)) * diamondNorm z ^ (-2*α) := by
  have hα0 : (0:ℝ) < α := by linarith
  have ha : 0 < |z 0| := abs_pos.2 h0
  have hb : 0 < |z 1| := abs_pos.2 h1
  have hr : diamondNorm z = |z 0| + |z 1| := rfl
  have hr0 : 0 < diamondNorm z := by rw [hr]; linarith
  have hne : |z 0| + |z 1| ≠ 0 := by positivity
  have hp : 0 < |z 0| / diamondNorm z := div_pos ha hr0
  have hplt : |z 0| / diamondNorm z < 1 := by rw [div_lt_one hr0, hr]; linarith
  have hsub : |z 1| / diamondNorm z = 1 - |z 0| / diamondNorm z := by
    rw [hr]
    field_simp
    ring
  rw [jumpGen_diamondPow_eq hα0 hα' h0 h1, hsub, diamondProfile_add_eq hα hα' hp hplt,
    Theta_eq_Theta_half' hα hα' hp hplt, Theta_half_eq hα hα']
  ring

end CenteredMaximal.Fractional

end

end
