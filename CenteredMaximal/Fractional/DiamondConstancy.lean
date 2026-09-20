/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The diamond profile is constant along each diamond

The diamond-power identity for the fractional generator of order `α` reduces, after passing to one
dimension and integrating by parts, to the statement that one explicit function of the position
`p` along a diamond `{|u| + |v| = r}` does not depend on `p`. This file isolates and proves that
statement; it is pure one-variable calculus and mentions no fractional operator.

For `1 < α < 2` and `p ∈ (0, 1/2]` the **diamond profile** is

`Θ α p = 2 ∫_0^p t^{-α} ((1+t)^{-α-1} - (1-t)^{-α-1}) dt + 2 ∫_p^∞ t^{-α} (1+t)^{-α-1} dt`
`        - ∫_p^{1-p} t^{-α} (1-t)^{-α-1} dt + (1/α) (p (1-p))^{-α}`

(all powers are `Real.rpow`). The four terms individually blow up as `p → 0⁺`, but their
combination is constant, and `Theta_eq_Theta_half` says so.

## Main results

* `Theta`, `Theta_def`: the diamond profile and its unfolded form.
* `exists_nearBracket_bound`: the first-order vanishing of `(1+t)^{-α-1} - (1-t)^{-α-1}` at `0`,
  which is what makes the first integral converge.
* `integrableOn_diamondNear`, `integrableOn_diamondFar`, `intervalIntegrable_diamondMid`: the
  pieces of `Theta` are honest integrals.
* `diamond_cancel`: the exact algebraic cancellation of the four term derivatives.
* `hasDerivAt_Theta`: `Θ α` has derivative `0` at every `p ∈ (0, 1)`.
* `Theta_eq_Theta_half`: consequently `Θ α p = Θ α (1/2)` for `0 < p ≤ 1/2`.

## The cancellation

Differentiating the four terms at `p` gives, respectively,
`2 p^{-α} ((1+p)^{-α-1} - (1-p)^{-α-1})`, `-2 p^{-α} (1+p)^{-α-1}`,
`p^{-α} (1-p)^{-α-1} + (1-p)^{-α} p^{-α-1}` and `-(p(1-p))^{-α-1} (1 - 2p)`.
The `(1+p)^{-α-1}` contributions cancel between the first two. Writing `p^{-α} = p · p^{-α-1}`
and `(1-p)^{-α} = (1-p) · (1-p)^{-α-1}` and factoring `p^{-α-1} (1-p)^{-α-1}` out of what is left
leaves the bracket `-p + (1 - p) - (1 - 2p) = 0`. That identity is `diamond_cancel`, and it is the
entire content of the theorem; everything else is the fundamental theorem of calculus and
integrability bookkeeping.

The singularity at `t = 0` is genuine: `t^{-α}` alone is not integrable at `0` for `α > 1`, so the
first integrand must be estimated as a whole. The mean value theorem bounds its bracket by a
multiple of `t`, leaving the integrable comparison function `t^{1-α}` (here `α < 2` enters). At
infinity the second integrand decays like `t^{-2α-1}` (here `α > 0` enters).

The middle term has *two* moving endpoints. Its lower endpoint is handled by the fundamental
theorem of calculus directly, and its upper endpoint `1 - p` by `HasDerivAt.comp_const_sub`, which
avoids the general chain rule.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace CenteredMaximal.Fractional

/-! ### The three integrands -/

/-- The near-axis integrand `t^{-α} ((1+t)^{-α-1} - (1-t)^{-α-1})` of the diamond profile. -/
def diamondNear (α t : ℝ) : ℝ := t ^ (-α) * ((1 + t) ^ (-α - 1) - (1 - t) ^ (-α - 1))

/-- The far integrand `t^{-α} (1+t)^{-α-1}` of the diamond profile. -/
def diamondFar (α t : ℝ) : ℝ := t ^ (-α) * (1 + t) ^ (-α - 1)

/-- The middle integrand `t^{-α} (1-t)^{-α-1}` of the diamond profile. -/
def diamondMid (α t : ℝ) : ℝ := t ^ (-α) * (1 - t) ^ (-α - 1)

theorem continuousAt_diamondFar {α t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => diamondFar α s) t := by
  have h₁ : ContinuousAt (fun s : ℝ => s ^ (-α)) t :=
    Real.continuousAt_rpow_const t (-α) (.inl ht.ne')
  have h₂ : ContinuousAt (fun s : ℝ => (1 + s) ^ (-α - 1)) t :=
    ContinuousAt.rpow_const (f := fun s : ℝ => 1 + s) (by fun_prop)
      (.inl (by linarith : (0:ℝ) < 1 + t).ne')
  exact h₁.mul h₂

theorem continuousAt_diamondMid {α t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    ContinuousAt (fun s : ℝ => diamondMid α s) t := by
  have h₁ : ContinuousAt (fun s : ℝ => s ^ (-α)) t :=
    Real.continuousAt_rpow_const t (-α) (.inl ht.ne')
  have h₂ : ContinuousAt (fun s : ℝ => (1 - s) ^ (-α - 1)) t :=
    ContinuousAt.rpow_const (f := fun s : ℝ => 1 - s) (by fun_prop)
      (.inl (by linarith : (0:ℝ) < 1 - t).ne')
  exact h₁.mul h₂

theorem continuousAt_diamondNear {α t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    ContinuousAt (fun s : ℝ => diamondNear α s) t := by
  have h₁ : ContinuousAt (fun s : ℝ => s ^ (-α)) t :=
    Real.continuousAt_rpow_const t (-α) (.inl ht.ne')
  have h₂ : ContinuousAt (fun s : ℝ => (1 + s) ^ (-α - 1) - (1 - s) ^ (-α - 1)) t :=
    (ContinuousAt.rpow_const (f := fun s : ℝ => 1 + s) (by fun_prop)
        (.inl (by linarith : (0:ℝ) < 1 + t).ne')).sub
      (ContinuousAt.rpow_const (f := fun s : ℝ => 1 - s) (by fun_prop)
        (.inl (by linarith : (0:ℝ) < 1 - t).ne'))
  exact h₁.mul h₂

theorem continuousOn_diamondFar (α : ℝ) : ContinuousOn (fun t : ℝ => diamondFar α t) (Ioi 0) :=
  fun _ ht => (continuousAt_diamondFar ht).continuousWithinAt

theorem continuousOn_diamondNear (α : ℝ) : ContinuousOn (fun t : ℝ => diamondNear α t) (Ioo 0 1) :=
  fun _ ht => (continuousAt_diamondNear ht.1 ht.2).continuousWithinAt

/-! ### Integrability -/

theorem rpow_neg_mul_self {t α : ℝ} (ht : 0 < t) : t ^ (-α) * t = t ^ (1 - α) := by
  rw [show (1 : ℝ) - α = -α + 1 by ring, Real.rpow_add ht, Real.rpow_one]

/-- The bracket `(1+t)^{-α-1} - (1-t)^{-α-1}` vanishes to first order at `t = 0`: on `[0, b]`
with `b < 1` it is at most a constant multiple of `t`. This cancellation is essential, because
`t^{-α}` on its own is not integrable at `0` once `α > 1`. -/
theorem exists_nearBracket_bound {α : ℝ} (hα : 0 < α) {b : ℝ} (hb0 : 0 ≤ b) (hb : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0:ℝ) b,
      |(1 + t) ^ (-α - 1) - (1 - t) ^ (-α - 1)| ≤ C * t := by
  have hbb : (0:ℝ) < 1 - b := by linarith
  have hpb : (0:ℝ) < (1 - b) ^ (-α - 1 - 1) := Real.rpow_pos_of_pos hbb _
  refine ⟨|(-α - 1)| * (1 + (1 - b) ^ (-α - 1 - 1)),
    mul_nonneg (abs_nonneg _) (by linarith), fun t ht => ?_⟩
  have hderiv : ∀ s ∈ Icc (0:ℝ) b,
      HasDerivWithinAt (fun y : ℝ => (1 + y) ^ (-α - 1) - (1 - y) ^ (-α - 1))
        ((-α - 1) * (1 + s) ^ (-α - 1 - 1) + (-α - 1) * (1 - s) ^ (-α - 1 - 1))
        (Icc (0:ℝ) b) s := by
    intro s hs
    have hs1 : (0:ℝ) < 1 + s := by linarith [hs.1]
    have hs2 : (0:ℝ) < 1 - s := by linarith [hs.2]
    have h₁ : HasDerivAt (fun y : ℝ => (1 + y) ^ (-α - 1))
        (1 * (-α - 1) * (1 + s) ^ (-α - 1 - 1)) s :=
      HasDerivAt.rpow_const (f := fun y : ℝ => 1 + y)
        ((hasDerivAt_id' s).const_add 1) (.inl hs1.ne')
    have h₂ : HasDerivAt (fun y : ℝ => (1 - y) ^ (-α - 1))
        (-1 * (-α - 1) * (1 - s) ^ (-α - 1 - 1)) s :=
      HasDerivAt.rpow_const (f := fun y : ℝ => 1 - y)
        ((hasDerivAt_id' s).const_sub 1) (.inl hs2.ne')
    have h := (h₁.sub h₂).hasDerivWithinAt (s := Icc (0:ℝ) b)
    have heq : 1 * (-α - 1) * (1 + s) ^ (-α - 1 - 1) - -1 * (-α - 1) * (1 - s) ^ (-α - 1 - 1)
        = (-α - 1) * (1 + s) ^ (-α - 1 - 1) + (-α - 1) * (1 - s) ^ (-α - 1 - 1) := by ring
    rwa [heq] at h
  have hbound : ∀ s ∈ Icc (0:ℝ) b,
      ‖(-α - 1) * (1 + s) ^ (-α - 1 - 1) + (-α - 1) * (1 - s) ^ (-α - 1 - 1)‖
        ≤ |(-α - 1)| * (1 + (1 - b) ^ (-α - 1 - 1)) := by
    intro s hs
    have p₁ : (0:ℝ) < (1 + s) ^ (-α - 1 - 1) := Real.rpow_pos_of_pos (by linarith [hs.1]) _
    have p₂ : (0:ℝ) < (1 - s) ^ (-α - 1 - 1) := Real.rpow_pos_of_pos (by linarith [hs.2]) _
    have e₁ : (1 + s) ^ (-α - 1 - 1) ≤ 1 := by
      calc (1 + s) ^ (-α - 1 - 1) ≤ (1:ℝ) ^ (-α - 1 - 1) :=
            Real.rpow_le_rpow_of_nonpos one_pos (by linarith [hs.1]) (by linarith)
        _ = 1 := Real.one_rpow _
    have e₂ : (1 - s) ^ (-α - 1 - 1) ≤ (1 - b) ^ (-α - 1 - 1) :=
      Real.rpow_le_rpow_of_nonpos hbb (by linarith [hs.2]) (by linarith)
    rw [Real.norm_eq_abs, ← mul_add, abs_mul,
      abs_of_pos (by linarith : (0:ℝ) < (1 + s) ^ (-α - 1 - 1) + (1 - s) ^ (-α - 1 - 1))]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have key := (convex_Icc (0:ℝ) b).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (left_mem_Icc.mpr hb0) ht
  simpa [Real.one_rpow, Real.norm_eq_abs, abs_of_nonneg ht.1] using key

theorem integrableOn_diamondNear {α p : ℝ} (hα : 0 < α) (hα' : α < 2) (hp : 0 < p) (hp' : p < 1) :
    IntegrableOn (fun t : ℝ => diamondNear α t) (Ioo 0 p) := by
  obtain ⟨C, hC0, hC⟩ := exists_nearBracket_bound hα hp.le hp'
  have hg : Integrable (fun t : ℝ => C * t ^ (1 - α)) (volume.restrict (Ioo 0 p)) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hp).mpr (by linarith)).const_mul C
  refine hg.mono' (((continuousOn_diamondNear α).mono
    (Ioo_subset_Ioo le_rfl hp'.le)).aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have ht0 : 0 < t := ht.1
  simp only [Real.norm_eq_abs, diamondNear]
  calc |t ^ (-α) * ((1 + t) ^ (-α - 1) - (1 - t) ^ (-α - 1))|
      = t ^ (-α) * |(1 + t) ^ (-α - 1) - (1 - t) ^ (-α - 1)| := by
        rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos ht0 _)]
    _ ≤ t ^ (-α) * (C * t) :=
        mul_le_mul_of_nonneg_left (hC t ⟨ht0.le, ht.2.le⟩) (Real.rpow_pos_of_pos ht0 _).le
    _ = C * t ^ (1 - α) := by rw [← rpow_neg_mul_self (α := α) ht0]; ring

theorem intervalIntegrable_diamondNear {α p : ℝ} (hα : 0 < α) (hα' : α < 2) (hp : 0 < p)
    (hp' : p < 1) : IntervalIntegrable (fun t : ℝ => diamondNear α t) volume 0 p :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le hp.le).mpr
    (integrableOn_diamondNear hα hα' hp hp')

theorem intervalIntegrable_diamondFar {α a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ => diamondFar α t) volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  rw [Set.mem_uIcc] at ht
  have h0 : 0 < t := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  exact (continuousAt_diamondFar h0).continuousWithinAt

theorem intervalIntegrable_diamondMid {α a b : ℝ} (ha : 0 < a) (ha' : a < 1) (hb : 0 < b)
    (hb' : b < 1) : IntervalIntegrable (fun t : ℝ => diamondMid α t) volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  rw [Set.mem_uIcc] at ht
  have h0 : 0 < t := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  have h1 : t < 1 := by rcases ht with ⟨_, h⟩ | ⟨_, h⟩ <;> linarith
  exact (continuousAt_diamondMid h0 h1).continuousWithinAt

theorem integrableOn_diamondFar_tail {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun t : ℝ => diamondFar α t) (Ioi 1) := by
  have hg : Integrable (fun t : ℝ => t ^ (-(2 * α) - 1)) (volume.restrict (Ioi 1)) :=
    (integrableOn_Ioi_rpow_iff one_pos).mpr (by linarith)
  refine hg.mono' (((continuousOn_diamondFar α).mono
    (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1:ℝ) < t := ht
  simp only [Real.norm_eq_abs, diamondFar]
  calc |t ^ (-α) * (1 + t) ^ (-α - 1)|
      = t ^ (-α) * (1 + t) ^ (-α - 1) :=
        abs_of_pos (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
          (Real.rpow_pos_of_pos (by linarith) _))
    _ ≤ t ^ (-α) * t ^ (-α - 1) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith))
          (Real.rpow_pos_of_pos (by linarith) _).le
    _ = t ^ (-(2 * α) - 1) := by
        rw [← Real.rpow_add (by linarith), show -α + (-α - 1) = -(2 * α) - 1 by ring]

theorem integrableOn_diamondFar {α p : ℝ} (hα : 0 < α) (hp : 0 < p) (hp' : p < 1) :
    IntegrableOn (fun t : ℝ => diamondFar α t) (Ioi p) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hp'.le]
  exact IntegrableOn.union
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hp'.le).mp
      (intervalIntegrable_diamondFar hp one_pos))
    (integrableOn_diamondFar_tail hα)

/-! ### The diamond profile -/

/-- The **diamond profile**
`Θ α p = 2 ∫_0^p t^{-α} ((1+t)^{-α-1} - (1-t)^{-α-1}) + 2 ∫_p^∞ t^{-α} (1+t)^{-α-1}`
`        - ∫_p^{1-p} t^{-α} (1-t)^{-α-1} + (1/α) (p(1-p))^{-α}`,
the explicit function of the position `p` along a diamond which the diamond-power identity asserts
to be constant. -/
def Theta (α p : ℝ) : ℝ :=
  2 * (∫ t in (0:ℝ)..p, diamondNear α t) + 2 * (∫ t in Ioi p, diamondFar α t)
    - (∫ t in p..(1 - p), diamondMid α t) + 1 / α * (p * (1 - p)) ^ (-α)

theorem Theta_def (α p : ℝ) : Theta α p =
    2 * (∫ t in (0:ℝ)..p, t ^ (-α) * ((1 + t) ^ (-α - 1) - (1 - t) ^ (-α - 1)))
      + 2 * (∫ t in Ioi p, t ^ (-α) * (1 + t) ^ (-α - 1))
      - (∫ t in p..(1 - p), t ^ (-α) * (1 - t) ^ (-α - 1))
      + 1 / α * (p * (1 - p)) ^ (-α) := rfl

/-- Splitting the improper tail integral at `1` turns it into an interval integral plus a
constant, which is what makes it differentiable in the lower limit. -/
theorem integral_Ioi_diamondFar {α p : ℝ} (hα : 0 < α) (hp : 0 < p) (hp' : p < 1) :
    (∫ t in Ioi p, diamondFar α t)
      = (∫ t in p..1, diamondFar α t) + ∫ t in Ioi (1:ℝ), diamondFar α t := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hp'.le,
    setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le hp'.le).mp
        (intervalIntegrable_diamondFar hp one_pos))
      (integrableOn_diamondFar_tail hα),
    intervalIntegral.integral_of_le hp'.le]

/-- The exact algebraic cancellation behind the constancy: with `A = p^{-α-1}`,
`B = (1-p)^{-α-1}` and `E = (1+p)^{-α-1}` the sum of the four term derivatives collapses to
`A B (-p + (1 - p) - (1 - 2p)) = 0`. -/
theorem diamond_cancel {α p A B E : ℝ} (hα : α ≠ 0) :
    2 * (p * A * (E - B)) + 2 * -(p * A * E) - (-(p * A * B) + -((1 - p) * B * A))
      + 1 / α * ((1 - 2 * p) * -α * (A * B)) = 0 := by
  have h : 1 / α * ((1 - 2 * p) * -α * (A * B)) = -((1 - 2 * p) * (A * B)) := by
    have hx : (1 - 2 * p) * -α * (A * B) = α * -((1 - 2 * p) * (A * B)) := by ring
    rw [hx, ← mul_assoc, one_div, inv_mul_cancel₀ hα, one_mul]
  rw [h]
  ring

theorem hasDerivAt_Theta {α : ℝ} (hα : 1 < α) (hα' : α < 2) {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    HasDerivAt (Theta α) 0 p := by
  have hα0 : (0:ℝ) < α := by linarith
  have hq : (0:ℝ) < 1 - p := by linarith
  -- the first term: the fundamental theorem of calculus at the upper limit
  have hT1 : HasDerivAt (fun q : ℝ => ∫ t in (0:ℝ)..q, diamondNear α t) (diamondNear α p) p :=
    intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_diamondNear hα0 hα' hp hp')
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
        (fun x hx => continuousAt_diamondNear hx.1 hx.2) p ⟨hp, hp'⟩)
      (continuousAt_diamondNear hp hp')
  -- the improper tail: split off the constant piece beyond `1`
  have hT2 : HasDerivAt (fun q : ℝ => ∫ t in Ioi q, diamondFar α t) (-diamondFar α p) p := by
    have hsplit : (fun q : ℝ => ∫ t in Ioi q, diamondFar α t) =ᶠ[𝓝 p]
        fun q : ℝ => (∫ t in q..1, diamondFar α t) + ∫ t in Ioi (1:ℝ), diamondFar α t := by
      filter_upwards [Ioo_mem_nhds hp hp'] with q hq'
      exact integral_Ioi_diamondFar hα0 hq'.1 hq'.2
    have hC : HasDerivAt (fun q : ℝ => (∫ t in q..1, diamondFar α t)
        + ∫ t in Ioi (1:ℝ), diamondFar α t) (-diamondFar α p) p :=
      (intervalIntegral.integral_hasDerivAt_left
        (intervalIntegrable_diamondFar hp one_pos)
        (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
          (fun x hx => continuousAt_diamondFar hx) p hp)
        (continuousAt_diamondFar hp)).add_const _
    exact hC.congr_of_eventuallyEq hsplit
  -- the middle term: both endpoints move
  have hT3 : HasDerivAt (fun q : ℝ => ∫ t in q..(1 - q), diamondMid α t)
      (-diamondMid α p + -diamondMid α (1 - p)) p := by
    have hsplit : (fun q : ℝ => ∫ t in q..(1 - q), diamondMid α t) =ᶠ[𝓝 p]
        fun q : ℝ => (∫ t in q..(1/2 : ℝ), diamondMid α t)
          + ∫ t in (1/2 : ℝ)..(1 - q), diamondMid α t := by
      filter_upwards [Ioo_mem_nhds hp hp'] with q hq'
      exact (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_diamondMid hq'.1 hq'.2 (by norm_num) (by norm_num))
        (intervalIntegrable_diamondMid (by norm_num) (by norm_num)
          (by linarith [hq'.2]) (by linarith [hq'.1]))).symm
    have hA : HasDerivAt (fun q : ℝ => ∫ t in q..(1/2 : ℝ), diamondMid α t)
        (-diamondMid α p) p :=
      intervalIntegral.integral_hasDerivAt_left
        (intervalIntegrable_diamondMid hp hp' (by norm_num) (by norm_num))
        (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
          (fun x hx => continuousAt_diamondMid hx.1 hx.2) p ⟨hp, hp'⟩)
        (continuousAt_diamondMid hp hp')
    have hv : HasDerivAt (fun u : ℝ => ∫ t in (1/2 : ℝ)..u, diamondMid α t)
        (diamondMid α (1 - p)) (1 - p) :=
      intervalIntegral.integral_hasDerivAt_right
        (intervalIntegrable_diamondMid (by norm_num) (by norm_num) hq (by linarith))
        (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
          (fun x hx => continuousAt_diamondMid hx.1 hx.2) (1 - p) ⟨hq, by linarith⟩)
        (continuousAt_diamondMid hq (by linarith))
    have hB : HasDerivAt (fun q : ℝ => ∫ t in (1/2 : ℝ)..(1 - q), diamondMid α t)
        (-diamondMid α (1 - p)) p := HasDerivAt.comp_const_sub 1 p hv
    have hAB : HasDerivAt (fun q : ℝ => (∫ t in q..(1/2 : ℝ), diamondMid α t)
        + ∫ t in (1/2 : ℝ)..(1 - q), diamondMid α t)
        (-diamondMid α p + -diamondMid α (1 - p)) p := hA.add hB
    exact hAB.congr_of_eventuallyEq hsplit
  -- the boundary term
  have hT4 : HasDerivAt (fun q : ℝ => 1 / α * (q * (1 - q)) ^ (-α))
      (1 / α * ((1 - 2 * p) * -α * (p * (1 - p)) ^ (-α - 1))) p := by
    have hu : HasDerivAt (fun q : ℝ => q * (1 - q)) (1 - 2 * p) p := by
      have h := (hasDerivAt_id' p).mul ((hasDerivAt_id' p).const_sub 1)
      have heq : (1:ℝ) * (1 - p) + p * -1 = 1 - 2 * p := by ring
      rwa [heq] at h
    exact (hu.rpow_const (.inl (mul_pos hp hq).ne')).const_mul (1 / α)
  have h : HasDerivAt (Theta α) (2 * diamondNear α p + 2 * -diamondFar α p
      - (-diamondMid α p + -diamondMid α (1 - p))
      + 1 / α * ((1 - 2 * p) * -α * (p * (1 - p)) ^ (-α - 1))) p :=
    (((hT1.const_mul 2).add (hT2.const_mul 2)).sub hT3).add hT4
  have hD : 2 * diamondNear α p + 2 * -diamondFar α p
      - (-diamondMid α p + -diamondMid α (1 - p))
      + 1 / α * ((1 - 2 * p) * -α * (p * (1 - p)) ^ (-α - 1)) = 0 := by
    have e₁ : p ^ (-α) = p * p ^ (-α - 1) := by
      conv_lhs => rw [show -α = (1:ℝ) + (-α - 1) from by ring]
      rw [Real.rpow_add hp, Real.rpow_one]
    have e₂ : (1 - p) ^ (-α) = (1 - p) * (1 - p) ^ (-α - 1) := by
      conv_lhs => rw [show -α = (1:ℝ) + (-α - 1) from by ring]
      rw [Real.rpow_add hq, Real.rpow_one]
    have e₃ : (p * (1 - p)) ^ (-α - 1) = p ^ (-α - 1) * (1 - p) ^ (-α - 1) :=
      Real.mul_rpow hp.le hq.le
    have e₄ : (1:ℝ) - (1 - p) = p := by ring
    have key := diamond_cancel (α := α) (p := p) (A := p ^ (-α - 1))
      (B := (1 - p) ^ (-α - 1)) (E := (1 + p) ^ (-α - 1)) hα0.ne'
    simp only [diamondNear, diamondFar, diamondMid, e₄, e₁, e₂, e₃]
    linear_combination key
  rwa [hD] at h

/-- **The diamond profile is constant along each diamond.** For `1 < α < 2` the explicit function
`Theta α` does not depend on the position `p ∈ (0, 1/2]`; it always equals its value at the
midpoint `p = 1/2`. -/
theorem Theta_eq_Theta_half {α : ℝ} (hα : 1 < α) (hα' : α < 2) {p : ℝ}
    (hp : 0 < p) (hp' : p ≤ 1/2) : Theta α p = Theta α (1/2) := by
  refine (constant_of_has_deriv_right_zero (f := Theta α) (a := p) (b := 1/2) ?_ ?_ (1/2)
    (right_mem_Icc.mpr hp')).symm
  · intro x hx
    exact (hasDerivAt_Theta hα hα' (lt_of_lt_of_le hp hx.1)
      (lt_of_le_of_lt hx.2 (by norm_num))).continuousAt.continuousWithinAt
  · intro x hx
    exact (hasDerivAt_Theta hα hα' (lt_of_lt_of_le hp hx.1)
      (hx.2.trans (by norm_num))).hasDerivWithinAt

end CenteredMaximal.Fractional
