/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.BetaIntegral
public import CenteredMaximal.Fractional.DiamondConstancy

/-!
# The Gamma-quotient form of the diamond constant

`CenteredMaximal.Fractional.DiamondConstancy` shows that the diamond profile `Theta α` is constant
on `(0, 1)`. Its constant value is naturally produced as a combination of Beta and Gamma values,

`2 Β (1 - α, 2α) - Γ (-α) Γ (1 - α) Γ (2α) sin (2πα) / π`,

and this file rewrites that combination in the pole-free closed form

`2π Γ (2α) cos (πα/2) / (α Γ α ^ 2 sin (πα/2))`,

valid for `1 < α < 2`. It also records the Gamma recurrence that relates `Β (1 - α, 2α)`, whose
first argument is negative, to `Β (2 - α, 2α)`, whose two arguments are both positive and which is
therefore the one with a convergent type-2 Beta integral.

## Main results

* `two_betaFun_sub_betaFun`: the closed form of the constant.
* `betaFun_one_sub_left_rec`: `Β (1 - α, 2α) = ((α + 1) / (1 - α)) Β (2 - α, 2α)`.

## The computation

Both statements are Euler's reflection formula plus the functional equation. Writing
`Γ (α + 1) = α Γ α` and `Γ (1 - α) = π / (sin (πα) Γ α)` turns the first term into
`2π Γ (2α) / (α sin (πα) Γ α ^ 2)`. For the second, `Γ (1 - α) = -α Γ (-α)` eliminates `Γ (-α)`
and the doubling formula `sin (2πα) = 2 sin (πα) cos (πα)` cancels one power of `sin (πα)`,
leaving `-2π Γ (2α) cos (πα) / (α sin (πα) Γ α ^ 2)`. The difference therefore carries the
bracket `1 + cos (πα)`, and the half-angle identities `1 + cos θ = 2 cos (θ/2) ^ 2` and
`sin θ = 2 sin (θ/2) cos (θ/2)` at `θ = πα` replace `(1 + cos (πα)) / sin (πα)` by
`cos (πα/2) / sin (πα/2)`.

The closed form is deliberately written with `Γ (2α)` and the half-angle tangent rather than as
`Β (-α, 1 - α) = Γ (-α) Γ (1 - α) / Γ (1 - 2α)`: the latter has a pole at `α = 3/2`, where
`1 - 2α = -2`, whereas every factor above is finite and nonzero throughout `1 < α < 2`.

Note that `sin (πα) < 0` on this range, since `πα ∈ (π, 2π)`; the proofs only use that it is
nonzero, and the nonvanishing of `sin (πα/2)` and `cos (πα/2)` is then read off the doubling
formula rather than proved separately.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set

open scoped Real Topology

namespace CenteredMaximal.Fractional

/-- On `1 < α < 2` the argument `πα` lies in `(π, 2π)`, so `sin (πα)` is negative. -/
theorem sin_pi_mul_neg {α : ℝ} (hα : 1 < α) (hα' : α < 2) : Real.sin (π * α) < 0 := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have h : 0 < Real.sin (π * α - π) :=
    Real.sin_pos_of_pos_of_lt_pi
      (by nlinarith [mul_pos hπ (by linarith : (0:ℝ) < α - 1)])
      (by nlinarith [mul_pos hπ (by linarith : (0:ℝ) < 2 - α)])
  rw [Real.sin_sub_pi] at h
  linarith

/-- **The closed form of the diamond constant.** For `1 < α < 2`,
`2 Β (1 - α, 2α) - Γ (-α) Γ (1 - α) Γ (2α) sin (2πα) / π`
`  = 2π Γ (2α) cos (πα/2) / (α Γ α ^ 2 sin (πα/2))`.
Every factor on the right is finite on `1 < α < 2`, in contrast with the superficially simpler
`Γ (-α) Γ (1 - α) / Γ (1 - 2α)`, which has a pole at `α = 3/2`. -/
theorem two_betaFun_sub_betaFun {α : ℝ} (hα : 1 < α) (hα' : α < 2) :
    2 * betaFun (1 - α) (2*α) - Real.Gamma (-α) * Real.Gamma (1-α) * Real.Gamma (2*α)
        * Real.sin (2*π*α) / π
      = 2 * π * Real.Gamma (2*α) * Real.cos (π*α/2)
          / (α * Real.Gamma α ^ 2 * Real.sin (π*α/2)) := by
  have hα0 : (0:ℝ) < α := by linarith
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hG : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα0).ne'
  have hsin : Real.sin (π * α) ≠ 0 := (sin_pi_mul_neg hα hα').ne
  -- the two half-angle identities, and the nonvanishing they yield
  have hsin2 : Real.sin (π * α) = 2 * Real.sin (π * α / 2) * Real.cos (π * α / 2) := by
    conv_lhs => rw [show π * α = 2 * (π * α / 2) from by ring]
    rw [Real.sin_two_mul]
  have hcos2 : Real.cos (π * α) = 2 * Real.cos (π * α / 2) ^ 2 - 1 := by
    conv_lhs => rw [show π * α = 2 * (π * α / 2) from by ring]
    rw [Real.cos_two_mul]
  have hprod : 2 * Real.sin (π * α / 2) * Real.cos (π * α / 2) ≠ 0 := by
    rw [← hsin2]; exact hsin
  have hs2 : Real.sin (π * α / 2) ≠ 0 := by
    intro h; rw [h] at hprod; simp at hprod
  have hc2 : Real.cos (π * α / 2) ≠ 0 := by
    intro h; rw [h] at hprod; simp at hprod
  -- the functional equation and the reflection formula
  have hGa1 : Real.Gamma (α + 1) = α * Real.Gamma α := Real.Gamma_add_one hα0.ne'
  have hG1a : Real.Gamma (1 - α) = π / (Real.sin (π * α) * Real.Gamma α) := by
    rw [eq_div_iff (mul_ne_zero hsin hG),
      show Real.Gamma (1 - α) * (Real.sin (π * α) * Real.Gamma α)
        = Real.Gamma α * Real.Gamma (1 - α) * Real.sin (π * α) from by ring,
      Real.Gamma_mul_Gamma_one_sub α]
    field_simp
  have hGneg : Real.Gamma (-α) = Real.Gamma (1 - α) / (-α) := by
    have h := Real.Gamma_add_one (s := -α) (neg_ne_zero.mpr hα0.ne')
    rw [show -α + 1 = 1 - α from by ring] at h
    rw [h]
    field_simp
  -- the doubling formula for the sine in the second term
  have hsin2pi : Real.sin (2 * π * α) = 2 * Real.sin (π * α) * Real.cos (π * α) := by
    rw [show 2 * π * α = 2 * (π * α) from by ring, Real.sin_two_mul]
  have hbeta : betaFun (1 - α) (2*α)
      = Real.Gamma (1 - α) * Real.Gamma (2*α) / (α * Real.Gamma α) := by
    rw [betaFun, show (1:ℝ) - α + 2*α = α + 1 from by ring, hGa1]
  rw [hbeta, hGneg, hsin2pi, hG1a, hcos2, hsin2]
  field_simp
  ring

/-- The Gamma recurrence in the first argument: `Β (1 - α, 2α) = ((α + 1) / (1 - α)) Β (2 - α, 2α)`
for `1 < α < 2`. The point is that `2 - α` and `2α` are both positive on this range, so the right
factor is the one with a convergent type-2 Beta integral, namely
`∫_0^∞ t ^ (1 - α) (1 + t) ^ (-α - 2)`. -/
theorem betaFun_one_sub_left_rec {α : ℝ} (hα : 1 < α) (hα' : α < 2) :
    betaFun (1 - α) (2*α) = (α + 1) / (1 - α) * betaFun (2 - α) (2*α) := by
  have hα0 : (0:ℝ) < α := by linarith
  have hG : Real.Gamma α ≠ 0 := (Real.Gamma_pos_of_pos hα0).ne'
  have h1 : (1:ℝ) - α ≠ 0 := sub_ne_zero.mpr hα.ne
  have hp1 : (1:ℝ) + α ≠ 0 := ne_of_gt (by linarith)
  have hGa1 : Real.Gamma (α + 1) = α * Real.Gamma α := Real.Gamma_add_one hα0.ne'
  have hG2m : Real.Gamma (2 - α) = (1 - α) * Real.Gamma (1 - α) := by
    have h := Real.Gamma_add_one (s := 1 - α) h1
    rwa [show (1:ℝ) - α + 1 = 2 - α from by ring] at h
  have hG2p : Real.Gamma (2 + α) = (1 + α) * (α * Real.Gamma α) := by
    have h := Real.Gamma_add_one (s := 1 + α) hp1
    rw [show (1:ℝ) + α + 1 = 2 + α from by ring] at h
    rw [h, show (1:ℝ) + α = α + 1 from by ring, hGa1]
  rw [betaFun, betaFun, show (1:ℝ) - α + 2*α = α + 1 from by ring,
    show (2:ℝ) - α + 2*α = 2 + α from by ring, hGa1, hG2m, hG2p]
  field_simp
  ring

/-! ### The Beta recurrence on the symmetric interval `[p, 1 - p]` -/

/-- The Beta kernel `t ↦ t ^ x * (1 - t) ^ y` is continuous at every point of `(0, 1)`. -/
theorem continuousAt_betaKernel {x y t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    ContinuousAt (fun s : ℝ => s ^ x * (1 - s) ^ y) t :=
  (Real.continuousAt_rpow_const t x (.inl ht.ne')).mul
    (ContinuousAt.rpow_const (f := fun s : ℝ => 1 - s) (by fun_prop)
      (.inl (by linarith : (0:ℝ) < 1 - t).ne'))

/-- On `[p, 1 - p]` with `0 < p < 1/2` the Beta kernel is continuous, hence interval integrable,
for *every* pair of exponents: the interval avoids both singular endpoints. -/
theorem intervalIntegrable_betaKernel {x y p : ℝ} (hp : 0 < p) (hp' : p < 1/2) :
    IntervalIntegrable (fun t : ℝ => t ^ x * (1 - t) ^ y) volume p (1 - p) := by
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  rw [uIcc_of_le (by linarith : p ≤ 1 - p)] at ht
  exact (continuousAt_betaKernel (by linarith [ht.1]) (by linarith [ht.2])).continuousWithinAt

/-- The derivative of `t ↦ t ^ a * (1 - t) ^ b` at a point of `(0, 1)`. -/
theorem hasDerivAt_betaKernel {a b t : ℝ} (ht : 0 < t) (ht' : t < 1) :
    HasDerivAt (fun s : ℝ => s ^ a * (1 - s) ^ b)
      (a * (t ^ (a - 1) * (1 - t) ^ b) - b * (t ^ a * (1 - t) ^ (b - 1))) t := by
  have h₁ : HasDerivAt (fun s : ℝ => s ^ a) (a * t ^ (a - 1)) t :=
    Real.hasDerivAt_rpow_const (.inl ht.ne')
  have h₂ : HasDerivAt (fun s : ℝ => (1 - s) ^ b) (-1 * b * (1 - t) ^ (b - 1)) t :=
    HasDerivAt.rpow_const (f := fun s : ℝ => 1 - s) ((hasDerivAt_id' t).const_sub 1)
      (.inl (by linarith : (0:ℝ) < 1 - t).ne')
  have heq : a * t ^ (a - 1) * (1 - t) ^ b + t ^ a * (-1 * b * (1 - t) ^ (b - 1))
      = a * (t ^ (a - 1) * (1 - t) ^ b) - b * (t ^ a * (1 - t) ^ (b - 1)) := by ring
  have h := h₁.mul h₂
  rwa [heq] at h

/-- The fundamental theorem of calculus for `t ↦ t ^ a * (1 - t) ^ b` on `[p, 1 - p]`.  Both
endpoints are interior to `(0, 1)`, so this is an honest integral of a continuous function and no
convergence hypothesis on `a` or `b` is needed. -/
theorem integral_betaKernel_deriv {a b p : ℝ} (hp : 0 < p) (hp' : p < 1/2) :
    a * (∫ t in p..(1 - p), t ^ (a - 1) * (1 - t) ^ b)
        - b * (∫ t in p..(1 - p), t ^ a * (1 - t) ^ (b - 1))
      = (1 - p) ^ a * p ^ b - p ^ a * (1 - p) ^ b := by
  have hle : p ≤ 1 - p := by linarith
  have hA : IntervalIntegrable (fun t : ℝ => a * (t ^ (a - 1) * (1 - t) ^ b)) volume p (1 - p) :=
    (intervalIntegrable_betaKernel hp hp').const_mul a
  have hB : IntervalIntegrable (fun t : ℝ => b * (t ^ a * (1 - t) ^ (b - 1))) volume p (1 - p) :=
    (intervalIntegrable_betaKernel hp hp').const_mul b
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => s ^ a * (1 - s) ^ b)
    (f' := fun t : ℝ => a * (t ^ (a - 1) * (1 - t) ^ b) - b * (t ^ a * (1 - t) ^ (b - 1)))
    (fun t ht => by
      rw [uIcc_of_le hle] at ht
      exact hasDerivAt_betaKernel (by linarith [ht.1]) (by linarith [ht.2])) (hA.sub hB)
  rw [intervalIntegral.integral_sub hA hB, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h
  rw [h, sub_sub_cancel]

/-- The trivial splitting `t ^ (a-1) (1-t) ^ (b-1) = t ^ (a-1) (1-t) ^ b + t ^ a (1-t) ^ (b-1)`,
which is `1 = (1 - t) + t` after factoring. -/
theorem integral_betaKernel_split {a b p : ℝ} (hp : 0 < p) (hp' : p < 1/2) :
    (∫ t in p..(1 - p), t ^ (a - 1) * (1 - t) ^ (b - 1))
      = (∫ t in p..(1 - p), t ^ (a - 1) * (1 - t) ^ b)
        + ∫ t in p..(1 - p), t ^ a * (1 - t) ^ (b - 1) := by
  rw [← intervalIntegral.integral_add (intervalIntegrable_betaKernel hp hp')
    (intervalIntegrable_betaKernel hp hp')]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le (by linarith : p ≤ 1 - p)] at ht
  have ht0 : (0:ℝ) < t := by linarith [ht.1]
  have ht1 : (0:ℝ) < 1 - t := by linarith [ht.2]
  have e₁ : (1 - t) ^ b = (1 - t) ^ (b - 1) * (1 - t) := by
    conv_lhs => rw [show b = b - 1 + 1 from by ring]
    rw [Real.rpow_add ht1, Real.rpow_one]
  have e₂ : t ^ a = t ^ (a - 1) * t := by
    conv_lhs => rw [show a = a - 1 + 1 from by ring]
    rw [Real.rpow_add ht0, Real.rpow_one]
  simp only [e₁, e₂]
  ring

/-- One step of the Beta recurrence raising the **first** exponent:
`a Β(a, b) - (a + b) Β(a + 1, b) = [t ^ a (1 - t) ^ b]` evaluated at the endpoints. -/
theorem betaStep_left {a b p : ℝ} (hp : 0 < p) (hp' : p < 1/2) :
    a * (∫ t in p..(1 - p), t ^ (a - 1) * (1 - t) ^ (b - 1))
        - (a + b) * (∫ t in p..(1 - p), t ^ a * (1 - t) ^ (b - 1))
      = (1 - p) ^ a * p ^ b - p ^ a * (1 - p) ^ b := by
  linear_combination integral_betaKernel_deriv (a := a) (b := b) hp hp'
    + a * integral_betaKernel_split (a := a) (b := b) hp hp'

/-- One step of the Beta recurrence raising the **second** exponent:
`(a + b) Β(a, b + 1) - b Β(a, b) = [t ^ a (1 - t) ^ b]` evaluated at the endpoints. -/
theorem betaStep_right {a b p : ℝ} (hp : 0 < p) (hp' : p < 1/2) :
    (a + b) * (∫ t in p..(1 - p), t ^ (a - 1) * (1 - t) ^ b)
        - b * (∫ t in p..(1 - p), t ^ (a - 1) * (1 - t) ^ (b - 1))
      = (1 - p) ^ a * p ^ b - p ^ a * (1 - p) ^ b := by
  linear_combination integral_betaKernel_deriv (a := a) (b := b) hp hp'
    - b * integral_betaKernel_split (a := a) (b := b) hp hp'

/-- **Three Beta steps regularise the middle integral.**  For `1 < α < 2` the exponents of
`diamondMid α`, namely `(1 - α, -α)`, are both too small for convergence; raising the first once
and the second twice reaches `(2 - α, 2 - α)`, which is convergent on all of `(0, 1)`.  The
identity below is exact for every `p ∈ (0, 1/2)` and is stated in cleared form, with no division
by `α (1 - α) ^ 2`. -/
theorem integral_diamondMid_chain {α p : ℝ} (hp : 0 < p) (hp' : p < 1/2) :
    α * (1 - α) ^ 2 * (∫ t in p..(1 - p), diamondMid α t)
      = α * (1 - α) * ((1 - p) ^ (1 - α) * p ^ (-α) - p ^ (1 - α) * (1 - p) ^ (-α))
        + (1 - 2*α) * (1 - α) * ((1 - p) ^ (2 - α) * p ^ (-α) - p ^ (2 - α) * (1 - p) ^ (-α))
        + (1 - 2*α) * (2 - 2*α) * ((1 - p) ^ (2 - α) * p ^ (1 - α)
            - p ^ (2 - α) * (1 - p) ^ (1 - α))
        - (1 - 2*α) * (2 - 2*α) * (3 - 2*α)
            * (∫ t in p..(1 - p), t ^ (1 - α) * (1 - t) ^ (1 - α)) := by
  have e₁ := betaStep_left (a := 1 - α) (b := -α) hp hp'
  have e₂ := betaStep_right (a := 2 - α) (b := -α) hp hp'
  have e₃ := betaStep_right (a := 2 - α) (b := 1 - α) hp hp'
  simp only [show (1:ℝ) - α - 1 = -α from by ring, show (2:ℝ) - α - 1 = 1 - α from by ring,
    show (1:ℝ) - α + -α = 1 - 2*α from by ring, show (2:ℝ) - α + -α = 2 - 2*α from by ring,
    show (2:ℝ) - α + (1 - α) = 3 - 2*α from by ring] at e₁ e₂ e₃
  simp only [diamondMid]
  linear_combination (α * (1 - α)) * e₁ + ((1 - 2*α) * (1 - α)) * e₂
    + ((1 - 2*α) * (2 - 2*α)) * e₃

/-! ### Regularising the far integral -/

/-- The far Beta kernel `t ↦ t ^ x * (1 + t) ^ y` is continuous at every point of `(0, ∞)`. -/
theorem continuousAt_farKernel {x y t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun s : ℝ => s ^ x * (1 + s) ^ y) t :=
  (Real.continuousAt_rpow_const t x (.inl ht.ne')).mul
    (ContinuousAt.rpow_const (f := fun s : ℝ => 1 + s) (by fun_prop)
      (.inl (by linarith : (0:ℝ) < 1 + t).ne'))

theorem intervalIntegrable_farKernel {x y a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ => t ^ x * (1 + t) ^ y) volume a b := by
  refine ContinuousOn.intervalIntegrable fun t ht => ?_
  rw [mem_uIcc] at ht
  have h0 : 0 < t := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
  exact (continuousAt_farKernel h0).continuousWithinAt

/-- The regularised far kernel `t ^ (1 - α) (1 + t) ^ (-α - 2)` is the type-2 Beta integrand with
parameters `(2 - α, 2α)`, both positive for `1 < α < 2`, so it is integrable on all of `(0, ∞)`. -/
theorem integrableOn_farKernelReg {α : ℝ} (hα : 1 < α) (hα' : α < 2) :
    IntegrableOn (fun t : ℝ => t ^ (1 - α) * (1 + t) ^ (-α - 2)) (Ioi 0) := by
  have h := integrableOn_Ioi_rpow_mul_one_add_rpow (a := 2 - α) (b := 2*α)
    (by linarith) (by linarith)
  rwa [show (2:ℝ) - α - 1 = 1 - α from by ring,
    show -(2 - α) - 2*α = -α - 2 from by ring] at h

/-- The derivative of `t ↦ t ^ (1 - α) * (1 + t) ^ (-α - 1)`: exactly the combination of
`diamondFar α` and the convergent kernel `t ^ (1 - α) (1 + t) ^ (-α - 2)` that the integration by
parts produces. -/
theorem hasDerivAt_farKernel {α t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => s ^ (1 - α) * (1 + s) ^ (-α - 1))
      ((1 - α) * diamondFar α t - (α + 1) * (t ^ (1 - α) * (1 + t) ^ (-α - 2))) t := by
  have h₁ : HasDerivAt (fun s : ℝ => s ^ (1 - α)) ((1 - α) * t ^ (1 - α - 1)) t :=
    Real.hasDerivAt_rpow_const (.inl ht.ne')
  have h₂ : HasDerivAt (fun s : ℝ => (1 + s) ^ (-α - 1))
      (1 * (-α - 1) * (1 + t) ^ (-α - 1 - 1)) t :=
    HasDerivAt.rpow_const (f := fun s : ℝ => 1 + s) ((hasDerivAt_id' t).const_add 1)
      (.inl (by linarith : (0:ℝ) < 1 + t).ne')
  have heq : (1 - α) * t ^ (1 - α - 1) * (1 + t) ^ (-α - 1)
        + t ^ (1 - α) * (1 * (-α - 1) * (1 + t) ^ (-α - 1 - 1))
      = (1 - α) * diamondFar α t - (α + 1) * (t ^ (1 - α) * (1 + t) ^ (-α - 2)) := by
    simp only [diamondFar, show (1:ℝ) - α - 1 = -α from by ring,
      show -α - 1 - 1 = -α - 2 from by ring]
    ring
  have h := h₁.mul h₂
  rwa [heq] at h

/-- The by-parts identity on a bounded interval `[p, R]`. -/
theorem integral_farKernel_deriv {α p R : ℝ} (hp : 0 < p) (hpR : p ≤ R) :
    (1 - α) * (∫ t in p..R, diamondFar α t)
        - (α + 1) * (∫ t in p..R, t ^ (1 - α) * (1 + t) ^ (-α - 2))
      = R ^ (1 - α) * (1 + R) ^ (-α - 1) - p ^ (1 - α) * (1 + p) ^ (-α - 1) := by
  have hR : (0:ℝ) < R := lt_of_lt_of_le hp hpR
  have hA : IntervalIntegrable (fun t : ℝ => (1 - α) * diamondFar α t) volume p R :=
    (intervalIntegrable_diamondFar hp hR).const_mul _
  have hB : IntervalIntegrable (fun t : ℝ => (α + 1) * (t ^ (1 - α) * (1 + t) ^ (-α - 2)))
      volume p R := (intervalIntegrable_farKernel hp hR).const_mul _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => s ^ (1 - α) * (1 + s) ^ (-α - 1))
    (f' := fun t : ℝ => (1 - α) * diamondFar α t
      - (α + 1) * (t ^ (1 - α) * (1 + t) ^ (-α - 2)))
    (fun t ht => by
      rw [uIcc_of_le hpR] at ht
      exact hasDerivAt_farKernel (by linarith [ht.1])) (hA.sub hB)
  rwa [intervalIntegral.integral_sub hA hB, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at h

/-- The by-parts boundary term dies at infinity: its exponent is `1 - α - α - 1 = -2α < 0`. -/
theorem tendsto_farKernel_atTop {α : ℝ} (hα : 1 < α) :
    Tendsto (fun R : ℝ => R ^ (1 - α) * (1 + R) ^ (-α - 1)) atTop (𝓝 0) := by
  have hg : Tendsto (fun R : ℝ => (1 + R) ^ (-α - 1)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (y := α + 1) (by linarith)).comp
      (tendsto_atTop_add_const_left atTop (1:ℝ) tendsto_id)
    simpa [Function.comp_def, show -(α + 1) = -α - 1 from by ring] using h
  refine squeeze_zero' ?_ ?_ hg
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    exact (mul_pos (Real.rpow_pos_of_pos (by linarith) _)
      (Real.rpow_pos_of_pos (by linarith) _)).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    calc R ^ (1 - α) * (1 + R) ^ (-α - 1)
        ≤ 1 * (1 + R) ^ (-α - 1) :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_one_of_one_le_of_nonpos hR (by linarith))
            (Real.rpow_pos_of_pos (by linarith) _).le
      _ = (1 + R) ^ (-α - 1) := one_mul _

/-- **Integration by parts on the half line.**  For `1 < α < 2` and `0 < p < 1`,
`(1 - α) ∫_p^∞ t^{-α}(1+t)^{-α-1} - (α + 1) ∫_p^∞ t^{1-α}(1+t)^{-α-2} = -p^{1-α}(1+p)^{-α-1}`.
The value at infinity contributes nothing, so the only boundary term is the one at `p`. -/
theorem integral_Ioi_diamondFar_chain {α p : ℝ} (hα : 1 < α) (hα' : α < 2) (hp : 0 < p)
    (hp' : p < 1) :
    (1 - α) * (∫ t in Ioi p, diamondFar α t)
        - (α + 1) * (∫ t in Ioi p, t ^ (1 - α) * (1 + t) ^ (-α - 2))
      = -(p ^ (1 - α) * (1 + p) ^ (-α - 1)) := by
  have hfar : IntegrableOn (fun t : ℝ => diamondFar α t) (Ioi p) :=
    integrableOn_diamondFar (by linarith) hp hp'
  have hreg : IntegrableOn (fun t : ℝ => t ^ (1 - α) * (1 + t) ^ (-α - 2)) (Ioi p) :=
    (integrableOn_farKernelReg hα hα').mono_set (Ioi_subset_Ioi hp.le)
  have t₁ : Tendsto (fun R : ℝ => ∫ t in p..R, diamondFar α t) atTop
      (𝓝 (∫ t in Ioi p, diamondFar α t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi p hfar tendsto_id
  have t₂ : Tendsto (fun R : ℝ => ∫ t in p..R, t ^ (1 - α) * (1 + t) ^ (-α - 2)) atTop
      (𝓝 (∫ t in Ioi p, t ^ (1 - α) * (1 + t) ^ (-α - 2))) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi p hreg tendsto_id
  have key := (t₁.const_mul (1 - α)).sub (t₂.const_mul (α + 1))
  have key2 := (tendsto_farKernel_atTop hα).sub_const (p ^ (1 - α) * (1 + p) ^ (-α - 1))
  have heq : ∀ᶠ R : ℝ in atTop,
      R ^ (1 - α) * (1 + R) ^ (-α - 1) - p ^ (1 - α) * (1 + p) ^ (-α - 1)
        = (1 - α) * (∫ t in p..R, diamondFar α t)
          - (α + 1) * (∫ t in p..R, t ^ (1 - α) * (1 + t) ^ (-α - 2)) := by
    filter_upwards [eventually_ge_atTop p] with R hR
    exact (integral_farKernel_deriv hp hR).symm
  have h := tendsto_nhds_unique key (key2.congr' heq)
  rw [h]
  ring

/-! ### The regularised form of the diamond profile -/

/-- The remainder `N α p = -α (1+p)^{-α-1} + (1-p)^{-α} (α + (1-2α) p (3-2p))` left behind by the
two regularisations.  It vanishes at `p = 0`, and `diamondRem_zero` is precisely the statement
that the `p^{-α}` and `p^{1-α}` divergences of the three singular terms of `Theta α` cancel. -/
def diamondRem (α p : ℝ) : ℝ :=
  -α * (1 + p) ^ (-α - 1) + (1 - p) ^ (-α) * (α + (1 - 2*α) * p * (3 - 2*p))

@[simp]
theorem diamondRem_zero (α : ℝ) : diamondRem α 0 = 0 := by
  simp only [diamondRem, add_zero, sub_zero, Real.one_rpow, mul_zero, zero_mul]
  ring

/-- **The diamond profile, regularised.**  For `1 < α < 2` and `0 < p < 1/2` the four terms of
`Theta α p`, three of which blow up as `p → 0⁺`, rearrange into a sum of three convergent integrals
and one explicit remainder `2 p^{1-α} N α p / (α (1 - α))`.  The far integral has been integrated
by parts once (`integral_Ioi_diamondFar_chain`) and the middle integral pushed through three Beta
steps (`integral_diamondMid_chain`); what is left over of the boundary terms, together with the
`(p(1-p))^{-α}` term, is the remainder. -/
theorem Theta_eq_regularised {α p : ℝ} (hα : 1 < α) (hα' : α < 2) (hp : 0 < p) (hp' : p < 1/2) :
    Theta α p = 2 * (∫ t in (0:ℝ)..p, diamondNear α t)
      + 2 * (α + 1) / (1 - α) * (∫ t in Ioi p, t ^ (1 - α) * (1 + t) ^ (-α - 2))
      + 2 * (1 - 2*α) * (3 - 2*α) / (α * (1 - α))
          * (∫ t in p..(1 - p), t ^ (1 - α) * (1 - t) ^ (1 - α))
      + 2 * p ^ (1 - α) * diamondRem α p / (α * (1 - α)) := by
  have hα0 : (0:ℝ) < α := by linarith
  have hq : (0:ℝ) < 1 - p := by linarith
  have h1α : (1:ℝ) - α ≠ 0 := sub_ne_zero.mpr hα.ne
  have hF : (∫ t in Ioi p, diamondFar α t)
      = ((α + 1) * (∫ t in Ioi p, t ^ (1 - α) * (1 + t) ^ (-α - 2))
          - p ^ (1 - α) * (1 + p) ^ (-α - 1)) / (1 - α) := by
    rw [eq_div_iff h1α]
    linear_combination integral_Ioi_diamondFar_chain hα hα' hp (by linarith)
  have hM : (∫ t in p..(1 - p), diamondMid α t)
      = (α * (1 - α) * ((1 - p) ^ (1 - α) * p ^ (-α) - p ^ (1 - α) * (1 - p) ^ (-α))
          + (1 - 2*α) * (1 - α) * ((1 - p) ^ (2 - α) * p ^ (-α) - p ^ (2 - α) * (1 - p) ^ (-α))
          + (1 - 2*α) * (2 - 2*α) * ((1 - p) ^ (2 - α) * p ^ (1 - α)
              - p ^ (2 - α) * (1 - p) ^ (1 - α))
          - (1 - 2*α) * (2 - 2*α) * (3 - 2*α)
              * (∫ t in p..(1 - p), t ^ (1 - α) * (1 - t) ^ (1 - α)))
        / (α * (1 - α) ^ 2) := by
    rw [eq_div_iff (mul_ne_zero hα0.ne' (pow_ne_zero 2 h1α))]
    linear_combination integral_diamondMid_chain (α := α) hp hp'
  have e₁ : p ^ (1 - α) = p * p ^ (-α) := by
    rw [show (1:ℝ) - α = 1 + -α from by ring, Real.rpow_add hp, Real.rpow_one]
  have e₂ : p ^ (2 - α) = p * (p * p ^ (-α)) := by
    rw [show (2:ℝ) - α = 1 + (1 + -α) from by ring, Real.rpow_add hp, Real.rpow_one,
      Real.rpow_add hp, Real.rpow_one]
  have f₁ : (1 - p) ^ (1 - α) = (1 - p) * (1 - p) ^ (-α) := by
    rw [show (1:ℝ) - α = 1 + -α from by ring, Real.rpow_add hq, Real.rpow_one]
  have f₂ : (1 - p) ^ (2 - α) = (1 - p) * ((1 - p) * (1 - p) ^ (-α)) := by
    rw [show (2:ℝ) - α = 1 + (1 + -α) from by ring, Real.rpow_add hq, Real.rpow_one,
      Real.rpow_add hq, Real.rpow_one]
  have g₁ : (p * (1 - p)) ^ (-α) = p ^ (-α) * (1 - p) ^ (-α) := Real.mul_rpow hp.le hq.le
  simp only [Theta, diamondRem]
  rw [hF, hM, g₁, e₂, f₂, e₁, f₁]
  field_simp
  ring

end CenteredMaximal.Fractional

end

end
