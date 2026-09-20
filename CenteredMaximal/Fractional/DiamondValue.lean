/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.BetaIntegral
public import CenteredMaximal.Fractional.DiamondConstancy

/-!
# The value of the diamond constant

`CenteredMaximal.Fractional.DiamondConstancy` shows that the diamond profile `Theta α` has
derivative `0` throughout `(0, 1)`, so it is constant there, but says nothing about the constant.
This file computes it: for `1 < α < 2`,

`Θ α (1/2) = 2π Γ (2α) cos (πα/2) / (α Γ α ^ 2 sin (πα/2))`.

## Main results

* `two_betaFun_sub_betaFun`: the pure Gamma identity
  `2 Β (1 - α, 2α) - Γ (-α) Γ (1 - α) Γ (2α) sin (2πα) / π`
  `  = 2π Γ (2α) cos (πα/2) / (α Γ α ^ 2 sin (πα/2))`.
* `betaFun_one_sub_left_rec`: `Β (1 - α, 2α) = ((α + 1) / (1 - α)) Β (2 - α, 2α)`, which trades the
  negative first argument for two positive ones.
* `betaStep_left`, `betaStep_right`: the two exact Beta recurrences on `[p, 1 - p]`.
* `integral_diamondMid_chain`: three Beta steps carry the middle integrand `t^{-α}(1-t)^{-α-1}`,
  divergent at both ends, to `t^{1-α}(1-t)^{1-α}`, convergent at both.
* `integral_Ioi_diamondFar_chain`: one integration by parts on the half line carries
  `t^{-α}(1+t)^{-α-1}` to `t^{1-α}(1+t)^{-α-2}`.
* `Theta_eq_regularised`: the resulting exact rewriting of `Theta α p` on `(0, 1/2)`.
* `Gamma_mul_Gamma_four_sub_two_mul`, `betaFun_two_sub_self_eq`, `regularised_limit`: the Gamma
  bookkeeping identifying the limit.
* `Theta_half_eq`: the value of the constant.

## The Gamma identity

`two_betaFun_sub_betaFun` is Euler's reflection formula plus the functional equation. Writing
`Γ (α + 1) = α Γ α` and `Γ (1 - α) = π / (sin (πα) Γ α)` turns the first term into
`2π Γ (2α) / (α sin (πα) Γ α ^ 2)`. For the second, `Γ (1 - α) = -α Γ (-α)` eliminates `Γ (-α)`
and the doubling formula `sin (2πα) = 2 sin (πα) cos (πα)` cancels one power of `sin (πα)`,
leaving `-2π Γ (2α) cos (πα) / (α sin (πα) Γ α ^ 2)`. The difference therefore carries the
bracket `1 + cos (πα)`, and the half-angle identities `1 + cos θ = 2 cos (θ/2) ^ 2` and
`sin θ = 2 sin (θ/2) cos (θ/2)` at `θ = πα` replace `(1 + cos (πα)) / sin (πα)` by
`cos (πα/2) / sin (πα/2)`.

The closed form is deliberately written with `Γ (2α)` and the half-angle tangent rather than as
`Β (-α, 1 - α) = Γ (-α) Γ (1 - α) / Γ (1 - 2α)`: the latter has a pole at `α = 3/2`, where
`1 - 2α = -2`, whereas every factor above is finite and nonzero throughout `1 < α < 2`. Note that
`sin (πα) < 0` on this range, since `πα ∈ (π, 2π)`; the proofs use only that it is nonzero, and the
nonvanishing of `sin (πα/2)` and `cos (πα/2)` is then read off the doubling formula.

## Evaluating the profile

`Theta α` is already known to be constant, so it suffices to identify `lim_{p → 0⁺} Θ α p`. Three
of its four terms diverge, so they are first rewritten by *exact* identities valid for every
`p ∈ (0, 1/2)`, after which every remaining piece has a limit that can be taken term by term.

The engine in both cases is the fundamental theorem of calculus on a compact interval strictly
inside the domain, where the integrands are continuous and no convergence hypothesis is needed.
Applied to `t ↦ t^a (1-t)^b` on `[p, 1-p]` it gives `a Β(a,b) - (a+b) Β(a+1,b)` and
`(a+b) Β(a,b+1) - b Β(a,b)` in terms of the endpoint values, which are `betaStep_left` and
`betaStep_right`; chaining one step in the first argument and two in the second sends `(1 - α, -α)`
to `(2 - α, 2 - α)`, both positive. Applied to `t ↦ t^{1-α}(1+t)^{-α-1}` on `[p, R]` and letting
`R → ∞` — the value at infinity has exponent `-2α < 0` and so vanishes — it gives the half-line
integration by parts. Mathlib has no by-parts lemma for a half line with a singular endpoint, but
none is needed on this route.

What is left of the boundary terms, together with `(1/α)(p(1-p))^{-α}`, is the remainder
`2 p^{1-α} N α p / (α (1 - α))` with `N = diamondRem`. Individually the pieces diverge at the
orders `p^{-α}` and `p^{1-α}`; that they cancel is exactly `diamondRem_zero`, `N α 0 = 0`. Since
`N` is also differentiable at `0`, the quotient `N α p / p` stays bounded, and the remainder is
`p^{2-α}` times a bounded factor, hence tends to `0` because `α < 2`. No asymptotic expansion and
no mean value estimate is needed.

The two surviving integrals tend to `Β (2 - α, 2α)` and `Β (2 - α, 2 - α)` by continuity of a
primitive, and the Gamma bookkeeping that assembles them uses the reflection formula in the
pole-free form `Γ (2α) Γ (4 - 2α) sin (2πα) = 2π (1 - 2α)(3 - 2α)(1 - α)`. That identity holds
throughout `1 < α < 2`, but its proof splits at `α = 3/2`: there both sides vanish, while the
recurrence `Γ (4 - 2α) = (3 - 2α) Γ (3 - 2α)` fails because `Γ (1 - 2α) = Γ (-2)` sits on a pole.
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

/-! ### From the regularised Beta values back to Gamma -/

theorem Gamma_one_sub_ne_zero {α : ℝ} (hα : 1 < α) (hα' : α < 2) : Real.Gamma (1 - α) ≠ 0 := by
  have hrefl := Real.Gamma_mul_Gamma_one_sub α
  have hne : π / Real.sin (π * α) ≠ 0 :=
    div_ne_zero Real.pi_ne_zero (sin_pi_mul_neg hα hα').ne
  intro h
  rw [h, mul_zero] at hrefl
  exact hne hrefl.symm

/-- On `1 < α < 2` the argument `2πα` lies in `(2π, 4π)`, whose only zero of the sine is `3π`; so
`sin (2πα) = 0` forces `α = 3/2`. -/
theorem sin_two_pi_mul_ne_zero {α : ℝ} (hα : 1 < α) (hα' : α < 2) (h32 : α ≠ 3/2) :
    Real.sin (2*π*α) ≠ 0 := by
  have hπ : (0:ℝ) < π := Real.pi_pos
  have key : Real.sin (2*π*α) = -Real.sin (2*π*α - 3*π) := by
    conv_lhs => rw [show 2*π*α = (2*π*α - 3*π) + π + 2*π from by ring]
    rw [Real.sin_add_two_pi, Real.sin_add_pi]
  intro h
  rw [key, neg_eq_zero] at h
  have hy₁ : -π < 2*π*α - 3*π := by
    nlinarith [mul_pos hπ (by linarith : (0:ℝ) < α - 1)]
  have hy₂ : 2*π*α - 3*π < π := by
    nlinarith [mul_pos hπ (by linarith : (0:ℝ) < 2 - α)]
  have hz := (Real.sin_eq_zero_iff_of_lt_of_lt hy₁ hy₂).mp h
  have hz' : π * (2*α - 3) = 0 := by linear_combination hz
  rcases mul_eq_zero.mp hz' with h' | h'
  · exact absurd h' Real.pi_ne_zero
  · exact h32 (by linarith)

/-- The reflection formula in the pole-free form needed here:
`Γ (2α) Γ (4 - 2α) sin (2πα) = 2π (1 - 2α)(3 - 2α)(1 - α)` for `1 < α < 2`.  At `α = 3/2` both
sides vanish — the left because `sin (3π) = 0`, the right because of the factor `3 - 2α` — and that
case has to be separated out, because there `Γ (1 - 2α) = Γ (-2)` sits on a pole and the Gamma
recurrence `Γ (4 - 2α) = (3 - 2α) Γ (3 - 2α)` fails. -/
theorem Gamma_mul_Gamma_four_sub_two_mul {α : ℝ} (hα : 1 < α) (hα' : α < 2) :
    Real.Gamma (2*α) * Real.Gamma (4 - 2*α) * Real.sin (2*π*α)
      = 2 * π * ((1 - 2*α) * (3 - 2*α) * (1 - α)) := by
  by_cases h32 : α = 3/2
  · subst h32
    have hs : Real.sin (2*π*(3/2 : ℝ)) = 0 := by
      rw [show 2*π*(3/2 : ℝ) = π + 2*π from by ring, Real.sin_add_two_pi, Real.sin_pi]
    rw [hs]
    ring
  · have h₁ : (1:ℝ) - 2*α ≠ 0 := by intro h; linarith
    have h₂ : (2:ℝ) - 2*α ≠ 0 := by intro h; linarith
    have h₃ : (3:ℝ) - 2*α ≠ 0 := fun h => h32 (by linarith)
    have hsin := sin_two_pi_mul_ne_zero hα hα' h32
    have a₁ := Real.Gamma_add_one (s := 1 - 2*α) h₁
    have a₂ := Real.Gamma_add_one (s := 2 - 2*α) h₂
    have a₃ := Real.Gamma_add_one (s := 3 - 2*α) h₃
    rw [show (1:ℝ) - 2*α + 1 = 2 - 2*α from by ring] at a₁
    rw [show (2:ℝ) - 2*α + 1 = 3 - 2*α from by ring] at a₂
    rw [show (3:ℝ) - 2*α + 1 = 4 - 2*α from by ring] at a₃
    have hrefl : Real.Gamma (2*α) * Real.Gamma (1 - 2*α) = π / Real.sin (2*π*α) := by
      have h := Real.Gamma_mul_Gamma_one_sub (2*α)
      rwa [show π * (2*α) = 2*π*α from by ring] at h
    have hrefl' : Real.Gamma (2*α) * Real.Gamma (1 - 2*α) * Real.sin (2*π*α) = π := by
      rw [hrefl]
      exact div_mul_cancel₀ π hsin
    rw [a₃, a₂, a₁]
    linear_combination ((3 - 2*α) * (2 - 2*α) * (1 - 2*α)) * hrefl'

/-- The regularised middle Beta value `Β (2 - α, 2 - α)`, with the coefficient produced by the
three Beta steps, is exactly the second term of the diamond constant. -/
theorem betaFun_two_sub_self_eq {α : ℝ} (hα : 1 < α) (hα' : α < 2) :
    2 * (1 - 2*α) * (3 - 2*α) / (α * (1 - α)) * betaFun (2 - α) (2 - α)
      = -(Real.Gamma (-α) * Real.Gamma (1-α) * Real.Gamma (2*α) * Real.sin (2*π*α) / π) := by
  have hα0 : (0:ℝ) < α := by linarith
  have h1α : (1:ℝ) - α ≠ 0 := sub_ne_zero.mpr hα.ne
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have hG1a : Real.Gamma (1 - α) ≠ 0 := Gamma_one_sub_ne_zero hα hα'
  have hG4 : Real.Gamma (4 - 2*α) ≠ 0 := (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hG2m : Real.Gamma (2 - α) = (1 - α) * Real.Gamma (1 - α) := by
    have h := Real.Gamma_add_one (s := 1 - α) h1α
    rwa [show (1:ℝ) - α + 1 = 2 - α from by ring] at h
  have hGneg : Real.Gamma (-α) = Real.Gamma (1 - α) / (-α) := by
    have h := Real.Gamma_add_one (s := -α) (neg_ne_zero.mpr hα0.ne')
    rw [show -α + 1 = 1 - α from by ring] at h
    rw [h]
    field_simp
  have hL : 2 * (1 - 2*α) * (3 - 2*α) / (α * (1 - α)) * betaFun (2 - α) (2 - α)
      = 2 * (1 - 2*α) * (3 - 2*α) * (1 - α) * Real.Gamma (1 - α) ^ 2
        / (α * Real.Gamma (4 - 2*α)) := by
    rw [betaFun, show (2:ℝ) - α + (2 - α) = 4 - 2*α from by ring, hG2m]
    field_simp
  have hR : -(Real.Gamma (-α) * Real.Gamma (1-α) * Real.Gamma (2*α) * Real.sin (2*π*α) / π)
      = Real.Gamma (1 - α) ^ 2 * Real.Gamma (2*α) * Real.sin (2*π*α) / (α * π) := by
    rw [hGneg]
    field_simp
  rw [hL, hR, div_eq_div_iff (mul_ne_zero hα0.ne' hG4) (mul_ne_zero hα0.ne' hπ)]
  linear_combination (-(α * Real.Gamma (1 - α) ^ 2)) * Gamma_mul_Gamma_four_sub_two_mul hα hα'

/-- The two regularised Beta values combine into the closed form of the diamond constant. -/
theorem regularised_limit {α : ℝ} (hα : 1 < α) (hα' : α < 2) :
    2 * (α + 1) / (1 - α) * betaFun (2 - α) (2*α)
        + 2 * (1 - 2*α) * (3 - 2*α) / (α * (1 - α)) * betaFun (2 - α) (2 - α)
      = 2 * π * Real.Gamma (2*α) * Real.cos (π*α/2)
          / (α * Real.Gamma α ^ 2 * Real.sin (π*α/2)) := by
  have h₁ : 2 * (α + 1) / (1 - α) * betaFun (2 - α) (2*α) = 2 * betaFun (1 - α) (2*α) := by
    rw [betaFun_one_sub_left_rec hα hα']
    ring
  rw [h₁, betaFun_two_sub_self_eq hα hα', ← two_betaFun_sub_betaFun hα hα']
  ring

/-! ### Passing to the limit `p → 0⁺` -/

theorem nhdsGT_zero_eq_Ioo : 𝓝[>] (0:ℝ) = 𝓝[Ioo (0:ℝ) (1/2)] 0 := by
  have h := nhdsWithin_restrict' (a := (0:ℝ)) (Ioi (0:ℝ))
    (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  rwa [Ioi_inter_Iio] at h

theorem nhdsGT_zero_le {b : ℝ} (hb : 1/2 ≤ b) : 𝓝[>] (0:ℝ) ≤ 𝓝[Icc (0:ℝ) b] 0 := by
  rw [nhdsGT_zero_eq_Ioo]
  exact nhdsWithin_mono _ fun x hx => ⟨hx.1.le, by linarith [hx.2]⟩

/-- The primitive of an interval-integrable function is continuous, so it vanishes in the limit at
its own base point. -/
theorem tendsto_integral_zero {f : ℝ → ℝ} {b : ℝ} (hb : (0:ℝ) < b)
    (hf : IntervalIntegrable f volume 0 b) :
    Tendsto (fun p : ℝ => ∫ t in (0:ℝ)..p, f t) (𝓝[Icc (0:ℝ) b] 0) (𝓝 0) := by
  have hcont := intervalIntegral.continuousOn_primitive_interval' hf left_mem_uIcc
  rw [uIcc_of_le hb.le] at hcont
  have h0 : Tendsto (fun p : ℝ => ∫ t in (0:ℝ)..p, f t) (𝓝[Icc (0:ℝ) b] 0)
      (𝓝 (∫ t in (0:ℝ)..(0:ℝ), f t)) := hcont 0 (left_mem_Icc.mpr hb.le)
  rwa [intervalIntegral.integral_same] at h0

/-- The same continuity read at the far endpoint: `∫_0^{1-p} → ∫_0^1` as `p → 0⁺`. -/
theorem tendsto_integral_one_sub {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 0 1) :
    Tendsto (fun p : ℝ => ∫ t in (0:ℝ)..(1 - p), f t) (𝓝[>] (0:ℝ))
      (𝓝 (∫ t in (0:ℝ)..(1:ℝ), f t)) := by
  have hcont := intervalIntegral.continuousOn_primitive_interval' hf left_mem_uIcc
  rw [uIcc_of_le zero_le_one] at hcont
  have h1 : Tendsto (fun x : ℝ => ∫ t in (0:ℝ)..x, f t) (𝓝[Icc (0:ℝ) 1] 1)
      (𝓝 (∫ t in (0:ℝ)..(1:ℝ), f t)) := hcont 1 (right_mem_Icc.mpr zero_le_one)
  have hmap : Tendsto (fun p : ℝ => 1 - p) (𝓝[>] (0:ℝ)) (𝓝[Icc (0:ℝ) 1] 1) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h : Tendsto (fun p : ℝ => 1 - p) (𝓝 (0:ℝ)) (𝓝 (1 - (0:ℝ))) :=
        (continuous_const.sub continuous_id).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    · rw [nhdsGT_zero_eq_Ioo]
      filter_upwards [self_mem_nhdsWithin] with p hp
      exact ⟨by linarith [hp.2], by linarith [hp.1]⟩
  simpa [Function.comp_def] using h1.comp hmap

/-- Splitting an integral over `(0, ∞)` at an interior point. -/
theorem integral_Ioi_split {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p) (hf : IntegrableOn f (Ioi 0)) :
    (∫ t in Ioi (0:ℝ), f t) = (∫ t in (0:ℝ)..p, f t) + ∫ t in Ioi p, f t := by
  rw [← Ioc_union_Ioi_eq_Ioi hp.le,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hf.mono_set fun x hx => hx.1) (hf.mono_set (Ioi_subset_Ioi hp.le)),
    intervalIntegral.integral_of_le hp.le]

theorem tendsto_integral_diamondNear {α : ℝ} (hα : 1 < α) (hα' : α < 2) :
    Tendsto (fun p : ℝ => ∫ t in (0:ℝ)..p, diamondNear α t) (𝓝[>] (0:ℝ)) (𝓝 0) :=
  (tendsto_integral_zero (by norm_num)
    (intervalIntegrable_diamondNear (by linarith) hα' (by norm_num) (by norm_num))).mono_left
    (nhdsGT_zero_le le_rfl)

theorem intervalIntegrable_midKernelReg {α : ℝ} (hα' : α < 2) :
    IntervalIntegrable (fun t : ℝ => t ^ (1 - α) * (1 - t) ^ (1 - α)) volume 0 1 := by
  have h := intervalIntegrable_rpow_mul_one_sub_rpow (a := 2 - α) (b := 2 - α)
    (by linarith) (by linarith)
  rwa [show (2:ℝ) - α - 1 = 1 - α from by ring] at h

theorem tendsto_integral_midKernelReg {α : ℝ} (hα' : α < 2) :
    Tendsto (fun p : ℝ => ∫ t in p..(1 - p), t ^ (1 - α) * (1 - t) ^ (1 - α)) (𝓝[>] (0:ℝ))
      (𝓝 (betaFun (2 - α) (2 - α))) := by
  have hint := intervalIntegrable_midKernelReg hα'
  have hval : (∫ t in (0:ℝ)..(1:ℝ), t ^ (1 - α) * (1 - t) ^ (1 - α))
      = betaFun (2 - α) (2 - α) := by
    have h := betaFun_eq_integral (a := 2 - α) (b := 2 - α) (by linarith) (by linarith)
    rw [show (2:ℝ) - α - 1 = 1 - α from by ring] at h
    exact h.symm
  have hsplit : ∀ᶠ p : ℝ in 𝓝[>] (0:ℝ),
      (∫ t in (0:ℝ)..(1 - p), t ^ (1 - α) * (1 - t) ^ (1 - α))
          - ∫ t in (0:ℝ)..p, t ^ (1 - α) * (1 - t) ^ (1 - α)
        = ∫ t in p..(1 - p), t ^ (1 - α) * (1 - t) ^ (1 - α) := by
    rw [nhdsGT_zero_eq_Ioo]
    filter_upwards [self_mem_nhdsWithin] with p hp
    have h₁ : IntervalIntegrable (fun t : ℝ => t ^ (1 - α) * (1 - t) ^ (1 - α)) volume 0 p := by
      refine hint.mono_set ?_
      rw [uIcc_of_le hp.1.le, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc le_rfl (by linarith [hp.2])
    have h₂ : IntervalIntegrable (fun t : ℝ => t ^ (1 - α) * (1 - t) ^ (1 - α))
        volume p (1 - p) := by
      refine hint.mono_set ?_
      rw [uIcc_of_le (by linarith [hp.2] : p ≤ 1 - p), uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hp.1.le (by linarith [hp.1])
    rw [eq_comm, eq_sub_iff_add_eq, add_comm]
    exact intervalIntegral.integral_add_adjacent_intervals h₁ h₂
  rw [← hval]
  refine Tendsto.congr' hsplit ?_
  simpa only [sub_zero] using (tendsto_integral_one_sub hint).sub
    ((tendsto_integral_zero zero_lt_one hint).mono_left (nhdsGT_zero_le (by norm_num)))

theorem tendsto_integral_farKernelReg {α : ℝ} (hα : 1 < α) (hα' : α < 2) :
    Tendsto (fun p : ℝ => ∫ t in Ioi p, t ^ (1 - α) * (1 + t) ^ (-α - 2)) (𝓝[>] (0:ℝ))
      (𝓝 (betaFun (2 - α) (2*α))) := by
  have hI := integrableOn_farKernelReg hα hα'
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (1 - α) * (1 + t) ^ (-α - 2)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      (hI.mono_set fun x hx => hx.1)
  have hval : (∫ t in Ioi (0:ℝ), t ^ (1 - α) * (1 + t) ^ (-α - 2)) = betaFun (2 - α) (2*α) := by
    have h := betaFun_eq_integral_Ioi (a := 2 - α) (b := 2*α) (by linarith) (by linarith)
    rw [show (2:ℝ) - α - 1 = 1 - α from by ring,
      show -(2 - α) - 2*α = -α - 2 from by ring] at h
    exact h.symm
  have hsplit : ∀ᶠ p : ℝ in 𝓝[>] (0:ℝ),
      (∫ t in Ioi (0:ℝ), t ^ (1 - α) * (1 + t) ^ (-α - 2))
          - ∫ t in (0:ℝ)..p, t ^ (1 - α) * (1 + t) ^ (-α - 2)
        = ∫ t in Ioi p, t ^ (1 - α) * (1 + t) ^ (-α - 2) := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    rw [eq_comm, eq_sub_iff_add_eq, add_comm]
    exact (integral_Ioi_split hp hI).symm
  rw [← hval]
  refine Tendsto.congr' hsplit ?_
  simpa only [sub_zero] using tendsto_const_nhds.sub
    ((tendsto_integral_zero zero_lt_one hint).mono_left (nhdsGT_zero_le (by norm_num)))

theorem differentiableAt_diamondRem (α : ℝ) : DifferentiableAt ℝ (diamondRem α) 0 := by
  have h₁ : DifferentiableAt ℝ (fun p : ℝ => (1 + p) ^ (-α - 1)) 0 :=
    (HasDerivAt.rpow_const (f := fun p : ℝ => 1 + p) ((hasDerivAt_id' (0:ℝ)).const_add 1)
      (.inl (by norm_num))).differentiableAt
  have h₂ : DifferentiableAt ℝ (fun p : ℝ => (1 - p) ^ (-α)) 0 :=
    (HasDerivAt.rpow_const (f := fun p : ℝ => 1 - p) ((hasDerivAt_id' (0:ℝ)).const_sub 1)
      (.inl (by norm_num))).differentiableAt
  have h₃ : DifferentiableAt ℝ (fun p : ℝ => α + (1 - 2*α) * p * (3 - 2*p)) 0 := by fun_prop
  show DifferentiableAt ℝ (fun p : ℝ => -α * (1 + p) ^ (-α - 1)
    + (1 - p) ^ (-α) * (α + (1 - 2*α) * p * (3 - 2*p))) 0
  exact (h₁.const_mul _).add (h₂.mul h₃)

/-- Because `diamondRem α` vanishes at `0` and is differentiable there, the quotient
`diamondRem α p / p` stays bounded as `p → 0`; that is all that is needed, and the value of the
derivative is irrelevant. -/
theorem tendsto_diamondRem_div (α : ℝ) :
    Tendsto (fun p : ℝ => diamondRem α p / p) (𝓝[≠] (0:ℝ)) (𝓝 (deriv (diamondRem α) 0)) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (differentiableAt_diamondRem α).hasDerivAt
  refine h.congr fun p => ?_
  rw [slope_def_field, diamondRem_zero, sub_zero, sub_zero]

theorem tendsto_diamondRem_term {α : ℝ} (hα : 1 < α) (hα' : α < 2) :
    Tendsto (fun p : ℝ => 2 * p ^ (1 - α) * diamondRem α p / (α * (1 - α))) (𝓝[>] (0:ℝ))
      (𝓝 0) := by
  have hα0 : (0:ℝ) < α := by linarith
  have h1α : (1:ℝ) - α ≠ 0 := sub_ne_zero.mpr hα.ne
  have hpow : Tendsto (fun p : ℝ => p ^ (2 - α)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hc : Tendsto (fun p : ℝ => p ^ (2 - α)) (𝓝 (0:ℝ)) (𝓝 ((0:ℝ) ^ (2 - α))) :=
      Real.continuousAt_rpow_const 0 (2 - α) (.inr (by linarith))
    rw [Real.zero_rpow (by linarith : (0:ℝ) < 2 - α).ne'] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  have hsub : Ioi (0:ℝ) ⊆ {(0:ℝ)}ᶜ := fun x hx => by
    simp only [mem_compl_iff, mem_singleton_iff]
    exact (mem_Ioi.mp hx).ne'
  have hslope := (tendsto_diamondRem_div α).mono_left (nhdsWithin_mono 0 hsub)
  have key : Tendsto (fun p : ℝ => 2 / (α * (1 - α)) * (p ^ (2 - α) * (diamondRem α p / p)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using (hpow.mul hslope).const_mul (2 / (α * (1 - α)))
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with p hp
  have hp0 : (0:ℝ) < p := hp
  have hp2 : p ^ (2 - α) = p * p ^ (1 - α) := by
    rw [show (2:ℝ) - α = 1 + (1 - α) from by ring, Real.rpow_add hp0, Real.rpow_one]
  rw [hp2]
  field_simp

/-- The limit of the regularised diamond profile as `p → 0⁺`.  The two boundary contributions
vanish and the two convergent integrals reach their Beta values. -/
theorem tendsto_Theta_regularised {α : ℝ} (hα : 1 < α) (hα' : α < 2) :
    Tendsto (fun p : ℝ => Theta α p) (𝓝[>] (0:ℝ))
      (𝓝 (2 * (α + 1) / (1 - α) * betaFun (2 - α) (2*α)
        + 2 * (1 - 2*α) * (3 - 2*α) / (α * (1 - α)) * betaFun (2 - α) (2 - α))) := by
  have hEq : ∀ᶠ p : ℝ in 𝓝[>] (0:ℝ), Theta α p
      = 2 * (∫ t in (0:ℝ)..p, diamondNear α t)
        + 2 * (α + 1) / (1 - α) * (∫ t in Ioi p, t ^ (1 - α) * (1 + t) ^ (-α - 2))
        + 2 * (1 - 2*α) * (3 - 2*α) / (α * (1 - α))
            * (∫ t in p..(1 - p), t ^ (1 - α) * (1 - t) ^ (1 - α))
        + 2 * p ^ (1 - α) * diamondRem α p / (α * (1 - α)) := by
    rw [nhdsGT_zero_eq_Ioo]
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact Theta_eq_regularised hα hα' hp.1 hp.2
  refine Tendsto.congr' (hEq.mono fun p h => h.symm) ?_
  have h := ((((tendsto_integral_diamondNear hα hα').const_mul 2).add
      ((tendsto_integral_farKernelReg hα hα').const_mul (2 * (α + 1) / (1 - α)))).add
      ((tendsto_integral_midKernelReg hα').const_mul
        (2 * (1 - 2*α) * (3 - 2*α) / (α * (1 - α))))).add
      (tendsto_diamondRem_term hα hα')
  simpa using h

/-- **The value of the diamond constant.**  For `1 < α < 2`,
`Θ α (1/2) = 2π Γ (2α) cos (πα/2) / (α Γ α ^ 2 sin (πα/2))`.
Combined with `Theta_eq_Theta_half` this evaluates `Θ α p` for every `p ∈ (0, 1/2]`. -/
theorem Theta_half_eq {α : ℝ} (hα : 1 < α) (hα' : α < 2) :
    Theta α (1/2)
      = 2 * π * Real.Gamma (2*α) * Real.cos (π*α/2)
          / (α * Real.Gamma α ^ 2 * Real.sin (π*α/2)) := by
  have hconst : Tendsto (fun p : ℝ => Theta α p) (𝓝[>] (0:ℝ)) (𝓝 (Theta α (1/2))) := by
    refine Tendsto.congr' ?_ tendsto_const_nhds
    rw [nhdsGT_zero_eq_Ioo]
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (Theta_eq_Theta_half hα hα' hp.1 hp.2.le).symm
  rw [tendsto_nhds_unique hconst (tendsto_Theta_regularised hα hα')]
  exact regularised_limit hα hα'

end CenteredMaximal.Fractional

end

end
