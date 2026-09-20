/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.BetaIntegral

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

open scoped Real

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

end CenteredMaximal.Fractional

end

end
