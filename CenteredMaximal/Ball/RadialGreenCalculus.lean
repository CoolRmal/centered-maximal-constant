/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.GreenIdentity
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Radial integration by parts for Green kernels

The planar and Newtonian Green pairings have the same one-dimensional calculation. A radial
profile `ψ` and cumulative Laplacian mass `F` satisfy a flux cancellation with a spherical
mean `m`. This lemma isolates the finite-annulus integration by parts, before the inner
radius is sent to zero.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped Interval

namespace CenteredMaximal.Ball

/-- Radial Green integration by parts on an annulus. The hypotheses describe the profile
derivative, the derivative of cumulative Laplacian mass, and the derivative of the spherical
mean. Their flux cancellation makes the derivative of `ψ F + k m` equal to `ψ q`.

For the planar kernel, `k = 2` when `m` is the unnormalized sphere integral. For the
Newtonian kernel, `k = n`. -/
theorem integral_radial_green_flux
    (δ ρ k : ℝ)
    (ψ F m q dψ dm : ℝ → ℝ)
    (hψρ : ψ ρ = 0)
    (hψ : ∀ s ∈ Set.uIcc δ ρ, HasDerivAt ψ (dψ s) s)
    (hF : ∀ s ∈ Set.uIcc δ ρ, HasDerivAt F (q s) s)
    (hm : ∀ s ∈ Set.uIcc δ ρ, HasDerivAt m (dm s) s)
    (hflux : ∀ s ∈ Set.uIcc δ ρ, dψ s * F s + k * dm s = 0)
    (hint : IntervalIntegrable (fun s ↦ ψ s * q s) volume δ ρ) :
    (∫ s in δ..ρ, ψ s * q s) =
      k * (m ρ - m δ) - ψ δ * F δ := by
  have hderiv : ∀ s ∈ Set.uIcc δ ρ,
      HasDerivAt (fun t ↦ ψ t * F t + k * m t) (ψ s * q s) s := by
    intro s hs
    have h := ((hψ s hs).mul (hF s hs)).add ((hm s hs).const_mul k)
    have hcoeff : dψ s * F s + ψ s * q s + k * dm s = ψ s * q s := by
      linarith [hflux s hs]
    have hfun : (ψ * F + fun y ↦ k * m y) = (fun t ↦ ψ t * F t + k * m t) := by
      funext t
      rfl
    rw [hfun, hcoeff] at h
    exact h
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hψρ] at hFTC
  convert hFTC using 1
  ring

/-- The finite-annulus Green pairing for the planar logarithmic profile, assuming the
cumulative ball integral `F` and spherical integral `m` obey the radial flux identity. -/
theorem integral_planar_green_profile_flux
    (δ ρ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ = planarGreenRadius)
    (F m q dm : ℝ → ℝ)
    (hF : ∀ s ∈ Set.uIcc δ ρ, HasDerivAt F (q s) s)
    (hm : ∀ s ∈ Set.uIcc δ ρ, HasDerivAt m (dm s) s)
    (hflux : ∀ s ∈ Set.uIcc δ ρ, F s = s * dm s)
    (hint : IntervalIntegrable (fun s ↦ planarGreenProfile s * q s) volume δ ρ) :
    (∫ s in δ..ρ, planarGreenProfile s * q s) =
      2 * (m ρ - m δ) - planarGreenProfile δ * F δ := by
  apply integral_radial_green_flux δ ρ 2 planarGreenProfile F m q
    (fun s ↦ deriv planarGreenProfile s) dm
  · rw [hρ]
    exact planarGreenProfile_at_radius
  · intro s hs
    have hs' : δ ≤ s := (Set.uIcc_of_le hδρ ▸ hs).1
    have hspos := lt_of_lt_of_le hδ hs'
    rw [(hasDerivAt_planarGreenProfile hspos).deriv]
    exact hasDerivAt_planarGreenProfile hspos
  · exact hF
  · exact hm
  · intro s hs
    rw [hflux s hs]
    have hs' : 0 < s := lt_of_lt_of_le hδ (Set.uIcc_of_le hδρ ▸ hs).1
    calc
      deriv planarGreenProfile s * (s * dm s) + 2 * dm s =
          (s * deriv planarGreenProfile s + 2) * dm s := by ring
      _ = 0 := by rw [planarGreenProfile_flux hs']; ring
  · exact hint

/-- The finite-annulus Green pairing for the Newtonian profile in any dimension `n ≥ 3`.
The only geometric input is the flux identity `F(s) = s^(n-1) m'(s)`. -/
theorem integral_newtonian_green_profile_flux
    (n : ℕ) (hn : 3 ≤ n)
    (δ ρ : ℝ) (hδ : 0 < δ) (hδρ : δ ≤ ρ) (hρ : ρ = greenRadius n)
    (F m q dm : ℝ → ℝ)
    (hF : ∀ s ∈ Set.uIcc δ ρ, HasDerivAt F (q s) s)
    (hm : ∀ s ∈ Set.uIcc δ ρ, HasDerivAt m (dm s) s)
    (hflux : ∀ s ∈ Set.uIcc δ ρ, F s = s ^ (n - 1) * dm s)
    (hint : IntervalIntegrable
      (fun s ↦ newtonianGreenProfile n s * q s) volume δ ρ) :
    (∫ s in δ..ρ, newtonianGreenProfile n s * q s) =
      (n : ℝ) * (m ρ - m δ) - newtonianGreenProfile n δ * F δ := by
  apply integral_radial_green_flux δ ρ (n : ℝ) (newtonianGreenProfile n) F m q
    (fun s ↦ deriv (newtonianGreenProfile n) s) dm
  · rw [hρ]
    exact newtonianGreenProfile_at_radius n hn
  · intro s hs
    have hs' : δ ≤ s := (Set.uIcc_of_le hδρ ▸ hs).1
    have hspos := lt_of_lt_of_le hδ hs'
    rw [(hasDerivAt_newtonianGreenProfile n hn hspos).deriv]
    exact hasDerivAt_newtonianGreenProfile n hn hspos
  · exact hF
  · exact hm
  · intro s hs
    rw [hflux s hs]
    have hs' : 0 < s := lt_of_lt_of_le hδ (Set.uIcc_of_le hδρ ▸ hs).1
    calc
      deriv (newtonianGreenProfile n) s * (s ^ (n - 1) * dm s) +
          (n : ℝ) * dm s =
            (s ^ (n - 1) * deriv (newtonianGreenProfile n) s + (n : ℝ)) * dm s := by
              ring
      _ = 0 := by rw [newtonianGreenProfile_flux n hn hs']; ring
  · exact hint

end CenteredMaximal.Ball
