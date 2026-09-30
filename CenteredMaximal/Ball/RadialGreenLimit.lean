/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.RadialGreenCalculus
public import CenteredMaximal.Ball.CenterLimits
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Passage to the center in radial Green integration by parts

The finite-annulus formulas in `RadialGreenCalculus` have an inner boundary term.
This file records the exact improper-integral limit that removes that term once the
center estimates have been established.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Interval Topology

namespace CenteredMaximal.Ball

/-- Integrals over `(δ,ρ)` tend to the integral over `(0,ρ)` as the lower endpoint
approaches zero from above, provided the integrand is integrable on `(0,ρ)`. -/
theorem tendsto_integral_interval_to_Ioo
    (u : ℝ → ℝ) {ρ : ℝ} (hρ : 0 < ρ) (hu : IntegrableOn u (Ioo (0 : ℝ) ρ)) :
    Tendsto (fun δ : ℝ ↦ ∫ s in δ..ρ, u s) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ s in Ioo (0 : ℝ) ρ, u s)) := by
  have hint : IntervalIntegrable u volume (0 : ℝ) ρ :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hρ.le).2 hu
  have hcont : ContinuousWithinAt (fun δ : ℝ ↦ ∫ s in ρ..δ, u s)
      (Icc (0 : ℝ) ρ) 0 := by
    have hInt' : IntervalIntegrable u volume (min ρ (0 : ℝ)) (max ρ ρ) := by
      simpa [min_eq_right hρ.le] using hint
    exact intervalIntegral.continuousWithinAt_primitive
      (a := ρ) (b₁ := 0) (b₂ := ρ) (b₀ := 0)
      (μ := volume) (measure_singleton (0 : ℝ)) hInt'
  have hmem : Icc (0 : ℝ) ρ ∈ 𝓝[>] (0 : ℝ) := by
    apply Filter.mem_of_superset
      (inter_mem_nhdsWithin (Ioi (0 : ℝ)) (Iio_mem_nhds hρ))
    intro δ hδ
    exact ⟨hδ.1.le, hδ.2.le⟩
  have hlim : Tendsto (fun δ : ℝ ↦ ∫ s in ρ..δ, u s)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ s in ρ..(0 : ℝ), u s)) :=
    hcont.mono_left (nhdsWithin_le_of_mem hmem)
  have hlim' := hlim.neg
  convert hlim' using 1
  · funext δ
    rw [intervalIntegral.integral_symm]
  · rw [intervalIntegral.integral_symm, neg_neg]
    rw [intervalIntegral.integral_of_le hρ.le, integral_Ioc_eq_integral_Ioo]

/-- Remove the inner annulus boundary from an abstract Green integration-by-parts identity.
The remaining value is the spherical mean at the outer radius minus its center limit. -/
theorem integral_radial_green_flux_of_annulus_limit
    (ρ k m₀ : ℝ) (hρ : 0 < ρ)
    (ψ F m q : ℝ → ℝ)
    (hint : IntegrableOn (fun s ↦ ψ s * q s) (Ioo (0 : ℝ) ρ))
    (hannulus : ∀ δ : ℝ, 0 < δ → δ ≤ ρ →
      (∫ s in δ..ρ, ψ s * q s) =
        k * (m ρ - m δ) - ψ δ * F δ)
    (hm₀ : Tendsto m (𝓝[>] (0 : ℝ)) (𝓝 m₀))
    (hboundary : Tendsto (fun δ ↦ ψ δ * F δ) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (∫ s in Ioo (0 : ℝ) ρ, ψ s * q s) = k * (m ρ - m₀) := by
  have hleft := tendsto_integral_interval_to_Ioo (fun s ↦ ψ s * q s) hρ hint
  have hright : Tendsto (fun δ : ℝ ↦ k * (m ρ - m δ) - ψ δ * F δ)
      (𝓝[>] (0 : ℝ)) (𝓝 (k * (m ρ - m₀))) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds.sub hm₀).const_mul k).sub hboundary
  have hδpos : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ := self_mem_nhdsWithin
  have hδle : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), δ ≤ ρ := by
    exact ((eventually_lt_nhds hρ).filter_mono nhdsWithin_le_nhds).mono
      (fun δ hδ ↦ hδ.le)
  have heq : (fun δ : ℝ ↦ ∫ s in δ..ρ, ψ s * q s) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun δ ↦ k * (m ρ - m δ) - ψ δ * F δ) := by
    filter_upwards [hδpos, hδle] with δ hpos hle
    exact hannulus δ hpos hle
  exact tendsto_nhds_unique (hleft.congr' heq) hright

/-- Full radial Green integration by parts from the finite-annulus flux identity and the
vanishing center boundary term. This is common to the logarithmic and Newtonian profiles. -/
theorem integral_radial_green_flux_of_center_limits
    (ρ k m₀ : ℝ) (hρ : 0 < ρ)
    (ψ F m q dψ dm : ℝ → ℝ)
    (hψρ : ψ ρ = 0)
    (hψ : ∀ s ∈ Ioc (0 : ℝ) ρ, HasDerivAt ψ (dψ s) s)
    (hF : ∀ s ∈ Ioc (0 : ℝ) ρ, HasDerivAt F (q s) s)
    (hm : ∀ s ∈ Ioc (0 : ℝ) ρ, HasDerivAt m (dm s) s)
    (hflux : ∀ s ∈ Ioc (0 : ℝ) ρ, dψ s * F s + k * dm s = 0)
    (hint : IntegrableOn (fun s ↦ ψ s * q s) (Ioo (0 : ℝ) ρ))
    (hm₀ : Tendsto m (𝓝[>] (0 : ℝ)) (𝓝 m₀))
    (hboundary : Tendsto (fun δ ↦ ψ δ * F δ) (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (∫ s in Ioo (0 : ℝ) ρ, ψ s * q s) = k * (m ρ - m₀) := by
  apply integral_radial_green_flux_of_annulus_limit ρ k m₀ hρ ψ F m q hint
    (fun δ hδ hδρ ↦ ?_) hm₀ hboundary
  have hsub : ∀ s ∈ uIcc δ ρ, s ∈ Ioc (0 : ℝ) ρ := by
    intro s hs
    rw [uIcc_of_le hδρ] at hs
    exact ⟨lt_of_lt_of_le hδ hs.1, hs.2⟩
  have hintδ : IntervalIntegrable (fun s ↦ ψ s * q s) volume δ ρ := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hδρ).2
    apply hint.mono_set
    intro s hs
    exact ⟨lt_trans hδ hs.1, hs.2⟩
  exact integral_radial_green_flux δ ρ k ψ F m q dψ dm hψρ
    (fun s hs ↦ hψ s (hsub s hs))
    (fun s hs ↦ hF s (hsub s hs))
    (fun s hs ↦ hm s (hsub s hs))
    (fun s hs ↦ hflux s (hsub s hs)) hintδ

/-- Full planar radial Green pairing after removal of its center boundary term. -/
theorem integral_planar_green_profile_of_center_limits
    (m₀ : ℝ) (F m q dm : ℝ → ℝ)
    (hF : ∀ s ∈ Ioc (0 : ℝ) planarGreenRadius, HasDerivAt F (q s) s)
    (hm : ∀ s ∈ Ioc (0 : ℝ) planarGreenRadius, HasDerivAt m (dm s) s)
    (hflux : ∀ s ∈ Ioc (0 : ℝ) planarGreenRadius, F s = s * dm s)
    (hint : IntegrableOn (fun s ↦ planarGreenProfile s * q s)
      (Ioo (0 : ℝ) planarGreenRadius))
    (hm₀ : Tendsto m (𝓝[>] (0 : ℝ)) (𝓝 m₀))
    (hboundary : Tendsto (fun δ ↦ planarGreenProfile δ * F δ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (∫ s in Ioo (0 : ℝ) planarGreenRadius, planarGreenProfile s * q s) =
      2 * (m planarGreenRadius - m₀) := by
  apply integral_radial_green_flux_of_annulus_limit planarGreenRadius 2 m₀
    (by unfold planarGreenRadius; positivity) planarGreenProfile F m q hint
    (fun δ hδ hδρ ↦ ?_) hm₀ hboundary
  have hsub : ∀ s ∈ uIcc δ planarGreenRadius, s ∈ Ioc (0 : ℝ) planarGreenRadius := by
    intro s hs
    rw [uIcc_of_le hδρ] at hs
    exact ⟨lt_of_lt_of_le hδ hs.1, hs.2⟩
  have hintδ : IntervalIntegrable (fun s ↦ planarGreenProfile s * q s)
      volume δ planarGreenRadius := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hδρ).2
    apply hint.mono_set
    intro s hs
    exact ⟨lt_trans hδ hs.1, hs.2⟩
  exact integral_planar_green_profile_flux δ planarGreenRadius hδ hδρ rfl F m q dm
    (fun s hs ↦ hF s (hsub s hs))
    (fun s hs ↦ hm s (hsub s hs))
    (fun s hs ↦ hflux s (hsub s hs)) hintδ

/-- Full Newtonian radial Green pairing after removal of its center boundary term. -/
theorem integral_newtonian_green_profile_of_center_limits
    (n : ℕ) (hn : 3 ≤ n)
    (m₀ : ℝ) (F m q dm : ℝ → ℝ)
    (hF : ∀ s ∈ Ioc (0 : ℝ) (greenRadius n), HasDerivAt F (q s) s)
    (hm : ∀ s ∈ Ioc (0 : ℝ) (greenRadius n), HasDerivAt m (dm s) s)
    (hflux : ∀ s ∈ Ioc (0 : ℝ) (greenRadius n), F s = s ^ (n - 1) * dm s)
    (hint : IntegrableOn (fun s ↦ newtonianGreenProfile n s * q s)
      (Ioo (0 : ℝ) (greenRadius n)))
    (hm₀ : Tendsto m (𝓝[>] (0 : ℝ)) (𝓝 m₀))
    (hboundary : Tendsto (fun δ ↦ newtonianGreenProfile n δ * F δ)
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    (∫ s in Ioo (0 : ℝ) (greenRadius n), newtonianGreenProfile n s * q s) =
      (n : ℝ) * (m (greenRadius n) - m₀) := by
  apply integral_radial_green_flux_of_annulus_limit (greenRadius n) (n : ℝ) m₀
    (greenRadius_pos n hn) (newtonianGreenProfile n) F m q hint
    (fun δ hδ hδρ ↦ ?_) hm₀ hboundary
  have hsub : ∀ s ∈ uIcc δ (greenRadius n), s ∈ Ioc (0 : ℝ) (greenRadius n) := by
    intro s hs
    rw [uIcc_of_le hδρ] at hs
    exact ⟨lt_of_lt_of_le hδ hs.1, hs.2⟩
  have hintδ : IntervalIntegrable (fun s ↦ newtonianGreenProfile n s * q s)
      volume δ (greenRadius n) := by
    apply (intervalIntegrable_iff_integrableOn_Ioo_of_le hδρ).2
    apply hint.mono_set
    intro s hs
    exact ⟨lt_trans hδ hs.1, hs.2⟩
  exact integral_newtonian_green_profile_flux n hn δ (greenRadius n) hδ hδρ rfl
    F m q dm
    (fun s hs ↦ hF s (hsub s hs))
    (fun s hs ↦ hm s (hsub s hs))
    (fun s hs ↦ hflux s (hsub s hs)) hintδ

end CenteredMaximal.Ball
