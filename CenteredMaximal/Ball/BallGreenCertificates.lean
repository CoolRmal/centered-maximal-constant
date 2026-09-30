/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.AERealCertificate
public import CenteredMaximal.Ball.BallComplementCertificate
public import CenteredMaximal.Ball.BallComplementGreenPairing
public import CenteredMaximal.Ball.BallComplementKernelComparison

/-!
# Direct obstacle certificates for Euclidean balls

The penalized Dirichlet obstacle gives a contact bound and a capped complementary density.
Its local Green pairing, proved by smooth approximation, gives the remaining kernel comparison
at almost every center.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal ContDiff RealInnerProductSpace

namespace CenteredMaximal.Ball

open DirichletSobolev

/-- The planar logarithmic kernel admits direct obstacle certificates at almost every center. -/
theorem hasRealAEDirectObstacleCertificates_planarKernel :
    HasRealAEDirectObstacleCertificates planarKernel := by
  intro f hfcomp hfsmooth hfnn κ hκ R r₀ hr₀ _hsupp
  let S : ℝ := greenCutoffInnerRadius R r₀ planarGreenRadius + 2 * r₀ + 2
  have hfcont : Continuous f := hfsmooth.continuous
  obtain ⟨U, _νpen, ρlocal, Ω, ν, _hρdef, hΩ, hνext,
    hcontact, hρcap, hνcap, hU, hweak⟩ :=
      exists_ball_smooth_complement_certificate
        (0 : EuclideanSpace ℝ (Fin 2)) S f hfcont hfcomp hfnn κ hκ.le
  have hU' : 0 ≤ (U : H1amb (ball (0 : EuclideanSpace ℝ (Fin 2)) S)) 0 := by
    simpa only [valueEmbedding_apply] using hU
  have hweak' := ball_weak_equation_sub
    (0 : EuclideanSpace ℝ (Fin 2)) S U
    (ballSourceL2 0 S f hfcont hfcomp) ρlocal hweak
  have hpair := ae_planar_ballComplement_green_pairing_nonneg
    R r₀ hr₀ f hfcont hfcomp κ hκ.le U ρlocal hU' hρcap hweak'
  have hcontain : greenCutoffDomain 2 R r₀ planarGreenRadius ⊆
      ball (0 : EuclideanSpace ℝ (Fin 2)) S := by
    intro y hy
    exact closure_greenCutoffDomain_subset_greenObstacleDomain 2 R r₀
      planarGreenRadius (subset_closure hy)
  refine ⟨Ω, ν, hcontact, hνcap, ?_⟩
  filter_upwards [hpair] with x hx
  intro r hxΩ hr hrr₀ hxR
  have hxΩ' : x ∉ {y | y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) S ∧
      0 < ((U : H1amb (ball (0 : EuclideanSpace ℝ (Fin 2)) S)) 0 y : ℝ)} := by
    simpa only [hΩ] using hxΩ
  simpa only [hνext] using
    (normalized_planarKernel_comparison_of_ballComplement hr₀ hcontain
      f hfcont hfcomp hfnn κ hκ.le ρlocal hρcap x hxR hr hrr₀
      (hx hxΩ' hxR r hr hrr₀))

/-- The Newtonian kernel admits direct obstacle certificates in dimensions at least three. -/
theorem hasRealAEDirectObstacleCertificates_newtonianKernel_succ
    (n : ℕ) (hn : 3 ≤ n + 1) :
    HasRealAEDirectObstacleCertificates (newtonianKernel (n + 1)) := by
  intro f hfcomp hfsmooth hfnn κ hκ R r₀ hr₀ _hsupp
  let S : ℝ := greenCutoffInnerRadius R r₀ (greenRadius (n + 1)) + 2 * r₀ + 2
  have hfcont : Continuous f := hfsmooth.continuous
  obtain ⟨U, _νpen, ρlocal, Ω, ν, _hρdef, hΩ, hνext,
    hcontact, hρcap, hνcap, hU, hweak⟩ :=
      exists_ball_smooth_complement_certificate
        (0 : EuclideanSpace ℝ (Fin (n + 1))) S f hfcont hfcomp hfnn κ hκ.le
  have hU' : 0 ≤ (U : H1amb (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) S)) 0 := by
    simpa only [valueEmbedding_apply] using hU
  have hweak' := ball_weak_equation_sub
    (0 : EuclideanSpace ℝ (Fin (n + 1))) S U
    (ballSourceL2 0 S f hfcont hfcomp) ρlocal hweak
  have hpair := ae_newtonian_ballComplement_green_pairing_nonneg
    n hn R r₀ hr₀ f hfcont hfcomp κ hκ.le U ρlocal hU' hρcap hweak'
  have hcontain : greenCutoffDomain (n + 1) R r₀ (greenRadius (n + 1)) ⊆
      ball (0 : EuclideanSpace ℝ (Fin (n + 1))) S := by
    intro y hy
    exact closure_greenCutoffDomain_subset_greenObstacleDomain (n + 1) R r₀
      (greenRadius (n + 1)) (subset_closure hy)
  refine ⟨Ω, ν, hcontact, hνcap, ?_⟩
  filter_upwards [hpair] with x hx
  intro r hxΩ hr hrr₀ hxR
  have hxΩ' : x ∉ {y | y ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) S ∧
      0 < ((U : H1amb (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) S)) 0 y : ℝ)} := by
    simpa only [hΩ] using hxΩ
  simpa only [hνext] using
    (normalized_newtonianKernel_comparison_of_ballComplement n hn hr₀ hcontain
      f hfcont hfcomp hfnn κ hκ.le ρlocal hρcap x hxR hr hrr₀
      (hx hxΩ' hxR r hr hrr₀))

/-- Newtonian direct obstacle certificates in every original dimension `n ≥ 3`. -/
theorem hasRealAEDirectObstacleCertificates_newtonianKernel
    (n : ℕ) (hn : 3 ≤ n) :
    HasRealAEDirectObstacleCertificates (newtonianKernel n) := by
  have hsub : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have h := hasRealAEDirectObstacleCertificates_newtonianKernel_succ (n - 1)
    (by omega : 3 ≤ n - 1 + 1)
  rw [hsub] at h
  exact h

end CenteredMaximal.Ball
