/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.KernelComparisonOnSupport
public import CenteredMaximal.Ball.BallComplementSourceBound
public import CenteredMaximal.Ball.BallKernelSupport

/-!
# Green comparison for the complementary obstacle density

The weak obstacle equation gives `ΔU = ρ - f` only inside the Dirichlet ball. A Green weight
supported there can still be compared with the whole-space zero extension of `ρ`.
-/

@[expose] public section

noncomputable section

open InnerProductSpace MeasureTheory Metric Set Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace CenteredMaximal.Ball

variable {n : ℕ}

/-- A normalized real Green weight is supported in any ball containing the common cutoff
domain. The cutoff identity avoids reasoning directly about the kernel singularity. -/
theorem normalized_real_kernel_support_of_cutoff
    (K : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞)
    {R r₀ G obstacleR : ℝ} (hr₀ : 0 < r₀) (hG : 0 ≤ G)
    (hK : ∀ z, G ≤ ‖z‖ → K z = 0)
    (hcontain : greenCutoffDomain (n + 1) R r₀ G ⊆
      ball (0 : EuclideanSpace ℝ (Fin (n + 1))) obstacleR)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : ‖x‖ < R + r₀)
    {r : ℝ} (hr : 0 < r) (hrr₀ : r < r₀) :
    ∀ y, ((volume (ball x r))⁻¹ * K (r⁻¹ • (x - y))).toReal ≠ 0 →
      y ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) obstacleR := by
  let χ := greenCutoff (n + 1) R r₀ G
  have hχD : tsupport χ ⊆ greenCutoffDomain (n + 1) R r₀ G :=
    greenCutoff_tsupport_subset_domain (n + 1) hr₀ hG
  intro y hqy
  have hmul := normalized_kernel_mul_greenCutoff (n + 1) K hr₀ hG
    hK x hx hr hrr₀ y
  have hχnz : χ y ≠ 0 := by
    intro hzero
    change greenCutoff (n + 1) R r₀ G y = 0 at hzero
    rw [hzero, mul_zero] at hmul
    exact hqy hmul.symm
  exact hcontain (hχD (subset_tsupport χ (by simpa [Function.mem_support] using hχnz)))

/-- A nonnegative real Green pairing with the local Laplacian yields the exact extended-real
kernel comparison needed by the direct obstacle certificate. -/
theorem normalized_green_comparison_of_ballComplement
    (center : EuclideanSpace ℝ (Fin (n + 1))) (R : ℝ)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f)
    (hf0 : ∀ y, 0 ≤ f y)
    (κ : ℝ) (hκ : 0 ≤ κ)
    (ρlocal : DirichletSobolev.L2D (ball center R))
    (hρ : 0 ≤ ρlocal ∧ ρlocal ≤ κ • DirichletSobolev.ballUnitL2 center R)
    (K : EuclideanSpace ℝ (Fin (n + 1)) → ℝ≥0∞)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (r : ℝ)
    (q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hqint : Integrable q)
    (hQ : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) = ENNReal.ofReal (q y))
    (hq0 : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))] q)
    (hsupport : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      q y ≠ 0 → y ∈ ball center R)
    (hpair : 0 ≤ ∫ y, q y *
      DirichletSobolev.ballComplementSourceExtension center R
        (DirichletSobolev.ballSourceL2 center R f hfcont hfcomp) ρlocal y) :
    (∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
      ∫⁻ y, (volume (ball x r))⁻¹ * K (r⁻¹ • (x - y)) *
        extendRestrictedDensity (ball center R) ρlocal y := by
  let D := ball center R
  let F := DirichletSobolev.ballSourceL2 center R f hfcont hfcomp
  let g := DirichletSobolev.ballComplementSourceExtension center R F ρlocal
  let ρ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := D.indicator (ρlocal : _ → ℝ)
  have hF : (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) =ᵐ[volume.restrict D] f :=
    DirichletSobolev.ballSourceL2_coeFn center R f hfcont hfcomp
  have hlocal : g =ᵐ[volume.restrict D]
      (fun y ↦ (ρlocal y : ℝ) - f y) := by
    filter_upwards [DirichletSobolev.ballComplementSourceExtension_ae_eq_local
      center R F ρlocal, Lp.coeFn_sub ρlocal F, hF]
      with y hg hsub hfy
    calc
      g y = ((ρlocal - F) y : ℝ) := hg
      _ = (ρlocal y : ℝ) - (F y : ℝ) := hsub
      _ = (ρlocal y : ℝ) - f y := by rw [hfy]
  have hrel : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      q y ≠ 0 → f y = ρ y - g y :=
    source_relation_on_kernel_support volume D measurableSet_ball q f
      ρlocal g hsupport hlocal
  have hρ0 : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))] ρ :=
    ae_nonneg_indicator_of_ae_restrict volume D measurableSet_ball ρlocal
      ((Lp.coeFn_nonneg ρlocal).2 hρ.1)
  have hN : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      extendRestrictedDensity D ρlocal y = ENNReal.ofReal (ρ y) := by
    filter_upwards with y
    exact extendRestrictedDensity_eq_ofReal_indicator D ρlocal y
  obtain ⟨M, hM⟩ := hfcomp.exists_bound_of_continuous hfcont
  have hfint : Integrable (fun y ↦ q y * f y) :=
    hqint.mul_bdd hfcont.aestronglyMeasurable (Filter.Eventually.of_forall hM)
  obtain ⟨B, hB0, hgmeas, hgbound⟩ :=
    DirichletSobolev.exists_bounded_ballComplementSourceExtension
      center R f hfcont hfcomp ρlocal κ hκ hρ
  have hgint : Integrable (fun y ↦ q y * g y) :=
    hqint.mul_bdd hgmeas hgbound
  have hρint : Integrable (fun y ↦ q y * ρ y) := by
    apply (hfint.add hgint).congr
    filter_upwards [hrel] with y hy
    by_cases hqy : q y = 0
    · simp [hqy]
    · dsimp
      rw [hy hqy]
      ring
  exact normalized_green_comparison_of_pairing_on_support K x r hQ hN
    hq0 (Filter.Eventually.of_forall hf0) hρ0 hfint hρint hgint hrel hpair

/-- The planar comparison from a Green pairing, with support containment supplied by the
common cutoff. -/
theorem normalized_planarKernel_comparison_of_ballComplement
    {Rsrc r₀ Robs : ℝ} (hr₀ : 0 < r₀)
    (hcontain : greenCutoffDomain 2 Rsrc r₀ planarGreenRadius ⊆
      ball (0 : EuclideanSpace ℝ (Fin 2)) Robs)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f)
    (hf0 : ∀ y, 0 ≤ f y) (κ : ℝ) (hκ : 0 ≤ κ)
    (ρlocal : DirichletSobolev.L2D
      (ball (0 : EuclideanSpace ℝ (Fin 2)) Robs))
    (hρ : 0 ≤ ρlocal ∧ ρlocal ≤ κ • DirichletSobolev.ballUnitL2 0 Robs)
    (x : EuclideanSpace ℝ (Fin 2)) (hx : ‖x‖ < Rsrc + r₀)
    {r : ℝ} (hr : 0 < r) (hrr₀ : r < r₀)
    (hpair : 0 ≤ ∫ y,
      ((volume (ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal *
        DirichletSobolev.ballComplementSourceExtension 0 Robs
          (DirichletSobolev.ballSourceL2 0 Robs f hfcont hfcomp) ρlocal y) :
    (∫⁻ y, (volume (ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
      ∫⁻ y, (volume (ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y)) *
        extendRestrictedDensity (ball (0 : EuclideanSpace ℝ (Fin 2)) Robs) ρlocal y := by
  let q : EuclideanSpace ℝ (Fin 2) → ℝ := fun y =>
    ((volume (ball x r))⁻¹ * planarKernel (r⁻¹ • (x - y))).toReal
  obtain ⟨hqint, hQ⟩ := normalized_planarKernel_real_representative x hr
  have hG : 0 ≤ planarGreenRadius := by unfold planarGreenRadius; positivity
  have hsupport : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin 2))),
      q y ≠ 0 → y ∈ ball (0 : EuclideanSpace ℝ (Fin 2)) Robs := by
    filter_upwards with y
    exact normalized_real_kernel_support_of_cutoff (n := 1) planarKernel
      hr₀ hG planarKernel_eq_zero_of_radius_le hcontain x hx hr hrr₀ y
  have hq0 : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 2)))] q :=
    Filter.Eventually.of_forall (fun y => ENNReal.toReal_nonneg)
  exact normalized_green_comparison_of_ballComplement 0 Robs f hfcont hfcomp
    hf0 κ hκ ρlocal hρ planarKernel x r q hqint hQ hq0 hsupport hpair

/-- The Newtonian comparison from a Green pairing in dimension `n+1 ≥ 3`. -/
theorem normalized_newtonianKernel_comparison_of_ballComplement (n : ℕ)
    (hn : 3 ≤ n + 1)
    {Rsrc r₀ Robs : ℝ} (hr₀ : 0 < r₀)
    (hcontain : greenCutoffDomain (n + 1) Rsrc r₀ (greenRadius (n + 1)) ⊆
      ball (0 : EuclideanSpace ℝ (Fin (n + 1))) Robs)
    (f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hfcont : Continuous f) (hfcomp : HasCompactSupport f)
    (hf0 : ∀ y, 0 ≤ f y) (κ : ℝ) (hκ : 0 ≤ κ)
    (ρlocal : DirichletSobolev.L2D
      (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) Robs))
    (hρ : 0 ≤ ρlocal ∧ ρlocal ≤ κ • DirichletSobolev.ballUnitL2 0 Robs)
    (x : EuclideanSpace ℝ (Fin (n + 1))) (hx : ‖x‖ < Rsrc + r₀)
    {r : ℝ} (hr : 0 < r) (hrr₀ : r < r₀)
    (hpair : 0 ≤ ∫ y,
      ((volume (ball x r))⁻¹ * newtonianKernel (n + 1) (r⁻¹ • (x - y))).toReal *
        DirichletSobolev.ballComplementSourceExtension 0 Robs
          (DirichletSobolev.ballSourceL2 0 Robs f hfcont hfcomp) ρlocal y) :
    (∫⁻ y, (volume (ball x r))⁻¹ * newtonianKernel (n + 1)
        (r⁻¹ • (x - y)) * ‖f y‖ₑ) ≤
      ∫⁻ y, (volume (ball x r))⁻¹ * newtonianKernel (n + 1)
        (r⁻¹ • (x - y)) *
        extendRestrictedDensity (ball (0 : EuclideanSpace ℝ (Fin (n + 1))) Robs)
          ρlocal y := by
  let q : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun y =>
    ((volume (ball x r))⁻¹ * newtonianKernel (n + 1) (r⁻¹ • (x - y))).toReal
  obtain ⟨hqint, hQ⟩ := normalized_newtonianKernel_real_representative
    (n + 1) hn x hr
  have hsupport : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      q y ≠ 0 → y ∈ ball (0 : EuclideanSpace ℝ (Fin (n + 1))) Robs := by
    filter_upwards with y
    exact normalized_real_kernel_support_of_cutoff (n := n)
      (newtonianKernel (n + 1)) hr₀ (greenRadius_pos (n + 1) hn).le
      (newtonianKernel_eq_zero_of_radius_le (n + 1) hn)
      hcontain x hx hr hrr₀ y
  have hq0 : 0 ≤ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (n + 1))))] q :=
    Filter.Eventually.of_forall (fun y => ENNReal.toReal_nonneg)
  exact normalized_green_comparison_of_ballComplement 0 Robs f hfcont hfcomp
    hf0 κ hκ ρlocal hρ (newtonianKernel (n + 1)) x r q
    hqint hQ hq0 hsupport hpair

end CenteredMaximal.Ball
