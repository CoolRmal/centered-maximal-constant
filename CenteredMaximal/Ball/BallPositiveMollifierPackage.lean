/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Ball.LocalMollifierDistribution
public import CenteredMaximal.Ball.BallKernelSupport
public import CenteredMaximal.Ball.BoundedConvolution
public import CenteredMaximal.Ball.ComplementDistributionAdapter
public import CenteredMaximal.Ball.BallComplementSourceBound
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A single mollifier sequence for the local obstacle comparison

A normalized bump sequence preserves positivity and compact support. Its classical Laplacians
satisfy the local weak equation throughout the common Green cutoff domain, converge almost
everywhere there, and share the global cap of the source density.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set Filter Topology ContinuousLinearMap
open scoped Convolution RealInnerProductSpace

namespace CenteredMaximal.Ball

/-- Outer radius of the standard shrinking bump. -/
def standardMollifierRadius (k : ℕ) : ℝ := 1 / (k + 1 : ℝ)

theorem standardMollifierRadius_pos (k : ℕ) :
    0 < standardMollifierRadius k := by
  unfold standardMollifierRadius
  positivity

theorem standardMollifierRadius_le_one (k : ℕ) :
    standardMollifierRadius k ≤ 1 := by
  unfold standardMollifierRadius
  have hk : (1 : ℝ) ≤ (k + 1 : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
  exact (div_le_iff₀ (by positivity : (0 : ℝ) < (k + 1 : ℝ))).mpr (by simpa only [one_mul] using hk)

/-- A compactly supported smooth probability kernel at scale `1/(k+1)`. -/
def standardMollifierBump (n k : ℕ) :
    ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) :=
  ⟨standardMollifierRadius k / 2, standardMollifierRadius k,
    half_pos (standardMollifierRadius_pos k),
    half_lt_self (standardMollifierRadius_pos k)⟩

/-- The standard positive mollification of a real function. -/
def standardMollification {n : ℕ} (u : EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  (standardMollifierBump n k).normed volume ⋆[lsmul ℝ ℝ, volume] u

theorem standardMollifierBump_rOut (n k : ℕ) :
    (standardMollifierBump n k).rOut = standardMollifierRadius k := rfl

theorem standardMollifierBump_rIn (n k : ℕ) :
    (standardMollifierBump n k).rIn = standardMollifierRadius k / 2 := rfl

theorem standardMollifierBump_tendsto_rOut (n : ℕ) :
    Tendsto (fun k => (standardMollifierBump n k).rOut) atTop (𝓝 0) := by
  simpa [standardMollifierBump_rOut, standardMollifierRadius, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

theorem standardMollifierBump_ratio (n : ℕ) :
    ∀ᶠ k : ℕ in atTop,
      (standardMollifierBump n k).rOut ≤ 2 * (standardMollifierBump n k).rIn := by
  filter_upwards with k
  simp only [standardMollifierBump_rOut, standardMollifierBump_rIn]
  have h : 2 * (standardMollifierRadius k / 2) = standardMollifierRadius k := by ring
  rw [h]

/-- Every standard mollification is smooth, compactly supported, and nonnegative; the
sequence converges almost everywhere to its integrable input. -/
theorem standardMollification_basic {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu_int : Integrable u) (hu_comp : HasCompactSupport u)
    (hu_nonneg : ∀ x, 0 ≤ u x) :
    (∀ k, ContDiff ℝ (⊤ : ℕ∞) (standardMollification u k)) ∧
    (∀ k, HasCompactSupport (standardMollification u k)) ∧
    (∀ k x, 0 ≤ standardMollification u k x) ∧
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun k => standardMollification u k x) atTop (𝓝 (u x)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    exact (standardMollifierBump n k).hasCompactSupport_normed.contDiff_convolution_left
      (lsmul ℝ ℝ) (standardMollifierBump n k).contDiff_normed hu_int.locallyIntegrable
  · intro k
    exact HasCompactSupport.convolution (lsmul ℝ ℝ)
      (standardMollifierBump n k).hasCompactSupport_normed hu_comp
  · intro k x
    change 0 ≤ ∫ y, (standardMollifierBump n k).normed volume y • u (x-y)
    apply integral_nonneg
    intro y
    simpa only [smul_eq_mul, Pi.zero_apply] using
      mul_nonneg ((standardMollifierBump n k).nonneg_normed (μ := volume) y)
        (hu_nonneg (x-y))
  · exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (standardMollifierBump_tendsto_rOut n) (standardMollifierBump_ratio n)
      hu_int.locallyIntegrable


/-- On the common Green cutoff domain, the mollified weak equation holds at every point. -/
theorem standardMollification_laplacian_eq_on_greenCutoffDomain
    (n : ℕ) (R r₀ G : ℝ)
    (u g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : Integrable u)
    (hlocal : HasLocalDistributionalLaplacian n
      (greenObstacleDomain n R r₀ G) u g)
    (k : ℕ) (y : EuclideanSpace ℝ (Fin n))
    (hy : y ∈ greenCutoffDomain n R r₀ G) :
    Laplacian.laplacian (standardMollification u k) y =
      ((standardMollifierBump n k).normed volume ⋆[lsmul ℝ ℝ, volume] g) y := by
  apply laplacian_normed_bump_convolution_eq_of_local_distribution
    0 (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2) u g hu hlocal
    (standardMollifierBump n k) y
  have hy' : dist y 0 < greenCutoffInnerRadius R r₀ G + 2 * r₀ := by
    simpa only [greenCutoffDomain, mem_ball] using hy
  have hk := standardMollifierRadius_le_one k
  change dist y 0 < greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2 -
    standardMollifierRadius k
  linarith

/-- The standard positive mollifications have uniformly capped Laplacians and their
Laplacians converge almost everywhere on the Green cutoff domain. -/
theorem standardMollification_green_laplacian_package
    (n : ℕ) (R r₀ G : ℝ)
    (u g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : Integrable u) (hg : Integrable g)
    (hlocal : HasLocalDistributionalLaplacian n
      (greenObstacleDomain n R r₀ G) u g)
    (B : ℝ)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B) :
    (∀ k y, y ∈ greenCutoffDomain n R r₀ G →
      ‖Laplacian.laplacian (standardMollification u k) y‖ ≤ B) ∧
    ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      y ∈ greenCutoffDomain n R r₀ G →
      Tendsto (fun k => Laplacian.laplacian (standardMollification u k) y)
        atTop (𝓝 (g y)) := by
  constructor
  · intro k y hy
    rw [standardMollification_laplacian_eq_on_greenCutoffDomain n R r₀ G u g
      hu hlocal k y hy]
    exact norm_convolution_le_of_ae_bound n
      ((standardMollifierBump n k).normed volume) g
      (standardMollifierBump n k).integrable_normed
      (standardMollifierBump n k).nonneg_normed
      (standardMollifierBump n k).integral_normed
      hg.aestronglyMeasurable B hBg y
  · have h := ae_tendsto_laplacian_mollification_on_ball
      0 (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2)
      (greenCutoffInnerRadius R r₀ G + 2 * r₀)
      (by linarith : greenCutoffInnerRadius R r₀ G + 2 * r₀ <
        greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2)
      u g hu hg.locallyIntegrable hlocal (standardMollifierBump n)
      (standardMollifierBump_tendsto_rOut n)
      ⟨2, standardMollifierBump_ratio n⟩
    simpa only [greenCutoffDomain, standardMollification] using h

/-- The full sequence consumed by the local Green-pairing theorem. -/
theorem exists_green_local_mollifiers
    (n : ℕ) (R r₀ G : ℝ)
    (u g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : Integrable u) (hu_comp : HasCompactSupport u)
    (hu_nonneg : ∀ y, 0 ≤ u y)
    (hg : Integrable g)
    (hlocal : HasLocalDistributionalLaplacian n
      (greenObstacleDomain n R r₀ G) u g)
    (B : ℝ)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))), ‖g y‖ ≤ B) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ k, ContDiff ℝ 2 (w k)) ∧
      (∀ k, HasCompactSupport (w k)) ∧
      (∀ k y, 0 ≤ w k y) ∧
      (∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        Tendsto (fun k => w k y) atTop (𝓝 (u y))) ∧
      (∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        y ∈ greenCutoffDomain n R r₀ G →
          ‖Laplacian.laplacian (w k) y‖ ≤ B) ∧
      (∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
        y ∈ greenCutoffDomain n R r₀ G →
          Tendsto (fun k => Laplacian.laplacian (w k) y) atTop (𝓝 (g y))) := by
  obtain ⟨hsmooth, hcomp, hnonneg, hlim⟩ :=
    standardMollification_basic u hu hu_comp hu_nonneg
  obtain ⟨hcap, hlimΔ⟩ :=
    standardMollification_green_laplacian_package n R r₀ G u g hu hg hlocal B hBg
  refine ⟨standardMollification u, ?_, hcomp, hnonneg, hlim, ?_, hlimΔ⟩
  · intro k
    exact (hsmooth k).of_le (by
      change (↑(2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  · intro k
    filter_upwards with y
    exact hcap k y


/-- Apply the mollifier package to the positive representative of a weak Dirichlet obstacle.
The whole-space source is the zero extension of `ρ-F`. -/
theorem exists_ballPositiveRepresentative_green_local_mollifiers
    (n : ℕ) (R r₀ G : ℝ)
    (U : DirichletSobolev.H01 (greenObstacleDomain (n + 1) R r₀ G))
    (F ρ : DirichletSobolev.L2D (greenObstacleDomain (n + 1) R r₀ G))
    (hU : 0 ≤ (U : DirichletSobolev.H1amb
      (greenObstacleDomain (n + 1) R r₀ G)) 0)
    (heq : ∀ V : DirichletSobolev.H01 (greenObstacleDomain (n + 1) R r₀ G),
      DirichletSobolev.laplaceBilin (greenObstacleDomain (n + 1) R r₀ G) U V =
        DirichletSobolev.l2Functional (greenObstacleDomain (n + 1) R r₀ G) (F - ρ) V)
    (B : ℝ)
    (hBg : ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
      ‖DirichletSobolev.ballComplementSourceExtension 0
        (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2) F ρ y‖ ≤ B) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin (n + 1)) → ℝ,
      (∀ k, ContDiff ℝ 2 (w k)) ∧
      (∀ k, HasCompactSupport (w k)) ∧
      (∀ k y, 0 ≤ w k y) ∧
      (∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
        Tendsto (fun k => w k y) atTop
          (𝓝 (DirichletSobolev.ballPositiveRepresentative 0
            (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2) U y))) ∧
      (∀ k, ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
        y ∈ greenCutoffDomain (n + 1) R r₀ G →
          ‖Laplacian.laplacian (w k) y‖ ≤ B) ∧
      (∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin (n + 1)))),
        y ∈ greenCutoffDomain (n + 1) R r₀ G →
          Tendsto (fun k => Laplacian.laplacian (w k) y) atTop
            (𝓝 (DirichletSobolev.ballComplementSourceExtension 0
              (greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2) F ρ y))) := by
  let S : ℝ := greenCutoffInnerRadius R r₀ G + 2 * r₀ + 2
  let u := DirichletSobolev.ballPositiveRepresentative 0 S U
  let g := DirichletSobolev.ballComplementSourceExtension 0 S F ρ
  have hu_int : Integrable u :=
    DirichletSobolev.ballPositiveRepresentative_integrable 0 S U hU
  have hu_comp : HasCompactSupport u :=
    DirichletSobolev.ballPositiveRepresentative_hasCompactSupport 0 S U
  have hu_nonneg : ∀ y, 0 ≤ u y :=
    DirichletSobolev.ballPositiveRepresentative_nonneg 0 S U
  have hg_int : Integrable g :=
    DirichletSobolev.ballComplementSourceExtension_integrable 0 S F ρ
  have hraw : HasLocalDistributionalLaplacian (n + 1)
      (greenObstacleDomain (n + 1) R r₀ G) u
      (fun y => ((ρ - F) y : ℝ)) :=
    DirichletSobolev.ballPositiveRepresentative_hasLocalDistributionalLaplacian_of_complement
      0 S U F ρ hU heq
  have hlocal : HasLocalDistributionalLaplacian (n + 1)
      (greenObstacleDomain (n + 1) R r₀ G) u g :=
    hraw.congr_ae_restrict _ measurableSet_ball _ _ _
      (DirichletSobolev.ballComplementSourceExtension_ae_eq_local 0 S F ρ).symm
  exact exists_green_local_mollifiers (n + 1) R r₀ G u g hu_int hu_comp hu_nonneg
    hg_int hlocal B hBg

end CenteredMaximal.Ball
