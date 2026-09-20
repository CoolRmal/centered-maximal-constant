/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.JumpGenerator
public import Mathlib.Analysis.Convex.Function

/-!
# Convex truncation increases the jump generator

A convex function of a potential has a jump generator at least as large as the corresponding
multiple of the generator of the potential itself. Concretely, if `F : ℝ → ℝ` admits a
subgradient `m` at the value `g x`, i.e.
`F (g x) + m * (y − g x) ≤ F y` for every `y : ℝ`,
then adding the subgradient inequality at `y = g (x + t e_j)` and at `y = g (x − t e_j)` cancels
the linear part against the `−2 g x` of the second difference and leaves

* `secondDiff_comp_le`: `m * secondDiff g j x t ≤ secondDiff (F ∘ g) j x t`,

which integrates against the nonnegative weight `|t|^{−(1+α)}` to

* `mul_le_jumpGen_comp`: `m * jumpGen α g x ≤ jumpGen α (F ∘ g) x`.

No differentiability of `F` is used; only the existence of one subgradient at the single point
`g x`. The corollary the project applies is

* `nonneg_jumpGen_comp_of_jumpGen_eq_zero`: where the generator of the potential vanishes — away
  from the origin, for the potentials at hand — the generator of the convex truncation is
  nonnegative, whatever the sign of `m`.

The truncation actually used is the positive part of an affine function, normalised by a positive
constant: the kernel `K₀ = (R/r − 1)₊ / (R − 1)` is `F ∘ G` with `G` the potential and
`F y = (2 π R y − 1)₊ / (R − 1)`. For this `F` the file records convexity
(`convexOn_posPart_affine`) and an explicit *nonnegative* subgradient at every point
(`subgradient_posPart_affine`), the slope being `a / c` above the kink and `0` below it.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace CenteredMaximal

variable {F : ℝ → ℝ} {g : (Fin 2 → ℝ) → ℝ} {m α : ℝ} {x : Fin 2 → ℝ}

/-! ### The pointwise inequality -/

/-- If `m` is a subgradient of `F` at `g x`, then the second difference of `F ∘ g` dominates `m`
times the second difference of `g`: add the subgradient inequality at `y = g (x + t e_j)` to the
one at `y = g (x − t e_j)`, whose linear parts sum to `m * secondDiff g j x t`. -/
theorem secondDiff_comp_le (hsub : ∀ y, F (g x) + m * (y - g x) ≤ F y) (j : Fin 2) (t : ℝ) :
    m * secondDiff g j x t ≤ secondDiff (F ∘ g) j x t := by
  have h₁ := hsub (g (x + t • Pi.single j 1))
  have h₂ := hsub (g (x - t • Pi.single j 1))
  simp only [secondDiff, Function.comp_apply]
  nlinarith [h₁, h₂]

/-- The pointwise inequality of `secondDiff_comp_le` multiplied by the nonnegative weight
`|t|^{−(1+α)}` of the jump generator. -/
theorem secondDiff_mul_rpow_comp_le (hsub : ∀ y, F (g x) + m * (y - g x) ≤ F y) (j : Fin 2)
    (t : ℝ) :
    m * (secondDiff g j x t * |t| ^ (-(1 + α))) ≤ secondDiff (F ∘ g) j x t * |t| ^ (-(1 + α)) := by
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (secondDiff_comp_le hsub j t)
    (Real.rpow_nonneg (abs_nonneg t) _)

/-! ### The inequality for the generator -/

/-- **Convex truncation increases the jump generator.** If `m` is a subgradient of `F` at `g x`
and both integrands are integrable, then `m * jumpGen α g x ≤ jumpGen α (F ∘ g) x`. -/
theorem mul_le_jumpGen_comp (hsub : ∀ y, F (g x) + m * (y - g x) ≤ F y)
    (hg : ∀ j, Integrable fun t : ℝ => secondDiff g j x t * |t| ^ (-(1 + α)))
    (hF : ∀ j, Integrable fun t : ℝ => secondDiff (F ∘ g) j x t * |t| ^ (-(1 + α))) :
    m * jumpGen α g x ≤ jumpGen α (F ∘ g) x := by
  rw [jumpGen, jumpGen, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [← integral_const_mul m fun t : ℝ => secondDiff g j x t * |t| ^ (-(1 + α))]
  exact integral_mono ((hg j).const_mul m) (hF j) fun t =>
    secondDiff_mul_rpow_comp_le hsub j t

/-- Where the generator of the potential vanishes, the generator of a convex function of the
potential is nonnegative, for any subgradient `m` — no sign condition on `m` is needed. -/
theorem nonneg_jumpGen_comp_of_jumpGen_eq_zero (hsub : ∀ y, F (g x) + m * (y - g x) ≤ F y)
    (hg : ∀ j, Integrable fun t : ℝ => secondDiff g j x t * |t| ^ (-(1 + α)))
    (hF : ∀ j, Integrable fun t : ℝ => secondDiff (F ∘ g) j x t * |t| ^ (-(1 + α)))
    (hzero : jumpGen α g x = 0) : 0 ≤ jumpGen α (F ∘ g) x := by
  have h := mul_le_jumpGen_comp hsub hg hF
  rwa [hzero, mul_zero] at h

/-! ### The truncation `y ↦ (a y − 1)₊ / c` -/

/-- The normalised positive part `y ↦ (a y − 1)₊ / c` of an affine function is convex, being the
maximum of two affine functions divided by `c > 0`. -/
theorem convexOn_posPart_affine {a c : ℝ} (hc : 0 < c) :
    ConvexOn ℝ Set.univ fun y => max (a * y - 1) 0 / c := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ p q hp hq hpq => ?_⟩
  have h₁ : p * (a * y₁ - 1) ≤ p * max (a * y₁ - 1) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hp
  have h₂ : q * (a * y₂ - 1) ≤ q * max (a * y₂ - 1) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hq
  have hm₁ : (0 : ℝ) ≤ max (a * y₁ - 1) 0 := le_max_right _ _
  have hm₂ : (0 : ℝ) ≤ max (a * y₂ - 1) 0 := le_max_right _ _
  have hkey : max (a * (p * y₁ + q * y₂) - 1) 0 ≤
      p * max (a * y₁ - 1) 0 + q * max (a * y₂ - 1) 0 := by
    refine max_le ?_ (by positivity)
    nlinarith [hpq]
  simp only [smul_eq_mul]
  calc max (a * (p * y₁ + q * y₂) - 1) 0 / c
      ≤ (p * max (a * y₁ - 1) 0 + q * max (a * y₂ - 1) 0) / c :=
        (div_le_div_iff_of_pos_right hc).2 hkey
    _ = p * (max (a * y₁ - 1) 0 / c) + q * (max (a * y₂ - 1) 0 / c) := by ring

/-- The normalised positive part `y ↦ (a y − 1)₊ / c` has a *nonnegative* subgradient at every
point when `a ≥ 0` and `c > 0`: the slope `a / c` above the kink `a y₀ = 1`, and the slope `0` on
or below it. Nonnegativity of the slope is what makes `mul_le_jumpGen_comp` usable at points where
the generator of the potential vanishes. -/
theorem subgradient_posPart_affine {a c y₀ : ℝ} (hc : 0 < c) (ha : 0 ≤ a) :
    ∃ m, 0 ≤ m ∧ ∀ y, max (a * y₀ - 1) 0 / c + m * (y - y₀) ≤ max (a * y - 1) 0 / c := by
  rcases le_or_gt (a * y₀ - 1) 0 with h | h
  · refine ⟨0, le_rfl, fun y => ?_⟩
    rw [max_eq_right h, zero_mul, zero_div, add_zero]
    positivity
  · refine ⟨a / c, by positivity, fun y => ?_⟩
    have hL : (a * y₀ - 1) / c + a / c * (y - y₀) = (a * y - 1) / c := by
      field_simp
      ring
    rw [max_eq_left h.le, hL, div_le_div_iff_of_pos_right hc]
    exact le_max_left _ _

end CenteredMaximal

end
