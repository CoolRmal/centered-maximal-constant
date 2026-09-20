/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Transfer.Commutation
public import CenteredMaximal.Transfer.Scaling
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Transferring the obstacle equation against a generator density of infinite mass

`CenteredMaximal.Transfer.Commutation` transfers the obstacle equation through a convolution under
the assumption that the generator of the kernel is represented by a *finite* measure minus a point
mass at the origin, `A K = β − a δ₀`. For a fractional order `α` the generator of the kernels we
use behaves like `|y|^{−2α}` at the origin, which is not locally integrable in the plane, so
neither `β` nor `a` exists separately. This file redoes the transfer for the merged form

`∫ K(x) A ψ(x) dx = ∫ g(y) (ψ(y) − ψ(0)) dy`,

with `g ≥ 0` measurable on the plane. The pairing on the right converges absolutely as soon as

`∫ g(y) min(1, ‖y‖) dy < ∞`                                   (`hgmom` below),

because a test function satisfies `|ψ(y + x) − ψ(x)| ≤ C min(1, ‖y‖)` uniformly in `x`
(`IsTestFunction.exists_bound_min_one`). The form subsumes the finite-mass one: if `g` is
integrable then `∫ g (ψ − ψ 0) = (∫ g ψ) − (∫ g) ψ 0`, i.e. `β = g · volume` and `a = ∫ g`
(`hKgen_fp_of_integrable`).

The `β`-term and the `a u` term of `Commutation.lean` merge into the single term
`x ↦ ∫ g(z) (u(x − z) − u(x)) dz`, which is finite exactly because the two divergent halves are
kept together. Its local integrability is not automatic, and it is what the second hypothesis

`∀ w test, Integrable ((x, z) ↦ g z ((u (x − z) − u x) w x))`  (`hgconv` below)

supplies; it is also what justifies the Fubini interchange in the self-adjointness step. At a point
where `u` vanishes the merged term is `∫ g(z) u(x − z) dz ≥ 0`, which is all the final bound needs.

* `IsTestFunction.exists_lipschitz_bound`, `IsTestFunction.exists_bound_min_one`: the uniform
  increment bounds for a test function, from the mean value inequality applied to its derivative
  (continuous with compact support, hence bounded);
* `integrable_density_mul_sub`, `integrable_mul_min_one_of_pairing`: the pairing
  `∫ g (ψ − ψ 0)` converges absolutely for every test function `ψ` if and only if the moment
  condition holds, so `hgmom` and the hypothesis `hgint` of the finite-mass form are equivalent;
* `integrable_prod_mul_density`, `integral_mul_integral_density`: convolution against the density
  in the merged form is self-adjoint for the pairing with a test function, the Fubini interchanges
  being dominated by `|u x| · g z min(1, ‖z‖)`;
* `integrable_density_conv_mul`, `locallyIntegrable_density_conv`: the merged convolution is
  locally integrable, by multiplying with a bump function that is `1` on a ball;
* `convolution_source_eq_fp`: the transfer identity
  `∫ (K ⋆ f) φ = ∫ (K ⋆ σ) φ − ∫ (g ⊛ u) φ`, with no point-mass term;
* `convolution_le_of_eq_zero_fp`: the pointwise bound `K ⋆ f ≤ κ ∫ K` at almost every point
  where `u` vanishes;
* `integral_dilate_mul_jumpGen`, `exists_gen_dilate_fp`: the density form survives dilation, with
  `g_s(y) = s^{−2−α} g(s⁻¹ y)`; `exists_gen_dilate_moment_fp` carries the moment condition along,
  as the chaining into `convolution_le_of_eq_zero_fp` needs it.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace CenteredMaximal

variable {K u σ f g φ : (Fin 2 → ℝ) → ℝ} {α κ : ℝ}

/-! ### Uniform increment bounds for a test function -/

/-- **A test function is globally Lipschitz.** Its derivative is continuous with compact support,
hence bounded, and the mean value inequality turns that bound into a Lipschitz constant. -/
theorem IsTestFunction.exists_lipschitz_bound (hφ : IsTestFunction φ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x z : Fin 2 → ℝ, |φ (z + x) - φ x| ≤ L * ‖z‖ := by
  obtain ⟨L, hL⟩ := (hφ.contDiff_two.continuous_fderiv
    (by norm_num)).bounded_above_of_compact_support (hφ.2.fderiv (𝕜 := ℝ))
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hlip : LipschitzWith L.toNNReal φ :=
    lipschitzWith_of_nnnorm_fderiv_le (hφ.contDiff_two.differentiable (by norm_num)) fun y => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal L hL0]
      exact hL y
  refine ⟨L, hL0, fun x z => ?_⟩
  have h := hlip.dist_le_mul (z + x) x
  rwa [Real.dist_eq, dist_eq_norm, add_sub_cancel_right, Real.coe_toNNReal L hL0] at h

/-- **The uniform increment bound for a test function**: `|φ (z + x) − φ x| ≤ C min(1, ‖z‖)`, with
`C` independent of the base point `x`. The Lipschitz bound is used for `‖z‖ ≤ 1` and the sup bound
for `‖z‖ ≥ 1`. This is the bound that makes the pairing with a generator density converge. -/
theorem IsTestFunction.exists_bound_min_one (hφ : IsTestFunction φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x z : Fin 2 → ℝ, |φ (z + x) - φ x| ≤ C * min 1 ‖z‖ := by
  obtain ⟨M, hM⟩ := hφ.continuous.bounded_above_of_compact_support hφ.2
  obtain ⟨L, hL0, hL⟩ := hφ.exists_lipschitz_bound
  refine ⟨max (2 * M) L, le_max_of_le_right hL0, fun x z => ?_⟩
  rcases le_total ‖z‖ 1 with h | h
  · rw [min_eq_right h]
    exact (hL x z).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · rw [min_eq_left h, mul_one]
    refine le_trans ?_ (le_max_left (2 * M) L)
    obtain ⟨h₁, h₂⟩ := abs_le.1 (hM (z + x))
    obtain ⟨h₃, h₄⟩ := abs_le.1 (hM x)
    rw [abs_le]
    constructor <;> linarith

/-! ### The pairing with a generator density -/

/-- **The pairing of a density against the increments of a test function converges absolutely.**
This is the hypothesis `hgint` of the finite-mass version, derived here from the moment condition
`∫ g(z) min(1, ‖z‖) dz < ∞`. -/
theorem integrable_density_mul_sub (hgm : Measurable g) (hg₀ : ∀ z, 0 ≤ g z)
    (hgmom : Integrable fun z => g z * min 1 ‖z‖) (hφ : IsTestFunction φ) :
    Integrable fun z => g z * (φ z - φ 0) := by
  obtain ⟨C, _hC0, hC⟩ := hφ.exists_bound_min_one
  refine (hgmom.const_mul C).mono' (hgm.aestronglyMeasurable.mul
    ((hφ.continuous.sub continuous_const).aestronglyMeasurable))
    (Filter.Eventually.of_forall fun z => ?_)
  have hz : |φ z - φ 0| ≤ C * min 1 ‖z‖ := by
    have h := hC 0 z
    rwa [add_zero] at h
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hg₀ z)]
  calc g z * |φ z - φ 0| ≤ g z * (C * min 1 ‖z‖) := mul_le_mul_of_nonneg_left hz (hg₀ z)
    _ = C * (g z * min 1 ‖z‖) := by ring

/-- **The moment condition follows from the absolute convergence of every pairing.** Conversely to
`integrable_density_mul_sub`: if `∫ g (ψ − ψ 0)` converges absolutely for *every* test function
`ψ`, then `∫ g(z) min(1, ‖z‖) dz < ∞`.

Test against the coordinate functions cut off by a bump `χ` that is `1` on the unit ball, and
against `χ` itself: this bounds `∫ g χ |z j|` for `j = 0, 1` and `∫ g |χ − 1|`, and
`min(1, ‖z‖) ≤ χ(z) (|z₀| + |z₁|) + |χ(z) − 1|` because `‖z‖ ≤ |z₀| + |z₁|`, the first summand
carrying the bound near the origin and the second the bound at infinity. -/
theorem integrable_mul_min_one_of_pairing (hgm : Measurable g) (hg₀ : ∀ z, 0 ≤ g z)
    (hgint : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      Integrable fun z => g z * (ψ z - ψ 0)) :
    Integrable fun z => g z * min 1 ‖z‖ := by
  obtain ⟨χ, hχ, hχ₀, hχ₁⟩ := exists_isTestFunction_eq_one_of_isCompact
    (isCompact_closedBall (0 : Fin 2 → ℝ) 1)
  have hχ0 : χ 0 = 1 := hχ₁ 0 (Metric.mem_closedBall_self zero_le_one)
  have hcoord : ∀ j : Fin 2, IsTestFunction fun z : Fin 2 → ℝ => z j * χ z := fun j =>
    ⟨(contDiff_apply ℝ ℝ j).mul hχ.1, hχ.2.mul_left⟩
  have hA : ∀ j : Fin 2, Integrable fun z : Fin 2 → ℝ => |g z * (z j * χ z)| := fun j => by
    have h := hgint _ (hcoord j)
    simp only [Pi.zero_apply, zero_mul, sub_zero] at h
    exact h.abs
  have hB : Integrable fun z : Fin 2 → ℝ => |g z * (χ z - 1)| := by
    have h := hgint χ hχ
    rw [hχ0] at h
    exact h.abs
  have hnorm : ∀ z : Fin 2 → ℝ, ‖z‖ ≤ |z 0| + |z 1| := fun z => by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · rw [Real.norm_eq_abs]; linarith [abs_nonneg (z 1)]
    · rw [Real.norm_eq_abs]; linarith [abs_nonneg (z 0)]
  refine ((hA 0).fun_add ((hA 1).fun_add hB)).mono' (hgm.aestronglyMeasurable.mul
    (continuous_const.min continuous_norm).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun z => ?_)
  have hmin : (0 : ℝ) ≤ min 1 ‖z‖ := le_min zero_le_one (norm_nonneg z)
  have key : min 1 ‖z‖ ≤ χ z * |z 0| + (χ z * |z 1| + |χ z - 1|) := by
    rcases le_total ‖z‖ 1 with h | h
    · have hz1 : χ z = 1 := hχ₁ z (mem_closedBall_zero_iff.2 h)
      rw [hz1]
      simp only [one_mul, sub_self, abs_zero, add_zero]
      exact (min_le_right _ _).trans (hnorm z)
    · have h1 : (1 : ℝ) ≤ |z 0| + |z 1| := h.trans (hnorm z)
      have h2 : 1 - χ z ≤ |χ z - 1| := by rw [abs_sub_comm]; exact le_abs_self _
      have h3 : χ z * 1 ≤ χ z * (|z 0| + |z 1|) := mul_le_mul_of_nonneg_left h1 (hχ₀ z)
      calc min 1 ‖z‖ ≤ 1 := min_le_left _ _
        _ ≤ χ z * |z 0| + (χ z * |z 1| + |χ z - 1|) := by nlinarith [h2, h3]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hg₀ z) hmin)]
  calc g z * min 1 ‖z‖ ≤ g z * (χ z * |z 0| + (χ z * |z 1| + |χ z - 1|)) :=
        mul_le_mul_of_nonneg_left key (hg₀ z)
    _ = |g z * (z 0 * χ z)| + (|g z * (z 1 * χ z)| + |g z * (χ z - 1)|) := by
        simp only [abs_mul, abs_of_nonneg (hg₀ z), abs_of_nonneg (hχ₀ z)]
        ring

/-- The integrand of the self-adjointness step is integrable on the product: it is dominated by
`C |u x| · g z min(1, ‖z‖)`, a product of integrable functions. -/
theorem integrable_prod_mul_density (huint : Integrable u) (hgm : Measurable g)
    (hg₀ : ∀ z, 0 ≤ g z) (hgmom : Integrable fun z => g z * min 1 ‖z‖) (hφ : IsTestFunction φ) :
    Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      u p.1 * (g p.2 * (φ (p.2 + p.1) - φ p.1))) (volume.prod volume) := by
  obtain ⟨C, _hC0, hC⟩ := hφ.exists_bound_min_one
  refine ((huint.abs.mul_prod hgmom).const_mul C).mono' ((huint.aestronglyMeasurable.comp_fst).mul
    (((hgm.comp measurable_snd).aestronglyMeasurable).mul
      (((hφ.continuous.comp (continuous_snd.add continuous_fst)).sub
        (hφ.continuous.comp continuous_fst)).aestronglyMeasurable)))
    (Filter.Eventually.of_forall fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hg₀ p.2)]
  calc |u p.1| * (g p.2 * |φ (p.2 + p.1) - φ p.1|)
      ≤ |u p.1| * (g p.2 * (C * min 1 ‖p.2‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC p.1 p.2) (hg₀ p.2))
          (abs_nonneg _)
    _ = C * (|u p.1| * (g p.2 * min 1 ‖p.2‖)) := by ring

/-- **Self-adjointness of the pairing with a generator density.** For an integrable `u` and a test
function `φ`,
`∫ u(x) (∫ g(z) (φ(z + x) − φ(x)) dz) dx = ∫ (∫ g(z) (u(x − z) − u(x)) dz) φ(x) dx`.

Both sides equal `∫ g(z) (∫ (u(x − z) − u(x)) φ(x) dx) dz`: the first interchange is dominated by
`|u x| · g z min(1, ‖z‖)` and the second is the hypothesis `hgconv`. The inner integral is computed
by translation invariance, as in the finite-measure case. -/
theorem integral_mul_integral_density (huint : Integrable u) (hgm : Measurable g)
    (hg₀ : ∀ z, 0 ≤ g z) (hgmom : Integrable fun z => g z * min 1 ‖z‖)
    (hgconv : Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      g p.2 * ((u (p.1 - p.2) - u p.1) * φ p.1)) (volume.prod volume))
    (hφ : IsTestFunction φ) :
    (∫ x, u x * ∫ z, g z * (φ (z + x) - φ x))
      = ∫ x, (∫ z, g z * (u (x - z) - u x)) * φ x := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφ.2
  have hbd : ∀ᵐ x : Fin 2 → ℝ, ‖φ x‖ ≤ C := Filter.Eventually.of_forall hC
  have huφ0 : Integrable fun x => u x * φ x :=
    huint.mul_bdd hφ.continuous.aestronglyMeasurable hbd
  have huφ : ∀ z : Fin 2 → ℝ, Integrable fun x => u (x - z) * φ x := fun z =>
    (huint.comp_sub_right z).mul_bdd hφ.continuous.aestronglyMeasurable hbd
  have hinner : ∀ z : Fin 2 → ℝ, (∫ x, u x * (g z * (φ (z + x) - φ x)))
      = g z * ∫ x, (u (x - z) - u x) * φ x := fun z => by
    have hA : Integrable fun x : Fin 2 → ℝ => u x * φ (z + x) :=
      huint.mul_bdd ((hφ.continuous.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => hC _)
    have hshift : (∫ x, u x * φ (z + x)) = ∫ x, u (x - z) * φ x := by
      have h := integral_sub_right_eq_self (μ := (volume : Measure (Fin 2 → ℝ)))
        (fun x => u x * φ (z + x)) z
      have hz : ∀ x : Fin 2 → ℝ, z + (x - z) = x := fun x => by abel
      rw [← h]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hz])
    calc (∫ x, u x * (g z * (φ (z + x) - φ x)))
        = ∫ x, g z * (u x * φ (z + x) - u x * φ x) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = g z * ∫ x, (u x * φ (z + x) - u x * φ x) := integral_const_mul _ _
      _ = g z * ((∫ x, u x * φ (z + x)) - ∫ x, u x * φ x) := by rw [integral_sub hA huφ0]
      _ = g z * ((∫ x, u (x - z) * φ x) - ∫ x, u x * φ x) := by rw [hshift]
      _ = g z * ∫ x, (u (x - z) - u x) * φ x := by
          rw [← integral_sub (huφ z) huφ0]
          exact congrArg _ (integral_congr_ae (Filter.Eventually.of_forall fun x => by ring))
  calc (∫ x, u x * ∫ z, g z * (φ (z + x) - φ x))
      = ∫ x, ∫ z, u x * (g z * (φ (z + x) - φ x)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => (integral_const_mul (u x) _).symm)
    _ = ∫ z, ∫ x, u x * (g z * (φ (z + x) - φ x)) :=
        integral_integral_swap (integrable_prod_mul_density huint hgm hg₀ hgmom hφ)
    _ = ∫ z, g z * ∫ x, (u (x - z) - u x) * φ x :=
        integral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = ∫ z, ∫ x, g z * ((u (x - z) - u x) * φ x) :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => (integral_const_mul (g z) _).symm)
    _ = ∫ x, ∫ z, g z * ((u (x - z) - u x) * φ x) := integral_integral_swap hgconv.swap
    _ = ∫ x, (∫ z, g z * (u (x - z) - u x)) * φ x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by
          show (∫ z, g z * ((u (x - z) - u x) * φ x))
            = (∫ z, g z * (u (x - z) - u x)) * φ x
          rw [← integral_mul_const]
          exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring))

/-! ### Local integrability of the merged convolution -/

/-- The merged convolution, multiplied by a test function, is integrable: this is `hgconv` read
through `Integrable.integral_prod_left`. -/
theorem integrable_density_conv_mul
    (hgconv : Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      g p.2 * ((u (p.1 - p.2) - u p.1) * φ p.1)) (volume.prod volume)) :
    Integrable fun x => (∫ z, g z * (u (x - z) - u x)) * φ x := by
  refine hgconv.integral_prod_left.congr (Filter.Eventually.of_forall fun x => ?_)
  show (∫ z, g z * ((u (x - z) - u x) * φ x)) = (∫ z, g z * (u (x - z) - u x)) * φ x
  rw [← integral_mul_const]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)

/-- A test function equal to `1` on the unit ball around a given point: a `ContDiffBump` with
inner radius `1` and outer radius `2`. -/
private theorem exists_isTestFunction_eq_one (x₀ : Fin 2 → ℝ) :
    ∃ w : (Fin 2 → ℝ) → ℝ, IsTestFunction w ∧ ∀ x ∈ Metric.ball x₀ 1, w x = 1 := by
  let b : ContDiffBump x₀ := ⟨1, 2, one_pos, one_lt_two⟩
  exact ⟨b, ⟨b.contDiff, b.hasCompactSupport⟩,
    fun x hx => b.one_of_mem_closedBall (Metric.ball_subset_closedBall hx)⟩

/-- **The merged convolution is locally integrable.** Around a given point, multiply by a bump
function that is `1` on the unit ball: `hgconv` makes the product integrable, and on the ball the
product agrees with the merged convolution. -/
theorem locallyIntegrable_density_conv
    (hgconv : ∀ w : (Fin 2 → ℝ) → ℝ, IsTestFunction w →
      Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        g p.2 * ((u (p.1 - p.2) - u p.1) * w p.1)) (volume.prod volume)) :
    LocallyIntegrable (fun x => ∫ z, g z * (u (x - z) - u x)) volume := by
  intro x₀
  obtain ⟨w, hw, hw1⟩ := exists_isTestFunction_eq_one x₀
  refine ⟨Metric.ball x₀ 1, Metric.ball_mem_nhds _ one_pos, ?_⟩
  refine ((integrable_density_conv_mul (hgconv w hw)).integrableOn).congr_fun
    (fun x hx => ?_) measurableSet_ball
  show (∫ z, g z * (u (x - z) - u x)) * w x = ∫ z, g z * (u (x - z) - u x)
  rw [hw1 x hx, mul_one]

/-! ### The transfer identity -/

/-- **The transfer identity against a generator density.** Assume `A u = σ − f` and
`∫ K A ψ = ∫ g (ψ − ψ 0)` weakly, for the jump generator `A = jumpGen α` with `0 < α < 2` and an
even integrable kernel `K` with compact support. Then for every test function `φ`,
`∫ (K ⋆ f) φ = ∫ (K ⋆ σ) φ − ∫ (∫ g(z) (u(· − z) − u(·)) dz) φ`.

Test the obstacle equation against `K ⋆ φ`. On the left, `A (K ⋆ φ) (x)` equals
`∫ K(y) Aφ(y + x) dy` by evenness of `K`, which is `∫ g(z) (φ(z + x) − φ(x)) dz` by the generator
identity applied to the translate `z ↦ φ (z + x)`; self-adjointness then moves the density
convolution onto `u`. On the right, convolution moves onto `σ − f`. Compared with the finite-mass
version there is no `a ∫ u φ` term: it has merged into the density term. -/
theorem convolution_source_eq_fp (hα : 0 < α) (hα' : α < 2) (hKint : Integrable K)
    (hKeven : ∀ z, K (-z) = K z) (hKsupp : HasCompactSupport K) (_hum : Measurable u)
    (huint : Integrable u) (hσint : Integrable σ) (hfint : Integrable f) (hgm : Measurable g)
    (hg₀ : ∀ z, 0 ≤ g z) (hgmom : Integrable fun z => g z * min 1 ‖z‖)
    (hgconv : Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      g p.2 * ((u (p.1 - p.2) - u p.1) * φ p.1)) (volume.prod volume))
    (hu : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, u x * jumpGen α ψ x) = ∫ x, (σ x - f x) * ψ x)
    (hKgen : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, K x * jumpGen α ψ x) = ∫ y, g y * (ψ y - ψ 0))
    (hφ : IsTestFunction φ) :
    (∫ x, (∫ y, K y * f (x - y)) * φ x)
      = (∫ x, (∫ y, K y * σ (x - y)) * φ x) - ∫ x, (∫ z, g z * (u (x - z) - u x)) * φ x := by
  have hψ : IsTestFunction fun z : Fin 2 → ℝ => ∫ y, K y * φ (z - y) :=
    isTestFunction_convolution hKint hKsupp hφ
  obtain ⟨D, hD⟩ := hψ.continuous.bounded_above_of_compact_support hψ.2
  have hstar : ∀ x : Fin 2 → ℝ,
      (∫ y, K y * jumpGen α φ (y + x)) = ∫ z, g z * (φ (z + x) - φ x) := fun x => by
    have h := hKgen (fun z => φ (z + x)) (hφ.comp_add_right x)
    simp only [zero_add] at h
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)) h
    rw [jumpGen_comp_add_right α φ x y]
  have hgen : ∀ x : Fin 2 → ℝ, jumpGen α (fun z => ∫ y, K y * φ (z - y)) x
      = ∫ z, g z * (φ (z + x) - φ x) := fun x => by
    rw [jumpGen_convolution hα hα' hKint hφ]
    calc (∫ y, K y * jumpGen α φ (x - y))
        = ∫ y, K (-y) * jumpGen α φ (-y + x) :=
          integral_congr_ae (Filter.Eventually.of_forall fun y => by
            dsimp only
            rw [hKeven, show -y + x = x - y from by abel])
      _ = ∫ y, K y * jumpGen α φ (y + x) :=
          integral_neg_eq_self (fun y => K y * jumpGen α φ (y + x)) volume
      _ = ∫ z, g z * (φ (z + x) - φ x) := hstar x
  have h1 : (∫ x, u x * jumpGen α (fun z => ∫ y, K y * φ (z - y)) x)
      = ∫ x, (σ x - f x) * ∫ y, K y * φ (x - y) := hu _ hψ
  have hLHS : (∫ x, u x * jumpGen α (fun z => ∫ y, K y * φ (z - y)) x)
      = ∫ x, (∫ z, g z * (u (x - z) - u x)) * φ x := by
    rw [← integral_mul_integral_density huint hgm hg₀ hgmom hgconv hφ]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hgen])
  have hJ₁ : Integrable fun x : Fin 2 → ℝ => σ x * ∫ y, K y * φ (x - y) :=
    hσint.mul_bdd hψ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hD)
  have hJ₂ : Integrable fun x : Fin 2 → ℝ => f x * ∫ y, K y * φ (x - y) :=
    hfint.mul_bdd hψ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hD)
  have hRHS : (∫ x, (σ x - f x) * ∫ y, K y * φ (x - y))
      = (∫ x, (∫ y, K y * σ (x - y)) * φ x) - ∫ x, (∫ y, K y * f (x - y)) * φ x := by
    calc (∫ x, (σ x - f x) * ∫ y, K y * φ (x - y))
        = ∫ x, ((σ x * ∫ y, K y * φ (x - y)) - f x * ∫ y, K y * φ (x - y)) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = (∫ x, σ x * ∫ y, K y * φ (x - y)) - ∫ x, f x * ∫ y, K y * φ (x - y) :=
          integral_sub hJ₁ hJ₂
      _ = (∫ x, (∫ y, K y * σ (x - y)) * φ x) - ∫ x, (∫ y, K y * f (x - y)) * φ x := by
          rw [integral_mul_convolution_comm hKint hKeven hσint hφ,
            integral_mul_convolution_comm hKint hKeven hfint hφ]
  linarith [h1, hLHS, hRHS]

/-- **The pointwise bound.** Under the hypotheses of `convolution_source_eq_fp`, with in addition
`0 ≤ u`, `0 ≤ σ ≤ κ` and `0 ≤ K`, at almost every point where `u` vanishes one has
`K ⋆ f ≤ κ ∫ K`.

The transfer identity says that the locally integrable functions `K ⋆ f` and
`K ⋆ σ − ∫ g(z) (u(· − z) − u(·)) dz` have the same integral against every test function, hence
agree almost everywhere. At a point where `u` vanishes the density term is `∫ g(z) u(x − z) dz ≥ 0`
because `g ≥ 0` and `u ≥ 0`, and `K ⋆ σ ≤ κ ∫ K` because `0 ≤ σ ≤ κ` and `K ≥ 0`. -/
theorem convolution_le_of_eq_zero_fp (hα : 0 < α) (hα' : α < 2) (hK₀ : ∀ z, 0 ≤ K z)
    (hKint : Integrable K) (hKeven : ∀ z, K (-z) = K z) (hKsupp : HasCompactSupport K)
    (hum : Measurable u) (huint : Integrable u) (hu₀ : ∀ x, 0 ≤ u x) (hσm : Measurable σ)
    (hσint : Integrable σ) (hσ₀ : ∀ x, 0 ≤ σ x) (hσκ : ∀ x, σ x ≤ κ) (hfint : Integrable f)
    (hgm : Measurable g) (hg₀ : ∀ z, 0 ≤ g z) (hgmom : Integrable fun z => g z * min 1 ‖z‖)
    (hgconv : ∀ w : (Fin 2 → ℝ) → ℝ, IsTestFunction w →
      Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
        g p.2 * ((u (p.1 - p.2) - u p.1) * w p.1)) (volume.prod volume))
    (hu : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, u x * jumpGen α ψ x) = ∫ x, (σ x - f x) * ψ x)
    (hKgen : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, K x * jumpGen α ψ x) = ∫ y, g y * (ψ y - ψ 0)) :
    ∀ᵐ x : Fin 2 → ℝ, u x = 0 → (∫ y, K y * f (x - y)) ≤ κ * ∫ y, K y := by
  have hae : ∀ᵐ x : Fin 2 → ℝ, (∫ y, K y * f (x - y))
      = (∫ y, K y * σ (x - y)) - ∫ z, g z * (u (x - z) - u x) := by
    have hL1 : LocallyIntegrable (fun x : Fin 2 → ℝ => ∫ y, K y * f (x - y)) volume :=
      (integrable_kernel_conv hKint hfint).locallyIntegrable
    have hL2 : LocallyIntegrable (fun x : Fin 2 → ℝ =>
        (∫ y, K y * σ (x - y)) - ∫ z, g z * (u (x - z) - u x)) volume :=
      (integrable_kernel_conv hKint hσint).locallyIntegrable.sub
        (locallyIntegrable_density_conv hgconv)
    refine ae_eq_of_integral_contDiff_smul_eq hL1 hL2 fun w hw hwc => ?_
    have hwt : IsTestFunction w := ⟨hw, hwc⟩
    obtain ⟨Cw, hCw⟩ := hwt.continuous.bounded_above_of_compact_support hwt.2
    have h1 : Integrable fun x : Fin 2 → ℝ => (∫ y, K y * σ (x - y)) * w x :=
      (integrable_kernel_conv hKint hσint).mul_bdd hwt.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall hCw)
    have h2 : Integrable fun x : Fin 2 → ℝ => (∫ z, g z * (u (x - z) - u x)) * w x :=
      integrable_density_conv_mul (hgconv w hwt)
    have hR : (∫ x, w x * ((∫ y, K y * σ (x - y)) - ∫ z, g z * (u (x - z) - u x)))
        = (∫ x, (∫ y, K y * σ (x - y)) * w x) - ∫ x, (∫ z, g z * (u (x - z) - u x)) * w x := by
      calc (∫ x, w x * ((∫ y, K y * σ (x - y)) - ∫ z, g z * (u (x - z) - u x)))
          = ∫ x, ((∫ y, K y * σ (x - y)) * w x - (∫ z, g z * (u (x - z) - u x)) * w x) :=
            integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
        _ = (∫ x, (∫ y, K y * σ (x - y)) * w x) - ∫ x, (∫ z, g z * (u (x - z) - u x)) * w x :=
            integral_sub h1 h2
    simp only [smul_eq_mul]
    rw [hR, integral_congr_ae (Filter.Eventually.of_forall fun x =>
      mul_comm (w x) (∫ y, K y * f (x - y)))]
    exact convolution_source_eq_fp hα hα' hKint hKeven hKsupp hum huint hσint hfint hgm hg₀
      hgmom
      (hgconv w hwt) hu hKgen hwt
  filter_upwards [hae] with x hx hux
  have h1 : (∫ y, K y * σ (x - y)) ≤ κ * ∫ y, K y := by
    have hi1 : Integrable fun y : Fin 2 → ℝ => K y * σ (x - y) :=
      hKint.mul_bdd ((hσm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hσ₀ _)]
          exact hσκ _)
    calc (∫ y, K y * σ (x - y)) ≤ ∫ y, K y * κ :=
          integral_mono hi1 (hKint.mul_const κ) fun y =>
            mul_le_mul_of_nonneg_left (hσκ _) (hK₀ y)
      _ = κ * ∫ y, K y := by rw [integral_mul_const]; ring
  have h2 : (0 : ℝ) ≤ ∫ z, g z * (u (x - z) - u x) :=
    integral_nonneg fun z => mul_nonneg (hg₀ z) (by rw [hux]; simpa using hu₀ (x - z))
  rw [hx]
  linarith

/-! ### Two sufficient forms of the hypotheses -/

/-- **The finite-mass generator identity is a special case.** If `g` is integrable then
`∫ g (ψ − ψ 0) = (∫ g ψ) − (∫ g) ψ 0`, so the density form subsumes the representation by the
finite measure `g · volume` and the point mass `∫ g` at the origin. -/
theorem hKgen_fp_of_integrable (hgint : Integrable g) (hφ : IsTestFunction φ) :
    (∫ y, g y * (φ y - φ 0)) = (∫ y, g y * φ y) - (∫ y, g y) * φ 0 := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφ.2
  have hA : Integrable fun y : Fin 2 → ℝ => g y * φ y :=
    hgint.mul_bdd hφ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hC)
  have hB : Integrable fun y : Fin 2 → ℝ => g y * φ 0 := hgint.mul_const _
  calc (∫ y, g y * (φ y - φ 0)) = ∫ y, (g y * φ y - g y * φ 0) :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    _ = (∫ y, g y * φ y) - ∫ y, g y * φ 0 := integral_sub hA hB
    _ = (∫ y, g y * φ y) - (∫ y, g y) * φ 0 := by rw [integral_mul_const]

/-- A sufficient form of `hgconv`: if the merged integrand is integrable on the whole product,
then so is its product with any test function, since a test function is bounded. -/
theorem hgconv_of_integrable_prod (hgconv : Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      g p.2 * (u (p.1 - p.2) - u p.1)) (volume.prod volume))
    (hφ : IsTestFunction φ) :
    Integrable (fun p : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      g p.2 * ((u (p.1 - p.2) - u p.1) * φ p.1)) (volume.prod volume) := by
  obtain ⟨C, hC⟩ := hφ.continuous.bounded_above_of_compact_support hφ.2
  refine (hgconv.mul_bdd ((hφ.continuous.comp continuous_fst).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun p => hC p.1)).congr
    (Filter.Eventually.of_forall fun p => by simp only [Function.comp_apply]; ring)

/-! ### Dilation of the density form -/

/-- The elementary rewriting `s^{−2−α} = (s²)⁻¹ s^{−α}` of the dilation exponent. -/
private theorem rpow_neg_two_sub {s : ℝ} (hs : 0 < s) (α : ℝ) :
    s ^ (-2 - α) = (s ^ 2)⁻¹ * s ^ (-α) := by
  rw [show (-2 - α : ℝ) = -2 + -α by ring, Real.rpow_add hs, Real.rpow_neg hs.le, Real.rpow_two]

/-- **The pairing identity for a dilated kernel.** For `s > 0` the dilation `K_s` is represented by
the dilated density `g_s(y) = s^{−2−α} g(s⁻¹ y)`: the factor `s^{−α}` comes from the scaling law of
the generator (`jumpGen_dilate_eq`) and the factor `(s²)⁻¹` from the substitution `y = s • z`,
whose Jacobian is `s²`. -/
theorem integral_dilate_mul_jumpGen {s : ℝ} (hs : 0 < s) (hK : Integrable K)
    (hKgen : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, K x * jumpGen α ψ x) = ∫ y, g y * (ψ y - ψ 0))
    (hφ : IsTestFunction φ) :
    (∫ x, dilate K s x * jumpGen α φ x)
      = ∫ y, s ^ (-2 - α) * g (s⁻¹ • y) * (φ y - φ 0) := by
  have hcov : (∫ z, g z * (φ (s • z) - φ 0))
      = (s ^ 2)⁻¹ * ∫ y, g (s⁻¹ • y) * (φ y - φ 0) := by
    have h := Measure.integral_comp_smul (volume : Measure (Fin 2 → ℝ))
      (fun y => g (s⁻¹ • y) * (φ y - φ 0)) s
    simpa only [inv_smul_smul₀ hs.ne', Module.finrank_fin_fun, smul_eq_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (s ^ 2)⁻¹)] using h
  have hgen := hKgen (fun z => φ (s • z)) (hφ.comp_smul hs.ne')
  simp only [smul_zero] at hgen
  calc (∫ x, dilate K s x * jumpGen α φ x)
      = s ^ (-α) * ∫ y, K y * jumpGen α (fun z => φ (s • z)) y :=
        jumpGen_dilate_eq hs K hK φ hφ
    _ = s ^ (-α) * ((s ^ 2)⁻¹ * ∫ y, g (s⁻¹ • y) * (φ y - φ 0)) := by rw [hgen, hcov]
    _ = ∫ y, s ^ (-2 - α) * (g (s⁻¹ • y) * (φ y - φ 0)) := by
        rw [integral_const_mul, rpow_neg_two_sub hs α]; ring
    _ = ∫ y, s ^ (-2 - α) * g (s⁻¹ • y) * (φ y - φ 0) :=
        integral_congr_ae (Filter.Eventually.of_forall fun y => (mul_assoc _ _ _).symm)

/-- **The density form survives dilation.** If the kernel `K` represents the generator of order `α`
against the density `g`, then so does every dilation `K_s`, against `g_s(y) = s^{−2−α} g(s⁻¹ y)`.
This is the analogue of `exists_gen_dilate` for a density of possibly infinite mass. -/
theorem exists_gen_dilate_fp (_hα : 0 < α) (hK : Integrable K) (hgm : Measurable g)
    (hg₀ : ∀ z, 0 ≤ g z)
    (hKgen : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, K x * jumpGen α ψ x) = ∫ y, g y * (ψ y - ψ 0))
    {s : ℝ} (hs : 0 < s) :
    ∃ g' : (Fin 2 → ℝ) → ℝ, Measurable g' ∧ (∀ z, 0 ≤ g' z) ∧
      ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
        (∫ x, dilate K s x * jumpGen α ψ x) = ∫ y, g' y * (ψ y - ψ 0) :=
  ⟨fun y => s ^ (-2 - α) * g (s⁻¹ • y),
    (hgm.comp (measurable_const_smul s⁻¹)).const_mul _,
    fun _z => mul_nonneg (Real.rpow_nonneg hs.le _) (hg₀ _),
    fun _ψ hψ => integral_dilate_mul_jumpGen hs hK hKgen hψ⟩

/-- The moment condition survives dilation: the substitution `y = s • z` turns
`∫ g_s(y) min(1, ‖y‖) dy` into `s^{−α} ∫ g(z) min(1, s ‖z‖) dz`, and
`min(1, s r) ≤ max(1, s) min(1, r)`. -/
theorem integrable_dilate_density_mul_min {s c : ℝ} (hs : 0 < s) (hgm : Measurable g)
    (hg₀ : ∀ z, 0 ≤ g z) (hgmom : Integrable fun z => g z * min 1 ‖z‖) :
    Integrable fun y => c * g (s⁻¹ • y) * min 1 ‖y‖ := by
  have key : ∀ z : Fin 2 → ℝ, min 1 (s * ‖z‖) ≤ max 1 s * min 1 ‖z‖ := fun z => by
    rcases le_total ‖z‖ 1 with h | h
    · rw [min_eq_right h]
      exact (min_le_right _ _).trans
        (mul_le_mul_of_nonneg_right (le_max_right 1 s) (norm_nonneg z))
    · rw [min_eq_left h]
      calc min 1 (s * ‖z‖) ≤ 1 := min_le_left _ _
        _ ≤ max 1 s * 1 := by rw [mul_one]; exact le_max_left 1 s
  have hmain : Integrable fun y : Fin 2 → ℝ => g (s⁻¹ • y) * min 1 ‖y‖ := by
    refine (integrable_comp_smul_iff volume _ hs.ne').mp ?_
    have hm : Measurable fun z : Fin 2 → ℝ => g (s⁻¹ • s • z) :=
      hgm.comp ((measurable_const_smul s⁻¹).comp (measurable_const_smul s))
    have hc : Continuous fun z : Fin 2 → ℝ => min 1 ‖s • z‖ :=
      continuous_const.min (continuous_norm.comp (continuous_const_smul s))
    refine (hgmom.const_mul (max 1 s)).mono'
      (hm.aestronglyMeasurable.mul hc.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    have hz : (0 : ℝ) ≤ min 1 (s * ‖z‖) := le_min zero_le_one (by positivity)
    rw [inv_smul_smul₀ hs.ne', norm_smul, Real.norm_eq_abs s, abs_of_pos hs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hg₀ z) hz)]
    calc g z * min 1 (s * ‖z‖) ≤ g z * (max 1 s * min 1 ‖z‖) :=
          mul_le_mul_of_nonneg_left (key z) (hg₀ z)
      _ = max 1 s * (g z * min 1 ‖z‖) := by ring
  exact (hmain.const_mul c).congr (Filter.Eventually.of_forall fun y => by ring)

/-- **The density form survives dilation, with the moment condition.** The version of
`exists_gen_dilate_fp` that carries `∫ g' min(1, ‖·‖) < ∞` along, which is what feeding the
dilated kernel back into `convolution_le_of_eq_zero_fp` requires. -/
theorem exists_gen_dilate_moment_fp (_hα : 0 < α) (hK : Integrable K) (hgm : Measurable g)
    (hg₀ : ∀ z, 0 ≤ g z) (hgmom : Integrable fun z => g z * min 1 ‖z‖)
    (hKgen : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, K x * jumpGen α ψ x) = ∫ y, g y * (ψ y - ψ 0))
    {s : ℝ} (hs : 0 < s) :
    ∃ g' : (Fin 2 → ℝ) → ℝ, Measurable g' ∧ (∀ z, 0 ≤ g' z) ∧
      (Integrable fun z => g' z * min 1 ‖z‖) ∧
      ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
        (∫ x, dilate K s x * jumpGen α ψ x) = ∫ y, g' y * (ψ y - ψ 0) :=
  ⟨fun y => s ^ (-2 - α) * g (s⁻¹ • y),
    (hgm.comp (measurable_const_smul s⁻¹)).const_mul _,
    fun _z => mul_nonneg (Real.rpow_nonneg hs.le _) (hg₀ _),
    integrable_dilate_density_mul_min hs hgm hg₀ hgmom,
    fun _ψ hψ => integral_dilate_mul_jumpGen hs hK hKgen hψ⟩

end CenteredMaximal

end

end
