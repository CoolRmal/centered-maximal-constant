/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.Pairing
public import CenteredMaximal.Cauchy.Delta
public import CenteredMaximal.Fractional.KernelPositivity

/-!
# The generator of a kernel as a merged density

`CenteredMaximal.Transfer.JumpTransfer` transfers the obstacle equation through a convolution once
the generator of the comparison kernel is represented in the *merged* form

`∫ K · jumpGen α ψ = ∫ g (ψ − ψ 0)`,

with `g` a nonnegative measurable density. This file establishes that representation for every
integrable kernel `K` satisfying a single moment hypothesis, `JumpMoment α K`, and specialises it to
the `α = 6/5` comparison kernel `CenteredMaximal.Fractional.fracKernel`.

This is the fractional analogue of `CenteredMaximal.Cauchy.Representation`, which does the same job
at `α = 1`. There the density had finite mass, so the identity split as
`(∫ g ψ) − pointMass · ψ 0`; here `g` behaves like `r^{−2α}` at the origin, which is not locally
integrable in the plane, and the two halves have to stay together. The gain is that *no point mass
and no limiting procedure* are needed: the whole identity is two applications of Fubini around the
elementary observation that the second difference of an integrable function integrates to zero.

## The argument

Write `Δ_j^t K (z) = K(z + t e_j) + K(z − t e_j) − 2 K(z)` and `w(t) = |t|^{−(1+α)}`. For a test
function `ψ`:

* the first exchange, `integrable_mul_secondDiff_mul_rpow`, needs only `K ∈ L¹`: the Tonelli bound
  is `∫ |K| · ∫ jumpBound α M₀ M₂ < ∞`, since the second difference of `ψ` is dominated by
  `min(M₂ t², 4 M₀)` *uniformly in `z`*. This is where the kernel may be unbounded — the estimate
  of `CenteredMaximal.Analysis.Pairing` trades the roles, asking `K` bounded and `ψ` merely
  integrable, and the diamond power `r^{−α}` is not bounded;
* at a fixed step the second difference moves from `ψ` onto `K` (`integral_mul_secondDiff_comm`),
  again by the two shifts `z ↦ z ∓ t e_j`, whose integrability now comes from `K ∈ L¹` and `ψ`
  bounded;
* `integral_secondDiff_eq_zero`: `∫ Δ_j^t K = 0` for every step, by translation invariance. This is
  the substitute for the point mass: it lets `ψ` be replaced by `ψ − ψ 0` inside the inner integral
  at no cost, and it is exactly what makes the *second* exchange legitimate, since `ψ − ψ 0`
  vanishes at the origin to first order (`IsTestFunction.exists_bound_min_one`);
* the second exchange is the hypothesis `JumpMoment α K`, and the same hypothesis gives the Lévy
  moment `∫ |A K| min(1, ‖z‖) < ∞` that `convolution_le_of_eq_zero_fp` consumes.

## Main results

* `JumpMoment`: the moment hypothesis, and `JumpMoment.add`, `JumpMoment.const_mul`,
  `jumpMoment_finsetSum`, `JumpMoment.congr`: it is additive, so it may be checked summand by
  summand on a kernel presented as a finite sum;
* `integral_mul_jumpGen_eq_integral_jumpGen_sub`: **the representation**
  `∫ K · jumpGen α ψ = ∫ (jumpGen α K) (ψ − ψ 0)`;
* `integrable_jumpGen_mul_min_one`: **the Lévy moment** `Integrable (jumpGen α K · min(1, ‖z‖))`;
* `measurable_fracKernel`, `fracDensity`, `measurable_fracDensity`: the density of the `α = 6/5`
  comparison kernel;
* `hKgen_fracKernel`, `integrable_fracDensity_mul_min_one`: the two hypotheses of
  `CenteredMaximal.convolution_le_of_eq_zero_fp`, both reduced to `JumpMoment (6/5) fracKernel`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace CenteredMaximal.Fractional

variable {α : ℝ} {K ψ : (Fin 2 → ℝ) → ℝ}

/-! ### The second difference of an integrable kernel -/

/-- The second difference is jointly measurable in the base point and the step. -/
theorem measurable_secondDiff_fst (hK : Measurable K) (j : Fin 2) :
    Measurable fun p : (Fin 2 → ℝ) × ℝ => secondDiff K j p.1 p.2 := by
  unfold secondDiff
  exact ((hK.comp (measurable_fst.add (measurable_snd.smul_const _))).add
    (hK.comp (measurable_fst.sub (measurable_snd.smul_const _)))).sub
    (measurable_const.mul (hK.comp measurable_fst))

/-- The second difference is jointly measurable in the step and the base point. -/
theorem measurable_secondDiff_snd (hK : Measurable K) (j : Fin 2) :
    Measurable fun p : ℝ × (Fin 2 → ℝ) => secondDiff K j p.2 p.1 := by
  unfold secondDiff
  exact ((hK.comp (measurable_snd.add (measurable_fst.smul_const _))).add
    (hK.comp (measurable_snd.sub (measurable_fst.smul_const _)))).sub
    (measurable_const.mul (hK.comp measurable_snd))

/-- At every fixed step the second difference of an integrable function is integrable, being a
combination of two translates of it and of the function itself. -/
theorem integrable_secondDiff (hK : Integrable K) (j : Fin 2) (t : ℝ) :
    Integrable fun z => secondDiff K j z t := by
  simp only [secondDiff]
  exact ((hK.comp_add_right _).add (hK.comp_sub_right _)).sub (hK.const_mul 2)

/-- **The second difference of an integrable function integrates to zero**, by the translation
invariance of Lebesgue measure. This is what replaces the point mass of the `α = 1` argument: it is
the exact statement that the generator of `K` has zero total mass in the principal value sense. -/
theorem integral_secondDiff_eq_zero (hK : Integrable K) (j : Fin 2) (t : ℝ) :
    ∫ z, secondDiff K j z t = 0 := by
  obtain ⟨a, ha⟩ : ∃ a : Fin 2 → ℝ, a = t • Pi.single j (1 : ℝ) := ⟨_, rfl⟩
  have hsdK : ∀ z, secondDiff K j z t = K (z + a) + K (z - a) - 2 * K z := fun z => by
    rw [ha]; rfl
  have hA : Integrable fun z => K (z + a) := hK.comp_add_right a
  have hB : Integrable fun z => K (z - a) := hK.comp_sub_right a
  have hsplit : (∫ z, secondDiff K j z t)
      = ((∫ z, K (z + a)) + ∫ z, K (z - a)) - 2 * ∫ z, K z := by
    calc (∫ z, secondDiff K j z t) = ∫ z, (K (z + a) + K (z - a) - 2 * K z) :=
          integral_congr_ae (ae_of_all _ fun z => hsdK z)
      _ = (∫ z, (K (z + a) + K (z - a))) - ∫ z, 2 * K z :=
          integral_sub (hA.add hB) (hK.const_mul 2)
      _ = ((∫ z, K (z + a)) + ∫ z, K (z - a)) - 2 * ∫ z, K z := by
          rw [integral_add hA hB, integral_const_mul]
  rw [hsplit, integral_add_right_eq_self K a, integral_sub_right_eq_self K a]
  ring

/-- **The pairing identity at a fixed step**, for `K` integrable and `ψ` a test function: the two
outer terms of the second difference are moved from `ψ` onto `K` by the shifts `z ↦ z ∓ t e_j`.
This is the mirror image of `CenteredMaximal.integral_mul_secondDiff_eq_integral_secondDiff_mul`,
which asks the kernel to be bounded and the test function merely integrable. -/
theorem integral_mul_secondDiff_comm (hK : Integrable K) (hψ : IsTestFunction ψ) (j : Fin 2)
    (t : ℝ) :
    ∫ z, K z * secondDiff ψ j z t = ∫ z, secondDiff K j z t * ψ z := by
  obtain ⟨M, hM⟩ := hψ.continuous.bounded_above_of_compact_support hψ.2
  obtain ⟨a, ha⟩ : ∃ a : Fin 2 → ℝ, a = t • Pi.single j (1 : ℝ) := ⟨_, rfl⟩
  have hsdψ : ∀ z, secondDiff ψ j z t = ψ (z + a) + ψ (z - a) - 2 * ψ z := fun z => by
    rw [ha]; rfl
  have hsdK : ∀ z, secondDiff K j z t = K (z + a) + K (z - a) - 2 * K z := fun z => by
    rw [ha]; rfl
  have hψb : ∀ᵐ z : Fin 2 → ℝ, ‖ψ z‖ ≤ M :=
    ae_of_all _ fun z => (Real.norm_eq_abs _).trans_le (hM z)
  have hmA : AEStronglyMeasurable fun z : Fin 2 → ℝ => ψ (z + a) :=
    (hψ.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable
  have hmB : AEStronglyMeasurable fun z : Fin 2 → ℝ => ψ (z - a) :=
    (hψ.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
  have hA : Integrable fun z => K z * ψ (z + a) :=
    hK.mul_bdd hmA (ae_of_all _ fun z => (Real.norm_eq_abs _).trans_le (hM _))
  have hB : Integrable fun z => K z * ψ (z - a) :=
    hK.mul_bdd hmB (ae_of_all _ fun z => (Real.norm_eq_abs _).trans_le (hM _))
  have hM0 : Integrable fun z => K z * ψ z :=
    hK.mul_bdd hψ.continuous.aestronglyMeasurable hψb
  have hA' : Integrable fun z => K (z + a) * ψ z :=
    (hK.comp_add_right a).mul_bdd hψ.continuous.aestronglyMeasurable hψb
  have hB' : Integrable fun z => K (z - a) * ψ z :=
    (hK.comp_sub_right a).mul_bdd hψ.continuous.aestronglyMeasurable hψb
  have hleft : (∫ z, K z * secondDiff ψ j z t)
      = ((∫ z, K z * ψ (z + a)) + ∫ z, K z * ψ (z - a)) - 2 * ∫ z, K z * ψ z := by
    calc (∫ z, K z * secondDiff ψ j z t)
        = ∫ z, (K z * ψ (z + a) + K z * ψ (z - a) - 2 * (K z * ψ z)) :=
          integral_congr_ae (ae_of_all _ fun z => by
            show K z * secondDiff ψ j z t
              = K z * ψ (z + a) + K z * ψ (z - a) - 2 * (K z * ψ z)
            rw [hsdψ z]; ring)
      _ = (∫ z, (K z * ψ (z + a) + K z * ψ (z - a))) - ∫ z, 2 * (K z * ψ z) :=
          integral_sub (hA.add hB) (hM0.const_mul 2)
      _ = ((∫ z, K z * ψ (z + a)) + ∫ z, K z * ψ (z - a)) - 2 * ∫ z, K z * ψ z := by
          rw [integral_add hA hB, integral_const_mul]
  have hright : (∫ z, secondDiff K j z t * ψ z)
      = ((∫ z, K (z - a) * ψ z) + ∫ z, K (z + a) * ψ z) - 2 * ∫ z, K z * ψ z := by
    calc (∫ z, secondDiff K j z t * ψ z)
        = ∫ z, (K (z - a) * ψ z + K (z + a) * ψ z - 2 * (K z * ψ z)) :=
          integral_congr_ae (ae_of_all _ fun z => by
            show secondDiff K j z t * ψ z
              = K (z - a) * ψ z + K (z + a) * ψ z - 2 * (K z * ψ z)
            rw [hsdK z]; ring)
      _ = (∫ z, (K (z - a) * ψ z + K (z + a) * ψ z)) - ∫ z, 2 * (K z * ψ z) :=
          integral_sub (hB'.add hA') (hM0.const_mul 2)
      _ = ((∫ z, K (z - a) * ψ z) + ∫ z, K (z + a) * ψ z) - 2 * ∫ z, K z * ψ z := by
          rw [integral_add hB' hA', integral_const_mul]
  have hshift1 : (∫ z, K z * ψ (z + a)) = ∫ z, K (z - a) * ψ z := by
    have h := integral_add_right_eq_self (μ := (volume : Measure (Fin 2 → ℝ)))
      (fun z : Fin 2 → ℝ => K (z - a) * ψ z) a
    simpa using h
  have hshift2 : (∫ z, K z * ψ (z - a)) = ∫ z, K (z + a) * ψ z := by
    have h := integral_sub_right_eq_self (μ := (volume : Measure (Fin 2 → ℝ)))
      (fun z : Fin 2 → ℝ => K (z + a) * ψ z) a
    simpa using h
  rw [hleft, hright, hshift1, hshift2]

/-- Against a test function the second difference of an integrable kernel does not see the value of
the test function at the origin, because the second difference integrates to zero. -/
theorem integral_secondDiff_mul_sub (hK : Integrable K) (hψ : IsTestFunction ψ) (j : Fin 2)
    (t : ℝ) : ∫ z, secondDiff K j z t * (ψ z - ψ 0) = ∫ z, secondDiff K j z t * ψ z := by
  obtain ⟨M, hM⟩ := hψ.continuous.bounded_above_of_compact_support hψ.2
  have hsd : Integrable fun z => secondDiff K j z t := integrable_secondDiff hK j t
  have h1 : Integrable fun z => secondDiff K j z t * ψ z :=
    hsd.mul_bdd hψ.continuous.aestronglyMeasurable
      (ae_of_all _ fun z => (Real.norm_eq_abs _).trans_le (hM z))
  have h2 : Integrable fun z => secondDiff K j z t * ψ 0 := hsd.mul_const _
  calc (∫ z, secondDiff K j z t * (ψ z - ψ 0))
      = (∫ z, secondDiff K j z t * ψ z) - ∫ z, secondDiff K j z t * ψ 0 := by
        rw [← integral_sub h1 h2]
        exact integral_congr_ae (ae_of_all _ fun z => by ring)
    _ = ∫ z, secondDiff K j z t * ψ z := by
        rw [integral_mul_const, integral_secondDiff_eq_zero hK j t, zero_mul, sub_zero]

/-! ### The first exchange -/

/-- **The integrand of the pairing is integrable on `ℝ² × ℝ` for every integrable kernel.** The
second difference of a test function is dominated by `min(M₂ t², 4 M₀)` uniformly in the base point,
so the integrand is dominated by the product `|K(z)| · jumpBound α M₀ M₂ (t)` of an integrable
function of `z` and an integrable function of `t`.

Unlike `CenteredMaximal.integrable_bdd_mul_secondDiff_mul_rpow`, which uses the compact support of
`ψ` to bound the `z`-integral and therefore needs `K` bounded, this uses the integrability of `K`
and therefore tolerates the singularity `r^{−α}` of the fractional kernels. -/
theorem integrable_mul_secondDiff_mul_rpow (hα : 0 < α) (hα' : α < 2) (hKm : Measurable K)
    (hK : Integrable K) (hψ : IsTestFunction ψ) (j : Fin 2) :
    Integrable (fun p : (Fin 2 → ℝ) × ℝ =>
        K p.1 * (secondDiff ψ j p.1 p.2 * |p.2| ^ (-(1 + α))))
      ((volume : Measure (Fin 2 → ℝ)).prod (volume : Measure ℝ)) := by
  have hψ2 : ContDiff ℝ 2 ψ := hψ.1.of_le (by norm_cast)
  obtain ⟨M₀, M₂, h₀, h₂⟩ := exists_bounds_of_hasCompactSupport hψ2 hψ.2
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (h₀ 0)
  have hM₂ : 0 ≤ M₂ := (norm_nonneg _).trans (h₂ 0)
  have hm : Measurable fun p : (Fin 2 → ℝ) × ℝ =>
      K p.1 * (secondDiff ψ j p.1 p.2 * |p.2| ^ (-(1 + α))) :=
    (hKm.comp measurable_fst).mul
      ((measurable_secondDiff_fst hψ.continuous.measurable j).mul
        ((continuous_abs.measurable.pow_const _).comp measurable_snd))
  refine (hK.abs.mul_prod (integrable_jumpBound hα hα' hM₀ hM₂)).mono'
    hm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  simpa [Real.norm_eq_abs] using
    norm_secondDiff_mul_rpow_le_jumpBound hψ2 h₀ h₂ α j p.1 p.2

/-! ### The moment hypothesis -/

/-- **The moment hypothesis for the second exchange.** Weighted by `min(1, ‖z‖)` — the size of the
increment `ψ(z) − ψ(0)` of a test function — the jump integrand of `K` is absolutely integrable on
`ℝ × ℝ²`.

For the kernels of interest the weight is exactly what makes this finite: the generator behaves like
`r^{−2α}` at the origin, where `min(1, ‖z‖) r^{−2α}` is integrable precisely for `α < 3/2`, and like
`r^{−(1+α)}` at infinity, where it is integrable precisely for `α > 1`. -/
def JumpMoment (α : ℝ) (K : (Fin 2 → ℝ) → ℝ) : Prop :=
  ∀ j : Fin 2, Integrable (Function.uncurry fun (t : ℝ) (z : Fin 2 → ℝ) =>
      secondDiff K j z t * min 1 ‖z‖ * |t| ^ (-(1 + α)))
    ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)))

/-- The moment hypothesis only depends on the kernel as a function. -/
theorem JumpMoment.congr {K L : (Fin 2 → ℝ) → ℝ} (hK : JumpMoment α K) (h : K = L) :
    JumpMoment α L := by
  rwa [← h]

/-- The moment hypothesis is additive. -/
theorem JumpMoment.add {K L : (Fin 2 → ℝ) → ℝ} (hK : JumpMoment α K) (hL : JumpMoment α L) :
    JumpMoment α fun z => K z + L z := by
  intro j
  refine ((hK j).add (hL j)).congr (ae_of_all _ fun p => ?_)
  show secondDiff K j p.2 p.1 * min 1 ‖p.2‖ * |p.1| ^ (-(1 + α))
      + secondDiff L j p.2 p.1 * min 1 ‖p.2‖ * |p.1| ^ (-(1 + α))
    = secondDiff (fun z => K z + L z) j p.2 p.1 * min 1 ‖p.2‖ * |p.1| ^ (-(1 + α))
  rw [show secondDiff (fun z => K z + L z) j p.2 p.1
      = secondDiff K j p.2 p.1 + secondDiff L j p.2 p.1 from by simp only [secondDiff]; ring]
  ring

/-- The moment hypothesis survives scaling. -/
theorem JumpMoment.const_mul {K : (Fin 2 → ℝ) → ℝ} (hK : JumpMoment α K) (c : ℝ) :
    JumpMoment α fun z => c * K z := by
  intro j
  refine ((hK j).const_mul c).congr (ae_of_all _ fun p => ?_)
  show c * (secondDiff K j p.2 p.1 * min 1 ‖p.2‖ * |p.1| ^ (-(1 + α)))
    = secondDiff (fun z => c * K z) j p.2 p.1 * min 1 ‖p.2‖ * |p.1| ^ (-(1 + α))
  rw [show secondDiff (fun z => c * K z) j p.2 p.1 = c * secondDiff K j p.2 p.1 from by
    simp only [secondDiff]; ring]
  ring

/-- The zero kernel satisfies the moment hypothesis. -/
theorem jumpMoment_zero : JumpMoment α fun _ : Fin 2 → ℝ => (0 : ℝ) := by
  intro j
  refine (integrable_zero _ _ _).congr (ae_of_all _ fun p => ?_)
  show (0 : ℝ) = secondDiff (fun _ : Fin 2 → ℝ => (0 : ℝ)) j p.2 p.1 * min 1 ‖p.2‖
    * |p.1| ^ (-(1 + α))
  simp [secondDiff]

/-- The moment hypothesis may be checked summand by summand on a finite sum of kernels. -/
theorem jumpMoment_finsetSum {ι : Type*} (s : Finset ι) {f : ι → (Fin 2 → ℝ) → ℝ}
    (h : ∀ i ∈ s, JumpMoment α (f i)) : JumpMoment α fun z => ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction with
  | empty => simpa using jumpMoment_zero (α := α)
  | insert a s ha ih =>
      have hrest : JumpMoment α fun z => ∑ i ∈ s, f i z :=
        ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine ((h a (Finset.mem_insert_self a s)).add hrest).congr ?_
      funext z
      rw [Finset.sum_insert ha]

/-! ### The representation -/

/-- **The representation of the generator of an integrable kernel.** For `0 < α < 2`, an integrable
measurable kernel `K` satisfying the moment hypothesis and every test function `ψ`,

`∫ K · jumpGen α ψ = ∫ (jumpGen α K) · (ψ − ψ 0)`.

Both sides converge absolutely: the left because `K ∈ L¹` and `jumpGen α ψ` is bounded, the right by
the moment hypothesis together with `|ψ(z) − ψ(0)| ≤ C min(1, ‖z‖)`. No point mass appears, and no
limit is taken: the `− ψ 0` is produced by `integral_secondDiff_eq_zero`, at the fixed step, before
either Fubini is applied. -/
theorem integral_mul_jumpGen_eq_integral_jumpGen_sub (hα : 0 < α) (hα' : α < 2)
    (hKm : Measurable K) (hK : Integrable K) (hmom : JumpMoment α K) (hψ : IsTestFunction ψ) :
    ∫ z, K z * jumpGen α ψ z = ∫ z, jumpGen α K z * (ψ z - ψ 0) := by
  obtain ⟨C, hC0, hC⟩ := hψ.exists_bound_min_one
  have hCz : ∀ z : Fin 2 → ℝ, |ψ z - ψ 0| ≤ C * min 1 ‖z‖ := fun z => by simpa using hC 0 z
  have hprod := fun j => integrable_mul_secondDiff_mul_rpow hα hα' hKm hK hψ j
  -- the second exchange is legitimate because `ψ − ψ 0` is dominated by `min (1, ‖z‖)`
  have hprod2 : ∀ j : Fin 2, Integrable (Function.uncurry fun (t : ℝ) (z : Fin 2 → ℝ) =>
      secondDiff K j z t * (ψ z - ψ 0) * |t| ^ (-(1 + α)))
      ((volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ))) := by
    intro j
    have hm : Measurable fun p : ℝ × (Fin 2 → ℝ) =>
        secondDiff K j p.2 p.1 * (ψ p.2 - ψ 0) * |p.1| ^ (-(1 + α)) :=
      ((measurable_secondDiff_snd hKm j).mul
        ((hψ.continuous.measurable.comp measurable_snd).sub measurable_const)).mul
        ((continuous_abs.measurable.pow_const _).comp measurable_fst)
    refine ((hmom j).abs.const_mul C).mono' hm.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    have hw : (0 : ℝ) ≤ |p.1| ^ (-(1 + α)) := Real.rpow_nonneg (abs_nonneg _) _
    have hmin : (0 : ℝ) ≤ min 1 ‖p.2‖ := le_min zero_le_one (norm_nonneg _)
    calc ‖secondDiff K j p.2 p.1 * (ψ p.2 - ψ 0) * |p.1| ^ (-(1 + α))‖
        = |secondDiff K j p.2 p.1| * |ψ p.2 - ψ 0| * |p.1| ^ (-(1 + α)) := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw]
      _ ≤ |secondDiff K j p.2 p.1| * (C * min 1 ‖p.2‖) * |p.1| ^ (-(1 + α)) := by
          gcongr
          exact hCz p.2
      _ = C * |secondDiff K j p.2 p.1 * min 1 ‖p.2‖ * |p.1| ^ (-(1 + α))| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hmin, abs_of_nonneg hw]
          ring
  -- the inner `t`-integrals on the right
  have hzK : ∀ (j : Fin 2) (z : Fin 2 → ℝ),
      (∫ t : ℝ, secondDiff K j z t * (ψ z - ψ 0) * |t| ^ (-(1 + α)))
        = (∫ t : ℝ, secondDiff K j z t * |t| ^ (-(1 + α))) * (ψ z - ψ 0) := by
    intro j z
    calc (∫ t : ℝ, secondDiff K j z t * (ψ z - ψ 0) * |t| ^ (-(1 + α)))
        = ∫ t : ℝ, secondDiff K j z t * |t| ^ (-(1 + α)) * (ψ z - ψ 0) :=
          integral_congr_ae (ae_of_all _ fun t => by ring)
      _ = _ := integral_mul_const _ _
  have hintR : ∀ j : Fin 2, Integrable fun z =>
      (∫ t : ℝ, secondDiff K j z t * |t| ^ (-(1 + α))) * (ψ z - ψ 0) := fun j =>
    (hprod2 j).integral_prod_right.congr (ae_of_all _ fun z => hzK j z)
  have hR : (∫ z, jumpGen α K z * (ψ z - ψ 0))
      = ∑ j : Fin 2, ∫ z, (∫ t : ℝ, secondDiff K j z t * |t| ^ (-(1 + α))) * (ψ z - ψ 0) := by
    rw [← integral_finsetSum _ fun j _ => hintR j]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show (∑ j : Fin 2, ∫ t : ℝ, secondDiff K j z t * |t| ^ (-(1 + α))) * (ψ z - ψ 0)
      = ∑ j : Fin 2, (∫ t : ℝ, secondDiff K j z t * |t| ^ (-(1 + α))) * (ψ z - ψ 0)
    rw [Finset.sum_mul]
  -- the inner `t`-integrals on the left
  have hintL : ∀ j : Fin 2, Integrable fun z =>
      K z * ∫ t : ℝ, secondDiff ψ j z t * |t| ^ (-(1 + α)) := fun j =>
    (hprod j).integral_prod_left.congr (ae_of_all _ fun z =>
      integral_const_mul (K z) fun t : ℝ => secondDiff ψ j z t * |t| ^ (-(1 + α)))
  have hL : (∫ z, K z * jumpGen α ψ z)
      = ∑ j : Fin 2, ∫ z, K z * ∫ t : ℝ, secondDiff ψ j z t * |t| ^ (-(1 + α)) := by
    rw [← integral_finsetSum _ fun j _ => hintL j]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show K z * ∑ j : Fin 2, ∫ t : ℝ, secondDiff ψ j z t * |t| ^ (-(1 + α))
      = ∑ j : Fin 2, K z * ∫ t : ℝ, secondDiff ψ j z t * |t| ^ (-(1 + α))
    rw [Finset.mul_sum]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun j _ => ?_
  have htrans : ∀ t : ℝ, (∫ z, K z * (secondDiff ψ j z t * |t| ^ (-(1 + α))))
      = (∫ z, secondDiff K j z t * (ψ z - ψ 0)) * |t| ^ (-(1 + α)) := by
    intro t
    calc (∫ z, K z * (secondDiff ψ j z t * |t| ^ (-(1 + α))))
        = ∫ z, K z * secondDiff ψ j z t * |t| ^ (-(1 + α)) :=
          integral_congr_ae (ae_of_all _ fun z => by ring)
      _ = (∫ z, K z * secondDiff ψ j z t) * |t| ^ (-(1 + α)) := integral_mul_const _ _
      _ = (∫ z, secondDiff K j z t * (ψ z - ψ 0)) * |t| ^ (-(1 + α)) := by
          rw [integral_mul_secondDiff_comm hK hψ j t,
            ← integral_secondDiff_mul_sub hK hψ j t]
  calc (∫ z, K z * ∫ t : ℝ, secondDiff ψ j z t * |t| ^ (-(1 + α)))
      = ∫ z, ∫ t : ℝ, K z * (secondDiff ψ j z t * |t| ^ (-(1 + α))) :=
        integral_congr_ae (ae_of_all _ fun z => (integral_const_mul _ _).symm)
    _ = ∫ t : ℝ, ∫ z, K z * (secondDiff ψ j z t * |t| ^ (-(1 + α))) :=
        integral_integral_swap (f := fun (z : Fin 2 → ℝ) (t : ℝ) =>
          K z * (secondDiff ψ j z t * |t| ^ (-(1 + α)))) (hprod j)
    _ = ∫ t : ℝ, (∫ z, secondDiff K j z t * (ψ z - ψ 0)) * |t| ^ (-(1 + α)) :=
        integral_congr_ae (ae_of_all _ htrans)
    _ = ∫ t : ℝ, ∫ z, secondDiff K j z t * (ψ z - ψ 0) * |t| ^ (-(1 + α)) :=
        integral_congr_ae (ae_of_all _ fun t => (integral_mul_const _ _).symm)
    _ = ∫ z, ∫ t : ℝ, secondDiff K j z t * (ψ z - ψ 0) * |t| ^ (-(1 + α)) :=
        integral_integral_swap (f := fun (t : ℝ) (z : Fin 2 → ℝ) =>
          secondDiff K j z t * (ψ z - ψ 0) * |t| ^ (-(1 + α))) (hprod2 j)
    _ = ∫ z, (∫ t : ℝ, secondDiff K j z t * |t| ^ (-(1 + α))) * (ψ z - ψ 0) :=
        integral_congr_ae (ae_of_all _ fun z => hzK j z)

/-- **The Lévy moment of the generator.** The moment hypothesis is exactly the Fubini form of the
hypothesis `hgmom` of `CenteredMaximal.convolution_le_of_eq_zero_fp`. -/
theorem integrable_jumpGen_mul_min_one (hmom : JumpMoment α K) :
    Integrable fun z => jumpGen α K z * min 1 ‖z‖ := by
  have hz : ∀ (j : Fin 2) (z : Fin 2 → ℝ),
      (∫ t : ℝ, secondDiff K j z t * min 1 ‖z‖ * |t| ^ (-(1 + α)))
        = (∫ t : ℝ, secondDiff K j z t * |t| ^ (-(1 + α))) * min 1 ‖z‖ := by
    intro j z
    calc (∫ t : ℝ, secondDiff K j z t * min 1 ‖z‖ * |t| ^ (-(1 + α)))
        = ∫ t : ℝ, secondDiff K j z t * |t| ^ (-(1 + α)) * min 1 ‖z‖ :=
          integral_congr_ae (ae_of_all _ fun t => by ring)
      _ = _ := integral_mul_const _ _
  have hj : ∀ j : Fin 2, Integrable fun z : Fin 2 → ℝ =>
      (∫ t : ℝ, secondDiff K j z t * |t| ^ (-(1 + α))) * min 1 ‖z‖ := fun j =>
    (hmom j).integral_prod_right.congr (ae_of_all _ fun z => hz j z)
  refine (integrable_finsetSum Finset.univ fun j _ => hj j).congr (ae_of_all _ fun z => ?_)
  show (∑ j : Fin 2, (∫ t : ℝ, secondDiff K j z t * |t| ^ (-(1 + α))) * min 1 ‖z‖)
    = jumpGen α K z * min 1 ‖z‖
  rw [← Finset.sum_mul]
  rfl

/-! ### The `α = 6/5` comparison kernel -/

/-- The comparison kernel is measurable. It is *not* continuous: the truncated diamond base jumps at
the origin, where Lean's convention `0 ^ (-α) = 0` makes it vanish. -/
theorem measurable_fracKernel : Measurable fracKernel := by
  have hfun : fracKernel = fun z : Fin 2 → ℝ => fracBaseCoeff * truncBase (6 / 5) (7 / 4) z
      + ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
          (bspline (16 * z 0 - ij.1) * bspline (16 * z 1 - ij.2)) :=
    funext fracKernel_eq_finsetSum
  rw [hfun]
  refine ((measurable_truncBase _ _).const_mul _).add (Finset.measurable_sum _ fun ij _ => ?_)
  refine Measurable.const_mul ?_ _
  exact ((continuous_bspline.comp ((continuous_const.mul (continuous_apply 0)).sub
    continuous_const)).mul (continuous_bspline.comp ((continuous_const.mul
    (continuous_apply 1)).sub continuous_const))).measurable

/-- **The generator density of the `α = 6/5` comparison kernel**: its own pointwise jump generator.
On the two coordinate axes, where the jump integrand is not integrable, Mathlib's convention makes
the Bochner integral vanish, so the density is `0` there; that set is null. -/
def fracDensity (z : Fin 2 → ℝ) : ℝ := jumpGen (6 / 5) fracKernel z

/-- The density is measurable: the kernel is measurable, so its second difference is jointly
measurable in the base point and the step, and the Bochner integral in the step is measurable in the
base point. -/
theorem measurable_fracDensity : Measurable fracDensity := by
  show Measurable fun z : Fin 2 → ℝ =>
    ∑ j : Fin 2, ∫ t : ℝ, secondDiff fracKernel j z t * |t| ^ (-(1 + (6 / 5 : ℝ)))
  refine Finset.measurable_sum _ fun j _ => ?_
  have hm : Measurable fun p : (Fin 2 → ℝ) × ℝ =>
      secondDiff fracKernel j p.1 p.2 * |p.2| ^ (-(1 + (6 / 5 : ℝ))) :=
    (measurable_secondDiff_fst measurable_fracKernel j).mul
      ((continuous_abs.measurable.pow_const _).comp measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable

/-- **The merged generator representation of the `α = 6/5` comparison kernel**, the hypothesis
`hKgen` of `CenteredMaximal.convolution_le_of_eq_zero_fp`, reduced to the moment hypothesis. -/
theorem hKgen_fracKernel (hmom : JumpMoment (6 / 5) fracKernel) (hψ : IsTestFunction ψ) :
    (∫ x, fracKernel x * jumpGen (6 / 5) ψ x) = ∫ y, fracDensity y * (ψ y - ψ 0) :=
  integral_mul_jumpGen_eq_integral_jumpGen_sub (by norm_num) (by norm_num) measurable_fracKernel
    integrable_fracKernel hmom hψ

/-- **The Lévy moment of the `α = 6/5` density**, the hypothesis `hgmom` of
`CenteredMaximal.convolution_le_of_eq_zero_fp`, reduced to the moment hypothesis. -/
theorem integrable_fracDensity_mul_min_one (hmom : JumpMoment (6 / 5) fracKernel) :
    Integrable fun z => fracDensity z * min 1 ‖z‖ :=
  integrable_jumpGen_mul_min_one hmom

end CenteredMaximal.Fractional

end

end
