/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Obstacle.Main
public import CenteredMaximal.Transfer.Commutation
public import CenteredMaximal.Transfer.Scaling

/-!
# Assembling the weak type bound from the obstacle decomposition

This file closes the chain that turns the obstacle decomposition of
`CenteredMaximal.Obstacle.Main` into the weak type `(1, 1)` bound
`c₂ ≤ ½ ∫ K = looseCost` for the one-bump comparison kernel `K` of
`CenteredMaximal.Cauchy.LooseKernel`.

Lean evaluates `looseKernel 0 = -looseBump < 0`, because `R / 0 = 0`; the kernel is meant to be
`+∞` at the origin. Since every statement below is either an integral or a bound on the unit
diamond, the single offending point is simply patched: `compKernel` agrees with `looseKernel` away
from the origin and takes the value `1` there. It is genuinely nonnegative, genuinely at least `1`
on the whole unit diamond, even, integrable with compact support, and has the same mass
`2 looseCost`.

The only input that is *not* proved here is the representation of the kernel's generator as a
positive finite measure minus a point mass at the origin,
`∫ K · A φ = ∫ φ dβ − a φ(0)` with `A = jumpGen 1`; it enters every theorem of the last section
as a hypothesis `hgen`.

## Main results

* `compKernel`, `compKernel_ae_eq`, `compKernel_nonneg`, `one_le_compKernel`, `compKernel_neg`,
  `integrable_compKernel`, `integral_compKernel`, `hasCompactSupport_compKernel`: the patched
  kernel and its basic properties, in particular `∫ compKernel = 2 looseCost`;
* `integral_dilate_eq`: the Bochner integral of a dilation of a nonnegative integrable kernel
  equals that of the kernel, the Jacobian `s²` cancelling the normalisation `(s²)⁻¹`;
* `exists_exceptional_set`: **the pointwise step.** For a bounded, nonnegative, compactly
  supported measurable obstacle `f` and a level `λ > 0`, the obstacle problem with cap
  `κ = λ / ∫ K` produces an exceptional set `Ω` of measure at most `(∫ K) (∫ f) / λ` off which
  every dilation average `∫ K_s(x − y) f(y) dy` is at most `λ`, almost everywhere for each
  scale `s > 0` separately;
* `weakTypeConstant_two_le_looseCost`, `weakTypeConstant_two_le_rat`,
  `weakTypeConstant_two_le_upper`: hence `c₂ ≤ looseCost = 2787954611/718800000 < 3.879`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal

namespace CenteredMaximal.Cauchy

/-! ### The patched kernel -/

/-- The comparison kernel: the loose kernel with its value at the origin patched to `1`. Lean
evaluates `looseKernel 0 = -looseBump`, because `R / 0 = 0`, while the kernel is meant to be `+∞`
there; the patch makes the kernel nonnegative and at least `1` on the *whole* unit diamond without
changing any integral. -/
def compKernel (z : Fin 2 → ℝ) : ℝ := if z = 0 then 1 else looseKernel z

@[simp]
theorem compKernel_zero : compKernel 0 = 1 :=
  if_pos rfl

theorem compKernel_of_ne {z : Fin 2 → ℝ} (hz : z ≠ 0) : compKernel z = looseKernel z :=
  if_neg hz

/-- The patch changes the kernel only at the origin, a null set. -/
theorem compKernel_ae_eq : compKernel =ᵐ[volume] looseKernel := by
  show ∀ᵐ z ∂volume, compKernel z = looseKernel z
  refine ae_iff.2 (measure_mono_null (fun z hz => ?_) (measure_singleton (0 : Fin 2 → ℝ)))
  by_contra hz₀
  exact hz (compKernel_of_ne hz₀)

/-- The loose kernel is measurable: it is the singular radial profile minus the bump profile,
both composed with the diamond radius. -/
theorem measurable_looseKernel : Measurable looseKernel := by
  have h : looseKernel =
      fun z => looseCusp (diamondNorm z) - looseBump * looseHump (diamondNorm z) :=
    funext looseKernel_eq
  rw [h]
  exact (measurable_looseCusp.comp measurable_diamondNorm).sub
    ((continuous_looseHump.measurable.comp measurable_diamondNorm).const_mul _)

theorem measurable_compKernel : Measurable compKernel :=
  Measurable.ite (measurableSet_singleton (0 : Fin 2 → ℝ)) measurable_const measurable_looseKernel

/-- The patched kernel is nonnegative everywhere. -/
theorem compKernel_nonneg (z : Fin 2 → ℝ) : 0 ≤ compKernel z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [compKernel_zero]
    norm_num
  · rw [compKernel_of_ne hz]
    exact looseKernel_nonneg hz

/-- The patched kernel is at least `1` on the whole closed unit diamond, the origin included. -/
theorem one_le_compKernel {z : Fin 2 → ℝ} (hz : diamondNorm z ≤ 1) : 1 ≤ compKernel z := by
  rcases eq_or_ne z 0 with rfl | hz₀
  · rw [compKernel_zero]
  · rw [compKernel_of_ne hz₀]
    exact one_le_looseKernel hz hz₀

/-- The patched kernel is even. -/
theorem compKernel_neg (z : Fin 2 → ℝ) : compKernel (-z) = compKernel z := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [neg_zero]
  · rw [compKernel_of_ne (neg_ne_zero.2 hz), compKernel_of_ne hz, looseKernel_neg]

theorem integrable_compKernel : Integrable compKernel :=
  integrable_looseKernel.congr compKernel_ae_eq.symm

/-- The mass of the patched kernel is twice the comparison cost. -/
theorem integral_compKernel : ∫ z, compKernel z = 2 * looseCost := by
  rw [integral_congr_ae compKernel_ae_eq, integral_looseKernel_eq_two_mul_looseCost]

/-- The comparison cost is positive, so the mass of the kernel is. -/
theorem integral_compKernel_pos : 0 < ∫ z, compKernel z := by
  rw [integral_compKernel, looseCost_eq]
  norm_num

/-- The patched kernel is supported in the Euclidean ball of radius `R`, which contains the
diamond of radius `R` since the norm is dominated by the diamond radius. -/
theorem hasCompactSupport_compKernel : HasCompactSupport compKernel := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 2 → ℝ) looseRadius)
    fun x hx => ?_
  have hnorm : looseRadius < ‖x‖ := by
    simpa [mem_closedBall_zero_iff, not_le] using hx
  have hx₀ : x ≠ 0 := fun h => by
    rw [h, norm_zero] at hnorm
    linarith [looseRadius_pos]
  rw [compKernel_of_ne hx₀]
  exact looseKernel_eq_zero_of_le (hnorm.le.trans (norm_le_diamondNorm x))

/-- Dilations of the patched kernel are even, because scaling commutes with the reflection. -/
theorem dilate_compKernel_neg (s : ℝ) (x : Fin 2 → ℝ) :
    dilate compKernel s (-x) = dilate compKernel s x := by
  rw [dilate, dilate, smul_neg, compKernel_neg]

/-- The `s`-dilation of the patched kernel is supported in the ball of radius `s R`: outside it
the rescaled point `s⁻¹ • x` has diamond radius beyond `R`. -/
theorem hasCompactSupport_dilate_compKernel {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (dilate compKernel s) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin 2 → ℝ) (s * looseRadius))
    fun x hx => ?_
  have hnorm : s * looseRadius < ‖x‖ := by
    simpa [mem_closedBall_zero_iff, not_le] using hx
  have h₁ : s * looseRadius < diamondNorm x := hnorm.trans_le (norm_le_diamondNorm x)
  have hd : looseRadius < diamondNorm (s⁻¹ • x) := by
    rw [diamondNorm_smul, abs_of_pos (inv_pos.2 hs)]
    calc looseRadius = s⁻¹ * (s * looseRadius) := by
          field_simp
      _ < s⁻¹ * diamondNorm x := mul_lt_mul_of_pos_left h₁ (inv_pos.2 hs)
  have hz₀ : s⁻¹ • x ≠ 0 := fun h => by
    rw [h, diamondNorm_eq_zero_iff.2 rfl] at hd
    linarith [looseRadius_pos]
  rw [dilate, compKernel_of_ne hz₀, looseKernel_eq_zero_of_le hd.le, mul_zero]

/-! ### The Bochner integral of a dilate -/

/-- A nonnegative function integrates to the real part of the Lebesgue integral of its enorm. -/
private theorem integral_eq_toReal_lintegral_enorm {L : (Fin 2 → ℝ) → ℝ} (hL₀ : ∀ z, 0 ≤ L z)
    (hLm : AEStronglyMeasurable L volume) : ∫ x, L x = (∫⁻ x, ‖L x‖ₑ).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hL₀) hLm]
  congr 1
  exact lintegral_congr fun x => (Real.enorm_eq_ofReal (hL₀ x)).symm

/-- **Dilation preserves the mass of a nonnegative integrable kernel.** The Jacobian `s²` of the
substitution `x = s • y` cancels the normalising factor `(s²)⁻¹` of `dilate`; in `ℝ≥0∞` this is
the `L¹` invariance `lintegral_enorm_dilate`. -/
theorem integral_dilate_eq {K : (Fin 2 → ℝ) → ℝ} (hK₀ : ∀ z, 0 ≤ K z) (hKint : Integrable K)
    {s : ℝ} (hs : 0 < s) : ∫ x, dilate K s x = ∫ x, K x := by
  rw [integral_eq_toReal_lintegral_enorm (dilate_nonneg (fun z => hK₀ z) hs)
      (integrable_dilate hKint hs).1,
    integral_eq_toReal_lintegral_enorm hK₀ hKint.1, lintegral_enorm_dilate K hs]

/-! ### The pointwise step -/

/-- **The pointwise bound at every scale.** Let `f` be a bounded, nonnegative, compactly supported
measurable obstacle and `λ > 0` a level. Solving the obstacle problem of order `1` with cap
`κ = λ / ∫ K` produces a nonnegative `u` and a density `σ ∈ [0, κ]` with `A u = σ − f` weakly, and
the contact set `Ω = {u > 0}` has measure at most `(∫ f) / κ = (∫ K) (∫ f) / λ`. For each scale
`s > 0` the dilation `K_s` again represents the generator against a finite measure and a point
mass (`exists_gen_dilate`), so `convolution_le_of_eq_zero` bounds `K_s ⋆ f` by `κ ∫ K_s = λ` at
almost every point where `u` vanishes.

The obstacle problem only provides `0 ≤ u` almost everywhere, while the convolution transfer needs
it pointwise, so `u` is replaced by its positive part `uPos`; this changes neither the contact set
nor any integral. -/
theorem exists_exceptional_set (β : Measure (Fin 2 → ℝ)) [IsFiniteMeasure β] {a : ℝ}
    (ha : 0 ≤ a)
    (hgen : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      ∫ x, compKernel x * jumpGen 1 ψ x = (∫ x, ψ x ∂β) - a * ψ 0)
    (f : (Fin 2 → ℝ) → ℝ) (Mf b : ℝ) (hfm : Measurable f) (hf₀ : ∀ x, 0 ≤ f x)
    (hfM : ∀ x, f x ≤ Mf) (hfsupp : ∀ x, b < ‖x‖ → f x = 0) (hb : 0 < b) (lam : ℝ)
    (hlam : 0 < lam) :
    ∃ Ω : Set (Fin 2 → ℝ), MeasurableSet Ω ∧
      volume Ω ≤ ENNReal.ofReal ((∫ x, compKernel x) * (∫ x, f x) / lam) ∧
      ∀ s : ℝ, 0 < s → ∀ᵐ x, x ∉ Ω → (∫ y, dilate compKernel s (x - y) * f y) ≤ lam := by
  have hMpos : 0 < ∫ x, compKernel x := integral_compKernel_pos
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = lam / (∫ x, compKernel x) := ⟨_, rfl⟩
  have hκ : 0 < κ := by
    rw [hκdef]
    exact div_pos hlam hMpos
  -- a bounded measurable function supported in a cube is integrable
  have hfint : Integrable f := by
    have hg : Integrable ((closedBall (0 : Fin 2 → ℝ) b).indicator fun _ => Mf) volume :=
      (integrableOn_const (volume_closedBall_ne_top hb.le)).integrable_indicator
        measurableSet_closedBall
    refine hg.mono' hfm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf₀ x)]
    by_cases hx : x ∈ closedBall (0 : Fin 2 → ℝ) b
    · rw [indicator_of_mem hx]
      exact hfM x
    · rw [indicator_of_notMem hx, hfsupp x (by simpa [mem_closedBall, dist_eq_norm] using hx)]
  obtain ⟨u, σ, hum, hu₀ae, huint, hσm, hσ₀, hσκ, hσint, hweak, -, -, hvolu⟩ :=
    exists_obstacle_solution (α := 1) zero_lt_one (by norm_num) hκ hfm hf₀ hfM hb hfsupp
  -- the positive part of the minimiser, nonnegative pointwise rather than almost everywhere
  obtain ⟨uPos, hupdef⟩ : ∃ v : (Fin 2 → ℝ) → ℝ, v = fun x => max (u x) 0 := ⟨_, rfl⟩
  have hupapp : ∀ x, uPos x = max (u x) 0 := fun x => by rw [hupdef]
  have hupm : Measurable uPos := by
    rw [hupdef]
    exact hum.max measurable_const
  have hup₀ : ∀ x, 0 ≤ uPos x := fun x => by
    rw [hupapp x]
    exact le_max_right _ _
  have hupeq : uPos =ᵐ[volume] u := by
    filter_upwards [hu₀ae] with x hx
    rw [hupapp x]
    exact max_eq_left hx
  have hupint : Integrable uPos := huint.congr hupeq.symm
  have hupweak : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      (∫ x, uPos x * jumpGen 1 ψ x) = ∫ x, (σ x - f x) * ψ x := by
    intro ψ hψ
    have heq : (fun x => uPos x * jumpGen 1 ψ x) =ᵐ[volume] fun x => u x * jumpGen 1 ψ x := by
      filter_upwards [hupeq] with x hx
      rw [hx]
    exact (integral_congr_ae heq).trans (hweak ψ hψ)
  refine ⟨{x | 0 < uPos x}, measurableSet_lt measurable_const hupm, ?_, ?_⟩
  · -- the contact set is the same for `u` and for its positive part
    have hset : {x | 0 < uPos x} = {x | 0 < u x} := by
      ext x
      simp [hupapp]
    have harith : (∫ x, f x) / κ = (∫ x, compKernel x) * (∫ x, f x) / lam := by
      rw [hκdef, div_div_eq_mul_div]
      ring
    rw [hset]
    exact hvolu.trans (le_of_eq (by rw [harith]))
  · intro s hs
    obtain ⟨β', hβ'fin, a', -, hgen'⟩ := exists_gen_dilate integrable_compKernel ha hgen hs
    haveI : IsFiniteMeasure β' := hβ'fin
    have hkey := convolution_le_of_eq_zero (α := 1) zero_lt_one (by norm_num)
      (fun z => dilate_nonneg (fun w => compKernel_nonneg w) hs z)
      (integrable_dilate integrable_compKernel hs) (dilate_compKernel_neg s)
      (hasCompactSupport_dilate_compKernel hs) hupm hupint hup₀ hσm hσint hσ₀ hσκ hfint
      hupweak hgen'
    have hlamEq : κ * (∫ y, dilate compKernel s y) = lam := by
      rw [integral_dilate_eq (fun z => compKernel_nonneg z) integrable_compKernel hs, hκdef,
        div_mul_cancel₀ lam hMpos.ne']
    -- the convolution written with the kernel translated instead of the obstacle
    have hflip : ∀ x : Fin 2 → ℝ, (∫ y, dilate compKernel s y * f (x - y))
        = ∫ y, dilate compKernel s (x - y) * f y := fun x =>
      calc (∫ y, dilate compKernel s y * f (x - y))
          = ∫ y, dilate compKernel s (x - y) * f (x - (x - y)) :=
            (integral_sub_left_eq_self
              (fun y => dilate compKernel s y * f (x - y)) volume x).symm
        _ = ∫ y, dilate compKernel s (x - y) * f y :=
            integral_congr_ae (Filter.Eventually.of_forall fun y => by
              simp only [sub_sub_cancel])
    filter_upwards [hkey] with x hx hxΩ
    have hnot : ¬ (0 < uPos x) := by simpa using hxΩ
    have hux : uPos x = 0 := le_antisymm (not_lt.1 hnot) (hup₀ x)
    rw [← hflip x, ← hlamEq]
    exact hx hux

/-! ### The weak type bound -/

/-- `ofReal (2 c) / 2 = ofReal c` in `ℝ≥0∞`, in the shape produced by the diamond reduction. -/
private theorem ofReal_two_mul_div_two (c : ℝ) :
    ENNReal.ofReal (2 * c) / 2 = ENNReal.ofReal c := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_div_assoc,
    ENNReal.mul_div_cancel (by simp) (by simp)]

/-- **The weak type bound for the centred maximal operator over cubes in the plane.** If the
patched comparison kernel represents the generator of order `1` against a finite measure `β` and a
nonnegative point mass `a` at the origin, then `c₂ ≤ ½ ∫ K = looseCost`.

The pointwise step `exists_exceptional_set` feeds `isKernelWeakTypeBound_of_pointwise`, which gives
the weak type bound `∫ K` for the kernel maximal operator; since `K ≥ 1` on the unit *diamond*,
`weakTypeConstant_two_le_of_diamond` halves it. -/
theorem weakTypeConstant_two_le_looseCost (β : Measure (Fin 2 → ℝ)) [IsFiniteMeasure β] {a : ℝ}
    (ha : 0 ≤ a)
    (hgen : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      ∫ x, compKernel x * jumpGen 1 ψ x = (∫ x, ψ x ∂β) - a * ψ 0) :
    weakTypeConstant 2 ≤ ENNReal.ofReal looseCost := by
  have hwt : IsKernelWeakTypeBound compKernel (ENNReal.ofReal (∫ x, compKernel x)) :=
    isKernelWeakTypeBound_of_pointwise (fun z => compKernel_nonneg z) integrable_compKernel
      fun g Mg c hgm hg₀ hgM hgsupp hc lam hlam =>
        exists_exceptional_set β ha hgen g Mg c hgm hg₀ hgM hgsupp hc lam hlam
  have h := weakTypeConstant_two_le_of_diamond integrable_compKernel
    (fun z hz => one_le_compKernel hz) hwt
  rwa [integral_compKernel, ofReal_two_mul_div_two] at h

/-- The weak type bound as an exact rational number. -/
theorem weakTypeConstant_two_le_rat (β : Measure (Fin 2 → ℝ)) [IsFiniteMeasure β] {a : ℝ}
    (ha : 0 ≤ a)
    (hgen : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      ∫ x, compKernel x * jumpGen 1 ψ x = (∫ x, ψ x ∂β) - a * ψ 0) :
    weakTypeConstant 2 ≤ ENNReal.ofReal (2787954611 / 718800000) := by
  rw [← looseCost_eq]
  exact weakTypeConstant_two_le_looseCost β ha hgen

/-- The weak type bound in decimal form: `c₂ < 3.879`. -/
theorem weakTypeConstant_two_le_upper (β : Measure (Fin 2 → ℝ)) [IsFiniteMeasure β] {a : ℝ}
    (ha : 0 ≤ a)
    (hgen : ∀ ψ : (Fin 2 → ℝ) → ℝ, IsTestFunction ψ →
      ∫ x, compKernel x * jumpGen 1 ψ x = (∫ x, ψ x ∂β) - a * ψ 0) :
    weakTypeConstant 2 ≤ ENNReal.ofReal (3879 / 1000) :=
  (weakTypeConstant_two_le_looseCost β ha hgen).trans
    (ENNReal.ofReal_le_ofReal looseCost_lt.le)

end CenteredMaximal.Cauchy
