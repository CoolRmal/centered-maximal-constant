/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Analysis.BoundedFunctional
public import CenteredMaximal.Analysis.JumpGenerator
public import CenteredMaximal.Cauchy.LooseKernel
public import CenteredMaximal.Transfer.AllScales
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Two changes of variables for the transfer argument

This file supplies the coordinate changes that the final assembly of the upper bound needs. Both
are pure measure theory.

## Dilation of the generator identity

The dilation `K_s(x) = s⁻² K(x / s)` of a kernel acts on the jump generator by the substitution
`x = s • y`, whose Jacobian `s²` cancels the normalising factor `(s²)⁻¹` of `dilate`, together
with the scaling law `jumpGen α (φ (s ·)) (y) = s^α jumpGen α φ (s • y)` of the generator. The
result is `jumpGen_dilate_eq`:
`∫ K_s(x) jumpGen α φ (x) dx = s^{−α} ∫ K(y) jumpGen α (φ (s ·)) (y) dy`.

Consequently, if `K` represents the generator against a finite measure `β` and a point mass `a`
at the origin, then so does every dilation `K_s`, with `β` pushed forward by `z ↦ s • z` and both
`β` and `a` scaled by `s^{−α}` (`exists_gen_dilate`).

## The diamond-to-square change of variables

The linear map `diamondToSquare : (u, v) ↦ (u + v, u − v)` turns the diamond norm `|u| + |v|` into
the sup norm `max(|x₀|, |x₁|)` (`norm_diamondToSquare`), so it carries the unit diamond onto the
unit cube. Its determinant is `−2` (`det_diamondToSquare`), so it halves Lebesgue measure
(`map_diamondToSquare_volume`).

* `lintegral_comp_diamondToSquare`, `integral_comp_diamondToSquare`,
  `volume_preimage_diamondToSquare`: the change of variables for integrals and for volumes; the
  volume statement holds for an arbitrary, not necessarily measurable, set, because a measurable
  equivalence computes the pushforward measure of every set;
* `isKernelWeakTypeBound_comp`: a weak type `(1, 1)` bound `M` for the kernel maximal operator of
  `K` transports to the bound `2 M` for the conjugated kernel `K ∘ diamondToSquare⁻¹`, the loss
  being the Jacobian;
* `weakTypeConstant_two_le_of_diamond`: hence a kernel that is at least `1` on the unit *diamond*
  and has weak type bound `M` gives `c₂ ≤ M / 2`, twice as good as the cube bound `M / 4`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace CenteredMaximal

/-! ### Dilation of the generator identity -/

section TestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A dilate `z ↦ φ (c • z)` of a test function is a test function, for `c ≠ 0`. -/
theorem IsTestFunction.comp_smul {φ : E → ℝ} (hφ : IsTestFunction φ) {c : ℝ} (hc : c ≠ 0) :
    IsTestFunction fun z => φ (c • z) := by
  refine ⟨?_, hφ.2.comp_smul hc⟩
  exact hφ.1.comp (contDiff_id.const_smul c)

end TestFunction

/-- The scaling law of the generator in the form needed for the change of variables: the generator
of `φ` at the dilated point `s • y` is `s^{−α}` times the generator of the dilate `z ↦ φ (s • z)`
at `y`. -/
theorem jumpGen_smul_eq {s : ℝ} (hs : 0 < s) (α : ℝ) (φ : (Fin 2 → ℝ) → ℝ) (y : Fin 2 → ℝ) :
    jumpGen α φ (s • y) = s ^ (-α) * jumpGen α (fun z => φ (s • z)) y := by
  have h : jumpGen α (fun z => φ (s • z)) y = s ^ α * jumpGen α φ (s • y) := by
    have h' := jumpGen_comp_smul_inv (inv_pos.2 hs) α φ y
    rw [inv_inv] at h'
    rwa [Real.inv_rpow hs.le, Real.rpow_neg hs.le, inv_inv] at h'
  rw [h, ← mul_assoc, ← Real.rpow_add hs, neg_add_cancel, Real.rpow_zero, one_mul]

/-- **Dilation of the generator identity.** For `s > 0` the dilation `K_s` pairs with the generator
of `φ` exactly as `K` pairs with the generator of the dilate `z ↦ φ (s • z)`, up to the factor
`s^{−α}`: the substitution `x = s • y` has Jacobian `s²`, which cancels the normalisation `(s²)⁻¹`
of `dilate`, and `jumpGen_smul_eq` supplies `s^{−α}`. -/
theorem jumpGen_dilate_eq {α s : ℝ} (hs : 0 < s) (K : (Fin 2 → ℝ) → ℝ) (_hK : Integrable K)
    (φ : (Fin 2 → ℝ) → ℝ) (_hφ : IsTestFunction φ) :
    ∫ x, dilate K s x * jumpGen α φ x
      = s ^ (-α) * ∫ y, K y * jumpGen α (fun z => φ (s • z)) y := by
  have hne : (s : ℝ) ^ 2 ≠ 0 := by positivity
  have hcov := Measure.integral_comp_smul (volume : Measure (Fin 2 → ℝ))
    (fun y => K y * jumpGen α φ (s • y)) s⁻¹
  simp only [smul_inv_smul₀ hs.ne', Module.finrank_fin_fun, inv_pow, inv_inv,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ s ^ 2), smul_eq_mul] at hcov
  have hL : ∫ x, dilate K s x * jumpGen α φ x
      = (s ^ 2)⁻¹ * ∫ x, K (s⁻¹ • x) * jumpGen α φ x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [dilate]; ring)
  have hR : ∫ y, K y * jumpGen α φ (s • y)
      = s ^ (-α) * ∫ y, K y * jumpGen α (fun z => φ (s • z)) y := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show K y * jumpGen α φ (s • y)
      = s ^ (-α) * (K y * jumpGen α (fun z => φ (s • z)) y)
    rw [jumpGen_smul_eq hs]
    ring
  rw [hL, hcov, hR, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-- **The generator identity survives dilation.** If the kernel `K` represents the generator of
order `α` against a finite measure `β` and a point mass `a` at the origin, then so does every
dilation `K_s`: the measure is pushed forward by `z ↦ s • z` and both it and the point mass are
scaled by `s^{−α}`. -/
theorem exists_gen_dilate {α a : ℝ} {K : (Fin 2 → ℝ) → ℝ} (hK : Integrable K)
    {β : Measure (Fin 2 → ℝ)} [IsFiniteMeasure β] (ha : 0 ≤ a)
    (hKgen : ∀ φ : (Fin 2 → ℝ) → ℝ, IsTestFunction φ →
      ∫ x, K x * jumpGen α φ x = (∫ x, φ x ∂β) - a * φ 0)
    {s : ℝ} (hs : 0 < s) :
    ∃ β' : Measure (Fin 2 → ℝ), IsFiniteMeasure β' ∧ ∃ a' : ℝ, 0 ≤ a' ∧
      ∀ φ : (Fin 2 → ℝ) → ℝ, IsTestFunction φ →
        ∫ x, dilate K s x * jumpGen α φ x = (∫ x, φ x ∂β') - a' * φ 0 := by
  haveI hmapfin : IsFiniteMeasure (Measure.map (fun z : Fin 2 → ℝ => s • z) β) :=
    β.isFiniteMeasure_map _
  refine ⟨ENNReal.ofReal (s ^ (-α)) • Measure.map (fun z : Fin 2 → ℝ => s • z) β,
    ⟨?_⟩, s ^ (-α) * a, mul_nonneg (Real.rpow_nonneg hs.le _) ha, fun φ hφ => ?_⟩
  · rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  · have hmap : ∫ x, φ x ∂(Measure.map (fun z : Fin 2 → ℝ => s • z) β) = ∫ z, φ (s • z) ∂β :=
      integral_map_equiv (Homeomorph.smul (isUnit_iff_ne_zero.2 hs.ne').unit).toMeasurableEquiv φ
    rw [jumpGen_dilate_eq hs K hK φ hφ, hKgen _ (hφ.comp_smul hs.ne'), integral_smul_measure,
      hmap, ENNReal.toReal_ofReal (Real.rpow_nonneg hs.le _), smul_eq_mul, smul_zero]
    ring

/-! ### The diamond-to-square change of variables -/

/-- The linear change of variables `(u, v) ↦ (u + v, u − v)` of the plane. It carries the unit
diamond `|u| + |v| ≤ 1` onto the unit cube `max(|x₀|, |x₁|) ≤ 1` and has determinant `−2`. -/
def diamondToSquare : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) where
  toFun z := ![z 0 + z 1, z 0 - z 1]
  map_add' z w := by funext i; fin_cases i <;> simp <;> ring
  map_smul' c z := by funext i; fin_cases i <;> simp <;> ring
  invFun x := ![(x 0 + x 1) / 2, (x 0 - x 1) / 2]
  left_inv z := by funext i; fin_cases i <;> simp
  right_inv x := by funext i; fin_cases i <;> simp <;> ring

@[simp]
theorem diamondToSquare_apply_zero (z : Fin 2 → ℝ) : diamondToSquare z 0 = z 0 + z 1 := rfl

@[simp]
theorem diamondToSquare_apply_one (z : Fin 2 → ℝ) : diamondToSquare z 1 = z 0 - z 1 := rfl

/-- The norm of the plane is the maximum of the absolute values of the two coordinates. -/
private theorem norm_fin_two (x : Fin 2 → ℝ) : ‖x‖ = max |x 0| |x 1| := by
  refine le_antisymm ?_ (max_le (by simpa using norm_le_pi_norm x 0)
    (by simpa using norm_le_pi_norm x 1))
  rw [pi_norm_le_iff_of_nonneg (by positivity), Fin.forall_fin_two]
  exact ⟨by simp, by simp⟩

/-- The key geometric identity behind the change of variables: `max |u + v| |u − v| = |u| + |v|`,
by splitting on the signs of the four quantities involved. -/
private theorem max_abs_add_abs_sub (u v : ℝ) : max |u + v| |u - v| = |u| + |v| := by
  rcases abs_cases u with ⟨h3, s3⟩ | ⟨h3, s3⟩ <;> rcases abs_cases v with ⟨h4, s4⟩ | ⟨h4, s4⟩ <;>
    rcases abs_cases (u + v) with ⟨h1, s1⟩ | ⟨h1, s1⟩ <;>
    rcases abs_cases (u - v) with ⟨h2, s2⟩ | ⟨h2, s2⟩ <;>
    rw [h1, h2, h3, h4, max_def] <;> split_ifs <;> linarith

/-- **The change of variables turns the diamond norm into the sup norm**:
`‖(u + v, u − v)‖ = |u| + |v|`. -/
theorem norm_diamondToSquare (z : Fin 2 → ℝ) : ‖diamondToSquare z‖ = Cauchy.diamondNorm z := by
  show ‖diamondToSquare z‖ = |z 0| + |z 1|
  rw [norm_fin_two, diamondToSquare_apply_zero, diamondToSquare_apply_one]
  exact max_abs_add_abs_sub _ _

/-- The determinant of the diamond-to-square change of variables is `−2`. -/
theorem det_diamondToSquare :
    LinearMap.det (diamondToSquare : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ) = -2 := by
  rw [← LinearMap.det_toMatrix' (diamondToSquare : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ),
    Matrix.det_fin_two]
  norm_num [LinearMap.toMatrix'_apply, Pi.single_apply]

/-- The diamond-to-square change of variables as a measurable equivalence. -/
def diamondToSquareEquiv : (Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) :=
  diamondToSquare.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv

@[simp]
theorem coe_diamondToSquareEquiv : ⇑diamondToSquareEquiv = ⇑diamondToSquare := rfl

/-- The change of variables halves Lebesgue measure, since `|det| = 2`. -/
theorem map_diamondToSquare_volume :
    Measure.map diamondToSquare (volume : Measure (Fin 2 → ℝ))
      = ENNReal.ofReal 2⁻¹ • volume := by
  have hdet : LinearMap.det (diamondToSquare : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ) ≠ 0 := by
    rw [det_diamondToSquare]; norm_num
  rw [show (⇑diamondToSquare : (Fin 2 → ℝ) → Fin 2 → ℝ)
      = ((diamondToSquare : (Fin 2 → ℝ) →ₗ[ℝ] Fin 2 → ℝ) : (Fin 2 → ℝ) → Fin 2 → ℝ) from rfl,
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, det_diamondToSquare]
  norm_num

/-- `2 · ½ = 1` in `ℝ≥0∞`, in the shape produced by the Jacobian of the change of variables. -/
private theorem two_mul_ofReal_inv_two : (2 : ℝ≥0∞) * ENNReal.ofReal 2⁻¹ = 1 := by
  rw [ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat,
    ENNReal.mul_inv_cancel (by simp) (by simp)]

/-- The `lintegral` change of variables: composing with `diamondToSquare` halves the integral. -/
theorem lintegral_comp_diamondToSquare (g : (Fin 2 → ℝ) → ℝ≥0∞) :
    ∫⁻ z, g (diamondToSquare z) = ENNReal.ofReal 2⁻¹ * ∫⁻ y, g y := by
  have he : ∫⁻ z, g (diamondToSquare z)
      = ∫⁻ y, g y ∂(Measure.map diamondToSquare (volume : Measure (Fin 2 → ℝ))) :=
    (lintegral_map_equiv g diamondToSquareEquiv).symm
  rw [he, map_diamondToSquare_volume, lintegral_smul_measure, smul_eq_mul]

/-- The `lintegral` change of variables, solved for the untransformed integral. -/
theorem lintegral_eq_two_mul_comp_diamondToSquare (g : (Fin 2 → ℝ) → ℝ≥0∞) :
    ∫⁻ y, g y = 2 * ∫⁻ z, g (diamondToSquare z) := by
  rw [lintegral_comp_diamondToSquare, ← mul_assoc, two_mul_ofReal_inv_two, one_mul]

/-- The Bochner integral change of variables: composing with `diamondToSquare` halves the
integral. -/
theorem integral_comp_diamondToSquare (g : (Fin 2 → ℝ) → ℝ) :
    ∫ z, g (diamondToSquare z) = 2⁻¹ * ∫ y, g y := by
  have he : ∫ z, g (diamondToSquare z)
      = ∫ y, g y ∂(Measure.map diamondToSquare (volume : Measure (Fin 2 → ℝ))) :=
    (integral_map_equiv diamondToSquareEquiv g).symm
  rw [he, map_diamondToSquare_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (by norm_num), smul_eq_mul]

/-- The preimage of an arbitrary set under `diamondToSquare` has half its volume. No measurability
is needed: a measurable equivalence computes the pushforward measure of every set. -/
theorem volume_preimage_diamondToSquare (S : Set (Fin 2 → ℝ)) :
    volume (diamondToSquare ⁻¹' S) = ENNReal.ofReal 2⁻¹ * volume S := by
  rw [Measure.addHaar_preimage_linearEquiv volume diamondToSquare, LinearEquiv.det_coe_symm,
    det_diamondToSquare]
  norm_num

/-- The volume statement solved for the volume of the original set. -/
theorem volume_eq_two_mul_preimage_diamondToSquare (S : Set (Fin 2 → ℝ)) :
    volume S = 2 * volume (diamondToSquare ⁻¹' S) := by
  rw [volume_preimage_diamondToSquare, ← mul_assoc, two_mul_ofReal_inv_two, one_mul]

/-- Integrability is preserved by the change of variables. -/
theorem integrable_comp_diamondToSquare {f : (Fin 2 → ℝ) → ℝ} (hf : Integrable f) :
    Integrable fun z => f (diamondToSquare z) := by
  have h : Integrable f (Measure.map diamondToSquareEquiv (volume : Measure (Fin 2 → ℝ))) := by
    rw [show Measure.map diamondToSquareEquiv (volume : Measure (Fin 2 → ℝ))
        = Measure.map diamondToSquare volume from rfl, map_diamondToSquare_volume]
    exact hf.smul_measure ENNReal.ofReal_ne_top
  exact (integrable_map_equiv diamondToSquareEquiv f).mp h

/-- The dilation of the conjugated kernel at a transformed point is the dilation of the original
kernel, because the change of variables commutes with the scalings. -/
theorem dilate_comp_diamondToSquare (K : (Fin 2 → ℝ) → ℝ) (s : ℝ) (u : Fin 2 → ℝ) :
    dilate (fun x => K (diamondToSquare.symm x)) s (diamondToSquare u) = dilate K s u := by
  have h : s⁻¹ • diamondToSquare u = diamondToSquare (s⁻¹ • u) := (map_smul _ _ _).symm
  simp only [dilate, h, LinearEquiv.symm_apply_apply]

/-- **The kernel maximal operator transported by the change of variables.** With
`K̃ = K ∘ diamondToSquare⁻¹` one has `M_{K̃} f (T z) = 2 M_K (f ∘ T) z`, the factor `2` being the
Jacobian of the substitution in the convolution integral. -/
theorem kernelMaximal_comp (K f : (Fin 2 → ℝ) → ℝ) (z : Fin 2 → ℝ) :
    kernelMaximal (fun x => K (diamondToSquare.symm x)) f (diamondToSquare z)
      = 2 * kernelMaximal K (fun w => f (diamondToSquare w)) z := by
  have key : ∀ s : ℝ, ∫⁻ y, ENNReal.ofReal (dilate (fun x => K (diamondToSquare.symm x)) s
        (diamondToSquare z - y)) * ‖f y‖ₑ
      = 2 * ∫⁻ w, ENNReal.ofReal (dilate K s (z - w)) * ‖f (diamondToSquare w)‖ₑ := by
    intro s
    have hg := lintegral_eq_two_mul_comp_diamondToSquare fun y =>
      ENNReal.ofReal (dilate (fun x => K (diamondToSquare.symm x)) s
        (diamondToSquare z - y)) * ‖f y‖ₑ
    simpa only [← map_sub, dilate_comp_diamondToSquare] using hg
  simp only [kernelMaximal, key, ENNReal.mul_iSup]

/-- **Transport of the weak type bound.** If `M` is a weak type `(1, 1)` bound for the kernel
maximal operator of `K`, then `2 M` is one for the conjugated kernel
`K̃ = K ∘ diamondToSquare⁻¹`. The level `α` for `K̃` corresponds to the level `α / 2` for `K`, and
each of the two sides picks up one factor `2` from the Jacobian. -/
theorem isKernelWeakTypeBound_comp {K : (Fin 2 → ℝ) → ℝ} (_hK : Integrable K) {M : ℝ≥0∞}
    (h : IsKernelWeakTypeBound K M) :
    IsKernelWeakTypeBound (fun x => K (diamondToSquare.symm x)) (2 * M) := by
  intro f hf α
  have hgint : Integrable fun w => f (diamondToSquare w) := integrable_comp_diamondToSquare hf
  have hsub : diamondToSquare ⁻¹'
        {x | α < kernelMaximal (fun x => K (diamondToSquare.symm x)) f x}
      ⊆ {z | α / 2 < kernelMaximal K (fun w => f (diamondToSquare w)) z} := fun z hz =>
    ENNReal.div_lt_of_lt_mul' (by rw [← kernelMaximal_comp K f z]; exact hz)
  have hα2 : (2 : ℝ≥0∞) * (α / 2) = α := by
    rw [ENNReal.div_eq_inv_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]
  calc α * volume {x | α < kernelMaximal (fun x => K (diamondToSquare.symm x)) f x}
      = 2 * (2 * (α / 2)) * volume (diamondToSquare ⁻¹'
          {x | α < kernelMaximal (fun x => K (diamondToSquare.symm x)) f x}) := by
        rw [volume_eq_two_mul_preimage_diamondToSquare, hα2]
        ring
    _ = 4 * (α / 2 * volume (diamondToSquare ⁻¹'
          {x | α < kernelMaximal (fun x => K (diamondToSquare.symm x)) f x})) := by
        generalize α / 2 = t
        ring
    _ ≤ 4 * (α / 2 * volume {z | α / 2 < kernelMaximal K (fun w => f (diamondToSquare w)) z}) :=
        mul_le_mul_right (mul_le_mul_right (measure_mono hsub) _) _
    _ ≤ 4 * (M * ∫⁻ w, ‖f (diamondToSquare w)‖ₑ) := mul_le_mul_right (h _ hgint (α / 2)) _
    _ = 2 * M * ∫⁻ x, ‖f x‖ₑ := by
        rw [lintegral_eq_two_mul_comp_diamondToSquare fun y => ‖f y‖ₑ]
        ring

/-- **The payoff of the change of variables.** An integrable kernel that is at least `1` on the
unit *diamond* `|u| + |v| ≤ 1` and has weak type bound `M` gives `c₂ ≤ M / 2`. The conjugated
kernel `K ∘ diamondToSquare⁻¹` is at least `1` on the unit cube by `norm_diamondToSquare` and has
weak type bound `2 M` by `isKernelWeakTypeBound_comp`, so the cube bound
`weakTypeConstant_two_le_of_isKernelWeakTypeBound` gives `c₂ ≤ 2 M / 4 = M / 2`. -/
theorem weakTypeConstant_two_le_of_diamond {K : (Fin 2 → ℝ) → ℝ} {M : ℝ≥0∞} (hK : Integrable K)
    (hK₁ : ∀ z, Cauchy.diamondNorm z ≤ 1 → 1 ≤ K z) (h : IsKernelWeakTypeBound K M) :
    weakTypeConstant 2 ≤ M / 2 := by
  have h₁ : ∀ x ∈ closedBall (0 : Fin 2 → ℝ) 1, 1 ≤ K (diamondToSquare.symm x) := by
    intro x hx
    refine hK₁ _ ?_
    rw [← norm_diamondToSquare, LinearEquiv.apply_symm_apply]
    exact mem_closedBall_zero_iff.1 hx
  refine (weakTypeConstant_two_le_of_isKernelWeakTypeBound h₁
    (isKernelWeakTypeBound_comp hK h)).trans (le_of_eq ?_)
  rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num,
    ENNReal.mul_div_mul_left M 2 (by simp) (by simp)]

end CenteredMaximal
