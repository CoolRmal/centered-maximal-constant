/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Basic

/-!
# Reduction to the maximal operator of a dilation family of kernels

Let `K : ℝ² → ℝ` be a kernel with `K ≥ 1` on the unit cube `Q(0, 1)`, and let
`K_s(x) = s⁻² K(x / s)` be its dilations. The kernel maximal operator
`M_K f (x) = sup_{s > 0} ∫ K_s(x - y) |f(y)| dy` dominates the centred maximal function over
cubes: for `y ∈ Q(x, r)` one has `K_r(x - y) ≥ r⁻²`, while `|Q(x, r)|⁻¹ = (2r)⁻² = 4⁻¹ r⁻²`, so
`M f ≤ 4⁻¹ M_K f`. Consequently a weak type `(1, 1)` bound `M` for `M_K` gives the weak type
bound `M / 4` for the centred maximal operator, and `c₂ ≤ M / 4`.

* `dilate`, `kernelMaximal`, `IsKernelWeakTypeBound`: the dilations, the kernel maximal operator
  and its weak type bounds;
* `maximalFunction_le_kernelMaximal`: `M f ≤ 4⁻¹ M_K f` pointwise;
* `isWeakTypeBound_of_isKernelWeakTypeBound`: a weak type bound `M` for `M_K` gives the weak
  type bound `M / 4` for the centred maximal operator;
* `weakTypeConstant_two_le_of_isKernelWeakTypeBound`: hence `c₂ ≤ M / 4`.

The kernel maximal operator is defined through `ENNReal.ofReal (dilate K s (x - y))`, which
discards any negative part of `K`, so no sign hypothesis on `K` is needed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace CenteredMaximal

/-- The dilation `K_s(x) = s⁻² K(x / s)` of a kernel on the plane. -/
def dilate (K : (Fin 2 → ℝ) → ℝ) (s : ℝ) (x : Fin 2 → ℝ) : ℝ := (s ^ 2)⁻¹ * K (s⁻¹ • x)

/-- The maximal operator of the dilation family of `K` applied to `|f|`:
`sup_{s > 0} ∫ K_s(x - y) |f(y)| dy`, with values in `[0, ∞]`. -/
def kernelMaximal (K f : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) : ℝ≥0∞ :=
  ⨆ (s : ℝ) (_ : 0 < s), ∫⁻ y, ENNReal.ofReal (dilate K s (x - y)) * ‖f y‖ₑ

/-- `M` is a weak type `(1, 1)` bound for the kernel maximal operator of `K`: for every integrable
`f : ℝ² → ℝ` and every level `α ∈ [0, ∞]`, `α · |{x : M_K f (x) > α}| ≤ M · ‖f‖₁`. -/
def IsKernelWeakTypeBound (K : (Fin 2 → ℝ) → ℝ) (M : ℝ≥0∞) : Prop :=
  ∀ f : (Fin 2 → ℝ) → ℝ, Integrable f → ∀ α : ℝ≥0∞,
    α * volume {x | α < kernelMaximal K f x} ≤ M * ∫⁻ x, ‖f x‖ₑ

/-- Every term of the dilation family is at most the kernel maximal operator. -/
theorem le_kernelMaximal (K f : (Fin 2 → ℝ) → ℝ) (x : Fin 2 → ℝ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ y, ENNReal.ofReal (dilate K s (x - y)) * ‖f y‖ₑ ≤ kernelMaximal K f x :=
  le_iSup₂ (f := fun s (_ : 0 < s) ↦ ∫⁻ y, ENNReal.ofReal (dilate K s (x - y)) * ‖f y‖ₑ) s hs

/-- The kernel maximal operator is monotone in `|f|`. -/
theorem kernelMaximal_mono (K : (Fin 2 → ℝ) → ℝ) {f g : (Fin 2 → ℝ) → ℝ}
    (h : ∀ y, ‖f y‖ₑ ≤ ‖g y‖ₑ) (x : Fin 2 → ℝ) : kernelMaximal K f x ≤ kernelMaximal K g x :=
  iSup₂_mono fun _ _ ↦ lintegral_mono fun y ↦ mul_le_mul_right (h y) _

/-- If `K ≥ 1` on the unit cube, then for `y` in the cube `Q(x, r)` the constant
`|Q(x, r)|⁻¹ = (2r)⁻²` is at most `4⁻¹ K_r(x - y)`. -/
theorem inv_volume_closedBall_le_ofReal_dilate {K : (Fin 2 → ℝ) → ℝ}
    (hK₁ : ∀ z ∈ closedBall (0 : Fin 2 → ℝ) 1, 1 ≤ K z) {x y : Fin 2 → ℝ} {r : ℝ} (hr : 0 < r)
    (hy : y ∈ closedBall x r) :
    (volume (closedBall x r))⁻¹ ≤ 4⁻¹ * ENNReal.ofReal (dilate K r (x - y)) := by
  -- `(x - y) / r` lies in the unit cube, so `K((x - y) / r) ≥ 1`
  have hz : r⁻¹ • (x - y) ∈ closedBall (0 : Fin 2 → ℝ) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_of_nonneg hr.le]
    exact inv_mul_le_one_of_le₀ (by rwa [mem_closedBall', dist_eq_norm] at hy) hr.le
  rw [volume_closedBall_eq x hr.le,
    ← ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < (2 * r) ^ 2)]
  calc ENNReal.ofReal (((2 * r) ^ 2)⁻¹) = ENNReal.ofReal (4⁻¹ * (r ^ 2)⁻¹) := by congr 1; ring
    _ ≤ ENNReal.ofReal (4⁻¹ * dilate K r (x - y)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
          (le_mul_of_one_le_right (by positivity) (hK₁ _ hz)) (by norm_num))
    _ = 4⁻¹ * ENNReal.ofReal (dilate K r (x - y)) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num),
          ENNReal.ofReal_ofNat]

/-- If `K ≥ 1` on the unit cube, the centred maximal function over cubes is at most `4⁻¹` times
the kernel maximal operator of `K`: the cube average of radius `r` is bounded by the term `s = r`
of the dilation family, using `inv_volume_closedBall_le_ofReal_dilate` on the cube. -/
theorem maximalFunction_le_kernelMaximal {K : (Fin 2 → ℝ) → ℝ}
    (hK₁ : ∀ z ∈ closedBall (0 : Fin 2 → ℝ) 1, 1 ≤ K z) (f : (Fin 2 → ℝ) → ℝ)
    (x : Fin 2 → ℝ) : maximalFunction f x ≤ 4⁻¹ * kernelMaximal K f x := by
  refine iSup₂_le fun r hr ↦ ?_
  calc (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ
      ≤ ∫⁻ y in closedBall x r, (volume (closedBall x r))⁻¹ * ‖f y‖ₑ :=
        lintegral_const_mul_le _ _
    _ ≤ ∫⁻ y in closedBall x r, 4⁻¹ * (ENNReal.ofReal (dilate K r (x - y)) * ‖f y‖ₑ) :=
        setLIntegral_mono' measurableSet_closedBall fun y hy ↦ by
          rw [← mul_assoc]
          exact mul_le_mul_left (inv_volume_closedBall_le_ofReal_dilate hK₁ hr hy) _
    _ ≤ ∫⁻ y, 4⁻¹ * (ENNReal.ofReal (dilate K r (x - y)) * ‖f y‖ₑ) :=
        setLIntegral_le_lintegral _ _
    _ = 4⁻¹ * ∫⁻ y, ENNReal.ofReal (dilate K r (x - y)) * ‖f y‖ₑ :=
        lintegral_const_mul' _ _ (by simp)
    _ ≤ 4⁻¹ * kernelMaximal K f x := mul_le_mul_right (le_kernelMaximal K f x hr) _

/-- A weak type `(1, 1)` bound `M` for the kernel maximal operator of a kernel `K ≥ 1` on the unit
cube gives the weak type bound `M / 4` for the centred maximal operator over cubes in the plane,
since `M f ≤ 4⁻¹ M_K f` by `maximalFunction_le_kernelMaximal`. -/
theorem isWeakTypeBound_of_isKernelWeakTypeBound {K : (Fin 2 → ℝ) → ℝ} {M : ℝ≥0∞}
    (hK₁ : ∀ z ∈ closedBall (0 : Fin 2 → ℝ) 1, 1 ≤ K z) (h : IsKernelWeakTypeBound K M) :
    IsWeakTypeBound 2 (M / 4) := by
  intro f hf α
  -- `α < M f (x) ≤ 4⁻¹ M_K f (x)` gives `4 α < M_K f (x)`
  have hsub : {x | α < maximalFunction f x} ⊆ {x | 4 * α < kernelMaximal K f x} := fun x hx ↦ by
    have hx' : α < kernelMaximal K f x / 4 :=
      ENNReal.div_eq_inv_mul ▸ lt_of_lt_of_le hx (maximalFunction_le_kernelMaximal hK₁ f x)
    exact ENNReal.mul_lt_of_lt_div' hx'
  calc α * volume {x | α < maximalFunction f x}
      = 4⁻¹ * (4 * α * volume {x | α < maximalFunction f x}) := by
        rw [mul_assoc, ENNReal.inv_mul_cancel_left (by simp) (by simp)]
    _ ≤ 4⁻¹ * (4 * α * volume {x | 4 * α < kernelMaximal K f x}) :=
        mul_le_mul_right (mul_le_mul_right (measure_mono hsub) _) _
    _ ≤ 4⁻¹ * (M * ∫⁻ x, ‖f x‖ₑ) := mul_le_mul_right (h f hf (4 * α)) _
    _ = M / 4 * ∫⁻ x, ‖f x‖ₑ := by rw [ENNReal.div_eq_inv_mul, mul_assoc]

/-- A weak type `(1, 1)` bound `M` for the kernel maximal operator of a kernel `K ≥ 1` on the unit
cube gives `c₂ ≤ M / 4`. -/
theorem weakTypeConstant_two_le_of_isKernelWeakTypeBound {K : (Fin 2 → ℝ) → ℝ} {M : ℝ≥0∞}
    (hK₁ : ∀ z ∈ closedBall (0 : Fin 2 → ℝ) 1, 1 ≤ K z) (h : IsKernelWeakTypeBound K M) :
    weakTypeConstant 2 ≤ M / 4 :=
  weakTypeConstant_le (isWeakTypeBound_of_isKernelWeakTypeBound hK₁ h)

end CenteredMaximal
