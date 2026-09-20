/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Cauchy.Certificate
public import CenteredMaximal.Cauchy.Harmonic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# The Cauchy generator of the comparison kernel is nonnegative

The one-bump comparison kernel `looseKernel = K_R − ε ψ` of `CenteredMaximal.Cauchy.LooseKernel`,
with `R = looseRadius`, `ε = looseBump` and `r = diamondNorm`, has an almost everywhere
nonnegative Cauchy jump generator:

`ae_jumpGen_looseKernel_nonneg`: `∀ᵐ z, 0 ≤ jumpGen 1 looseKernel z`.

## The affine splitting

Away from the origin the pointwise identity `(R/r − 1)₊ = (R/r − 1) + (1 − R/r)₊` splits the
singular profile into an affine function of the Cauchy potential plus the exterior tail
(`looseCusp_eq_add`), so that `looseKernel = looseKernelAff` off the origin
(`looseKernel_eq_affine`) with

`looseKernelAff z = (c₁ potential z + c₂) + (tail R z − ε ψ z)`,   `c₁ = 2πR/(R − 1)`,
`c₂ = −1/(R − 1)`,

using `2πR potential z = R/r`. Both kernels take the same values along every coordinate line
through a point off the two axes, because such a line never meets the origin
(`add_single_ne_zero`), so their generators agree there (`jumpGen_looseKernel_eq_aff`). The affine
potential part is generator-harmonic off the axes
(`CenteredMaximal.Cauchy.jumpGen_affine_potential_eq_zero`), whence inside the open diamond

`jumpGen_looseKernel_eq`: `jumpGen 1 looseKernel z = jumpGen 1 (tail R) z − ε jumpGen 1 ψ z`,

the linearity of the generator being applied through the integrability of the three one-dimensional
integrands (`integrable_profileDiff`, `integrable_secondDiff_tail`, `integrable_bumpSliceDiff`).

## The three regimes

Inside the unit diamond the exact bounds `jumpGen_tail_ge_Jfun_sharp` and `jumpGen_bump_le` reduce
the sign to `certificate`, `ε R (R − 1) T r ≤ J (2r/R)`. Between the unit diamond and the diamond
of radius `R` they reduce it, through `one_le_Jfun` and `jumpGen_bump_le_exterior`, to
`exterior_certificate`, `ε (2 − 2 log 2) ≤ 1/(R (R − 1))`. Beyond the diamond of radius `R` the
kernel vanishes at `z` while remaining nonnegative everywhere, so every second difference along a
coordinate line is nonnegative and no integrability is needed at all. Together these give
`jumpGen_looseKernel_nonneg` at every point off the two coordinate axes, and the axes are null
(`volume_coord_eq_zero`).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set

namespace CenteredMaximal.Cauchy

/-- The affine form of the loose kernel away from the origin: an affine function of the Cauchy
potential plus the exterior tail minus the bump. -/
def looseKernelAff (z : Fin 2 → ℝ) : ℝ :=
  (2 * Real.pi * looseRadius / (looseRadius - 1) * potential z + -(1 / (looseRadius - 1)))
    + (tail looseRadius z - looseBump * bump z)

/-! ### Coordinates along a line through a point off the axes -/

private theorem diamondNorm_eq_abs_add' (z : Fin 2 → ℝ) (j : Fin 2) :
    diamondNorm z = |z j| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem diamondNorm_add_single' (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z + s • Pi.single j 1) = |z j + s| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem coord_ne_zero {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2) :
    z j ≠ 0 := by
  fin_cases j
  · simpa using h0
  · simpa using h1

private theorem coord_succ_ne_zero {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2) :
    z (j + 1) ≠ 0 := by
  fin_cases j
  · simpa using h1
  · simpa using h0

/-- A coordinate line through a point off the two axes never meets the origin: the displacement
does not touch the other coordinate, which stays nonzero. -/
private theorem add_single_ne_zero {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2)
    (t : ℝ) : z + t • Pi.single j 1 ≠ 0 := by
  intro h
  have hd : diamondNorm (z + t • Pi.single j 1) = 0 := diamondNorm_eq_zero_iff.2 h
  rw [diamondNorm_add_single'] at hd
  have hpos := abs_pos.2 (coord_succ_ne_zero h0 h1 j)
  linarith [abs_nonneg (z j + t)]

private theorem sub_single_ne_zero {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2)
    (t : ℝ) : z - t • Pi.single j 1 ≠ 0 := by
  rw [sub_eq_add_neg, ← neg_smul]
  exact add_single_ne_zero h0 h1 j (-t)

/-! ### The affine splitting of the kernel -/

/-- **The pointwise splitting of the singular profile**: `(R/t − 1)₊ = (R/t − 1) + (1 − R/t)₊`,
divided by `R − 1`. -/
theorem looseCusp_eq_add {r : ℝ} (hr : 0 < r) :
    looseCusp r = (looseRadius / r - 1) / (looseRadius - 1) + tailProfile looseRadius r := by
  rcases le_or_gt r looseRadius with h | h
  · have hm : (0 : ℝ) ≤ looseRadius / r - 1 := by
      rw [sub_nonneg, le_div_iff₀ hr, one_mul]
      exact h
    rw [looseCusp, max_eq_left hm, tailProfile, max_eq_right (by linarith), zero_div, add_zero]
  · have hm : looseRadius / r - 1 ≤ 0 := by
      rw [sub_nonpos, div_le_one (by linarith : (0 : ℝ) < r)]
      exact h.le
    rw [looseCusp, max_eq_right hm, tailProfile, max_eq_left (by linarith), zero_div]
    ring

/-- **The affine form of the kernel away from the origin.** -/
theorem looseKernel_eq_affine {z : Fin 2 → ℝ} (hz : z ≠ 0) :
    looseKernel z = looseKernelAff z := by
  have hr : 0 < diamondNorm z := diamondNorm_pos hz
  have hr' : diamondNorm z ≠ 0 := hr.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hR1 : looseRadius - 1 ≠ 0 := by norm_num [looseRadius]
  have hb : bump z = looseHump (diamondNorm z) := rfl
  have hc : 2 * Real.pi * looseRadius / (looseRadius - 1) * potential z
        + -(1 / (looseRadius - 1))
      = (looseRadius / diamondNorm z - 1) / (looseRadius - 1) := by
    rw [potential]
    field_simp
    ring
  rw [looseKernel_eq, looseCusp_eq_add hr, looseKernelAff, hc, tail_eq, hb]
  ring

/-! ### The two kernels have the same generator off the axes -/

private theorem secondDiff_looseKernel_eq {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0)
    (j : Fin 2) (t : ℝ) : secondDiff looseKernel j z t = secondDiff looseKernelAff j z t := by
  have hz : z ≠ 0 := fun h => h0 (by rw [h]; simp)
  rw [secondDiff, secondDiff, looseKernel_eq_affine (add_single_ne_zero h0 h1 j t),
    looseKernel_eq_affine (sub_single_ne_zero h0 h1 j t), looseKernel_eq_affine hz]

/-- Off the two coordinate axes the loose kernel and its affine form have the same generator. -/
theorem jumpGen_looseKernel_eq_aff {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) :
    jumpGen 1 looseKernel z = jumpGen 1 looseKernelAff z := by
  unfold jumpGen
  refine Finset.sum_congr rfl fun j _ => integral_congr_ae
    (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [secondDiff_looseKernel_eq h0 h1 j t]

/-! ### Integrability of the three pieces -/

private theorem rpow_neg_two_eq (t : ℝ) : |t| ^ (-(1 + 1) : ℝ) = 1 / t ^ 2 := by
  rw [CenteredMaximal.abs_rpow_neg_two, one_div]

/-- The axis-`j` jump integrand of the potential is the one-dimensional profile integrand. -/
private theorem secondDiff_potential_mul (z : Fin 2 → ℝ) (j : Fin 2) (t : ℝ) :
    secondDiff potential j z t * |t| ^ (-(1 + 1) : ℝ)
      = (2 * Real.pi)⁻¹ * profileDiff |z j| |z (j + 1)| t := by
  have h1 : potential (z + t • Pi.single j 1)
      = (2 * Real.pi)⁻¹ * (|z j + t| + |z (j + 1)|)⁻¹ := by
    rw [potential, diamondNorm_add_single', one_div, mul_inv]
  have h2 : potential (z - t • Pi.single j 1)
      = (2 * Real.pi)⁻¹ * (|z j - t| + |z (j + 1)|)⁻¹ := by
    rw [sub_eq_add_neg, ← neg_smul, potential, diamondNorm_add_single', ← sub_eq_add_neg,
      one_div, mul_inv]
  have h3 : potential z = (2 * Real.pi)⁻¹ * (|z j| + |z (j + 1)|)⁻¹ := by
    rw [potential, diamondNorm_eq_abs_add' z j, one_div, mul_inv]
  rw [secondDiff, h1, h2, h3, rpow_neg_two_eq, ← profileDiff_abs_left]
  ring

private theorem integrable_secondDiff_affine {c₁ c₂ : ℝ} {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0)
    (h1 : z 1 ≠ 0) (j : Fin 2) :
    Integrable fun t : ℝ =>
      secondDiff (fun w => c₁ * potential w + c₂) j z t * |t| ^ (-(1 + 1) : ℝ) := by
  refine ((integrable_profileDiff (abs_pos.2 (coord_ne_zero h0 h1 j))
    (abs_pos.2 (coord_succ_ne_zero h0 h1 j))).const_mul (c₁ * (2 * Real.pi)⁻¹)).congr
    (Filter.Eventually.of_forall fun t => ?_)
  calc c₁ * (2 * Real.pi)⁻¹ * profileDiff |z j| |z (j + 1)| t
      = c₁ * (secondDiff potential j z t * |t| ^ (-(1 + 1) : ℝ)) := by
        rw [secondDiff_potential_mul]; ring
    _ = secondDiff (fun w => c₁ * potential w + c₂) j z t * |t| ^ (-(1 + 1) : ℝ) := by
        simp only [secondDiff]; ring

private theorem integrable_secondDiff_bump {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0)
    (j : Fin 2) :
    Integrable fun t : ℝ => secondDiff bump j z t * |t| ^ (-(1 + 1) : ℝ) := by
  fin_cases j
  · show Integrable fun t : ℝ => secondDiff bump 0 z t * |t| ^ (-(1 + 1) : ℝ)
    refine (integrable_bumpSliceDiff (c := z 1) h0).congr
      (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [secondDiff_bump_zero]
  · show Integrable fun t : ℝ => secondDiff bump 1 z t * |t| ^ (-(1 + 1) : ℝ)
    refine (integrable_bumpSliceDiff (c := z 0) h1).congr
      (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    rw [secondDiff_bump_one]

private theorem integrable_secondDiff_sub {φ ψ : (Fin 2 → ℝ) → ℝ} {z : Fin 2 → ℝ} {j : Fin 2}
    (hφ : Integrable fun t : ℝ => secondDiff φ j z t * |t| ^ (-(1 + 1) : ℝ))
    (hψ : Integrable fun t : ℝ => secondDiff ψ j z t * |t| ^ (-(1 + 1) : ℝ)) :
    Integrable fun t : ℝ => secondDiff (φ - ψ) j z t * |t| ^ (-(1 + 1) : ℝ) := by
  refine (hφ.sub hψ).congr (Filter.Eventually.of_forall fun t => ?_)
  simp only [secondDiff, Pi.sub_apply]
  ring

private theorem integrable_secondDiff_smul {φ : (Fin 2 → ℝ) → ℝ} {z : Fin 2 → ℝ} {j : Fin 2}
    {c : ℝ} (hφ : Integrable fun t : ℝ => secondDiff φ j z t * |t| ^ (-(1 + 1) : ℝ)) :
    Integrable fun t : ℝ => secondDiff (c • φ) j z t * |t| ^ (-(1 + 1) : ℝ) := by
  refine (hφ.const_mul c).congr (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [secondDiff_smul]
  ring

/-! ### The generator of the kernel inside the diamond -/

/-- **The generator of the kernel inside the diamond of radius `R`.** The affine potential part is
generator-harmonic off the axes, leaving the tail minus `ε` times the bump. -/
theorem jumpGen_looseKernel_eq {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0)
    (hzR : diamondNorm z < looseRadius) :
    jumpGen 1 looseKernel z
      = jumpGen 1 (tail looseRadius) z - looseBump * jumpGen 1 bump z := by
  have hzne : z ≠ 0 := fun h => h0 (by rw [h]; simp)
  have hz : 0 < diamondNorm z := diamondNorm_pos hzne
  have hP : ∀ j, Integrable fun t : ℝ =>
      secondDiff (fun w => 2 * Real.pi * looseRadius / (looseRadius - 1) * potential w
        + -(1 / (looseRadius - 1))) j z t * |t| ^ (-(1 + 1) : ℝ) :=
    fun j => integrable_secondDiff_affine h0 h1 j
  have hT : ∀ j, Integrable fun t : ℝ =>
      secondDiff (tail looseRadius) j z t * |t| ^ (-(1 + 1) : ℝ) :=
    fun j => integrable_secondDiff_tail one_lt_looseRadius j hz hzR
  have hB : ∀ j, Integrable fun t : ℝ =>
      secondDiff (looseBump • bump) j z t * |t| ^ (-(1 + 1) : ℝ) :=
    fun j => integrable_secondDiff_smul (integrable_secondDiff_bump h0 h1 j)
  have hTB : ∀ j, Integrable fun t : ℝ =>
      secondDiff (tail looseRadius - looseBump • bump) j z t * |t| ^ (-(1 + 1) : ℝ) :=
    fun j => integrable_secondDiff_sub (hT j) (hB j)
  have hsplit : looseKernelAff
      = (fun w => 2 * Real.pi * looseRadius / (looseRadius - 1) * potential w
          + -(1 / (looseRadius - 1))) + (tail looseRadius - looseBump • bump) := by
    funext w
    simp only [looseKernelAff, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [jumpGen_looseKernel_eq_aff h0 h1, hsplit, jumpGen_add hP hTB, jumpGen_sub hT hB,
    jumpGen_smul, jumpGen_affine_potential_eq_zero h0 h1, zero_add]

/-! ### The sign of the generator -/

/-- **The generator of the comparison kernel is nonnegative off the two coordinate axes.** Inside
the unit diamond this is `certificate`, between the unit diamond and the diamond of radius `R` it
is `exterior_certificate`, and beyond that diamond the kernel vanishes at `z` while remaining
nonnegative elsewhere. -/
theorem jumpGen_looseKernel_nonneg {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) :
    0 ≤ jumpGen 1 looseKernel z := by
  have hzne : z ≠ 0 := fun h => h0 (by rw [h]; simp)
  have hz : 0 < diamondNorm z := diamondNorm_pos hzne
  rcases lt_or_ge (diamondNorm z) looseRadius with hzR | hzR
  · rw [jumpGen_looseKernel_eq h0 h1 hzR, sub_nonneg]
    have hc : (0 : ℝ) < 4 / (looseRadius * (looseRadius - 1)) := by norm_num [looseRadius]
    have hA := jumpGen_tail_ge_Jfun_sharp one_lt_looseRadius hz hzR
    rcases lt_or_ge (diamondNorm z) 1 with hr1 | hr1
    · have hmul : looseBump * jumpGen 1 bump z
          ≤ looseBump * (4 * Tfun (diamondNorm z)) :=
        mul_le_mul_of_nonneg_left (jumpGen_bump_le h0 h1 hr1) looseBump_pos.le
      have hstep : looseBump * (4 * Tfun (diamondNorm z))
          ≤ 4 / (looseRadius * (looseRadius - 1))
            * Jfun (2 * diamondNorm z / looseRadius) := by
        calc looseBump * (4 * Tfun (diamondNorm z))
            = 4 / (looseRadius * (looseRadius - 1))
                * (looseBump * looseRadius * (looseRadius - 1) * Tfun (diamondNorm z)) := by
              rw [looseRadius]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (certificate hz hr1) hc.le
      linarith
    · have hJ : 1 ≤ Jfun (2 * diamondNorm z / looseRadius) :=
        one_le_Jfun (div_pos (by linarith) looseRadius_pos)
          (by rw [div_lt_iff₀ looseRadius_pos]; linarith)
      have hcJ : 4 / (looseRadius * (looseRadius - 1))
          ≤ 4 / (looseRadius * (looseRadius - 1))
            * Jfun (2 * diamondNorm z / looseRadius) :=
        le_mul_of_one_le_right hc.le hJ
      have hmul : looseBump * jumpGen 1 bump z
          ≤ 4 * (looseBump * (2 - 2 * Real.log 2)) := by
        calc looseBump * jumpGen 1 bump z
            ≤ looseBump * (4 * (2 - 2 * Real.log 2)) :=
              mul_le_mul_of_nonneg_left (jumpGen_bump_le_exterior h0 h1 hr1) looseBump_pos.le
          _ = 4 * (looseBump * (2 - 2 * Real.log 2)) := by ring
      have he : (4 : ℝ) * (1 / (looseRadius * (looseRadius - 1)))
          = 4 / (looseRadius * (looseRadius - 1)) := by ring
      linarith [exterior_certificate]
  · have hK : looseKernel z = 0 := looseKernel_eq_zero_of_le hzR
    unfold jumpGen
    refine Finset.sum_nonneg fun j _ => integral_nonneg fun t => ?_
    have e1 : 0 ≤ looseKernel (z + t • Pi.single j 1) :=
      looseKernel_nonneg (add_single_ne_zero h0 h1 j t)
    have e2 : 0 ≤ looseKernel (z - t • Pi.single j 1) :=
      looseKernel_nonneg (sub_single_ne_zero h0 h1 j t)
    rw [secondDiff, hK]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (abs_nonneg t) _)

/-! ### The coordinate axes are null -/

/-- A coordinate hyperplane of the plane is a null set, being a strict subspace. -/
private theorem volume_coord_eq_zero (i : Fin 2) : volume {z : Fin 2 → ℝ | z i = 0} = 0 := by
  have hset : {z : Fin 2 → ℝ | z i = 0}
      = (LinearMap.ker (LinearMap.proj i : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) : Set (Fin 2 → ℝ)) := by
    ext z
    simp [LinearMap.mem_ker]
  rw [hset]
  refine Measure.addHaar_submodule volume _ fun htop => ?_
  have hmem : Pi.single i (1 : ℝ) ∈ LinearMap.ker (LinearMap.proj i : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) := by
    rw [htop]
    exact Submodule.mem_top
  simp [LinearMap.mem_ker] at hmem

/-- **The Cauchy jump generator of the comparison kernel is almost everywhere nonnegative.** -/
theorem ae_jumpGen_looseKernel_nonneg :
    ∀ᵐ z ∂(volume : Measure (Fin 2 → ℝ)), 0 ≤ jumpGen 1 looseKernel z := by
  rw [ae_iff]
  refine measure_mono_null (fun z hz => ?_)
    (measure_union_null (volume_coord_eq_zero 0) (volume_coord_eq_zero 1))
  by_contra hcon
  simp only [mem_union, mem_setOf_eq, not_or] at hcon
  exact hz (jumpGen_looseKernel_nonneg hcon.1 hcon.2)

end CenteredMaximal.Cauchy

end

end
