/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.FracRepresentation
public import CenteredMaximal.Fractional.MajorKernel

/-!
# The easy two thirds of the generator's sign: the exterior and the axes

`CenteredMaximal.Fractional.FracAssembly.weakTypeConstant_two_le_frac` asks for the almost
everywhere nonnegativity of the generator density `g = fracDensity = jumpGen (6/5) fracKernel`.
The plane splits into three regions, and two of them are settled here.

* **The two coordinate axes are null.**  `volume_coord_eq_zero` is `Measure.addHaar_submodule`
  applied to `ker (LinearMap.proj i)`, a strict subspace of the plane.  So the density needs no
  sign at all there — which is just as well, since that is exactly where the jump integrand fails
  to be integrable and Mathlib's convention makes the Bochner integral vanish.
* **The exterior `7/4 ≤ diamondNorm z`, off the axes.**  There `fracKernel z = 0`
  (`fracKernel_eq_zero_of_le`), so each directional integrand is the bare sum of the two displaced
  values, `(K (z + t e_j) + K (z − t e_j)) |t|^{−(1+α)}`.  Both displaced points are nonzero,
  because the displacement leaves the other coordinate alone and that coordinate is nonzero off the
  axes, so `MajorKernel.fracKernel_nonneg` applies to each and the integrand is nonnegative.
  `MeasureTheory.integral_nonneg` needs no integrability: a non-integrable Bochner integral is `0`,
  which is still `≥ 0`.

What is left is the **interior** `diamondNorm z < 7/4` off the axes, where the kernel does not
vanish and the sign is a genuine analytic fact.  `ae_fracDensity_nonneg_of_interior` reduces the
hypothesis of `weakTypeConstant_two_le_frac` to exactly that region.

## Main results

* `jumpGen_fracKernel_nonneg_of_exterior`: **the exterior region.**
* `ae_fracDensity_nonneg_of_interior`: **the reduction.**  A pointwise sign on the punctured open
  diamond off the axes gives `0 ≤ᵐ[volume] fracDensity`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### A coordinate line off the axes misses the origin -/

private theorem diamondNorm_add_single'' (z : Fin 2 → ℝ) (j : Fin 2) (s : ℝ) :
    diamondNorm (z + s • Pi.single j 1) = |z j + s| + |z (j + 1)| := by
  fin_cases j <;> simp [diamondNorm, add_comm]

private theorem coord_succ_ne_zero' {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2) :
    z (j + 1) ≠ 0 := by
  fin_cases j
  · simpa using h1
  · simpa using h0

/-- A coordinate line through a point off the two axes never meets the origin: the displacement
leaves the other coordinate alone, and that coordinate is nonzero. -/
private theorem add_single_ne_zero' {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2)
    (s : ℝ) : z + s • Pi.single j 1 ≠ 0 := by
  intro h
  have hd : diamondNorm (z + s • Pi.single j 1) = 0 := diamondNorm_eq_zero_iff.2 h
  rw [diamondNorm_add_single''] at hd
  linarith [abs_nonneg (z j + s), abs_pos.2 (coord_succ_ne_zero' h0 h1 j)]

private theorem sub_single_ne_zero' {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (j : Fin 2)
    (s : ℝ) : z - s • Pi.single j 1 ≠ 0 := by
  rw [sub_eq_add_neg, ← neg_smul]
  exact add_single_ne_zero' h0 h1 j (-s)

/-! ### The exterior region -/

/-- **The generator of the comparison kernel is nonnegative outside the support**, at a point off
the two coordinate axes.  The kernel vanishes at the base point, so every directional integrand is
a sum of two values of the kernel at nonzero points, each nonnegative by `fracKernel_nonneg`.  No
integrability is needed: `integral_nonneg` is about the Bochner integral, which Mathlib sets to `0`
when the integrand is not integrable. -/
theorem jumpGen_fracKernel_nonneg_of_exterior {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0)
    (hz : 7 / 4 ≤ diamondNorm z) : 0 ≤ jumpGen (6 / 5) fracKernel z := by
  have hK : fracKernel z = 0 := fracKernel_eq_zero_of_le hz
  unfold jumpGen
  refine Finset.sum_nonneg fun j _ => integral_nonneg fun t => ?_
  have e1 : 0 ≤ fracKernel (z + t • Pi.single j 1) :=
    fracKernel_nonneg (add_single_ne_zero' h0 h1 j t)
  have e2 : 0 ≤ fracKernel (z - t • Pi.single j 1) :=
    fracKernel_nonneg (sub_single_ne_zero' h0 h1 j t)
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

/-! ### The reduction -/

/-- **The generator density is almost everywhere nonnegative as soon as it is nonnegative on the
punctured open diamond off the coordinate axes.**  The axes are null, and off them the exterior is
handled by `jumpGen_fracKernel_nonneg_of_exterior`.  This is the hypothesis `hgen` of
`CenteredMaximal.Fractional.weakTypeConstant_two_le_frac`, reduced to the one region the finite
certificate has to cover. -/
theorem ae_fracDensity_nonneg_of_interior
    (hint : ∀ z : Fin 2 → ℝ, z 0 ≠ 0 → z 1 ≠ 0 → diamondNorm z < 7 / 4 →
      0 ≤ jumpGen (6 / 5) fracKernel z) :
    0 ≤ᵐ[volume] fracDensity := by
  have key : ∀ z : Fin 2 → ℝ, z 0 ≠ 0 → z 1 ≠ 0 → 0 ≤ fracDensity z := by
    intro z h0 h1
    rw [fracDensity]
    rcases lt_or_ge (diamondNorm z) (7 / 4) with h | h
    · exact hint z h0 h1 h
    · exact jumpGen_fracKernel_nonneg_of_exterior h0 h1 h
  have hae : ∀ᵐ z ∂(volume : Measure (Fin 2 → ℝ)), 0 ≤ fracDensity z := by
    rw [ae_iff]
    refine measure_mono_null (fun z hz => ?_)
      (measure_union_null (volume_coord_eq_zero 0) (volume_coord_eq_zero 1))
    by_contra hcon
    simp only [mem_union, mem_setOf_eq, not_or] at hcon
    exact hz (key z hcon.1 hcon.2)
  exact hae

end CenteredMaximal.Fractional

end

end
