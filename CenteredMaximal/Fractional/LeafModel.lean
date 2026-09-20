/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.BaseModel
public import CenteredMaximal.Fractional.DirModel
public import CenteredMaximal.Fractional.GenEven

/-!
# The polynomial model of a whole leaf of the generator certificate

This file assembles the two coordinate directions of
`CenteredMaximal.Fractional.dirModel_bound` and the base half of
`CenteredMaximal.Fractional.termsValR_baseTerms` into one centred bivariate model of the whole
generator, and discharges `hmodel` of
`CenteredMaximal.Fractional.jumpGen_fracKernel_nonneg_of_centred` with it.

## Why the second direction is transposed

`CenteredMaximal.Fractional.splineGen_eq_rowSum` reads the generator in both coordinate
directions, and `CenteredMaximal.Fractional.dirModel_bound` always calls the coordinate its rows
live in the first one.  In the second direction the rows live in `v` and the profile in `u`, so its
bidegrees arrive exchanged; `transposeTerms` puts them back.  Nothing else distinguishes the two
directions, because `CenteredMaximal.Fractional.fracArrSwap_eq_fracArr` says the certificate's
coefficient array is symmetric, so both directions read the *same* profile.

## Why the whole model is one list

The two directions and the base are concatenated, not merged.  Two terms of the same bidegree —
and there are over a hundred of them on the linear bidegrees — are added when
`CenteredMaximal.Fractional.termsCoI` reads that bidegree out, in exact rational arithmetic, and
only the *sum* is ever given to `RatItv.absmax`.  This is the cancellation the certificate lives
on: the base's radial slope, of size `S r^{−17/5}`, and the spline's linear coefficient nearly
annihilate, and bounding the two halves separately is short by a factor of about `10³` near the
origin (see the module docstring of `CenteredMaximal.Fractional.CentredLeaf`).

## Main results

* `transposeTerms`, `termsValR_transpose`: exchanging the two bidegrees of a model.
* `encItv_hi_pos`, `rowErrQ_nonneg`, `dirErrQ_nonneg`: the model's error is nonnegative, which is
  what lets it be scaled by the *upper* end of the enclosure of `(625/108) · 16 ^ (6/5)`.
* `leafSplineTerms`, `leafSplineErrQ`, `leafSpline_bound`: **the spline half of a leaf's model**
  and the inequality it satisfies against the generator's spline half.
* `jumpGen_fracKernel_nonneg_of_leaf`: **one rectangle of the certificate.**  The generator of the
  comparison kernel is nonnegative on a rectangle as soon as a single rational inequality on the
  model's coefficients holds.
-/

@[expose] public section

open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### Transposing a model -/

/-- A model with its two bidegrees exchanged, which is how the second coordinate direction's rows
enter a leaf. -/
def transposeTerms (M : List ModelTerm) : List ModelTerm :=
  M.map fun w => ⟨w.b, w.a, w.q, w.x, w.e⟩

theorem termsValR_transpose (M : List ModelTerm) (s t : ℝ) :
    termsValR (transposeTerms M) s t = termsValR M t s := by
  rw [transposeTerms, termsValR, termsValR, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun w _ => ?_)
  simp only [Function.comp_apply, ModelTerm.coR]
  ring

theorem transposeTerms_pos {M : List ModelTerm} (h : ∀ w ∈ M, 0 < w.x ∧ w.a < 4 ∧ w.b < 4) :
    ∀ w ∈ transposeTerms M, 0 < w.x ∧ w.a < 4 ∧ w.b < 4 := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
  exact ⟨(h v hv).1, (h v hv).2.2, (h v hv).2.1⟩

/-! ### The model's error is nonnegative -/

/-- **The upper end of an enclosure is positive.**  Both branches of `encItv` produce a positive
upper end, the table's because it is `(dig + 1) / 10 ^ 12` and the fallback's by
`rpowFifthEnc_pos`. -/
theorem encItv_hi_pos (L : List FifthEnc) (x : ℚ) (e : ℤ) : 0 < (encItv L x e).hi := by
  rw [encItv]
  split
  · rename_i c _
    rw [FifthEnc.hiQ]
    positivity
  · exact rpowFifthEnc_pos x e 12

theorem rowErrQ_nonneg (L : List FifthEnc) (m δ : ℚ) (touch : Bool) (p : ℕ → ℚ) :
    0 ≤ rowErrQ L m δ touch p := by
  rw [rowErrQ]
  refine mul_nonneg (bernMax_nonneg p δ) ?_
  split
  · exact mul_nonneg (by norm_num) (encItv_hi_pos L δ 9).le
  · exact mul_nonneg (by positivity) (encItv_hi_pos L (m - δ) (-11)).le

theorem dirErrQ_nonneg (L : List FifthEnc) (mcell : ℤ) (uc mu δ : ℚ) :
    0 ≤ dirErrQ L mcell uc mu δ := by
  rw [dirErrQ]
  refine List.sum_nonneg fun x hx => ?_
  obtain ⟨k, _, rfl⟩ := List.mem_map.1 hx
  exact rowErrQ_nonneg _ _ _ _ _

/-! ### The spline half of a leaf's model -/

/-- **The spline half of a leaf's model**: the rows of the first coordinate direction, then the
rows of the second, transposed. -/
def leafSplineTerms (icell jcell : ℤ) (uc vc δ : ℚ) : List ModelTerm :=
  dirTerms jcell uc (vc - (jcell : ℚ)) δ
    ++ transposeTerms (dirTerms icell vc (uc - (icell : ℚ)) δ)

/-- The error of the spline half, before it is scaled by `(625/108) · 16 ^ (6/5)`. -/
def leafSplineErrQ (L : List FifthEnc) (icell jcell : ℤ) (uc vc δ : ℚ) : ℚ :=
  dirErrQ L jcell uc (vc - (jcell : ℚ)) δ + dirErrQ L icell vc (uc - (icell : ℚ)) δ

theorem leafSplineTerms_pos {icell jcell : ℤ} {uc vc δ : ℚ} (hδ : 0 < δ)
    (hsu : ∀ k ∈ rowIdx, δ ≤ rowDist uc k) (hsv : ∀ k ∈ rowIdx, δ ≤ rowDist vc k) :
    ∀ w ∈ leafSplineTerms icell jcell uc vc δ, 0 < w.x ∧ w.a < 4 ∧ w.b < 4 := by
  intro w hw
  rcases List.mem_append.1 hw with h | h
  · exact dirTerms_pos hδ hsu w h
  · exact transposeTerms_pos (dirTerms_pos hδ hsv) w h

/-- **The spline half of the model minorises the spline half of the generator.** -/
theorem leafSpline_bound {L : List FifthEnc} (hL : L.all (fun c => c.check 12) = true)
    {icell jcell : ℤ} {uc vc δ : ℚ} (hδ : 0 < δ)
    (hsu : ∀ k ∈ rowIdx, δ ≤ rowDist uc k) (hsv : ∀ k ∈ rowIdx, δ ≤ rowDist vc k)
    {U V : ℝ} (hu : |U - (uc : ℝ)| ≤ (δ : ℝ)) (hv : |V - (vc : ℝ)| ≤ (δ : ℝ))
    (hui : 0 ≤ U - (icell : ℝ)) (hui' : U - (icell : ℝ) ≤ 1)
    (hvj : 0 ≤ V - (jcell : ℝ)) (hvj' : V - (jcell : ℝ) ≤ 1) :
    termsValR (leafSplineTerms icell jcell uc vc δ) (U - (uc : ℝ)) (V - (vc : ℝ))
        - ((leafSplineErrQ L icell jcell uc vc δ : ℚ) : ℝ)
      ≤ (∑ k ∈ Finset.Icc (-26 : ℤ) 26,
            (∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
                colProfile fracArr (k + 2 - q) V) * |U - (k : ℝ)| ^ (9 / 5 : ℝ))
        + ∑ k ∈ Finset.Icc (-26 : ℤ) 26,
            (∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
                colProfile fracArr (k + 2 - q) U) * |V - (k : ℝ)| ^ (9 / 5 : ℝ) := by
  set s : ℝ := U - (uc : ℝ) with hs
  set t : ℝ := V - (vc : ℝ) with ht
  have hcellV : ((vc - (jcell : ℚ) : ℚ) : ℝ) + t = V - (jcell : ℝ) := by
    rw [ht]
    push_cast
    ring
  have hcellU : ((uc - (icell : ℚ) : ℚ) : ℝ) + s = U - (icell : ℝ) := by
    rw [hs]
    push_cast
    ring
  have hV0 : (0 : ℝ) ≤ ((vc - (jcell : ℚ) : ℚ) : ℝ) + t := by rw [hcellV]; exact hvj
  have hV1 : ((vc - (jcell : ℚ) : ℚ) : ℝ) + t ≤ 1 := by rw [hcellV]; exact hvj'
  have hU0 : (0 : ℝ) ≤ ((uc - (icell : ℚ) : ℚ) : ℝ) + s := by rw [hcellU]; exact hui
  have hU1 : ((uc - (icell : ℚ) : ℚ) : ℝ) + s ≤ 1 := by rw [hcellU]; exact hui'
  have h0 := dirModel_bound (mcell := jcell) (mu := vc - (jcell : ℚ)) hL hδ hsu hu hv hV0 hV1
  have h1 := dirModel_bound (mcell := icell) (mu := uc - (icell : ℚ)) hL hδ hsv hv hu hU0 hU1
  rw [hcellV] at h0
  rw [hcellU] at h1
  have hU : (uc : ℝ) + s = U := by rw [hs]; ring
  have hV : (vc : ℝ) + t = V := by rw [ht]; ring
  have hVj : (jcell : ℝ) + (V - (jcell : ℝ)) = V := by ring
  have hUi : (icell : ℝ) + (U - (icell : ℝ)) = U := by ring
  rw [hU, hVj] at h0
  rw [hV, hUi] at h1
  rw [leafSplineTerms, termsValR_append, termsValR_transpose, leafSplineErrQ]
  push_cast
  linarith

/-! ### One rectangle of the certificate -/

/-- **The model error of a leaf**, scaled by the upper end of the enclosure of
`(625/108) · 16 ^ (6/5)`. -/
def leafErrQ (L : List FifthEnc) (icell jcell : ℤ) (uc vc δ : ℚ) : ℚ :=
  (splineScaleI L).hi * leafSplineErrQ L icell jcell uc vc δ

/-- **One rectangle of the `α = 6/5` generator certificate.**  On a dyadic rectangle of the open
diamond, off the coordinate axes and inside one cell of the spline grid, the generator of the
comparison kernel is nonnegative as soon as the single rational inequality `hchk` holds between the
model's coefficient intervals and its error.

Everything else in the hypotheses is arithmetic on the leaf's own indices: that the rectangle lies
in the cell `(icell, jcell)`, that no row of either direction is closer to the centre than the
half-width, and that the intrinsic constant `S` is a valid rational lower bound. -/
theorem jumpGen_fracKernel_nonneg_of_leaf {L : List FifthEnc}
    (hL : L.all (fun c => c.check 12) = true) {S r₀ d₀ : ℚ} {K Ltail : ℕ}
    (hS : 0 ≤ (S : ℝ))
    (hSle : (S : ℝ) ≤ -4 * Real.pi * Real.Gamma (2 * (6 / 5)) * Real.cos (Real.pi * (6 / 5) / 2)
      / (6 / 5 * Real.Gamma (6 / 5) ^ 2 * Real.sin (Real.pi * (6 / 5) / 2)))
    (hr₀ : 0 < r₀) {icell jcell : ℤ} {uc vc δ : ℚ} (hδ : 0 < δ)
    (hsu : ∀ k ∈ rowIdx, δ ≤ rowDist uc k) (hsv : ∀ k ∈ rowIdx, δ ≤ rowDist vc k)
    (hchk : 0 ≤ leafCheckQ L (leafSplineTerms icell jcell uc vc δ)
      (baseTerms S r₀ d₀ K Ltail uc vc) δ (leafErrQ L icell jcell uc vc δ))
    {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < 7 / 4)
    (hu : |16 * |z 0| - (uc : ℝ)| ≤ (δ : ℝ)) (hv : |16 * |z 1| - (vc : ℝ)| ≤ (δ : ℝ))
    (hui : 0 ≤ 16 * |z 0| - (icell : ℝ)) (hui' : 16 * |z 0| - (icell : ℝ) ≤ 1)
    (hvj : 0 ≤ 16 * |z 1| - (jcell : ℝ)) (hvj' : 16 * |z 1| - (jcell : ℝ) ≤ 1) :
    0 ≤ jumpGen (6 / 5) fracKernel z := by
  have hr₀R : (0 : ℝ) < (r₀ : ℝ) := by exact_mod_cast hr₀
  -- the spline half of the generator, collapsed onto the rows
  have habs : splineGen (16 * |z 0|) (16 * |z 1|) = splineGen (16 * z 0) (16 * z 1) := by
    rw [show (16 : ℝ) * |z 0| = |16 * z 0| from by rw [abs_mul]; norm_num,
      show (16 : ℝ) * |z 1| = |16 * z 1| from by rw [abs_mul]; norm_num, splineGen_abs]
  have hrow := splineGen_eq_rowSum (16 * |z 0|) (16 * |z 1|)
  rw [← splineGen_eq_finsetSum, fracArrSwap_eq_fracArr, habs] at hrow
  -- the spline half of the model
  have hspl := leafSpline_bound hL hδ hsu hsv hu hv hui hui' hvj hvj'
  have hscale := splineScaleI_mem (L := L) hL
  have hsc : (0 : ℝ) < splineScale := by
    rw [splineScale]
    positivity
  have herr : (0 : ℚ) ≤ leafSplineErrQ L icell jcell uc vc δ :=
    add_nonneg (dirErrQ_nonneg _ _ _ _ _) (dirErrQ_nonneg _ _ _ _ _)
  have herrR : (0 : ℝ) ≤ ((leafSplineErrQ L icell jcell uc vc δ : ℚ) : ℝ) := by
    exact_mod_cast herr
  have hmul := mul_le_mul_of_nonneg_left hspl hsc.le
  rw [mul_sub] at hmul
  have hbnd : splineScale * ((leafSplineErrQ L icell jcell uc vc δ : ℚ) : ℝ)
      ≤ ((leafErrQ L icell jcell uc vc δ : ℚ) : ℝ) := by
    rw [leafErrQ, Rat.cast_mul]
    exact mul_le_mul_of_nonneg_right hscale.2 herrR
  -- the generator's spline half, with the dilation factor pulled out
  have hfact : ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
        ((16 : ℝ) ^ (6 / 5 : ℝ) *
          (jumpGen1 (6 / 5) bspline (16 * z 0 - ij.1) * bspline (16 * z 1 - ij.2)
            + bspline (16 * z 0 - ij.1) * jumpGen1 (6 / 5) bspline (16 * z 1 - ij.2)))
      = (16 : ℝ) ^ (6 / 5 : ℝ) * ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
          (jumpGen1 (6 / 5) bspline (16 * z 0 - ij.1) * bspline (16 * z 1 - ij.2)
            + bspline (16 * z 0 - ij.1) * jumpGen1 (6 / 5) bspline (16 * z 1 - ij.2)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun ij _ => by ring
  -- the base half of the model is exact
  have hbase := termsValR_baseTerms (S := S) (r₀ := r₀) (d₀ := d₀) hr₀ K Ltail uc vc |z 0| |z 1|
  have hdn : |z 0| + |z 1| = diamondNorm z := rfl
  rw [hdn] at hbase
  refine jumpGen_fracKernel_nonneg_of_terms hL
    (leafSplineTerms_pos hδ hsu hsv) (baseTerms_pos hr₀ K Ltail uc vc)
    (S := (S : ℝ)) (r₀ := (r₀ : ℝ)) (d₀ := (d₀ : ℝ)) (K := K) (Ltail := Ltail) hS hSle hr₀R
    hδ.le hchk h0 h1 hz hu hv ?_
  rw [leafValR, hfact, ← splineGen_eq_finsetSum, hrow, hbase, splineScale]
  rw [splineScale] at hmul hbnd
  linarith

end CenteredMaximal.Fractional

end
