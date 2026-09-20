/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.KernelPositivity
public import CenteredMaximal.Fractional.LeafBound
public import CenteredMaximal.Fractional.MajorBase

/-!
# Collapsing the `1201` cells onto the `53` rows of the generator certificate

The spline half of the `α = 6/5` generator certificate is the double sum

`∑_{i,j} C_{ij} (G(u − i) β(v − j) + β(u − i) G(v − j))`,   `G = jumpGen1 (6/5) β`,

over the `1201` cells of `CenteredMaximal.Fractional.KernelData`.  Evaluating it cell by cell on a
rectangle is hopeless: each cell would need its own Taylor model of `G`, `1201` of them per leaf.

`jumpGen1_bspline_sixFifths` writes `G(x)` as `625/108` times the fourth difference
`∑_{q<5} (−1)^q C(4,q) |x + 2 − q|^{9/5}`, so the first summand is

`625/108 ∑_{i,q} C_{i·}(v) (−1)^q C(4,q) |u − (i + q − 2)|^{9/5}`,

and grouping the pairs `(i, q)` by `k = i + q − 2` turns it into a sum over the **`53` row
indices** `k ∈ [−26, 26]` of `(a cubic in v) · |u − k|^{9/5}` — one elementary function per row
instead of five per cell.  This is the reduction the search program performs in `Dpolys`, and this
file is its Lean counterpart.

The regrouping is a translation of an integer interval: for fixed `q` the map `i ↦ i + q − 2`
carries `[−24, 24]` into `[−26, 26]`, and the column profile vanishes outside `[−24, 24]`, so the
translated sum may be padded out to the common index range before the two sums are exchanged.

## Main results

* `colProfile`, `colProfile_eq_zero`: the `v`-profile of one column of the coefficient array, and
  its vanishing outside the support.
* `sum_Icc_jumpGen1_collapse`: **the row collapse**, for an arbitrary coefficient array supported
  in `[−24, 24] × [−24, 24]`, so that it serves both coordinate orders.
* `fracArr`, `fracArrSwap`, `fracCellCoeff_eq_zero_of_notMem`, `fracCellFinset_subset_box`: the
  certificate's coefficient array in the two index orders, and its support.
* `splineGen_eq_rowSum`: **the collapse of the certificate's own spline sum**, both directions.
-/

@[expose] public section

noncomputable section

open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### Translating an interval sum -/

private theorem sum_Icc_shift (g : ℤ → ℝ) (a b c : ℤ) :
    ∑ i ∈ Finset.Icc a b, g (i + c) = ∑ k ∈ Finset.Icc (a + c) (b + c), g k := by
  rw [← Finset.map_add_right_Icc, Finset.sum_map]
  rfl

/-! ### The column profile -/

/-- The `v`-profile of the `i`-th column of a coefficient array. -/
def colProfile (c : ℤ → ℤ → ℝ) (i : ℤ) (v : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc (-24 : ℤ) 24, c i j * bspline (v - j)

/-- A column outside the support of the array carries no profile. -/
theorem colProfile_eq_zero {c : ℤ → ℤ → ℝ} (hc : ∀ i j : ℤ, 24 < |i| → c i j = 0) {i : ℤ}
    (hi : 24 < |i|) (v : ℝ) : colProfile c i v = 0 :=
  Finset.sum_eq_zero fun j _ => by rw [hc i j hi, zero_mul]

/-! ### The row collapse -/

set_option maxHeartbeats 1000000 in
/-- **The row collapse.**  For a coefficient array supported in `[−24, 24]` in its first index, the
sum of the spline generator in the first coordinate against the array collapses onto the `53` row
indices `k ∈ [−26, 26]`, each carrying the single elementary function `|u − k|^{9/5}`.

The array is a parameter rather than `fracCellCoeff` itself, so that the same lemma serves the
other coordinate order, which is the array with its two indices exchanged. -/
theorem sum_Icc_jumpGen1_collapse {c : ℤ → ℤ → ℝ} (hc : ∀ i j : ℤ, 24 < |i| → c i j = 0)
    (u v : ℝ) :
    ∑ i ∈ Finset.Icc (-24 : ℤ) 24, jumpGen1 (6 / 5) bspline (u - i) * colProfile c i v
      = 625 / 108 * ∑ k ∈ Finset.Icc (-26 : ℤ) 26,
          (∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
              colProfile c (k + 2 - q) v) * |u - (k : ℝ)| ^ (9 / 5 : ℝ) := by
  -- expand the generator into its five shifted powers
  have hexp : ∀ i ∈ Finset.Icc (-24 : ℤ) 24,
      jumpGen1 (6 / 5) bspline (u - i) * colProfile c i v
        = 625 / 108 * ∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
            (colProfile c i v * |u - ((i + (q : ℤ) - 2 : ℤ) : ℝ)| ^ (9 / 5 : ℝ)) := by
    intro i _
    rw [jumpGen1_bspline_sixFifths, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    have hcast : (u : ℝ) - (i : ℝ) + 2 - (q : ℝ) = u - ((i + (q : ℤ) - 2 : ℤ) : ℝ) := by
      push_cast
      ring
    rw [hcast]
    ring
  -- write the right side as the same double sum, in the other order
  have hrhs : ∑ k ∈ Finset.Icc (-26 : ℤ) 26,
      (∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * colProfile c (k + 2 - q) v)
        * |u - (k : ℝ)| ^ (9 / 5 : ℝ)
      = ∑ q ∈ Finset.range 5, ∑ k ∈ Finset.Icc (-26 : ℤ) 26,
          (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
            (colProfile c (k + 2 - q) v * |u - (k : ℝ)| ^ (9 / 5 : ℝ)) := by
    rw [← Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun q _ => by ring
  rw [Finset.sum_congr rfl hexp, ← Finset.mul_sum, Finset.sum_comm, hrhs]
  congr 1
  -- for each `q`, translate the index and pad out to the common range
  refine Finset.sum_congr rfl fun q hq => ?_
  have hq4 : (q : ℤ) ≤ 4 := by
    have := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    exact_mod_cast this
  set d : ℤ := (q : ℤ) - 2 with hd
  set g : ℤ → ℝ := fun k => colProfile c (k - d) v * |u - (k : ℝ)| ^ (9 / 5 : ℝ) with hg
  have hidx : ∀ i : ℤ, i + (q : ℤ) - 2 = i + d := fun i => by omega
  have hstep : ∑ i ∈ Finset.Icc (-24 : ℤ) 24,
      (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
        (colProfile c i v * |u - ((i + (q : ℤ) - 2 : ℤ) : ℝ)| ^ (9 / 5 : ℝ))
      = (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * ∑ i ∈ Finset.Icc (-24 : ℤ) 24, g (i + d) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hidx i]
    simp only [hg, add_sub_cancel_right]
  have hsub : Finset.Icc (-24 + d) (24 + d) ⊆ Finset.Icc (-26 : ℤ) 26 := by
    intro k hk
    rw [Finset.mem_Icc] at hk ⊢
    omega
  have hzero : ∀ k ∈ Finset.Icc (-26 : ℤ) 26, k ∉ Finset.Icc (-24 + d) (24 + d) → g k = 0 := by
    intro k _ hk
    rw [Finset.mem_Icc] at hk
    have habs : 24 < |k - d| := by
      rcases not_and_or.1 hk with h | h
      · exact lt_abs.2 (Or.inr (by omega))
      · exact lt_abs.2 (Or.inl (by omega))
    simp only [hg]
    rw [colProfile_eq_zero hc habs, zero_mul]
  rw [hstep, sum_Icc_shift, Finset.sum_subset hsub hzero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hg]
  have hk : k - d = k + 2 - (q : ℤ) := by omega
  rw [hk]

/-! ### The certificate's own sum, written over the box -/

/-- The box of index pairs that can carry a nonzero coefficient. -/
def fracBox : Finset (ℤ × ℤ) := Finset.Icc (-24 : ℤ) 24 ×ˢ Finset.Icc (-24 : ℤ) 24

/-- The coefficient array of the certificate. -/
def fracArr (i j : ℤ) : ℝ := fracCoeff (fracCellCoeff (i, j))

/-- The coefficient array with its two indices exchanged, which is what the second coordinate
direction of the generator reads. -/
def fracArrSwap (i j : ℤ) : ℝ := fracCoeff (fracCellCoeff (j, i))

theorem fracCoeff_zero : fracCoeff 0 = 0 := by
  rw [fracCoeff_eq]
  norm_num

/-- An index pair that is not a cell of the certificate carries no coefficient. -/
theorem fracCellCoeff_eq_zero_of_notMem {ij : ℤ × ℤ} (h : ij ∉ fracCellFinset) :
    fracCellCoeff ij = 0 := by
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  refine if_neg fun hpe => h ?_
  rw [fracCellFinset, Finset.mem_image]
  exact ⟨p, List.mem_toFinset.2 hp, hpe⟩

/-- **Every cell of the certificate lies in the box**, by `fracCells_absAdd_le`. -/
theorem fracCellFinset_subset_box : fracCellFinset ⊆ fracBox := by
  intro ij hij
  rw [fracCellFinset, Finset.mem_image] at hij
  obtain ⟨p, hp, rfl⟩ := hij
  have habs := fracCells_absAdd_le (List.mem_toFinset.1 hp)
  have h0 := abs_nonneg p.1.1
  have h1 := abs_nonneg p.1.2
  have e0 := neg_abs_le p.1.1
  have e1 := le_abs_self p.1.1
  have f0 := neg_abs_le p.1.2
  have f1 := le_abs_self p.1.2
  rw [fracBox, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- A pair with either index outside `[−24, 24]` is not a cell. -/
private theorem notMem_of_abs_gt {i j : ℤ} (h : 24 < |i| ∨ 24 < |j|) :
    (i, j) ∉ fracCellFinset := by
  intro hm
  have hb := fracCellFinset_subset_box hm
  rw [fracBox, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hb
  rcases h with h | h
  · rcases abs_cases i with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h <;> omega
  · rcases abs_cases j with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] at h <;> omega

/-- The coefficient array is supported in `[−24, 24]` in its first index. -/
theorem fracArr_eq_zero {i j : ℤ} (hi : 24 < |i|) : fracArr i j = 0 := by
  rw [fracArr, fracCellCoeff_eq_zero_of_notMem (notMem_of_abs_gt (Or.inl hi)), fracCoeff_zero]

/-- So is the exchanged array. -/
theorem fracArrSwap_eq_zero {i j : ℤ} (hi : 24 < |i|) : fracArrSwap i j = 0 := by
  rw [fracArrSwap, fracCellCoeff_eq_zero_of_notMem (notMem_of_abs_gt (Or.inr hi)), fracCoeff_zero]

/-! ### The spline half of the generator, collapsed -/

set_option maxHeartbeats 1000000 in
/-- **The spline half of the generator of the comparison kernel, collapsed onto the rows.**  The
`1201`-cell double sum becomes two sums of `53` terms, one per coordinate direction, each term a
profile in one coordinate times the single elementary function `|· − k|^{9/5}` in the other. -/
theorem splineGen_eq_rowSum (u v : ℝ) :
    ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
        (jumpGen1 (6 / 5) bspline (u - ij.1) * bspline (v - ij.2)
          + bspline (u - ij.1) * jumpGen1 (6 / 5) bspline (v - ij.2))
      = 625 / 108 * ∑ k ∈ Finset.Icc (-26 : ℤ) 26,
            (∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
                colProfile fracArr (k + 2 - q) v) * |u - (k : ℝ)| ^ (9 / 5 : ℝ)
        + 625 / 108 * ∑ k ∈ Finset.Icc (-26 : ℤ) 26,
            (∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
                colProfile fracArrSwap (k + 2 - q) u) * |v - (k : ℝ)| ^ (9 / 5 : ℝ) := by
  -- extend the sum from the cells to the whole box
  have hext : ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
        (jumpGen1 (6 / 5) bspline (u - ij.1) * bspline (v - ij.2)
          + bspline (u - ij.1) * jumpGen1 (6 / 5) bspline (v - ij.2))
      = ∑ ij ∈ fracBox, fracCoeff (fracCellCoeff ij) *
        (jumpGen1 (6 / 5) bspline (u - ij.1) * bspline (v - ij.2)
          + bspline (u - ij.1) * jumpGen1 (6 / 5) bspline (v - ij.2)) :=
    Finset.sum_subset fracCellFinset_subset_box fun ij _ hij => by
      rw [fracCellCoeff_eq_zero_of_notMem hij, fracCoeff_zero, zero_mul]
  rw [hext, fracBox, Finset.sum_product]
  -- split the two coordinate directions
  have hsplit : ∀ i ∈ Finset.Icc (-24 : ℤ) 24,
      (∑ j ∈ Finset.Icc (-24 : ℤ) 24, fracCoeff (fracCellCoeff (i, j)) *
          (jumpGen1 (6 / 5) bspline (u - i) * bspline (v - j)
            + bspline (u - i) * jumpGen1 (6 / 5) bspline (v - j)))
        = jumpGen1 (6 / 5) bspline (u - i) * colProfile fracArr i v
          + ∑ j ∈ Finset.Icc (-24 : ℤ) 24,
              bspline (u - i) * (fracArrSwap j i * jumpGen1 (6 / 5) bspline (v - j)) := by
    intro i _
    rw [colProfile, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [fracArr, fracArrSwap]
    ring
  -- the second direction, with the two indices exchanged
  have hsecond : (∑ i ∈ Finset.Icc (-24 : ℤ) 24, ∑ j ∈ Finset.Icc (-24 : ℤ) 24,
        bspline (u - i) * (fracArrSwap j i * jumpGen1 (6 / 5) bspline (v - j)))
      = 625 / 108 * ∑ k ∈ Finset.Icc (-26 : ℤ) 26,
          (∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
              colProfile fracArrSwap (k + 2 - q) u) * |v - (k : ℝ)| ^ (9 / 5 : ℝ) := by
    rw [Finset.sum_comm,
      ← sum_Icc_jumpGen1_collapse (fun i j hi => fracArrSwap_eq_zero hi) v u]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [colProfile, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
    sum_Icc_jumpGen1_collapse (fun i j hi => fracArr_eq_zero hi) u v, hsecond]

end CenteredMaximal.Fractional

end

end
