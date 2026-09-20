/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.ModelTerm
public import CenteredMaximal.Fractional.RowTaylor

/-!
# Folding the `53` rows of one coordinate direction into a model

`CenteredMaximal.Fractional.rowProduct_bound` models **one** row of the collapsed spline generator.
A leaf has `53` rows in each of two coordinate directions, and this file supplies the bookkeeping
that turns one row's sixteen terms into a list and the list of lists into the flat
`List ModelTerm` that `CenteredMaximal.Fractional.jumpGen_fracKernel_nonneg_of_terms` consumes.

## Three pieces of glue

* **The index range.**  `CenteredMaximal.Fractional.splineGen_eq_rowSum` sums over
  `Finset.Icc (-26) 26`, while a model is a list; `sum_Icc_eq_rowIdx` says the two agree, and it is
  `rfl` up to the shape of the map, because `Finset.Icc` on `ℤ` *is* a translated `List.range`.
* **Concatenation.**  A model built row by row is a `List.flatMap`, and `termsValR_flatMap` says its
  value is the sum of the rows' values.  Concatenating rather than merging equal bidegrees is
  deliberate: `termsCoI` merges them when it reads a bidegree out, and doing it there rather than
  here means the fold is a single pass with no search.
* **Re-centring.**  `CenteredMaximal.Fractional.colProfile_eq_cubic` gives a row profile as a cubic
  in the offset from the *cell*, while the model wants the offset from the *centre of the leaf's
  rectangle*.  `recentre` performs the binomial shift between the two, in exact rational
  arithmetic.

## Main results

* `rowIdx`, `sum_Icc_eq_rowIdx`: the `53` row indices as a list, and the sum over them.
* `termsValR_flatMap`: the value of a concatenated model.
* `rowTerms`, `termsValR_rowTerms`, `rowTerms_pos`: the terms of one row, their value, and the two
  conditions the assembly needs of them.  The degree bound `deg` is `4` for a row whose interval
  stays away from the origin and `2` for one that touches it, where only the affine model is
  available.
* `recentre`, `recentre_spec`: the binomial shift of a cubic's coefficients.
-/

@[expose] public section

noncomputable section

namespace CenteredMaximal.Fractional

/-! ### Sums over a range, as list sums -/

/-- A sum over `Finset.range` is the sum of the mapped `List.range`, definitionally. -/
theorem sum_range_list {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := rfl

/-- The `53` row indices of the collapsed spline generator. -/
def rowIdx : List ℤ := (List.range 53).map fun i => (i : ℤ) - 26

theorem rowIdx_nodup : rowIdx.Nodup := by decide

/-- **The sum over the row range is a list sum.**  `Finset.Icc` on `ℤ` is a translated
`List.range`, so this is `rfl` once the two maps are composed. -/
theorem sum_Icc_eq_rowIdx {M : Type*} [AddCommMonoid M] (f : ℤ → M) :
    ∑ k ∈ Finset.Icc (-26 : ℤ) 26, f k = (rowIdx.map f).sum := by
  rw [rowIdx]
  simp only [List.map_map]
  rfl

/-! ### The value of a concatenated model -/

/-- **A model built row by row has the sum of the rows' values.** -/
theorem termsValR_flatMap {α : Type*} (l : List α) (g : α → List ModelTerm) (s t : ℝ) :
    termsValR (l.flatMap g) s t = (l.map fun x => termsValR (g x) s t).sum := by
  induction l with
  | nil => rw [List.flatMap_nil, termsValR_nil, List.map_nil, List.sum_nil]
  | cons a l ih =>
      rw [List.flatMap_cons, termsValR_append, ih, List.map_cons, List.sum_cons]

/-- Membership in a concatenated model. -/
theorem mem_flatMap_of {α : Type*} {l : List α} {g : α → List ModelTerm} {P : ModelTerm → Prop}
    (h : ∀ x ∈ l, ∀ w ∈ g x, P w) : ∀ w ∈ l.flatMap g, P w := by
  intro w hw
  obtain ⟨x, hx, hwx⟩ := List.mem_flatMap.1 hw
  exact h x hx w hwx

/-! ### The terms of one row -/

/-- **The terms of one row of one coordinate direction.**  The `(a, b)` term carries the `a`-th
Taylor coefficient of `|· − k| ^ (9/5)` at the centre, whose base is the distance `m` from the
centre to the row, times the `b`-th coefficient of the recentred row profile.

`deg` is `4` on a row whose interval stays away from the origin and `2` on one that touches it,
where `CenteredMaximal.Fractional.abs_rpow_nine_fifths_taylor` does not apply and only the affine
model is available. -/
def rowTerms (deg : ℕ) (pos : Bool) (m : ℚ) (p : ℕ → ℚ) : List ModelTerm :=
  (List.range deg).flatMap fun a =>
    (List.range 4).map fun b => ⟨a, b, taylorRhoQ pos a * p b, m, taylorExp a⟩

/-- **The value of one row's terms** is the centred bicubic of
`CenteredMaximal.Fractional.rowProduct_bound`. -/
theorem termsValR_rowTerms (deg : ℕ) (pos : Bool) (m : ℚ) (p : ℕ → ℚ) (s t : ℝ) :
    termsValR (rowTerms deg pos m p) s t
      = ∑ a ∈ Finset.range deg, ∑ b ∈ Finset.range 4,
          ((taylorRhoQ pos a * p b : ℚ) : ℝ) * (m : ℝ) ^ (((taylorExp a : ℤ) : ℝ) / 5)
            * s ^ a * t ^ b := by
  rw [rowTerms, termsValR_flatMap, sum_range_list]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [termsValR, List.map_map, sum_range_list]
  exact Finset.sum_congr rfl fun b _ => rfl

/-- **The two conditions the assembly needs of a row's terms**: a positive base and a bidegree
inside the bicubic box. -/
theorem rowTerms_pos {deg : ℕ} (hdeg : deg ≤ 4) {m : ℚ} (hm : 0 < m) (pos : Bool) (p : ℕ → ℚ) :
    ∀ w ∈ rowTerms deg pos m p, 0 < w.x ∧ w.a < 4 ∧ w.b < 4 := by
  refine mem_flatMap_of fun a ha w hw => ?_
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hw
  exact ⟨hm, lt_of_lt_of_le (List.mem_range.1 ha) hdeg, List.mem_range.1 hb⟩

/-! ### Re-centring a cubic -/

/-- **The binomial shift of a cubic's coefficients.**  If `A` are the coefficients of a cubic in
the offset from a cell and `μ` is the offset of the centre of the leaf's rectangle from that cell,
then `recentre A μ` are its coefficients in the offset from the centre. -/
def recentre (A : ℕ → ℚ) (μ : ℚ) : ℕ → ℚ
  | 0 => A 0 + A 1 * μ + A 2 * μ ^ 2 + A 3 * μ ^ 3
  | 1 => A 1 + 2 * A 2 * μ + 3 * A 3 * μ ^ 2
  | 2 => A 2 + 3 * A 3 * μ
  | 3 => A 3
  | _ + 4 => 0

/-- **Re-centring is value-preserving.** -/
theorem recentre_spec (A : ℕ → ℚ) (μ : ℚ) (t : ℝ) :
    ∑ dg ∈ Finset.range 4, ((A dg : ℚ) : ℝ) * (t + (μ : ℝ)) ^ dg
      = ∑ b ∈ Finset.range 4, ((recentre A μ b : ℚ) : ℝ) * t ^ b := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, recentre]
  push_cast
  ring

end CenteredMaximal.Fractional

end

end
