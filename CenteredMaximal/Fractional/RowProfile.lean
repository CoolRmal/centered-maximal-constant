/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.RowCollapse

/-!
# The row profile of the `α = 6/5` generator certificate, as an integer cubic

`CenteredMaximal.Fractional.RowCollapse` turns the `1201`-cell spline sum of the certificate into
`53` rows, the `k`-th of which carries the *row profile*

`P_k(v) = ∑_{q<5} (−1)^q C(4,q) · colProfile fracArr (k + 2 − q) v`

against the single elementary function `|u − k|^{9/5}`.  This file evaluates that profile.  On the
unit cell `v = m + t`, `0 ≤ t ≤ 1`, every B-spline factor is its local cubic piece, so `P_k` is a
cubic in `t`, and `rowProfile_eq_cubic` writes it out with **integer** coefficients over the single
denominator `6 · fracDenNum`.

## Why an integer over one fixed denominator

The four coefficients are exact rationals whose denominators divide `6 · 5 · 10^16`: the `5 · 10^16`
is the common denominator of the certificate, and the `6` is the `1/6` of the cardinal cubic
B-spline.  They are carried as the integer numerator over that one denominator and never as a `ℚ`.
The reason is recorded in `CenteredMaximal.Fractional.MajorCell`: the kernel grinds `Rat.mul`
through `Nat.gcd`, which is compiled by well-founded recursion and costs about `20 µs` per Euclidean
step, so a rational multiplication with denominators of size `10^18` costs over a millisecond.  With
the denominator factored out of the fold, every step of `rowProfNum` is an integer multiply.

## Why the two guards

`rowProfCell` is guarded by `−2 ≤ i − k ≤ 2` on the row index and by `−2 ≤ m − j ≤ 1` on the column
index.  Neither is needed mathematically: outside the first range no `q < 5` has `i = k + 2 − q`, so
the alternating weight is absent, and outside the second range `betaCoef` already vanishes
(`betaCoef_eq_zero_of_lt`, `betaCoef_eq_zero_of_gt`).  Both are there so that the fold over the
`1201` cells skips a cell in four integer comparisons instead of multiplying three `19`-digit
integers and discarding the product.

## Why the swap symmetry is here

The row collapse reads the coefficient array in both index orders, as `fracArr` and `fracArrSwap`.
`fracArrSwap_eq_fracArr` says the two are the same array, because `diamondOrbit i j` lists `(j, i)`
alongside `(i, j)`, so exchanging the indices carries `fracCells` into a permutation of itself.
Hence the second coordinate direction of the collapse reads the **same** `53` row profiles as the
first, and `rowProfNum` has to be tabulated only once.

## Main results

* `perm_diamondOrbit_swap`, `perm_fracCells_swapCell`, `fracCellCoeff_swap`,
  `fracArrSwap_eq_fracArr`: **the swap symmetry** of the certificate's coefficient array.
* `betaNum`, `betaNum_cast`: `6 · betaCoef`, which is an integer.
* `betaCoef_eq_zero_of_lt`, `betaCoef_eq_zero_of_gt`: the locality of the local cubic pieces.
* `altChoose4`, `rowProfCell`, `rowProfNum`: the integer coefficient of `t ^ dg` in the `k`-th row
  profile on the cell `m`, scaled by `6 · fracDenNum`.
* `rowProfile_eq_cubic`: **the row profile is that explicit integer-coefficient cubic.**
-/

@[expose] public section

namespace CenteredMaximal.Fractional

/-! ### The swap symmetry of the cell list -/

/-- Exchanging the two indices of a cell, coefficient included. -/
def swapCell (p : (ℤ × ℤ) × ℤ) : (ℤ × ℤ) × ℤ := (p.1.swap, p.2)

/-- Exchanging two adjacent blocks of four while transposing the middle pair of each.  This is the
permutation that `Prod.swap` induces on the eight listed members of a diamond orbit. -/
private theorem perm_swapBlocks {α : Type*} (a b c d e f g h : α) :
    ([e, g, f, h, a, c, b, d] : List α).Perm [a, b, c, d, e, f, g, h] := by
  refine (List.perm_append_comm (l₁ := [e, g, f, h]) (l₂ := [a, c, b, d])).trans ?_
  exact ((List.Perm.swap b c [d]).cons a).append ((List.Perm.swap f g [h]).cons e)

/-- **Exchanging the two indices permutes an orbit.**  The orbit of `(i, j)` lists the four signed
copies of `(i, j)` followed by the four signed copies of `(j, i)`, and `Prod.swap` exchanges the two
blocks while transposing the middle pair of each. -/
theorem perm_diamondOrbit_swap (i j : ℤ) :
    ((diamondOrbit i j).map Prod.swap).Perm (diamondOrbit i j) := by
  rw [diamondOrbit, ← List.dedup_map_of_injective Prod.swap_injective]
  refine List.Perm.dedup ?_
  simp only [List.map_cons, List.map_nil, Prod.swap_prod_mk]
  exact perm_swapBlocks (i, j) (-i, j) (i, -j) (-i, -j) (j, i) (-j, i) (j, -i) (-j, -i)

/-- A symmetry of every orbit is a symmetry of the whole cell list. -/
private theorem perm_swapAux {f : ℤ × ℤ → ℤ × ℤ}
    (hf : ∀ i j : ℤ, ((diamondOrbit i j).map f).Perm (diamondOrbit i j)) :
    (fracCells.map fun p => (f p.1, p.2)).Perm fracCells := by
  rw [fracCells, List.map_flatMap]
  refine List.Perm.flatMap_left _ fun o _ => ?_
  have h := (hf o.1 o.2.1).map fun q : ℤ × ℤ => (q, o.2.2)
  rw [List.map_map] at h
  simpa [Function.comp_def] using h

/-- **The cell list is carried into a permutation of itself by the index swap.** -/
theorem perm_fracCells_swapCell : (fracCells.map swapCell).Perm fracCells :=
  perm_swapAux perm_diamondOrbit_swap

/-- **The coefficient array of the certificate is symmetric.** -/
theorem fracCellCoeff_swap (i j : ℤ) : fracCellCoeff (j, i) = fracCellCoeff (i, j) := by
  have h : ∀ p : (ℤ × ℤ) × ℤ,
      (if p.1 = (j, i) then p.2 else 0)
        = ((fun q : (ℤ × ℤ) × ℤ => if q.1 = (i, j) then q.2 else 0) ∘ swapCell) p := by
    rintro ⟨⟨x, y⟩, n⟩
    simp only [Function.comp_apply, swapCell, Prod.swap_prod_mk, Prod.mk.injEq]
    exact if_congr and_comm rfl rfl
  rw [fracCellCoeff, fracCellCoeff, List.map_congr_left fun p _ => h p, ← List.map_map]
  exact (perm_fracCells_swapCell.map _).sum_eq

/-! ### Integer-valued local B-spline coefficients -/

/-- `6 · betaCoef d dg`, which is an integer for every `d` and `dg`: the six values taken by
`betaCoef` are `1/6, 1/2, 2/3, −1, −1/2, −1/6`. -/
def betaNum (d : ℤ) (dg : ℕ) : ℤ :=
  if d = -2 then (if dg = 3 then 1 else 0)
  else if d = -1 then
    (if dg = 0 then 1 else if dg = 1 then 3 else if dg = 2 then 3 else if dg = 3 then -3 else 0)
  else if d = 0 then
    (if dg = 0 then 4 else if dg = 2 then -6 else if dg = 3 then 3 else 0)
  else if d = 1 then
    (if dg = 0 then 1 else if dg = 1 then -3 else if dg = 2 then 3 else if dg = 3 then -1 else 0)
  else 0

/-- **`betaNum` is six times `betaCoef`.** -/
theorem betaNum_cast (d : ℤ) (dg : ℕ) : ((betaNum d dg : ℤ) : ℚ) = 6 * betaCoef d dg := by
  simp only [betaNum, betaCoef]
  split_ifs <;> norm_num

/-- The real form of `betaNum_cast`. -/
theorem betaNum_cast_real (d : ℤ) (dg : ℕ) :
    ((betaNum d dg : ℤ) : ℝ) = 6 * (betaCoef d dg : ℝ) := by
  have h := congrArg (fun x : ℚ => (x : ℝ)) (betaNum_cast d dg)
  push_cast at h
  exact h

/-- Below the support of the cardinal cubic B-spline the local pieces vanish. -/
theorem betaCoef_eq_zero_of_lt {d : ℤ} (h : d < -2) (dg : ℕ) : betaCoef d dg = 0 := by
  have h1 : d ≠ -2 := by omega
  have h2 : d ≠ -1 := by omega
  have h3 : d ≠ 0 := by omega
  have h4 : d ≠ 1 := by omega
  simp [betaCoef, h1, h2, h3, h4]

/-- Above the support of the cardinal cubic B-spline the local pieces vanish. -/
theorem betaCoef_eq_zero_of_gt {d : ℤ} (h : 1 < d) (dg : ℕ) : betaCoef d dg = 0 := by
  have h1 : d ≠ -2 := by omega
  have h2 : d ≠ -1 := by omega
  have h3 : d ≠ 0 := by omega
  have h4 : d ≠ 1 := by omega
  simp [betaCoef, h1, h2, h3, h4]

/-! ### The integer row profile -/

/-- The alternating fourth-difference weight `(−1)^q C(4,q)` as an integer.  It is a palindrome, so
it may be read at `q` or at `4 − q` indifferently. -/
def altChoose4 (q : ℕ) : ℤ :=
  if q = 0 then 1 else if q = 1 then -4 else if q = 2 then 6
  else if q = 3 then -4 else if q = 4 then 1 else 0

/-- **The alternating weight, read backwards.** -/
theorem altChoose4_cast {q : ℕ} (hq : q < 5) :
    ((altChoose4 (4 - q) : ℤ) : ℝ) = (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) := by
  interval_cases q <;> norm_num [altChoose4, Nat.choose]

/-- The integer contribution of one certificate cell to the coefficient of `t ^ dg` in the `k`-th
row profile on the cell `m`, scaled by `6 · fracDenNum`.  Both guards are there to keep the fold
cheap; neither is needed for the identity. -/
def rowProfCell (m k : ℤ) (dg : ℕ) (p : (ℤ × ℤ) × ℤ) : ℤ :=
  if -2 ≤ p.1.1 - k ∧ p.1.1 - k ≤ 2 ∧ -2 ≤ m - p.1.2 ∧ m - p.1.2 ≤ 1 then
    altChoose4 (p.1.1 - k + 2).toNat * p.2 * betaNum (m - p.1.2) dg
  else 0

/-- **The integer coefficient of `t ^ dg` in the `k`-th row profile on the cell `m`**, scaled by
`6 · fracDenNum`. -/
def rowProfNum (m k : ℤ) (dg : ℕ) : ℤ := (fracCells.map (rowProfCell m k dg)).sum

/-! ### Two list-sum manipulations -/

/-- Pushing a real scalar through the cast of an integer list sum. -/
private theorem listSum_intCast_mul (l : List ((ℤ × ℤ) × ℤ)) (h : ((ℤ × ℤ) × ℤ) → ℤ) (c : ℝ) :
    c * (((l.map h).sum : ℤ) : ℝ) = (l.map fun p => c * ((h p : ℤ) : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons a u ih =>
      rw [List.map_cons, List.sum_cons, Int.cast_add, mul_add, ih, List.map_cons, List.sum_cons]

/-- Pulling a fixed denominator out of a list sum of integer casts. -/
private theorem listSum_intCast_div (l : List ((ℤ × ℤ) × ℤ)) (h : ((ℤ × ℤ) × ℤ) → ℤ) (c : ℝ) :
    (l.map fun p => ((h p : ℤ) : ℝ) / c).sum = (((l.map h).sum : ℤ) : ℝ) / c := by
  induction l with
  | nil => simp
  | cons a u ih =>
      rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, Int.cast_add, add_div]

/-- Exchanging a finite sum with a list sum. -/
private theorem sum_list_comm {ι : Type*} (s : Finset ι) (l : List ((ℤ × ℤ) × ℤ))
    (f : ι → ((ℤ × ℤ) × ℤ) → ℝ) :
    ∑ x ∈ s, (l.map (f x)).sum = (l.map fun p => ∑ x ∈ s, f x p).sum := by
  induction l with
  | nil => simp
  | cons a u ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [Finset.sum_add_distrib, ih]

noncomputable section

/-- The real weight that a cell numerator sitting at the row index `k + 2 − q` and the column index
`j` contributes to the coefficient of `t ^ dg` of the `k`-th row profile on the cell `m`. -/
def rowWeight (m : ℤ) (dg : ℕ) (q : ℕ) (j : ℤ) : ℝ :=
  (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) / (fracDenNum : ℝ) * (betaCoef (m - j) dg : ℝ)

/-- **One cell's share of the scaled row profile.**  For a cell at `(i, j₀)` the `(q, j)` double
sum collapses onto `j = j₀`, which lies in the box by `fracCells_absAdd_le`, and onto the single
`q < 5` with `k + 2 − q = i`, if there is one. -/
private theorem rowProfCell_cast (m k : ℤ) (dg : ℕ) {p : (ℤ × ℤ) × ℤ} (hp : p ∈ fracCells) :
    (∑ q ∈ Finset.range 5, ∑ j ∈ Finset.Icc (-24 : ℤ) 24,
        rowWeight m dg q j * ((if p.1 = (k + 2 - (q : ℤ), j) then p.2 else 0 : ℤ) : ℝ))
      = ((rowProfCell m k dg p : ℤ) : ℝ) / (6 * (fracDenNum : ℝ)) := by
  obtain ⟨⟨a, b⟩, n⟩ := p
  have habs : |a| + |b| ≤ 24 := fracCells_absAdd_le hp
  have hb : b ∈ Finset.Icc (-24 : ℤ) 24 := by
    have h1 := abs_nonneg a
    have h2 := neg_abs_le b
    have h3 := le_abs_self b
    rw [Finset.mem_Icc]
    exact ⟨by linarith, by linarith⟩
  -- the column sum collapses onto `j = b`
  have hinner : ∀ q : ℕ, (∑ j ∈ Finset.Icc (-24 : ℤ) 24,
      rowWeight m dg q j * ((if ((a, b) : ℤ × ℤ) = (k + 2 - (q : ℤ), j) then n else 0 : ℤ) : ℝ))
      = if a = k + 2 - (q : ℤ) then rowWeight m dg q b * (n : ℝ) else 0 := by
    intro q
    by_cases ha : a = k + 2 - (q : ℤ)
    · rw [if_pos ha]
      have hsum : ∀ j ∈ Finset.Icc (-24 : ℤ) 24,
          rowWeight m dg q j *
              ((if ((a, b) : ℤ × ℤ) = (k + 2 - (q : ℤ), j) then n else 0 : ℤ) : ℝ)
            = if j = b then rowWeight m dg q j * (n : ℝ) else 0 := by
        intro j _
        by_cases hj : j = b
        · have he : ((a, b) : ℤ × ℤ) = (k + 2 - (q : ℤ), j) := by rw [ha, hj]
          rw [if_pos he, if_pos hj]
        · have he : ¬ (((a, b) : ℤ × ℤ) = (k + 2 - (q : ℤ), j)) := fun hc =>
            hj (congrArg Prod.snd hc).symm
          rw [if_neg he, if_neg hj, Int.cast_zero, mul_zero]
      rw [Finset.sum_congr rfl hsum, Finset.sum_eq_single b]
      · simp
      · intro j _ hj
        exact if_neg hj
      · intro hnb
        exact absurd hb hnb
    · rw [if_neg ha]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [if_neg fun hc => ha (congrArg Prod.fst hc), Int.cast_zero, mul_zero]
  rw [Finset.sum_congr rfl fun q _ => hinner q]
  by_cases hg : -2 ≤ a - k ∧ a - k ≤ 2
  · -- the single surviving alternating weight
    set q₀ : ℕ := (k + 2 - a).toNat with hq₀def
    have hq₀ : (q₀ : ℤ) = k + 2 - a := by rw [hq₀def]; omega
    have hq₀lt : q₀ < 5 := by omega
    rw [Finset.sum_eq_single q₀]
    · rw [if_pos (by omega : a = k + 2 - (q₀ : ℤ))]
      rw [rowProfCell]
      by_cases hbg : -2 ≤ m - b ∧ m - b ≤ 1
      · rw [if_pos ⟨hg.1, hg.2, hbg.1, hbg.2⟩]
        have htn : ((a, b) : ℤ × ℤ).1 - k + 2 = ((4 - q₀ : ℕ) : ℤ) := by
          simp only []
          omega
        have hcast : (((a, b) : ℤ × ℤ).1 - k + 2).toNat = 4 - q₀ := by rw [htn]; simp
        rw [hcast, rowWeight]
        push_cast [altChoose4_cast hq₀lt, betaNum_cast_real]
        field_simp
      · have hz : (betaCoef (m - b) dg : ℚ) = 0 := by
          rcases not_and_or.1 hbg with h | h
          · exact betaCoef_eq_zero_of_lt (by omega) dg
          · exact betaCoef_eq_zero_of_gt (by omega) dg
        rw [if_neg fun hc => hbg ⟨hc.2.2.1, hc.2.2.2⟩, rowWeight, hz]
        push_cast
        ring
    · intro q hq hne
      rw [Finset.mem_range] at hq
      refine if_neg fun hc => hne ?_
      have h4 : (q : ℤ) ≤ 4 := by exact_mod_cast Nat.lt_succ_iff.1 hq
      omega
    · intro hnb
      exact absurd (Finset.mem_range.2 hq₀lt) hnb
  · rw [rowProfCell, if_neg fun hc => hg ⟨hc.1, hc.2.1⟩]
    push_cast
    rw [zero_div]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.mem_range] at hq
    refine if_neg fun hc => hg ?_
    have h4 : (q : ℤ) ≤ 4 := by exact_mod_cast Nat.lt_succ_iff.1 hq
    have h0 : (0 : ℤ) ≤ (q : ℤ) := Int.natCast_nonneg q
    omega

/-- **The degree-`dg` coefficient of the `k`-th row profile is `rowProfNum` over `6 · fracDenNum`.**
This is `rowProfile_eq_cubic` with the `t`-powers stripped off. -/
theorem rowProfNum_cast (m k : ℤ) (dg : ℕ) :
    (∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
        ∑ j ∈ Finset.Icc (-24 : ℤ) 24, fracArr (k + 2 - q) j * (betaCoef (m - j) dg : ℝ))
      = ((rowProfNum m k dg : ℤ) : ℝ) / (6 * (fracDenNum : ℝ)) := by
  -- one `(q, j)` term, as a sum over the cells
  have hterm : ∀ (q : ℕ) (j : ℤ),
      (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
          (fracArr (k + 2 - (q : ℤ)) j * (betaCoef (m - j) dg : ℝ))
        = (fracCells.map fun p =>
            rowWeight m dg q j *
              ((if p.1 = (k + 2 - (q : ℤ), j) then p.2 else 0 : ℤ) : ℝ)).sum := by
    intro q j
    rw [← listSum_intCast_mul]
    have hN : fracArr (k + 2 - (q : ℤ)) j
        = (((fracCells.map fun p => if p.1 = (k + 2 - (q : ℤ), j) then p.2 else 0).sum : ℤ) : ℝ)
            / ((fracDenNum : ℤ) : ℝ) := rfl
    rw [hN, rowWeight]
    ring
  -- exchange the two finite sums with the list sum
  have hexch :
      (∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
          ∑ j ∈ Finset.Icc (-24 : ℤ) 24, fracArr (k + 2 - q) j * (betaCoef (m - j) dg : ℝ))
        = (fracCells.map fun p => ∑ q ∈ Finset.range 5, ∑ j ∈ Finset.Icc (-24 : ℤ) 24,
            rowWeight m dg q j *
              ((if p.1 = (k + 2 - (q : ℤ), j) then p.2 else 0 : ℤ) : ℝ)).sum := by
    rw [← sum_list_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.mul_sum, ← sum_list_comm]
    exact Finset.sum_congr rfl fun j _ => hterm q j
  rw [hexch, List.map_congr_left fun p hp => rowProfCell_cast m k dg hp,
    listSum_intCast_div, rowProfNum]

/-- **The row profile is an explicit integer-coefficient cubic on a unit cell.**  On the cell
`v = m + t`, `0 ≤ t ≤ 1`, the fourth difference of the column profiles that the row collapse of
`sum_Icc_jumpGen1_collapse` attaches to the row index `k` is the cubic whose coefficients are the
integers `rowProfNum m k ·` over the single denominator `6 · fracDenNum`. -/
theorem rowProfile_eq_cubic (m k : ℤ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
        colProfile fracArr (k + 2 - q) ((m : ℝ) + t))
      = ∑ dg ∈ Finset.range 4,
          ((rowProfNum m k dg : ℤ) : ℝ) / (6 * (fracDenNum : ℝ)) * t ^ dg := by
  have hstep : ∀ q ∈ Finset.range 5,
      (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) * colProfile fracArr (k + 2 - q) ((m : ℝ) + t)
        = ∑ dg ∈ Finset.range 4,
            ((-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
              ∑ j ∈ Finset.Icc (-24 : ℤ) 24, fracArr (k + 2 - q) j * (betaCoef (m - j) dg : ℝ))
              * t ^ dg := by
    intro q _
    rw [colProfile_eq_cubic fracArr (k + 2 - q) m ht ht1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun dg _ => by ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm]
  refine Finset.sum_congr rfl fun dg _ => ?_
  rw [← Finset.sum_mul, rowProfNum_cast]

/-! ### The two coordinate directions read the same profile -/

/-- **The coefficient array is symmetric**, so the second coordinate direction of the row collapse
reads exactly the same row profiles as the first. -/
theorem fracArrSwap_eq_fracArr : fracArrSwap = fracArr := by
  funext i j
  rw [fracArrSwap, fracArr, fracCellCoeff_swap]

end

end CenteredMaximal.Fractional

end
