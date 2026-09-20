/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.RowFold
public import CenteredMaximal.Fractional.RowProfile
public import CenteredMaximal.Fractional.SplineAffine

/-!
# One coordinate direction of the spline half of a leaf's model

`CenteredMaximal.Fractional.splineGen_eq_rowSum` writes the spline half of the generator as `53`
rows in each of two coordinate directions.  This file models **one** direction: it fixes the row
model of `CenteredMaximal.Fractional.rowProduct_bound` for every row, concatenates the rows' terms,
adds up their errors, and proves the resulting inequality against the direction's row sum.

## The two kinds of row

A row's Taylor interval is `[c − δ, c + δ]` with `c = u_c − k`, so it is the *distance from the
centre of the rectangle to the row* that decides which model is available.  Since `u_c` is a dyadic
midpoint of denominator `1/δ`, that distance is never less than `δ` and never zero, and exactly two
cases occur:

* `δ < |c|`: the interval stays away from the origin and the **cubic** model of
  `CenteredMaximal.Fractional.abs_rpow_nine_fifths_taylor` applies, with the four terms
  `ρ(a) |c| ^ ((9 − 5a)/5)` and the remainder `(9/625) δ⁴ (|c| − δ)^{−11/5}`;
* `|c| = δ`: the interval *touches* the origin, the cubic model is unavailable, and the **affine**
  model of `CenteredMaximal.Fractional.abs_rpow_nine_fifths_affine` applies, with two terms and the
  remainder `(4/5) δ^{9/5}`.

The second case is not exceptional: `2644` of the certificate's `4582` rectangles have at least one
touching row.

## Where the errors go

Both remainders multiply the row profile, so each is weighted by the profile's Bernstein sup bound
`CenteredMaximal.Fractional.bernMax` on the rectangle, and both are rationalised by taking the
*upper* end of the enclosure of the power they contain — `(|c| − δ)^{−11/5}` and `δ^{9/5}`
respectively.  A direction's error is therefore a single rational, the sum of `53` such products,
and it is subtracted once rather than being carried through the coefficients.

## Main results

* `rowProduct_bound_touch`: the model of a row whose interval touches the origin.
* `rowErrQ`, `rowTerms_bound`: the two cases in one statement, with a rational error.
* `rowProfCoeff`: the row profile, recentred from its cell to the centre of the rectangle.
* `dirTerms`, `dirErrQ`, `dirModel_bound`: **one coordinate direction of the model**, and the
  inequality it satisfies against that direction's row sum.
-/

@[expose] public section

open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### A row whose interval touches the origin -/

/-- **The centred model of a row whose Taylor interval touches the origin.**  Only the affine part
of the model survives, and the remainder is `(4/5) δ^{9/5}` rather than `O(δ⁴)`. -/
theorem rowProduct_bound_touch {c s t : ℝ} {m δ : ℚ} (hδ : 0 < δ) (hmδ : m = δ)
    (hm : (m : ℝ) = |c|) {pos : Bool} (hpos : if pos then 0 < c else c < 0)
    (hs : |s| ≤ (δ : ℝ)) (ht : |t| ≤ (δ : ℝ)) (p : ℕ → ℚ) :
    |(∑ b ∈ Finset.range 4, (p b : ℝ) * t ^ b) * |c + s| ^ (9 / 5 : ℝ)
        - ∑ a ∈ Finset.range 2, ∑ b ∈ Finset.range 4,
            ((taylorRhoQ pos a * p b : ℚ) : ℝ) * (m : ℝ) ^ (((taylorExp a : ℤ) : ℝ) / 5)
              * s ^ a * t ^ b|
      ≤ ((bernMax p δ : ℚ) : ℝ) * (4 / 5 * (δ : ℝ) ^ (9 / 5 : ℝ)) := by
  have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
  have hcabs : |c| = (δ : ℝ) := by rw [← hm, hmδ]
  have hbern := abs_centredCubic_le_bernMax (a := p) hδ ht
  -- the product of the two factors
  have hprod : (∑ b ∈ Finset.range 4, (p b : ℝ) * t ^ b) * nineFifthsAffine c (c + s)
      = ∑ a ∈ Finset.range 2, ∑ b ∈ Finset.range 4,
          ((taylorRhoQ pos a * p b : ℚ) : ℝ) * (m : ℝ) ^ (((taylorExp a : ℤ) : ℝ) / 5)
            * s ^ a * t ^ b := by
    rw [nineFifthsAffine_eq_sum hm hpos, add_sub_cancel_left, mul_comm, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  have hsplit : (∑ b ∈ Finset.range 4, (p b : ℝ) * t ^ b) * |c + s| ^ (9 / 5 : ℝ)
      - ∑ a ∈ Finset.range 2, ∑ b ∈ Finset.range 4,
          ((taylorRhoQ pos a * p b : ℚ) : ℝ) * (m : ℝ) ^ (((taylorExp a : ℤ) : ℝ) / 5)
            * s ^ a * t ^ b
      = (∑ b ∈ Finset.range 4, (p b : ℝ) * t ^ b) *
          ((|c + s| ^ (9 / 5 : ℝ)) - nineFifthsAffine c (c + s)) := by
    rw [← hprod]
    ring
  have hxc : |c + s - c| ≤ (δ : ℝ) := by rwa [add_sub_cancel_left]
  have haff := abs_rpow_nine_fifths_affine (c := c) (δ := (δ : ℝ)) (x := c + s) hδR hcabs hxc
  rw [hsplit, abs_mul]
  refine mul_le_mul hbern haff (abs_nonneg _) ?_
  have := bernMax_nonneg p δ
  exact_mod_cast this

/-! ### The two kinds of row in one statement -/

/-- **The rational error of one row.**  The profile's Bernstein sup bound times the upper end of
the enclosure of the remainder's power. -/
def rowErrQ (L : List FifthEnc) (m δ : ℚ) (touch : Bool) (p : ℕ → ℚ) : ℚ :=
  bernMax p δ *
    (if touch then 4 / 5 * (encItv L δ 9).hi
      else 9 / 625 * δ ^ 4 * (encItv L (m - δ) (-11)).hi)

/-- **The model of one row, in both cases.**  `touch` records whether the row's Taylor interval
touches the origin; the model then has two degrees instead of four and the other remainder. -/
theorem rowTerms_bound {L : List FifthEnc} (hL : L.all (fun c => c.check 12) = true)
    {c s t : ℝ} {m δ : ℚ} (hδ : 0 < δ) {pos touch : Bool} (hm : (m : ℝ) = |c|)
    (hpos : if pos then 0 < c else c < 0) (htouch : if touch then m = δ else δ < m)
    (hs : |s| ≤ (δ : ℝ)) (ht : |t| ≤ (δ : ℝ)) (p : ℕ → ℚ) :
    termsValR (rowTerms (if touch then 2 else 4) pos m p) s t
        - ((rowErrQ L m δ touch p : ℚ) : ℝ)
      ≤ (∑ b ∈ Finset.range 4, (p b : ℝ) * t ^ b) * |c + s| ^ (9 / 5 : ℝ) := by
  have hbnn : (0 : ℝ) ≤ ((bernMax p δ : ℚ) : ℝ) := by
    have := bernMax_nonneg p δ
    exact_mod_cast this
  cases touch with
  | true =>
      have hmδ : m = δ := by simpa using htouch
      have hδR : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ
      -- the enclosure of `δ ^ (9/5)`
      have henc := encItv_mem hL hδ 9
      have hexp : (((9 : ℤ) : ℝ) / 5) = 9 / 5 := by norm_num
      rw [hexp] at henc
      have hrem : (δ : ℝ) ^ (9 / 5 : ℝ) ≤ (((encItv L δ 9).hi : ℚ) : ℝ) := henc.2
      have hstep := rowProduct_bound_touch hδ hmδ hm hpos hs ht p
      have hcast : ((rowErrQ L m δ true p : ℚ) : ℝ)
          = ((bernMax p δ : ℚ) : ℝ) * (4 / 5 * (((encItv L δ 9).hi : ℚ) : ℝ)) := by
        rw [rowErrQ, if_pos rfl]
        push_cast
        ring
      rw [termsValR_rowTerms, if_pos rfl, hcast]
      have habs := abs_le.1 hstep
      have hmono : ((bernMax p δ : ℚ) : ℝ) * (4 / 5 * (δ : ℝ) ^ (9 / 5 : ℝ))
          ≤ ((bernMax p δ : ℚ) : ℝ) * (4 / 5 * (((encItv L δ 9).hi : ℚ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hbnn
        linarith
      linarith [habs.1]
  | false =>
      have hlt : δ < m := by simpa using htouch
      have hpos' : (0 : ℚ) < m - δ := by linarith
      have henc := encItv_mem hL hpos' (-11)
      have hexp : ((((-11 : ℤ)) : ℝ) / 5) = -(11 / 5 : ℝ) := by norm_num
      rw [hexp] at henc
      have hrem : (((m - δ : ℚ)) : ℝ) ^ (-(11 / 5) : ℝ)
          ≤ (((encItv L (m - δ) (-11)).hi : ℚ) : ℝ) := henc.2
      have hstep := rowProduct_bound hδ hlt hm hpos hs ht p
      have hcast : ((rowErrQ L m δ false p : ℚ) : ℝ)
          = ((bernMax p δ : ℚ) : ℝ) *
            (9 / 625 * (δ : ℝ) ^ 4 * (((encItv L (m - δ) (-11)).hi : ℚ) : ℝ)) := by
        rw [rowErrQ, if_neg (by simp)]
        push_cast
        ring
      rw [termsValR_rowTerms, if_neg (by simp), hcast]
      have habs := abs_le.1 hstep
      have hδ4 : (0 : ℝ) ≤ 9 / 625 * (δ : ℝ) ^ 4 := by positivity
      have hmono : ((bernMax p δ : ℚ) : ℝ) *
            (9 / 625 * (δ : ℝ) ^ 4 * (((m - δ : ℚ)) : ℝ) ^ (-(11 / 5) : ℝ))
          ≤ ((bernMax p δ : ℚ) : ℝ) *
            (9 / 625 * (δ : ℝ) ^ 4 * (((encItv L (m - δ) (-11)).hi : ℚ) : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrem hδ4) hbnn
      linarith [habs.1]

/-! ### List sums of rationals and of differences -/

private theorem cast_list_sum {α : Type*} (l : List α) (f : α → ℚ) :
    (((l.map f).sum : ℚ) : ℝ) = (l.map fun x => ((f x : ℚ) : ℝ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.map_cons, List.sum_cons, Rat.cast_add, ih, List.map_cons, List.sum_cons]

private theorem list_sum_sub {α : Type*} (l : List α) (f e : α → ℝ) :
    (l.map f).sum - (l.map e).sum = (l.map fun x => f x - e x).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons, List.map_cons,
        List.sum_cons, ← ih]
      ring

private theorem list_sum_le {α : Type*} {l : List α} {f g : α → ℝ} (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      exact add_le_add (h a (List.mem_cons_self ..))
        (ih fun x hx => h x (List.mem_cons_of_mem a hx))

/-! ### The row profile, recentred -/

/-- **The row profile of the cell `mcell`, recentred at the centre of the rectangle.**  The
coefficients of `CenteredMaximal.Fractional.rowProfile_eq_cubic` are integers over the single
denominator `6 · fracDenNum`; `mu` is the offset of the centre of the rectangle from the cell, and
`CenteredMaximal.Fractional.recentre` performs the binomial shift. -/
def rowProfCoeff (mcell k : ℤ) (mu : ℚ) (b : ℕ) : ℚ :=
  recentre (fun dg => (rowProfNum mcell k dg : ℚ) / (6 * (fracDenNum : ℚ))) mu b

/-- **The recentred profile is the row profile.** -/
theorem rowProfCoeff_spec (mcell k : ℤ) (mu : ℚ) {t : ℝ} (ht0 : 0 ≤ (mu : ℝ) + t)
    (ht1 : (mu : ℝ) + t ≤ 1) :
    ∑ b ∈ Finset.range 4, ((rowProfCoeff mcell k mu b : ℚ) : ℝ) * t ^ b
      = ∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
          colProfile fracArr (k + 2 - q) ((mcell : ℝ) + ((mu : ℝ) + t)) := by
  rw [rowProfile_eq_cubic mcell k ht0 ht1]
  simp only [rowProfCoeff]
  rw [← recentre_spec (fun dg => (rowProfNum mcell k dg : ℚ) / (6 * (fracDenNum : ℚ))) mu t]
  refine Finset.sum_congr rfl fun dg _ => ?_
  rw [add_comm ((mu : ℝ)) t]
  push_cast
  ring

/-! ### One coordinate direction -/

/-- The distance from the centre of the rectangle to the row `k`. -/
def rowDist (uc : ℚ) (k : ℤ) : ℚ := |uc - (k : ℚ)|

/-- Whether the centre of the rectangle lies above the row `k`. -/
def rowPos (uc : ℚ) (k : ℤ) : Bool := decide (0 < uc - (k : ℚ))

/-- Whether the row `k`'s Taylor interval touches the origin. -/
def rowTouch (uc δ : ℚ) (k : ℤ) : Bool := decide (rowDist uc k = δ)

/-- **The terms of one coordinate direction of the model**: the `53` rows concatenated. -/
def dirTerms (mcell : ℤ) (uc mu δ : ℚ) : List ModelTerm :=
  rowIdx.flatMap fun k =>
    rowTerms (if rowTouch uc δ k then 2 else 4) (rowPos uc k) (rowDist uc k)
      (rowProfCoeff mcell k mu)

/-- **The error of one coordinate direction of the model.** -/
def dirErrQ (L : List FifthEnc) (mcell : ℤ) (uc mu δ : ℚ) : ℚ :=
  (rowIdx.map fun k =>
    rowErrQ L (rowDist uc k) δ (rowTouch uc δ k) (rowProfCoeff mcell k mu)).sum

/-- Every term of a direction has a positive base and a bicubic bidegree. -/
theorem dirTerms_pos {mcell : ℤ} {uc mu δ : ℚ} (hδ : 0 < δ)
    (hsafe : ∀ k ∈ rowIdx, δ ≤ rowDist uc k) :
    ∀ w ∈ dirTerms mcell uc mu δ, 0 < w.x ∧ w.a < 4 ∧ w.b < 4 := by
  refine mem_flatMap_of fun k hk => ?_
  refine rowTerms_pos ?_ (lt_of_lt_of_le hδ (hsafe k hk)) _ _
  split <;> norm_num

/-- **One coordinate direction of the model minorises that direction's row sum.** -/
theorem dirModel_bound {L : List FifthEnc} (hL : L.all (fun c => c.check 12) = true)
    {mcell : ℤ} {uc mu δ : ℚ} (hδ : 0 < δ) (hsafe : ∀ k ∈ rowIdx, δ ≤ rowDist uc k)
    {s t : ℝ} (hs : |s| ≤ (δ : ℝ)) (ht : |t| ≤ (δ : ℝ))
    (ht0 : 0 ≤ (mu : ℝ) + t) (ht1 : (mu : ℝ) + t ≤ 1) :
    termsValR (dirTerms mcell uc mu δ) s t - ((dirErrQ L mcell uc mu δ : ℚ) : ℝ)
      ≤ ∑ k ∈ Finset.Icc (-26 : ℤ) 26,
          (∑ q ∈ Finset.range 5, (-1 : ℝ) ^ q * (Nat.choose 4 q : ℝ) *
              colProfile fracArr (k + 2 - q) ((mcell : ℝ) + ((mu : ℝ) + t)))
            * |((uc : ℝ) + s) - (k : ℝ)| ^ (9 / 5 : ℝ) := by
  rw [dirTerms, termsValR_flatMap, dirErrQ, cast_list_sum, sum_Icc_eq_rowIdx, list_sum_sub]
  refine list_sum_le fun k hk => ?_
  -- the row's Taylor centre
  set c : ℝ := (uc : ℝ) - (k : ℝ) with hc
  have hdist : ((rowDist uc k : ℚ) : ℝ) = |c| := by
    rw [rowDist, hc]
    push_cast
    rfl
  have hle : δ ≤ rowDist uc k := hsafe k hk
  have hne : uc - (k : ℚ) ≠ 0 := by
    intro h
    rw [rowDist, h, abs_zero] at hle
    linarith
  have hposC : if rowPos uc k then 0 < c else c < 0 := by
    rw [rowPos, hc]
    by_cases hp : (0 : ℚ) < uc - (k : ℚ)
    · rw [decide_eq_true hp, if_pos rfl]
      have : (0 : ℝ) < ((uc - (k : ℚ) : ℚ) : ℝ) := by exact_mod_cast hp
      push_cast at this
      linarith
    · rw [decide_eq_false hp]
      simp only [Bool.false_eq_true, if_false]
      have hneg : uc - (k : ℚ) < 0 := lt_of_le_of_ne (not_lt.1 hp) hne
      have : ((uc - (k : ℚ) : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
      push_cast at this
      linarith
  have htouch : if rowTouch uc δ k then rowDist uc k = δ else δ < rowDist uc k := by
    rw [rowTouch]
    by_cases hq : rowDist uc k = δ
    · rw [decide_eq_true hq, if_pos rfl]
      exact hq
    · rw [decide_eq_false hq]
      simp only [Bool.false_eq_true, if_false]
      exact lt_of_le_of_ne hle fun h => hq h.symm
  have hstep := rowTerms_bound hL hδ hdist hposC htouch hs ht (rowProfCoeff mcell k mu)
  rw [rowProfCoeff_spec mcell k mu ht0 ht1] at hstep
  have hcs : c + s = (uc : ℝ) + s - (k : ℝ) := by rw [hc]; ring
  rw [hcs] at hstep
  exact hstep

end CenteredMaximal.Fractional

end
