/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.FifthTable

/-!
# Rational intervals, and the enclosure reader of the generator certificate

Every coefficient of a leaf's polynomial model is a sum of terms `q · x ^ (e/5)` with `q` rational
and `x` a positive rational, so it is an *irrational* number known only to lie between two
rationals.  The coefficients of the linear monomials, moreover, are sums of some fifteen hundred
such terms that **very nearly cancel**, and the certificate passes only because the cancellation
happens before absolute values are taken (see
`CenteredMaximal.Fractional.jumpGen_fracKernel_nonneg_of_centred`).  A coefficient must therefore be
carried as an *interval* that is added to, not as a pair of independent bounds on the two halves.

This file supplies that arithmetic: a two-rational interval, its real membership predicate, the
three operations a model fold performs — addition, scaling by a rational, and one multiplication by
the interval of `16 ^ (6/5)` — and the two numbers a leaf check reads out of a coefficient, namely
its lower end and the larger of the absolute values of its two ends.

## The enclosure reader is total

`CenteredMaximal.Fractional.encTable` holds the `11045` fifth-root enclosures the certificate
consumes, each verified by one kernel reduction.  `encItv` reads a row out of a table by its
`(numerator, denominator, exponent)` key — and when the key is *absent* it falls back to computing
`rpowFifthEnc` on the spot.  The fallback is what makes `encItv_mem` unconditional: there is no
"key present" side condition to thread through a fold of a hundred thousand terms, and a table that
is missing a row costs kernel time rather than soundness.  A lookup that misses is `11.8 ms` of
integer fifth root, against the few hundred list steps of a lookup that hits.

## Main results

* `RatItv`, `RatItv.Mem`: a rational interval and what it means for a real to lie in it.
* `RatItv.mem_add`, `RatItv.mem_scale`, `RatItv.mem_mul`, `RatItv.mem_pt`: **the arithmetic is
  sound.**  `mem_mul` is the four-corner bound of interval multiplication, which is where the sign
  of neither factor is known.
* `RatItv.abs_le_absmax`: the number a leaf check pays for a non-constant monomial.
* `encItv`, `encItv_mem`: **the enclosure reader**, and the fact that it always brackets
  `x ^ (e/5)`.
-/

@[expose] public section

namespace CenteredMaximal.Fractional

/-! ### Rational intervals -/

/-- A closed interval with rational endpoints, as it is carried through a model fold.  No
invariant `lo ≤ hi` is imposed: the predicate `Mem` is what the soundness lemmas speak about, and
an interval with `hi < lo` simply has no members. -/
structure RatItv where
  /-- The lower endpoint. -/
  lo : ℚ
  /-- The upper endpoint. -/
  hi : ℚ

namespace RatItv

/-- A real number lies in a rational interval when it is between the two endpoints. -/
def Mem (I : RatItv) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- The one-point interval of a rational. -/
def pt (q : ℚ) : RatItv := ⟨q, q⟩

/-- The zero interval. -/
def zero : RatItv := pt 0

/-- The sum of two intervals. -/
def add (I J : RatItv) : RatItv := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- An interval scaled by a rational, with the endpoints exchanged when the scalar is negative. -/
def scale (q : ℚ) (I : RatItv) : RatItv :=
  if 0 ≤ q then ⟨q * I.lo, q * I.hi⟩ else ⟨q * I.hi, q * I.lo⟩

/-- The product of two intervals, as the smallest and largest of the four corner products. -/
def mul (I J : RatItv) : RatItv :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
    max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

/-- The larger of the absolute values of the two endpoints: an upper bound for `|x|` over the
interval, and what a leaf check pays for a non-constant monomial. -/
def absmax (I : RatItv) : ℚ := max |I.lo| |I.hi|

theorem absmax_nonneg (I : RatItv) : 0 ≤ I.absmax :=
  le_trans (abs_nonneg I.lo) (le_max_left _ _)

/-! ### Soundness of the arithmetic -/

theorem mem_pt (q : ℚ) : (pt q).Mem ((q : ℚ) : ℝ) := ⟨le_refl _, le_refl _⟩

theorem mem_zero : zero.Mem 0 := by
  refine ⟨?_, ?_⟩ <;> simp [zero, pt]

theorem mem_add {I J : RatItv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.add J).Mem (x + y) := by
  refine ⟨?_, ?_⟩ <;> rw [add] <;> push_cast <;> [exact add_le_add hx.1 hy.1;
    exact add_le_add hx.2 hy.2]

theorem mem_scale {I : RatItv} {x : ℝ} (q : ℚ) (hx : I.Mem x) :
    (scale q I).Mem ((q : ℝ) * x) := by
  rw [scale]
  split
  · rename_i hq
    have hq' : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    refine ⟨?_, ?_⟩ <;> push_cast <;>
      [exact mul_le_mul_of_nonneg_left hx.1 hq'; exact mul_le_mul_of_nonneg_left hx.2 hq']
  · rename_i hq
    have hq' : (q : ℝ) ≤ 0 := by
      rw [not_le] at hq
      exact_mod_cast hq.le
    refine ⟨?_, ?_⟩ <;> push_cast <;>
      [exact mul_le_mul_of_nonpos_left hx.2 hq'; exact mul_le_mul_of_nonpos_left hx.1 hq']

/-- **One factor of the four-corner bound.**  For `a ≤ x ≤ b` and any real `c`, the product `x * c`
lies between the two corner products, whichever way the sign of `c` orders them. -/
private theorem mul_mem_right {a b x c : ℝ} (h1 : a ≤ x) (h2 : x ≤ b) :
    min (a * c) (b * c) ≤ x * c ∧ x * c ≤ max (a * c) (b * c) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right h1 hc),
      le_trans (mul_le_mul_of_nonneg_right h2 hc) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right h2 hc),
      le_trans (mul_le_mul_of_nonpos_right h1 hc) (le_max_left _ _)⟩

/-- The same bound with the fixed factor on the left, which is the shape the second half of
`mem_mul` needs. -/
private theorem mul_mem_left {a b y c : ℝ} (h1 : a ≤ y) (h2 : y ≤ b) :
    min (c * a) (c * b) ≤ c * y ∧ c * y ≤ max (c * a) (c * b) := by
  obtain ⟨h3, h4⟩ := mul_mem_right (c := c) h1 h2
  rw [mul_comm c a, mul_comm c b, mul_comm c y]
  exact ⟨h3, h4⟩

theorem mem_mul {I J : RatItv} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) : (I.mul J).Mem (x * y) := by
  obtain ⟨hlo, hhi⟩ := mul_mem_right (c := y) hx.1 hx.2
  obtain ⟨hclo, hchi⟩ := mul_mem_left (c := (I.lo : ℝ)) hy.1 hy.2
  obtain ⟨hdlo, hdhi⟩ := mul_mem_left (c := (I.hi : ℝ)) hy.1 hy.2
  refine ⟨?_, ?_⟩ <;> rw [mul] <;> push_cast
  · exact le_trans (min_le_min hclo hdlo) hlo
  · exact le_trans hhi (max_le_max hchi hdhi)

/-- **What a leaf check pays for a non-constant monomial.**  A member of an interval is at most
`absmax` in absolute value. -/
theorem abs_le_absmax {I : RatItv} {x : ℝ} (hx : I.Mem x) : |x| ≤ ((I.absmax : ℚ) : ℝ) := by
  rw [absmax]
  push_cast
  refine abs_le.2 ⟨?_, ?_⟩
  · refine le_trans ?_ hx.1
    rw [neg_le]
    exact le_trans (neg_le_abs _) (le_max_left _ _)
  · exact le_trans hx.2 (le_trans (le_abs_self _) (le_max_right _ _))

/-- The lower end of an interval bounds its members below, in the form a leaf check reads. -/
theorem lo_le {I : RatItv} {x : ℝ} (hx : I.Mem x) : ((I.lo : ℚ) : ℝ) ≤ x := hx.1

end RatItv

/-! ### The enclosure reader -/

/-- The key by which a fifth-root enclosure is looked up: the numerator, the denominator and the
exponent, all compared as numerals so that no rational division is performed. -/
def encKey (x : ℚ) (e : ℤ) (c : FifthEnc) : Bool :=
  c.num == x.num.toNat && c.den == x.den && c.exp == e

/-- **The enclosure reader.**  The interval of `x ^ (e/5)` for a positive rational `x`, read out of
the table `L` by `encKey`, and computed on the spot when the table does not carry it. -/
def encItv (L : List FifthEnc) (x : ℚ) (e : ℤ) : RatItv :=
  match L.find? (encKey x e) with
  | some c => ⟨c.loQ 12, c.hiQ 12⟩
  | none => ⟨(rpowFifthEnc x e 12).1, (rpowFifthEnc x e 12).2⟩

/-- A row whose key matches a positive rational has that rational as its base. -/
private
theorem base_eq_of_encKey {x : ℚ} (hx : 0 < x) {e : ℤ} {c : FifthEnc} (h : encKey x e c = true) :
    c.base = x ∧ 0 < c.num ∧ 0 < c.den ∧ c.exp = e := by
  simp only [encKey, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hnum, hden⟩, hexp⟩ := h
  have hpos : 0 < x.num := Rat.num_pos.2 hx
  have hcast : ((x.num.toNat : ℕ) : ℚ) = (x.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg hpos.le
  refine ⟨?_, ?_, ?_, hexp⟩
  · rw [FifthEnc.base, hnum, hden, hcast]
    exact Rat.num_div_den x
  · rw [hnum]
    omega
  · rw [hden]
    exact x.pos

/-- **The enclosure reader always brackets the power.**  When the table carries the key this is the
table's own soundness; when it does not, it is `rpowFifthEnc`'s.  There is no side condition beyond
positivity of the base, which is what lets a fold of a hundred thousand terms carry no proof
obligation per term. -/
theorem encItv_mem {L : List FifthEnc} (hL : L.all (fun c => c.check 12) = true) {x : ℚ}
    (hx : 0 < x) (e : ℤ) : (encItv L x e).Mem ((x : ℝ) ^ ((e : ℝ) / 5)) := by
  rw [encItv]
  split
  · rename_i c hc
    obtain ⟨hbase, hnum, hden, hexp⟩ := base_eq_of_encKey hx (List.find?_some hc)
    have hs := FifthEnc.sound_of_all hL (List.mem_of_find?_eq_some hc) hnum hden
    rw [hbase, hexp] at hs
    exact hs
  · exact ⟨rpowFifthEnc_le hx e 12, le_rpowFifthEnc hx e 12⟩

end CenteredMaximal.Fractional

end
