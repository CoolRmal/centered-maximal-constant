/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.RatPow

/-!
# Two-sided fifth-root enclosure rows

`CenteredMaximal.Fractional.FifthClaim` records a *one-sided* claim: a rational upper bound for
`x ^ (p/5)`.  The `α = 6/5` generator certificate needs both ends of the enclosure of every one of
its fifth-power-exponent numbers, because each of them is multiplied by a spline coefficient whose
sign is not known in advance.  Storing two independent rows per number would double the cost of the
table, since each row's `check` runs one integer fifth root, by far the most expensive step.

This file records instead **one row per number**, holding only the digit string of the *lower* end.
The upper end costs nothing: by `rpowFifthEnc_snd_eq` the two ends of `rpowFifthEnc` always differ
by exactly `10 ^ (-prec)`, so a row that pins the lower end pins the upper end too, and `check`
performs a single fifth root.

## Main results

* `FifthEnc`: one row, four natural/integer numerals — `num`, `den`, `exp`, `dig`.
* `rpowFifthEnc_snd_eq`: the two ends of an enclosure differ by `10 ^ (-prec)`.
* `FifthEnc.check`, `FifthEnc.check_sound`: the single kernel check and what it buys, namely
  `dig / 10 ^ prec ≤ (num/den) ^ (exp/5) ≤ (dig + 1) / 10 ^ prec` as an inequality of **reals**.
* `FifthEnc.sound_of_all`: the form in which a shard's `List.all` check is consumed.

## Why a structure

Certificate data must be anonymous constructors of a structure, never bare numeral tuples: with
tuples every numeral's `OfNat` problem is postponed and the elaborator's queue grows quadratically,
which costs `104 s` for `2000` rows against `1.8 s` for the same rows as a structure.  The
measurement is recorded in `CenteredMaximal.Fractional.RatPow`.
-/

@[expose] public section

namespace CenteredMaximal.Fractional

/-! ### The two ends of an enclosure differ by one digit -/

/-- **The upper end of `fifthEnc` is the lower end plus one unit in the last place.** -/
theorem fifthEnc_snd_eq (y : ℚ) (prec : ℕ) :
    (fifthEnc y prec).2 = (fifthEnc y prec).1 + 1 / 10 ^ prec := by
  simp only [fifthEnc]
  rw [add_div]

/-- **The upper end of `rpowFifthEnc` is the lower end plus one unit in the last place.** Both
branches of the definition are a `fifthEnc`, so this is `fifthEnc_snd_eq` twice. -/
theorem rpowFifthEnc_snd_eq (x : ℚ) (p : ℤ) (prec : ℕ) :
    (rpowFifthEnc x p prec).2 = (rpowFifthEnc x p prec).1 + 1 / 10 ^ prec := by
  simp only [rpowFifthEnc]
  split <;> exact fifthEnc_snd_eq _ _

/-! ### One row of the table -/

/-- One row of the two-sided fifth-root table: the claim that the enclosure of
`(num / den) ^ (exp / 5)` computed at the table's precision has lower end exactly
`dig / 10 ^ prec`, and hence upper end `(dig + 1) / 10 ^ prec`. -/
structure FifthEnc where
  /-- Numerator of the rational base. -/
  num : ℕ
  /-- Denominator of the rational base. -/
  den : ℕ
  /-- Numerator of the exponent, whose denominator is five. -/
  exp : ℤ
  /-- The digit string of the lower end of the enclosure, over `10 ^ prec`. -/
  dig : ℕ

namespace FifthEnc

/-- The base of a row as a rational. -/
def base (c : FifthEnc) : ℚ := (c.num : ℚ) / (c.den : ℚ)

/-- The lower end of the row's enclosure, at precision `prec`. -/
def loQ (c : FifthEnc) (prec : ℕ) : ℚ := (c.dig : ℚ) / 10 ^ prec

/-- The upper end of the row's enclosure, at precision `prec`. -/
def hiQ (c : FifthEnc) (prec : ℕ) : ℚ := ((c.dig : ℚ) + 1) / 10 ^ prec

/-- **The single kernel check for one row.**  Only the *first* component of the enclosure is
forced, so exactly one integer fifth root is computed. -/
def check (c : FifthEnc) (prec : ℕ) : Bool :=
  decide ((rpowFifthEnc c.base c.exp prec).1 = c.loQ prec)

/-- A row with positive numerator and denominator has positive base. -/
theorem base_pos {c : FifthEnc} (h1 : 0 < c.num) (h2 : 0 < c.den) : 0 < c.base := by
  refine div_pos ?_ ?_ <;> exact_mod_cast ‹_›

/-- **Soundness of one row.**  A check that passes brackets the *real* number
`base ^ (exp / 5)` between the row's two rational ends.  The lower half is
`rpowFifthEnc_le`; the upper half is `le_rpowFifthEnc` followed by
`rpowFifthEnc_snd_eq`, which is what makes the second end free. -/
theorem check_sound {c : FifthEnc} {prec : ℕ} (hc : c.check prec = true) (hb : 0 < c.base) :
    ((c.loQ prec : ℚ) : ℝ) ≤ (c.base : ℝ) ^ ((c.exp : ℝ) / 5) ∧
      (c.base : ℝ) ^ ((c.exp : ℝ) / 5) ≤ ((c.hiQ prec : ℚ) : ℝ) := by
  have hlo : (rpowFifthEnc c.base c.exp prec).1 = c.loQ prec := of_decide_eq_true hc
  refine ⟨?_, ?_⟩
  · have := rpowFifthEnc_le hb c.exp prec
    rwa [hlo] at this
  · have := le_rpowFifthEnc hb c.exp prec
    rw [rpowFifthEnc_snd_eq, hlo] at this
    refine this.trans_eq ?_
    have : c.loQ prec + 1 / 10 ^ prec = c.hiQ prec := by
      rw [loQ, hiQ, add_div]
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) this

/-- **Soundness of a shard.**  A `List.all` check over a shard bounds every row of it. -/
theorem sound_of_all {l : List FifthEnc} {prec : ℕ} (hl : l.all (fun c => c.check prec) = true)
    {c : FifthEnc} (hc : c ∈ l) (h1 : 0 < c.num) (h2 : 0 < c.den) :
    ((c.loQ prec : ℚ) : ℝ) ≤ (c.base : ℝ) ^ ((c.exp : ℝ) / 5) ∧
      (c.base : ℝ) ^ ((c.exp : ℝ) / 5) ≤ ((c.hiQ prec : ℚ) : ℝ) :=
  check_sound (List.all_eq_true.mp hl c hc) (base_pos h1 h2)

end FifthEnc

end CenteredMaximal.Fractional

end
