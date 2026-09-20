/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Nat.Log
public import Mathlib.Tactic.NormNum.Basic

/-!
# Integer fifth roots

The `α = 6/5` certificate has to bound thousands of real numbers of the shape `|x| ^ (9/5)` and
`r ^ (-12/5)` for *rational* `x` and `r`, i.e. fifth roots of rationals.  Every such bound is
ultimately an integer comparison `q ^ 5 ≤ N`, and the enclosing rational `q` is produced by an
*integer fifth root*.  This file provides that root as a computable function which the **kernel**
can evaluate, because `decide` — not `#eval` — is what discharges a certificate.

## Design

`iroot5` is a descending-bit binary search: it inspects the bit weights
`2 ^ (K - 1), …, 2 ^ 1, 2 ^ 0` in turn, keeping the partial root `r` for which `r ^ 5 ≤ n`, so it
costs `K` fifth powers of numbers no larger than `n`.  The number of rounds `K` is
`bitLen n / 5 + 1`, where `bitLen` counts binary digits by repeated halving.  Both loops are
*structural* recursions on a `Nat` that decreases by one: the kernel unfolds them one step at a
time and every arithmetic step (`/ 2`, `+ 1`, `^ 5`, `≤`) is GMP-accelerated, so a `60`-digit
argument costs a few hundred cheap big-integer operations.  Nothing here uses well-founded
recursion, which the kernel cannot unfold at all.

## Main results

* `iroot5`: the integer fifth root, kernel-computable.
* `iroot5_le`: `iroot5 n ^ 5 ≤ n`.
* `lt_iroot5_succ`: `n < (iroot5 n + 1) ^ 5`.
* `iroot5_eq_of`: the two bounds characterise `iroot5 n`, which identifies it with the greatest
  `r` satisfying `r ^ 5 ≤ n`.
-/

@[expose] public section

namespace CenteredMaximal.Fractional

/-! ### Bit length -/

/-- `bitLenAux fuel m` halves `m`, counting the halvings, at most `fuel` times.  As soon as
`fuel` is at least `m` the cap is never reached and the result is the number of binary digits
of `m`; this is the only regime `lt_two_pow_bitLenAux` speaks about.  The recursion is
structural in `fuel`, which decreases by one per step, so the kernel unfolds it lazily. -/
def bitLenAux : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m => if m = 0 then 0 else bitLenAux fuel (m / 2) + 1

@[simp] theorem bitLenAux_zero (m : ℕ) : bitLenAux 0 m = 0 := rfl

theorem bitLenAux_succ (fuel m : ℕ) :
    bitLenAux (fuel + 1) m = if m = 0 then 0 else bitLenAux fuel (m / 2) + 1 := rfl

/-- **The only property of `bitLenAux` that matters**: given enough fuel it produces an exponent
that dominates its argument.  Induction on the fuel; the step uses `m / 2 ≤ fuel`, which holds
because `m ≤ fuel + 1` and `m ≠ 0`. -/
theorem lt_two_pow_bitLenAux : ∀ fuel m : ℕ, m ≤ fuel → m < 2 ^ bitLenAux fuel m := by
  intro fuel
  induction fuel with
  | zero => intro m hm; simp [Nat.le_zero.mp hm]
  | succ fuel ih =>
    intro m hm
    rw [bitLenAux_succ]
    by_cases h : m = 0
    · simp [h]
    · have h2 : m / 2 < 2 ^ bitLenAux fuel (m / 2) := ih _ (by omega)
      rw [if_neg h, pow_succ]
      omega

/-- The number of binary digits of `m`: running `bitLenAux` with `m` itself as the fuel always
has enough fuel, since `m` needs at most `m` halvings. -/
def bitLen (m : ℕ) : ℕ := bitLenAux m m

/-- `m < 2 ^ bitLen m`: the budget `bitLen` hands to the binary search is large enough. -/
theorem lt_two_pow_bitLen (m : ℕ) : m < 2 ^ bitLen m :=
  lt_two_pow_bitLenAux m m le_rfl

/-! ### The descending-bit search -/

/-- `iroot5Go n k r` refines the partial root `r` using the bit weights `2 ^ (k-1), …, 2 ^ 0`,
adding each weight exactly when the result still has fifth power at most `n`.  Structural in
`k`. -/
def iroot5Go (n : ℕ) : ℕ → ℕ → ℕ
  | 0, r => r
  | k + 1, r => iroot5Go n k (if (r + 2 ^ k) ^ 5 ≤ n then r + 2 ^ k else r)

theorem iroot5Go_zero (n r : ℕ) : iroot5Go n 0 r = r := rfl

theorem iroot5Go_succ (n k r : ℕ) :
    iroot5Go n (k + 1) r = iroot5Go n k (if (r + 2 ^ k) ^ 5 ≤ n then r + 2 ^ k else r) := rfl

/-- **The loop invariant**: `r ^ 5 ≤ n < (r + 2 ^ k) ^ 5` is preserved with `k` decremented, and
at `k = 0` it *is* the specification of the integer fifth root.  Adding the weight `2 ^ k` turns
`n < (r + 2 ^ (k+1)) ^ 5` into `n < (r + 2 ^ k + 2 ^ k) ^ 5`; declining it keeps `r` and uses the
failed test as the new upper bound. -/
theorem iroot5Go_spec (n : ℕ) : ∀ k r : ℕ, r ^ 5 ≤ n → n < (r + 2 ^ k) ^ 5 →
    iroot5Go n k r ^ 5 ≤ n ∧ n < (iroot5Go n k r + 1) ^ 5 := by
  intro k
  induction k with
  | zero =>
    intro r h1 h2
    rw [pow_zero] at h2
    exact ⟨h1, h2⟩
  | succ k ih =>
    intro r h1 h2
    rw [iroot5Go_succ]
    by_cases h : (r + 2 ^ k) ^ 5 ≤ n
    · rw [if_pos h]
      refine ih _ h ?_
      have hw : r + 2 ^ k + 2 ^ k = r + 2 ^ (k + 1) := by rw [pow_succ]; omega
      rw [hw]
      exact h2
    · rw [if_neg h]
      exact ih _ h1 (Nat.lt_of_not_le h)

/-! ### The integer fifth root -/

/-- **The integer fifth root**: the greatest `r` with `r ^ 5 ≤ n`.  A fifth root has about a
fifth of the binary digits of its argument, so `bitLen n / 5 + 1` rounds of the descending-bit
search suffice. -/
def iroot5 (n : ℕ) : ℕ := iroot5Go n (bitLen n / 5 + 1) 0

/-- **The defining two-sided bound** on `iroot5`. -/
theorem iroot5_spec (n : ℕ) : iroot5 n ^ 5 ≤ n ∧ n < (iroot5 n + 1) ^ 5 := by
  refine iroot5Go_spec n _ 0 (by simp) ?_
  have hb : bitLen n ≤ (bitLen n / 5 + 1) * 5 := by omega
  calc n < 2 ^ bitLen n := lt_two_pow_bitLen n
    _ ≤ 2 ^ ((bitLen n / 5 + 1) * 5) := Nat.pow_le_pow_right (by omega) hb
    _ = (0 + 2 ^ (bitLen n / 5 + 1)) ^ 5 := by rw [zero_add, pow_mul]

/-- **The lower half of the specification**: `iroot5 n` really is a fifth root from below. -/
theorem iroot5_le {n : ℕ} : iroot5 n ^ 5 ≤ n := (iroot5_spec n).1

/-- **The upper half of the specification**: the next integer overshoots. -/
theorem lt_iroot5_succ {n : ℕ} : n < (iroot5 n + 1) ^ 5 := (iroot5_spec n).2

/-- `iroot5` is *the* greatest `r` with `r ^ 5 ≤ n`: any `r` with `r ^ 5 ≤ n < (r + 1) ^ 5`
equals it.  Useful for rewriting a computed root into a closed form. -/
theorem iroot5_eq_of {n r : ℕ} (h1 : r ^ 5 ≤ n) (h2 : n < (r + 1) ^ 5) : iroot5 n = r := by
  by_contra hne
  rcases Nat.lt_or_ge (iroot5 n) r with h | h
  · exact absurd ((Nat.pow_le_pow_left h 5).trans h1) (Nat.not_le.mpr lt_iroot5_succ)
  · have hr : r + 1 ≤ iroot5 n := by omega
    exact absurd ((Nat.pow_le_pow_left hr 5).trans iroot5_le) (Nat.not_le.mpr h2)

end CenteredMaximal.Fractional

end
