/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.SplineGenerator

/-!
# The barycentric certificate algebra of the majorization certificate

The majorization certificate of the `α = 6/5` comparison kernel bounds a piecewise polynomial
below on a triangle, and it does so by the **Bernstein test**: a polynomial written in the
barycentric monomials `λ₀^a λ₁^b λ₂^c` of a triangle with *nonnegative* coefficients is
nonnegative wherever the three barycentric coordinates are, because every monomial is.  This file
carries the sparse polynomial algebra the test needs and the two facts about the cardinal cubic
B-spline that turn the spline part of the kernel into such a polynomial.

Nothing here is specific to the certificate: the file is a general-purpose, kernel-reducible
`ℚ`-coefficient polynomial arithmetic in three variables, together with its evaluation
homomorphism into `ℝ`.

## Main results

* `Poly3`, `eval3`: a polynomial as an association list from exponent triples to rational
  coefficients, and its real evaluation.  Duplicate exponents are allowed in a raw list — the
  evaluation is just the sum of the terms — and `insert3` merges them.
* `eval3_add3`, `eval3_mul3`, `eval3_smul3`, `eval3_pow3`: **`eval3` is a ring homomorphism** in
  the sense that it turns the list operations into the corresponding real ones.  No normal form
  and no sortedness is needed for this: `insert3` merges an exponent wherever it occurs.
* `eval3_nonneg`: **the Bernstein test.**  Nonnegative coefficients and nonnegative variables give
  a nonnegative value.
* `bspline_neg`: `β` is even.  The five truncated cubes of the defining alternating sum are *not*
  individually even, so the proof runs through `truncCube_neg` and the vanishing of the fourth
  difference of a cubic.
* `bspline_intAdd`: **the cell form of the B-spline.**  For `0 ≤ s ≤ 1` and an integer `d`,
  `β (d + s)` is the cubic `pieceVal d s`, whose four coefficients `betaCoef d ·` are the local
  polynomial pieces of `β` — and are zero unless `-2 ≤ d ≤ 1`, which is the locality that reduces
  the `1201` cells of the certificate to the `16` that meet a given cell.
-/

@[expose] public section

namespace CenteredMaximal.Fractional

/-! ### Sparse polynomials in three variables -/

/-- An exponent triple `(a, b, c)` standing for the monomial `λ₀^a λ₁^b λ₂^c`. -/
abbrev Exp3 := ℕ × ℕ × ℕ

/-- A polynomial in three variables as a list of (exponent triple, rational coefficient) pairs.
Repeated exponents are allowed; the value is the sum of the listed terms. -/
abbrev Poly3 := List (Exp3 × ℚ)

/-- The real value of one monomial. -/
def mono3 (e : Exp3) (w x y : ℝ) : ℝ := w ^ e.1 * x ^ e.2.1 * y ^ e.2.2

/-- The real value of a polynomial: the sum of its terms, in the order they are listed. -/
def eval3 (p : Poly3) (w x y : ℝ) : ℝ := (p.map fun t => (t.2 : ℝ) * mono3 t.1 w x y).sum

@[simp] theorem eval3_nil (w x y : ℝ) : eval3 [] w x y = 0 := rfl

@[simp] theorem eval3_cons (t : Exp3 × ℚ) (p : Poly3) (w x y : ℝ) :
    eval3 (t :: p) w x y = (t.2 : ℝ) * mono3 t.1 w x y + eval3 p w x y := rfl

theorem eval3_append (p q : Poly3) (w x y : ℝ) :
    eval3 (p ++ q) w x y = eval3 p w x y + eval3 q w x y := by
  simp [eval3, List.sum_append]

/-- Adding one term to a polynomial, merging it into an existing term with the same exponent and
**dropping a coefficient that cancels**.  Keeping the lists free of zero coefficients is what makes
the certificate affordable: a triangle's `s`-form has a zero coefficient at two of its three
vertices, and a zero coefficient dragged through a product of two cubics costs the kernel a
hundred list steps for nothing. -/
def insert3 (t : Exp3 × ℚ) : Poly3 → Poly3
  | [] => if t.2 = 0 then [] else [t]
  | u :: p => if t.1 = u.1 then (if t.2 + u.2 = 0 then p else (t.1, t.2 + u.2) :: p)
              else u :: insert3 t p

/-- **Inserting a term adds its value.** -/
theorem eval3_insert3 (t : Exp3 × ℚ) (p : Poly3) (w x y : ℝ) :
    eval3 (insert3 t p) w x y = (t.2 : ℝ) * mono3 t.1 w x y + eval3 p w x y := by
  induction p with
  | nil =>
      rw [insert3]
      split
      · rename_i h
        rw [h, eval3_nil]
        push_cast
        ring
      · rw [eval3_cons, eval3_nil]
  | cons u p ih =>
      by_cases h : t.1 = u.1
      · rw [insert3, if_pos h]
        split
        · rename_i hz
          rw [eval3_cons, h]
          have hc : ((t.2 : ℚ) : ℝ) + ((u.2 : ℚ) : ℝ) = 0 := by
            rw [← Rat.cast_add, hz, Rat.cast_zero]
          have : ((t.2 : ℚ) : ℝ) * mono3 u.1 w x y + ((u.2 : ℚ) : ℝ) * mono3 u.1 w x y = 0 := by
            rw [← add_mul, hc, zero_mul]
          linarith
        · rw [eval3_cons, eval3_cons, h]
          push_cast
          ring
      · rw [insert3, if_neg h, eval3_cons, ih, eval3_cons]
        ring

/-- The sum of two polynomials, with the terms of the first merged into the second. -/
def add3 (p q : Poly3) : Poly3 := p.foldr insert3 q

/-- **`add3` adds.** -/
theorem eval3_add3 (p q : Poly3) (w x y : ℝ) :
    eval3 (add3 p q) w x y = eval3 p w x y + eval3 q w x y := by
  induction p with
  | nil => simp [add3]
  | cons t p ih => rw [add3, List.foldr_cons, eval3_insert3, ← add3, ih, eval3_cons]; ring

/-- Collecting the repeated exponents of a raw list. -/
def norm3 (p : Poly3) : Poly3 := p.foldr insert3 []

/-- **Normalisation does not change the value.** -/
theorem eval3_norm3 (p : Poly3) (w x y : ℝ) : eval3 (norm3 p) w x y = eval3 p w x y := by
  have : norm3 p = add3 p [] := rfl
  rw [this, eval3_add3, eval3_nil, add_zero]

/-- Scaling a polynomial by a rational. -/
def smul3 (c : ℚ) (p : Poly3) : Poly3 := p.map fun t => (t.1, c * t.2)

/-- **`smul3` scales.** -/
theorem eval3_smul3 (c : ℚ) (p : Poly3) (w x y : ℝ) :
    eval3 (smul3 c p) w x y = (c : ℝ) * eval3 p w x y := by
  induction p with
  | nil => simp [smul3]
  | cons t p ih =>
      rw [smul3, List.map_cons, ← smul3, eval3_cons, eval3_cons, ih]
      push_cast
      ring

/-- The raw (unmerged) product of two polynomials. -/
def rawMul3 (p q : Poly3) : Poly3 :=
  p.flatMap fun t => q.map fun u => ((t.1.1 + u.1.1, t.1.2.1 + u.1.2.1, t.1.2.2 + u.1.2.2),
    t.2 * u.2)

/-- One term times a polynomial. -/
private theorem eval3_termMul (t : Exp3 × ℚ) (q : Poly3) (w x y : ℝ) :
    eval3 (q.map fun u => ((t.1.1 + u.1.1, t.1.2.1 + u.1.2.1, t.1.2.2 + u.1.2.2), t.2 * u.2))
        w x y = (t.2 : ℝ) * mono3 t.1 w x y * eval3 q w x y := by
  induction q with
  | nil => simp [eval3]
  | cons u q ih =>
      rw [List.map_cons, eval3_cons, ih, eval3_cons]
      simp only [mono3, pow_add]
      push_cast
      ring

/-- **The raw product multiplies.** -/
theorem eval3_rawMul3 (p q : Poly3) (w x y : ℝ) :
    eval3 (rawMul3 p q) w x y = eval3 p w x y * eval3 q w x y := by
  induction p with
  | nil => simp [rawMul3, eval3]
  | cons t p ih =>
      rw [rawMul3, List.flatMap_cons, eval3_append, ← rawMul3, ih, eval3_termMul, eval3_cons]
      ring

/-- The product of two polynomials, with repeated exponents collected. -/
def mul3 (p q : Poly3) : Poly3 := norm3 (rawMul3 p q)

/-- **`mul3` multiplies.** -/
theorem eval3_mul3 (p q : Poly3) (w x y : ℝ) :
    eval3 (mul3 p q) w x y = eval3 p w x y * eval3 q w x y := by
  rw [mul3, eval3_norm3, eval3_rawMul3]

/-- The constant polynomial `1`. -/
def one3 : Poly3 := [((0, 0, 0), (1 : ℚ))]

@[simp] theorem eval3_one3 (w x y : ℝ) : eval3 one3 w x y = 1 := by
  simp [one3, eval3, mono3]

/-- Powers of a polynomial. -/
def pow3 (p : Poly3) : ℕ → Poly3
  | 0 => one3
  | n + 1 => mul3 (pow3 p n) p

/-- **`pow3` takes powers.** -/
theorem eval3_pow3 (p : Poly3) (n : ℕ) (w x y : ℝ) :
    eval3 (pow3 p n) w x y = eval3 p w x y ^ n := by
  induction n with
  | zero => simp [pow3]
  | succ n ih => rw [pow3, eval3_mul3, ih, pow_succ]

/-! ### The Bernstein test -/

/-- **A polynomial with nonnegative coefficients is nonnegative on the nonnegative octant.**
This is the whole content of the Bernstein test: on a triangle the barycentric coordinates are
nonnegative, so every barycentric monomial is. -/
theorem eval3_nonneg {p : Poly3} (hp : ∀ t ∈ p, 0 ≤ t.2) {w x y : ℝ} (hw : 0 ≤ w) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : 0 ≤ eval3 p w x y := by
  refine List.sum_nonneg ?_
  intro a ha
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 ha
  have h2 : (0 : ℝ) ≤ (t.2 : ℚ) := by exact_mod_cast hp t ht
  have : (0 : ℝ) ≤ mono3 t.1 w x y := by
    refine mul_nonneg (mul_nonneg (pow_nonneg hw _) (pow_nonneg hx _)) (pow_nonneg hy _)
  exact mul_nonneg h2 this

/-- The `List.all` form of the coefficient test, which is what a kernel check produces. -/
theorem eval3_nonneg_of_all {p : Poly3} (hp : p.all (fun t => 0 ≤ t.2) = true) {w x y : ℝ}
    (hw : 0 ≤ w) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ eval3 p w x y :=
  eval3_nonneg (fun t ht => of_decide_eq_true (List.all_eq_true.1 hp t ht)) hw hx hy

/-! ### The truncated cube and the evenness of the B-spline -/

/-- `(−x)₊³ = x₊³ − x³`: the two truncated cubes differ by the cube itself. -/
theorem truncCube_neg (x : ℝ) : truncCube (-x) = truncCube x - x ^ 3 := by
  rcases le_total x 0 with h | h
  · rw [truncCube_of_nonneg (by linarith : (0 : ℝ) ≤ -x), truncCube_of_nonpos h]
    ring
  · rw [truncCube_of_nonpos (by linarith : -x ≤ 0), truncCube_of_nonneg h]
    ring

/-- The defining alternating sum of the cardinal cubic B-spline, written out. -/
theorem bspline_eq_five (x : ℝ) :
    bspline x = 1 / 6 * (truncCube (x + 2) - 4 * truncCube (x + 1) + 6 * truncCube x
      - 4 * truncCube (x - 1) + truncCube (x - 2)) := by
  rw [bspline, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  norm_num [Nat.choose]
  ring_nf

/-- **The cardinal cubic B-spline is even.**  Its five truncated cubes are not individually even;
what makes the sum even is `truncCube_neg` together with the vanishing of the fourth difference
`(x−2)³ − 4(x−1)³ + 6x³ − 4(x+1)³ + (x+2)³` of a cubic. -/
theorem bspline_neg (x : ℝ) : bspline (-x) = bspline x := by
  rw [bspline_eq_five, bspline_eq_five]
  rw [show -x + 2 = -(x - 2) from by ring, show -x + 1 = -(x - 1) from by ring,
    show -x - 1 = -(x + 1) from by ring, show -x - 2 = -(x + 2) from by ring,
    truncCube_neg (x - 2), truncCube_neg (x - 1), truncCube_neg x, truncCube_neg (x + 1),
    truncCube_neg (x + 2)]
  ring

/-! ### The cell form of the B-spline -/

/-- The four coefficients of the local cubic piece of `β` on the cell at integer offset `d`:
`β (d + s) = ∑ᵢ betaCoef d i · sⁱ` for `0 ≤ s ≤ 1`.  They vanish unless `−2 ≤ d ≤ 1`. -/
def betaCoef (d : ℤ) (i : ℕ) : ℚ :=
  if d = -2 then (if i = 3 then 1 / 6 else 0)
  else if d = -1 then
    (if i = 0 then 1 / 6 else if i = 1 then 1 / 2 else if i = 2 then 1 / 2
      else if i = 3 then -(1 / 2) else 0)
  else if d = 0 then
    (if i = 0 then 2 / 3 else if i = 2 then -1 else if i = 3 then 1 / 2 else 0)
  else if d = 1 then
    (if i = 0 then 1 / 6 else if i = 1 then -(1 / 2) else if i = 2 then 1 / 2
      else if i = 3 then -(1 / 6) else 0)
  else 0

/-- The local cubic piece of `β` on the cell at integer offset `d`. -/
def pieceVal (d : ℤ) (s : ℝ) : ℝ :=
  (betaCoef d 0 : ℝ) + (betaCoef d 1 : ℝ) * s + (betaCoef d 2 : ℝ) * s ^ 2
    + (betaCoef d 3 : ℝ) * s ^ 3

/-- Outside the four supported offsets the local piece is zero. -/
theorem pieceVal_of_lt {d : ℤ} (h : d < -2) (s : ℝ) : pieceVal d s = 0 := by
  have h1 : d ≠ -2 := by omega
  have h2 : d ≠ -1 := by omega
  have h3 : d ≠ 0 := by omega
  have h4 : d ≠ 1 := by omega
  simp [pieceVal, betaCoef, h1, h2, h3, h4]

theorem pieceVal_of_gt {d : ℤ} (h : 1 < d) (s : ℝ) : pieceVal d s = 0 := by
  have h1 : d ≠ -2 := by omega
  have h2 : d ≠ -1 := by omega
  have h3 : d ≠ 0 := by omega
  have h4 : d ≠ 1 := by omega
  simp [pieceVal, betaCoef, h1, h2, h3, h4]

/-- **The cell form of the B-spline.**  On the unit cell the shifted B-spline is the explicit
cubic `pieceVal`, and it vanishes unless the shift `d` lies in `{−2, −1, 0, 1}`. -/
theorem bspline_intAdd (d : ℤ) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    bspline ((d : ℝ) + s) = pieceVal d s := by
  rcases lt_trichotomy d (-2) with hlt | heq | hgt
  · have hd : (d : ℝ) ≤ -3 := by exact_mod_cast (by omega : d ≤ -3)
    rw [bspline_of_le_neg_two (by linarith), pieceVal_of_lt hlt]
  · subst heq
    rw [bspline_eq_five]
    have e1 : ((-2 : ℤ) : ℝ) + s + 2 = s := by push_cast; ring
    have e2 : ((-2 : ℤ) : ℝ) + s + 1 = s - 1 := by push_cast; ring
    have e3 : ((-2 : ℤ) : ℝ) + s = s - 2 := by push_cast; ring
    have e4 : ((-2 : ℤ) : ℝ) + s - 1 = s - 3 := by push_cast; ring
    have e5 : ((-2 : ℤ) : ℝ) + s - 2 = s - 4 := by push_cast; ring
    rw [e1, e2, e4, e5, e3, truncCube_of_nonneg hs,
      truncCube_of_nonpos (by linarith : s - 1 ≤ 0), truncCube_of_nonpos (by linarith : s - 2 ≤ 0),
      truncCube_of_nonpos (by linarith : s - 3 ≤ 0), truncCube_of_nonpos (by linarith : s - 4 ≤ 0)]
    simp only [pieceVal, betaCoef]
    norm_num
    try ring
  · rcases lt_trichotomy d (-1) with hlt2 | heq2 | hgt2
    · omega
    · subst heq2
      rw [bspline_eq_five]
      have e1 : ((-1 : ℤ) : ℝ) + s + 2 = s + 1 := by push_cast; ring
      have e2 : ((-1 : ℤ) : ℝ) + s + 1 = s := by push_cast; ring
      have e3 : ((-1 : ℤ) : ℝ) + s = s - 1 := by push_cast; ring
      have e4 : ((-1 : ℤ) : ℝ) + s - 1 = s - 2 := by push_cast; ring
      have e5 : ((-1 : ℤ) : ℝ) + s - 2 = s - 3 := by push_cast; ring
      rw [e1, e2, e4, e5, e3, truncCube_of_nonneg (by linarith : (0 : ℝ) ≤ s + 1),
        truncCube_of_nonneg hs, truncCube_of_nonpos (by linarith : s - 1 ≤ 0),
        truncCube_of_nonpos (by linarith : s - 2 ≤ 0),
        truncCube_of_nonpos (by linarith : s - 3 ≤ 0)]
      simp only [pieceVal, betaCoef]
      norm_num
      try ring
    · rcases lt_trichotomy d 0 with hlt3 | heq3 | hgt3
      · omega
      · subst heq3
        rw [bspline_eq_five]
        have e1 : ((0 : ℤ) : ℝ) + s + 2 = s + 2 := by push_cast; ring
        have e2 : ((0 : ℤ) : ℝ) + s + 1 = s + 1 := by push_cast; ring
        have e3 : ((0 : ℤ) : ℝ) + s = s := by push_cast; ring
        have e4 : ((0 : ℤ) : ℝ) + s - 1 = s - 1 := by push_cast; ring
        have e5 : ((0 : ℤ) : ℝ) + s - 2 = s - 2 := by push_cast; ring
        rw [e1, e2, e4, e5, e3, truncCube_of_nonneg (by linarith : (0 : ℝ) ≤ s + 2),
          truncCube_of_nonneg (by linarith : (0 : ℝ) ≤ s + 1), truncCube_of_nonneg hs,
          truncCube_of_nonpos (by linarith : s - 1 ≤ 0),
          truncCube_of_nonpos (by linarith : s - 2 ≤ 0)]
        simp only [pieceVal, betaCoef]
        norm_num
        try ring
      · rcases lt_trichotomy d 1 with hlt4 | heq4 | hgt4
        · omega
        · subst heq4
          rw [bspline_eq_five]
          have e1 : ((1 : ℤ) : ℝ) + s + 2 = s + 3 := by push_cast; ring
          have e2 : ((1 : ℤ) : ℝ) + s + 1 = s + 2 := by push_cast; ring
          have e3 : ((1 : ℤ) : ℝ) + s = s + 1 := by push_cast; ring
          have e4 : ((1 : ℤ) : ℝ) + s - 1 = s := by push_cast; ring
          have e5 : ((1 : ℤ) : ℝ) + s - 2 = s - 1 := by push_cast; ring
          rw [e1, e2, e4, e5, e3, truncCube_of_nonneg (by linarith : (0 : ℝ) ≤ s + 3),
            truncCube_of_nonneg (by linarith : (0 : ℝ) ≤ s + 2),
            truncCube_of_nonneg (by linarith : (0 : ℝ) ≤ s + 1), truncCube_of_nonneg hs,
            truncCube_of_nonpos (by linarith : s - 1 ≤ 0)]
          simp only [pieceVal, betaCoef]
          norm_num
          try ring
        · have hd : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : (2 : ℤ) ≤ d)
          rw [bspline_of_two_le (by linarith), pieceVal_of_gt hgt4]

end CenteredMaximal.Fractional

end
