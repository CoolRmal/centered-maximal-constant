/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.FifthEnclosure
public import CenteredMaximal.Fractional.MajorCell

/-!
# One row of the majorization certificate

A row of the majorization certificate is a triangle inside one cell of the spline grid, together
with the radius at which the base's tangent minorant is taken.  This file defines the row, the
`Poly3` it produces, the single kernel check it has to pass, and — the point of the file — what a
passing row buys: a pointwise lower bound on `fracKernel` over the whole triangle.

## The row

A row `⟨k, l, tgt, ext, mq, s₀, s₁, s₂, t₀, t₁, t₂⟩` asserts `tgt ≤ K` on the triangle of the cell
`(k, l)` whose three vertices are `(sᵢ, tᵢ)` in the local coordinates `s = 16 z₀ - k`,
`t = 16 z₁ - l`.  The tangent radius is `q = mq / 64`, and `ext` is a degree elevation, used only
on the one cell whose unit triangles the degree-`6` Bernstein test cannot certify.

The two rational enclosures of `q ^ (-6/5)` and `q ^ (-11/5)` are *not* stored on the row: they are
read out of `majEncTable` by the radius, because the `814` rows use only `34` distinct radii.  A
radius missing from the table makes `majLo` return `0`, which is still a valid lower bound for a
positive power — so `majLo_le` needs no side condition, and a row simply fails its Bernstein check
if a radius is missing.

## Main results

* `majEncTable`, `majEncTable_ok`, `majLo_le`: the `60` fifth-root enclosures, verified by one
  kernel reduction, and the lower bound they buy.
* `majRUp_sound`: the one *upper* enclosure the certificate needs, `(7/4) ^ (-6/5) ≤ majRUpQ`.
* `homT`, `Rows4.hom`: the barycentric rewriting of a bicubic, as **four** products of cubics.
* `MajRow.poly`, `MajRow.check`: the barycentric polynomial of a row and its Bernstein test.
* `eval3_MajRow_poly`: **the barycentric identity**, that the row's polynomial evaluated at the
  barycentric coordinates of a point of the triangle is the cell bicubic plus the affine base
  minorant, minus the target.
* `MajRow.sound`: **what a passing row buys.**  `tgt ≤ fracKernel z` for every `z ≠ 0` whose folded
  coordinates lie in the row's triangle.
-/

@[expose] public section

noncomputable section

open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### The fifth-root enclosures of the radii -/

/-- The `68` fifth-root enclosures the majorization certificate reads: for each of the `34` radii
`q = mq / 64` that occur, the lower ends of `q ^ (-6/5)` and `q ^ (-11/5)` at precision `12`. -/
def majEncTable : List FifthEnc :=
  [⟨4, 64, -6, 27857618025475⟩, ⟨4, 64, -11, 445721888407615⟩, ⟨8, 64, -6, 12125732532083⟩,
   ⟨8, 64, -11, 97005860256665⟩, ⟨12, 64, -6, 7454155933563⟩, ⟨12, 64, -11, 39755498312338⟩,
   ⟨16, 64, -6, 5278031643091⟩, ⟨16, 64, -11, 21112126572366⟩, ⟨20, 64, -6, 4038127004673⟩,
   ⟨20, 64, -11, 12922006414954⟩, ⟨24, 64, -6, 3244609823430⟩, ⟨24, 64, -11, 8652292862481⟩,
   ⟨28, 64, -6, 2696660856486⟩, ⟨28, 64, -11, 6163796243397⟩, ⟨32, 64, -6, 2297396709994⟩,
   ⟨32, 64, -11, 4594793419988⟩, ⟨36, 64, -6, 1994586925237⟩, ⟨36, 64, -11, 3545932311533⟩,
   ⟨40, 64, -6, 1757696869289⟩, ⟨40, 64, -11, 2812314990863⟩, ⟨44, 64, -6, 1567735371218⟩,
   ⟨44, 64, -11, 2280342358136⟩, ⟨48, 64, -6, 1412298454731⟩, ⟨48, 64, -11, 1883064606308⟩,
   ⟨52, 64, -6, 1282956573879⟩, ⟨52, 64, -11, 1579023475544⟩, ⟨56, 64, -6, 1173789813816⟩,
   ⟨56, 64, -11, 1341474072933⟩, ⟨60, 64, -6, 1080524126105⟩, ⟨60, 64, -11, 1152559067846⟩,
   ⟨64, 64, -6, 1000000000000⟩, ⟨64, 64, -11, 1000000000000⟩, ⟨68, 64, -6, 929833681263⟩,
   ⟨68, 64, -11, 875137582365⟩, ⟨72, 64, -6, 868194385654⟩, ⟨72, 64, -11, 771728342803⟩,
   ⟨76, 64, -6, 813653801840⟩, ⟨76, 64, -11, 685182148918⟩, ⟨80, 64, -6, 765081999832⟩,
   ⟨80, 64, -11, 612065599865⟩, ⟨84, 64, -6, 721573915824⟩, ⟨84, 64, -11, 549770602532⟩,
   ⟨88, 64, -6, 682396455256⟩, ⟨88, 64, -11, 496288331095⟩, ⟨89, 64, -6, 673205973342⟩,
   ⟨89, 64, -11, 484103171841⟩, ⟨90, 64, -6, 664239896819⟩, ⟨90, 64, -11, 472348371071⟩,
   ⟨91, 64, -6, 655490343238⟩, ⟨91, 64, -11, 461004197442⟩, ⟨92, 64, -6, 646949789607⟩,
   ⟨92, 64, -11, 450052027552⟩, ⟨93, 64, -6, 638611052313⟩, ⟨93, 64, -11, 439474272559⟩,
   ⟨94, 64, -6, 630467268369⟩, ⟨94, 64, -11, 429254310379⟩, ⟨95, 64, -6, 622511877882⟩,
   ⟨95, 64, -11, 419376422994⟩, ⟨96, 64, -6, 614738607654⟩, ⟨96, 64, -11, 409825738436⟩,
   ⟨100, 64, -6, 585350466466⟩, ⟨100, 64, -11, 374624298538⟩, ⟨104, 64, -6, 558439284037⟩,
   ⟨104, 64, -11, 343654944023⟩, ⟨108, 64, -6, 533712607810⟩, ⟨108, 64, -11, 316274137961⟩,
   ⟨112, 64, -6, 510921691804⟩, ⟨112, 64, -11, 291955252459⟩]

/-- **All `68` enclosures verify.** -/
theorem majEncTable_ok : majEncTable.all (fun c => c.check 12) = true := by decide +kernel

/-- The stored lower end of `(n / 64) ^ (e / 5)`, or `0` when the radius is not tabulated. -/
def majLo (n : ℕ) (e : ℤ) : ℚ :=
  match majEncTable.find? fun c => c.num == n && c.den == 64 && c.exp == e with
  | some c => c.loQ 12
  | none => 0

theorem majLo_nonneg (n : ℕ) (e : ℤ) : 0 ≤ majLo n e := by
  rw [majLo]
  split
  · rename_i c _
    rw [FifthEnc.loQ]
    positivity
  · exact le_refl 0

/-- **The table's lower ends really are lower bounds.**  An untabulated radius gives `0`, which is
below every positive power of a nonnegative number, so there is no side condition beyond `0 < n`. -/
theorem majLo_le {n : ℕ} (hn : 0 < n) (e : ℤ) :
    ((majLo n e : ℚ) : ℝ) ≤ ((n : ℝ) / 64) ^ ((e : ℝ) / 5) := by
  rw [majLo]
  split
  · rename_i c hc
    have hmem : c ∈ majEncTable := List.mem_of_find?_eq_some hc
    have hpred := List.find?_some hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hpred
    obtain ⟨⟨hnum, hden⟩, hexp⟩ := hpred
    have h1 : 0 < c.num := by rw [hnum]; exact hn
    have h2 : 0 < c.den := by rw [hden]; norm_num
    have hs := (FifthEnc.sound_of_all majEncTable_ok hmem h1 h2).1
    rw [hexp] at hs
    refine hs.trans_eq ?_
    rw [FifthEnc.base, hnum, hden]
    push_cast
    ring_nf
  · have : (0 : ℝ) ≤ ((n : ℝ) / 64) ^ ((e : ℝ) / 5) := Real.rpow_nonneg (by positivity) _
    simpa using this

/-- The single *upper* enclosure of `(7/4) ^ (-6/5)` the certificate needs. -/
def majRRow : FifthEnc := ⟨7, 4, -6, 510921691804⟩

theorem majRRow_ok : majRRow.check 12 = true := by decide +kernel

/-- The rational upper bound `0.510921691805` for `(7/4) ^ (-6/5)`. -/
def majRUpQ : ℚ := majRRow.hiQ 12

/-- **`(7/4) ^ (-6/5)` lies below `majRUpQ`.** -/
theorem majRUp_sound : ((7 : ℝ) / 4) ^ ((-6 : ℝ) / 5) ≤ (majRUpQ : ℝ) := by
  have h := (FifthEnc.check_sound majRRow_ok (by rw [FifthEnc.base, majRRow]; norm_num)).2
  rw [majRUpQ]
  refine le_trans (le_of_eq ?_) h
  rw [FifthEnc.base, majRRow]
  norm_num

/-! ### Homogenising a monomial to the barycentric basis -/

/-- The constant `1` written homogeneously, as `λ₀ + λ₁ + λ₂`. -/
def homOne : Poly3 := [((1, 0, 0), (1 : ℚ)), ((0, 1, 0), (1 : ℚ)), ((0, 0, 1), (1 : ℚ))]

theorem eval3_homOne {l0 l1 l2 : ℝ} (h : l0 + l1 + l2 = 1) : eval3 homOne l0 l1 l2 = 1 := by
  simp only [homOne, eval3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mono3,
    pow_zero, pow_one, Rat.cast_one, one_mul, mul_one]
  linarith

/-- `V ^ i` lifted to a homogeneous form of degree `3`. -/
def homDeg3 (V : Poly3) (i : ℕ) : Poly3 := mul3 (pow3 V i) (pow3 homOne (3 - i))

theorem eval3_homDeg3 (V : Poly3) (i : ℕ) {l0 l1 l2 : ℝ} (h : l0 + l1 + l2 = 1) :
    eval3 (homDeg3 V i) l0 l1 l2 = eval3 V l0 l1 l2 ^ i := by
  rw [homDeg3, eval3_mul3, eval3_pow3, eval3_pow3, eval3_homOne h, one_pow, mul_one]

/-- A cubic in `t` written in the barycentric basis, homogeneously of degree `3`. -/
def homT (T g : Poly3) : Poly3 :=
  g.foldr (fun e acc => add3 (smul3 e.2 (homDeg3 T e.1.2.2)) acc) []

theorem eval3_homT (T g : Poly3) {l0 l1 l2 : ℝ} (h : l0 + l1 + l2 = 1) :
    eval3 (homT T g) l0 l1 l2 = eval3 g 1 1 (eval3 T l0 l1 l2) := by
  induction g with
  | nil => simp [homT, eval3]
  | cons e g ih =>
      rw [homT, List.foldr_cons, eval3_add3, ← homT, ih, eval3_smul3, eval3_homDeg3 _ _ h,
        eval3_cons, mono3, one_pow, one_pow, one_mul, one_mul]

/-- **The barycentric rewriting of a bicubic.**  Four products of cubics, one per coefficient
row: `∑ᵢ (Sⁱ O³⁻ⁱ) · homT T gᵢ`. -/
def Rows4.hom (R : Rows4) (S T : Poly3) : Poly3 :=
  add3 (mul3 (homDeg3 S 0) (homT T R.g0))
    (add3 (mul3 (homDeg3 S 1) (homT T R.g1))
      (add3 (mul3 (homDeg3 S 2) (homT T R.g2)) (mul3 (homDeg3 S 3) (homT T R.g3))))

/-- **The barycentric rewriting is value-preserving.** -/
theorem eval3_Rows4_hom (R : Rows4) (S T : Poly3) {l0 l1 l2 : ℝ} (h : l0 + l1 + l2 = 1) :
    eval3 (R.hom S T) l0 l1 l2 = R.eval (eval3 S l0 l1 l2) (eval3 T l0 l1 l2) := by
  rw [Rows4.hom, eval3_add3, eval3_add3, eval3_add3, eval3_mul3, eval3_mul3, eval3_mul3,
    eval3_mul3, eval3_homDeg3 _ _ h, eval3_homDeg3 _ _ h, eval3_homDeg3 _ _ h,
    eval3_homDeg3 _ _ h, eval3_homT _ _ h, eval3_homT _ _ h, eval3_homT _ _ h, eval3_homT _ _ h,
    Rows4.eval]
  ring

/-! ### The row -/

/-- One row of the majorization certificate: the cell `(k, l)`, the target `tgt`, the tangent
radius `q = mq / 64`, and the triangle, which is half of the axis-parallel square of side `h` with
lower-left corner `(p, q')` in the cell's local coordinates — the lower half if `up` is false and
the upper half if it is true. -/
structure MajRow where
  /-- The first cell index. -/
  k : ℕ
  /-- The second cell index. -/
  l : ℕ
  /-- The lower bound asserted on the triangle, `0` or `1`. -/
  tgt : ℕ
  /-- `64` times the radius at which the base's tangent minorant is taken. -/
  mq : ℕ
  /-- Whether the triangle is the upper half of its square. -/
  up : Bool
  /-- The `s`-coordinate of the square's lower-left corner. -/
  p : ℚ
  /-- The `t`-coordinate of the square's lower-left corner. -/
  q : ℚ
  /-- The side of the square. -/
  h : ℚ

namespace MajRow

/-- The `s`-coordinate of the first vertex. -/
def s0 (r : MajRow) : ℚ := if r.up then r.p + r.h else r.p
/-- The `s`-coordinate of the second vertex. -/
def s1 (r : MajRow) : ℚ := if r.up then r.p else r.p + r.h
/-- The `s`-coordinate of the third vertex. -/
def s2 (r : MajRow) : ℚ := if r.up then r.p + r.h else r.p
/-- The `t`-coordinate of the first vertex. -/
def t0 (r : MajRow) : ℚ := if r.up then r.q + r.h else r.q
/-- The `t`-coordinate of the second vertex. -/
def t1 (r : MajRow) : ℚ := if r.up then r.q + r.h else r.q
/-- The `t`-coordinate of the third vertex. -/
def t2 (r : MajRow) : ℚ := if r.up then r.q else r.q + r.h

/-- The base coefficient `a` of the kernel, as a rational. -/
def baseQ : ℚ := 45006666551170177 / 25000000000000000

theorem baseQ_cast : ((baseQ : ℚ) : ℝ) = fracBaseCoeff := by
  rw [fracBaseCoeff_eq, baseQ]
  push_cast
  ring

theorem baseQ_pos : 0 < baseQ := by rw [baseQ]; norm_num

/-- The slope `a α q ^ (-α-1)` of the base's tangent minorant, rounded down. -/
def slope (r : MajRow) : ℚ := baseQ * (6 / 5) * majLo r.mq (-11)

/-- The height `a (q ^ (-α) - R ^ (-α))` of the base's tangent minorant, rounded down.  At the
truncation radius itself the height is *exactly* zero, and taking it to be zero rather than the
difference of two enclosures is what keeps the certificate exact on the `55` triangles that meet
the support boundary. -/
def height (r : MajRow) : ℚ :=
  if r.mq = 112 then 0 else baseQ * (majLo r.mq (-6) - majRUpQ)

/-- The constant term of the affine base minorant, with the target already subtracted. -/
def cst (r : MajRow) : ℚ :=
  r.height + r.slope * ((r.mq : ℚ) / 64 - ((r.k : ℚ) + (r.l : ℚ)) / 16) - (r.tgt : ℚ)

/-- The local coordinate `s` as a linear form in the barycentric coordinates.  It is normalised,
so a vertex with `s = 0` costs the products nothing. -/
def sHom (r : MajRow) : Poly3 := norm3 [((1, 0, 0), r.s0), ((0, 1, 0), r.s1), ((0, 0, 1), r.s2)]

/-- The local coordinate `t` as a linear form in the barycentric coordinates. -/
def tHom (r : MajRow) : Poly3 := norm3 [((1, 0, 0), r.t0), ((0, 1, 0), r.t1), ((0, 0, 1), r.t2)]

/-- The affine part of the row's bicubic: the base minorant minus the target, scaled. -/
def aff (r : MajRow) : Rows4 :=
  ⟨[((0, 0, 0), majScaleQ * r.cst), ((0, 0, 1), majScaleQ * (-r.slope / 16))],
   [((0, 0, 0), majScaleQ * (-r.slope / 16))], [], []⟩

/-- **The row's barycentric polynomial.**  Its coefficients are the Bernstein coefficients of the
certified bound, times positive multinomials. -/
def poly (r : MajRow) : Poly3 :=
  Rows4.hom (Rows4.add (cellRows (r.k : ℤ) (r.l : ℤ)) r.aff) r.sHom r.tHom

/-- **The single kernel check of one row**: the radius is positive, each vertex of the triangle has
diamond radius at most `q`, and every barycentric coefficient is nonnegative. -/
def check (r : MajRow) : Bool :=
  decide (0 < r.mq) &&
  decide (4 * ((r.k : ℚ) + (r.l : ℚ)) + 4 * (r.s0 + r.t0) ≤ (r.mq : ℚ)) &&
  decide (4 * ((r.k : ℚ) + (r.l : ℚ)) + 4 * (r.s1 + r.t1) ≤ (r.mq : ℚ)) &&
  decide (4 * ((r.k : ℚ) + (r.l : ℚ)) + 4 * (r.s2 + r.t2) ≤ (r.mq : ℚ)) &&
  r.poly.all fun e => decide (0 ≤ e.2)

end MajRow

/-- **The barycentric identity.**  At a point of the triangle, written in barycentric coordinates,
the row's polynomial is the scaled cell bicubic plus the scaled affine base minorant minus the
target. -/
theorem eval3_MajRow_poly (r : MajRow) {s t l0 l1 l2 : ℝ} (hsum : l0 + l1 + l2 = 1)
    (hS : s = (r.s0 : ℝ) * l0 + (r.s1 : ℝ) * l1 + (r.s2 : ℝ) * l2)
    (hT : t = (r.t0 : ℝ) * l0 + (r.t1 : ℝ) * l1 + (r.t2 : ℝ) * l2) :
    eval3 r.poly l0 l1 l2
      = (cellRows (r.k : ℤ) (r.l : ℤ)).eval s t
        + ((majScaleQ : ℚ) : ℝ) * (((r.cst : ℚ) : ℝ) - ((r.slope : ℚ) : ℝ) / 16 * s
            - ((r.slope : ℚ) : ℝ) / 16 * t) := by
  have hSe : eval3 r.sHom l0 l1 l2 = s := by
    rw [MajRow.sHom, eval3_norm3]
    simp only [eval3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mono3,
      pow_zero, pow_one, one_mul, mul_one]
    rw [hS]
    ring
  have hTe : eval3 r.tHom l0 l1 l2 = t := by
    rw [MajRow.tHom, eval3_norm3]
    simp only [eval3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mono3,
      pow_zero, pow_one, one_mul, mul_one]
    rw [hT]
    ring
  rw [MajRow.poly, eval3_Rows4_hom _ _ _ hsum, hSe, hTe, Rows4.eval_add]
  congr 1
  simp only [MajRow.aff, Rows4.eval, eval3, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, mono3, pow_zero, pow_one, one_mul, mul_one, zero_mul]
  push_cast
  ring

/-- **What a passing row buys.**  If `z` is nonzero and its folded, scaled coordinates
`16 |z₀| = k + s`, `16 |z₁| = l + t` lie in the row's triangle — witnessed by nonnegative
barycentric coordinates `l₀, l₁, l₂` summing to `1` — then `tgt ≤ fracKernel z`. -/
theorem MajRow.sound {r : MajRow} (hr : r.check = true) {z : Fin 2 → ℝ} {s t l0 l1 l2 : ℝ}
    (hz : 0 < diamondNorm z)
    (hu : 16 * |z 0| = (r.k : ℝ) + s) (hv : 16 * |z 1| = (r.l : ℝ) + t)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h0 : 0 ≤ l0) (h1 : 0 ≤ l1) (h2 : 0 ≤ l2) (hsum : l0 + l1 + l2 = 1)
    (hS : s = (r.s0 : ℝ) * l0 + (r.s1 : ℝ) * l1 + (r.s2 : ℝ) * l2)
    (hT : t = (r.t0 : ℝ) * l0 + (r.t1 : ℝ) * l1 + (r.t2 : ℝ) * l2) :
    (r.tgt : ℝ) ≤ fracKernel z := by
  rw [MajRow.check] at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨⟨⟨⟨hmq, e0⟩, e1⟩, e2⟩, hall⟩ := hr
  -- the radius of `z`, and that it is at most the tangent radius
  have hdn : diamondNorm z = ((r.k : ℝ) + s + ((r.l : ℝ) + t)) / 16 := by
    have hab : diamondNorm z = |z 0| + |z 1| := rfl
    rw [hab]
    linarith
  have f0 : 4 * ((r.k : ℝ) + (r.l : ℝ)) + 4 * ((r.s0 : ℝ) + (r.t0 : ℝ)) ≤ (r.mq : ℝ) := by
    exact_mod_cast e0
  have f1 : 4 * ((r.k : ℝ) + (r.l : ℝ)) + 4 * ((r.s1 : ℝ) + (r.t1 : ℝ)) ≤ (r.mq : ℝ) := by
    exact_mod_cast e1
  have f2 : 4 * ((r.k : ℝ) + (r.l : ℝ)) + 4 * ((r.s2 : ℝ) + (r.t2 : ℝ)) ≤ (r.mq : ℝ) := by
    exact_mod_cast e2
  have hexp : 4 * ((r.k : ℝ) + (r.l : ℝ)) + 4 * (s + t)
      = l0 * (4 * ((r.k : ℝ) + (r.l : ℝ)) + 4 * ((r.s0 : ℝ) + (r.t0 : ℝ)))
        + l1 * (4 * ((r.k : ℝ) + (r.l : ℝ)) + 4 * ((r.s1 : ℝ) + (r.t1 : ℝ)))
        + l2 * (4 * ((r.k : ℝ) + (r.l : ℝ)) + 4 * ((r.s2 : ℝ) + (r.t2 : ℝ))) := by
    rw [hS, hT]
    linear_combination (4 * ((r.k : ℝ) + (r.l : ℝ))) * hsum.symm
  have hsumq : l0 * (r.mq : ℝ) + l1 * (r.mq : ℝ) + l2 * (r.mq : ℝ) = (r.mq : ℝ) := by
    linear_combination (r.mq : ℝ) * hsum
  have hkey : 4 * ((r.k : ℝ) + (r.l : ℝ)) + 4 * (s + t) ≤ (r.mq : ℝ) := by
    rw [hexp, ← hsumq]
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left f0 h0)
      (mul_le_mul_of_nonneg_left f1 h1)) (mul_le_mul_of_nonneg_left f2 h2)
  have hqpos : (0 : ℝ) < (r.mq : ℝ) / 64 := by
    have : (0 : ℝ) < (r.mq : ℝ) := by exact_mod_cast hmq
    positivity
  have hqr : diamondNorm z ≤ (r.mq : ℝ) / 64 := by rw [hdn]; linarith
  -- the affine minorant of the base
  have htan := tangent_sub_le_truncBase (α := 6 / 5) (R := 7 / 4) (by norm_num) hz hqpos
  have hslo : ((r.slope : ℚ) : ℝ)
      ≤ fracBaseCoeff * (6 / 5 * ((r.mq : ℝ) / 64) ^ (-(6 / 5 : ℝ) - 1)) := by
    have hl := majLo_le hmq (-11)
    have hee : (((-11 : ℤ) : ℝ)) / 5 = -(6 / 5 : ℝ) - 1 := by norm_num
    rw [hee] at hl
    rw [MajRow.slope]
    push_cast
    rw [MajRow.baseQ_cast.symm]
    have hb : (0 : ℝ) < ((MajRow.baseQ : ℚ) : ℝ) := by
      rw [MajRow.baseQ_cast]; exact fracBaseCoeff_pos
    calc ((MajRow.baseQ : ℚ) : ℝ) * (6 / 5) * ((majLo r.mq (-11) : ℚ) : ℝ)
        ≤ ((MajRow.baseQ : ℚ) : ℝ) * (6 / 5) * (((r.mq : ℝ) / 64) ^ (-(6 / 5 : ℝ) - 1)) := by
          exact mul_le_mul_of_nonneg_left hl (by positivity)
      _ = ((MajRow.baseQ : ℚ) : ℝ) * (6 / 5 * ((r.mq : ℝ) / 64) ^ (-(6 / 5 : ℝ) - 1)) := by ring
  have hslope_nonneg : (0 : ℝ) ≤ ((r.slope : ℚ) : ℝ) := by
    rw [MajRow.slope]
    have := majLo_nonneg r.mq (-11)
    have hb := MajRow.baseQ_pos
    push_cast
    positivity
  have hhei : ((r.height : ℚ) : ℝ)
      ≤ fracBaseCoeff * (((r.mq : ℝ) / 64) ^ (-(6 / 5 : ℝ)) - ((7 : ℝ) / 4) ^ (-(6 / 5 : ℝ))) := by
    have hb : (0 : ℝ) < fracBaseCoeff := fracBaseCoeff_pos
    rw [MajRow.height]
    split
    · rename_i h112
      have hq : ((r.mq : ℝ)) / 64 = (7 : ℝ) / 4 := by rw [h112]; norm_num
      rw [hq]
      simp
    · have hl := majLo_le hmq (-6)
      have hee : (((-6 : ℤ) : ℝ)) / 5 = -(6 / 5 : ℝ) := by norm_num
      rw [hee] at hl
      have hu2 : ((7 : ℝ) / 4) ^ (-(6 / 5 : ℝ)) ≤ ((majRUpQ : ℚ) : ℝ) := by
        have := majRUp_sound
        rw [show ((-6 : ℝ)) / 5 = -(6 / 5 : ℝ) from by norm_num] at this
        exact this
      push_cast
      rw [MajRow.baseQ_cast.symm]
      have hb2 : (0 : ℝ) < ((MajRow.baseQ : ℚ) : ℝ) := by
        rw [MajRow.baseQ_cast]; exact fracBaseCoeff_pos
      have hstep : ((majLo r.mq (-6) : ℚ) : ℝ) - ((majRUpQ : ℚ) : ℝ)
          ≤ ((r.mq : ℝ) / 64) ^ (-(6 / 5 : ℝ)) - ((7 : ℝ) / 4) ^ (-(6 / 5 : ℝ)) := by linarith
      exact mul_le_mul_of_nonneg_left hstep hb2.le
  have hbase : ((r.height : ℚ) : ℝ)
      + ((r.slope : ℚ) : ℝ) * ((r.mq : ℝ) / 64 - diamondNorm z)
        ≤ fracBaseCoeff * truncBase (6 / 5) (7 / 4) z := by
    have hb : (0 : ℝ) < fracBaseCoeff := fracBaseCoeff_pos
    have hgap : (0 : ℝ) ≤ (r.mq : ℝ) / 64 - diamondNorm z := by linarith
    have hmul : fracBaseCoeff * (((r.mq : ℝ) / 64) ^ (-(6 / 5 : ℝ))
        + 6 / 5 * ((r.mq : ℝ) / 64) ^ (-(6 / 5 : ℝ) - 1) * ((r.mq : ℝ) / 64 - diamondNorm z)
        - ((7 : ℝ) / 4) ^ (-(6 / 5 : ℝ))) ≤ fracBaseCoeff * truncBase (6 / 5) (7 / 4) z :=
      mul_le_mul_of_nonneg_left htan hb.le
    have hsl2 : ((r.slope : ℚ) : ℝ) * ((r.mq : ℝ) / 64 - diamondNorm z)
        ≤ fracBaseCoeff * (6 / 5 * ((r.mq : ℝ) / 64) ^ (-(6 / 5 : ℝ) - 1))
            * ((r.mq : ℝ) / 64 - diamondNorm z) :=
      mul_le_mul_of_nonneg_right hslo hgap
    nlinarith [hhei, hsl2, hmul]
  -- the spline part
  have hsp : (cellRows (r.k : ℤ) (r.l : ℤ)).eval s t
      = ((majScaleQ : ℚ) : ℝ) * splineSum (16 * z 0) (16 * z 1) := by
    have habs : splineSum (16 * z 0) (16 * z 1) = splineSum (16 * |z 0|) (16 * |z 1|) := by
      rw [show (16 : ℝ) * |z 0| = |16 * z 0| from by rw [abs_mul]; norm_num,
        show (16 : ℝ) * |z 1| = |16 * z 1| from by rw [abs_mul]; norm_num, splineSum_abs]
    rw [habs, hu, hv]
    exact splineSum_eq_eval3 (Int.natCast_nonneg r.k) (Int.natCast_nonneg r.l) hs0 hs1 ht0 ht1
  -- the Bernstein test
  have hscale : (0 : ℝ) < ((majScaleQ : ℚ) : ℝ) := by rw [majScaleQ_real]; norm_num
  have hnn : 0 ≤ eval3 r.poly l0 l1 l2 := eval3_nonneg_of_all hall h0 h1 h2
  have hfac : eval3 r.poly l0 l1 l2
      = ((majScaleQ : ℚ) : ℝ) * (splineSum (16 * z 0) (16 * z 1) + ((r.cst : ℚ) : ℝ)
          - ((r.slope : ℚ) : ℝ) / 16 * s - ((r.slope : ℚ) : ℝ) / 16 * t) := by
    rw [eval3_MajRow_poly r hsum hS hT, hsp]
    ring
  rw [hfac] at hnn
  have hnn' : 0 ≤ splineSum (16 * z 0) (16 * z 1) + ((r.cst : ℚ) : ℝ)
      - ((r.slope : ℚ) : ℝ) / 16 * s - ((r.slope : ℚ) : ℝ) / 16 * t := by
    refine le_of_mul_le_mul_left ?_ hscale
    rw [mul_zero]
    exact hnn
  have hcst : ((r.cst : ℚ) : ℝ) = ((r.height : ℚ) : ℝ)
      + ((r.slope : ℚ) : ℝ) * ((r.mq : ℝ) / 64 - ((r.k : ℝ) + (r.l : ℝ)) / 16)
      - (r.tgt : ℝ) := by
    rw [MajRow.cst]
    push_cast
    ring
  have hsplit : ((r.slope : ℚ) : ℝ) * ((r.mq : ℝ) / 64 - diamondNorm z)
      = ((r.slope : ℚ) : ℝ) * ((r.mq : ℝ) / 64 - ((r.k : ℝ) + (r.l : ℝ)) / 16)
        - ((r.slope : ℚ) : ℝ) / 16 * s - ((r.slope : ℚ) : ℝ) / 16 * t := by
    rw [hdn]
    ring
  rw [hsplit] at hbase
  rw [fracKernel_eq]
  linarith

/-! ### The two triangle shapes -/

/-- **A lower-half triangle covers its corner square's lower half.**  The barycentric coordinates
are `(1 - σ - τ, σ, τ)` with `σ = (s - p)/h`, `τ = (t - q)/h`. -/
theorem MajRow.sound_down {r : MajRow} (hr : r.check = true) (hup : r.up = false)
    {z : Fin 2 → ℝ} {s t : ℝ} (hz : 0 < diamondNorm z)
    (hu : 16 * |z 0| = (r.k : ℝ) + s) (hv : 16 * |z 1| = (r.l : ℝ) + t)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hh : (0 : ℝ) < (r.h : ℝ))
    (hA : (r.p : ℝ) ≤ s) (hB : (r.q : ℝ) ≤ t)
    (hC : s - (r.p : ℝ) + (t - (r.q : ℝ)) ≤ (r.h : ℝ)) :
    (r.tgt : ℝ) ≤ fracKernel z := by
  have hne : ¬(r.up = true) := by simp [hup]
  have e0 : (r.s0 : ℝ) = (r.p : ℝ) := by rw [MajRow.s0, if_neg hne]
  have e1 : (r.s1 : ℝ) = (r.p : ℝ) + (r.h : ℝ) := by
    rw [MajRow.s1, if_neg hne]; push_cast; ring
  have e2 : (r.s2 : ℝ) = (r.p : ℝ) := by rw [MajRow.s2, if_neg hne]
  have f0 : (r.t0 : ℝ) = (r.q : ℝ) := by rw [MajRow.t0, if_neg hne]
  have f1 : (r.t1 : ℝ) = (r.q : ℝ) := by rw [MajRow.t1, if_neg hne]
  have f2 : (r.t2 : ℝ) = (r.q : ℝ) + (r.h : ℝ) := by
    rw [MajRow.t2, if_neg hne]; push_cast; ring
  refine MajRow.sound hr hz hu hv hs0 hs1 ht0 ht1
    (l0 := 1 - (s - (r.p : ℝ)) / (r.h : ℝ) - (t - (r.q : ℝ)) / (r.h : ℝ))
    (l1 := (s - (r.p : ℝ)) / (r.h : ℝ)) (l2 := (t - (r.q : ℝ)) / (r.h : ℝ)) ?_ ?_ ?_ ?_ ?_ ?_
  · have key : (s - (r.p : ℝ)) / (r.h : ℝ) + (t - (r.q : ℝ)) / (r.h : ℝ)
        = (s - (r.p : ℝ) + (t - (r.q : ℝ))) / (r.h : ℝ) := by ring
    rw [sub_sub, sub_nonneg, key, div_le_one hh]
    linarith
  · exact div_nonneg (by linarith) hh.le
  · exact div_nonneg (by linarith) hh.le
  · ring
  · rw [e0, e1, e2]
    field_simp
    ring
  · rw [f0, f1, f2]
    field_simp
    ring

/-- **An upper-half triangle covers its corner square's upper half.**  The barycentric coordinates
are `(σ + τ - 1, 1 - σ, 1 - τ)`. -/
theorem MajRow.sound_up {r : MajRow} (hr : r.check = true) (hup : r.up = true)
    {z : Fin 2 → ℝ} {s t : ℝ} (hz : 0 < diamondNorm z)
    (hu : 16 * |z 0| = (r.k : ℝ) + s) (hv : 16 * |z 1| = (r.l : ℝ) + t)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hh : (0 : ℝ) < (r.h : ℝ))
    (hA : s ≤ (r.p : ℝ) + (r.h : ℝ)) (hB : t ≤ (r.q : ℝ) + (r.h : ℝ))
    (hC : (r.h : ℝ) ≤ s - (r.p : ℝ) + (t - (r.q : ℝ))) :
    (r.tgt : ℝ) ≤ fracKernel z := by
  have e0 : (r.s0 : ℝ) = (r.p : ℝ) + (r.h : ℝ) := by
    rw [MajRow.s0, if_pos hup]; push_cast; ring
  have e1 : (r.s1 : ℝ) = (r.p : ℝ) := by rw [MajRow.s1, if_pos hup]
  have e2 : (r.s2 : ℝ) = (r.p : ℝ) + (r.h : ℝ) := by
    rw [MajRow.s2, if_pos hup]; push_cast; ring
  have f0 : (r.t0 : ℝ) = (r.q : ℝ) + (r.h : ℝ) := by
    rw [MajRow.t0, if_pos hup]; push_cast; ring
  have f1 : (r.t1 : ℝ) = (r.q : ℝ) + (r.h : ℝ) := by
    rw [MajRow.t1, if_pos hup]; push_cast; ring
  have f2 : (r.t2 : ℝ) = (r.q : ℝ) := by rw [MajRow.t2, if_pos hup]
  refine MajRow.sound hr hz hu hv hs0 hs1 ht0 ht1
    (l0 := (s - (r.p : ℝ)) / (r.h : ℝ) + (t - (r.q : ℝ)) / (r.h : ℝ) - 1)
    (l1 := 1 - (s - (r.p : ℝ)) / (r.h : ℝ)) (l2 := 1 - (t - (r.q : ℝ)) / (r.h : ℝ))
    ?_ ?_ ?_ ?_ ?_ ?_
  · have key : (s - (r.p : ℝ)) / (r.h : ℝ) + (t - (r.q : ℝ)) / (r.h : ℝ)
        = (s - (r.p : ℝ) + (t - (r.q : ℝ))) / (r.h : ℝ) := by ring
    rw [sub_nonneg, key, le_div_iff₀ hh]
    linarith
  · rw [sub_nonneg, div_le_one hh]
    linarith
  · rw [sub_nonneg, div_le_one hh]
    linarith
  · ring
  · rw [e0, e1, e2]
    field_simp
    ring
  · rw [f0, f1, f2]
    field_simp
    ring

end CenteredMaximal.Fractional

end

end
