/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.CentredLeaf
public import CenteredMaximal.Fractional.RatItv

/-!
# The interval-coefficient polynomial model of a certificate leaf

`CenteredMaximal.Fractional.jumpGen_fracKernel_nonneg_of_centred` reduces one rectangle of the
`α = 6/5` generator certificate to two hypotheses about a **single** centred bivariate polynomial
model of the whole generator: `hmodel`, that the model minorises the generator up to `err`, and
`hcheck`, a rational inequality on the model's coefficients.  This file carries the model.

## A term, and why the coefficients are intervals

Every coefficient the model produces is a sum of terms

`q · x ^ (e/5)`,      `q, x` rational, `x > 0`, `e` an integer,

because both halves of the generator reduce to that shape: the base's tangent minorant through the
two radial powers `r ^ (−12/5)` and `r ^ (−17/5)` and the truncation power `(7/4) ^ (−12/5)`, and
the spline half through the four Taylor powers `|c| ^ ((9 − 5a)/5)` of
`CenteredMaximal.Fractional.taylorRhoQ`.  A `ModelTerm` is one such term, together with the
bidegree `(a, b)` of the monomial `sᵃ tᵇ` it sits on.

A coefficient is therefore an *irrational* number, and it is carried as an interval rather than as
a pair of independent bounds on the two halves, because the coefficients of `s` and of `t` are sums
of some fifteen hundred terms that **very nearly cancel** — the spline was fitted to the base, so
its gradient tracks minus the base's.  Bounding the two halves separately costs a factor of about
`10³` near the origin and fails `2674` of the `4582` rectangles; see the module docstring of
`CenteredMaximal.Fractional.CentredLeaf`.

## Why the spline half is scaled last

`splineScale = (625/108) · 16 ^ (6/5)` multiplies the *whole* spline half, and the model applies it
to the already-accumulated coefficient interval rather than to each of the fifteen hundred terms.
That is both cheaper — one interval multiplication per bidegree instead of one per term — and
tighter, because the cancellation between the rows happens in exact rational arithmetic before the
only genuinely two-sided multiplication of the certificate.  It is what the search program does.

## Main results

* `ModelTerm`, `ModelTerm.coR`, `ModelTerm.coI`, `ModelTerm.coI_mem`: one term, its real value and
  its interval.  A term with exponent `0` is exactly rational and is not sent to the table.
* `termsCoR`, `termsCoI`, `termsValR`: the coefficient of one bidegree, its interval, and the value
  of the whole model at a point of the rectangle.
* `termsCoI_mem`, `termsValR_eq_sum`: **the model's two structural facts** — every coefficient lies
  in its interval, and the model's value is the sum of its coefficients against the monomials.
* `leafCoR`, `leafCoI`, `leafValR`, `leafCheckQ`: the two-list model of a leaf, with the spline half
  scaled, and the single rational number a leaf check tests.
* `jumpGen_fracKernel_nonneg_of_terms`: **the assembly.**  A model whose value minorises the
  generator up to `err`, and whose rational check is nonnegative, proves the generator nonnegative
  on the rectangle.
-/

@[expose] public section

open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### One term of a model -/

/-- One term of a leaf's polynomial model: the monomial `q · x ^ (e/5) · sᵃ tᵇ`, with `x` a
positive rational whose fifth-power-exponent power the enclosure table carries. -/
structure ModelTerm where
  /-- The degree in the first deviation `s`. -/
  a : ℕ
  /-- The degree in the second deviation `t`. -/
  b : ℕ
  /-- The rational scalar. -/
  q : ℚ
  /-- The base of the power, a positive rational. -/
  x : ℚ
  /-- The numerator, over `5`, of the exponent. -/
  e : ℤ

namespace ModelTerm

/-- The real coefficient a term contributes. -/
noncomputable def coR (w : ModelTerm) : ℝ := (w.q : ℝ) * (w.x : ℝ) ^ ((w.e : ℝ) / 5)

/-- The interval a term contributes.  An exponent of `0` makes the term exactly rational, and
sending it to the table would widen it by a unit in the last place for nothing. -/
def coI (L : List FifthEnc) (w : ModelTerm) : RatItv :=
  if w.e = 0 then RatItv.pt w.q else RatItv.scale w.q (encItv L w.x w.e)

/-- **A term's real coefficient lies in its interval.** -/
theorem coI_mem {L : List FifthEnc} (hL : L.all (fun c => c.check 12) = true) {w : ModelTerm}
    (hx : 0 < w.x) : (w.coI L).Mem w.coR := by
  rw [coI, coR]
  split
  · rename_i he
    rw [he]
    have hz : (((0 : ℤ) : ℝ) / 5) = 0 := by norm_num
    rw [hz, Real.rpow_zero, mul_one]
    exact RatItv.mem_pt w.q
  · exact RatItv.mem_scale w.q (encItv_mem hL hx w.e)

end ModelTerm

/-! ### A list of terms -/

/-- The real coefficient of the bidegree `p` in a list of terms. -/
noncomputable def termsCoR (M : List ModelTerm) (p : ℕ × ℕ) : ℝ :=
  (M.map fun w => if (w.a, w.b) = p then w.coR else 0).sum

/-- The interval of the coefficient of the bidegree `p` in a list of terms. -/
def termsCoI (L : List FifthEnc) (M : List ModelTerm) (p : ℕ × ℕ) : RatItv :=
  M.foldr (fun w acc => if (w.a, w.b) = p then RatItv.add (w.coI L) acc else acc) RatItv.zero

/-- The value of a list of terms at a point of the rectangle, in the deviations `s` and `t` from
its centre. -/
noncomputable def termsValR (M : List ModelTerm) (s t : ℝ) : ℝ :=
  (M.map fun w => w.coR * s ^ w.a * t ^ w.b).sum

/-- **Every coefficient of a model lies in its interval.** -/
theorem termsCoI_mem {L : List FifthEnc} (hL : L.all (fun c => c.check 12) = true)
    {M : List ModelTerm} (hx : ∀ w ∈ M, 0 < w.x) (p : ℕ × ℕ) :
    (termsCoI L M p).Mem (termsCoR M p) := by
  induction M with
  | nil => exact RatItv.mem_zero
  | cons w M ih =>
      have hmem : ∀ v ∈ M, 0 < v.x := fun v hv => hx v (List.mem_cons_of_mem w hv)
      have hstep := ih hmem
      rw [termsCoR, List.map_cons, List.sum_cons, ← termsCoR, termsCoI, List.foldr_cons,
        ← termsCoI]
      split
      · exact RatItv.mem_add (w.coI_mem hL (hx w (List.mem_cons_self ..))) hstep
      · rw [zero_add]
        exact hstep

theorem termsValR_nil (s t : ℝ) : termsValR [] s t = 0 := rfl

theorem termsValR_append (M N : List ModelTerm) (s t : ℝ) :
    termsValR (M ++ N) s t = termsValR M s t + termsValR N s t := by
  simp [termsValR, List.sum_append]

/-- **The model's value is the sum of its coefficients against the monomials.**  The bidegrees of
the terms have to lie in the index set `F`, which is what lets the term-by-term sum be regrouped
into a sum over `F`. -/
theorem termsValR_eq_sum {F : Finset (ℕ × ℕ)} {M : List ModelTerm}
    (hF : ∀ w ∈ M, (w.a, w.b) ∈ F) (s t : ℝ) :
    termsValR M s t = ∑ p ∈ F, termsCoR M p * s ^ p.1 * t ^ p.2 := by
  induction M with
  | nil =>
      rw [termsValR_nil]
      refine (Finset.sum_eq_zero fun p _ => ?_).symm
      rw [termsCoR]
      simp
  | cons w M ih =>
      have hmem : ∀ v ∈ M, (v.a, v.b) ∈ F := fun v hv => hF v (List.mem_cons_of_mem w hv)
      have hsplit : ∀ p ∈ F, termsCoR (w :: M) p * s ^ p.1 * t ^ p.2
          = (if p = (w.a, w.b) then w.coR * s ^ w.a * t ^ w.b else 0)
            + termsCoR M p * s ^ p.1 * t ^ p.2 := by
        intro p _
        rw [termsCoR, List.map_cons, List.sum_cons, ← termsCoR]
        by_cases hp : (w.a, w.b) = p
        · rw [if_pos hp, if_pos hp.symm, ← hp]
          ring
        · rw [if_neg hp, if_neg fun h => hp h.symm]
          ring
      rw [termsValR, List.map_cons, List.sum_cons, ← termsValR, ih hmem,
        Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
        Finset.sum_ite_eq' F (w.a, w.b) (fun _ => w.coR * s ^ w.a * t ^ w.b),
        if_pos (hF w (List.mem_cons_self ..))]

/-! ### The two-list model of a leaf -/

/-- The constant the spline half of the generator is scaled by: the `625/108` of the fourth
difference of `CenteredMaximal.Fractional.jumpGen1_bspline_sixFifths` and the `16 ^ (6/5)` of the
dilation of the spline grid. -/
noncomputable def splineScale : ℝ := 625 / 108 * (16 : ℝ) ^ ((6 : ℝ) / 5)

/-- The interval of `splineScale`, the certificate's only genuinely two-sided multiplication. -/
def splineScaleI (L : List FifthEnc) : RatItv := RatItv.scale (625 / 108) (encItv L 16 6)

theorem splineScaleI_mem {L : List FifthEnc} (hL : L.all (fun c => c.check 12) = true) :
    (splineScaleI L).Mem splineScale := by
  have h := RatItv.mem_scale (I := encItv L 16 6) (625 / 108) (encItv_mem hL (by norm_num) 6)
  have hcast : ((625 / 108 : ℚ) : ℝ) * ((16 : ℚ) : ℝ) ^ (((6 : ℤ) : ℝ) / 5) = splineScale := by
    rw [splineScale]
    push_cast
    norm_num
  rw [splineScaleI, ← hcast]
  exact h

/-- The real coefficient of the bidegree `p` in a leaf's model: the spline half, scaled, plus the
base half. -/
noncomputable def leafCoR (Msp Mba : List ModelTerm) (p : ℕ × ℕ) : ℝ :=
  splineScale * termsCoR Msp p + termsCoR Mba p

/-- The interval of that coefficient. -/
def leafCoI (L : List FifthEnc) (Msp Mba : List ModelTerm) (p : ℕ × ℕ) : RatItv :=
  RatItv.add (RatItv.mul (splineScaleI L) (termsCoI L Msp p)) (termsCoI L Mba p)

/-- The value of a leaf's model at a point of its rectangle. -/
noncomputable def leafValR (Msp Mba : List ModelTerm) (s t : ℝ) : ℝ :=
  splineScale * termsValR Msp s t + termsValR Mba s t

theorem leafCoI_mem {L : List FifthEnc} (hL : L.all (fun c => c.check 12) = true)
    {Msp Mba : List ModelTerm} (hsp : ∀ w ∈ Msp, 0 < w.x) (hba : ∀ w ∈ Mba, 0 < w.x)
    (p : ℕ × ℕ) : (leafCoI L Msp Mba p).Mem (leafCoR Msp Mba p) :=
  RatItv.mem_add (RatItv.mem_mul (splineScaleI_mem hL) (termsCoI_mem hL hsp p))
    (termsCoI_mem hL hba p)

/-! ### The index set of the model -/

/-- The fifteen non-constant bidegrees of a bicubic model. -/
def modelExps : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3),
   (3, 0), (3, 1), (3, 2), (3, 3)]

/-- The sixteen bidegrees of a bicubic model. -/
def modelFinset : Finset (ℕ × ℕ) := insert (0, 0) modelExps.toFinset

theorem modelExps_nodup : modelExps.Nodup := by decide

theorem zero_notMem_modelExps : (0, 0) ∉ modelExps.toFinset := by decide

theorem zero_mem_modelFinset : (0, 0) ∈ modelFinset := Finset.mem_insert_self _ _

theorem modelFinset_erase : modelFinset.erase (0, 0) = modelExps.toFinset :=
  Finset.erase_insert zero_notMem_modelExps

/-- A bidegree of a bicubic lies in the index set. -/
theorem mem_modelFinset {w : ModelTerm} (ha : w.a < 4) (hb : w.b < 4) :
    (w.a, w.b) ∈ modelFinset := by
  rw [modelFinset, Finset.mem_insert, List.mem_toFinset]
  interval_cases h : w.a <;> interval_cases h' : w.b <;> simp [modelExps]

/-! ### The rational check of a leaf -/

/-- **The single rational number a leaf check tests.**  The lower end of the constant coefficient,
less the `δ`-weighted sum of the largest absolute values of the other fifteen, less the model
error.  A leaf passes when this is nonnegative. -/
def leafCheckQ (L : List FifthEnc) (Msp Mba : List ModelTerm) (δ err : ℚ) : ℚ :=
  (leafCoI L Msp Mba (0, 0)).lo
    - (modelExps.map fun p => (leafCoI L Msp Mba p).absmax * δ ^ (p.1 + p.2)).sum - err

/-! ### The assembly -/

/-- **The leaf inequality, driven by a two-list model.**  A model of the generator on a rectangle
whose value minorises the generator up to the rational error `err`, and whose rational check is
nonnegative, proves the generator of the comparison kernel nonnegative on that rectangle.

This is `CenteredMaximal.Fractional.jumpGen_fracKernel_nonneg_of_centred` with its `co` supplied by
`leafCoR` and its `hcheck` discharged from the rational inequality `hchk`, which a certificate
shard decides in the kernel. -/
theorem jumpGen_fracKernel_nonneg_of_terms {L : List FifthEnc}
    (hL : L.all (fun c => c.check 12) = true) {Msp Mba : List ModelTerm}
    (hsp : ∀ w ∈ Msp, 0 < w.x ∧ w.a < 4 ∧ w.b < 4)
    (hba : ∀ w ∈ Mba, 0 < w.x ∧ w.a < 4 ∧ w.b < 4)
    {S r₀ d₀ : ℝ} {K Ltail : ℕ} (hS : 0 ≤ S)
    (hSle : S ≤ -4 * Real.pi * Real.Gamma (2 * (6 / 5)) * Real.cos (Real.pi * (6 / 5) / 2)
      / (6 / 5 * Real.Gamma (6 / 5) ^ 2 * Real.sin (Real.pi * (6 / 5) / 2)))
    (hr₀ : 0 < r₀) {uc vc : ℝ} {δ err : ℚ} (hδ : 0 ≤ δ)
    (hchk : 0 ≤ leafCheckQ L Msp Mba δ err)
    {z : Fin 2 → ℝ} (h0 : z 0 ≠ 0) (h1 : z 1 ≠ 0) (hz : diamondNorm z < 7 / 4)
    (hu : |16 * |z 0| - uc| ≤ (δ : ℝ)) (hv : |16 * |z 1| - vc| ≤ (δ : ℝ))
    (hmodel : leafValR Msp Mba (16 * |z 0| - uc) (16 * |z 1| - vc) - (err : ℝ)
      ≤ fracBaseCoeff * fullMinorant (6 / 5) (7 / 4) S K Ltail r₀ d₀ (diamondNorm z)
          (|z 0| - |z 1|)
        + ∑ ij ∈ fracCellFinset, fracCoeff (fracCellCoeff ij) *
            ((16 : ℝ) ^ (6 / 5 : ℝ) *
              (jumpGen1 (6 / 5) bspline (16 * z 0 - ij.1) * bspline (16 * z 1 - ij.2)
                + bspline (16 * z 0 - ij.1) * jumpGen1 (6 / 5) bspline (16 * z 1 - ij.2)))) :
    0 ≤ jumpGen (6 / 5) fracKernel z := by
  have hδR : (0 : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hδ
  have hspx : ∀ w ∈ Msp, 0 < w.x := fun w hw => (hsp w hw).1
  have hbax : ∀ w ∈ Mba, 0 < w.x := fun w hw => (hba w hw).1
  have hspF : ∀ w ∈ Msp, (w.a, w.b) ∈ modelFinset :=
    fun w hw => mem_modelFinset (hsp w hw).2.1 (hsp w hw).2.2
  have hbaF : ∀ w ∈ Mba, (w.a, w.b) ∈ modelFinset :=
    fun w hw => mem_modelFinset (hba w hw).2.1 (hba w hw).2.2
  -- the model's value is the sum of its coefficients against the monomials
  have hval : ∀ s t : ℝ, leafValR Msp Mba s t
      = ∑ p ∈ modelFinset, leafCoR Msp Mba p * s ^ p.1 * t ^ p.2 := by
    intro s t
    rw [leafValR, termsValR_eq_sum hspF, termsValR_eq_sum hbaF, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by rw [leafCoR]; ring
  -- the rational check implies the real one
  have hmem := leafCoI_mem hL hspx hbax
  have hlo : ((leafCoI L Msp Mba (0, 0)).lo : ℝ) ≤ leafCoR Msp Mba (0, 0) := (hmem (0, 0)).1
  have hterm : ∀ p ∈ modelExps.toFinset,
      |leafCoR Msp Mba p| * (δ : ℝ) ^ (p.1 + p.2)
        ≤ ((leafCoI L Msp Mba p).absmax : ℝ) * (δ : ℝ) ^ (p.1 + p.2) := fun p _ =>
    mul_le_mul_of_nonneg_right (RatItv.abs_le_absmax (hmem p)) (by positivity)
  have hlist : (((modelExps.map fun p =>
        (leafCoI L Msp Mba p).absmax * δ ^ (p.1 + p.2)).sum : ℚ) : ℝ)
      = ∑ p ∈ modelExps.toFinset, ((leafCoI L Msp Mba p).absmax : ℝ) * (δ : ℝ) ^ (p.1 + p.2) := by
    rw [← List.sum_toFinset _ modelExps_nodup, Rat.cast_sum]
    exact Finset.sum_congr rfl fun p _ => by push_cast; ring
  have hchkR : (0 : ℝ) ≤ ((leafCoI L Msp Mba (0, 0)).lo : ℝ)
      - (∑ p ∈ modelExps.toFinset, ((leafCoI L Msp Mba p).absmax : ℝ) * (δ : ℝ) ^ (p.1 + p.2))
      - (err : ℝ) := by
    have h : (0 : ℝ) ≤ ((leafCheckQ L Msp Mba δ err : ℚ) : ℝ) := by exact_mod_cast hchk
    rwa [leafCheckQ, Rat.cast_sub, Rat.cast_sub, hlist] at h
  have hcheck : 0 ≤ leafCoR Msp Mba (0, 0)
      - (∑ p ∈ modelFinset.erase (0, 0), |leafCoR Msp Mba p| * (δ : ℝ) ^ (p.1 + p.2))
      - (err : ℝ) := by
    rw [modelFinset_erase]
    have hle := Finset.sum_le_sum hterm
    linarith
  exact jumpGen_fracKernel_nonneg_of_centred hS hSle hr₀ zero_mem_modelFinset
    (leafCoR Msp Mba) hcheck h0 h1 hz hu hv (by rw [← hval]; exact hmodel)

end CenteredMaximal.Fractional

end
