/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.MajorShard0
public import CenteredMaximal.Fractional.MajorShard1
public import CenteredMaximal.Fractional.MajorShard2
public import CenteredMaximal.Fractional.MajorShard3
public import CenteredMaximal.Fractional.MajorShard4
public import CenteredMaximal.Fractional.MajorShard5
public import CenteredMaximal.Fractional.MajorShard6
public import CenteredMaximal.Fractional.MajorShard7

/-!
# The majorization certificate of the `α = 6/5` comparison kernel

This file assembles the `814` triangles of the majorization certificate and deduces the two
pointwise bounds the comparison argument needs:

`0 ≤ fracKernel z` for `z ≠ 0`, and `1 ≤ fracKernel z` on the punctured unit diamond.

## The covering

By `fracKernel_abs` only the closed first quadrant matters, and by `fracKernel_eq_zero_of_le` only
the diamond `|z₀| + |z₁| < 7/4` does.  Writing `u = 16 |z₀|`, `v = 16 |z₁|`, the cell of a point is
chosen by `exists_cell`, which returns `u = k + s` with `0 ≤ s ≤ 1` and — the point of the lemma —
`s > 0` whenever `u > 0`.  That last clause is what makes the covering work at the cell corners: it
forces `k + l < u + v`, so `k + l ≤ 27` throughout the support and `k + l ≤ 15` inside the unit
diamond, which is exactly the range of cells the certificate carries.  The two halves of a cell are
separated by `s + t ≤ 1` against `s + t > 1`.

One cell, `(11, 11)`, is not certified by the degree-`6` Bernstein test on its two unit triangles:
the tangent minorant of the base is too weak over a whole cell at that radius, and no choice of
tangent radius repairs it (the deficit is about `-0.021`, and degree elevation diverges, so the
minorant really is negative somewhere on the triangle).  That cell is therefore covered by a
uniform `4 × 4` refinement, `32` triangles of side `1/4`, and `exists_subcell` locates the
sub-square by the same ceiling rule at scale `4`.  Nothing else is special, and no triangle needs
any degree elevation.

## Main results

* `majRows`, `majRows_ok`: the `814` triangles and the fact that every one passes its check.
* `majOk`: **the covering is complete** — a single kernel reduction verifying that the certificate
  really does carry a row for every cell and every sub-square the covering rule can produce, with
  the right target.
* `exists_row_cover`: for `z ≠ 0` inside the support there is a row of the certificate whose
  triangle contains the folded point, and its target bounds `fracKernel z` below.
* `fracKernel_nonneg`, `one_le_fracKernel`: **the two headline bounds.**

## The hypothesis `z ≠ 0` is necessary

`fracKernel 0 = -153740147944789861/6250000000000000 = -24.5984…`: the truncated base is a
`Real.rpow`, and `(0 : ℝ) ^ (-6/5) = 0` by definition, so at the origin the base contributes
nothing while the spline part contributes `∑_{|i|,|j| ≤ 1} C_{ij} β(i) β(j) < 0`.  The origin is a
single point, so this costs the comparison argument nothing, but `0 ≤ fracKernel z` is false
without a hypothesis.
-/

@[expose] public section

noncomputable section

open CenteredMaximal.Cauchy

namespace CenteredMaximal.Fractional

/-! ### The assembled certificate -/

/-- The `814` triangles of the majorization certificate. -/
def majRows : List MajRow :=
  majShard0 ++ majShard1 ++ majShard2 ++ majShard3 ++ majShard4 ++ majShard5 ++ majShard6 ++
    majShard7

/-- **The certificate has `814` triangles.**  Proved from the shard lengths. -/
theorem majRows_length : majRows.length = 814 := by
  simp only [majRows, List.length_append, majShard0_length, majShard1_length, majShard2_length,
    majShard3_length, majShard4_length, majShard5_length, majShard6_length, majShard7_length]

/-- **Every triangle of the certificate passes its Bernstein test.**  Assembled from the eight
shard checks by `List.all_append`; nothing is decided again here. -/
theorem majRows_ok : majRows.all (fun r => r.check) = true := by
  simp only [majRows, List.all_append, Bool.and_eq_true, majShard0_ok, majShard1_ok, majShard2_ok,
    majShard3_ok, majShard4_ok, majShard5_ok, majShard6_ok, majShard7_ok, and_self]

/-! ### Looking a triangle up -/

/-- The triangle of the certificate at a given cell, half and sub-square. -/
def majFind (k l : ℕ) (up : Bool) (p q h : ℚ) : Option MajRow :=
  majRows.find? fun r => r.k == k && r.l == l && r.up == up && r.p == p && r.q == q && r.h == h

/-- The target the certificate asserts on a given half of a given cell: `1` exactly when the whole
half lies inside the unit diamond. -/
def majTgt (k l : ℕ) (up : Bool) : ℕ := if (if up then k + l + 2 else k + l + 1) ≤ 16 then 1 else 0

theorem majTgt_false (k l : ℕ) : majTgt k l false = if k + l + 1 ≤ 16 then 1 else 0 := rfl

theorem majTgt_true (k l : ℕ) : majTgt k l true = if k + l + 2 ≤ 16 then 1 else 0 := rfl

/-- One key of the covering: the triangle exists and has the expected target. -/
def majKeyOk (k l : ℕ) (up : Bool) (p q h : ℚ) : Bool :=
  match majFind k l up p q h with
  | some r => r.tgt == majTgt k l up
  | none => false

/-- **The keys the covering rule can produce.**  For every cell of the support the certificate
carries both halves, except the refined cell `(11, 11)`, where it carries both halves of each of
the `16` sub-squares of side `1/4`. -/
def majOk : Bool :=
  (List.range 28).all fun k => (List.range 28).all fun l =>
    if k == 11 && l == 11 then
      (List.range 4).all fun a => (List.range 4).all fun b =>
        majKeyOk 11 11 false ((a : ℚ) / 4) ((b : ℚ) / 4) (1 / 4) &&
          majKeyOk 11 11 true ((a : ℚ) / 4) ((b : ℚ) / 4) (1 / 4)
    else
      (if k + l ≤ 27 then majKeyOk k l false 0 0 1 else true) &&
        (if k + l ≤ 26 then majKeyOk k l true 0 0 1 else true)

set_option maxRecDepth 8000000 in
/-- **The covering is complete.** -/
theorem majOk_true : majOk = true := by decide +kernel

private theorem majFind_spec {k l : ℕ} {up : Bool} {p q h : ℚ} {r : MajRow}
    (hf : majFind k l up p q h = some r) :
    r ∈ majRows ∧ r.k = k ∧ r.l = l ∧ r.up = up ∧ r.p = p ∧ r.q = q ∧ r.h = h := by
  refine ⟨List.mem_of_find?_eq_some hf, ?_⟩
  have hp := List.find?_some hf
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  tauto

/-- What one key of the covering buys: a checked row with the requested geometry and target. -/
private theorem majKey_spec {k l : ℕ} {up : Bool} {p q h : ℚ}
    (hok : majKeyOk k l up p q h = true) :
    ∃ r : MajRow, r ∈ majRows ∧ r.check = true ∧ r.k = k ∧ r.l = l ∧ r.up = up ∧ r.p = p
      ∧ r.q = q ∧ r.h = h ∧ r.tgt = majTgt k l up := by
  rcases hx : majFind k l up p q h with _ | r
  · rw [majKeyOk, hx] at hok
    simp at hok
  · obtain ⟨hm, h1, h2, h3, h4, h5, h6⟩ := majFind_spec hx
    refine ⟨r, hm, List.all_eq_true.1 majRows_ok r hm, h1, h2, h3, h4, h5, h6, ?_⟩
    rw [majKeyOk, hx] at hok
    simpa using hok

/-! ### Locating a point in the grid -/

/-- **The cell of a nonnegative coordinate.**  `u = k + s` with `0 ≤ s ≤ 1`, and `s > 0` unless
`u = 0`: the cell is the one *ending* at `u`, not the one starting there, which is what keeps
`k + l` strictly below `u + v` and so inside the range the certificate carries. -/
theorem exists_cell {u : ℝ} (hu : 0 ≤ u) :
    ∃ (k : ℕ) (s : ℝ), 0 ≤ s ∧ s ≤ 1 ∧ u = (k : ℝ) + s ∧ (0 < u → 0 < s) := by
  rcases eq_or_lt_of_le hu with h | h
  · refine ⟨0, 0, le_refl 0, zero_le_one, ?_, ?_⟩
    · rw [← h]
      norm_num
    · intro hc
      rw [← h] at hc
      exact absurd hc (lt_irrefl 0)
  · have hc : (0 : ℤ) < ⌈u⌉ := by rwa [Int.lt_ceil, Int.cast_zero]
    have hk : ((⌈u⌉ - 1).toNat : ℤ) = ⌈u⌉ - 1 := Int.toNat_of_nonneg (by omega)
    have hkR : (((⌈u⌉ - 1).toNat : ℕ) : ℝ) = (⌈u⌉ : ℝ) - 1 := by
      have h3 : ((((⌈u⌉ - 1).toNat : ℕ) : ℤ) : ℝ) = ((⌈u⌉ - 1 : ℤ) : ℝ) := by rw [hk]
      push_cast at h3
      exact h3
    have hlt : (⌈u⌉ : ℝ) - 1 < u := by
      have := Int.ceil_lt_add_one u
      linarith
    have hle : u ≤ (⌈u⌉ : ℝ) := Int.le_ceil u
    refine ⟨(⌈u⌉ - 1).toNat, u - ((⌈u⌉ : ℝ) - 1), by linarith, by linarith, ?_, fun _ => by
      linarith⟩
    rw [hkR]
    ring

/-- **The sub-square of a cell coordinate at scale `M`.** -/
theorem exists_subcell {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) {M : ℕ} (hM : 0 < M) :
    ∃ a : ℕ, a < M ∧ (a : ℝ) / M ≤ s ∧ s ≤ ((a : ℝ) + 1) / M := by
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  obtain ⟨a, σ, hσ0, hσ1, hms, hσpos⟩ := exists_cell (u := (M : ℝ) * s) (by positivity)
  have haM : a < M := by
    rcases eq_or_lt_of_le hs with h | h
    · have : (a : ℝ) + σ = 0 := by rw [← hms, ← h]; ring
      have ha0 : (a : ℝ) = 0 := by linarith
      have : a = 0 := by exact_mod_cast ha0
      omega
    · have hpos : 0 < (M : ℝ) * s := by positivity
      have hσ : 0 < σ := hσpos hpos
      have : (a : ℝ) < (M : ℝ) := by
        have h1 : (a : ℝ) < (M : ℝ) * s := by linarith
        nlinarith [hMR, hs1]
      exact_mod_cast this
  refine ⟨a, haM, ?_, ?_⟩
  · rw [div_le_iff₀ hMR]
    nlinarith
  · rw [le_div_iff₀ hMR]
    nlinarith

/-! ### The covering -/

set_option maxHeartbeats 1000000 in
/-- **The certificate covers the support.**  For `z ≠ 0` inside the diamond of radius `7/4` there
is a triangle of the certificate containing the folded, scaled point, and its target is a lower
bound for `fracKernel z` — equal to `1` whenever `z` lies in the unit diamond. -/
theorem exists_row_cover {z : Fin 2 → ℝ} (hz : z ≠ 0) (hR : diamondNorm z < 7 / 4) :
    ∃ r : MajRow, r ∈ majRows ∧ (r.tgt : ℝ) ≤ fracKernel z
      ∧ (diamondNorm z ≤ 1 → r.tgt = 1) := by
  have hdn : diamondNorm z = |z 0| + |z 1| := rfl
  have hpos : 0 < diamondNorm z := diamondNorm_pos hz
  obtain ⟨k, s, hs0, hs1, hks, hspos⟩ := exists_cell (u := 16 * |z 0|) (by positivity)
  obtain ⟨l, t, ht0, ht1, hlt, htpos⟩ := exists_cell (u := 16 * |z 1|) (by positivity)
  have hsum16 : (k : ℝ) + s + ((l : ℝ) + t) = 16 * diamondNorm z := by
    rw [hdn, ← hks, ← hlt]
    ring
  have hst : 0 < s + t := by
    rcases eq_or_lt_of_le (abs_nonneg (z 0)) with h0 | h0
    · have : 0 < |z 1| := by rw [hdn] at hpos; linarith
      have := htpos (by positivity)
      linarith
    · have := hspos (by positivity)
      linarith
  have hklR : (k : ℝ) + (l : ℝ) < 28 := by
    have : 16 * diamondNorm z < 28 := by linarith
    linarith
  have hkl27 : k + l ≤ 27 := by
    have : ((k + l : ℕ) : ℝ) < 28 := by push_cast; linarith
    have : (k + l : ℕ) < 28 := by exact_mod_cast this
    omega
  have hk28 : k < 28 := by omega
  have hl28 : l < 28 := by omega
  have htgtF : diamondNorm z ≤ 1 → majTgt k l false = 1 := by
    intro h1
    have h16 : (k : ℝ) + (l : ℝ) + (s + t) ≤ 16 := by linarith
    have hc : ((k + l : ℕ) : ℝ) < 16 := by push_cast; linarith
    have h2 : k + l < 16 := by exact_mod_cast hc
    rw [majTgt_false, if_pos (by omega)]
  have htgtT : diamondNorm z ≤ 1 → 1 < s + t → majTgt k l true = 1 := by
    intro h1 hgt
    have h16 : (k : ℝ) + (l : ℝ) + (s + t) ≤ 16 := by linarith
    have hc : ((k + l : ℕ) : ℝ) < 15 := by push_cast; linarith
    have h2 : k + l < 15 := by exact_mod_cast hc
    rw [majTgt_true, if_pos (by omega)]
  have hallk := List.all_eq_true.1 majOk_true k (List.mem_range.2 hk28)
  have hkey := List.all_eq_true.1 hallk l (List.mem_range.2 hl28)
  by_cases hsp : k = 11 ∧ l = 11
  · -- the refined cell
    obtain ⟨rfl, rfl⟩ := hsp
    rw [if_pos (by simp)] at hkey
    obtain ⟨a, haM, hap, hap1⟩ := exists_subcell hs0 hs1 (M := 4) (by norm_num)
    obtain ⟨b, hbM, hbq, hbq1⟩ := exists_subcell ht0 ht1 (M := 4) (by norm_num)
    have hka := List.all_eq_true.1 hkey a (List.mem_range.2 haM)
    have hkb := List.all_eq_true.1 hka b (List.mem_range.2 hbM)
    rw [Bool.and_eq_true] at hkb
    have hnot : ¬ diamondNorm z ≤ 1 := by
      intro h1
      have h16 : (11 : ℝ) + (11 : ℝ) + (s + t) ≤ 16 := by
        have := hsum16
        push_cast at this ⊢
        linarith
      linarith
    have hp4 : (((a : ℚ) / 4 : ℚ) : ℝ) = (a : ℝ) / 4 := by push_cast; ring
    have hq4 : (((b : ℚ) / 4 : ℚ) : ℝ) = (b : ℝ) / 4 := by push_cast; ring
    have hh4 : (((1 / 4 : ℚ) : ℚ) : ℝ) = 1 / 4 := by norm_num
    rcases le_or_gt (s - (a : ℝ) / 4 + (t - (b : ℝ) / 4)) (1 / 4) with hlow | hhigh
    · obtain ⟨r, hm, hck, hrk, hrl, hru, hrp, hrq, hrh, _⟩ := majKey_spec hkb.1
      refine ⟨r, hm, ?_, fun h1 => absurd h1 hnot⟩
      refine MajRow.sound_down hck hru hpos ?_ ?_ hs0 hs1 ht0 ht1 ?_ ?_ ?_ ?_
      · rw [hrk, hks]
      · rw [hrl, hlt]
      · rw [hrh, hh4]; norm_num
      · rw [hrp, hp4]; exact hap
      · rw [hrq, hq4]; exact hbq
      · rw [hrp, hrq, hrh, hp4, hq4, hh4]; exact hlow
    · obtain ⟨r, hm, hck, hrk, hrl, hru, hrp, hrq, hrh, _⟩ := majKey_spec hkb.2
      refine ⟨r, hm, ?_, fun h1 => absurd h1 hnot⟩
      refine MajRow.sound_up hck hru hpos ?_ ?_ hs0 hs1 ht0 ht1 ?_ ?_ ?_ ?_
      · rw [hrk, hks]
      · rw [hrl, hlt]
      · rw [hrh, hh4]; norm_num
      · rw [hrp, hrh, hp4, hh4]; linarith
      · rw [hrq, hrh, hq4, hh4]; linarith
      · rw [hrp, hrq, hrh, hp4, hq4, hh4]; linarith
  · -- an unrefined cell
    rw [if_neg (by simpa [Bool.and_eq_true, beq_iff_eq] using hsp)] at hkey
    rw [Bool.and_eq_true] at hkey
    have hz0 : (((0 : ℚ) : ℚ) : ℝ) = 0 := by norm_num
    have hz1 : (((1 : ℚ) : ℚ) : ℝ) = 1 := by norm_num
    rcases le_or_gt (s + t) 1 with hlow | hhigh
    · have hk1 : majKeyOk k l false 0 0 1 = true := by
        have hx := hkey.1
        rwa [if_pos hkl27] at hx
      obtain ⟨r, hm, hck, hrk, hrl, hru, hrp, hrq, hrh, hrt⟩ := majKey_spec hk1
      refine ⟨r, hm, ?_, fun h1 => by rw [hrt]; exact htgtF h1⟩
      refine MajRow.sound_down hck hru hpos ?_ ?_ hs0 hs1 ht0 ht1 ?_ ?_ ?_ ?_
      · rw [hrk, hks]
      · rw [hrl, hlt]
      · rw [hrh, hz1]; norm_num
      · rw [hrp, hz0]; exact hs0
      · rw [hrq, hz0]; exact ht0
      · rw [hrp, hrq, hrh, hz0, hz1]; linarith
    · have hkl26 : k + l ≤ 26 := by
        have : ((k + l : ℕ) : ℝ) < 27 := by push_cast; linarith
        have : (k + l : ℕ) < 27 := by exact_mod_cast this
        omega
      have hk1 : majKeyOk k l true 0 0 1 = true := by
        have hx := hkey.2
        rwa [if_pos hkl26] at hx
      obtain ⟨r, hm, hck, hrk, hrl, hru, hrp, hrq, hrh, hrt⟩ := majKey_spec hk1
      refine ⟨r, hm, ?_, fun h1 => by rw [hrt]; exact htgtT h1 hhigh⟩
      refine MajRow.sound_up hck hru hpos ?_ ?_ hs0 hs1 ht0 ht1 ?_ ?_ ?_ ?_
      · rw [hrk, hks]
      · rw [hrl, hlt]
      · rw [hrh, hz1]; norm_num
      · rw [hrp, hrh, hz0, hz1]; linarith
      · rw [hrq, hrh, hz0, hz1]; linarith
      · rw [hrp, hrq, hrh, hz0, hz1]; linarith

/-! ### The two headline bounds -/

/-- **The comparison kernel is nonnegative away from the origin.**  Outside the diamond of radius
`7/4` it vanishes; inside, a triangle of the certificate bounds it below by its target, which is
`0` or `1`.  The hypothesis cannot be dropped: `fracKernel 0 = -24.5984…`, because the truncated
base is a `Real.rpow` and `(0 : ℝ) ^ (-6/5) = 0`. -/
theorem fracKernel_nonneg {z : Fin 2 → ℝ} (hz : z ≠ 0) : 0 ≤ fracKernel z := by
  rcases le_or_gt (7 / 4 : ℝ) (diamondNorm z) with h | h
  · rw [fracKernel_eq_zero_of_le h]
  · obtain ⟨r, _, hle, _⟩ := exists_row_cover hz h
    have h0 : (0 : ℝ) ≤ (r.tgt : ℝ) := Nat.cast_nonneg _
    linarith

/-- **The comparison kernel dominates `1` on the punctured unit diamond.**  This is what makes the
kernel majorize the centred maximal function. -/
theorem one_le_fracKernel {z : Fin 2 → ℝ} (hz : diamondNorm z ≤ 1) (hz0 : z ≠ 0) :
    1 ≤ fracKernel z := by
  obtain ⟨r, _, hle, htg⟩ := exists_row_cover hz0 (by linarith)
  rw [htg hz] at hle
  simpa using hle

end CenteredMaximal.Fractional

end

end
