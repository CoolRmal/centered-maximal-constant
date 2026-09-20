/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.FifthTable0
public import CenteredMaximal.Fractional.FifthTable1
public import CenteredMaximal.Fractional.FifthTable2
public import CenteredMaximal.Fractional.FifthTable3
public import CenteredMaximal.Fractional.FifthTable4
public import CenteredMaximal.Fractional.FifthTable5
public import CenteredMaximal.Fractional.FifthTable6
public import CenteredMaximal.Fractional.FifthTable7

/-!
# The fifth-root enclosure table of the `α = 6/5` generator certificate

The generator certificate for the comparison kernel `fracKernel` bounds the fractional generator
below on `4582` dyadic rectangles.  Each rectangle's bound is a rational expression in

* `|x| ^ (9/5)`, `|x| ^ (4/5)`, `|x| ^ (-1/5)`, `|x| ^ (-6/5)` — the four cubic Taylor
  coefficients of the elementary function `F(x) = |x| ^ (3 − α)` of the spline generator, at the
  centre `x` of a dyadic interval,
* `(|x| − δ) ^ (-11/5)` — the fourth-derivative factor of the Taylor remainder on that interval,
* `r ^ (-12/5)` and `r ^ (-17/5)` — the intrinsic diamond-power density and its radial derivative.

Across the whole certificate these are only **`11045` distinct real numbers**, because a dyadic
interval's centre and half-width depend on the subdivision, not on the rectangle: the `25582`
one-dimensional evaluation sites of the `4582` rectangles collapse to `2321` distinct
`(centre, half-width)` pairs, and the base contributes `287` distinct radii.  Enclosing each
number once, here, instead of once per use is what makes the certificate affordable at all.

## Main results

* `encTable`: the `11045` rows, as eight shards of about `1381` rows each.
* `encTable_ok`: **all `11045` rows verify**, assembled from the eight shard checks by
  `List.all_append` — no row is reduced twice.
* `encTable_sound`: **what the table buys**: for every row, the *real* number
  `(num / den) ^ (exp / 5)` lies between the row's two rational ends.

## Measured cost

One row costs `11.8 ms` of kernel time at precision `12`: the eight shards build in
`15.4, 15.4, 14.4, 15.9, 16.0, 16.9, 17.1, 19.6` seconds of wall clock, `130.7 s` in total, each
against a `1.5 s` baseline for the enclosure file alone.  The shards must be built **one at a
time**: eight concurrent `decide +kernel` reductions of this size thrash memory and do not finish
in ten minutes.  The dominant cost per row is the single integer fifth root of a `200`-bit number
inside `CenteredMaximal.Fractional.rpowFifthEnc`, which is why `FifthEnc.check` is written to force
only the lower end of the enclosure and to recover the upper end from `rpowFifthEnc_snd_eq`.
-/

@[expose] public section

namespace CenteredMaximal.Fractional

/-- The `11045` fifth-root enclosures the `α = 6/5` generator certificate consumes. -/
def encTable : List FifthEnc :=
  encShard0 ++ encShard1 ++ encShard2 ++ encShard3 ++ encShard4 ++ encShard5 ++ encShard6 ++
    encShard7

/-- **The table has `11045` rows.**  Proved from the shard lengths, so no `11045`-element list is
ever reduced. -/
theorem encTable_length : encTable.length = 11045 := by
  simp only [encTable, List.length_append, encShard0_length, encShard1_length, encShard2_length,
    encShard3_length, encShard4_length, encShard5_length, encShard6_length, encShard7_length]

/-- **Every one of the `11045` rows verifies.**  Assembled from the eight shard checks by
`List.all_append`; nothing is decided again here. -/
theorem encTable_ok : encTable.all (fun c => c.check 12) = true := by
  simp only [encTable, List.all_append, Bool.and_eq_true, encShard0_ok, encShard1_ok,
    encShard2_ok, encShard3_ok, encShard4_ok, encShard5_ok, encShard6_ok, encShard7_ok,
    and_self]

/-- **What the table buys.**  Every row of `encTable` with positive numerator and denominator
brackets the real number `(num / den) ^ (exp / 5)` between its two stored rational ends.  This is
the interface the `4582` rectangle bounds consume: the certificate never evaluates a fifth root,
it only reads a pair of rationals out of this table. -/
theorem encTable_sound {c : FifthEnc} (hc : c ∈ encTable) (h1 : 0 < c.num) (h2 : 0 < c.den) :
    ((c.loQ 12 : ℚ) : ℝ) ≤ (c.base : ℝ) ^ ((c.exp : ℝ) / 5) ∧
      (c.base : ℝ) ^ ((c.exp : ℝ) / 5) ≤ ((c.hiQ 12 : ℚ) : ℝ) :=
  FifthEnc.sound_of_all encTable_ok hc h1 h2

end CenteredMaximal.Fractional

end
