/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.MajorRow

/-!
# The majorization certificate of the `α = 6/5` comparison kernel, shard 4

One of the `8` shards of the `814` triangles of the majorization certificate.  See
`CenteredMaximal.Fractional.MajorRow` for what a row means and
`CenteredMaximal.Fractional.MajorKernel` for the assembled certificate.

The rows are checked in **groups of eight**, not all at once.  The kernel's `whnf` cache is kept
for the whole of one declaration, so a single `decide +kernel` over a hundred triangles holds every
intermediate polynomial of every triangle live at once: `20` triangles in one reduction cost `20 s`
of user time and `47 s` of system time, against `16 s` and `2.7 s` as four reductions of five.
-/

@[expose] public section

namespace CenteredMaximal.Fractional

/-- Group `51` of the majorization certificate: `8` triangles. -/
def majGroup51 : List MajRow :=
  [⟨8, 12, 0, 84, false, 0, 0, 1⟩, ⟨8, 12, 0, 88, true, 0, 0, 1⟩, ⟨8, 13, 0, 88, false, 0, 0, 1⟩,
   ⟨8, 13, 0, 92, true, 0, 0, 1⟩, ⟨8, 14, 0, 92, false, 0, 0, 1⟩, ⟨8, 14, 0, 96, true, 0, 0, 1⟩,
   ⟨8, 15, 0, 96, false, 0, 0, 1⟩, ⟨8, 15, 0, 100, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup51_ok : majGroup51.all (fun r => r.check) = true := by decide +kernel

/-- Group `52` of the majorization certificate: `8` triangles. -/
def majGroup52 : List MajRow :=
  [⟨8, 16, 0, 100, false, 0, 0, 1⟩, ⟨8, 16, 0, 104, true, 0, 0, 1⟩,
   ⟨8, 17, 0, 104, false, 0, 0, 1⟩, ⟨8, 17, 0, 108, true, 0, 0, 1⟩,
   ⟨8, 18, 0, 108, false, 0, 0, 1⟩, ⟨8, 18, 0, 112, true, 0, 0, 1⟩,
   ⟨8, 19, 0, 112, false, 0, 0, 1⟩, ⟨9, 0, 1, 40, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup52_ok : majGroup52.all (fun r => r.check) = true := by decide +kernel

/-- Group `53` of the majorization certificate: `8` triangles. -/
def majGroup53 : List MajRow :=
  [⟨9, 0, 1, 44, true, 0, 0, 1⟩, ⟨9, 1, 1, 44, false, 0, 0, 1⟩, ⟨9, 1, 1, 48, true, 0, 0, 1⟩,
   ⟨9, 2, 1, 48, false, 0, 0, 1⟩, ⟨9, 2, 1, 52, true, 0, 0, 1⟩, ⟨9, 3, 1, 52, false, 0, 0, 1⟩,
   ⟨9, 3, 1, 56, true, 0, 0, 1⟩, ⟨9, 4, 1, 56, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup53_ok : majGroup53.all (fun r => r.check) = true := by decide +kernel

/-- Group `54` of the majorization certificate: `8` triangles. -/
def majGroup54 : List MajRow :=
  [⟨9, 4, 1, 60, true, 0, 0, 1⟩, ⟨9, 5, 1, 60, false, 0, 0, 1⟩, ⟨9, 5, 1, 64, true, 0, 0, 1⟩,
   ⟨9, 6, 1, 64, false, 0, 0, 1⟩, ⟨9, 6, 0, 68, true, 0, 0, 1⟩, ⟨9, 7, 0, 68, false, 0, 0, 1⟩,
   ⟨9, 7, 0, 72, true, 0, 0, 1⟩, ⟨9, 8, 0, 72, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup54_ok : majGroup54.all (fun r => r.check) = true := by decide +kernel

/-- Group `55` of the majorization certificate: `8` triangles. -/
def majGroup55 : List MajRow :=
  [⟨9, 8, 0, 76, true, 0, 0, 1⟩, ⟨9, 9, 0, 76, false, 0, 0, 1⟩, ⟨9, 9, 0, 80, true, 0, 0, 1⟩,
   ⟨9, 10, 0, 80, false, 0, 0, 1⟩, ⟨9, 10, 0, 84, true, 0, 0, 1⟩, ⟨9, 11, 0, 84, false, 0, 0, 1⟩,
   ⟨9, 11, 0, 88, true, 0, 0, 1⟩, ⟨9, 12, 0, 88, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup55_ok : majGroup55.all (fun r => r.check) = true := by decide +kernel

/-- Group `56` of the majorization certificate: `8` triangles. -/
def majGroup56 : List MajRow :=
  [⟨9, 12, 0, 92, true, 0, 0, 1⟩, ⟨9, 13, 0, 92, false, 0, 0, 1⟩, ⟨9, 13, 0, 96, true, 0, 0, 1⟩,
   ⟨9, 14, 0, 96, false, 0, 0, 1⟩, ⟨9, 14, 0, 100, true, 0, 0, 1⟩,
   ⟨9, 15, 0, 100, false, 0, 0, 1⟩, ⟨9, 15, 0, 104, true, 0, 0, 1⟩,
   ⟨9, 16, 0, 104, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup56_ok : majGroup56.all (fun r => r.check) = true := by decide +kernel

/-- Group `57` of the majorization certificate: `8` triangles. -/
def majGroup57 : List MajRow :=
  [⟨9, 16, 0, 108, true, 0, 0, 1⟩, ⟨9, 17, 0, 108, false, 0, 0, 1⟩,
   ⟨9, 17, 0, 112, true, 0, 0, 1⟩, ⟨9, 18, 0, 112, false, 0, 0, 1⟩,
   ⟨10, 0, 1, 44, false, 0, 0, 1⟩, ⟨10, 0, 1, 48, true, 0, 0, 1⟩, ⟨10, 1, 1, 48, false, 0, 0, 1⟩,
   ⟨10, 1, 1, 52, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup57_ok : majGroup57.all (fun r => r.check) = true := by decide +kernel

/-- Group `58` of the majorization certificate: `8` triangles. -/
def majGroup58 : List MajRow :=
  [⟨10, 2, 1, 52, false, 0, 0, 1⟩, ⟨10, 2, 1, 56, true, 0, 0, 1⟩, ⟨10, 3, 1, 56, false, 0, 0, 1⟩,
   ⟨10, 3, 1, 60, true, 0, 0, 1⟩, ⟨10, 4, 1, 60, false, 0, 0, 1⟩, ⟨10, 4, 1, 64, true, 0, 0, 1⟩,
   ⟨10, 5, 1, 64, false, 0, 0, 1⟩, ⟨10, 5, 0, 68, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup58_ok : majGroup58.all (fun r => r.check) = true := by decide +kernel

/-- Group `59` of the majorization certificate: `8` triangles. -/
def majGroup59 : List MajRow :=
  [⟨10, 6, 0, 68, false, 0, 0, 1⟩, ⟨10, 6, 0, 72, true, 0, 0, 1⟩, ⟨10, 7, 0, 72, false, 0, 0, 1⟩,
   ⟨10, 7, 0, 76, true, 0, 0, 1⟩, ⟨10, 8, 0, 76, false, 0, 0, 1⟩, ⟨10, 8, 0, 80, true, 0, 0, 1⟩,
   ⟨10, 9, 0, 80, false, 0, 0, 1⟩, ⟨10, 9, 0, 84, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup59_ok : majGroup59.all (fun r => r.check) = true := by decide +kernel

/-- Group `60` of the majorization certificate: `8` triangles. -/
def majGroup60 : List MajRow :=
  [⟨10, 10, 0, 84, false, 0, 0, 1⟩, ⟨10, 10, 0, 88, true, 0, 0, 1⟩,
   ⟨10, 11, 0, 88, false, 0, 0, 1⟩, ⟨10, 11, 0, 92, true, 0, 0, 1⟩,
   ⟨10, 12, 0, 92, false, 0, 0, 1⟩, ⟨10, 12, 0, 96, true, 0, 0, 1⟩,
   ⟨10, 13, 0, 96, false, 0, 0, 1⟩, ⟨10, 13, 0, 100, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup60_ok : majGroup60.all (fun r => r.check) = true := by decide +kernel

/-- Group `61` of the majorization certificate: `8` triangles. -/
def majGroup61 : List MajRow :=
  [⟨10, 14, 0, 100, false, 0, 0, 1⟩, ⟨10, 14, 0, 104, true, 0, 0, 1⟩,
   ⟨10, 15, 0, 104, false, 0, 0, 1⟩, ⟨10, 15, 0, 108, true, 0, 0, 1⟩,
   ⟨10, 16, 0, 108, false, 0, 0, 1⟩, ⟨10, 16, 0, 112, true, 0, 0, 1⟩,
   ⟨10, 17, 0, 112, false, 0, 0, 1⟩, ⟨11, 0, 1, 48, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup61_ok : majGroup61.all (fun r => r.check) = true := by decide +kernel

/-- Group `62` of the majorization certificate: `8` triangles. -/
def majGroup62 : List MajRow :=
  [⟨11, 0, 1, 52, true, 0, 0, 1⟩, ⟨11, 1, 1, 52, false, 0, 0, 1⟩, ⟨11, 1, 1, 56, true, 0, 0, 1⟩,
   ⟨11, 2, 1, 56, false, 0, 0, 1⟩, ⟨11, 2, 1, 60, true, 0, 0, 1⟩, ⟨11, 3, 1, 60, false, 0, 0, 1⟩,
   ⟨11, 3, 1, 64, true, 0, 0, 1⟩, ⟨11, 4, 1, 64, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup62_ok : majGroup62.all (fun r => r.check) = true := by decide +kernel

/-- Shard `4` of the majorization certificate: `96` triangles. -/
def majShard4 : List MajRow :=
  majGroup51 ++ majGroup52 ++ majGroup53 ++ majGroup54 ++ majGroup55 ++ majGroup56 ++ majGroup57 ++
    majGroup58 ++ majGroup59 ++ majGroup60 ++ majGroup61 ++ majGroup62

set_option maxRecDepth 4000 in
theorem majShard4_length : majShard4.length = 96 := by rfl

/-- **Every triangle of shard `4` passes its Bernstein test.** -/
theorem majShard4_ok : majShard4.all (fun r => r.check) = true := by
  simp only [majShard4, List.all_append, Bool.and_eq_true, majGroup51_ok,
    majGroup52_ok,
    majGroup53_ok,
    majGroup54_ok,
    majGroup55_ok,
    majGroup56_ok,
    majGroup57_ok,
    majGroup58_ok,
    majGroup59_ok,
    majGroup60_ok,
    majGroup61_ok,
    majGroup62_ok,
    and_self]

end CenteredMaximal.Fractional

end
