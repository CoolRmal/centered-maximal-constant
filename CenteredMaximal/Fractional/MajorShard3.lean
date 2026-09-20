/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.MajorRow

/-!
# The majorization certificate of the `α = 6/5` comparison kernel, shard 3

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

/-- Group `38` of the majorization certificate: `8` triangles. -/
def majGroup38 : List MajRow :=
  [⟨6, 2, 1, 36, false, 0, 0, 1⟩, ⟨6, 2, 1, 40, true, 0, 0, 1⟩, ⟨6, 3, 1, 40, false, 0, 0, 1⟩,
   ⟨6, 3, 1, 44, true, 0, 0, 1⟩, ⟨6, 4, 1, 44, false, 0, 0, 1⟩, ⟨6, 4, 1, 48, true, 0, 0, 1⟩,
   ⟨6, 5, 1, 48, false, 0, 0, 1⟩, ⟨6, 5, 1, 52, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup38_ok : majGroup38.all (fun r => r.check) = true := by decide +kernel

/-- Group `39` of the majorization certificate: `8` triangles. -/
def majGroup39 : List MajRow :=
  [⟨6, 6, 1, 52, false, 0, 0, 1⟩, ⟨6, 6, 1, 56, true, 0, 0, 1⟩, ⟨6, 7, 1, 56, false, 0, 0, 1⟩,
   ⟨6, 7, 1, 60, true, 0, 0, 1⟩, ⟨6, 8, 1, 60, false, 0, 0, 1⟩, ⟨6, 8, 1, 64, true, 0, 0, 1⟩,
   ⟨6, 9, 1, 64, false, 0, 0, 1⟩, ⟨6, 9, 0, 68, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup39_ok : majGroup39.all (fun r => r.check) = true := by decide +kernel

/-- Group `40` of the majorization certificate: `8` triangles. -/
def majGroup40 : List MajRow :=
  [⟨6, 10, 0, 68, false, 0, 0, 1⟩, ⟨6, 10, 0, 72, true, 0, 0, 1⟩, ⟨6, 11, 0, 72, false, 0, 0, 1⟩,
   ⟨6, 11, 0, 76, true, 0, 0, 1⟩, ⟨6, 12, 0, 76, false, 0, 0, 1⟩, ⟨6, 12, 0, 80, true, 0, 0, 1⟩,
   ⟨6, 13, 0, 80, false, 0, 0, 1⟩, ⟨6, 13, 0, 84, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup40_ok : majGroup40.all (fun r => r.check) = true := by decide +kernel

/-- Group `41` of the majorization certificate: `8` triangles. -/
def majGroup41 : List MajRow :=
  [⟨6, 14, 0, 84, false, 0, 0, 1⟩, ⟨6, 14, 0, 88, true, 0, 0, 1⟩, ⟨6, 15, 0, 88, false, 0, 0, 1⟩,
   ⟨6, 15, 0, 92, true, 0, 0, 1⟩, ⟨6, 16, 0, 92, false, 0, 0, 1⟩, ⟨6, 16, 0, 96, true, 0, 0, 1⟩,
   ⟨6, 17, 0, 96, false, 0, 0, 1⟩, ⟨6, 17, 0, 100, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup41_ok : majGroup41.all (fun r => r.check) = true := by decide +kernel

/-- Group `42` of the majorization certificate: `8` triangles. -/
def majGroup42 : List MajRow :=
  [⟨6, 18, 0, 100, false, 0, 0, 1⟩, ⟨6, 18, 0, 104, true, 0, 0, 1⟩,
   ⟨6, 19, 0, 104, false, 0, 0, 1⟩, ⟨6, 19, 0, 108, true, 0, 0, 1⟩,
   ⟨6, 20, 0, 108, false, 0, 0, 1⟩, ⟨6, 20, 0, 112, true, 0, 0, 1⟩,
   ⟨6, 21, 0, 112, false, 0, 0, 1⟩, ⟨7, 0, 1, 32, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup42_ok : majGroup42.all (fun r => r.check) = true := by decide +kernel

/-- Group `43` of the majorization certificate: `8` triangles. -/
def majGroup43 : List MajRow :=
  [⟨7, 0, 1, 36, true, 0, 0, 1⟩, ⟨7, 1, 1, 36, false, 0, 0, 1⟩, ⟨7, 1, 1, 40, true, 0, 0, 1⟩,
   ⟨7, 2, 1, 40, false, 0, 0, 1⟩, ⟨7, 2, 1, 44, true, 0, 0, 1⟩, ⟨7, 3, 1, 44, false, 0, 0, 1⟩,
   ⟨7, 3, 1, 48, true, 0, 0, 1⟩, ⟨7, 4, 1, 48, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup43_ok : majGroup43.all (fun r => r.check) = true := by decide +kernel

/-- Group `44` of the majorization certificate: `8` triangles. -/
def majGroup44 : List MajRow :=
  [⟨7, 4, 1, 52, true, 0, 0, 1⟩, ⟨7, 5, 1, 52, false, 0, 0, 1⟩, ⟨7, 5, 1, 56, true, 0, 0, 1⟩,
   ⟨7, 6, 1, 56, false, 0, 0, 1⟩, ⟨7, 6, 1, 60, true, 0, 0, 1⟩, ⟨7, 7, 1, 60, false, 0, 0, 1⟩,
   ⟨7, 7, 1, 64, true, 0, 0, 1⟩, ⟨7, 8, 1, 64, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup44_ok : majGroup44.all (fun r => r.check) = true := by decide +kernel

/-- Group `45` of the majorization certificate: `8` triangles. -/
def majGroup45 : List MajRow :=
  [⟨7, 8, 0, 68, true, 0, 0, 1⟩, ⟨7, 9, 0, 68, false, 0, 0, 1⟩, ⟨7, 9, 0, 72, true, 0, 0, 1⟩,
   ⟨7, 10, 0, 72, false, 0, 0, 1⟩, ⟨7, 10, 0, 76, true, 0, 0, 1⟩, ⟨7, 11, 0, 76, false, 0, 0, 1⟩,
   ⟨7, 11, 0, 80, true, 0, 0, 1⟩, ⟨7, 12, 0, 80, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup45_ok : majGroup45.all (fun r => r.check) = true := by decide +kernel

/-- Group `46` of the majorization certificate: `8` triangles. -/
def majGroup46 : List MajRow :=
  [⟨7, 12, 0, 84, true, 0, 0, 1⟩, ⟨7, 13, 0, 84, false, 0, 0, 1⟩, ⟨7, 13, 0, 88, true, 0, 0, 1⟩,
   ⟨7, 14, 0, 88, false, 0, 0, 1⟩, ⟨7, 14, 0, 92, true, 0, 0, 1⟩, ⟨7, 15, 0, 92, false, 0, 0, 1⟩,
   ⟨7, 15, 0, 96, true, 0, 0, 1⟩, ⟨7, 16, 0, 96, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup46_ok : majGroup46.all (fun r => r.check) = true := by decide +kernel

/-- Group `47` of the majorization certificate: `8` triangles. -/
def majGroup47 : List MajRow :=
  [⟨7, 16, 0, 100, true, 0, 0, 1⟩, ⟨7, 17, 0, 100, false, 0, 0, 1⟩,
   ⟨7, 17, 0, 104, true, 0, 0, 1⟩, ⟨7, 18, 0, 104, false, 0, 0, 1⟩,
   ⟨7, 18, 0, 108, true, 0, 0, 1⟩, ⟨7, 19, 0, 108, false, 0, 0, 1⟩,
   ⟨7, 19, 0, 112, true, 0, 0, 1⟩, ⟨7, 20, 0, 112, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup47_ok : majGroup47.all (fun r => r.check) = true := by decide +kernel

/-- Group `48` of the majorization certificate: `8` triangles. -/
def majGroup48 : List MajRow :=
  [⟨8, 0, 1, 36, false, 0, 0, 1⟩, ⟨8, 0, 1, 40, true, 0, 0, 1⟩, ⟨8, 1, 1, 40, false, 0, 0, 1⟩,
   ⟨8, 1, 1, 44, true, 0, 0, 1⟩, ⟨8, 2, 1, 44, false, 0, 0, 1⟩, ⟨8, 2, 1, 48, true, 0, 0, 1⟩,
   ⟨8, 3, 1, 48, false, 0, 0, 1⟩, ⟨8, 3, 1, 52, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup48_ok : majGroup48.all (fun r => r.check) = true := by decide +kernel

/-- Group `49` of the majorization certificate: `8` triangles. -/
def majGroup49 : List MajRow :=
  [⟨8, 4, 1, 52, false, 0, 0, 1⟩, ⟨8, 4, 1, 56, true, 0, 0, 1⟩, ⟨8, 5, 1, 56, false, 0, 0, 1⟩,
   ⟨8, 5, 1, 60, true, 0, 0, 1⟩, ⟨8, 6, 1, 60, false, 0, 0, 1⟩, ⟨8, 6, 1, 64, true, 0, 0, 1⟩,
   ⟨8, 7, 1, 64, false, 0, 0, 1⟩, ⟨8, 7, 0, 68, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup49_ok : majGroup49.all (fun r => r.check) = true := by decide +kernel

/-- Group `50` of the majorization certificate: `8` triangles. -/
def majGroup50 : List MajRow :=
  [⟨8, 8, 0, 68, false, 0, 0, 1⟩, ⟨8, 8, 0, 72, true, 0, 0, 1⟩, ⟨8, 9, 0, 72, false, 0, 0, 1⟩,
   ⟨8, 9, 0, 76, true, 0, 0, 1⟩, ⟨8, 10, 0, 76, false, 0, 0, 1⟩, ⟨8, 10, 0, 80, true, 0, 0, 1⟩,
   ⟨8, 11, 0, 80, false, 0, 0, 1⟩, ⟨8, 11, 0, 84, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup50_ok : majGroup50.all (fun r => r.check) = true := by decide +kernel

/-- Shard `3` of the majorization certificate: `104` triangles. -/
def majShard3 : List MajRow :=
  majGroup38 ++ majGroup39 ++ majGroup40 ++ majGroup41 ++ majGroup42 ++ majGroup43 ++ majGroup44 ++
    majGroup45 ++ majGroup46 ++ majGroup47 ++ majGroup48 ++ majGroup49 ++ majGroup50

set_option maxRecDepth 4000 in
theorem majShard3_length : majShard3.length = 104 := by rfl

/-- **Every triangle of shard `3` passes its Bernstein test.** -/
theorem majShard3_ok : majShard3.all (fun r => r.check) = true := by
  simp only [majShard3, List.all_append, Bool.and_eq_true, majGroup38_ok,
    majGroup39_ok,
    majGroup40_ok,
    majGroup41_ok,
    majGroup42_ok,
    majGroup43_ok,
    majGroup44_ok,
    majGroup45_ok,
    majGroup46_ok,
    majGroup47_ok,
    majGroup48_ok,
    majGroup49_ok,
    majGroup50_ok,
    and_self]

end CenteredMaximal.Fractional

end
