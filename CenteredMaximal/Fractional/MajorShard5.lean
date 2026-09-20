/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.MajorRow

/-!
# The majorization certificate of the `α = 6/5` comparison kernel, shard 5

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

/-- Group `63` of the majorization certificate: `8` triangles. -/
def majGroup63 : List MajRow :=
  [⟨11, 4, 0, 68, true, 0, 0, 1⟩, ⟨11, 5, 0, 68, false, 0, 0, 1⟩, ⟨11, 5, 0, 72, true, 0, 0, 1⟩,
   ⟨11, 6, 0, 72, false, 0, 0, 1⟩, ⟨11, 6, 0, 76, true, 0, 0, 1⟩, ⟨11, 7, 0, 76, false, 0, 0, 1⟩,
   ⟨11, 7, 0, 80, true, 0, 0, 1⟩, ⟨11, 8, 0, 80, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup63_ok : majGroup63.all (fun r => r.check) = true := by decide +kernel

/-- Group `64` of the majorization certificate: `8` triangles. -/
def majGroup64 : List MajRow :=
  [⟨11, 8, 0, 84, true, 0, 0, 1⟩, ⟨11, 9, 0, 84, false, 0, 0, 1⟩, ⟨11, 9, 0, 88, true, 0, 0, 1⟩,
   ⟨11, 10, 0, 88, false, 0, 0, 1⟩, ⟨11, 10, 0, 92, true, 0, 0, 1⟩,
   ⟨11, 11, 0, 89, false, 0, 0, 1/4⟩, ⟨11, 11, 0, 90, false, 0, 1/4, 1/4⟩,
   ⟨11, 11, 0, 91, false, 0, 1/2, 1/4⟩]

set_option maxRecDepth 4000000 in
theorem majGroup64_ok : majGroup64.all (fun r => r.check) = true := by decide +kernel

/-- Group `65` of the majorization certificate: `8` triangles. -/
def majGroup65 : List MajRow :=
  [⟨11, 11, 0, 92, false, 0, 3/4, 1/4⟩, ⟨11, 11, 0, 90, false, 1/4, 0, 1/4⟩,
   ⟨11, 11, 0, 91, false, 1/4, 1/4, 1/4⟩, ⟨11, 11, 0, 92, false, 1/4, 1/2, 1/4⟩,
   ⟨11, 11, 0, 93, false, 1/4, 3/4, 1/4⟩, ⟨11, 11, 0, 91, false, 1/2, 0, 1/4⟩,
   ⟨11, 11, 0, 92, false, 1/2, 1/4, 1/4⟩, ⟨11, 11, 0, 93, false, 1/2, 1/2, 1/4⟩]

set_option maxRecDepth 4000000 in
theorem majGroup65_ok : majGroup65.all (fun r => r.check) = true := by decide +kernel

/-- Group `66` of the majorization certificate: `8` triangles. -/
def majGroup66 : List MajRow :=
  [⟨11, 11, 0, 94, false, 1/2, 3/4, 1/4⟩, ⟨11, 11, 0, 92, false, 3/4, 0, 1/4⟩,
   ⟨11, 11, 0, 93, false, 3/4, 1/4, 1/4⟩, ⟨11, 11, 0, 94, false, 3/4, 1/2, 1/4⟩,
   ⟨11, 11, 0, 95, false, 3/4, 3/4, 1/4⟩, ⟨11, 11, 0, 90, true, 0, 0, 1/4⟩,
   ⟨11, 11, 0, 91, true, 0, 1/4, 1/4⟩, ⟨11, 11, 0, 92, true, 0, 1/2, 1/4⟩]

set_option maxRecDepth 4000000 in
theorem majGroup66_ok : majGroup66.all (fun r => r.check) = true := by decide +kernel

/-- Group `67` of the majorization certificate: `8` triangles. -/
def majGroup67 : List MajRow :=
  [⟨11, 11, 0, 93, true, 0, 3/4, 1/4⟩, ⟨11, 11, 0, 91, true, 1/4, 0, 1/4⟩,
   ⟨11, 11, 0, 92, true, 1/4, 1/4, 1/4⟩, ⟨11, 11, 0, 93, true, 1/4, 1/2, 1/4⟩,
   ⟨11, 11, 0, 94, true, 1/4, 3/4, 1/4⟩, ⟨11, 11, 0, 92, true, 1/2, 0, 1/4⟩,
   ⟨11, 11, 0, 93, true, 1/2, 1/4, 1/4⟩, ⟨11, 11, 0, 94, true, 1/2, 1/2, 1/4⟩]

set_option maxRecDepth 4000000 in
theorem majGroup67_ok : majGroup67.all (fun r => r.check) = true := by decide +kernel

/-- Group `68` of the majorization certificate: `8` triangles. -/
def majGroup68 : List MajRow :=
  [⟨11, 11, 0, 95, true, 1/2, 3/4, 1/4⟩, ⟨11, 11, 0, 93, true, 3/4, 0, 1/4⟩,
   ⟨11, 11, 0, 94, true, 3/4, 1/4, 1/4⟩, ⟨11, 11, 0, 95, true, 3/4, 1/2, 1/4⟩,
   ⟨11, 11, 0, 96, true, 3/4, 3/4, 1/4⟩, ⟨11, 12, 0, 96, false, 0, 0, 1⟩,
   ⟨11, 12, 0, 100, true, 0, 0, 1⟩, ⟨11, 13, 0, 100, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup68_ok : majGroup68.all (fun r => r.check) = true := by decide +kernel

/-- Group `69` of the majorization certificate: `8` triangles. -/
def majGroup69 : List MajRow :=
  [⟨11, 13, 0, 104, true, 0, 0, 1⟩, ⟨11, 14, 0, 104, false, 0, 0, 1⟩,
   ⟨11, 14, 0, 108, true, 0, 0, 1⟩, ⟨11, 15, 0, 108, false, 0, 0, 1⟩,
   ⟨11, 15, 0, 112, true, 0, 0, 1⟩, ⟨11, 16, 0, 112, false, 0, 0, 1⟩,
   ⟨12, 0, 1, 52, false, 0, 0, 1⟩, ⟨12, 0, 1, 56, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup69_ok : majGroup69.all (fun r => r.check) = true := by decide +kernel

/-- Group `70` of the majorization certificate: `8` triangles. -/
def majGroup70 : List MajRow :=
  [⟨12, 1, 1, 56, false, 0, 0, 1⟩, ⟨12, 1, 1, 60, true, 0, 0, 1⟩, ⟨12, 2, 1, 60, false, 0, 0, 1⟩,
   ⟨12, 2, 1, 64, true, 0, 0, 1⟩, ⟨12, 3, 1, 64, false, 0, 0, 1⟩, ⟨12, 3, 0, 68, true, 0, 0, 1⟩,
   ⟨12, 4, 0, 68, false, 0, 0, 1⟩, ⟨12, 4, 0, 72, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup70_ok : majGroup70.all (fun r => r.check) = true := by decide +kernel

/-- Group `71` of the majorization certificate: `8` triangles. -/
def majGroup71 : List MajRow :=
  [⟨12, 5, 0, 72, false, 0, 0, 1⟩, ⟨12, 5, 0, 76, true, 0, 0, 1⟩, ⟨12, 6, 0, 76, false, 0, 0, 1⟩,
   ⟨12, 6, 0, 80, true, 0, 0, 1⟩, ⟨12, 7, 0, 80, false, 0, 0, 1⟩, ⟨12, 7, 0, 84, true, 0, 0, 1⟩,
   ⟨12, 8, 0, 84, false, 0, 0, 1⟩, ⟨12, 8, 0, 88, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup71_ok : majGroup71.all (fun r => r.check) = true := by decide +kernel

/-- Group `72` of the majorization certificate: `8` triangles. -/
def majGroup72 : List MajRow :=
  [⟨12, 9, 0, 88, false, 0, 0, 1⟩, ⟨12, 9, 0, 92, true, 0, 0, 1⟩, ⟨12, 10, 0, 92, false, 0, 0, 1⟩,
   ⟨12, 10, 0, 96, true, 0, 0, 1⟩, ⟨12, 11, 0, 96, false, 0, 0, 1⟩,
   ⟨12, 11, 0, 100, true, 0, 0, 1⟩, ⟨12, 12, 0, 100, false, 0, 0, 1⟩,
   ⟨12, 12, 0, 104, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup72_ok : majGroup72.all (fun r => r.check) = true := by decide +kernel

/-- Group `73` of the majorization certificate: `8` triangles. -/
def majGroup73 : List MajRow :=
  [⟨12, 13, 0, 104, false, 0, 0, 1⟩, ⟨12, 13, 0, 108, true, 0, 0, 1⟩,
   ⟨12, 14, 0, 108, false, 0, 0, 1⟩, ⟨12, 14, 0, 112, true, 0, 0, 1⟩,
   ⟨12, 15, 0, 112, false, 0, 0, 1⟩, ⟨13, 0, 1, 56, false, 0, 0, 1⟩,
   ⟨13, 0, 1, 60, true, 0, 0, 1⟩, ⟨13, 1, 1, 60, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup73_ok : majGroup73.all (fun r => r.check) = true := by decide +kernel

/-- Group `74` of the majorization certificate: `8` triangles. -/
def majGroup74 : List MajRow :=
  [⟨13, 1, 1, 64, true, 0, 0, 1⟩, ⟨13, 2, 1, 64, false, 0, 0, 1⟩, ⟨13, 2, 0, 68, true, 0, 0, 1⟩,
   ⟨13, 3, 0, 68, false, 0, 0, 1⟩, ⟨13, 3, 0, 72, true, 0, 0, 1⟩, ⟨13, 4, 0, 72, false, 0, 0, 1⟩,
   ⟨13, 4, 0, 76, true, 0, 0, 1⟩, ⟨13, 5, 0, 76, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup74_ok : majGroup74.all (fun r => r.check) = true := by decide +kernel

/-- Group `75` of the majorization certificate: `8` triangles. -/
def majGroup75 : List MajRow :=
  [⟨13, 5, 0, 80, true, 0, 0, 1⟩, ⟨13, 6, 0, 80, false, 0, 0, 1⟩, ⟨13, 6, 0, 84, true, 0, 0, 1⟩,
   ⟨13, 7, 0, 84, false, 0, 0, 1⟩, ⟨13, 7, 0, 88, true, 0, 0, 1⟩, ⟨13, 8, 0, 88, false, 0, 0, 1⟩,
   ⟨13, 8, 0, 92, true, 0, 0, 1⟩, ⟨13, 9, 0, 92, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup75_ok : majGroup75.all (fun r => r.check) = true := by decide +kernel

/-- Shard `5` of the majorization certificate: `104` triangles. -/
def majShard5 : List MajRow :=
  majGroup63 ++ majGroup64 ++ majGroup65 ++ majGroup66 ++ majGroup67 ++ majGroup68 ++ majGroup69 ++
    majGroup70 ++ majGroup71 ++ majGroup72 ++ majGroup73 ++ majGroup74 ++ majGroup75

set_option maxRecDepth 4000 in
theorem majShard5_length : majShard5.length = 104 := by rfl

/-- **Every triangle of shard `5` passes its Bernstein test.** -/
theorem majShard5_ok : majShard5.all (fun r => r.check) = true := by
  simp only [majShard5, List.all_append, Bool.and_eq_true, majGroup63_ok,
    majGroup64_ok,
    majGroup65_ok,
    majGroup66_ok,
    majGroup67_ok,
    majGroup68_ok,
    majGroup69_ok,
    majGroup70_ok,
    majGroup71_ok,
    majGroup72_ok,
    majGroup73_ok,
    majGroup74_ok,
    majGroup75_ok,
    and_self]

end CenteredMaximal.Fractional

end
