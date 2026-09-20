/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.MajorRow

/-!
# The majorization certificate of the `α = 6/5` comparison kernel, shard 0

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

/-- Group `0` of the majorization certificate: `8` triangles. -/
def majGroup0 : List MajRow :=
  [⟨0, 0, 1, 4, false, 0, 0, 1⟩, ⟨0, 0, 1, 8, true, 0, 0, 1⟩, ⟨0, 1, 1, 8, false, 0, 0, 1⟩,
   ⟨0, 1, 1, 12, true, 0, 0, 1⟩, ⟨0, 2, 1, 12, false, 0, 0, 1⟩, ⟨0, 2, 1, 16, true, 0, 0, 1⟩,
   ⟨0, 3, 1, 16, false, 0, 0, 1⟩, ⟨0, 3, 1, 20, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup0_ok : majGroup0.all (fun r => r.check) = true := by decide +kernel

/-- Group `1` of the majorization certificate: `8` triangles. -/
def majGroup1 : List MajRow :=
  [⟨0, 4, 1, 20, false, 0, 0, 1⟩, ⟨0, 4, 1, 24, true, 0, 0, 1⟩, ⟨0, 5, 1, 24, false, 0, 0, 1⟩,
   ⟨0, 5, 1, 28, true, 0, 0, 1⟩, ⟨0, 6, 1, 28, false, 0, 0, 1⟩, ⟨0, 6, 1, 32, true, 0, 0, 1⟩,
   ⟨0, 7, 1, 32, false, 0, 0, 1⟩, ⟨0, 7, 1, 36, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup1_ok : majGroup1.all (fun r => r.check) = true := by decide +kernel

/-- Group `2` of the majorization certificate: `8` triangles. -/
def majGroup2 : List MajRow :=
  [⟨0, 8, 1, 36, false, 0, 0, 1⟩, ⟨0, 8, 1, 40, true, 0, 0, 1⟩, ⟨0, 9, 1, 40, false, 0, 0, 1⟩,
   ⟨0, 9, 1, 44, true, 0, 0, 1⟩, ⟨0, 10, 1, 44, false, 0, 0, 1⟩, ⟨0, 10, 1, 48, true, 0, 0, 1⟩,
   ⟨0, 11, 1, 48, false, 0, 0, 1⟩, ⟨0, 11, 1, 52, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup2_ok : majGroup2.all (fun r => r.check) = true := by decide +kernel

/-- Group `3` of the majorization certificate: `8` triangles. -/
def majGroup3 : List MajRow :=
  [⟨0, 12, 1, 52, false, 0, 0, 1⟩, ⟨0, 12, 1, 56, true, 0, 0, 1⟩, ⟨0, 13, 1, 56, false, 0, 0, 1⟩,
   ⟨0, 13, 1, 60, true, 0, 0, 1⟩, ⟨0, 14, 1, 60, false, 0, 0, 1⟩, ⟨0, 14, 1, 64, true, 0, 0, 1⟩,
   ⟨0, 15, 1, 64, false, 0, 0, 1⟩, ⟨0, 15, 0, 68, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup3_ok : majGroup3.all (fun r => r.check) = true := by decide +kernel

/-- Group `4` of the majorization certificate: `8` triangles. -/
def majGroup4 : List MajRow :=
  [⟨0, 16, 0, 68, false, 0, 0, 1⟩, ⟨0, 16, 0, 72, true, 0, 0, 1⟩, ⟨0, 17, 0, 72, false, 0, 0, 1⟩,
   ⟨0, 17, 0, 76, true, 0, 0, 1⟩, ⟨0, 18, 0, 76, false, 0, 0, 1⟩, ⟨0, 18, 0, 80, true, 0, 0, 1⟩,
   ⟨0, 19, 0, 80, false, 0, 0, 1⟩, ⟨0, 19, 0, 84, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup4_ok : majGroup4.all (fun r => r.check) = true := by decide +kernel

/-- Group `5` of the majorization certificate: `8` triangles. -/
def majGroup5 : List MajRow :=
  [⟨0, 20, 0, 84, false, 0, 0, 1⟩, ⟨0, 20, 0, 88, true, 0, 0, 1⟩, ⟨0, 21, 0, 88, false, 0, 0, 1⟩,
   ⟨0, 21, 0, 92, true, 0, 0, 1⟩, ⟨0, 22, 0, 92, false, 0, 0, 1⟩, ⟨0, 22, 0, 96, true, 0, 0, 1⟩,
   ⟨0, 23, 0, 96, false, 0, 0, 1⟩, ⟨0, 23, 0, 100, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup5_ok : majGroup5.all (fun r => r.check) = true := by decide +kernel

/-- Group `6` of the majorization certificate: `8` triangles. -/
def majGroup6 : List MajRow :=
  [⟨0, 24, 0, 100, false, 0, 0, 1⟩, ⟨0, 24, 0, 104, true, 0, 0, 1⟩,
   ⟨0, 25, 0, 104, false, 0, 0, 1⟩, ⟨0, 25, 0, 108, true, 0, 0, 1⟩,
   ⟨0, 26, 0, 108, false, 0, 0, 1⟩, ⟨0, 26, 0, 112, true, 0, 0, 1⟩,
   ⟨0, 27, 0, 112, false, 0, 0, 1⟩, ⟨1, 0, 1, 8, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup6_ok : majGroup6.all (fun r => r.check) = true := by decide +kernel

/-- Group `7` of the majorization certificate: `8` triangles. -/
def majGroup7 : List MajRow :=
  [⟨1, 0, 1, 12, true, 0, 0, 1⟩, ⟨1, 1, 1, 12, false, 0, 0, 1⟩, ⟨1, 1, 1, 16, true, 0, 0, 1⟩,
   ⟨1, 2, 1, 16, false, 0, 0, 1⟩, ⟨1, 2, 1, 20, true, 0, 0, 1⟩, ⟨1, 3, 1, 20, false, 0, 0, 1⟩,
   ⟨1, 3, 1, 24, true, 0, 0, 1⟩, ⟨1, 4, 1, 24, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup7_ok : majGroup7.all (fun r => r.check) = true := by decide +kernel

/-- Group `8` of the majorization certificate: `8` triangles. -/
def majGroup8 : List MajRow :=
  [⟨1, 4, 1, 28, true, 0, 0, 1⟩, ⟨1, 5, 1, 28, false, 0, 0, 1⟩, ⟨1, 5, 1, 32, true, 0, 0, 1⟩,
   ⟨1, 6, 1, 32, false, 0, 0, 1⟩, ⟨1, 6, 1, 36, true, 0, 0, 1⟩, ⟨1, 7, 1, 36, false, 0, 0, 1⟩,
   ⟨1, 7, 1, 40, true, 0, 0, 1⟩, ⟨1, 8, 1, 40, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup8_ok : majGroup8.all (fun r => r.check) = true := by decide +kernel

/-- Group `9` of the majorization certificate: `8` triangles. -/
def majGroup9 : List MajRow :=
  [⟨1, 8, 1, 44, true, 0, 0, 1⟩, ⟨1, 9, 1, 44, false, 0, 0, 1⟩, ⟨1, 9, 1, 48, true, 0, 0, 1⟩,
   ⟨1, 10, 1, 48, false, 0, 0, 1⟩, ⟨1, 10, 1, 52, true, 0, 0, 1⟩, ⟨1, 11, 1, 52, false, 0, 0, 1⟩,
   ⟨1, 11, 1, 56, true, 0, 0, 1⟩, ⟨1, 12, 1, 56, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup9_ok : majGroup9.all (fun r => r.check) = true := by decide +kernel

/-- Group `10` of the majorization certificate: `8` triangles. -/
def majGroup10 : List MajRow :=
  [⟨1, 12, 1, 60, true, 0, 0, 1⟩, ⟨1, 13, 1, 60, false, 0, 0, 1⟩, ⟨1, 13, 1, 64, true, 0, 0, 1⟩,
   ⟨1, 14, 1, 64, false, 0, 0, 1⟩, ⟨1, 14, 0, 68, true, 0, 0, 1⟩, ⟨1, 15, 0, 68, false, 0, 0, 1⟩,
   ⟨1, 15, 0, 72, true, 0, 0, 1⟩, ⟨1, 16, 0, 72, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup10_ok : majGroup10.all (fun r => r.check) = true := by decide +kernel

/-- Group `11` of the majorization certificate: `8` triangles. -/
def majGroup11 : List MajRow :=
  [⟨1, 16, 0, 76, true, 0, 0, 1⟩, ⟨1, 17, 0, 76, false, 0, 0, 1⟩, ⟨1, 17, 0, 80, true, 0, 0, 1⟩,
   ⟨1, 18, 0, 80, false, 0, 0, 1⟩, ⟨1, 18, 0, 84, true, 0, 0, 1⟩, ⟨1, 19, 0, 84, false, 0, 0, 1⟩,
   ⟨1, 19, 0, 88, true, 0, 0, 1⟩, ⟨1, 20, 0, 88, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup11_ok : majGroup11.all (fun r => r.check) = true := by decide +kernel

/-- Shard `0` of the majorization certificate: `96` triangles. -/
def majShard0 : List MajRow :=
  majGroup0 ++ majGroup1 ++ majGroup2 ++ majGroup3 ++ majGroup4 ++ majGroup5 ++ majGroup6 ++
    majGroup7 ++ majGroup8 ++ majGroup9 ++ majGroup10 ++ majGroup11

set_option maxRecDepth 4000 in
theorem majShard0_length : majShard0.length = 96 := by rfl

/-- **Every triangle of shard `0` passes its Bernstein test.** -/
theorem majShard0_ok : majShard0.all (fun r => r.check) = true := by
  simp only [majShard0, List.all_append, Bool.and_eq_true, majGroup0_ok,
    majGroup1_ok,
    majGroup2_ok,
    majGroup3_ok,
    majGroup4_ok,
    majGroup5_ok,
    majGroup6_ok,
    majGroup7_ok,
    majGroup8_ok,
    majGroup9_ok,
    majGroup10_ok,
    majGroup11_ok,
    and_self]

end CenteredMaximal.Fractional

end
