/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.MajorRow

/-!
# The majorization certificate of the `α = 6/5` comparison kernel, shard 1

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

/-- Group `12` of the majorization certificate: `8` triangles. -/
def majGroup12 : List MajRow :=
  [⟨1, 20, 0, 92, true, 0, 0, 1⟩, ⟨1, 21, 0, 92, false, 0, 0, 1⟩, ⟨1, 21, 0, 96, true, 0, 0, 1⟩,
   ⟨1, 22, 0, 96, false, 0, 0, 1⟩, ⟨1, 22, 0, 100, true, 0, 0, 1⟩,
   ⟨1, 23, 0, 100, false, 0, 0, 1⟩, ⟨1, 23, 0, 104, true, 0, 0, 1⟩,
   ⟨1, 24, 0, 104, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup12_ok : majGroup12.all (fun r => r.check) = true := by decide +kernel

/-- Group `13` of the majorization certificate: `8` triangles. -/
def majGroup13 : List MajRow :=
  [⟨1, 24, 0, 108, true, 0, 0, 1⟩, ⟨1, 25, 0, 108, false, 0, 0, 1⟩,
   ⟨1, 25, 0, 112, true, 0, 0, 1⟩, ⟨1, 26, 0, 112, false, 0, 0, 1⟩, ⟨2, 0, 1, 12, false, 0, 0, 1⟩,
   ⟨2, 0, 1, 16, true, 0, 0, 1⟩, ⟨2, 1, 1, 16, false, 0, 0, 1⟩, ⟨2, 1, 1, 20, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup13_ok : majGroup13.all (fun r => r.check) = true := by decide +kernel

/-- Group `14` of the majorization certificate: `8` triangles. -/
def majGroup14 : List MajRow :=
  [⟨2, 2, 1, 20, false, 0, 0, 1⟩, ⟨2, 2, 1, 24, true, 0, 0, 1⟩, ⟨2, 3, 1, 24, false, 0, 0, 1⟩,
   ⟨2, 3, 1, 28, true, 0, 0, 1⟩, ⟨2, 4, 1, 28, false, 0, 0, 1⟩, ⟨2, 4, 1, 32, true, 0, 0, 1⟩,
   ⟨2, 5, 1, 32, false, 0, 0, 1⟩, ⟨2, 5, 1, 36, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup14_ok : majGroup14.all (fun r => r.check) = true := by decide +kernel

/-- Group `15` of the majorization certificate: `8` triangles. -/
def majGroup15 : List MajRow :=
  [⟨2, 6, 1, 36, false, 0, 0, 1⟩, ⟨2, 6, 1, 40, true, 0, 0, 1⟩, ⟨2, 7, 1, 40, false, 0, 0, 1⟩,
   ⟨2, 7, 1, 44, true, 0, 0, 1⟩, ⟨2, 8, 1, 44, false, 0, 0, 1⟩, ⟨2, 8, 1, 48, true, 0, 0, 1⟩,
   ⟨2, 9, 1, 48, false, 0, 0, 1⟩, ⟨2, 9, 1, 52, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup15_ok : majGroup15.all (fun r => r.check) = true := by decide +kernel

/-- Group `16` of the majorization certificate: `8` triangles. -/
def majGroup16 : List MajRow :=
  [⟨2, 10, 1, 52, false, 0, 0, 1⟩, ⟨2, 10, 1, 56, true, 0, 0, 1⟩, ⟨2, 11, 1, 56, false, 0, 0, 1⟩,
   ⟨2, 11, 1, 60, true, 0, 0, 1⟩, ⟨2, 12, 1, 60, false, 0, 0, 1⟩, ⟨2, 12, 1, 64, true, 0, 0, 1⟩,
   ⟨2, 13, 1, 64, false, 0, 0, 1⟩, ⟨2, 13, 0, 68, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup16_ok : majGroup16.all (fun r => r.check) = true := by decide +kernel

/-- Group `17` of the majorization certificate: `8` triangles. -/
def majGroup17 : List MajRow :=
  [⟨2, 14, 0, 68, false, 0, 0, 1⟩, ⟨2, 14, 0, 72, true, 0, 0, 1⟩, ⟨2, 15, 0, 72, false, 0, 0, 1⟩,
   ⟨2, 15, 0, 76, true, 0, 0, 1⟩, ⟨2, 16, 0, 76, false, 0, 0, 1⟩, ⟨2, 16, 0, 80, true, 0, 0, 1⟩,
   ⟨2, 17, 0, 80, false, 0, 0, 1⟩, ⟨2, 17, 0, 84, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup17_ok : majGroup17.all (fun r => r.check) = true := by decide +kernel

/-- Group `18` of the majorization certificate: `8` triangles. -/
def majGroup18 : List MajRow :=
  [⟨2, 18, 0, 84, false, 0, 0, 1⟩, ⟨2, 18, 0, 88, true, 0, 0, 1⟩, ⟨2, 19, 0, 88, false, 0, 0, 1⟩,
   ⟨2, 19, 0, 92, true, 0, 0, 1⟩, ⟨2, 20, 0, 92, false, 0, 0, 1⟩, ⟨2, 20, 0, 96, true, 0, 0, 1⟩,
   ⟨2, 21, 0, 96, false, 0, 0, 1⟩, ⟨2, 21, 0, 100, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup18_ok : majGroup18.all (fun r => r.check) = true := by decide +kernel

/-- Group `19` of the majorization certificate: `8` triangles. -/
def majGroup19 : List MajRow :=
  [⟨2, 22, 0, 100, false, 0, 0, 1⟩, ⟨2, 22, 0, 104, true, 0, 0, 1⟩,
   ⟨2, 23, 0, 104, false, 0, 0, 1⟩, ⟨2, 23, 0, 108, true, 0, 0, 1⟩,
   ⟨2, 24, 0, 108, false, 0, 0, 1⟩, ⟨2, 24, 0, 112, true, 0, 0, 1⟩,
   ⟨2, 25, 0, 112, false, 0, 0, 1⟩, ⟨3, 0, 1, 16, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup19_ok : majGroup19.all (fun r => r.check) = true := by decide +kernel

/-- Group `20` of the majorization certificate: `8` triangles. -/
def majGroup20 : List MajRow :=
  [⟨3, 0, 1, 20, true, 0, 0, 1⟩, ⟨3, 1, 1, 20, false, 0, 0, 1⟩, ⟨3, 1, 1, 24, true, 0, 0, 1⟩,
   ⟨3, 2, 1, 24, false, 0, 0, 1⟩, ⟨3, 2, 1, 28, true, 0, 0, 1⟩, ⟨3, 3, 1, 28, false, 0, 0, 1⟩,
   ⟨3, 3, 1, 32, true, 0, 0, 1⟩, ⟨3, 4, 1, 32, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup20_ok : majGroup20.all (fun r => r.check) = true := by decide +kernel

/-- Group `21` of the majorization certificate: `8` triangles. -/
def majGroup21 : List MajRow :=
  [⟨3, 4, 1, 36, true, 0, 0, 1⟩, ⟨3, 5, 1, 36, false, 0, 0, 1⟩, ⟨3, 5, 1, 40, true, 0, 0, 1⟩,
   ⟨3, 6, 1, 40, false, 0, 0, 1⟩, ⟨3, 6, 1, 44, true, 0, 0, 1⟩, ⟨3, 7, 1, 44, false, 0, 0, 1⟩,
   ⟨3, 7, 1, 48, true, 0, 0, 1⟩, ⟨3, 8, 1, 48, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup21_ok : majGroup21.all (fun r => r.check) = true := by decide +kernel

/-- Group `22` of the majorization certificate: `8` triangles. -/
def majGroup22 : List MajRow :=
  [⟨3, 8, 1, 52, true, 0, 0, 1⟩, ⟨3, 9, 1, 52, false, 0, 0, 1⟩, ⟨3, 9, 1, 56, true, 0, 0, 1⟩,
   ⟨3, 10, 1, 56, false, 0, 0, 1⟩, ⟨3, 10, 1, 60, true, 0, 0, 1⟩, ⟨3, 11, 1, 60, false, 0, 0, 1⟩,
   ⟨3, 11, 1, 64, true, 0, 0, 1⟩, ⟨3, 12, 1, 64, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup22_ok : majGroup22.all (fun r => r.check) = true := by decide +kernel

/-- Group `23` of the majorization certificate: `8` triangles. -/
def majGroup23 : List MajRow :=
  [⟨3, 12, 0, 68, true, 0, 0, 1⟩, ⟨3, 13, 0, 68, false, 0, 0, 1⟩, ⟨3, 13, 0, 72, true, 0, 0, 1⟩,
   ⟨3, 14, 0, 72, false, 0, 0, 1⟩, ⟨3, 14, 0, 76, true, 0, 0, 1⟩, ⟨3, 15, 0, 76, false, 0, 0, 1⟩,
   ⟨3, 15, 0, 80, true, 0, 0, 1⟩, ⟨3, 16, 0, 80, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup23_ok : majGroup23.all (fun r => r.check) = true := by decide +kernel

/-- Group `24` of the majorization certificate: `8` triangles. -/
def majGroup24 : List MajRow :=
  [⟨3, 16, 0, 84, true, 0, 0, 1⟩, ⟨3, 17, 0, 84, false, 0, 0, 1⟩, ⟨3, 17, 0, 88, true, 0, 0, 1⟩,
   ⟨3, 18, 0, 88, false, 0, 0, 1⟩, ⟨3, 18, 0, 92, true, 0, 0, 1⟩, ⟨3, 19, 0, 92, false, 0, 0, 1⟩,
   ⟨3, 19, 0, 96, true, 0, 0, 1⟩, ⟨3, 20, 0, 96, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup24_ok : majGroup24.all (fun r => r.check) = true := by decide +kernel

/-- Shard `1` of the majorization certificate: `104` triangles. -/
def majShard1 : List MajRow :=
  majGroup12 ++ majGroup13 ++ majGroup14 ++ majGroup15 ++ majGroup16 ++ majGroup17 ++ majGroup18 ++
    majGroup19 ++ majGroup20 ++ majGroup21 ++ majGroup22 ++ majGroup23 ++ majGroup24

set_option maxRecDepth 4000 in
theorem majShard1_length : majShard1.length = 104 := by rfl

/-- **Every triangle of shard `1` passes its Bernstein test.** -/
theorem majShard1_ok : majShard1.all (fun r => r.check) = true := by
  simp only [majShard1, List.all_append, Bool.and_eq_true, majGroup12_ok,
    majGroup13_ok,
    majGroup14_ok,
    majGroup15_ok,
    majGroup16_ok,
    majGroup17_ok,
    majGroup18_ok,
    majGroup19_ok,
    majGroup20_ok,
    majGroup21_ok,
    majGroup22_ok,
    majGroup23_ok,
    majGroup24_ok,
    and_self]

end CenteredMaximal.Fractional

end
