/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.MajorRow

/-!
# The majorization certificate of the `α = 6/5` comparison kernel, shard 2

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

/-- Group `25` of the majorization certificate: `8` triangles. -/
def majGroup25 : List MajRow :=
  [⟨3, 20, 0, 100, true, 0, 0, 1⟩, ⟨3, 21, 0, 100, false, 0, 0, 1⟩,
   ⟨3, 21, 0, 104, true, 0, 0, 1⟩, ⟨3, 22, 0, 104, false, 0, 0, 1⟩,
   ⟨3, 22, 0, 108, true, 0, 0, 1⟩, ⟨3, 23, 0, 108, false, 0, 0, 1⟩,
   ⟨3, 23, 0, 112, true, 0, 0, 1⟩, ⟨3, 24, 0, 112, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup25_ok : majGroup25.all (fun r => r.check) = true := by decide +kernel

/-- Group `26` of the majorization certificate: `8` triangles. -/
def majGroup26 : List MajRow :=
  [⟨4, 0, 1, 20, false, 0, 0, 1⟩, ⟨4, 0, 1, 24, true, 0, 0, 1⟩, ⟨4, 1, 1, 24, false, 0, 0, 1⟩,
   ⟨4, 1, 1, 28, true, 0, 0, 1⟩, ⟨4, 2, 1, 28, false, 0, 0, 1⟩, ⟨4, 2, 1, 32, true, 0, 0, 1⟩,
   ⟨4, 3, 1, 32, false, 0, 0, 1⟩, ⟨4, 3, 1, 36, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup26_ok : majGroup26.all (fun r => r.check) = true := by decide +kernel

/-- Group `27` of the majorization certificate: `8` triangles. -/
def majGroup27 : List MajRow :=
  [⟨4, 4, 1, 36, false, 0, 0, 1⟩, ⟨4, 4, 1, 40, true, 0, 0, 1⟩, ⟨4, 5, 1, 40, false, 0, 0, 1⟩,
   ⟨4, 5, 1, 44, true, 0, 0, 1⟩, ⟨4, 6, 1, 44, false, 0, 0, 1⟩, ⟨4, 6, 1, 48, true, 0, 0, 1⟩,
   ⟨4, 7, 1, 48, false, 0, 0, 1⟩, ⟨4, 7, 1, 52, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup27_ok : majGroup27.all (fun r => r.check) = true := by decide +kernel

/-- Group `28` of the majorization certificate: `8` triangles. -/
def majGroup28 : List MajRow :=
  [⟨4, 8, 1, 52, false, 0, 0, 1⟩, ⟨4, 8, 1, 56, true, 0, 0, 1⟩, ⟨4, 9, 1, 56, false, 0, 0, 1⟩,
   ⟨4, 9, 1, 60, true, 0, 0, 1⟩, ⟨4, 10, 1, 60, false, 0, 0, 1⟩, ⟨4, 10, 1, 64, true, 0, 0, 1⟩,
   ⟨4, 11, 1, 64, false, 0, 0, 1⟩, ⟨4, 11, 0, 68, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup28_ok : majGroup28.all (fun r => r.check) = true := by decide +kernel

/-- Group `29` of the majorization certificate: `8` triangles. -/
def majGroup29 : List MajRow :=
  [⟨4, 12, 0, 68, false, 0, 0, 1⟩, ⟨4, 12, 0, 72, true, 0, 0, 1⟩, ⟨4, 13, 0, 72, false, 0, 0, 1⟩,
   ⟨4, 13, 0, 76, true, 0, 0, 1⟩, ⟨4, 14, 0, 76, false, 0, 0, 1⟩, ⟨4, 14, 0, 80, true, 0, 0, 1⟩,
   ⟨4, 15, 0, 80, false, 0, 0, 1⟩, ⟨4, 15, 0, 84, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup29_ok : majGroup29.all (fun r => r.check) = true := by decide +kernel

/-- Group `30` of the majorization certificate: `8` triangles. -/
def majGroup30 : List MajRow :=
  [⟨4, 16, 0, 84, false, 0, 0, 1⟩, ⟨4, 16, 0, 88, true, 0, 0, 1⟩, ⟨4, 17, 0, 88, false, 0, 0, 1⟩,
   ⟨4, 17, 0, 92, true, 0, 0, 1⟩, ⟨4, 18, 0, 92, false, 0, 0, 1⟩, ⟨4, 18, 0, 96, true, 0, 0, 1⟩,
   ⟨4, 19, 0, 96, false, 0, 0, 1⟩, ⟨4, 19, 0, 100, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup30_ok : majGroup30.all (fun r => r.check) = true := by decide +kernel

/-- Group `31` of the majorization certificate: `8` triangles. -/
def majGroup31 : List MajRow :=
  [⟨4, 20, 0, 100, false, 0, 0, 1⟩, ⟨4, 20, 0, 104, true, 0, 0, 1⟩,
   ⟨4, 21, 0, 104, false, 0, 0, 1⟩, ⟨4, 21, 0, 108, true, 0, 0, 1⟩,
   ⟨4, 22, 0, 108, false, 0, 0, 1⟩, ⟨4, 22, 0, 112, true, 0, 0, 1⟩,
   ⟨4, 23, 0, 112, false, 0, 0, 1⟩, ⟨5, 0, 1, 24, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup31_ok : majGroup31.all (fun r => r.check) = true := by decide +kernel

/-- Group `32` of the majorization certificate: `8` triangles. -/
def majGroup32 : List MajRow :=
  [⟨5, 0, 1, 28, true, 0, 0, 1⟩, ⟨5, 1, 1, 28, false, 0, 0, 1⟩, ⟨5, 1, 1, 32, true, 0, 0, 1⟩,
   ⟨5, 2, 1, 32, false, 0, 0, 1⟩, ⟨5, 2, 1, 36, true, 0, 0, 1⟩, ⟨5, 3, 1, 36, false, 0, 0, 1⟩,
   ⟨5, 3, 1, 40, true, 0, 0, 1⟩, ⟨5, 4, 1, 40, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup32_ok : majGroup32.all (fun r => r.check) = true := by decide +kernel

/-- Group `33` of the majorization certificate: `8` triangles. -/
def majGroup33 : List MajRow :=
  [⟨5, 4, 1, 44, true, 0, 0, 1⟩, ⟨5, 5, 1, 44, false, 0, 0, 1⟩, ⟨5, 5, 1, 48, true, 0, 0, 1⟩,
   ⟨5, 6, 1, 48, false, 0, 0, 1⟩, ⟨5, 6, 1, 52, true, 0, 0, 1⟩, ⟨5, 7, 1, 52, false, 0, 0, 1⟩,
   ⟨5, 7, 1, 56, true, 0, 0, 1⟩, ⟨5, 8, 1, 56, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup33_ok : majGroup33.all (fun r => r.check) = true := by decide +kernel

/-- Group `34` of the majorization certificate: `8` triangles. -/
def majGroup34 : List MajRow :=
  [⟨5, 8, 1, 60, true, 0, 0, 1⟩, ⟨5, 9, 1, 60, false, 0, 0, 1⟩, ⟨5, 9, 1, 64, true, 0, 0, 1⟩,
   ⟨5, 10, 1, 64, false, 0, 0, 1⟩, ⟨5, 10, 0, 68, true, 0, 0, 1⟩, ⟨5, 11, 0, 68, false, 0, 0, 1⟩,
   ⟨5, 11, 0, 72, true, 0, 0, 1⟩, ⟨5, 12, 0, 72, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup34_ok : majGroup34.all (fun r => r.check) = true := by decide +kernel

/-- Group `35` of the majorization certificate: `8` triangles. -/
def majGroup35 : List MajRow :=
  [⟨5, 12, 0, 76, true, 0, 0, 1⟩, ⟨5, 13, 0, 76, false, 0, 0, 1⟩, ⟨5, 13, 0, 80, true, 0, 0, 1⟩,
   ⟨5, 14, 0, 80, false, 0, 0, 1⟩, ⟨5, 14, 0, 84, true, 0, 0, 1⟩, ⟨5, 15, 0, 84, false, 0, 0, 1⟩,
   ⟨5, 15, 0, 88, true, 0, 0, 1⟩, ⟨5, 16, 0, 88, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup35_ok : majGroup35.all (fun r => r.check) = true := by decide +kernel

/-- Group `36` of the majorization certificate: `8` triangles. -/
def majGroup36 : List MajRow :=
  [⟨5, 16, 0, 92, true, 0, 0, 1⟩, ⟨5, 17, 0, 92, false, 0, 0, 1⟩, ⟨5, 17, 0, 96, true, 0, 0, 1⟩,
   ⟨5, 18, 0, 96, false, 0, 0, 1⟩, ⟨5, 18, 0, 100, true, 0, 0, 1⟩,
   ⟨5, 19, 0, 100, false, 0, 0, 1⟩, ⟨5, 19, 0, 104, true, 0, 0, 1⟩,
   ⟨5, 20, 0, 104, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup36_ok : majGroup36.all (fun r => r.check) = true := by decide +kernel

/-- Group `37` of the majorization certificate: `8` triangles. -/
def majGroup37 : List MajRow :=
  [⟨5, 20, 0, 108, true, 0, 0, 1⟩, ⟨5, 21, 0, 108, false, 0, 0, 1⟩,
   ⟨5, 21, 0, 112, true, 0, 0, 1⟩, ⟨5, 22, 0, 112, false, 0, 0, 1⟩, ⟨6, 0, 1, 28, false, 0, 0, 1⟩,
   ⟨6, 0, 1, 32, true, 0, 0, 1⟩, ⟨6, 1, 1, 32, false, 0, 0, 1⟩, ⟨6, 1, 1, 36, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup37_ok : majGroup37.all (fun r => r.check) = true := by decide +kernel

/-- Shard `2` of the majorization certificate: `104` triangles. -/
def majShard2 : List MajRow :=
  majGroup25 ++ majGroup26 ++ majGroup27 ++ majGroup28 ++ majGroup29 ++ majGroup30 ++ majGroup31 ++
    majGroup32 ++ majGroup33 ++ majGroup34 ++ majGroup35 ++ majGroup36 ++ majGroup37

set_option maxRecDepth 4000 in
theorem majShard2_length : majShard2.length = 104 := by rfl

/-- **Every triangle of shard `2` passes its Bernstein test.** -/
theorem majShard2_ok : majShard2.all (fun r => r.check) = true := by
  simp only [majShard2, List.all_append, Bool.and_eq_true, majGroup25_ok,
    majGroup26_ok,
    majGroup27_ok,
    majGroup28_ok,
    majGroup29_ok,
    majGroup30_ok,
    majGroup31_ok,
    majGroup32_ok,
    majGroup33_ok,
    majGroup34_ok,
    majGroup35_ok,
    majGroup36_ok,
    majGroup37_ok,
    and_self]

end CenteredMaximal.Fractional

end
