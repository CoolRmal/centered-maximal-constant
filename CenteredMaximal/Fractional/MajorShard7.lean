/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.MajorRow

/-!
# The majorization certificate of the `α = 6/5` comparison kernel, shard 7

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

/-- Group `89` of the majorization certificate: `8` triangles. -/
def majGroup89 : List MajRow :=
  [⟨17, 9, 0, 112, true, 0, 0, 1⟩, ⟨17, 10, 0, 112, false, 0, 0, 1⟩,
   ⟨18, 0, 0, 76, false, 0, 0, 1⟩, ⟨18, 0, 0, 80, true, 0, 0, 1⟩, ⟨18, 1, 0, 80, false, 0, 0, 1⟩,
   ⟨18, 1, 0, 84, true, 0, 0, 1⟩, ⟨18, 2, 0, 84, false, 0, 0, 1⟩, ⟨18, 2, 0, 88, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup89_ok : majGroup89.all (fun r => r.check) = true := by decide +kernel

/-- Group `90` of the majorization certificate: `8` triangles. -/
def majGroup90 : List MajRow :=
  [⟨18, 3, 0, 88, false, 0, 0, 1⟩, ⟨18, 3, 0, 92, true, 0, 0, 1⟩, ⟨18, 4, 0, 92, false, 0, 0, 1⟩,
   ⟨18, 4, 0, 96, true, 0, 0, 1⟩, ⟨18, 5, 0, 96, false, 0, 0, 1⟩, ⟨18, 5, 0, 100, true, 0, 0, 1⟩,
   ⟨18, 6, 0, 100, false, 0, 0, 1⟩, ⟨18, 6, 0, 104, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup90_ok : majGroup90.all (fun r => r.check) = true := by decide +kernel

/-- Group `91` of the majorization certificate: `8` triangles. -/
def majGroup91 : List MajRow :=
  [⟨18, 7, 0, 104, false, 0, 0, 1⟩, ⟨18, 7, 0, 108, true, 0, 0, 1⟩,
   ⟨18, 8, 0, 108, false, 0, 0, 1⟩, ⟨18, 8, 0, 112, true, 0, 0, 1⟩,
   ⟨18, 9, 0, 112, false, 0, 0, 1⟩, ⟨19, 0, 0, 80, false, 0, 0, 1⟩, ⟨19, 0, 0, 84, true, 0, 0, 1⟩,
   ⟨19, 1, 0, 84, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup91_ok : majGroup91.all (fun r => r.check) = true := by decide +kernel

/-- Group `92` of the majorization certificate: `8` triangles. -/
def majGroup92 : List MajRow :=
  [⟨19, 1, 0, 88, true, 0, 0, 1⟩, ⟨19, 2, 0, 88, false, 0, 0, 1⟩, ⟨19, 2, 0, 92, true, 0, 0, 1⟩,
   ⟨19, 3, 0, 92, false, 0, 0, 1⟩, ⟨19, 3, 0, 96, true, 0, 0, 1⟩, ⟨19, 4, 0, 96, false, 0, 0, 1⟩,
   ⟨19, 4, 0, 100, true, 0, 0, 1⟩, ⟨19, 5, 0, 100, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup92_ok : majGroup92.all (fun r => r.check) = true := by decide +kernel

/-- Group `93` of the majorization certificate: `8` triangles. -/
def majGroup93 : List MajRow :=
  [⟨19, 5, 0, 104, true, 0, 0, 1⟩, ⟨19, 6, 0, 104, false, 0, 0, 1⟩,
   ⟨19, 6, 0, 108, true, 0, 0, 1⟩, ⟨19, 7, 0, 108, false, 0, 0, 1⟩,
   ⟨19, 7, 0, 112, true, 0, 0, 1⟩, ⟨19, 8, 0, 112, false, 0, 0, 1⟩,
   ⟨20, 0, 0, 84, false, 0, 0, 1⟩, ⟨20, 0, 0, 88, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup93_ok : majGroup93.all (fun r => r.check) = true := by decide +kernel

/-- Group `94` of the majorization certificate: `8` triangles. -/
def majGroup94 : List MajRow :=
  [⟨20, 1, 0, 88, false, 0, 0, 1⟩, ⟨20, 1, 0, 92, true, 0, 0, 1⟩, ⟨20, 2, 0, 92, false, 0, 0, 1⟩,
   ⟨20, 2, 0, 96, true, 0, 0, 1⟩, ⟨20, 3, 0, 96, false, 0, 0, 1⟩, ⟨20, 3, 0, 100, true, 0, 0, 1⟩,
   ⟨20, 4, 0, 100, false, 0, 0, 1⟩, ⟨20, 4, 0, 104, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup94_ok : majGroup94.all (fun r => r.check) = true := by decide +kernel

/-- Group `95` of the majorization certificate: `8` triangles. -/
def majGroup95 : List MajRow :=
  [⟨20, 5, 0, 104, false, 0, 0, 1⟩, ⟨20, 5, 0, 108, true, 0, 0, 1⟩,
   ⟨20, 6, 0, 108, false, 0, 0, 1⟩, ⟨20, 6, 0, 112, true, 0, 0, 1⟩,
   ⟨20, 7, 0, 112, false, 0, 0, 1⟩, ⟨21, 0, 0, 88, false, 0, 0, 1⟩, ⟨21, 0, 0, 92, true, 0, 0, 1⟩,
   ⟨21, 1, 0, 92, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup95_ok : majGroup95.all (fun r => r.check) = true := by decide +kernel

/-- Group `96` of the majorization certificate: `8` triangles. -/
def majGroup96 : List MajRow :=
  [⟨21, 1, 0, 96, true, 0, 0, 1⟩, ⟨21, 2, 0, 96, false, 0, 0, 1⟩, ⟨21, 2, 0, 100, true, 0, 0, 1⟩,
   ⟨21, 3, 0, 100, false, 0, 0, 1⟩, ⟨21, 3, 0, 104, true, 0, 0, 1⟩,
   ⟨21, 4, 0, 104, false, 0, 0, 1⟩, ⟨21, 4, 0, 108, true, 0, 0, 1⟩,
   ⟨21, 5, 0, 108, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup96_ok : majGroup96.all (fun r => r.check) = true := by decide +kernel

/-- Group `97` of the majorization certificate: `8` triangles. -/
def majGroup97 : List MajRow :=
  [⟨21, 5, 0, 112, true, 0, 0, 1⟩, ⟨21, 6, 0, 112, false, 0, 0, 1⟩,
   ⟨22, 0, 0, 92, false, 0, 0, 1⟩, ⟨22, 0, 0, 96, true, 0, 0, 1⟩, ⟨22, 1, 0, 96, false, 0, 0, 1⟩,
   ⟨22, 1, 0, 100, true, 0, 0, 1⟩, ⟨22, 2, 0, 100, false, 0, 0, 1⟩,
   ⟨22, 2, 0, 104, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup97_ok : majGroup97.all (fun r => r.check) = true := by decide +kernel

/-- Group `98` of the majorization certificate: `8` triangles. -/
def majGroup98 : List MajRow :=
  [⟨22, 3, 0, 104, false, 0, 0, 1⟩, ⟨22, 3, 0, 108, true, 0, 0, 1⟩,
   ⟨22, 4, 0, 108, false, 0, 0, 1⟩, ⟨22, 4, 0, 112, true, 0, 0, 1⟩,
   ⟨22, 5, 0, 112, false, 0, 0, 1⟩, ⟨23, 0, 0, 96, false, 0, 0, 1⟩,
   ⟨23, 0, 0, 100, true, 0, 0, 1⟩, ⟨23, 1, 0, 100, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup98_ok : majGroup98.all (fun r => r.check) = true := by decide +kernel

/-- Group `99` of the majorization certificate: `8` triangles. -/
def majGroup99 : List MajRow :=
  [⟨23, 1, 0, 104, true, 0, 0, 1⟩, ⟨23, 2, 0, 104, false, 0, 0, 1⟩,
   ⟨23, 2, 0, 108, true, 0, 0, 1⟩, ⟨23, 3, 0, 108, false, 0, 0, 1⟩,
   ⟨23, 3, 0, 112, true, 0, 0, 1⟩, ⟨23, 4, 0, 112, false, 0, 0, 1⟩,
   ⟨24, 0, 0, 100, false, 0, 0, 1⟩, ⟨24, 0, 0, 104, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup99_ok : majGroup99.all (fun r => r.check) = true := by decide +kernel

/-- Group `100` of the majorization certificate: `8` triangles. -/
def majGroup100 : List MajRow :=
  [⟨24, 1, 0, 104, false, 0, 0, 1⟩, ⟨24, 1, 0, 108, true, 0, 0, 1⟩,
   ⟨24, 2, 0, 108, false, 0, 0, 1⟩, ⟨24, 2, 0, 112, true, 0, 0, 1⟩,
   ⟨24, 3, 0, 112, false, 0, 0, 1⟩, ⟨25, 0, 0, 104, false, 0, 0, 1⟩,
   ⟨25, 0, 0, 108, true, 0, 0, 1⟩, ⟨25, 1, 0, 108, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup100_ok : majGroup100.all (fun r => r.check) = true := by decide +kernel

/-- Group `101` of the majorization certificate: `6` triangles. -/
def majGroup101 : List MajRow :=
  [⟨25, 1, 0, 112, true, 0, 0, 1⟩, ⟨25, 2, 0, 112, false, 0, 0, 1⟩,
   ⟨26, 0, 0, 108, false, 0, 0, 1⟩, ⟨26, 0, 0, 112, true, 0, 0, 1⟩,
   ⟨26, 1, 0, 112, false, 0, 0, 1⟩, ⟨27, 0, 0, 112, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup101_ok : majGroup101.all (fun r => r.check) = true := by decide +kernel

/-- Shard `7` of the majorization certificate: `102` triangles. -/
def majShard7 : List MajRow :=
  majGroup89 ++ majGroup90 ++ majGroup91 ++ majGroup92 ++ majGroup93 ++ majGroup94 ++ majGroup95 ++
    majGroup96 ++ majGroup97 ++ majGroup98 ++ majGroup99 ++ majGroup100 ++ majGroup101

set_option maxRecDepth 4000 in
theorem majShard7_length : majShard7.length = 102 := by rfl

/-- **Every triangle of shard `7` passes its Bernstein test.** -/
theorem majShard7_ok : majShard7.all (fun r => r.check) = true := by
  simp only [majShard7, List.all_append, Bool.and_eq_true, majGroup89_ok,
    majGroup90_ok,
    majGroup91_ok,
    majGroup92_ok,
    majGroup93_ok,
    majGroup94_ok,
    majGroup95_ok,
    majGroup96_ok,
    majGroup97_ok,
    majGroup98_ok,
    majGroup99_ok,
    majGroup100_ok,
    majGroup101_ok,
    and_self]

end CenteredMaximal.Fractional

end
