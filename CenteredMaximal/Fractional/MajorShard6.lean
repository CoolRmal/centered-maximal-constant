/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.MajorRow

/-!
# The majorization certificate of the `α = 6/5` comparison kernel, shard 6

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

/-- Group `76` of the majorization certificate: `8` triangles. -/
def majGroup76 : List MajRow :=
  [⟨13, 9, 0, 96, true, 0, 0, 1⟩, ⟨13, 10, 0, 96, false, 0, 0, 1⟩,
   ⟨13, 10, 0, 100, true, 0, 0, 1⟩, ⟨13, 11, 0, 100, false, 0, 0, 1⟩,
   ⟨13, 11, 0, 104, true, 0, 0, 1⟩, ⟨13, 12, 0, 104, false, 0, 0, 1⟩,
   ⟨13, 12, 0, 108, true, 0, 0, 1⟩, ⟨13, 13, 0, 108, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup76_ok : majGroup76.all (fun r => r.check) = true := by decide +kernel

/-- Group `77` of the majorization certificate: `8` triangles. -/
def majGroup77 : List MajRow :=
  [⟨13, 13, 0, 112, true, 0, 0, 1⟩, ⟨13, 14, 0, 112, false, 0, 0, 1⟩,
   ⟨14, 0, 1, 60, false, 0, 0, 1⟩, ⟨14, 0, 1, 64, true, 0, 0, 1⟩, ⟨14, 1, 1, 64, false, 0, 0, 1⟩,
   ⟨14, 1, 0, 68, true, 0, 0, 1⟩, ⟨14, 2, 0, 68, false, 0, 0, 1⟩, ⟨14, 2, 0, 72, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup77_ok : majGroup77.all (fun r => r.check) = true := by decide +kernel

/-- Group `78` of the majorization certificate: `8` triangles. -/
def majGroup78 : List MajRow :=
  [⟨14, 3, 0, 72, false, 0, 0, 1⟩, ⟨14, 3, 0, 76, true, 0, 0, 1⟩, ⟨14, 4, 0, 76, false, 0, 0, 1⟩,
   ⟨14, 4, 0, 80, true, 0, 0, 1⟩, ⟨14, 5, 0, 80, false, 0, 0, 1⟩, ⟨14, 5, 0, 84, true, 0, 0, 1⟩,
   ⟨14, 6, 0, 84, false, 0, 0, 1⟩, ⟨14, 6, 0, 88, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup78_ok : majGroup78.all (fun r => r.check) = true := by decide +kernel

/-- Group `79` of the majorization certificate: `8` triangles. -/
def majGroup79 : List MajRow :=
  [⟨14, 7, 0, 88, false, 0, 0, 1⟩, ⟨14, 7, 0, 92, true, 0, 0, 1⟩, ⟨14, 8, 0, 92, false, 0, 0, 1⟩,
   ⟨14, 8, 0, 96, true, 0, 0, 1⟩, ⟨14, 9, 0, 96, false, 0, 0, 1⟩, ⟨14, 9, 0, 100, true, 0, 0, 1⟩,
   ⟨14, 10, 0, 100, false, 0, 0, 1⟩, ⟨14, 10, 0, 104, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup79_ok : majGroup79.all (fun r => r.check) = true := by decide +kernel

/-- Group `80` of the majorization certificate: `8` triangles. -/
def majGroup80 : List MajRow :=
  [⟨14, 11, 0, 104, false, 0, 0, 1⟩, ⟨14, 11, 0, 108, true, 0, 0, 1⟩,
   ⟨14, 12, 0, 108, false, 0, 0, 1⟩, ⟨14, 12, 0, 112, true, 0, 0, 1⟩,
   ⟨14, 13, 0, 112, false, 0, 0, 1⟩, ⟨15, 0, 1, 64, false, 0, 0, 1⟩,
   ⟨15, 0, 0, 68, true, 0, 0, 1⟩, ⟨15, 1, 0, 68, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup80_ok : majGroup80.all (fun r => r.check) = true := by decide +kernel

/-- Group `81` of the majorization certificate: `8` triangles. -/
def majGroup81 : List MajRow :=
  [⟨15, 1, 0, 72, true, 0, 0, 1⟩, ⟨15, 2, 0, 72, false, 0, 0, 1⟩, ⟨15, 2, 0, 76, true, 0, 0, 1⟩,
   ⟨15, 3, 0, 76, false, 0, 0, 1⟩, ⟨15, 3, 0, 80, true, 0, 0, 1⟩, ⟨15, 4, 0, 80, false, 0, 0, 1⟩,
   ⟨15, 4, 0, 84, true, 0, 0, 1⟩, ⟨15, 5, 0, 84, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup81_ok : majGroup81.all (fun r => r.check) = true := by decide +kernel

/-- Group `82` of the majorization certificate: `8` triangles. -/
def majGroup82 : List MajRow :=
  [⟨15, 5, 0, 88, true, 0, 0, 1⟩, ⟨15, 6, 0, 88, false, 0, 0, 1⟩, ⟨15, 6, 0, 92, true, 0, 0, 1⟩,
   ⟨15, 7, 0, 92, false, 0, 0, 1⟩, ⟨15, 7, 0, 96, true, 0, 0, 1⟩, ⟨15, 8, 0, 96, false, 0, 0, 1⟩,
   ⟨15, 8, 0, 100, true, 0, 0, 1⟩, ⟨15, 9, 0, 100, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup82_ok : majGroup82.all (fun r => r.check) = true := by decide +kernel

/-- Group `83` of the majorization certificate: `8` triangles. -/
def majGroup83 : List MajRow :=
  [⟨15, 9, 0, 104, true, 0, 0, 1⟩, ⟨15, 10, 0, 104, false, 0, 0, 1⟩,
   ⟨15, 10, 0, 108, true, 0, 0, 1⟩, ⟨15, 11, 0, 108, false, 0, 0, 1⟩,
   ⟨15, 11, 0, 112, true, 0, 0, 1⟩, ⟨15, 12, 0, 112, false, 0, 0, 1⟩,
   ⟨16, 0, 0, 68, false, 0, 0, 1⟩, ⟨16, 0, 0, 72, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup83_ok : majGroup83.all (fun r => r.check) = true := by decide +kernel

/-- Group `84` of the majorization certificate: `8` triangles. -/
def majGroup84 : List MajRow :=
  [⟨16, 1, 0, 72, false, 0, 0, 1⟩, ⟨16, 1, 0, 76, true, 0, 0, 1⟩, ⟨16, 2, 0, 76, false, 0, 0, 1⟩,
   ⟨16, 2, 0, 80, true, 0, 0, 1⟩, ⟨16, 3, 0, 80, false, 0, 0, 1⟩, ⟨16, 3, 0, 84, true, 0, 0, 1⟩,
   ⟨16, 4, 0, 84, false, 0, 0, 1⟩, ⟨16, 4, 0, 88, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup84_ok : majGroup84.all (fun r => r.check) = true := by decide +kernel

/-- Group `85` of the majorization certificate: `8` triangles. -/
def majGroup85 : List MajRow :=
  [⟨16, 5, 0, 88, false, 0, 0, 1⟩, ⟨16, 5, 0, 92, true, 0, 0, 1⟩, ⟨16, 6, 0, 92, false, 0, 0, 1⟩,
   ⟨16, 6, 0, 96, true, 0, 0, 1⟩, ⟨16, 7, 0, 96, false, 0, 0, 1⟩, ⟨16, 7, 0, 100, true, 0, 0, 1⟩,
   ⟨16, 8, 0, 100, false, 0, 0, 1⟩, ⟨16, 8, 0, 104, true, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup85_ok : majGroup85.all (fun r => r.check) = true := by decide +kernel

/-- Group `86` of the majorization certificate: `8` triangles. -/
def majGroup86 : List MajRow :=
  [⟨16, 9, 0, 104, false, 0, 0, 1⟩, ⟨16, 9, 0, 108, true, 0, 0, 1⟩,
   ⟨16, 10, 0, 108, false, 0, 0, 1⟩, ⟨16, 10, 0, 112, true, 0, 0, 1⟩,
   ⟨16, 11, 0, 112, false, 0, 0, 1⟩, ⟨17, 0, 0, 72, false, 0, 0, 1⟩,
   ⟨17, 0, 0, 76, true, 0, 0, 1⟩, ⟨17, 1, 0, 76, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup86_ok : majGroup86.all (fun r => r.check) = true := by decide +kernel

/-- Group `87` of the majorization certificate: `8` triangles. -/
def majGroup87 : List MajRow :=
  [⟨17, 1, 0, 80, true, 0, 0, 1⟩, ⟨17, 2, 0, 80, false, 0, 0, 1⟩, ⟨17, 2, 0, 84, true, 0, 0, 1⟩,
   ⟨17, 3, 0, 84, false, 0, 0, 1⟩, ⟨17, 3, 0, 88, true, 0, 0, 1⟩, ⟨17, 4, 0, 88, false, 0, 0, 1⟩,
   ⟨17, 4, 0, 92, true, 0, 0, 1⟩, ⟨17, 5, 0, 92, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup87_ok : majGroup87.all (fun r => r.check) = true := by decide +kernel

/-- Group `88` of the majorization certificate: `8` triangles. -/
def majGroup88 : List MajRow :=
  [⟨17, 5, 0, 96, true, 0, 0, 1⟩, ⟨17, 6, 0, 96, false, 0, 0, 1⟩, ⟨17, 6, 0, 100, true, 0, 0, 1⟩,
   ⟨17, 7, 0, 100, false, 0, 0, 1⟩, ⟨17, 7, 0, 104, true, 0, 0, 1⟩,
   ⟨17, 8, 0, 104, false, 0, 0, 1⟩, ⟨17, 8, 0, 108, true, 0, 0, 1⟩,
   ⟨17, 9, 0, 108, false, 0, 0, 1⟩]

set_option maxRecDepth 4000000 in
theorem majGroup88_ok : majGroup88.all (fun r => r.check) = true := by decide +kernel

/-- Shard `6` of the majorization certificate: `104` triangles. -/
def majShard6 : List MajRow :=
  majGroup76 ++ majGroup77 ++ majGroup78 ++ majGroup79 ++ majGroup80 ++ majGroup81 ++ majGroup82 ++
    majGroup83 ++ majGroup84 ++ majGroup85 ++ majGroup86 ++ majGroup87 ++ majGroup88

set_option maxRecDepth 4000 in
theorem majShard6_length : majShard6.length = 104 := by rfl

/-- **Every triangle of shard `6` passes its Bernstein test.** -/
theorem majShard6_ok : majShard6.all (fun r => r.check) = true := by
  simp only [majShard6, List.all_append, Bool.and_eq_true, majGroup76_ok,
    majGroup77_ok,
    majGroup78_ok,
    majGroup79_ok,
    majGroup80_ok,
    majGroup81_ok,
    majGroup82_ok,
    majGroup83_ok,
    majGroup84_ok,
    majGroup85_ok,
    majGroup86_ok,
    majGroup87_ok,
    majGroup88_ok,
    and_self]

end CenteredMaximal.Fractional

end
