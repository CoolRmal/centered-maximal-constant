/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.AntiRadial

/-!
# The rational coefficients of the two tail series at `α = 6/5`

`CenteredMaximal.Fractional.tailCoeffQ` is the radial tail coefficient at `α = 6/5`, *exactly*, as
a rational.  The anti-radial reserve needs the same for its even counterpart, and both series have
to be moved across the cast `ℚ → ℝ` before a certificate row can check them by kernel reduction.
This file supplies both, and is deliberately **computable** — like the `tailCoeffQ` section of
`CenteredMaximal.Fractional.TailSeries`, it lives outside any `noncomputable section`, because
`decide +kernel` has to evaluate the recursion.

## Main results

* `evenTailCoeffQ`, `evenTailCoeffQ_eq`, `evenTailCoeffQ_nonneg`: the even tail coefficient as an
  exact rational.
* `tailSum_cast`, `tailDerSum_cast`, `evenSum_cast`, `evenDerSum_cast`: the four truncated series
  that `fullMinorant` reads, each as the cast of an exact rational.
-/

@[expose] public section

namespace CenteredMaximal.Fractional

/-- The even part of the tail coefficient sequence at `α = 6/5`, exactly, as a rational. -/
def evenTailCoeffQ (n : ℕ) : ℚ := if n % 2 = 0 then tailCoeffQ n else 0

theorem evenTailCoeffQ_nonneg (n : ℕ) : 0 ≤ evenTailCoeffQ n := by
  rw [evenTailCoeffQ]
  split
  · exact (tailCoeffQ_pos n).le
  · exact le_refl 0

/-- **The even coefficients at `α = 6/5` are exactly rational.** -/
theorem evenTailCoeffQ_eq (n : ℕ) : ((evenTailCoeffQ n : ℚ) : ℝ) = evenTailCoeff (6 / 5) n := by
  rw [evenTailCoeffQ, evenTailCoeff]
  split
  · exact tailCoeffQ_eq n
  · rw [Rat.cast_zero]

/-- The truncated radial tail series at a rational argument is the cast of an exact rational. -/
theorem tailSum_cast (K : ℕ) (x : ℚ) :
    ∑ n ∈ Finset.range K, tailCoeff (6 / 5) n * (x : ℝ) ^ n
      = ((∑ n ∈ Finset.range K, tailCoeffQ n * x ^ n : ℚ) : ℝ) := by
  push_cast
  exact Finset.sum_congr rfl fun n _ => by rw [tailCoeffQ_eq]

/-- The same for the derivative sum of the radial series. -/
theorem tailDerSum_cast (K : ℕ) (x : ℚ) :
    ∑ n ∈ Finset.range K, tailCoeff (6 / 5) n * (n : ℝ) * (x : ℝ) ^ (n - 1)
      = ((∑ n ∈ Finset.range K, tailCoeffQ n * (n : ℚ) * x ^ (n - 1) : ℚ) : ℝ) := by
  push_cast
  exact Finset.sum_congr rfl fun n _ => by rw [tailCoeffQ_eq]

/-- The truncated even tail series at a rational argument is the cast of an exact rational. -/
theorem evenSum_cast (L : ℕ) (x : ℚ) :
    ∑ n ∈ Finset.range L, evenTailCoeff (6 / 5) n * (x : ℝ) ^ n
      = ((∑ n ∈ Finset.range L, evenTailCoeffQ n * x ^ n : ℚ) : ℝ) := by
  push_cast
  exact Finset.sum_congr rfl fun n _ => by rw [evenTailCoeffQ_eq]

/-- The same for the derivative sum of the even series. -/
theorem evenDerSum_cast (L : ℕ) (x : ℚ) :
    ∑ n ∈ Finset.range L, evenTailCoeff (6 / 5) n * (n : ℝ) * (x : ℝ) ^ (n - 1)
      = ((∑ n ∈ Finset.range L, evenTailCoeffQ n * (n : ℚ) * x ^ (n - 1) : ℚ) : ℝ) := by
  push_cast
  exact Finset.sum_congr rfl fun n _ => by rw [evenTailCoeffQ_eq]

end CenteredMaximal.Fractional

end
