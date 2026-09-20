/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.ModelTerm
public import CenteredMaximal.Fractional.EvenCoeffQ

/-!
# The base half of a certificate leaf's polynomial model

`CenteredMaximal.Fractional.jumpGen_fracKernel_nonneg_of_terms` reads one leaf of the `α = 6/5`
generator certificate off a **single** centred polynomial model of the whole generator, carried as
two lists of `ModelTerm`s.  This file builds the list for the base half: the affine minorant
`fracBaseCoeff · fullMinorant` of the reserve of the truncated diamond base, written in the
deviations `s = 16 x − u_c`, `t = 16 y − v_c` of the grid coordinates from the centre of the leaf's
rectangle.

## Why the base contributes exactly three bidegrees

`fullMinorant` is a sum of two tangent lines: the radial tangent of `radialMinorant`, taken at `r₀`
and affine in the diamond radius `r = x + y`, and the anti-radial tangent of `antiMinorant`, taken
at `d₀` and affine in the coordinate difference `d = x − y`.  An affine function of `x + y` plus an
affine function of `x − y` is an affine function of `(x, y)`, so the base half of a leaf's model is
*exactly* a constant plus two linear terms — the bidegrees `(0, 0)`, `(1, 0)` and `(0, 1)` — and
every one of the remaining thirteen bidegrees of `modelFinset` is fed by the spline half alone.

Nothing is discarded in saying so.  `termsValR_baseTerms` is an **identity**, not a bound: the one
inequality the base half is allowed has already been spent, once, in `fullMinorant_le`, where the
two convex series were replaced by their tangents.  Everything after that point is exact rational
bookkeeping against the three enclosed powers `r₀ ^ (−12/5)`, `r₀ ^ (−17/5)` and `(7/4) ^ (−12/5)`.

## Why the two slopes are unequal

With `radialMinorant … r₀ r = a + b r` and `antiMinorant … d₀ d = c + e d`, `fullMinorant_centred`
reports the two slopes as `(b + e)/16` and `(b − e)/16`.  The anti-radial tangent enters the two
coordinates with *opposite* signs, because `d = x − y`, so the two linear coefficients differ by
`e/8`, and `e = 4 · (7/4) ^ (−12/5) · ED / (7/4)` vanishes only on the diagonal `d₀ = 0`, where the
even tail series is at its critical point.  A model of the base by a function of the radius alone
would therefore be wrong off the diagonal, which is why `baseTerms` carries `(1, 0)` and `(0, 1)`
separately rather than one common radial slope.

## Why the slopes are folded in before absolute values are taken

`leafCheckQ` tests `co (0,0) − ∑ |co p| δ ^ (p₁ + p₂) − err`, so it is the **absolute value of the
sum** of the base's and the spline's coefficients on `(1, 0)` and on `(0, 1)` that a leaf pays for.
Those two contributions nearly cancel: the spline was fitted to the base, so its gradient tracks
`−∂_r` of the base, and near the origin `|A_base|` is of size `S · r ^ (−17/5)` while
`A_base + A_spline` is `O(1)`.  Bounding the two halves separately costs a factor of about `10³`
there and fails `2674` of the `4582` rectangles; see the module docstring of
`CenteredMaximal.Fractional.CentredLeaf` for the measurement.  Hence the base's slopes are produced
here as plain `ModelTerm`s on `(1, 0)` and `(0, 1)`, to be appended to the spline's list and summed
by `termsCoR` *before* `leafCheckQ` ever takes an absolute value.

## Main results

* `fracBaseQ`, `fracBaseQ_cast`: the kernel's base coefficient as the exact rational it is.
* `baseTailQ`: the four rational tail sums a base tangent reads, evaluated **once** per leaf.
* `baseTermsQ`, `baseTerms`: **the base half of a leaf's polynomial model**, seven terms on the
  three bidegrees `(0, 0)`, `(1, 0)`, `(0, 1)`.
* `baseTerms_pos`: its bases are positive and its bidegrees are bicubic, the two side conditions
  `jumpGen_fracKernel_nonneg_of_terms` asks of a model.
* `termsValR_baseTerms`: **the base half of the model is exactly the affine minorant of the
  reserve.**
-/

@[expose] public section

noncomputable section

namespace CenteredMaximal.Fractional

/-! ### The base coefficient as a rational -/

/-- The base coefficient `a = 45006666551170177/25000000000000000` of the comparison kernel, as the
exact rational it is. -/
def fracBaseQ : ℚ := 45006666551170177 / 25000000000000000

theorem fracBaseQ_cast : ((fracBaseQ : ℚ) : ℝ) = fracBaseCoeff := by
  rw [fracBaseCoeff_eq, fracBaseQ]
  push_cast
  ring

/-! ### The four rational tail sums -/

/-- **The four rational tail sums a base tangent reads**, at the truncation radius `R = 7/4`: the
truncated radial tail series `T` and its derivative series `TD` at `ρ = r₀ / R = 4 r₀ / 7`, and the
truncated even tail series `E` and its derivative series `ED` at `σ = d₀ / R = 4 d₀ / 7`.  All four
are exact rationals, by `tailSum_cast`, `tailDerSum_cast`, `evenSum_cast` and `evenDerSum_cast`.

The natural subtraction in the two derivative sums is deliberate: it is the form in which the four
cast lemmas are stated, and the `n = 0` term carries the factor `n` and so vanishes anyway. -/
def baseTailQ (K Ltail : ℕ) (r₀ d₀ : ℚ) : ℚ × ℚ × ℚ × ℚ :=
  (∑ n ∈ Finset.range K, tailCoeffQ n * (r₀ * 4 / 7) ^ n,
    ∑ n ∈ Finset.range K, tailCoeffQ n * (n : ℚ) * (r₀ * 4 / 7) ^ (n - 1),
    ∑ n ∈ Finset.range Ltail, evenTailCoeffQ n * (d₀ * 4 / 7) ^ n,
    ∑ n ∈ Finset.range Ltail, evenTailCoeffQ n * (n : ℚ) * (d₀ * 4 / 7) ^ (n - 1))

/-! ### The terms of the base half -/

/-- The base half of a leaf's model, given the four tail sums of `baseTailQ` already evaluated.

The three enclosed powers are `r₀ ^ (−12/5)`, `r₀ ^ (−17/5)` and `(7/4) ^ (−12/5)`, written as the
`ModelTerm` exponent numerators `-12`, `-17` and `-12`.  Only `r₀ ^ (−12/5)` fails to appear on the
two linear bidegrees: it is the value, not the slope, of the intrinsic power's tangent.

The scalars are shared through three `let`s: `aS = a · S`, the slope magnitude `sl = 3 a S / 20`
of the intrinsic tangent — which is `±` one of three coefficients — and `a7 = a / 7`.  So the base
coefficient `a`, whose denominator is `2.5 · 10^16`, enters three rational operations rather than
the seven a term-by-term spelling would need, and the four tail sums enter `baseTermsQ` already
evaluated.  See the module docstring of `CenteredMaximal.Fractional.MajorCell` for why a `Rat.mul`
with a large denominator is worth avoiding. -/
def baseTermsQ (S r₀ d₀ uc vc : ℚ) (t : ℚ × ℚ × ℚ × ℚ) : List ModelTerm :=
  let T := t.1
  let TD := t.2.1
  let E := t.2.2.1
  let ED := t.2.2.2
  let aS := fracBaseQ * S
  let sl := aS * (3 / 20)
  let a7 := fracBaseQ / 7
  [⟨0, 0, aS, r₀, -12⟩,
    ⟨0, 0, sl * (16 * r₀ - uc - vc), r₀, -17⟩,
    ⟨0, 0, 4 * fracBaseQ * (T - TD * (r₀ * 4 / 7) + E - ED * (d₀ * 4 / 7))
      + a7 * (TD * (uc + vc) + ED * (uc - vc)), 7 / 4, -12⟩,
    ⟨1, 0, -sl, r₀, -17⟩,
    ⟨1, 0, a7 * (TD + ED), 7 / 4, -12⟩,
    ⟨0, 1, -sl, r₀, -17⟩,
    ⟨0, 1, a7 * (TD - ED), 7 / 4, -12⟩]

/-- **The base half of a leaf's polynomial model**, seven terms on the three bidegrees `(0, 0)`,
`(1, 0)`, `(0, 1)`.  The four tail sums are evaluated once, by the single application of
`baseTailQ`, and reused by all seven terms. -/
def baseTerms (S r₀ d₀ : ℚ) (K Ltail : ℕ) (uc vc : ℚ) : List ModelTerm :=
  baseTermsQ S r₀ d₀ uc vc (baseTailQ K Ltail r₀ d₀)

/-- The two side conditions `jumpGen_fracKernel_nonneg_of_terms` asks of a model: every base of a
power is positive, and every bidegree is bicubic. -/
theorem baseTerms_pos {S r₀ d₀ : ℚ} (hr₀ : 0 < r₀) (K Ltail : ℕ) (uc vc : ℚ) :
    ∀ w ∈ baseTerms S r₀ d₀ K Ltail uc vc, 0 < w.x ∧ w.a < 4 ∧ w.b < 4 := by
  intro w hw
  simp only [baseTerms, baseTermsQ, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine ⟨?_, by norm_num, by norm_num⟩ <;> first | exact hr₀ | norm_num

/-! ### The identity -/

set_option linter.unusedVariables false in
/-- **The base half of the model is exactly the affine minorant of the reserve.**  There is no
error term and no inequality: in the deviations `16 x − u_c`, `16 y − v_c` the seven terms of
`baseTerms` sum to `fracBaseCoeff · fullMinorant`, on the nose.

The proof is `fullMinorant_centred` with the two affine forms `radialMinorant_eq_affine` and
`antiMinorant_eq_affine` supplied, followed by the four cast lemmas of
`CenteredMaximal.Fractional.EvenCoeffQ`, which replace each truncated series at the rational
argument `4 r₀ / 7` or `4 d₀ / 7` by the cast of the exact rational `baseTailQ` computes.  What is
left is a rational identity between the coefficients of the three enclosed powers.

`hr₀` is carried for uniformity with `baseTerms_pos` and with the leaf assembly; the identity
itself holds at every `r₀`, because both sides read the *same* `Real.rpow` of `r₀`. -/
theorem termsValR_baseTerms {S r₀ d₀ : ℚ} (hr₀ : 0 < r₀) (K Ltail : ℕ) (uc vc : ℚ) (x y : ℝ) :
    termsValR (baseTerms S r₀ d₀ K Ltail uc vc) (16 * x - (uc : ℝ)) (16 * y - (vc : ℝ))
      = fracBaseCoeff *
          fullMinorant (6 / 5) (7 / 4) (S : ℝ) K Ltail (r₀ : ℝ) (d₀ : ℝ) (x + y) (x - y) := by
  have hρ : ((r₀ : ℝ) / (7 / 4)) = ((r₀ * 4 / 7 : ℚ) : ℝ) := by push_cast; ring
  have hσ : ((d₀ : ℝ) / (7 / 4)) = ((d₀ * 4 / 7 : ℚ) : ℝ) := by push_cast; ring
  have h12 : ((r₀ : ℚ) : ℝ) ^ (((-12 : ℤ) : ℝ) / 5) = (r₀ : ℝ) ^ (-(2 * (6 / 5)) : ℝ) := by
    norm_num
  have h17 : ((r₀ : ℚ) : ℝ) ^ (((-17 : ℤ) : ℝ) / 5) = (r₀ : ℝ) ^ (-(2 * (6 / 5)) - 1 : ℝ) := by
    norm_num
  have hQ : ((7 / 4 : ℚ) : ℝ) ^ (((-12 : ℤ) : ℝ) / 5) = (7 / 4 : ℝ) ^ (-2 * (6 / 5) : ℝ) := by
    norm_num
  rw [fullMinorant_centred (radialMinorant_eq_affine (6 / 5) (7 / 4) (S : ℝ) K (r₀ : ℝ))
      (antiMinorant_eq_affine (6 / 5) (7 / 4) Ltail (d₀ : ℝ)) (uc : ℝ) (vc : ℝ) x y,
    hρ, hσ, tailSum_cast, tailDerSum_cast, evenSum_cast, evenDerSum_cast]
  simp only [baseTerms, baseTermsQ, baseTailQ, termsValR, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, ModelTerm.coR]
  rw [h12, h17, hQ]
  push_cast [fracBaseQ_cast]
  ring

end CenteredMaximal.Fractional

end

end
