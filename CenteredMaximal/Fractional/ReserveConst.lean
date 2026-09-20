/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.SixFifthsArith

/-!
# The reserve constant in closed form

`Fractional/TailRadial.lean` states the generator's positive reserve with the coefficient

`-4 π Γ(2α) cos(π α / 2) / (α Γ(α)² sin(π α / 2))`,

while `Fractional/SixFifthsArith.lean` bounds the constant `sixFifthsConst`, written with a Beta
value and `tan (π / 10)`. At `α = 6/5` the two differ by exactly the factor `2` that `jumpGen`
contributes by integrating over the whole line rather than a half-line. This file records the
identification, so that the rational bound `lt_sixFifths_const` can be fed to the certificate.

## Main results

* `reserveCoeff_eq`: the reserve coefficient at `α = 6/5` is `2 * sixFifthsConst`.
* `lt_reserveCoeff`: hence it exceeds `125337337/25000000 = 5.01349348`.
-/

@[expose] public section

noncomputable section

open Real

namespace CenteredMaximal.Fractional

/-- The coefficient of `r ^ (-2α)` in the generator's positive reserve, at `α = 6/5`. -/
def reserveCoeff : ℝ :=
  -4 * π * Real.Gamma (2 * (6 / 5)) * Real.cos (π * (6 / 5) / 2) /
    ((6 / 5) * Real.Gamma (6 / 5) ^ 2 * Real.sin (π * (6 / 5) / 2))

/-- `sin (3 π / 5) > 0`, since `3 π / 5` lies in `(0, π)`. -/
theorem sin_pi_mul_sixFifths_div_two_pos : 0 < Real.sin (π * (6 / 5) / 2) := by
  have h : π * (6 / 5) / 2 = 3 * π / 5 := by ring
  rw [h]
  exact Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])

/-- **The identification.** `jumpGen` integrates over the whole line, so the reserve coefficient is
twice the constant `sixFifthsConst` that the Beta-integral bound is stated for. -/
theorem reserveCoeff_eq : reserveCoeff = 2 * sixFifthsConst := by
  have hs : Real.sin (π * (6 / 5) / 2) ≠ 0 := sin_pi_mul_sixFifths_div_two_pos.ne'
  have hG : Real.Gamma (6 / 5 : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hG2 : Real.Gamma (12 / 5 : ℝ) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hsum : (6 / 5 : ℝ) + 6 / 5 = 12 / 5 := by norm_num
  have htwo : (2 : ℝ) * (6 / 5) = 12 / 5 := by norm_num
  rw [reserveCoeff, sixFifthsConst_eq_cot, Real.cot_eq_cos_div_sin, betaFun, hsum, htwo]
  field_simp
  ring

/-- The reserve coefficient exceeds `5.01349348`. -/
theorem lt_reserveCoeff : (125337337 / 25000000 : ℝ) < reserveCoeff := by
  rw [reserveCoeff_eq]
  nlinarith [lt_sixFifths_const]

end CenteredMaximal.Fractional
