/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Data.Int.Notation
public import Mathlib.Data.List.Dedup

/-!
# The coefficient data of the `α = 6/5` comparison kernel

The comparison kernel of order `α = 6/5` with truncation radius `R = 7/4` and spline scale
`N = 16` is

`K z = a · truncBase (6/5) (7/4) z + ∑_{(i,j)} C_{ij} β(16 z₀ − i) β(16 z₁ − j)`,

and this file carries nothing but its numerical data, so that the analytic file
`CenteredMaximal.Fractional.KernelMass` stays small and the data can be swapped for a refined
candidate without touching a single proof.

Every coefficient of the certificate is an exact rational with denominator dividing
`fracDen = 5 · 10^16`, so a coefficient is stored as its **integer numerator over that one
denominator**; no rounding takes place anywhere.

## The orbit structure

The kernel is invariant under the eight symmetries of the diamond — the two independent sign flips
of the coordinates and the swap of the two coordinates — so the `1201` spline cells that occur fall
into `169` orbits, each represented by its unique member with `i ≥ j ≥ 0`. `fracOrbits` lists the
`169` representatives together with the common numerator of their orbit, `diamondOrbit` expands one
representative into its orbit (`8`, `4` or `1` cells, according to the stabiliser), and `fracCells`
is the resulting list of all `1201` cells.

## Main results

* `fracOrbits`, `diamondOrbit`, `fracCells`: the data and its expansion.
* `fracOrbits_length`, `fracCells_length`: there are `169` orbits and `1201` cells.
* `fracCellSumNum_eq`: `∑ C = −15451820578328440516 / (5 · 10^16) = −309.0364115666…`, the number
  the mass of the kernel consumes.
-/

@[expose] public section

namespace CenteredMaximal.Fractional

/-- The common denominator `5 · 10^16` of every coefficient of the certificate. -/
def fracDenNum : ℤ := 50000000000000000

/-- The numerator of the base coefficient `a = 45006666551170177/25000000000000000`, i.e.
`a = fracBaseNum / fracDenNum ≈ 1.800266662047`. -/
def fracBaseNum : ℤ := 90013333102340354

/-- The `169` orbit representatives `(i, j, n)` of the spline part of the certificate, with
`i ≥ j ≥ 0` and coefficient `n / fracDenNum`. Transcribed verbatim from
`research/angular-spline-certificate-alpha6over5-N16.json`. -/
def fracOrbits : List (ℤ × ℤ × ℤ) :=
  [    (0, 0, -2547046210462529440), (1, 0, -7269607403482599), (1, 1, -852027380560821836),
    (2, 0, -146423983353359768), (2, 1, -238341931072081130), (2, 2, -398877749152174698),
    (3, 0, -83216193392406480), (3, 1, -133157503859616712), (3, 2, -154801472880179881),
    (3, 3, -226318102624696929), (4, 0, -55046509250335078), (4, 1, -73466128470012432),
    (4, 2, -85582297928151661), (4, 3, -91689026223339503), (4, 4, -105152808017640845),
    (5, 0, -33599129797494471), (5, 1, -42356335508015487), (5, 2, -47040203511214753),
    (5, 3, -46719592668118146), (5, 4, -39624806030486152), (5, 5, -22752468245135531),
    (6, 0, -19911720807664882), (6, 1, -24469317597751215), (6, 2, -26294739978666747),
    (6, 3, -24632408120644338), (6, 4, -18892141168997929), (6, 5, -9861276007763663),
    (6, 6, -2934522718407686), (7, 0, -11087006669019365), (7, 1, -13600219522564108),
    (7, 2, -14184558074915116), (7, 3, -12482890606828831), (7, 4, -8337674814168567),
    (7, 5, -2825448469356709), (7, 6, 1431384897663294), (7, 7, 4086986413855695),
    (8, 0, -5298673751507836), (8, 1, -6712558180555115), (8, 2, -6753344824668652),
    (8, 3, -5241976745317179), (8, 4, -2253701614952172), (8, 5, 1358929995081505),
    (8, 6, 4067708522862887), (8, 7, 5665773305234903), (8, 8, 6255196688637729),
    (9, 0, -1441989018365420), (9, 1, -2271051795395257), (9, 2, -2051507809712585),
    (9, 3, -789105611275177), (9, 4, 1404885672389927), (9, 5, 3840363750766151),
    (9, 6, 5523581598146192), (9, 7, 6278491335555915), (9, 8, 6133386821947322),
    (9, 9, 4863514485990769), (10, 0, 1116169260773126), (10, 1, 646333045121008),
    (10, 2, 954954988526385), (10, 3, 2000377446624011), (10, 4, 3600907651040819),
    (10, 5, 5238330927249784), (10, 6, 6187515640402726), (10, 7, 6247906921783555),
    (10, 8, 5284433467373837), (10, 9, 2437558428614120), (10, 10, -7757073023369817),
    (11, 0, 2900107999508412), (11, 1, 2620466050413911), (11, 2, 2972521698372793),
    (11, 3, 3822116459800625), (11, 4, 5022169906962355), (11, 5, 6128118368875419),
    (11, 6, 6602620134942888), (11, 7, 6290857471984225), (11, 8, 4991535465076062),
    (11, 9, 2127363699344492), (11, 10, -4368596924241466), (11, 11, -26993563417783235),
    (12, 0, 4231234831742597), (12, 1, 4087239159486644), (12, 2, 4439287658441468),
    (12, 3, 5160365827874726), (12, 4, 6083722288065625), (12, 5, 6872513517164435),
    (12, 6, 7119374011411928), (12, 7, 6711191174646336), (12, 8, 5577767708063880),
    (12, 9, 3431673210425166), (12, 10, -304611302413929), (12, 11, -4619360660360334),
    (12, 12, -13716877815936022), (13, 0, 5166910636688514), (13, 1, 5100076288057212),
    (13, 2, 5442197892756912), (13, 3, 6048415469906838), (13, 4, 6772380390275647),
    (13, 5, 7336854162149806), (13, 6, 7430219131020140), (13, 7, 6996919347310312),
    (13, 8, 5998498707429256), (13, 9, 4403348426855553), (13, 10, 1921723263795916),
    (13, 11, -1238596865049229), (14, 0, 5732174930318074), (14, 1, 5713879883210002),
    (14, 2, 6024984310817283), (14, 3, 6523668726553867), (14, 4, 7070556246734806),
    (14, 5, 7437916152474052), (14, 6, 7381379730414186), (14, 7, 6841173595847787),
    (14, 8, 5870550988235339), (14, 9, 4269772597044829), (14, 10, 2634890930980231),
    (15, 0, 6000185554211520), (15, 1, 6001238864009690), (15, 2, 6269940654410902),
    (15, 3, 6656327157187379), (15, 4, 7033822043909045), (15, 5, 7204360412155669),
    (15, 6, 6952705730163200), (15, 7, 6266353579481163), (15, 8, 5002395687165562),
    (15, 9, 3550392912654266), (16, 0, 6033950757754626), (16, 1, 6031049937499545),
    (16, 2, 6248793174569652), (16, 3, 6515047216576577), (16, 4, 6717956906577182),
    (16, 5, 6668295206445355), (16, 6, 6192824228321472), (16, 7, 5133189768902146),
    (16, 8, 3745496934236645), (17, 0, 5862256666995232), (17, 1, 5870026679880006),
    (17, 2, 6013148190015974), (17, 3, 6150615265490290), (17, 4, 6153748612322423),
    (17, 5, 5860215144102046), (17, 6, 4968485848034793), (17, 7, 3749177159993251),
    (18, 0, 5548706166386131), (18, 1, 5538605250060043), (18, 2, 5602843684950785),
    (18, 3, 5581092661130644), (18, 4, 5365936940952798), (18, 5, 4684972409981934),
    (18, 6, 3600874501138831), (19, 0, 5101858448264928), (19, 1, 5074530331268622),
    (19, 2, 5028677399764697), (19, 3, 4832868226870369), (19, 4, 4257556470385953),
    (19, 5, 3329566868929532), (20, 0, 4563802742073561), (20, 1, 4478213910964913),
    (20, 2, 4318976089765659), (20, 3, 3807156487714993), (20, 4, 3012965518409952),
    (21, 0, 3884329285540872), (21, 1, 3801471448554745), (21, 2, 3355819433676934),
    (21, 3, 2713498918713954), (22, 0, 3230126643598869), (22, 1, 2888986590196245),
    (22, 2, 2438455111588335), (23, 0, 2180477021162272), (23, 1, 2179316983395314),
    (24, 0, 1940294168996596)]

/-- The orbit of an index pair under the eight symmetries of the diamond: the two independent sign
flips and the swap. Duplicates are removed, so the orbit of `(0, 0)` is a single cell, that of
`(i, 0)` or `(i, i)` with `i ≠ 0` has four cells, and a general orbit has eight. -/
def diamondOrbit (i j : ℤ) : List (ℤ × ℤ) :=
  [(i, j), (-i, j), (i, -j), (-i, -j), (j, i), (-j, i), (j, -i), (-j, -i)].dedup

/-- The `1201` cells of the certificate, each paired with the numerator of its coefficient. -/
def fracCells : List ((ℤ × ℤ) × ℤ) :=
  fracOrbits.flatMap fun o => (diamondOrbit o.1 o.2.1).map fun p => (p, o.2.2)

/-- The numerator of `∑ C`, the total spline coefficient mass. -/
def fracCellSumNum : ℤ := (fracCells.map fun p => p.2).sum

theorem fracCellSumNum_def : fracCellSumNum = (fracCells.map fun p => p.2).sum := rfl

/-- There are `169` orbits. -/
theorem fracOrbits_length : fracOrbits.length = 169 := by rfl

set_option maxRecDepth 20000 in
/-- **The `169` orbits expand to exactly `1201` cells.** -/
theorem fracCells_length : fracCells.length = 1201 := by rfl

set_option maxRecDepth 20000 in
/-- **The exact total spline coefficient mass**, `∑ C = −15451820578328440516 / (5 · 10^16)`,
which is `−309.0364115666…`. -/
theorem fracCellSumNum_eq : fracCellSumNum = -15451820578328440516 := by rfl

end CenteredMaximal.Fractional

end
