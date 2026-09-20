/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import CenteredMaximal.Fractional.MajorBase

/-!
# The spline part of the kernel on one cell

On the closed first quadrant only the `374` cells of the certificate with `i ≥ -1` and `j ≥ -1` can
contribute, because `β (16 z₀ - i)` already vanishes once `i ≤ -2` and `z₀ ≥ 0`.  And on a single
unit cell `16 z₀ ∈ [k, k+1]`, `16 z₁ ∈ [l, l+1]` only the `16` of those with
`k - 1 ≤ i ≤ k + 2` and `l - 1 ≤ j ≤ l + 2` contribute, each as an explicit bicubic.  This file
performs both reductions and packages the result as a `Poly3` in the two cell coordinates.

## Main results

* `majCellData`: the `374` cells with `i ≥ -1` and `j ≥ -1`, listed **verbatim in the order
  `fracCells` produces them**, and `majCells_eq`, which checks that against `fracCells.filter` by
  one kernel reduction.  Working from a literal, rather than from the filter itself, keeps the
  `790` per-triangle folds down to `374` steps each.
* `cellMono`: the bicubic of the spline part on the cell `(k, l)`, in the two local coordinates
  `s = 16 z₀ - k`, `t = 16 z₁ - l`, as a `Poly3` whose `λ₀`-exponent is `0` — so it is read by
  `eval3 · 1 s t`.  The guard inside `cellTermG` skips a cell in four integer comparisons, which is
  what makes the fold affordable.
* `splineSum_eq_eval3`: **the cell identity.**  For `k, l ≥ 0` and `0 ≤ s, t ≤ 1`,
  `splineSum (k + s) (l + t) = eval3 (cellMono k l) 1 s t`.

## Why a structure

The `374` rows are anonymous constructors of `MajCell`, never bare numeral triples: with tuples
every numeral's `OfNat` problem is postponed and the elaborator's queue grows quadratically.  The
first draft of this file used triples and did not elaborate inside `200000` heartbeats; as a
structure it elaborates in under a second.
-/

@[expose] public section

noncomputable section

namespace CenteredMaximal.Fractional

/-! ### The cells that can contribute on the first quadrant -/

/-- One row of the reduced cell list: the two indices and the coefficient numerator. -/
structure MajCell where
  /-- The first index. -/
  i : ℤ
  /-- The second index. -/
  j : ℤ
  /-- The numerator of the coefficient over `5 · 10^16`. -/
  n : ℤ

/-- A row as the `fracCells` entry it stands for. -/
def MajCell.toPair (c : MajCell) : (ℤ × ℤ) × ℤ := ((c.i, c.j), c.n)

/-- The `374` cells of the certificate with `i ≥ -1` and `j ≥ -1`, in the order `fracCells`
produces them.  Transcribed from the expansion of `fracOrbits`. -/
def majCellData : List MajCell :=
  [⟨0, 0, -2547046210462529440⟩, ⟨1, 0, -7269607403482599⟩, ⟨-1, 0, -7269607403482599⟩,
   ⟨0, 1, -7269607403482599⟩, ⟨0, -1, -7269607403482599⟩, ⟨1, 1, -852027380560821836⟩,
   ⟨-1, 1, -852027380560821836⟩, ⟨1, -1, -852027380560821836⟩, ⟨-1, -1, -852027380560821836⟩,
   ⟨2, 0, -146423983353359768⟩, ⟨0, 2, -146423983353359768⟩, ⟨2, 1, -238341931072081130⟩,
   ⟨2, -1, -238341931072081130⟩, ⟨1, 2, -238341931072081130⟩, ⟨-1, 2, -238341931072081130⟩,
   ⟨2, 2, -398877749152174698⟩, ⟨3, 0, -83216193392406480⟩, ⟨0, 3, -83216193392406480⟩,
   ⟨3, 1, -133157503859616712⟩, ⟨3, -1, -133157503859616712⟩, ⟨1, 3, -133157503859616712⟩,
   ⟨-1, 3, -133157503859616712⟩, ⟨3, 2, -154801472880179881⟩, ⟨2, 3, -154801472880179881⟩,
   ⟨3, 3, -226318102624696929⟩, ⟨4, 0, -55046509250335078⟩, ⟨0, 4, -55046509250335078⟩,
   ⟨4, 1, -73466128470012432⟩, ⟨4, -1, -73466128470012432⟩, ⟨1, 4, -73466128470012432⟩,
   ⟨-1, 4, -73466128470012432⟩, ⟨4, 2, -85582297928151661⟩, ⟨2, 4, -85582297928151661⟩,
   ⟨4, 3, -91689026223339503⟩, ⟨3, 4, -91689026223339503⟩, ⟨4, 4, -105152808017640845⟩,
   ⟨5, 0, -33599129797494471⟩, ⟨0, 5, -33599129797494471⟩, ⟨5, 1, -42356335508015487⟩,
   ⟨5, -1, -42356335508015487⟩, ⟨1, 5, -42356335508015487⟩, ⟨-1, 5, -42356335508015487⟩,
   ⟨5, 2, -47040203511214753⟩, ⟨2, 5, -47040203511214753⟩, ⟨5, 3, -46719592668118146⟩,
   ⟨3, 5, -46719592668118146⟩, ⟨5, 4, -39624806030486152⟩, ⟨4, 5, -39624806030486152⟩,
   ⟨5, 5, -22752468245135531⟩, ⟨6, 0, -19911720807664882⟩, ⟨0, 6, -19911720807664882⟩,
   ⟨6, 1, -24469317597751215⟩, ⟨6, -1, -24469317597751215⟩, ⟨1, 6, -24469317597751215⟩,
   ⟨-1, 6, -24469317597751215⟩, ⟨6, 2, -26294739978666747⟩, ⟨2, 6, -26294739978666747⟩,
   ⟨6, 3, -24632408120644338⟩, ⟨3, 6, -24632408120644338⟩, ⟨6, 4, -18892141168997929⟩,
   ⟨4, 6, -18892141168997929⟩, ⟨6, 5, -9861276007763663⟩, ⟨5, 6, -9861276007763663⟩,
   ⟨6, 6, -2934522718407686⟩, ⟨7, 0, -11087006669019365⟩, ⟨0, 7, -11087006669019365⟩,
   ⟨7, 1, -13600219522564108⟩, ⟨7, -1, -13600219522564108⟩, ⟨1, 7, -13600219522564108⟩,
   ⟨-1, 7, -13600219522564108⟩, ⟨7, 2, -14184558074915116⟩, ⟨2, 7, -14184558074915116⟩,
   ⟨7, 3, -12482890606828831⟩, ⟨3, 7, -12482890606828831⟩, ⟨7, 4, -8337674814168567⟩,
   ⟨4, 7, -8337674814168567⟩, ⟨7, 5, -2825448469356709⟩, ⟨5, 7, -2825448469356709⟩,
   ⟨7, 6, 1431384897663294⟩, ⟨6, 7, 1431384897663294⟩, ⟨7, 7, 4086986413855695⟩,
   ⟨8, 0, -5298673751507836⟩, ⟨0, 8, -5298673751507836⟩, ⟨8, 1, -6712558180555115⟩,
   ⟨8, -1, -6712558180555115⟩, ⟨1, 8, -6712558180555115⟩, ⟨-1, 8, -6712558180555115⟩,
   ⟨8, 2, -6753344824668652⟩, ⟨2, 8, -6753344824668652⟩, ⟨8, 3, -5241976745317179⟩,
   ⟨3, 8, -5241976745317179⟩, ⟨8, 4, -2253701614952172⟩, ⟨4, 8, -2253701614952172⟩,
   ⟨8, 5, 1358929995081505⟩, ⟨5, 8, 1358929995081505⟩, ⟨8, 6, 4067708522862887⟩,
   ⟨6, 8, 4067708522862887⟩, ⟨8, 7, 5665773305234903⟩, ⟨7, 8, 5665773305234903⟩,
   ⟨8, 8, 6255196688637729⟩, ⟨9, 0, -1441989018365420⟩, ⟨0, 9, -1441989018365420⟩,
   ⟨9, 1, -2271051795395257⟩, ⟨9, -1, -2271051795395257⟩, ⟨1, 9, -2271051795395257⟩,
   ⟨-1, 9, -2271051795395257⟩, ⟨9, 2, -2051507809712585⟩, ⟨2, 9, -2051507809712585⟩,
   ⟨9, 3, -789105611275177⟩, ⟨3, 9, -789105611275177⟩, ⟨9, 4, 1404885672389927⟩,
   ⟨4, 9, 1404885672389927⟩, ⟨9, 5, 3840363750766151⟩, ⟨5, 9, 3840363750766151⟩,
   ⟨9, 6, 5523581598146192⟩, ⟨6, 9, 5523581598146192⟩, ⟨9, 7, 6278491335555915⟩,
   ⟨7, 9, 6278491335555915⟩, ⟨9, 8, 6133386821947322⟩, ⟨8, 9, 6133386821947322⟩,
   ⟨9, 9, 4863514485990769⟩, ⟨10, 0, 1116169260773126⟩, ⟨0, 10, 1116169260773126⟩,
   ⟨10, 1, 646333045121008⟩, ⟨10, -1, 646333045121008⟩, ⟨1, 10, 646333045121008⟩,
   ⟨-1, 10, 646333045121008⟩, ⟨10, 2, 954954988526385⟩, ⟨2, 10, 954954988526385⟩,
   ⟨10, 3, 2000377446624011⟩, ⟨3, 10, 2000377446624011⟩, ⟨10, 4, 3600907651040819⟩,
   ⟨4, 10, 3600907651040819⟩, ⟨10, 5, 5238330927249784⟩, ⟨5, 10, 5238330927249784⟩,
   ⟨10, 6, 6187515640402726⟩, ⟨6, 10, 6187515640402726⟩, ⟨10, 7, 6247906921783555⟩,
   ⟨7, 10, 6247906921783555⟩, ⟨10, 8, 5284433467373837⟩, ⟨8, 10, 5284433467373837⟩,
   ⟨10, 9, 2437558428614120⟩, ⟨9, 10, 2437558428614120⟩, ⟨10, 10, -7757073023369817⟩,
   ⟨11, 0, 2900107999508412⟩, ⟨0, 11, 2900107999508412⟩, ⟨11, 1, 2620466050413911⟩,
   ⟨11, -1, 2620466050413911⟩, ⟨1, 11, 2620466050413911⟩, ⟨-1, 11, 2620466050413911⟩,
   ⟨11, 2, 2972521698372793⟩, ⟨2, 11, 2972521698372793⟩, ⟨11, 3, 3822116459800625⟩,
   ⟨3, 11, 3822116459800625⟩, ⟨11, 4, 5022169906962355⟩, ⟨4, 11, 5022169906962355⟩,
   ⟨11, 5, 6128118368875419⟩, ⟨5, 11, 6128118368875419⟩, ⟨11, 6, 6602620134942888⟩,
   ⟨6, 11, 6602620134942888⟩, ⟨11, 7, 6290857471984225⟩, ⟨7, 11, 6290857471984225⟩,
   ⟨11, 8, 4991535465076062⟩, ⟨8, 11, 4991535465076062⟩, ⟨11, 9, 2127363699344492⟩,
   ⟨9, 11, 2127363699344492⟩, ⟨11, 10, -4368596924241466⟩, ⟨10, 11, -4368596924241466⟩,
   ⟨11, 11, -26993563417783235⟩, ⟨12, 0, 4231234831742597⟩, ⟨0, 12, 4231234831742597⟩,
   ⟨12, 1, 4087239159486644⟩, ⟨12, -1, 4087239159486644⟩, ⟨1, 12, 4087239159486644⟩,
   ⟨-1, 12, 4087239159486644⟩, ⟨12, 2, 4439287658441468⟩, ⟨2, 12, 4439287658441468⟩,
   ⟨12, 3, 5160365827874726⟩, ⟨3, 12, 5160365827874726⟩, ⟨12, 4, 6083722288065625⟩,
   ⟨4, 12, 6083722288065625⟩, ⟨12, 5, 6872513517164435⟩, ⟨5, 12, 6872513517164435⟩,
   ⟨12, 6, 7119374011411928⟩, ⟨6, 12, 7119374011411928⟩, ⟨12, 7, 6711191174646336⟩,
   ⟨7, 12, 6711191174646336⟩, ⟨12, 8, 5577767708063880⟩, ⟨8, 12, 5577767708063880⟩,
   ⟨12, 9, 3431673210425166⟩, ⟨9, 12, 3431673210425166⟩, ⟨12, 10, -304611302413929⟩,
   ⟨10, 12, -304611302413929⟩, ⟨12, 11, -4619360660360334⟩, ⟨11, 12, -4619360660360334⟩,
   ⟨12, 12, -13716877815936022⟩, ⟨13, 0, 5166910636688514⟩, ⟨0, 13, 5166910636688514⟩,
   ⟨13, 1, 5100076288057212⟩, ⟨13, -1, 5100076288057212⟩, ⟨1, 13, 5100076288057212⟩,
   ⟨-1, 13, 5100076288057212⟩, ⟨13, 2, 5442197892756912⟩, ⟨2, 13, 5442197892756912⟩,
   ⟨13, 3, 6048415469906838⟩, ⟨3, 13, 6048415469906838⟩, ⟨13, 4, 6772380390275647⟩,
   ⟨4, 13, 6772380390275647⟩, ⟨13, 5, 7336854162149806⟩, ⟨5, 13, 7336854162149806⟩,
   ⟨13, 6, 7430219131020140⟩, ⟨6, 13, 7430219131020140⟩, ⟨13, 7, 6996919347310312⟩,
   ⟨7, 13, 6996919347310312⟩, ⟨13, 8, 5998498707429256⟩, ⟨8, 13, 5998498707429256⟩,
   ⟨13, 9, 4403348426855553⟩, ⟨9, 13, 4403348426855553⟩, ⟨13, 10, 1921723263795916⟩,
   ⟨10, 13, 1921723263795916⟩, ⟨13, 11, -1238596865049229⟩, ⟨11, 13, -1238596865049229⟩,
   ⟨14, 0, 5732174930318074⟩, ⟨0, 14, 5732174930318074⟩, ⟨14, 1, 5713879883210002⟩,
   ⟨14, -1, 5713879883210002⟩, ⟨1, 14, 5713879883210002⟩, ⟨-1, 14, 5713879883210002⟩,
   ⟨14, 2, 6024984310817283⟩, ⟨2, 14, 6024984310817283⟩, ⟨14, 3, 6523668726553867⟩,
   ⟨3, 14, 6523668726553867⟩, ⟨14, 4, 7070556246734806⟩, ⟨4, 14, 7070556246734806⟩,
   ⟨14, 5, 7437916152474052⟩, ⟨5, 14, 7437916152474052⟩, ⟨14, 6, 7381379730414186⟩,
   ⟨6, 14, 7381379730414186⟩, ⟨14, 7, 6841173595847787⟩, ⟨7, 14, 6841173595847787⟩,
   ⟨14, 8, 5870550988235339⟩, ⟨8, 14, 5870550988235339⟩, ⟨14, 9, 4269772597044829⟩,
   ⟨9, 14, 4269772597044829⟩, ⟨14, 10, 2634890930980231⟩, ⟨10, 14, 2634890930980231⟩,
   ⟨15, 0, 6000185554211520⟩, ⟨0, 15, 6000185554211520⟩, ⟨15, 1, 6001238864009690⟩,
   ⟨15, -1, 6001238864009690⟩, ⟨1, 15, 6001238864009690⟩, ⟨-1, 15, 6001238864009690⟩,
   ⟨15, 2, 6269940654410902⟩, ⟨2, 15, 6269940654410902⟩, ⟨15, 3, 6656327157187379⟩,
   ⟨3, 15, 6656327157187379⟩, ⟨15, 4, 7033822043909045⟩, ⟨4, 15, 7033822043909045⟩,
   ⟨15, 5, 7204360412155669⟩, ⟨5, 15, 7204360412155669⟩, ⟨15, 6, 6952705730163200⟩,
   ⟨6, 15, 6952705730163200⟩, ⟨15, 7, 6266353579481163⟩, ⟨7, 15, 6266353579481163⟩,
   ⟨15, 8, 5002395687165562⟩, ⟨8, 15, 5002395687165562⟩, ⟨15, 9, 3550392912654266⟩,
   ⟨9, 15, 3550392912654266⟩, ⟨16, 0, 6033950757754626⟩, ⟨0, 16, 6033950757754626⟩,
   ⟨16, 1, 6031049937499545⟩, ⟨16, -1, 6031049937499545⟩, ⟨1, 16, 6031049937499545⟩,
   ⟨-1, 16, 6031049937499545⟩, ⟨16, 2, 6248793174569652⟩, ⟨2, 16, 6248793174569652⟩,
   ⟨16, 3, 6515047216576577⟩, ⟨3, 16, 6515047216576577⟩, ⟨16, 4, 6717956906577182⟩,
   ⟨4, 16, 6717956906577182⟩, ⟨16, 5, 6668295206445355⟩, ⟨5, 16, 6668295206445355⟩,
   ⟨16, 6, 6192824228321472⟩, ⟨6, 16, 6192824228321472⟩, ⟨16, 7, 5133189768902146⟩,
   ⟨7, 16, 5133189768902146⟩, ⟨16, 8, 3745496934236645⟩, ⟨8, 16, 3745496934236645⟩,
   ⟨17, 0, 5862256666995232⟩, ⟨0, 17, 5862256666995232⟩, ⟨17, 1, 5870026679880006⟩,
   ⟨17, -1, 5870026679880006⟩, ⟨1, 17, 5870026679880006⟩, ⟨-1, 17, 5870026679880006⟩,
   ⟨17, 2, 6013148190015974⟩, ⟨2, 17, 6013148190015974⟩, ⟨17, 3, 6150615265490290⟩,
   ⟨3, 17, 6150615265490290⟩, ⟨17, 4, 6153748612322423⟩, ⟨4, 17, 6153748612322423⟩,
   ⟨17, 5, 5860215144102046⟩, ⟨5, 17, 5860215144102046⟩, ⟨17, 6, 4968485848034793⟩,
   ⟨6, 17, 4968485848034793⟩, ⟨17, 7, 3749177159993251⟩, ⟨7, 17, 3749177159993251⟩,
   ⟨18, 0, 5548706166386131⟩, ⟨0, 18, 5548706166386131⟩, ⟨18, 1, 5538605250060043⟩,
   ⟨18, -1, 5538605250060043⟩, ⟨1, 18, 5538605250060043⟩, ⟨-1, 18, 5538605250060043⟩,
   ⟨18, 2, 5602843684950785⟩, ⟨2, 18, 5602843684950785⟩, ⟨18, 3, 5581092661130644⟩,
   ⟨3, 18, 5581092661130644⟩, ⟨18, 4, 5365936940952798⟩, ⟨4, 18, 5365936940952798⟩,
   ⟨18, 5, 4684972409981934⟩, ⟨5, 18, 4684972409981934⟩, ⟨18, 6, 3600874501138831⟩,
   ⟨6, 18, 3600874501138831⟩, ⟨19, 0, 5101858448264928⟩, ⟨0, 19, 5101858448264928⟩,
   ⟨19, 1, 5074530331268622⟩, ⟨19, -1, 5074530331268622⟩, ⟨1, 19, 5074530331268622⟩,
   ⟨-1, 19, 5074530331268622⟩, ⟨19, 2, 5028677399764697⟩, ⟨2, 19, 5028677399764697⟩,
   ⟨19, 3, 4832868226870369⟩, ⟨3, 19, 4832868226870369⟩, ⟨19, 4, 4257556470385953⟩,
   ⟨4, 19, 4257556470385953⟩, ⟨19, 5, 3329566868929532⟩, ⟨5, 19, 3329566868929532⟩,
   ⟨20, 0, 4563802742073561⟩, ⟨0, 20, 4563802742073561⟩, ⟨20, 1, 4478213910964913⟩,
   ⟨20, -1, 4478213910964913⟩, ⟨1, 20, 4478213910964913⟩, ⟨-1, 20, 4478213910964913⟩,
   ⟨20, 2, 4318976089765659⟩, ⟨2, 20, 4318976089765659⟩, ⟨20, 3, 3807156487714993⟩,
   ⟨3, 20, 3807156487714993⟩, ⟨20, 4, 3012965518409952⟩, ⟨4, 20, 3012965518409952⟩,
   ⟨21, 0, 3884329285540872⟩, ⟨0, 21, 3884329285540872⟩, ⟨21, 1, 3801471448554745⟩,
   ⟨21, -1, 3801471448554745⟩, ⟨1, 21, 3801471448554745⟩, ⟨-1, 21, 3801471448554745⟩,
   ⟨21, 2, 3355819433676934⟩, ⟨2, 21, 3355819433676934⟩, ⟨21, 3, 2713498918713954⟩,
   ⟨3, 21, 2713498918713954⟩, ⟨22, 0, 3230126643598869⟩, ⟨0, 22, 3230126643598869⟩,
   ⟨22, 1, 2888986590196245⟩, ⟨22, -1, 2888986590196245⟩, ⟨1, 22, 2888986590196245⟩,
   ⟨-1, 22, 2888986590196245⟩, ⟨22, 2, 2438455111588335⟩, ⟨2, 22, 2438455111588335⟩,
   ⟨23, 0, 2180477021162272⟩, ⟨0, 23, 2180477021162272⟩, ⟨23, 1, 2179316983395314⟩,
   ⟨23, -1, 2179316983395314⟩, ⟨1, 23, 2179316983395314⟩, ⟨-1, 23, 2179316983395314⟩,
   ⟨24, 0, 1940294168996596⟩, ⟨0, 24, 1940294168996596⟩]

/-- **The literal really is the relevant sublist of `fracCells`.** -/
theorem majCells_eq :
    (fracCells.filter fun p => decide (-1 ≤ p.1.1) && decide (-1 ≤ p.1.2))
      = majCellData.map MajCell.toPair := by
  decide +kernel

/-! ### Dropping the terms that vanish -/

/-- If a term vanishes wherever the filter rejects it, the filtered sum is the whole sum. -/
theorem sum_map_eq_sum_map_filter {α : Type*} {f : α → ℝ} {p : α → Bool} :
    ∀ {l : List α}, (∀ a ∈ l, p a = false → f a = 0) →
      (l.map f).sum = ((l.filter p).map f).sum := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a t ih =>
      intro h
      have ht : ∀ b ∈ t, p b = false → f b = 0 := fun b hb => h b (List.mem_cons_of_mem a hb)
      by_cases hpa : p a = true
      · rw [List.map_cons, List.sum_cons, List.filter_cons_of_pos hpa, List.map_cons,
          List.sum_cons, ih ht]
      · rw [Bool.not_eq_true] at hpa
        rw [List.map_cons, List.sum_cons, List.filter_cons_of_neg (by simp [hpa]), ih ht,
          h a (List.mem_cons_self ..) hpa, zero_add]

/-! ### The bicubic of one cell -/

/-- The certificate coefficient of a cell, as a rational. -/
def fracCoeffQ (n : ℤ) : ℚ := (n : ℚ) / 50000000000000000

theorem fracCoeffQ_cast (n : ℤ) : ((fracCoeffQ n : ℚ) : ℝ) = fracCoeff n := by
  rw [fracCoeffQ, fracCoeff_eq]
  push_cast
  ring

/-- The `16` monomials `sⁱ tʲ` of one cell's contribution, with coefficient `c` and the two local
offsets `d` and `e`. -/
def cellTerm (c : ℚ) (d e : ℤ) : Poly3 :=
  [((0, 0, 0), c * betaCoef d 0 * betaCoef e 0), ((0, 0, 1), c * betaCoef d 0 * betaCoef e 1),
   ((0, 0, 2), c * betaCoef d 0 * betaCoef e 2), ((0, 0, 3), c * betaCoef d 0 * betaCoef e 3),
   ((0, 1, 0), c * betaCoef d 1 * betaCoef e 0), ((0, 1, 1), c * betaCoef d 1 * betaCoef e 1),
   ((0, 1, 2), c * betaCoef d 1 * betaCoef e 2), ((0, 1, 3), c * betaCoef d 1 * betaCoef e 3),
   ((0, 2, 0), c * betaCoef d 2 * betaCoef e 0), ((0, 2, 1), c * betaCoef d 2 * betaCoef e 1),
   ((0, 2, 2), c * betaCoef d 2 * betaCoef e 2), ((0, 2, 3), c * betaCoef d 2 * betaCoef e 3),
   ((0, 3, 0), c * betaCoef d 3 * betaCoef e 0), ((0, 3, 1), c * betaCoef d 3 * betaCoef e 1),
   ((0, 3, 2), c * betaCoef d 3 * betaCoef e 2), ((0, 3, 3), c * betaCoef d 3 * betaCoef e 3)]

theorem eval3_cellTerm (c : ℚ) (d e : ℤ) (s t : ℝ) :
    eval3 (cellTerm c d e) 1 s t = (c : ℝ) * (pieceVal d s * pieceVal e t) := by
  simp only [cellTerm, eval3, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, mono3,
    pieceVal, pow_zero, one_pow, one_mul, mul_one, pow_one]
  push_cast
  ring

/-- One cell's contribution to the bicubic, guarded by the four-integer support test. -/
def cellTermG (k l : ℤ) (c : MajCell) : Poly3 :=
  if decide (-2 ≤ k - c.i) && decide (k - c.i ≤ 1) && decide (-2 ≤ l - c.j)
      && decide (l - c.j ≤ 1) then
    cellTerm (fracCoeffQ c.n) (k - c.i) (l - c.j)
  else []

theorem eval3_cellTermG (k l : ℤ) (c : MajCell) (s t : ℝ) :
    eval3 (cellTermG k l c) 1 s t
      = fracCoeff c.n * (pieceVal (k - c.i) s * pieceVal (l - c.j) t) := by
  rw [cellTermG]
  split
  · rw [eval3_cellTerm, fracCoeffQ_cast]
  · rename_i hg
    have hg' : ¬((-2 ≤ k - c.i ∧ k - c.i ≤ 1) ∧ (-2 ≤ l - c.j ∧ l - c.j ≤ 1)) := by
      simpa [Bool.and_eq_true, and_assoc] using hg
    rw [eval3_nil]
    rcases not_and_or.1 hg' with h | h
    · rcases not_and_or.1 h with h | h
      · rw [pieceVal_of_lt (by omega) s, zero_mul, mul_zero]
      · rw [pieceVal_of_gt (by omega) s, zero_mul, mul_zero]
    · rcases not_and_or.1 h with h | h
      · rw [pieceVal_of_lt (by omega) t, mul_zero, mul_zero]
      · rw [pieceVal_of_gt (by omega) t, mul_zero, mul_zero]

/-- **The bicubic of the spline part on the cell `(k, l)`**, in the local coordinates
`s = 16 z₀ - k` and `t = 16 z₁ - l`. -/
def cellMono (k l : ℤ) : Poly3 := majCellData.foldr (fun c acc => add3 (cellTermG k l c) acc) []

/-- The fold computes the sum of the cell contributions. -/
theorem eval3_cellFold (k l : ℤ) (s t : ℝ) :
    ∀ L : List MajCell,
      eval3 (L.foldr (fun c acc => add3 (cellTermG k l c) acc) []) 1 s t
        = (L.map fun c => fracCoeff c.n
            * (pieceVal (k - c.i) s * pieceVal (l - c.j) t)).sum := by
  intro L
  induction L with
  | nil => simp [eval3]
  | cons c L ih =>
      rw [List.foldr_cons, eval3_add3, ih, eval3_cellTermG, List.map_cons, List.sum_cons]

/-- Each B-spline factor on a cell is the corresponding local cubic piece. -/
theorem bspline_cell (k i : ℤ) {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    bspline ((k : ℝ) + s - (i : ℝ)) = pieceVal (k - i) s := by
  rw [show (k : ℝ) + s - (i : ℝ) = (((k - i : ℤ) : ℝ)) + s from by push_cast; ring]
  exact bspline_intAdd (k - i) hs hs1

/-- **The cell identity.**  On the cell `16 z₀ ∈ [k, k+1]`, `16 z₁ ∈ [l, l+1]` inside the first
quadrant, the spline part of the kernel is the bicubic `cellMono k l` of the two local
coordinates. -/
theorem splineSum_eq_eval3 {k l : ℤ} (hk : 0 ≤ k) (hl : 0 ≤ l) {s t : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    splineSum ((k : ℝ) + s) ((l : ℝ) + t) = eval3 (cellMono k l) 1 s t := by
  have hkR : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlR : (0 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl
  have hzero : ∀ p ∈ fracCells, (decide (-1 ≤ p.1.1) && decide (-1 ≤ p.1.2)) = false →
      fracCoeff p.2 * (bspline ((k : ℝ) + s - p.1.1) * bspline ((l : ℝ) + t - p.1.2)) = 0 := by
    intro p _ hp
    have hp' : ¬(-1 ≤ p.1.1 ∧ -1 ≤ p.1.2) := by simpa [Bool.and_eq_true] using hp
    rcases not_and_or.1 hp' with h | h
    · have h2 : ((p.1.1 : ℤ) : ℝ) ≤ -2 := by exact_mod_cast (by omega : p.1.1 ≤ -2)
      rw [bspline_of_two_le (show (2 : ℝ) ≤ (k : ℝ) + s - p.1.1 from by linarith), zero_mul,
        mul_zero]
    · have h2 : ((p.1.2 : ℤ) : ℝ) ≤ -2 := by exact_mod_cast (by omega : p.1.2 ≤ -2)
      rw [bspline_of_two_le (show (2 : ℝ) ≤ (l : ℝ) + t - p.1.2 from by linarith), mul_zero,
        mul_zero]
  rw [splineSum, sum_map_eq_sum_map_filter hzero, majCells_eq, cellMono,
    eval3_cellFold k l s t, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun c _ => ?_)
  simp only [Function.comp_apply, MajCell.toPair]
  rw [bspline_cell k c.i hs hs1, bspline_cell l c.j ht ht1]

end CenteredMaximal.Fractional

end

end
