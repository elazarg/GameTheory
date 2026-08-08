/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Algebra.Order.Ring.Cone
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Data.Real.Basic

/-!
# `ℝ(t)` ordered by behavior at `0⁺`, with `t` a positive infinitesimal

This file starts the **RCF-transfer** infrastructure for the uniform-equilibrium program: it
equips `RatFunc ℝ` — the field of rational functions `ℝ(t)` — with the linear order induced by
the sign of a rational function's germ as `t → 0⁺`, and shows this makes `RatFunc ℝ` a linearly
ordered field (`LinearOrder` + `IsOrderedRing`, hence `IsStrictOrderedRing` automatically, since
`RatFunc ℝ` is already a `Field`) in which `RatFunc.X` (i.e. `t`) is a *positive infinitesimal*:
`0 < t`, `t` is smaller than every positive real constant, and `t` beats every natural multiple
against `1` (a non-Archimedean witness).

## Why this matters for the uniform-equilibrium program

The eventual goal is a tower converting *vanishing-discount* analysis (statements about
`β ↦ v_β` as `β → 1⁻`, equivalently about germs at `t := 1 - β → 0⁺`) into *first-order algebra*
over a real-closed field extending `ℝ`, via:

1. **This file** — `ℝ(t)` ordered at `0⁺`, `t` infinitesimal (an ordered field, not yet real
   closed).
2. The real closure of `ℝ(t)` (Puiseux series in `t^{1/n}`) — a genuinely real-closed field.
3. Model completeness of the theory of real-closed fields (Tarski) — transfers first-order
   `ℝ`-facts to facts in the real closure of `ℝ(t)`, and hence (via the germ dictionary below)
   to facts about `v_β` for `β` close enough to `1`.
4. A germ dictionary: first-order statements about `t` in the real closure of `ℝ(t)` correspond
   to statements that hold *eventually* as `λ := 1 - β → 0⁺` (Puiseux/Łojasiewicz-type
   germ-to-eventual-behavior correspondence).

None of steps 2–4 are attempted here; see "What remains for the transfer package" at the end of
this file for the precise missing statements and the Mathlib gaps blocking them.

## Mathematical design

For a nonzero polynomial `p : Polynomial ℝ`, the sign of `p` near `0⁺` (i.e. the sign of `p(λ)`
for small `λ > 0`) is the sign of `p.trailingCoeff`, the coefficient of the *lowest*-degree
nonzero term (Mathlib: `Polynomial.trailingCoeff`; multiplicativity `Polynomial.trailingCoeff_mul`
already holds unconditionally for `Polynomial ℝ`, since it is a domain). For `f : RatFunc ℝ`,
using the *canonical* numerator/denominator pair `f.num`, `f.denom` (monic denominator; Mathlib:
`RatFunc.num`, `RatFunc.denom`), we declare

`PosNearZero f ↔ 0 < (f.num * f.denom).trailingCoeff`

(sign of the numerator divided by the sign of the denominator, computed without division by
multiplying by the denominator instead). Because `f.num`/`f.denom` are *functions* of `f` (not
representatives of an equivalence class), this is automatically well-defined; the mathematical
content is instead in showing this predicate is a positivity cone: closed under addition and
multiplication, and satisfies trichotomy. The bridge from an *arbitrary* fraction `p / q`
representing `x + y` (not necessarily the canonical one) to the canonical
`(x + y).num`/`(x + y).denom` uses Mathlib's cross-multiplication identities
(`RatFunc.num_denom_add`, `RatFunc.num_denom_mul`, `RatFunc.num_denom_neg`) together with a
general real-number lemma (`sign_eq_of_mul_sq_eq`) that reads off the common sign from a relation
`a * d = c * b` (`d`, `b` nonzero) by multiplying through by the positive squares `d ^ 2`, `b ^ 2`.

The one genuinely delicate step (flagged in the design brief) is **addition**: the canonical
numerator of `x + y` is (up to the cross-multiplication bridge above) `x.num * y.denom +
x.denom * y.num`, a *sum* of two products, so `Polynomial.trailingCoeff` does not distribute over
it in general — trailing terms of the two summands could cancel if their signs disagreed. We rule
this out by first showing directly that whenever both summands have positive trailing
coefficients, so does the sum (`trailingCoeff_add_pos`, case-split on which trailing degree is
smaller; equal degrees add without cancellation since both are positive, unequal degrees means
the smaller-degree summand's trailing term survives untouched), and then a small computation
(multiplying by the squared cross-denominator) shows the two relevant products always inherit
matching signs from `PosNearZero x` and `PosNearZero y` — so no cancellation ever threatens the
sum that actually arises here.

## Main results

Trailing-coefficient algebra on `Polynomial ℝ` (`Math.InfinitesimalRatFunc` namespace):
* `trailingCoeff_neg` — `(-p).trailingCoeff = -p.trailingCoeff`.
* `sign_eq_of_mul_sq_eq` — general real-number "read off the sign from a cross relation" lemma.
* `trailingCoeff_add_pos` — the addition case-split: positive + positive is positive.
* `posProd_congr` — cross-multiplication invariance of the sign of `(a * b).trailingCoeff`.

The positivity predicate on `RatFunc ℝ` and cone axioms:
* `PosNearZero` — the positivity predicate (germ sign at `0⁺`).
* `posNearZero_add`, `posNearZero_mul`, `posNearZero_neg_iff`, `trichotomy_posNearZero`,
  `not_posNearZero_and_neg` — the positivity-cone axioms.

Order instances (all `scoped` to this namespace — see the diamond-avoidance note below):
* `cone : RingCone (RatFunc ℝ)` and `scoped instance : LinearOrder (RatFunc ℝ)`,
  `scoped instance : IsOrderedRing (RatFunc ℝ)` (which makes `IsStrictOrderedRing (RatFunc ℝ)`
  available automatically, since `RatFunc ℝ` is a domain).

Headline lemmas (`t` is a positive infinitesimal):
* `zero_lt_X` — `0 < RatFunc.X`.
* `X_lt_const` — `∀ r : ℝ, 0 < r → RatFunc.X < RatFunc.C r`.
* `X_infinitesimal` — `∀ n : ℕ, (n : RatFunc ℝ) * RatFunc.X < 1` (non-Archimedean witness).
* `C_lt_C_iff` — `RatFunc.C r < RatFunc.C s ↔ r < s` (`ℝ` embeds order-preservingly via `C`).

## Instance-packaging choices and diamond avoidance

Mathlib does **not** currently equip `RatFunc K` with any order structure, so there is no
existing instance to collide with. Nevertheless, per the design brief, both order instances here
(`LinearOrder (RatFunc ℝ)` and `IsOrderedRing (RatFunc ℝ)`) are declared `scoped` inside the
`Math.InfinitesimalRatFunc` namespace rather than as global instances: anyone consuming this file
must `open scoped Math.InfinitesimalRatFunc` to bring `<`/`≤` on `RatFunc ℝ` into scope. This
keeps the order invisible to unrelated code and leaves room for a different order on `RatFunc K`
(e.g. at a different point, or the order relevant to a different `K`) to be added later without a
clash. The order is built via Mathlib's `RingCone`/`AddGroupCone` positivity-cone framework
(`Mathlib.Algebra.Order.Ring.Cone`) rather than by hand-rolling `LinearOrder` axioms: this is the
modern, blessed route (introduced specifically to replace the old `LinearOrderedField.mk''`
pattern) and it automatically discharges `IsOrderedAddMonoid`/`IsOrderedRing` from the cone
closure lemmas. One genuine diamond hazard was found and worked around: elaborating
`IsOrderedRing.mkOfCone cone` in *term* mode against the ambient `PartialOrder (RatFunc ℝ)`
found via the generic `LinearOrder → Lattice → PartialOrder` derivation chain fails outright
(`Type mismatch`, differing `Semiring`/`PartialOrder` projection paths); wrapping the same term in
`by exact ...` (tactic-mode elaboration, which retries unification more aggressively) resolves it
cleanly, so `IsOrderedRing (RatFunc ℝ)` below is proved with `by exact IsOrderedRing.mkOfCone cone`
rather than a bare term. `IsStrictOrderedRing (RatFunc ℝ)` is *not* declared explicitly: it comes
for free from the library instance `IsOrderedRing.toIsStrictOrderedRing` once `IsOrderedRing`,
`NoZeroDivisors`, and `Nontrivial` are all in scope (the latter two already hold for `RatFunc ℝ`
as a `Field`).

## What remains for the transfer package

This file is only the base of the tower described above. Still missing, all genuinely hard and
none attempted here:

* **Real closure of `ℝ(t)`.** The Puiseux series field `⋃ₙ ℝ((t^{1/n}))` (or, order-
  theoretically, the real closure of the ordered field constructed in this file) is real closed
  by the Newton–Puiseux theorem. Mathlib's `IsRealClosed` (as of this writing) is nascent — no
  general "real closure of an ordered field exists" construction, and no Puiseux series type.
  `Mathlib.RingTheory.HahnSeries` (Hahn series, i.e. formal series with well-ordered support in a
  general ordered abelian group of exponents) is the most promising existing carrier: Puiseux
  series embed as `HahnSeries` valued in `ℚ` (or a suitable subgroup), and `HahnSeries` already
  has a working order (`Mathlib.RingTheory.HahnSeries.Lex`, via the *leading* — not trailing —
  coefficient, since Hahn series expand in decreasing order of significance rather than around a
  point); adapting that machinery to `0⁺`-germs and closing it under `n`-th roots to reach real
  closedness is unstarted.
* **Model completeness of RCF (Tarski–Seidenberg).** No `Mathlib` statement of the transfer
  principle "a first-order sentence with parameters in a real-closed subfield `k` of a real-closed
  field `K` holds in `k` iff it holds in `K`" is available; `Mathlib.ModelTheory` has general
  first-order logic and some algebraic model theory, but not this specific theorem.
* **The germ dictionary.** Even granting the previous two items, one still needs the *analytic*
  correspondence: a first-order statement about the infinitesimal `t` (equivalently, a
  first-order statement true in the real closure of `ℝ(t)`) translates to "the corresponding
  statement about `β`-discounted quantities holds for all `β` sufficiently close to `1⁻`". This is
  a Łojasiewicz/Puiseux-expansion argument specific to the semi-algebraic functions
  `β ↦ v_β` arising from the Shapley/Fink fixed-point equations (see
  `GameTheory/Concepts/Stochastic/ZeroSum/Basic.lean`, `Fink.lean`), and has no
  counterpart in this file at all.
-/

namespace Math
namespace InfinitesimalRatFunc

open Polynomial RatFunc

/-! ## 1. Trailing-coefficient sign lemmas on `Polynomial ℝ`

`Polynomial.trailingCoeff_mul` (multiplicativity of the trailing coefficient) already holds
unconditionally in Mathlib for `Polynomial ℝ` (any `[Semiring R] [NoZeroDivisors R]`), so it is
used directly below without restating it. What Mathlib does *not* provide is the addition
case-split (`trailingCoeff_add_pos`) or the cross-multiplication sign lemma (`posProd_congr`).
-/

/-- The trailing coefficient of `-p` is the negative of that of `p`: negation does not change
which term is trailing, only its sign. -/
theorem trailingCoeff_neg (p : Polynomial ℝ) : (-p).trailingCoeff = -p.trailingCoeff := by
  unfold trailingCoeff
  rw [natTrailingDegree_neg, coeff_neg]

/-- The trailing coefficient of a nonzero constant polynomial is that constant (and this also
holds, trivially, at `a = 0`, since `Polynomial.C 0 = 0` and `trailingCoeff 0 = 0`). -/
theorem trailingCoeff_C (a : ℝ) : (Polynomial.C a).trailingCoeff = a := by
  unfold trailingCoeff
  simp

/-- If two nonzero reals `a`, `b` are related by `a * t ^ 2 = b * s ^ 2` for nonzero `s`, `t`,
they have the same sign. This is the algebraic core of representation-independence: it lets us
compare the sign of a product `(f.num * f.denom).trailingCoeff` computed from two different
(cross-related) fraction representations of the same rational function, without needing to know
the exact magnitudes. -/
theorem sign_eq_of_mul_sq_eq {a b s t : ℝ} (hs : s ≠ 0) (ht : t ≠ 0)
    (h : a * t ^ 2 = b * s ^ 2) : 0 < a ↔ 0 < b := by
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have ht2 : (0 : ℝ) < t ^ 2 := by positivity
  constructor
  · intro ha
    by_contra hb
    have hb' := not_lt.mp hb
    nlinarith
  · intro hb
    by_contra ha
    have ha' := not_lt.mp ha
    nlinarith

/-- Cross-multiplication invariance of the sign of a trailing-coefficient product: if
`a * d = c * b` with `b`, `d` nonzero, then `(a * b).trailingCoeff` and `(c * d).trailingCoeff`
have the same sign. Applied below to Mathlib's `RatFunc.num_denom_add`/`_mul`/`_neg` identities,
this is what lets us transfer positivity facts between an (arbitrary) fraction representation and
the canonical `num`/`denom` pair. -/
theorem posProd_congr {a b c d : Polynomial ℝ} (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d = c * b) :
    0 < (a * b).trailingCoeff ↔ 0 < (c * d).trailingCoeff := by
  have key : a.trailingCoeff * d.trailingCoeff = c.trailingCoeff * b.trailingCoeff := by
    rw [← trailingCoeff_mul, ← trailingCoeff_mul, h]
  apply sign_eq_of_mul_sq_eq (s := b.trailingCoeff) (t := d.trailingCoeff)
  · exact trailingCoeff_eq_zero.not.mpr hb
  · exact trailingCoeff_eq_zero.not.mpr hd
  · rw [trailingCoeff_mul, trailingCoeff_mul]
    calc a.trailingCoeff * b.trailingCoeff * d.trailingCoeff ^ 2
        = a.trailingCoeff * d.trailingCoeff * (b.trailingCoeff * d.trailingCoeff) := by ring
      _ = c.trailingCoeff * b.trailingCoeff * (b.trailingCoeff * d.trailingCoeff) := by rw [key]
      _ = c.trailingCoeff * d.trailingCoeff * b.trailingCoeff ^ 2 := by ring

/-- **The addition case-split lemma.** If `p` and `q` both have positive trailing coefficient,
so does `p + q`. Proof: compare the trailing degrees of `p` and `q`. If they differ, the summand
with the smaller trailing degree survives untouched in `p + q` (its trailing term cannot be
cancelled by the other summand, which vanishes at that degree), so `(p + q).trailingCoeff` equals
that summand's (positive) trailing coefficient. If they agree, the two trailing coefficients
literally add (both positive, so no cancellation), and all lower coefficients of `p + q` still
vanish, so `(p + q).trailingCoeff` is that positive sum. -/
theorem trailingCoeff_add_pos {p q : Polynomial ℝ} (hp : 0 < p.trailingCoeff)
    (hq : 0 < q.trailingCoeff) : 0 < (p + q).trailingCoeff := by
  have hp0 : p ≠ 0 := fun h => by simp [h] at hp
  have hq0 : q ≠ 0 := fun h => by simp [h] at hq
  rcases lt_trichotomy p.natTrailingDegree q.natTrailingDegree with hlt | heq | hgt
  · -- `p`'s trailing term dominates: `q` vanishes there and below.
    have hcoeff : (p + q).coeff p.natTrailingDegree = p.trailingCoeff := by
      rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree hlt, add_zero]
      rfl
    have hlow : ∀ m < p.natTrailingDegree, (p + q).coeff m = 0 := by
      intro m hm
      rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree hm,
        coeff_eq_zero_of_lt_natTrailingDegree (hm.trans hlt), zero_add]
    have hpq0 : p + q ≠ 0 := by
      intro h
      rw [h, coeff_zero] at hcoeff
      exact absurd hcoeff.symm hp.ne'
    have hdeg : (p + q).natTrailingDegree = p.natTrailingDegree :=
      le_antisymm (natTrailingDegree_le_of_ne_zero (hcoeff ▸ hp.ne'))
        (le_natTrailingDegree hpq0 hlow)
    unfold trailingCoeff
    rw [hdeg, hcoeff]
    exact hp
  · -- Equal trailing degree: the trailing coefficients add without cancellation.
    have hcoeff : (p + q).coeff p.natTrailingDegree = p.trailingCoeff + q.trailingCoeff := by
      unfold trailingCoeff
      rw [coeff_add, heq]
    have hlow : ∀ m < p.natTrailingDegree, (p + q).coeff m = 0 := by
      intro m hm
      rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree hm,
        coeff_eq_zero_of_lt_natTrailingDegree (heq ▸ hm), zero_add]
    have hsum_ne : p.trailingCoeff + q.trailingCoeff ≠ 0 := by linarith
    have hpq0 : p + q ≠ 0 := by
      intro h
      rw [h, coeff_zero] at hcoeff
      exact hsum_ne hcoeff.symm
    have hdeg : (p + q).natTrailingDegree = p.natTrailingDegree :=
      le_antisymm (natTrailingDegree_le_of_ne_zero (hcoeff ▸ hsum_ne))
        (le_natTrailingDegree hpq0 hlow)
    unfold trailingCoeff
    rw [hdeg, hcoeff]
    linarith
  · -- `q`'s trailing term dominates: `p` vanishes there and below.
    have hcoeff : (p + q).coeff q.natTrailingDegree = q.trailingCoeff := by
      rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree hgt, zero_add]
      rfl
    have hlow : ∀ m < q.natTrailingDegree, (p + q).coeff m = 0 := by
      intro m hm
      rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree hm,
        coeff_eq_zero_of_lt_natTrailingDegree (hm.trans hgt), add_zero]
    have hpq0 : p + q ≠ 0 := by
      intro h
      rw [h, coeff_zero] at hcoeff
      exact absurd hcoeff.symm hq.ne'
    have hdeg : (p + q).natTrailingDegree = q.natTrailingDegree :=
      le_antisymm (natTrailingDegree_le_of_ne_zero (hcoeff ▸ hq.ne'))
        (le_natTrailingDegree hpq0 hlow)
    unfold trailingCoeff
    rw [hdeg, hcoeff]
    exact hq

/-! ## 2. The positivity predicate on `RatFunc ℝ` and the cone axioms -/

/-- `f` is positive near `0⁺` iff the germ of `f(λ)` as `λ → 0⁺` is (eventually) positive:
concretely, the sign of the trailing coefficient of `f.num * f.denom` — the sign of the numerator
times the sign of the denominator, equivalently the sign of the numerator divided by the sign of
the denominator, computed without division. Since `RatFunc.num`/`RatFunc.denom` are canonical
(functions of `f`, with monic denominator), this is automatically well-defined; no separate
representation-independence lemma is needed for the *definition* — it is only needed (via
`posProd_congr` above) to relate this to non-canonical fraction representations when proving the
cone-closure lemmas below. -/
def PosNearZero (f : RatFunc ℝ) : Prop := 0 < (f.num * f.denom).trailingCoeff

theorem not_posNearZero_zero : ¬ PosNearZero (0 : RatFunc ℝ) := by
  unfold PosNearZero
  simp

theorem posNearZero_ne_zero {x : RatFunc ℝ} (hx : PosNearZero x) : x ≠ 0 :=
  fun heq => not_posNearZero_zero (heq ▸ hx)

/-- Negation flips the sign of the germ: `-x` is positive near `0⁺` iff `x`'s canonical
`num * denom` product has *negative* trailing coefficient. Proved via the cross-multiplication
identity `RatFunc.num_denom_neg`. -/
theorem posNearZero_neg_iff {x : RatFunc ℝ} :
    PosNearZero (-x) ↔ (x.num * x.denom).trailingCoeff < 0 := by
  have h := posProd_congr (a := (-x).num) (b := (-x).denom) (c := -x.num) (d := x.denom)
    (denom_ne_zero (-x)) (denom_ne_zero x) (num_denom_neg x)
  unfold PosNearZero
  rw [h, show (-x.num * x.denom) = -(x.num * x.denom) from by ring, trailingCoeff_neg]
  constructor <;> intro hlt <;> linarith

theorem not_posNearZero_and_neg {x : RatFunc ℝ} (hx : PosNearZero x) : ¬ PosNearZero (-x) := by
  intro hneg
  rw [posNearZero_neg_iff] at hneg
  unfold PosNearZero at hx
  linarith

/-- Trichotomy: every rational function is zero, positive near `0⁺`, or has positive negation
(i.e. is negative near `0⁺`). -/
theorem trichotomy_posNearZero (x : RatFunc ℝ) :
    x = 0 ∨ PosNearZero x ∨ PosNearZero (-x) := by
  by_cases hx : x = 0
  · exact Or.inl hx
  · have hn : (x.num * x.denom).trailingCoeff ≠ 0 := by
      rw [trailingCoeff_mul]
      exact mul_ne_zero (trailingCoeff_eq_zero.not.mpr (num_ne_zero hx))
        (trailingCoeff_eq_zero.not.mpr (denom_ne_zero x))
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · exact Or.inr (Or.inr (posNearZero_neg_iff.mpr hlt))
    · exact Or.inr (Or.inl hgt)

/-- Cone closure under addition: sum of two germ-positive rational functions is germ-positive.
The canonical numerator of `x + y` is cross-related (via `RatFunc.num_denom_add`) to
`x.num * y.denom + x.denom * y.num`, a sum of two products; `trailingCoeff_add_pos` shows each of
those two products, multiplied by the common denominator `x.denom * y.denom`, has positive
trailing coefficient (this is where the squared-cross-denominator computation from
`sign_eq_of_mul_sq_eq`/`posProd_congr` is doing its work — turning the *hypotheses* `PosNearZero
x`, `PosNearZero y` into positivity of the two individual summands actually being added). -/
theorem posNearZero_add {x y : RatFunc ℝ} (hx : PosNearZero x) (hy : PosNearZero y) :
    PosNearZero (x + y) := by
  have hd : x.denom * y.denom ≠ 0 := mul_ne_zero (denom_ne_zero x) (denom_ne_zero y)
  refine (posProd_congr (denom_ne_zero (x + y)) hd (num_denom_add x y)).mpr ?_
  have hexpand : (x.num * y.denom + x.denom * y.num) * (x.denom * y.denom)
      = x.num * y.denom * (x.denom * y.denom) + x.denom * y.num * (x.denom * y.denom) := by ring
  rw [hexpand]
  apply trailingCoeff_add_pos
  · rw [trailingCoeff_mul, trailingCoeff_mul, trailingCoeff_mul]
    unfold PosNearZero at hx
    rw [trailingCoeff_mul] at hx
    have hdy : y.denom.trailingCoeff ≠ 0 := trailingCoeff_eq_zero.not.mpr (denom_ne_zero y)
    nlinarith [sq_pos_of_ne_zero hdy]
  · rw [trailingCoeff_mul, trailingCoeff_mul, trailingCoeff_mul]
    unfold PosNearZero at hy
    rw [trailingCoeff_mul] at hy
    have hdx : x.denom.trailingCoeff ≠ 0 := trailingCoeff_eq_zero.not.mpr (denom_ne_zero x)
    nlinarith [sq_pos_of_ne_zero hdx]

/-- Cone closure under multiplication: product of two germ-positive rational functions is
germ-positive. Simpler than addition — no case-split needed, since `RatFunc.num_denom_mul`
relates the canonical numerator of `x * y` to a *product* `x.num * y.num`, and
`Polynomial.trailingCoeff_mul` is unconditionally multiplicative. -/
theorem posNearZero_mul {x y : RatFunc ℝ} (hx : PosNearZero x) (hy : PosNearZero y) :
    PosNearZero (x * y) := by
  have hd : x.denom * y.denom ≠ 0 := mul_ne_zero (denom_ne_zero x) (denom_ne_zero y)
  refine (posProd_congr (denom_ne_zero (x * y)) hd (num_denom_mul x y)).mpr ?_
  rw [trailingCoeff_mul]
  unfold PosNearZero at hx hy
  rw [trailingCoeff_mul] at hx hy
  rw [trailingCoeff_mul, trailingCoeff_mul]
  nlinarith [hx, hy]

theorem posNearZero_one : PosNearZero (1 : RatFunc ℝ) := by
  unfold PosNearZero
  rw [RatFunc.num_one, RatFunc.denom_one, mul_one]
  unfold trailingCoeff
  simp

/-! ## 3. The order instances

Both instances below are `scoped` — see the "Instance-packaging choices" section of the module
docstring for why, and for the diamond that had to be worked around. -/

/-- The cone of rational functions that are zero or positive near `0⁺`. This packages
`PosNearZero` (together with the closure lemmas above) into the shape Mathlib's
`RingCone`/`AddGroupCone` framework expects, from which the actual order instances are derived
below via `LinearOrder.mkOfAddGroupCone` and `IsOrderedRing.mkOfCone`. -/
noncomputable def cone : RingCone (RatFunc ℝ) where
  carrier := {f | f = 0 ∨ PosNearZero f}
  zero_mem' := Or.inl rfl
  one_mem' := Or.inr posNearZero_one
  add_mem' := by
    rintro a b (rfl | ha) (rfl | hb)
    · exact Or.inl (by simp)
    · simpa using Or.inr hb
    · simpa using Or.inr ha
    · exact Or.inr (posNearZero_add ha hb)
  mul_mem' := by
    rintro a b (rfl | ha) (rfl | hb)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inl (by simp)
    · exact Or.inr (posNearZero_mul ha hb)
  eq_zero_of_mem_of_neg_mem' := by
    rintro a (rfl | ha) (h0 | hneg)
    · rfl
    · rfl
    · exact neg_eq_zero.mp h0
    · exact absurd hneg (not_posNearZero_and_neg ha)

/-- Trichotomy of the cone: every rational function is in `cone` or its negation is (this is
Mathlib's `HasMemOrNegMem`, the hypothesis needed to upgrade the `PartialOrder` from `cone` to a
full `LinearOrder`). -/
instance instHasMemOrNegMem : HasMemOrNegMem cone := by
  refine ⟨fun a => ?_⟩
  rcases trichotomy_posNearZero a with h | h | h
  · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr h)
  · exact Or.inr (Or.inr h)

open Classical in
/-- The `0⁺`-germ linear order on `RatFunc ℝ`. Scoped: `open scoped Math.InfinitesimalRatFunc`
to use `<`/`≤` on `RatFunc ℝ`. -/
noncomputable scoped instance : LinearOrder (RatFunc ℝ) := .mkOfAddGroupCone cone

/-- `RatFunc ℝ` is an ordered ring under the `0⁺`-germ order (elaborated in tactic mode to route
around a `PartialOrder`/`Semiring` diamond between the cone-derived and generically-derived
instances — see the module docstring). Together with `RatFunc ℝ` being a `Field` (hence a domain),
this automatically makes `IsStrictOrderedRing (RatFunc ℝ)` available via the library instance
`IsOrderedRing.toIsStrictOrderedRing`, without any further declaration here. -/
scoped instance : IsOrderedRing (RatFunc ℝ) := by exact IsOrderedRing.mkOfCone cone

theorem le_iff_sub (a b : RatFunc ℝ) : a ≤ b ↔ b - a ∈ cone := Iff.rfl

/-- Bridge lemma: the abstract order `<` on `RatFunc ℝ` unfolds to the concrete `PosNearZero`
predicate on the difference. This is what makes the headline lemmas below provable by direct
`trailingCoeff` computation. -/
theorem lt_iff_posNearZero_sub (a b : RatFunc ℝ) : a < b ↔ PosNearZero (b - a) := by
  rw [lt_iff_le_not_ge, le_iff_sub, le_iff_sub]
  show (b - a ∈ cone) ∧ ¬ (a - b ∈ cone) ↔ PosNearZero (b - a)
  constructor
  · rintro ⟨h1 | h1, h2⟩
    · exact absurd (Or.inl (by rw [show a - b = -(b - a) from by ring, h1]; simp)) h2
    · exact h1
  · intro h
    refine ⟨Or.inr h, ?_⟩
    rintro (h2 | h2)
    · exact posNearZero_ne_zero h (by rw [show b - a = -(a - b) from by ring, h2]; simp)
    · rw [show a - b = -(b - a) from by ring] at h2
      exact not_posNearZero_and_neg h h2

/-! ## 4. Headline lemmas: `RatFunc.X` (i.e. `t`) is a positive infinitesimal -/

/-- `t` is positive. -/
theorem zero_lt_X : (0 : RatFunc ℝ) < RatFunc.X := by
  rw [lt_iff_posNearZero_sub, sub_zero]
  unfold PosNearZero
  rw [RatFunc.num_X, RatFunc.denom_X, mul_one]
  unfold trailingCoeff
  simp

/-- `t` is smaller than every positive real constant: `t` is infinitesimal. -/
theorem X_lt_const (r : ℝ) (hr : 0 < r) : RatFunc.X < RatFunc.C r := by
  rw [lt_iff_posNearZero_sub]
  have heq : RatFunc.C r - RatFunc.X
      = algebraMap (Polynomial ℝ) (RatFunc ℝ) (Polynomial.C r - Polynomial.X) := by
    rw [map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  unfold PosNearZero
  rw [heq, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, mul_one]
  rw [trailingCoeff_eq_coeff_zero (by simpa using hr.ne')]
  simpa using hr

/-- `t` beats every natural multiple against `1`: a non-Archimedean witness (no natural number of
copies of `t` reaches `1`). -/
theorem X_infinitesimal (n : ℕ) : (n : RatFunc ℝ) * RatFunc.X < 1 := by
  rw [lt_iff_posNearZero_sub]
  have heq : (1 : RatFunc ℝ) - (n : RatFunc ℝ) * RatFunc.X
      = algebraMap (Polynomial ℝ) (RatFunc ℝ) (1 - (n : Polynomial ℝ) * Polynomial.X) := by
    rw [map_sub, map_mul, map_one, map_natCast, RatFunc.algebraMap_X]
  unfold PosNearZero
  rw [heq, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, mul_one]
  rw [trailingCoeff_eq_coeff_zero (by simp)]
  simp

/-- `ℝ` embeds order-preservingly into `RatFunc ℝ` via `RatFunc.C`. -/
theorem C_lt_C_iff (r s : ℝ) : RatFunc.C r < RatFunc.C s ↔ r < s := by
  rw [lt_iff_posNearZero_sub]
  have heq : RatFunc.C s - RatFunc.C r
      = algebraMap (Polynomial ℝ) (RatFunc ℝ) (Polynomial.C (s - r)) := by
    rw [Polynomial.C_sub, map_sub, RatFunc.algebraMap_C, RatFunc.algebraMap_C]
  unfold PosNearZero
  rw [heq, RatFunc.num_algebraMap, RatFunc.denom_algebraMap, mul_one, trailingCoeff_C]
  constructor <;> intro <;> linarith

end InfinitesimalRatFunc
end Math
