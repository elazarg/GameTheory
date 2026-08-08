/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Repair.SureSetRepairCounterexample
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Repair.BoundedSurgeryDescentCounterexample
import Math.SurvivalProduct

/-!
# A completely absorbing inverse iterate with unbounded values

## The claim this file fences

An *inverse iterate* for a quitting weight is an `IsQuittingInverseIterate`:
rows `y t` and values `z t` with `z t = F_{y t}(z (t+1))` and `(y t, z (t+1))`
complementary at every time.  Its survival product is `∏_t c(y t)`, and it is
*completely absorbing* when that product is `0`.  The claim

> this weight admits no completely absorbing inverse iterate,

**stated with no boundedness condition on the values**, is
`NoCompletelyAbsorbingInverseIterate`.  This file refutes it for an explicit
three-coordinate weight, for every value of the weight's parameter `η ≥ 0`.

## Relation to the source

E. Solan, *The dynamics of the Nash correspondence and `n`-player stochastic
games*, Int. Game Theory Rev. **3**(4), 291–299 (2001),
doi:10.1142/S0219198901000488, Theorem 2.1: for every
`ε > 0` sufficiently small, `F_ε` contains only trivial vectors.  There an
*admissible sequence* is exactly an `IsQuittingInverseIterate`, *completely
absorbing* is exactly `IsCompletelyAbsorbing`, `F_ε` is the set of first
elements of admissible sequences, and `y ∈ F_ε` is *trivial* when no admissible
sequence for it is completely absorbing.  The game `G_ε` of its Figure 1 is
the table below multiplied by `3` on all seven entries, with `η = ε`.  So the
statement matches, and **no boundedness hypothesis appears in it**.

Its proof runs through display (1), `Σ_i y_i ≤ 4` and `0 ≤ y_i ≤ 3` — the
convex hull of the terminal payoffs — asserted for non-trivial `y` on the
ground that a completely absorbing admissible sequence makes `y(1)` the
*equilibrium payoff* of the induced profile.  That step needs the homogeneous
boundary term to vanish, which needs the values bounded.  The witness below is
a machine-checked instance where it does not: in the source's scaling it is
`y = (1, 3, 1 + η p)`, whose coordinate sum `5 + η p` exceeds the `4` of
display (1), and its induced profile is not an equilibrium of `G_ε` because
the third player receives `0` and can profit by quitting.

So the literal statement is false and the unstated hypothesis is boundedness;
the theorem's intended content is the bounded form, which its proof
establishes and which nothing here touches.

## What is and is not refuted

**The witness constructed here has unbounded values.**  Its third value
coordinate grows exactly like the reciprocal of the survival product, so it
leaves every bounded box (`not_bddAbove_value`).  Consequently:

* the **unqualified** form — no boundedness condition on the values — is
  false, and `not_noCompletelyAbsorbingInverseIterate` is the machine-checked
  fence saying so;
* the **bounded** form, `NoBoundedCompletelyAbsorbingInverseIterate`, is
  **not** refuted by anything in this file.  It is the statement the research
  route actually needs, and it is what Solan's Theorem 2.1 proves.

A reader who takes away "the no-absorbing-iterate claim is false" without the
boundedness qualifier will draw a wrong conclusion about the route.  Both
Props are stated separately below precisely so that the gap between them is
visible in the formal text and not only in prose.

## The mechanism

The refutation is not delicate.  Write `c_N = ∏_{t < N} c(y t)` for the
survival prefix.  A bounded value array forces `c_N * z_N → 0`, which is what
lets a limit argument consume the homogeneous boundary term of the backward
recursion.  Here `c_N * (z_N)_2` is the **nonzero constant** `(1 + η p)/3`
(`survivalPrefix_mul_value_two`), so the boundary term is never consumed even
though `c_N → 0`.  That unconsumed homogeneous term is the entire content of
the counterexample, and it is exactly what a boundedness hypothesis rules
out.

## The weight

With players `0, 1, 2` (the table's `1, 2, 3`) and parameter `η ≥ 0`:

| quitter set | reward |
|---|---|
| `{0}`       | `(1/3, 1, 0)` |
| `{1}`       | `(0, 1/3, 1)` |
| `{2}`       | `(1, 0, 1/3)` |
| `{0,1}`     | `((1+η)/3, 0, 1/3)` |
| `{0,2}`     | `(0, 1/3, (1+η)/3)` |
| `{1,2}`     | `(1/3, (1+η)/3, 0)` |
| `{0,1,2}`   | `(0, 0, 0)` |

`Fin 3` is used rather than an abstract three-element type because the
Fubini expansion `expect_pmfPi_fin3_bool` and the `![a, b, c]` action
notation are already available for it, which makes the eight-action
expectations reduce by `simp`.

## The witness

For `p ∈ (0,1)`, `q = 1 - p` and `K = (1 + η p)/3`, at every time `t`

    y t = (p, 0, 0),      z t = (1/3, 1, K / q ^ t).

Only `∅` and `{0}` carry mass under `y t`, so `F_{y t}(z) = (p/3 + q z_0,
p + q z_1, q z_2)`; the three fixed-point checks are `(p + q)/3 = 1/3`,
`p + q = 1`, and `q * (K / q^(t+1)) = K / q^t`.  Complementarity holds with
room to spare at the two silent coordinates: coordinate `0` is exactly
indifferent, coordinate `1` has gap `q/3 - 1 < 0`, and coordinate `2` has gap
`K (1 - q^{-t}) ≤ 0`.  The survival factor is the constant `q < 1`, so the
survival prefix is `q^N → 0`.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι]

/-! ## Survival prefixes and complete absorption -/

/-- The survival prefix `∏_{t < N} c(y t)`: the probability that the first
`N` rows all fail to absorb. -/
def quittingSurvivalPrefix (rows : ℕ → ι → PMF Bool) (N : ℕ) : ℝ :=
  ∏ t ∈ Finset.range N, quittingStationaryContinueMass (rows t)

/-- **Bridge to the canonical survival product.**  `quittingSurvivalPrefix`
is `Math.survivalProduct` at the stationary continue mass, hardwired to
`start = 0` -- see the module docstring of `Math.SurvivalProduct` for the
full census this bridges into. -/
theorem quittingSurvivalPrefix_eq_survivalProduct (rows : ℕ → ι → PMF Bool) (N : ℕ) :
    quittingSurvivalPrefix rows N =
      Math.survivalProduct (fun t => quittingStationaryContinueMass (rows t)) 0 N := by
  simp [quittingSurvivalPrefix, Math.survivalProduct]

@[simp] theorem quittingSurvivalPrefix_zero (rows : ℕ → ι → PMF Bool) :
    quittingSurvivalPrefix rows 0 = 1 := by
  simp [quittingSurvivalPrefix]

theorem quittingSurvivalPrefix_succ (rows : ℕ → ι → PMF Bool) (N : ℕ) :
    quittingSurvivalPrefix rows (N + 1) =
      quittingSurvivalPrefix rows N * quittingStationaryContinueMass (rows N) :=
  Finset.prod_range_succ _ N

theorem quittingSurvivalPrefix_nonneg (rows : ℕ → ι → PMF Bool) (N : ℕ) :
    0 ≤ quittingSurvivalPrefix rows N :=
  Finset.prod_nonneg fun t _ => quittingStationaryContinueMass_nonneg (rows t)

theorem quittingSurvivalPrefix_le_one (rows : ℕ → ι → PMF Bool) (N : ℕ) :
    quittingSurvivalPrefix rows N ≤ 1 :=
  Finset.prod_le_one (fun t _ => quittingStationaryContinueMass_nonneg (rows t))
    fun t _ => quittingStationaryContinueMass_le_one (rows t)

theorem quittingSurvivalPrefix_antitone (rows : ℕ → ι → PMF Bool) :
    Antitone (quittingSurvivalPrefix rows) := by
  refine antitone_nat_of_succ_le fun N => ?_
  rw [quittingSurvivalPrefix_succ]
  calc quittingSurvivalPrefix rows N * quittingStationaryContinueMass (rows N)
      ≤ quittingSurvivalPrefix rows N * 1 :=
        mul_le_mul_of_nonneg_left
          (quittingStationaryContinueMass_le_one (rows N))
          (quittingSurvivalPrefix_nonneg rows N)
    _ = quittingSurvivalPrefix rows N := mul_one _

/-- The survival prefix always converges: every factor lies in `[0,1]`, so the
prefix is antitone and bounded below by `0`.  This is why demanding the limit
be `0` — rather than invoking an infinite-product formalism — is the faithful
reading of `∏_t c(y t) = 0`: the limit exists unconditionally, and it is `0`
exactly when the play is absorbed almost surely. -/
theorem exists_tendsto_quittingSurvivalPrefix (rows : ℕ → ι → PMF Bool) :
    ∃ L : ℝ, Tendsto (quittingSurvivalPrefix rows) atTop (𝓝 L) :=
  ⟨_, tendsto_atTop_ciInf (quittingSurvivalPrefix_antitone rows)
    ⟨0, by rintro x ⟨N, rfl⟩; exact quittingSurvivalPrefix_nonneg rows N⟩⟩

/-- An array of rows is **completely absorbing** when its survival product is
`0`, read as the limit of the survival prefixes.  By
`exists_tendsto_quittingSurvivalPrefix` that limit always exists, so this is
an honest reading of `∏_t c(y t) = 0` and not a convention choice. -/
def IsCompletelyAbsorbing (rows : ℕ → ι → PMF Bool) : Prop :=
  Tendsto (quittingSurvivalPrefix rows) atTop (𝓝 0)

/-! ## The vanishing boundary term

The step of Solan's proof that this file's counterexample defeats is exactly
this squeeze: a bounded value sequence against a completely absorbing row
array forces the survival-prefix-weighted value to `0`.  The hypothesis used
below is an *eventual* bound on a single real sequence, which is strictly
weaker than the uniform bound over all times and all players that
`NoBoundedCompletelyAbsorbingInverseIterate` states: any array satisfying that
uniform bound satisfies this one, coordinate by coordinate, but not
conversely (a sequence may be unbounded yet still eventually bounded past
some horizon, or bounded only along the one coordinate examined). -/

/-- **The vanishing boundary term, general form.** If a real sequence is
eventually bounded and the rows are completely absorbing, the survival
prefix times the sequence tends to `0`.  `survivalPrefix_mul_value_two` below
is the case where even this weaker hypothesis fails: coordinate `2`'s value
is unbounded, on every tail, so no `M` works. -/
theorem tendsto_survivalPrefix_mul_of_bounded (rows : ℕ → ι → PMF Bool)
    (f : ℕ → ℝ) (M : ℝ) (hbound : ∀ᶠ t in atTop, |f t| ≤ M)
    (habsorb : IsCompletelyAbsorbing rows) :
    Tendsto (fun N => quittingSurvivalPrefix rows N * f N) atTop (𝓝 0) := by
  have hM : Tendsto (fun N => quittingSurvivalPrefix rows N * M) atTop (𝓝 0) := by
    simpa using habsorb.mul_const M
  refine squeeze_zero_norm' (hbound.mono fun N hN => ?_) hM
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (quittingSurvivalPrefix_nonneg rows N)]
  exact mul_le_mul_of_nonneg_left hN (quittingSurvivalPrefix_nonneg rows N)

/-- **The vanishing boundary term, uniform-bound corollary.** The shape
`NoBoundedCompletelyAbsorbingInverseIterate` actually states: a bound holding
at *every* time and for *every* player still gives the vanishing product, one
coordinate at a time. -/
theorem tendsto_survivalPrefix_mul_value_of_bounded
    (rows : ℕ → ι → PMF Bool) (values : ℕ → Payoff ι) (M : ℝ)
    (hbound : ∀ t who, |values t who| ≤ M) (habsorb : IsCompletelyAbsorbing rows)
    (who : ι) :
    Tendsto (fun N => quittingSurvivalPrefix rows N * values N who) atTop (𝓝 0) :=
  tendsto_survivalPrefix_mul_of_bounded rows (fun t => values t who) M
    (Eventually.of_forall fun t => hbound t who) habsorb

/-! ## Inverse iterates and the two forms of the claim -/

variable [DecidableEq ι]

/-- An **inverse iterate** of a quitting weight: an infinite backward array of
rows `rows t` and values `values t` such that at every time the current value
is the one-stage successor of the next value under the current row, and the
current row is exactly complementary against the next value.

Unfolded, `IsεQuittingRootSuccessorCertificate reward 0 y z' z` is
`z' = F_y(z)` together with `IsεQuittingRootEndpointNash reward z 0 y`, and
the latter is the pair of complementarity clauses
`(1 - y_i) * g_i ≤ 0` and `0 ≤ y_i * g_i` — i.e. `y_i < 1 → g_i ≤ 0` and
`y_i > 0 → g_i ≥ 0` — where `g_i` is `quittingRootEndpointDifference`,
player `i`'s pure-Quit value minus its pure-Continue value. -/
def IsQuittingInverseIterate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (rows : ℕ → ι → PMF Bool) (values : ℕ → Payoff ι) : Prop :=
  ∀ t, IsεQuittingRootSuccessorCertificate reward 0 (rows t)
    (values t) (values (t + 1))

/-- **The loose claim.**  "This weight admits no infinite complementary array
whose survival product tends to zero", with *no* boundedness condition on the
values.  This is the form that was restated in project control, and it is the
form refuted below. -/
def NoCompletelyAbsorbingInverseIterate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ¬ ∃ (rows : ℕ → ι → PMF Bool) (values : ℕ → Payoff ι),
      IsQuittingInverseIterate reward rows values ∧ IsCompletelyAbsorbing rows

/-- **The bounded claim.**  The same statement restricted to arrays whose
values stay in a fixed box.  Nothing in this file refutes it; it is weaker
than `NoCompletelyAbsorbingInverseIterate` and it is the statement the
research route needs.

**Status: neither established nor refuted here, and it is left as a bare
statement.**  `tendsto_survivalPrefix_mul_value_of_bounded` above proves
exactly the analytic step Solan's proof needs from boundedness — the
homogeneous boundary term `quittingSurvivalPrefix rows N * values N who`
vanishes — for *any* weight, not only the one below.  That step is not the
whole theorem: Solan's Theorem 2.1 goes on to use the vanished boundary term
to identify `values 0` with the equilibrium payoff of the profile induced by
`rows`, and from there derives the convex-hull bound `Σ_i y_i ≤ 4`,
`0 ≤ y_i ≤ 3` of its display (1) by a case analysis on the induced profile's
best-response structure — content with no counterpart in this file at all.
Establishing `NoBoundedCompletelyAbsorbingInverseIterate` for the weight
`reward` below would need that whole argument, not just the vanishing
boundary term.  Separately, the source proves its claim only "for `ε`
sufficiently small"; nothing here pins down whether
`NoBoundedCompletelyAbsorbingInverseIterate (reward η)` is even true at
every `η ≥ 0`, as opposed to some bounded range of `η`, so a further proof
attempt should not assume the unqualified-in-`η` statement is the right one
to target. -/
def NoBoundedCompletelyAbsorbingInverseIterate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ¬ ∃ (rows : ℕ → ι → PMF Bool) (values : ℕ → Payoff ι) (M : ℝ),
      (∀ t who, |values t who| ≤ M) ∧
        IsQuittingInverseIterate reward rows values ∧ IsCompletelyAbsorbing rows

/-- The loose claim is the *stronger* of the two: it implies the bounded
claim.  Hence refuting the loose claim, as the headline below does, refutes
only the stronger statement and leaves the weaker, bounded one open.  There
is no implication in the other direction, and none is proved here. -/
theorem noBounded_of_noCompletelyAbsorbingInverseIterate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (h : NoCompletelyAbsorbingInverseIterate reward) :
    NoBoundedCompletelyAbsorbingInverseIterate reward := by
  rintro ⟨rows, values, _, -, hiterate, habsorb⟩
  exact h ⟨rows, values, hiterate, habsorb⟩

namespace QuittingUnboundedInverseIterate

open QuittingSureSetRepairCounterexample (expect_pmfPi_fin3_bool)
open QuittingBoundedSurgeryDescentCounterexample (coin)

/-! ## The three-coordinate weight -/

/-- The three coordinates; the table's players `1, 2, 3`. -/
abbrev Player := Fin 3

/-- Coordinatewise introduction over the three players, with the indices in
numeral form.  `fin_cases` leaves goals whose index is a raw `Fin.mk`, which
blocks `rw` against lemmas stated at `0`, `1`, `2`; this helper does the case
split once and hands back numeral-indexed goals. -/
theorem forall_player {P : Player → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) :
    ∀ who : Player, P who := by
  intro who
  fin_cases who
  · exact h0
  · exact h1
  · exact h2

/-- A nonempty quitter set. -/
abbrev Terminal := {S : Finset Player // S.Nonempty}

/-- The seven-row terminal table, with parameter `η`.  Note that
`(1 + η) / 3` exceeds `1` once `η > 2`: the table is deliberately not
confined to `[0,1]`, and no such confinement is needed anywhere below. -/
def reward (η : ℝ) (S : Terminal) : Payoff Player :=
  if 0 ∈ S.1 then
    if 1 ∈ S.1 then
      (if 2 ∈ S.1 then ![0, 0, 0] else ![(1 + η) / 3, 0, 1 / 3])
    else
      (if 2 ∈ S.1 then ![0, 1 / 3, (1 + η) / 3] else ![1 / 3, 1, 0])
  else
    if 1 ∈ S.1 then
      (if 2 ∈ S.1 then ![1 / 3, (1 + η) / 3, 0] else ![0, 1 / 3, 1])
    else
      (if 2 ∈ S.1 then ![1, 0, 1 / 3] else ![0, 0, 0])

@[simp] theorem reward_zero (η : ℝ) (h : ({0} : Finset Player).Nonempty) :
    reward η ⟨{0}, h⟩ = ![1 / 3, 1, 0] := by
  simp [reward]

@[simp] theorem reward_one (η : ℝ) (h : ({1} : Finset Player).Nonempty) :
    reward η ⟨{1}, h⟩ = ![0, 1 / 3, 1] := by
  simp [reward]

@[simp] theorem reward_two (η : ℝ) (h : ({2} : Finset Player).Nonempty) :
    reward η ⟨{2}, h⟩ = ![1, 0, 1 / 3] := by
  simp [reward]

@[simp] theorem reward_zero_one (η : ℝ) (h : ({0, 1} : Finset Player).Nonempty) :
    reward η ⟨{0, 1}, h⟩ = ![(1 + η) / 3, 0, 1 / 3] := by
  simp [reward]

@[simp] theorem reward_zero_two (η : ℝ) (h : ({0, 2} : Finset Player).Nonempty) :
    reward η ⟨{0, 2}, h⟩ = ![0, 1 / 3, (1 + η) / 3] := by
  simp [reward]

@[simp] theorem reward_one_two (η : ℝ) (h : ({1, 2} : Finset Player).Nonempty) :
    reward η ⟨{1, 2}, h⟩ = ![1 / 3, (1 + η) / 3, 0] := by
  simp [reward]

@[simp] theorem reward_zero_one_two (η : ℝ)
    (h : ({0, 1, 2} : Finset Player).Nonempty) :
    reward η ⟨{0, 1, 2}, h⟩ = ![0, 0, 0] := by
  simp [reward]

/-! ## The row `y = (p, 0, 0)` -/

/-- The row `y = (p, 0, 0)`: coordinate `0` quits at rate `p`, coordinates `1`
and `2` are silent. -/
def row (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Player → PMF Bool :=
  fun who => if who = 0 then coin p hp0 hp1 else PMF.pure false

@[simp] theorem row_apply_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    row p hp0 hp1 0 = coin p hp0 hp1 := by
  simp [row]

@[simp] theorem row_apply_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    row p hp0 hp1 1 = PMF.pure false := by
  simp [row]

@[simp] theorem row_apply_two (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    row p hp0 hp1 2 = PMF.pure false := by
  simp [row]

@[simp] theorem expect_coin (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (f : Bool → ℝ) :
    expect (coin p hp0 hp1) f = (1 - p) * f false + p * f true := by
  rw [expect_eq_sum, Fintype.sum_bool]
  simp
  ring

/-! ## The six endpoint values at the row `(p, 0, 0)`

Only `∅` and `{0}` carry mass at `y = (p, 0, 0)`, so each endpoint is a
two-term expression. -/

/-- Coordinate `0` quitting alone gets `r({0})_0 = 1/3`, whatever the tail. -/
theorem quitPayoff_zero (η p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (tail : Payoff Player) :
    quittingRootQuitPayoff (reward η) tail (row p hp0 hp1) 0 = 1 / 3 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  simp [quittingRootPayoff, reward]

/-- Coordinate `0` continuing meets only silent opponents, so it gets the
tail. -/
theorem continuePayoff_zero (η p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (tail : Payoff Player) :
    quittingRootContinuePayoff (reward η) tail (row p hp0 hp1) 0 = tail 0 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  simp [quittingRootPayoff, reward]

/-- Coordinate `1` quitting meets `{1}` with mass `1 - p` and `{0,1}` with
mass `p`; `r({1})_1 = 1/3` and `r({0,1})_1 = 0`. -/
theorem quitPayoff_one (η p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (tail : Payoff Player) :
    quittingRootQuitPayoff (reward η) tail (row p hp0 hp1) 1 = (1 - p) / 3 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  simp [quittingRootPayoff, reward]
  ring

/-- Coordinate `1` continuing meets `∅` with mass `1 - p` and `{0}` with mass
`p`; `r({0})_1 = 1`. -/
theorem continuePayoff_one (η p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (tail : Payoff Player) :
    quittingRootContinuePayoff (reward η) tail (row p hp0 hp1) 1 =
      p + (1 - p) * tail 1 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  simp [quittingRootPayoff, reward]
  ring

/-- Coordinate `2` quitting meets `{2}` with mass `1 - p` and `{0,2}` with
mass `p`; `r({2})_2 = 1/3` and `r({0,2})_2 = (1+η)/3`.  The result is the
constant `K = (1 + η p)/3`. -/
theorem quitPayoff_two (η p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (tail : Payoff Player) :
    quittingRootQuitPayoff (reward η) tail (row p hp0 hp1) 2 =
      (1 + η * p) / 3 := by
  unfold quittingRootQuitPayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  simp [quittingRootPayoff, reward]
  ring

/-- Coordinate `2` continuing meets `∅` with mass `1 - p` and `{0}` with mass
`p`; `r({0})_2 = 0`, so the whole endpoint is the discounted tail. -/
theorem continuePayoff_two (η p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (tail : Payoff Player) :
    quittingRootContinuePayoff (reward η) tail (row p hp0 hp1) 2 =
      (1 - p) * tail 2 := by
  unfold quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  simp [quittingRootPayoff, reward]

/-! ## Quit probabilities of the row -/

@[simp] theorem row_quit_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (row p hp0 hp1 0 true).toReal = p := by
  simp

@[simp] theorem row_continue_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (row p hp0 hp1 0 false).toReal = 1 - p := by
  simp

@[simp] theorem row_quit_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (row p hp0 hp1 1 true).toReal = 0 := by
  simp

@[simp] theorem row_continue_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (row p hp0 hp1 1 false).toReal = 1 := by
  simp

@[simp] theorem row_quit_two (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (row p hp0 hp1 2 true).toReal = 0 := by
  simp

@[simp] theorem row_continue_two (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (row p hp0 hp1 2 false).toReal = 1 := by
  simp

/-! ## The value array -/

/-- `K = (1 + η p)/3`.  Three readings of the same number: coordinate `2`'s
pure-Quit endpoint value at the row `(p, 0, 0)`; the scale of the geometric
blow-up of coordinate `2`'s value; and the constant value of the unconsumed
homogeneous boundary term `c_N * (z_N)_2`. -/
def boundaryConstant (η p : ℝ) : ℝ := (1 + η * p) / 3

theorem boundaryConstant_pos {η p : ℝ} (hη : 0 ≤ η) (hp : 0 ≤ p) :
    0 < boundaryConstant η p := by
  have : 0 ≤ η * p := mul_nonneg hη hp
  unfold boundaryConstant
  linarith

/-- The value at time `t`: `(1/3, 1, K / q^t)` with `q = 1 - p`. -/
def value (η p : ℝ) (t : ℕ) : Payoff Player :=
  ![1 / 3, 1, boundaryConstant η p / (1 - p) ^ t]

@[simp] theorem value_apply_zero (η p : ℝ) (t : ℕ) : value η p t 0 = 1 / 3 := rfl

@[simp] theorem value_apply_one (η p : ℝ) (t : ℕ) : value η p t 1 = 1 := rfl

@[simp] theorem value_apply_two (η p : ℝ) (t : ℕ) :
    value η p t 2 = boundaryConstant η p / (1 - p) ^ t := rfl

/-! ## The backward recursion holds at every time -/

/-- `F_{(p,0,0)}(z)_0 = p/3 + q z_0`, which is `1/3` at `z_0 = 1/3`. -/
theorem successor_apply_zero (η p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ) :
    quittingRootSuccessorPayoff (reward η) (value η p (t + 1))
        (row p hp0 hp1) 0 = 1 / 3 := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quitPayoff_zero,
    continuePayoff_zero]
  simp only [row_quit_zero, row_continue_zero, value_apply_zero]
  ring

/-- `F_{(p,0,0)}(z)_1 = p + q z_1`, which is `1` at `z_1 = 1`. -/
theorem successor_apply_one (η p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ) :
    quittingRootSuccessorPayoff (reward η) (value η p (t + 1))
        (row p hp0 hp1) 1 = 1 := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quitPayoff_one,
    continuePayoff_one]
  simp only [row_quit_one, row_continue_one, value_apply_one]
  ring

/-- `F_{(p,0,0)}(z)_2 = q z_2`, which turns `K / q^(t+1)` into `K / q^t`. -/
theorem successor_apply_two (η p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (t : ℕ) :
    quittingRootSuccessorPayoff (reward η) (value η p (t + 1))
        (row p hp0 hp1.le) 2 = boundaryConstant η p / (1 - p) ^ t := by
  have hq : (0 : ℝ) < 1 - p := by linarith
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quitPayoff_two,
    continuePayoff_two]
  simp only [row_quit_two, row_continue_two, value_apply_two]
  rw [pow_succ]
  field_simp
  ring

theorem value_eq_successor (η p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (t : ℕ) :
    value η p t =
      quittingRootSuccessorPayoff (reward η) (value η p (t + 1))
        (row p hp0.le hp1.le) := by
  apply funext
  refine forall_player ?_ ?_ ?_
  · rw [value_apply_zero, successor_apply_zero]
  · rw [value_apply_one, successor_apply_one]
  · rw [value_apply_two, successor_apply_two η p hp0.le hp1]

/-! ## Complementarity holds at every time, at all three coordinates -/

/-- Coordinate `0` is exactly indifferent: its Quit endpoint `1/3` equals its
Continue endpoint `z_0 = 1/3`. -/
theorem endpointDifference_zero (η p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ) :
    quittingRootEndpointDifference (reward η) (value η p (t + 1))
      (row p hp0 hp1) 0 = 0 := by
  rw [quittingRootEndpointDifference, quitPayoff_zero, continuePayoff_zero]
  norm_num

/-- Coordinate `1` is silent and strictly prefers to continue: its gap is
`q/3 - 1 < 0`. -/
theorem endpointDifference_one (η p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (t : ℕ) :
    quittingRootEndpointDifference (reward η) (value η p (t + 1))
      (row p hp0 hp1) 1 = (1 - p) / 3 - 1 := by
  rw [quittingRootEndpointDifference, quitPayoff_one, continuePayoff_one]
  simp only [value_apply_one]
  ring

/-- Coordinate `2` is silent and weakly prefers to continue: its gap is
`K (1 - q^{-t})`, which is `0` at `t = 0` and strictly negative afterwards. -/
theorem endpointDifference_two (η p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (t : ℕ) :
    quittingRootEndpointDifference (reward η) (value η p (t + 1))
      (row p hp0 hp1.le) 2 =
      boundaryConstant η p - boundaryConstant η p / (1 - p) ^ t := by
  have hq : (0 : ℝ) < 1 - p := by linarith
  rw [quittingRootEndpointDifference, quitPayoff_two, continuePayoff_two]
  simp only [value_apply_two]
  rw [pow_succ]
  have : boundaryConstant η p = (1 + η * p) / 3 := rfl
  rw [← this]
  field_simp

theorem isEndpointNash (η p : ℝ) (hη : 0 ≤ η) (hp0 : 0 < p) (hp1 : p < 1)
    (t : ℕ) :
    IsεQuittingRootEndpointNash (reward η) (value η p (t + 1)) 0
      (row p hp0.le hp1.le) := by
  have hq : (0 : ℝ) < 1 - p := by linarith
  have hK : 0 < boundaryConstant η p := boundaryConstant_pos hη hp0.le
  have hpow : (0 : ℝ) < (1 - p) ^ t := pow_pos hq t
  have hpowle : (1 - p) ^ t ≤ 1 := pow_le_one₀ hq.le (by linarith)
  intro who
  revert who
  refine forall_player ?_ ?_ ?_
  · rw [endpointDifference_zero]
    constructor <;> simp
  · rw [endpointDifference_one]
    simp only [row_quit_one, row_continue_one]
    constructor
    · nlinarith
    · norm_num
  · rw [endpointDifference_two η p hp0.le hp1]
    simp only [row_quit_two, row_continue_two]
    refine ⟨?_, by norm_num⟩
    have hle : boundaryConstant η p ≤ boundaryConstant η p / (1 - p) ^ t := by
      rw [le_div_iff₀ hpow]
      nlinarith
    linarith

/-- **The witness is an inverse iterate**: the recursion and the
complementarity clauses hold at every time and at every coordinate. -/
theorem isQuittingInverseIterate (η p : ℝ) (hη : 0 ≤ η) (hp0 : 0 < p)
    (hp1 : p < 1) :
    IsQuittingInverseIterate (reward η) (fun _ => row p hp0.le hp1.le)
      (value η p) :=
  fun t => ⟨value_eq_successor η p hp0 hp1 t, isEndpointNash η p hη hp0 hp1 t⟩

/-! ## The witness is completely absorbing -/

/-- Only coordinate `0` can absorb, so one row survives with probability
`q = 1 - p`. -/
theorem continueMass_row (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingStationaryContinueMass (row p hp0 hp1) = 1 - p := by
  unfold quittingStationaryContinueMass
  rw [pmfPi_apply, ENNReal.toReal_prod]
  simp [quittingAllContinueAction, Fin.prod_univ_succ]

theorem survivalPrefix_eq_pow (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    quittingSurvivalPrefix (fun _ => row p hp0 hp1) N = (1 - p) ^ N := by
  unfold quittingSurvivalPrefix
  simp [continueMass_row]

theorem isCompletelyAbsorbing (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    IsCompletelyAbsorbing (fun _ : ℕ => row p hp0.le hp1.le) := by
  have hq : (0 : ℝ) ≤ 1 - p := by linarith
  have hlt : (1 : ℝ) - p < 1 := by linarith
  refine Tendsto.congr (fun N => (survivalPrefix_eq_pow p hp0.le hp1.le N).symm) ?_
  exact tendsto_pow_atTop_nhds_zero_of_lt_one hq hlt

/-! ## The mechanism: the homogeneous boundary term is never consumed -/

/-- **The mechanism.**  The survival prefix times coordinate `2`'s value is the
constant `K`, at every horizon.  The prefix tends to `0`; the product does
not.  A bounded value array would force this product to `0`, and that is
exactly the step a boundedness hypothesis buys. -/
theorem survivalPrefix_mul_value_two (η p : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (N : ℕ) :
    quittingSurvivalPrefix (fun _ => row p hp0.le hp1.le) N *
        value η p N 2 = boundaryConstant η p := by
  have hq : (0 : ℝ) < 1 - p := by linarith
  have hpow : ((1 : ℝ) - p) ^ N ≠ 0 := (pow_pos hq N).ne'
  rw [survivalPrefix_eq_pow, value_apply_two]
  field_simp

/-- The homogeneous boundary term does not vanish along the absorbing
sequence, even though the survival prefix does. -/
theorem not_tendsto_survivalPrefix_mul_value_two (η p : ℝ) (hη : 0 ≤ η)
    (hp0 : 0 < p) (hp1 : p < 1) :
    ¬ Tendsto (fun N => quittingSurvivalPrefix (fun _ => row p hp0.le hp1.le) N *
        value η p N 2) atTop (𝓝 0) := by
  intro htendsto
  have hconst : Tendsto (fun N : ℕ =>
      quittingSurvivalPrefix (fun _ => row p hp0.le hp1.le) N * value η p N 2)
      atTop (𝓝 (boundaryConstant η p)) := by
    refine Tendsto.congr
      (fun N => (survivalPrefix_mul_value_two η p hp0 hp1 N).symm) ?_
    exact tendsto_const_nhds
  have := tendsto_nhds_unique hconst htendsto
  exact absurd this (boundaryConstant_pos hη hp0.le).ne'

/-! ## The values are unbounded -/

/-- Coordinate `2`'s value blows up like the reciprocal of the survival
prefix. -/
theorem tendsto_value_two_atTop (η p : ℝ) (hη : 0 ≤ η) (hp0 : 0 < p)
    (hp1 : p < 1) :
    Tendsto (fun t => value η p t 2) atTop atTop := by
  have hq : (0 : ℝ) < 1 - p := by linarith
  have hone : (1 : ℝ) < (1 - p)⁻¹ := by
    have hmul := mul_lt_mul_of_pos_right (show (1 : ℝ) - p < 1 by linarith)
      (inv_pos.mpr hq)
    rwa [mul_inv_cancel₀ hq.ne', one_mul] at hmul
  have hpow : Tendsto (fun t : ℕ => ((1 - p)⁻¹) ^ t) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt hone
  have hscaled : Tendsto
      (fun t : ℕ => boundaryConstant η p * ((1 - p)⁻¹) ^ t) atTop atTop :=
    hpow.const_mul_atTop (boundaryConstant_pos hη hp0.le)
  refine hscaled.congr fun t => ?_
  rw [value_apply_two, inv_pow, ← div_eq_mul_inv]

/-- **The values leave every box.**  This is the exact gap between the refuted
loose claim and the untouched bounded claim: the witness constructed here is
not a bounded array, and nothing in this file says a bounded one exists. -/
theorem not_bddAbove_value (η p : ℝ) (hη : 0 ≤ η) (hp0 : 0 < p) (hp1 : p < 1) :
    ¬ ∃ M : ℝ, ∀ (t : ℕ) (who : Player), |value η p t who| ≤ M := by
  rintro ⟨M, hM⟩
  have hev := (tendsto_value_two_atTop η p hη hp0 hp1).eventually_gt_atTop M
  obtain ⟨t, ht⟩ := hev.exists
  have := hM t 2
  have habs : value η p t 2 ≤ |value η p t 2| := le_abs_self _
  linarith

/-! ## The headline -/

/-- **HEADLINE** — for every `η ≥ 0` the displayed three-coordinate weight
admits a completely absorbing inverse iterate, so the claim that it admits
none is false **when stated without a boundedness condition on the values**;
the witness here has unbounded values (`not_bddAbove_value`), and the bounded
form of the claim, `NoBoundedCompletelyAbsorbingInverseIterate`, is *not*
refuted by this and remains open. -/
theorem not_noCompletelyAbsorbingInverseIterate (η : ℝ) (hη : 0 ≤ η) :
    ¬ NoCompletelyAbsorbingInverseIterate (reward η) := by
  intro hclaim
  exact hclaim ⟨fun _ => row (1 / 2) (by norm_num) (by norm_num),
    value η (1 / 2),
    isQuittingInverseIterate η (1 / 2) hη (by norm_num) (by norm_num),
    isCompletelyAbsorbing (1 / 2) (by norm_num) (by norm_num)⟩

/-- The existential form of the headline, carrying the unboundedness of the
witness in the statement so the qualifier cannot be dropped by a reader who
only looks at the conclusion.  (The per-rate construction above works for
every `p ∈ (0,1)`; `p = 1/2` is chosen here only to close the existential.) -/
theorem exists_completelyAbsorbing_inverseIterate (η : ℝ) (hη : 0 ≤ η) :
    ∃ (rows : ℕ → Player → PMF Bool) (values : ℕ → Payoff Player),
      IsQuittingInverseIterate (reward η) rows values ∧
        IsCompletelyAbsorbing rows ∧
        ¬ ∃ M : ℝ, ∀ (t : ℕ) (who : Player), |values t who| ≤ M :=
  ⟨fun _ => row (1 / 2) (by norm_num) (by norm_num), value η (1 / 2),
    isQuittingInverseIterate η (1 / 2) hη (by norm_num) (by norm_num),
    isCompletelyAbsorbing (1 / 2) (by norm_num) (by norm_num),
    not_bddAbove_value η (1 / 2) hη (by norm_num) (by norm_num)⟩

end QuittingUnboundedInverseIterate

end GameTheory
