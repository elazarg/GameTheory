/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.PureExternalityCycle
import Math.LinearAlgebra.OwnerLabeledFlowHolonomy

/-!
# The Route-0 acceptance pair of the pure-externality cycle

The mandatory acceptance test of Question 79 (*Direct Closure of
Strategically Inert Mixed Certificates*), Part C: the two-state
pure-externality game of Question 71 Part E must be closed **at the target
`v = (0, 0)` by the prescribed profile, leaving the mixed circulation
unconsumed**.

This file assembles the two halves of that test, which until now lived in
two unrelated modules:

* the *game* half — `GameTheory.StochasticGame.PureExternalityCycle`, whose
  capstone `isUniformEquilibriumPayoff_zero` says the prescribed
  constant-`0` profile witnesses the uniform equilibrium payoff `(0, 0)`;
* the *flow* half — `Math.LinearAlgebra.OwnerLabeledFlowHolonomy.TwoCycle`,
  the abstract two-row owner-switching circulation system on which the
  mixed uniform circulation has strictly positive holonomy, no owner-pure
  component and no common scalar account potential.

The bridge is the *tagged-row reading* of the game's two unilateral
zero-slack deviation rows (Question 71, eq. (62)-(63)): row `b` is player
`b`'s deviation to action `1` at the state `b` that player `b` controls.
Under that reading the row system **is** `TwoCycle`, and the row charge is
identically `1` (eq. (77)).

## The acceptance pair

`routeZero_acceptance` states the conjunction that any general Route-0
theorem must reproduce.  The two halves point in apparently opposite
directions and are both true of the same finite datum:

* the row system carries a normalized mixed circulation whose holonomy is
  `1 > 0`, no owner-pure circulation at all, and no common account
  potential (Question 71, eq. (78)-(81));
* the game nevertheless *has* `IsUniformEquilibriumPayoff` at `(0, 0)`,
  witnessed by the prescribed profile.

So positive mixed holonomy is **not** an obstruction to equilibrium: the
mixed certificate encodes a joint improvement that no unilateral deviator
can realize, and a Route-0 closure theorem must close this leaf *without
consuming the circulation*.

## Honesty note on the charge

`rowCharge` is read off the payoff table directly:
`stagePayoffOf b b true - target b`, the deviating owner's own stage payoff
on their deviation row minus their target coordinate.  Informally this is
the Bellman slack of the tagged row, and the underlying discounted Bellman
equalities are *exact* (Question 71, §12, eq. (64)-(67): neither a player's
own payoff nor the transition depends on that player's own action, so every
action is an exact discounted best reply at every discount factor).  But
this file does **not** formalize a germ-level tagging layer that would
derive the charge from a formally defined Bellman slack; that bridge would
need infrastructure this acceptance test does not require, and is future
work.  Everything below is proved from the payoff table and the abstract
flow system, with nothing hidden in between.

## Main definitions

* `rowSrc`, `rowOwner`, `rowTransition` — the tagged-row reading of the two
  unilateral deviation rows, definitionally the abstract `TwoCycle` data
* `rowCharge` — the target-relative owner charge of a row
* `mixedCertificate` — the uniform `(1/2, 1/2)` circulation `m` of eq. (69)

## Main results

* `rowCharge_eq_one` — both row charges equal `1` (eq. (77))
* `mixedCertificate_not_zeroHolonomy` — the gluing condition fails
* `mixedCertificate_no_accountPotential` — eq. (78)-(80)
* `ownerPure_harmless` — every owner-pure circulation vanishes (§13)
* `routeZero_acceptance` — **the acceptance pair**
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

namespace PureExternalityCycleHolonomy

open Math.LinearAlgebra.OwnerLabeledFlowHolonomy
open PureExternalityCycle (game Player stagePayoffOf)

/-! ## The tagged-row reading

Question 71, eq. (62)-(63).  There are exactly two unilateral zero-slack
deviation rows: player `1` playing action `1` at state `x`, and player `2`
playing action `1` at state `y`.  In the `Bool` encoding of
`PureExternalityCycle` — where state `s` is the state controlled by player
`s` — both rows are indexed by the single bit `b`: *row `b` is player `b`
deviating at state `b`*. -/

/-- The two tagged deviation rows.  Row `false` is player 1's deviation at
state `x`; row `true` is player 2's deviation at state `y`. -/
abbrev Row : Type := Bool

/-- Row `b` is sourced at state `b`, the state its owner controls.  This is
the abstract `TwoCycle.src` on the nose. -/
def rowSrc : Row → Bool := TwoCycle.src

/-- Row `b` is owned by player `b`, the deviator.  The two rows have
distinct owners: this is the *mixed* character of the certificate.  Equal
to the abstract `TwoCycle.ownerOf`. -/
def rowOwner : Row → Player := TwoCycle.ownerOf

/-- Every action switches the state, so row `b` moves deterministically
from `b` to `!b` — the lifted history cycle `ℓ₁ → ℓ₂ → ℓ₁` of eq. (68).
Equal to the abstract `TwoCycle.transition`. -/
def rowTransition : Row → Bool → ℝ := TwoCycle.transition

/-- The deviating action taken on every tagged row: action `1`, the
nonprescribed action, which pays the *opponent* `1` instead of `-1`. -/
def rowAction : Row → Bool := fun _ => true

/-- The target payoff vector `v = (0, 0)` of eq. (60): the uniform value
the prescribed profile delivers. -/
def target : Payoff Player := fun _ => 0

/-- **The target-relative owner charge of a tagged row.**  Read directly
off the payoff table: the deviating owner's own stage payoff on their
deviation row, minus that owner's target coordinate.

Informally this is the row's Bellman slack against the target; see the
honesty note in the module docstring — the discounted Bellman equalities
of Question 71 §12 are exact, but no germ-level tagging layer is
formalized here. -/
def rowCharge : Row → ℝ := fun b =>
  stagePayoffOf (rowSrc b) (rowOwner b) (rowAction b) - target (rowOwner b)

/-- Both row charges are `1`: the owner of a state is paid `1` there
whatever it does (pure externality), and the target is `0`.  This is the
positive owner-labelled mean of Question 71, eq. (77). -/
@[simp] theorem rowCharge_eq_one (b : Row) : rowCharge b = 1 := by
  cases b <;>
    norm_num [rowCharge, rowSrc, rowOwner, rowAction, target, stagePayoffOf,
      TwoCycle.src, TwoCycle.ownerOf]

/-- The charge cochain is the abstract two-row charge at `α₁ = α₂ = 1`. -/
theorem rowCharge_eq_charge : rowCharge = TwoCycle.charge 1 1 := by
  funext b
  rw [rowCharge_eq_one]
  cases b <;> simp [TwoCycle.charge]

/-- The row transition weights form a row-stochastic matrix. -/
theorem isStochastic_rowTransition : IsStochastic rowTransition :=
  TwoCycle.isStochastic_transition

/-! ## The mixed certificate -/

/-- **The mixed certificate `m`** of Question 71, eq. (69): the uniform
occupation `m(r₁) = m(r₂) = 1/2` of the two tagged deviation rows.  It is
the unique normalized point of the active circulation cone (eq. (70)), and
it is *mixed*: both owners carry mass. -/
def mixedCertificate : Row → ℝ := TwoCycle.uniform

/-- The mixed certificate is a normalized circulation of the tagged-row
system: nonnegative, balanced at both states, total mass `1`. -/
theorem isNormalizedCirculation_mixedCertificate :
    IsNormalizedCirculation rowSrc rowTransition mixedCertificate :=
  TwoCycle.isNormalizedCirculation_uniform

/-- A normalized circulation of the tagged-row system exists. -/
theorem exists_isNormalizedCirculation :
    ∃ m : Row → ℝ, IsNormalizedCirculation rowSrc rowTransition m :=
  ⟨mixedCertificate, isNormalizedCirculation_mixedCertificate⟩

/-- **The mixed holonomy is `1`.**  Each row contributes `1/2 · 1`; this is
the left-hand side of the Farkas identity of eq. (81) at `α₁ = α₂ = 1`. -/
theorem holonomy_mixedCertificate : holonomy rowCharge mixedCertificate = 1 := by
  have h : holonomy (TwoCycle.charge 1 1) TwoCycle.uniform = 1 := by
    rw [TwoCycle.holonomy_uniform]
    norm_num
  rw [rowCharge_eq_charge]
  exact h

/-- The mixed holonomy is strictly positive. -/
theorem holonomy_mixedCertificate_pos : 0 < holonomy rowCharge mixedCertificate := by
  rw [holonomy_mixedCertificate]
  norm_num

/-! ## The three abstract refutations, read in the game -/

/-- **The gluing condition fails.**  The game's mixed circulation is the
exact Farkas witness of Question 71, eq. (81): it is a genuine circulation
of the tagged-row system whose pairing with the charge cochain is
`(1 + 1) / 2 = 1 > 0`, so not every circulation pairs nonpositively. -/
theorem mixedCertificate_not_zeroHolonomy :
    ¬ ZeroHolonomy rowSrc rowTransition rowCharge := by
  rw [rowCharge_eq_charge]
  exact TwoCycle.not_zeroHolonomy (a₁ := 1) (a₂ := 1) (by norm_num)

/-- **No common scalar account potential** (Question 71, eq. (78)-(80)).
A potential `H` would have to satisfy `1 + H y - H x ≤ 0` on player 1's row
and `1 + H x - H y ≤ 0` on player 2's row; adding gives `2 ≤ 0`.  The
common-account route (Route C) is therefore closed for this datum. -/
theorem mixedCertificate_no_accountPotential :
    ¬ ∃ H : Bool → ℝ, IsAccountPotential rowSrc rowTransition rowCharge H := by
  rw [rowCharge_eq_charge]
  exact TwoCycle.not_exists_accountPotential (a₁ := 1) (a₂ := 1) (by norm_num)

/-- **Owner-pure harmlessness on the active cone** (Question 71, §13).
Every circulation of the tagged-row system supported on a single owner's
rows is identically zero: neither owner has any nonzero circulation at
all, so the certificate has no owner-pure component to purify.  This is
the hypothesis Route 0 is allowed to use. -/
theorem ownerPure_harmless {i : Player} {μ : Row → ℝ}
    (hcirc : IsCirculation rowSrc rowTransition μ)
    (hpure : IsOwnerPure rowOwner i μ) : μ = 0 :=
  TwoCycle.ownerPure_circulation_eq_zero hcirc hpure

/-! ## The acceptance pair -/

/-- **The Route-0 acceptance pair of Question 79 Part C.**  The two sides
of the mandatory acceptance test, as one proposition: the flow side (a
normalized mixed circulation with positive holonomy, no owner-pure
component, no common account potential) and the game side (the prescribed
profile really does deliver the target as a uniform equilibrium
payoff). -/
structure RouteZeroAcceptance : Prop where
  /-- The mixed certificate `m` is a normalized circulation of the row
  system generated by the game's exact unilateral best replies. -/
  normalized : IsNormalizedCirculation rowSrc rowTransition mixedCertificate
  /-- Its holonomy against the target-relative charges is strictly
  positive. -/
  holonomy_pos : 0 < holonomy rowCharge mixedCertificate
  /-- Every owner-pure circulation of the row system vanishes. -/
  ownerPure_trivial : ∀ (i : Player) (μ : Row → ℝ),
    IsCirculation rowSrc rowTransition μ → IsOwnerPure rowOwner i μ → μ = 0
  /-- The gluing condition fails. -/
  not_zeroHolonomy : ¬ ZeroHolonomy rowSrc rowTransition rowCharge
  /-- No common scalar account potential discharges the charges. -/
  no_accountPotential :
    ¬ ∃ H : Bool → ℝ, IsAccountPotential rowSrc rowTransition rowCharge H
  /-- **And yet** the game has the target as a uniform equilibrium payoff,
  from every initial state. -/
  equilibrium : ∀ s₀ : Bool, game.IsUniformEquilibriumPayoff s₀ target

/-- **The acceptance pair holds for the two-state pure-externality
cycle.**

The row system generated by the game's exact unilateral best replies at
the target `(0, 0)` carries a normalized *mixed* circulation with strictly
positive holonomy, no owner-pure component whatsoever, and no common
scalar account potential — *and* the game nevertheless has
`IsUniformEquilibriumPayoff` at `(0, 0)`, witnessed by the prescribed
constant-`0` profile
(`PureExternalityCycle.isUniformEquilibriumPayoff_zero`).

Two consequences, which are the point of the file.

* **Any general Route-0 theorem (Question 79 Part A) must reproduce this
  closure without consuming the circulation.**  The certificate `m` is
  still a full-support normalized circulation after the closure; nothing
  in the equilibrium proof spends it.
* **Any claim that positive mixed holonomy obstructs equilibrium is
  refuted by this instance.**  Here the holonomy is `1 > 0`, the gluing
  invariant of Question 71 §20 fails, every account route is closed — and
  the equilibrium exists anyway.  The mixed certificate encodes a *joint*
  improvement that no unilateral deviator can realize, because in this
  game a player's own payoff never depends on that player's own action
  (`PureExternalityCycle.stagePayoff_indep_own_action`). -/
theorem routeZero_acceptance : RouteZeroAcceptance where
  normalized := isNormalizedCirculation_mixedCertificate
  holonomy_pos := holonomy_mixedCertificate_pos
  ownerPure_trivial := fun _ _ hcirc hpure => ownerPure_harmless hcirc hpure
  not_zeroHolonomy := mixedCertificate_not_zeroHolonomy
  no_accountPotential := mixedCertificate_no_accountPotential
  equilibrium := PureExternalityCycle.isUniformEquilibriumPayoff_zero

/-- The acceptance pair spelled out as a bare conjunction, for consumers
that prefer not to unfold the structure. -/
theorem routeZero_acceptance_conj :
    (IsNormalizedCirculation rowSrc rowTransition mixedCertificate ∧
        0 < holonomy rowCharge mixedCertificate ∧
        ¬ ZeroHolonomy rowSrc rowTransition rowCharge ∧
        ¬ ∃ H : Bool → ℝ, IsAccountPotential rowSrc rowTransition rowCharge H) ∧
      ∀ s₀ : Bool, game.IsUniformEquilibriumPayoff s₀ target :=
  ⟨⟨routeZero_acceptance.normalized, routeZero_acceptance.holonomy_pos,
      routeZero_acceptance.not_zeroHolonomy,
      routeZero_acceptance.no_accountPotential⟩,
    routeZero_acceptance.equilibrium⟩

end PureExternalityCycleHolonomy

end StochasticGame

end GameTheory

end
