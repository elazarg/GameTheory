/-
# The executable rational finite-table frontend

This module contains data, enumeration, and boolean procedures only. It imports
`GameTheory.Core.Signature` for the shared profile operations and nothing
real-valued, topological, or noncomputable. There is no
`open Classical` and no `Fintype.ofFinite`: the game's own enumeration and
decidable equality are authoritative everywhere below.

Correctness against the semantic predicates lives in
`GameTheory.Finite.Correctness`, which may import Core.
-/

import GameTheory.Core.Signature
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Rat.Lemmas

namespace GameTheory.Finite

universe u v

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- A finite game in rational table form. The `Fintype` and `DecidableEq`
witnesses are carried as data, so every algorithm below uses the game's actual
enumeration. -/
structure TableGame (ι : Type u) [Fintype ι] [DecidableEq ι] where
  /-- Each player's action carrier. -/
  Action : ι → Type v
  /-- The authoritative enumeration of each action carrier. -/
  actionFintype : ∀ i, Fintype (Action i)
  /-- The authoritative decidable equality of each action carrier. -/
  actionDecEq : ∀ i, DecidableEq (Action i)
  /-- Exact rational payoffs. -/
  payoff : (∀ i, Action i) → ι → ℚ

namespace TableGame

instance instFintypeAction (G : TableGame ι) (i : ι) : Fintype (G.Action i) :=
  G.actionFintype i

instance instDecidableEqAction (G : TableGame ι) (i : ι) : DecidableEq (G.Action i) :=
  G.actionDecEq i

/-- The signature of the compiled game: strategies are actions and outcomes are
realized action profiles. -/
abbrev sig (G : TableGame ι) : GameSignature ι where
  Strategy := G.Action
  Outcome := ∀ i, G.Action i

instance instFintypeProfile (G : TableGame ι) : Fintype (Profile G.sig) :=
  Pi.instFintype

instance instDecidableEqProfile (G : TableGame ι) : DecidableEq (Profile G.sig) :=
  Fintype.decidablePiFintype

/-- Mixed strategies presented by exact rational weights. -/
abbrev mixedSig (G : TableGame ι) : GameSignature ι where
  Strategy i := G.Action i → ℚ
  Outcome := ∀ i, G.Action i

/-! ## Pure Nash -/

/-- Boolean pure-Nash verification. -/
def isNash (G : TableGame ι) (profile : Profile G.sig) : Bool :=
  decide (∀ (who : ι) (replacement : G.Action who),
    G.payoff (Profile.update profile who replacement) who ≤ G.payoff profile who)

/-- Enumerate every pure Nash equilibrium. -/
def enumerateNash (G : TableGame ι) : Finset (Profile G.sig) :=
  Finset.univ.filter fun profile => G.isNash profile

/-! ## Dominance -/

/-- `preferred` is at least as good as `alternative` at every profile. -/
def veryWeaklyDominates (G : TableGame ι) (who : ι)
    (preferred alternative : G.Action who) : Bool :=
  decide (∀ profile : Profile G.sig,
    G.payoff (Profile.update profile who alternative) who ≤
      G.payoff (Profile.update profile who preferred) who)

/-- `preferred` is at least as good everywhere and strictly better somewhere. -/
def weaklyDominates (G : TableGame ι) (who : ι)
    (preferred alternative : G.Action who) : Bool :=
  decide ((∀ profile : Profile G.sig,
      G.payoff (Profile.update profile who alternative) who ≤
        G.payoff (Profile.update profile who preferred) who) ∧
    ∃ profile : Profile G.sig,
      G.payoff (Profile.update profile who alternative) who <
        G.payoff (Profile.update profile who preferred) who)

/-- `preferred` is strictly better than `alternative` at every profile. -/
def strictlyDominates (G : TableGame ι) (who : ι) (preferred alternative : G.Action who) : Bool :=
  decide (∀ profile : Profile G.sig,
    G.payoff (Profile.update profile who alternative) who <
      G.payoff (Profile.update profile who preferred) who)

/-- `s` is at least as good as every alternative at every profile. -/
def isDominant (G : TableGame ι) (who : ι) (s : G.Action who) : Bool :=
  decide (∀ alternative : G.Action who,
    G.veryWeaklyDominates who s alternative = true)

/-- Every player plays a dominant action. -/
def isDominantProfile (G : TableGame ι) (profile : Profile G.sig) : Bool :=
  decide (∀ who : ι, G.isDominant who (profile who) = true)

/-! ## Iterated strict dominance -/

/-- One round of elimination by pure strictly dominating actions, where
domination is tested only against opponents' actions that are still allowed. -/
def eliminatePureRound (G : TableGame ι) (allowed : ∀ i, Finset (G.Action i)) :
    ∀ i, Finset (G.Action i) :=
  fun i => (allowed i).filter fun s =>
    ∀ t ∈ allowed i, ¬ ∀ profile : Profile G.sig, (∀ j, profile j ∈ allowed j) →
      G.payoff (Profile.update profile i s) i < G.payoff (Profile.update profile i t) i

/-- The actions surviving `round` rounds of iterated pure strict dominance. -/
def pureSurvivors (G : TableGame ι) : ℕ → ∀ i, Finset (G.Action i)
  | 0 => fun _ => Finset.univ
  | round + 1 => G.eliminatePureRound (G.pureSurvivors round)

/-- `pureSurvivors` has stabilized at `round`. Once this is `true`, no later
pure-elimination round removes anything. -/
def pureSurvivorsStable (G : TableGame ι) (round : ℕ) : Bool :=
  decide (∀ i, G.pureSurvivors (round + 1) i = G.pureSurvivors round i)

/-! ## Pareto efficiency -/

/-- `better` Pareto-dominates `worse`. -/
def paretoDominates (G : TableGame ι) (better worse : Profile G.sig) : Bool :=
  decide ((∀ i, G.payoff worse i ≤ G.payoff better i) ∧
    ∃ i, G.payoff worse i < G.payoff better i)

/-- No profile Pareto-dominates `profile`. -/
def isParetoEfficient (G : TableGame ι) (profile : Profile G.sig) : Bool :=
  decide (∀ other : Profile G.sig, G.paretoDominates other profile = false)

/-! ## Exact rational mixed profiles -/

/-- The rational weight vectors are genuine distributions. -/
def isMixed (G : TableGame ι) (mixed : Profile G.mixedSig) : Bool :=
  decide (∀ i, (∀ a, 0 ≤ mixed i a) ∧ ∑ a, mixed i a = 1)

/-- The independent probability of a pure profile under a rational mixed
profile. -/
def mixedWeight (G : TableGame ι) (mixed : Profile G.mixedSig)
    (profile : Profile G.sig) : ℚ :=
  ∏ i, mixed i (profile i)

/-- Exact rational expected payoff of a mixed profile. -/
def expectedPayoff (G : TableGame ι) (mixed : Profile G.mixedSig) (who : ι) : ℚ :=
  ∑ profile : Profile G.sig, G.mixedWeight mixed profile * G.payoff profile who

/-- The point-mass rational mixed strategy on `a`. -/
def pureMixed (G : TableGame ι) (who : ι) (a : G.Action who) : G.Action who → ℚ :=
  fun b => if b = a then 1 else 0

/-- Exact verification of a supplied rational mixed profile. -/
def verifyMixedNash (G : TableGame ι) (mixed : Profile G.mixedSig) : Bool :=
  G.isMixed mixed &&
    decide (∀ (who : ι) (a : G.Action who),
      G.expectedPayoff (Profile.update mixed who (G.pureMixed who a)) who ≤
        G.expectedPayoff mixed who)

end TableGame

end GameTheory.Finite
