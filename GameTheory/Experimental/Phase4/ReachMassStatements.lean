/-
# EXP-019: can the reach-mass conditions be stated without transport?

The more general recall direction of Kuhn's theorem can be stated from three
conditions about *reach mass*, with recall demoted to a
sufficient condition. That is more general than what the library proves. It is
also, structurally, a family of named adequacy certificates — the stratification
D7 rejected on a baseline of zero consumers — so restating the theorem over
these conditions would be the first real consumer of such a level.

Before any of that is worth attempting, one question has to be answered, and it
is the falsifiable half of the prediction recorded for EXP-019: **can the three
conditions be written in this library's vocabulary without a transport in the
statement?**

The snapshot cannot. Its global determinism condition puts `▸` inside a
hypothesis, and its posterior-locality condition is stated through `HEq`, both
because its information projection lives over length-indexed lists of states.
The claim under test is that histories-as-data removes the need, because
reachability is intrinsic to a `Trace` and an information state can be
quantified over before the objects indexed by it.

This file is the answer and nothing more: the three conditions written out, and
one sufficiency proof to check that the third is not vacuous in the wrong
direction. It is not public API.

The answer is yes for all three. Condition one is direct. Condition two needs a
pointwise variant of a joint action, which is a transport in the obvious
spelling and none in the coordinate-decomposition spelling this layer already
uses. Condition three is where the snapshot needs heterogeneous equality, and
quantifying over the information state before the objects indexed by it removes
the need — both sides land in one type by construction.
-/

import GameTheory.Protocol.Information

noncomputable section

namespace GameTheory.Experimental.Phase4

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol (Trace History)

universe uι

variable {ι : Type uι} (E : ExecutionProtocol ι)

/-- One legal joint action at a state. -/
abbrev LegalJoint (state : E.State) : Type _ :=
  { joint : ∀ i, Option (E.Action i) // E.Legal state joint }

/-! ## Condition one: how a state is reached does not change its mass

Direct, and transport-free: both sides are real masses of the same target under
two laws over the same carrier. -/

/-- Two joint actions that can both produce a state produce it with the same
mass. -/
def StepMassInvariant : Prop :=
  ∀ {state target : E.State} (first second : LegalJoint E state),
    target ∈ (E.step state first).support → target ∈ (E.step state second).support →
      (E.step state first).prob target = (E.step state second).prob target

/-! ## Condition two: reaching a state factors player by player

The snapshot states this with a pointwise update of a profile. A pointwise
update of a dependent function transports along an equality of indices, and this
layer budgets that at zero — the same collision the commitment construction met.
The resolution is the same one: the coordinate decomposition already used for
factoring a product law also splices one coordinate into a joint action, and it
needs no transport of ours. -/

/-- The joint action that follows `witness` everywhere except at `i`, where it
follows `other`. -/
def spliceAt [DecidableEq ι] {state : E.State} (witness other : LegalJoint E state) (i : ι) :
    ∀ j, Option (E.Action j) :=
  (Equiv.piSplitAt i fun j => Option (E.Action j)).symm
    (other.1 i, fun j => witness.1 j.1)

/-- Given one joint action that reaches a state, another reaches it exactly when
each of its single-player variants does. -/
def StepSupportFactorization [DecidableEq ι] : Prop :=
  ∀ {state target : E.State} (witness other : LegalJoint E state),
    target ∈ (E.step state witness).support →
      (target ∈ (E.step state other).support ↔
        ∀ (i : ι) (variant : LegalJoint E state), variant.1 = spliceAt E witness other i →
          target ∈ (E.step state variant).support)

/-! ## Condition three: the posterior at an information state is local

The snapshot needs heterogeneous equality here, because the type of a local
strategy depends on the information state and the two sides are indexed by two
propositionally equal ones. Quantifying over the information state *first*, and
letting histories reach it by hypothesis, keeps both sides in one type. -/

variable {E} in
/-- **The answer's law at an information state does not depend on which history
reached it.** The two conditioning events are the player's own records along the
two histories; where recall fails those records differ, so the condition has
content. Both sides land in `FinDist (M.Choice i info)` for the one `info`
quantified over first, so nothing is transported.

Recall makes this automatic — the two records coincide — which is the precise
sense in which recall is *sufficient* rather than necessary. -/
def ActionPosteriorLocal (M : InformationModel E) (i : ι) : Prop :=
  ∀ (info : M.InfoState i) (mixed : M.MixedPolicy i) (first second : E.History),
    M.infoOf i first.trace = info → M.infoOf i second.trace = info →
    ∀ (hfirst : ∃ q ∈ M.Consistent i (M.ownPlay i first.trace), q ∈ mixed.support)
      (hsecond : ∃ q ∈ M.Consistent i (M.ownPlay i second.trace), q ∈ mixed.support),
      FinDist.map (fun policy => policy info)
          (mixed.condOn (M.Consistent i (M.ownPlay i first.trace)) hfirst) =
        FinDist.map (fun policy => policy info)
          (mixed.condOn (M.Consistent i (M.ownPlay i second.trace)) hsecond)

variable {E} in
/-- And the sufficiency, which is the one thing this file proves — now from the
weaker condition the library's own theorem runs on, not from recall. The two
conditioning events are equal as *sets*; the records behind them need not be. -/
theorem actionPosteriorLocal_of_constrainsAlike {M : InformationModel E}
    (hconstrain : M.ConstrainsAlike) (i : ι) : ActionPosteriorLocal M i := by
  intro info mixed first second hfirst hsecond hf hs
  have hsame : M.Consistent i (M.ownPlay i first.trace) =
      M.Consistent i (M.ownPlay i second.trace) :=
    hconstrain i first.trace second.trace (by rw [hfirst, hsecond])
  rw [FinDist.condOn_congr _ hsame hf (by rw [← hsame]; exact hf)]

end GameTheory.Experimental.Phase4
