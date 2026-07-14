/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Transport.Corners

/-!
# Serialization-oblivious realizations as index-quantified transports

A compiler that turns simultaneous moves into a sequence must pick an order. The
obligation it owes — that no player can condition on the chosen order — is not a
new structure but a *quantifier*: an index type `I` of serialization orders and a
family of realizations `T : I → Realization G H VG VH` (or `I → Transport …` when
backtranslation is needed) sharing one source, whose guarantees are uniform in
`i : I`.

Two facts follow for every such family:

* **Observed-law index-independence** (`claw_index_independent`): if a single
  source `μG` is related to `μH i` under `T i` and to `μH j` under `T j`, then
  every unit sees the same observed law, `VH.claw u (μH i) = VH.claw u (μH j)`.
  No unit's observed law depends on the serialization index. This is a
  *strong-linearizability analogue*, not the exact statement: strong
  linearizability proper is defined over execution histories with a
  prefix-preserving linearization map (Attiya–Enea, DISC 2019), and a `GameForm`
  has neither histories nor prefixes.
* **Transport under every index** (`transport_under_every_index`): a source
  deviation-family equilibrium transports to a target one at *every* index.

The degenerate corner is a realization that ignores the index entirely
(`Transport.ofIndexIndependent`) — the constructor a bridge uses when its target
presentation does not serialize simultaneous moves at all.

`boolOrderSerializer` is a finite positive instance: a two-order serializer that
bakes the order bit into the compiled *state* while the view discards it, so the
observed law is order-independent — order in state, not in view.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type}

/-- **Observed-law index-independence.** For a family of realizations sharing one
source `μG`, every unit's observed law is the same at every index: no unit's
observed law depends on the serialization index.

This is a strong-linearizability *analogue*. Strong linearizability proper is
defined over execution histories with a prefix-preserving linearization map
(Attiya–Enea, DISC 2019); a `GameForm` carries neither histories nor prefixes, so
what survives here is the order-independence of each unit's observed outcome law. -/
theorem claw_index_independent {G H : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {I : Type} (R : I → Realization G H VG VH)
    {μG : PMF G.Profile} {μH : I → PMF H.Profile}
    (hrel : ∀ i, (R i).rel μG (μH i)) (i j : I) (u : U) :
    VH.claw u (μH i) = VH.claw u (μH j) := by
  rw [← (R i).law_eq (hrel i) u, (R j).law_eq (hrel j) u]

/-- **Transport under every index.** A source deviation-family equilibrium under
observed preferences is realized as a target one at every serialization index, by
per-index application of the generic transfer theorem. -/
theorem transport_under_every_index {G H : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    {I : Type} (T : I → Transport G H VG VH ΔG ΔH)
    {μG : PMF G.Profile} {μH : I → PMF H.Profile}
    (hrel : ∀ i, (T i).rel μG (μH i))
    {prefΩ : ∀ u, PMF (Ω u) → PMF (Ω u) → Prop}
    (hEq : G.IsDeviationEqFor (observedPref VG prefΩ) μG ΔG)
    (i : I) :
    H.IsDeviationEqFor (observedPref VH prefΩ) (μH i) ΔH :=
  (T i).target_eq_of_source_eq (hrel i) hEq

/-- The **index-independent** family: a single transport used at every index. Its
observed law is trivially order-independent, being one realization; this is the
corner a bridge uses when its target presentation does not serialize at all. -/
def Transport.ofIndexIndependent {G H : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (T : Transport G H VG VH ΔG ΔH) (I : Type) : I → Transport G H VG VH ΔG ΔH :=
  fun _ => T

namespace ObliviousExamples

open TransportExamples

/-- A target presentation whose outcome records the serialization order alongside
the Boolean value: strategies and outcomes are `(value, order)` pairs. -/
noncomputable def orderTracedForm : GameForm Unit where
  Strategy := fun _ => Bool × Bool
  Outcome := Bool × Bool
  outcomeKernel := fun σ => PMF.pure (σ ())

/-- The observation projects to the Boolean value and discards the recorded
order. -/
noncomputable def orderTracedView : ViewFamily orderTracedForm Unit (fun _ => Bool) :=
  ViewFamily.const Prod.fst

/-- A two-order serializer, presented as a `Bool`-indexed family of transports
that bakes the order bit into the compiled state. Because the view discards it,
the induced observed law is the same under both orders: the order lives in the
state but not in what any player observes. -/
noncomputable def boolOrderSerializer (s : Bool) :
    Transport boolOutcomeForm orderTracedForm boolOutcomeView orderTracedView
      boolOutcomeForm.constantDeviationProfileFamily
      orderTracedForm.constantDeviationProfileFamily :=
  Transport.ofConstantProfileMap boolOutcomeView orderTracedView
    (fun σ _ => (σ (), s))
    (by
      intro i σ
      simp [ViewFamily.plaw, ViewFamily.const, boolOutcomeView, orderTracedView,
        boolOutcomeForm, orderTracedForm, PMF.pure_map])
    (by
      intro who sH
      cases who
      refine ⟨sH.1, ?_⟩
      intro σ
      simp [ViewFamily.plaw, ViewFamily.const, boolOutcomeView, orderTracedView,
        boolOutcomeForm, orderTracedForm, PMF.pure_map, Function.update_self])

/-- The order-`s` trace of a source distribution: the compiled target distribution
that records the serialization order `s` in state alongside the Boolean value. -/
noncomputable def boolOrderTrace (s : Bool) (μG : PMF boolOutcomeForm.Profile) :
    PMF orderTracedForm.Profile :=
  PMF.map (fun σ (_ : Unit) => (σ (), s)) μG

/-- Honest play under `boolOrderSerializer` at order `s` realizes each source
distribution as its order-`s` trace. -/
theorem boolOrderSerializer_rel (s : Bool) (μG : PMF boolOutcomeForm.Profile) :
    (boolOrderSerializer s).rel μG (boolOrderTrace s μG) :=
  rfl

/-- The compiled observed law is identical under both serialization orders. -/
example (μG : PMF boolOutcomeForm.Profile) (u : Unit) :
    orderTracedView.claw u (boolOrderTrace true μG) =
      orderTracedView.claw u (boolOrderTrace false μG) :=
  claw_index_independent (fun s => (boolOrderSerializer s).toRealization)
    (μH := fun s => boolOrderTrace s μG)
    (fun s => boolOrderSerializer_rel s μG) true false u

/-- A source coarse-correlated equilibrium is realized under both serialization
orders. -/
example (μG : PMF boolOutcomeForm.Profile)
    {prefΩ : Unit → PMF Bool → PMF Bool → Prop}
    (hCCE : boolOutcomeForm.IsCoarseCorrelatedEqFor
      (observedPref boolOutcomeView prefΩ) μG)
    (s : Bool) :
    orderTracedForm.IsCoarseCorrelatedEqFor (observedPref orderTracedView prefΩ)
      (boolOrderTrace s μG) :=
  transport_under_every_index boolOrderSerializer
    (μH := fun s => boolOrderTrace s μG)
    (fun s => boolOrderSerializer_rel s μG) hCCE s

end ObliviousExamples

end GameForm

end GameTheory
