/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.DeviationSimulation

/-!
# GameTheory.Concepts.Foundations.SerializationObliviousness

Prophecy-freedom for presentations that serialize simultaneous moves.

A compiler that turns simultaneous moves into a sequence must pick an order. An
`ObliviousSerializer` packages such a compiler as a `Sched`-indexed family of
profile realizations `realize : Sched → G.Profile → H.Profile`, together with two
guarantees that hold *for every schedule*:

* `law_eq`: every schedule reproduces the source's observed outcome law;
* `simulate_target_deviation`: every schedule matches every target-side unilateral
  deviation by a source-side one.

Because both guarantees are quantified over the schedule, the observed law is
independent of the serialization order (`observedLaw_schedule_independent`) and a
source equilibrium is realized under *every* schedule
(`source_nash_transports_under_every_schedule`). No serialization order is
distinguished, so a player cannot condition on it — the game-theoretic analogue of
strong linearizability's prohibition on prophecy: the compiled information a player
acts on never encodes the order in which simultaneous moves were resolved.

This is the shape of the obligation owed by any bridge that resolves a
simultaneous frontier one mover at a time; it is intended to be discharged once
per serializer, rather than reproving a distribution equality after the fact.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι Ω : Type} [DecidableEq ι]

/-- A serializer presents each source profile as a target profile, parameterized
by a schedule: a choice of serialization order for the source's simultaneous
moves. The two fields are the prophecy-freedom obligation, stated over *every*
schedule: honest play reproduces the source observed law, and every target-side
unilateral deviation is matched by a source-side one. -/
structure ObliviousSerializer (G H : GameForm ι) (Ω Sched : Type) where
  viewG : OutcomeView G Ω
  viewH : OutcomeView H Ω
  realize : Sched → G.Profile → H.Profile
  law_eq : ∀ (s : Sched) (σ : G.Profile), viewG.law σ = viewH.law (realize s σ)
  simulate_target_deviation :
    ∀ (s : Sched) (σ : G.Profile) (who : ι) (sH : H.Strategy who),
      ∃ sG : G.Strategy who,
        viewG.law (Function.update σ who sG) =
          viewH.law (Function.update (realize s σ) who sH)

namespace ObliviousSerializer

variable {G H : GameForm ι} {Sched : Type}

/-- The one-way deviation simulation induced by a single schedule. -/
def toNashSimulation (O : ObliviousSerializer G H Ω Sched) (s : Sched) :
    NashDeviationSimulation G H Ω :=
  NashDeviationSimulation.ofFunctionalRealization O.viewG O.viewH (O.realize s)
    (O.law_eq s)
    (fun σ who sH => O.simulate_target_deviation s σ who sH)

/-- Prophecy-freedom, explicit form: the compiled observed outcome law does not
depend on the serialization schedule. -/
theorem observedLaw_schedule_independent
    (O : ObliviousSerializer G H Ω Sched) (s s' : Sched) (σ : G.Profile) :
    O.viewH.law (O.realize s σ) = O.viewH.law (O.realize s' σ) :=
  (O.law_eq s σ).symm.trans (O.law_eq s' σ)

/-- Prophecy-freedom for equilibrium: a source Nash equilibrium is realized as a
target Nash equilibrium under *every* schedule. No serialization order is
distinguished, so a player cannot gain by conditioning on the order. -/
theorem source_nash_transports_under_every_schedule
    (O : ObliviousSerializer G H Ω Sched)
    {σ : G.Profile}
    {prefΩ : ι → PMF Ω → PMF Ω → Prop}
    (hN : G.IsNashFor (observedPref O.viewG prefΩ) σ)
    (s : Sched) :
    H.IsNashFor (observedPref O.viewH prefΩ) (O.realize s σ) :=
  (O.toNashSimulation s).target_nash_of_source_nash rfl hN

/-- A realization that ignores the schedule is trivially prophecy-free: this is
the degenerate corner of the obligation, and the constructor a bridge uses when
its target presentation does not serialize simultaneous moves at all. -/
def ofScheduleIndependent
    (viewG : OutcomeView G Ω) (viewH : OutcomeView H Ω)
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ σ, viewG.law σ = viewH.law (realize σ))
    (simulate_target_deviation :
      ∀ (σ : G.Profile) (who : ι) (sH : H.Strategy who),
        ∃ sG : G.Strategy who,
          viewG.law (Function.update σ who sG) =
            viewH.law (Function.update (realize σ) who sH)) :
    ObliviousSerializer G H Ω Sched where
  viewG := viewG
  viewH := viewH
  realize := fun _ => realize
  law_eq := fun _ => law_eq
  simulate_target_deviation := fun _ => simulate_target_deviation

end ObliviousSerializer

namespace SerializationObliviousnessExamples

open DeviationSimulationExamples

/-- A target presentation whose outcome records the serialization order alongside
the Boolean value: strategies and outcomes are `(value, order)` pairs. -/
noncomputable def orderTracedForm : GameForm Unit where
  Strategy := fun _ => Bool × Bool
  Outcome := Bool × Bool
  outcomeKernel := fun σ => PMF.pure (σ ())

/-- The observation projects to the Boolean value and discards the recorded
order. -/
def orderTracedView : OutcomeView orderTracedForm Bool where
  observe := Prod.fst

/-- A two-schedule serializer that bakes the schedule bit into the compiled
outcome. Because the view discards it, the induced observed law is the same under
both orders: the order lives in the state but not in what any player observes. -/
noncomputable def boolOrderSerializer :
    ObliviousSerializer boolOutcomeForm orderTracedForm Bool Bool where
  viewG := boolOutcomeView
  viewH := orderTracedView
  realize := fun s σ => fun _ => (σ (), s)
  law_eq := by
    intro s σ
    simp [OutcomeView.law, boolOutcomeView, orderTracedView,
      boolOutcomeForm, orderTracedForm, PMF.pure_map]
  simulate_target_deviation := by
    intro s σ who sH
    cases who
    refine ⟨sH.1, ?_⟩
    simp [OutcomeView.law, boolOutcomeView, orderTracedView,
      boolOutcomeForm, orderTracedForm, PMF.pure_map, Function.update_self]

/-- The compiled observed law is identical under both serialization orders. -/
example (σ : boolOutcomeForm.Profile) :
    orderTracedView.law (boolOrderSerializer.realize true σ) =
      orderTracedView.law (boolOrderSerializer.realize false σ) :=
  boolOrderSerializer.observedLaw_schedule_independent true false σ

/-- A source equilibrium is realized under both serialization orders. -/
example {σ : boolOutcomeForm.Profile}
    {prefΩ : Unit → PMF Bool → PMF Bool → Prop}
    (hN : boolOutcomeForm.IsNashFor
      (observedPref boolOrderSerializer.viewG prefΩ) σ)
    (s : Bool) :
    orderTracedForm.IsNashFor
      (observedPref boolOrderSerializer.viewH prefΩ) (boolOrderSerializer.realize s σ) :=
  boolOrderSerializer.source_nash_transports_under_every_schedule hN s

end SerializationObliviousnessExamples

end GameForm

end GameTheory
