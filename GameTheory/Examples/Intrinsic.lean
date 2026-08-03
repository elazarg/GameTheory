/-
# Intrinsic-form examples

This leaf recovers the native causal examples from pinned v1
`GameTheory/Languages/Intrinsic/{Examples,Tests}.lean` at commit
`a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.  It deliberately retains only
closed-loop configurations, information, solvability, and causality; evaluation,
probability, temporal execution, and randomization are separate consumers.
-/

import GameTheory.Languages.Intrinsic
import Mathlib.Logic.Equiv.Bool

namespace GameTheory.Examples.Intrinsic

open GameTheory.Languages.Intrinsic

/-- The indiscrete information relation used by the fixtures. -/
private def universalSetoid (α : Type*) : Setoid α where
  r _ _ := True
  iseqv := ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

/-- Two simultaneous Boolean decision agents with no information. -/
def noInformation : Model where
  Agent := Bool
  Nature := Unit
  Decision _ := Bool
  info _ := universalSetoid _

/-- Universal information makes every pure decision rule constant, so every
pure profile has one closed-loop solution at each nature value. -/
theorem noInformation_isSolvable : noInformation.IsSolvable := by
  intro profile nature
  let seed : (agent : Bool) → noInformation.Decision agent :=
    fun agent => (profile agent).act ⟨nature, fun _ => false⟩
  refine ⟨seed, ?_, ?_⟩
  · intro agent
    exact (profile agent).respects _ _ trivial
  · intro decision hfixed
    funext agent
    rw [hfixed agent]
    exact (profile agent).respects _ _ trivial

/-- An explicit exhaustive two-slot schedule; no ordering capability is stored
on the intrinsic model. -/
def noInformationSchedule : noInformation.Schedule 2 :=
  ⟨fun _ => finTwoEquiv⟩

/-- No-information agents satisfy causality for the fixed schedule. -/
theorem noInformation_isCausal :
    Model.IsCausalWith noInformationSchedule := by
  intro left right slot hprefix hagree
  trivial

/-- A two-agent signaling model. `false` is the sender and observes nature;
`true` is the receiver and observes the sender's message. -/
def signaling : Model where
  Agent := Bool
  Nature := Bool
  Decision _ := Bool
  info
    | false =>
        { r := fun left right => left.nature = right.nature
          iseqv := ⟨fun _ => rfl, fun h => h.symm,
            fun hleft hright => hleft.trans hright⟩ }
    | true =>
        { r := fun left right => left.decision false = right.decision false
          iseqv := ⟨fun _ => rfl, fun h => h.symm,
            fun hleft hright => hleft.trans hright⟩ }

/-- Sender information is exactly equality of the nature value. -/
theorem signaling_sender_info_iff
    (left right : signaling.Configuration) :
    (signaling.info false).r left right ↔ left.nature = right.nature := Iff.rfl

/-- Receiver information is exactly equality of the sender's message. -/
theorem signaling_receiver_info_iff
    (left right : signaling.Configuration) :
    (signaling.info true).r left right ↔
      left.decision false = right.decision false := Iff.rfl

/-- A model in which the first scheduled agent observes the later decision. -/
def futureLooking : Model where
  Agent := Bool
  Nature := Unit
  Decision _ := Bool
  info
    | false =>
        { r := fun left right => left.decision true = right.decision true
          iseqv := ⟨fun _ => rfl, fun h => h.symm,
            fun hleft hright => hleft.trans hright⟩ }
    | true => universalSetoid _

private def futureFalse : futureLooking.Configuration :=
  ⟨(), fun _ => false⟩

private def futureTrue : futureLooking.Configuration :=
  ⟨(), fun agent => agent⟩

/-- The same fixed schedule puts the future-observing agent first. -/
def futureLookingSchedule : futureLooking.Schedule 2 :=
  ⟨fun _ => finTwoEquiv⟩

/-- Intrinsic causality rejects information about a later decision before any
temporal execution is introduced. -/
theorem futureLooking_not_causal :
    ¬ Model.IsCausalWith futureLookingSchedule := by
  intro hcausal
  have hinfo := hcausal futureFalse futureTrue (0 : Fin 2)
    (by
      intro earlier hearlier
      rfl)
    (by
      constructor
      · rfl
      · intro earlier hearlier
        omega)
  have hunequal : futureFalse.decision true = futureTrue.decision true := hinfo
  have hne : (false : futureLooking.Decision true) ≠ true := by decide
  exact hne hunequal

end GameTheory.Examples.Intrinsic
