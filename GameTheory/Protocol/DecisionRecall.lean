/-
# Recall at genuine decision information sets

Perfect recall asks every information state to determine the player's own
past play. Only information states at which the player can act need to: an
observation made while inactive may be shared by histories along which the
player did different things. Decision recall asks exactly this, and adds no
observations or memory to the protocol.

It is enough for everything recall is used for at decisions. A decision
information state is never revisited once the player acts there, decision
fibers are history antichains, each own decision record lists distinct
information states, and the record read off a decision information state is
the actual own play along every history producing it.
-/

import GameTheory.Protocol.BehavioralAssessment
import GameTheory.Protocol.PolicyRandomization

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol

variable {ι : Type*} {E : ExecutionProtocol ι} (M : InformationModel E)

/-- Histories in each genuine decision fiber carry the same own-play record. -/
def DecisionRecall : Prop :=
  ∀ (who : ι) (site : M.InformationSite who) (first second : M.InformationHistory who site.1),
    M.ownPlay who first.1.trace = M.ownPlay who second.1.trace

theorem decisionRecall_of_perfectRecall (hrecall : M.PerfectRecall) : M.DecisionRecall :=
  fun who _ first second => hrecall who _ _ (first.2.trans second.2.symm)

/-- An active player at a nonterminal history is at a decision site. -/
theorem exists_informationSite_of_active (who : ι) (history : E.History)
    (hterm : ¬ E.terminal history.state) (hactive : E.active history.state who) :
    ∃ site : M.InformationSite who, site.1 = M.infoOf who history.trace := by
  obtain ⟨joint, legal⟩ := E.exists_legal hterm
  obtain ⟨action, haction⟩ :=
    (E.legalOption_of_legal legal who).exists_eq_some_of_active (joint who) hactive
  have hmenu : some action ∈ M.menu who (M.infoOf who history.trace) := by
    rw [← haction]
    exact (M.menu_adequate who history.trace (joint who)).mpr (E.legalOption_of_legal legal who)
  exact ⟨M.informationSite who history action hterm hmenu, rfl⟩

/-- Every information state in an own-action record comes from an earlier
history with a strictly shorter record. -/
private theorem exists_shorter_of_mem_actedAt (who : ι) :
    ∀ {state : E.State} (trace : E.Trace state) {info : M.InfoState who},
      info ∈ M.actedAt who trace →
        ∃ earlier : E.History, M.infoOf who earlier.trace = info ∧
          (M.ownPlay who earlier.trace).length < (M.ownPlay who trace).length
  | _, .start, _, hmem => by cases hmem
  | _, .extend prior joint legal realized, info, hmem => by
      cases hchoice : joint who with
      | none =>
          simp only [InfoSignals.actedAt, hchoice] at hmem
          obtain ⟨earlier, hinfo, hshorter⟩ := exists_shorter_of_mem_actedAt who prior hmem
          exact ⟨earlier, hinfo, by simpa only [InfoSignals.ownPlay, hchoice] using hshorter⟩
      | some action =>
          simp only [InfoSignals.actedAt, hchoice, List.mem_cons] at hmem
          rcases hmem with rfl | hmem
          · refine ⟨⟨_, prior⟩, rfl, ?_⟩
            simp only [InfoSignals.ownPlay, hchoice, List.length_cons]
            exact Nat.lt_succ_self _
          · obtain ⟨earlier, hinfo, hshorter⟩ := exists_shorter_of_mem_actedAt who prior hmem
            refine ⟨earlier, hinfo, ?_⟩
            simp only [InfoSignals.ownPlay, hchoice, List.length_cons]
            exact Nat.lt_succ_of_lt hshorter

namespace DecisionRecall

variable {M}

/-- The record read off a decision information state is the own play along
every history producing it. -/
theorem recordAt_eq_ownPlay (hrecall : M.DecisionRecall) (who : ι)
    (site : M.InformationSite who) (history : M.InformationHistory who site.1) :
    M.recordAt who site.1 = M.ownPlay who history.1.trace := by
  have hreached : ∃ other : E.History, M.infoOf who other.trace = site.1 :=
    ⟨history.1, history.2⟩
  rw [InformationModel.recordAt, dite_eq_left hreached]
  exact hrecall who site ⟨_, Classical.choose_spec hreached⟩ history

theorem recordAt_eq_ownPlay_of_active (hrecall : M.DecisionRecall) (who : ι)
    (history : E.History) (hterm : ¬ E.terminal history.state)
    (hactive : E.active history.state who) :
    M.recordAt who (M.infoOf who history.trace) = M.ownPlay who history.trace := by
  obtain ⟨site, hsite⟩ := M.exists_informationSite_of_active who history hterm hactive
  rw [← hsite]
  exact hrecall.recordAt_eq_ownPlay who site ⟨history, hsite.symm⟩

/-- Once a player acts, that decision information state never recurs. -/
theorem infoOf_ne_after_step (hrecall : M.DecisionRecall) (who : ι)
    {history later : E.History} {fuel : ℕ}
    {joint : ∀ player, Option (E.Action player)} (legal : E.Legal history.state joint)
    {next : E.State} (realized : next ∈ (E.step history.state ⟨joint, legal⟩).support)
    (hactive : E.active history.state who)
    (hreach : E.ReachesWithin fuel (history.extend legal realized) later) :
    M.infoOf who later.trace ≠ M.infoOf who history.trace := by
  intro hsame
  obtain ⟨action, haction⟩ :=
    (E.legalOption_of_legal legal who).exists_eq_some_of_active (joint who) hactive
  have hmenu : some action ∈ M.menu who (M.infoOf who history.trace) := by
    rw [← haction]
    exact (M.menu_adequate who history.trace _).mpr (E.legalOption_of_legal legal who)
  let site := M.informationSite who history action legal.1 hmenu
  have hown : M.ownPlay who history.trace = M.ownPlay who later.trace :=
    hrecall who site ⟨history, rfl⟩ ⟨later, hsame⟩
  have hlength := (M.ownPlay_isSuffix_of_reachesWithin who hreach).length_le
  simp only [History.extend, InfoSignals.ownPlay_extend, haction, List.length_cons] at hlength
  rw [← hown] at hlength
  omega

theorem decisionInformationAntichain (hrecall : M.DecisionRecall) :
    M.DecisionInformationAntichain := by
  intro who site first second joint legal next realized fuel hreach
  exact hrecall.infoOf_ne_after_step who legal realized (InformationSite.active M site first)
    hreach (second.2.trans first.2.symm)

/-- Every own-action record lists distinct information states. -/
theorem actsOnceAtEachInfoState (hrecall : M.DecisionRecall) : M.ActsOnceAtEachInfoState := by
  intro who state trace
  induction trace with
  | start => simp [InfoSignals.actedAt]
  | @extend before after prior joint legal realized ih =>
      cases hchoice : joint who with
      | none => simpa only [InfoSignals.actedAt, hchoice] using ih
      | some action =>
          simp only [InfoSignals.actedAt, hchoice, List.nodup_cons]
          refine ⟨?_, ih⟩
          intro hmem
          obtain ⟨earlier, hinfo, hshorter⟩ := M.exists_shorter_of_mem_actedAt who prior hmem
          have hmenu : some action ∈ M.menu who (M.infoOf who prior) := by
            rw [← hchoice]
            exact (M.menu_adequate who prior _).mpr (E.legalOption_of_legal legal who)
          let site := M.informationSite who ⟨before, prior⟩ action legal.1 hmenu
          have hown : M.ownPlay who earlier.trace = M.ownPlay who prior :=
            hrecall who site ⟨earlier, hinfo⟩ ⟨⟨before, prior⟩, rfl⟩
          rw [hown] at hshorter
          exact Nat.lt_irrefl _ hshorter

theorem actsOnceWhereItMatters (hrecall : M.DecisionRecall) : M.ActsOnceWhereItMatters :=
  M.actsOnceWhereItMatters_of_actsOnce hrecall.actsOnceAtEachInfoState

end DecisionRecall

end GameTheory.Protocol.InformationModel
