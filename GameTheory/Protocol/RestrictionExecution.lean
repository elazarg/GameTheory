/-
# Execution laws derived from an action restriction

The one-step square determines every behavioral law of an extending profile:
the larger protocol's play from an embedded history is the embedded play of
the smaller one. Behavior at new information values and any equilibrium
property are irrelevant. A horizon bounding the larger protocol bounds the
smaller one, so terminal play corresponds as well.
-/

import GameTheory.Protocol.ActionRestriction
import GameTheory.Protocol.BehavioralTerminal
import GameTheory.Protocol.FiniteHorizon

noncomputable section

namespace GameTheory.Protocol.InformationModel.ActionRestriction

open GameTheory.Math.Probability ExecutionProtocol

variable {ι : Type*} {E T : ExecutionProtocol ι}
  {M : InformationModel E} {N : InformationModel T} (restriction : M.ActionRestriction N)
variable [E.FiniteMovers] [T.FiniteMovers]

/-- An embedded history has exactly the movers of its original. -/
theorem movers_history (original : E.History) :
    T.movers (restriction.history original).state = E.movers original.state := by
  ext who
  rw [ExecutionProtocol.mem_movers, ExecutionProtocol.mem_movers, restriction.active]

theorem joint_law (source : (i : ι) → M.BehavioralPolicy i)
    (target : (i : ι) → N.BehavioralPolicy i)
    (agrees : restriction.ExtendsProfile source target)
    (original : E.History) (running : ¬ E.terminal original.state) :
    finitaryProduct (fun who => target who (N.infoOf who (restriction.history original).trace))
        (T.movers (restriction.history original).state) =
      (finitaryProduct (fun who => source who (M.infoOf who original.trace))
          (E.movers original.state)).map
        (fun draws who => restriction.choiceAt who original (draws who)) := by
  have localLaws := funext (restriction.extends_at_history source target agrees original running)
  rw [localLaws, restriction.movers_history]
  exact (finitaryProduct_map (fun who => source who (M.infoOf who original.trace))
    (fun who => ⇑(restriction.choiceAt who original))
    (M.isPointMass_of_not_mem_movers source original.trace)).symm

/-- Complete behavioral laws follow from the local square. -/
theorem runFrom_law (source : (i : ι) → M.BehavioralPolicy i)
    (target : (i : ι) → N.BehavioralPolicy i)
    (agrees : restriction.ExtendsProfile source target) (fuel : ℕ) (original : E.History) :
    (M.runBehavioralFrom source fuel original).map restriction.history =
      N.runBehavioralFrom target fuel (restriction.history original) := by
  induction fuel generalizing original with
  | zero => exact PMF.pure_map _ _
  | succ fuel induction =>
      by_cases stopped : E.terminal original.state
      · rw [M.runBehavioralFrom_of_terminal source _ stopped,
          N.runBehavioralFrom_of_terminal target _ ((restriction.terminal original).mpr stopped),
          PMF.pure_map]
      · rw [M.runBehavioralFrom_succ_localStep, N.runBehavioralFrom_succ_localStep,
          restriction.joint_law source target agrees original stopped,
          PMF.map_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def, PMF.bind_bind]
        apply bind_congr_on_support _
        intro draws _
        have one := restriction.step original draws
        change (M.localStep original draws).map restriction.history =
          N.localStep (restriction.history original)
            (fun who => restriction.choiceAt who original (draws who)) at one
        rw [← one, PMF.bind_map]
        exact bind_congr_on_support _ fun next _ => induction next

theorem initialized_law (source : (i : ι) → M.BehavioralPolicy i)
    (target : (i : ι) → N.BehavioralPolicy i)
    (agrees : restriction.ExtendsProfile source target) (fuel : ℕ) :
    (M.runBehavioral source fuel).map restriction.history = N.runBehavioral target fuel := by
  simpa only [runBehavioral, restriction.initial] using
    restriction.runFrom_law source target agrees fuel E.initHistory

omit [E.FiniteMovers] [T.FiniteMovers] in
include restriction in
/-- A horizon bounding the larger protocol bounds the smaller one. -/
theorem boundedHorizon {bound : ℕ} (bounded : T.BoundedHorizon bound) : E.BoundedHorizon bound := by
  intro state trace long
  have stopped := bounded (restriction.history ⟨state, trace⟩).state
    (restriction.history ⟨state, trace⟩).trace (by
      rw [show (restriction.history ⟨state, trace⟩).trace.length = trace.length from
        restriction.length ⟨state, trace⟩]
      exact long)
  exact (restriction.terminal ⟨state, trace⟩).mp stopped

/-- Terminal play of an extending profile from an embedded history is the
embedded terminal play of the smaller protocol. -/
theorem terminal_law [Finite T.History] (sourceCertificate : E.WellFoundedHistories)
    (targetCertificate : T.WellFoundedHistories)
    (source : (i : ι) → M.BehavioralPolicy i) (target : (i : ι) → N.BehavioralPolicy i)
    (agrees : restriction.ExtendsProfile source target) (original : E.History) :
    (M.runBehavioralTerminalFrom sourceCertificate source original).map restriction.history =
      N.runBehavioralTerminalFrom targetCertificate target (restriction.history original) := by
  let _ := Fintype.ofFinite T.History
  obtain ⟨bound, -, bounded⟩ := T.exists_pos_boundedHorizon
  rw [M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded sourceCertificate
      (restriction.boundedHorizon bounded),
    N.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded targetCertificate bounded]
  exact restriction.runFrom_law source target agrees bound original

omit [E.FiniteMovers] [T.FiniteMovers] in
/-- A retained belief fiber embeds into the full fiber of the larger protocol,
which may also contain histories that take a new action. -/
def informationHistory (who : ι) (site : M.InformationSite who) :
    M.InformationHistory who site.1 ↪ N.InformationHistory who (restriction.site who site).1 where
  toFun original := ⟨restriction.history original.1,
    (restriction.observed who original.1).trans
      (congrArg (restriction.information who) original.2)⟩
  inj' := by
    intro first second same
    exact Subtype.ext (restriction.history.injective (congrArg Subtype.val same))

omit [E.FiniteMovers] [T.FiniteMovers] in
theorem informationHistory_val (who : ι) (site : M.InformationSite who)
    (original : M.InformationHistory who site.1) :
    (restriction.informationHistory who site original).1 = restriction.history original.1 := rfl

omit [E.FiniteMovers] [T.FiniteMovers] in
/-- A retained site of the larger protocol at a common depth is at that depth
in the smaller protocol too. -/
theorem source_commonDepth (who : ι) (site : M.InformationSite who) (depth : ℕ)
    (clock : InformationSite.CommonDepth N (restriction.site who site) depth) :
    InformationSite.CommonDepth M site depth := by
  intro original
  have target := clock (restriction.informationHistory who site original)
  exact (restriction.length original.1).symm.trans target

omit [E.FiniteMovers] [T.FiniteMovers]

/-- One legal step of the smaller protocol embeds as one step of the larger. -/
theorem reachesWithin_step {start : E.History} {joint : ∀ i, Option (E.Action i)}
    (isLegal : E.Legal start.state joint) {reached : E.State}
    (realized : reached ∈ (E.step start.state ⟨joint, isLegal⟩).support) :
    T.ReachesWithin 1 (restriction.history start)
      (restriction.history (start.extend isLegal realized)) := by
  classical
  let choices (who : ι) : M.Choice who (M.infoOf who start.trace) :=
    ⟨joint who, (M.menu_adequate who start.trace (joint who)).mpr
      (ExecutionProtocol.legalOption_of_legal isLegal who)⟩
  have source : start.extend isLegal realized ∈ (M.localStep start choices).support := by
    rw [localStep, dite_eq_right isLegal.1, PMF.mem_support_bindOnSupport_iff]
    exact ⟨reached, realized, by rw [PMF.support_pure]; rfl⟩
  have image : restriction.history (start.extend isLegal realized) ∈
      ((M.localStep start choices).map restriction.history).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨_, source, rfl⟩
  have running : ¬ T.terminal (restriction.history start).state :=
    fun stopped => isLegal.1 ((restriction.terminal start).mp stopped)
  rw [restriction.step start choices, localStep, dite_eq_right running,
    PMF.mem_support_bindOnSupport_iff] at image
  obtain ⟨next, step, landed⟩ := image
  rw [PMF.support_pure, Set.mem_singleton_iff] at landed
  rw [landed]
  exact .step _ _ step (.refl 0 _)

/-- The embedding of histories preserves bounded reachability. -/
theorem reachesWithin_history {fuel : ℕ} {start final : E.History}
    (reach : E.ReachesWithin fuel start final) :
    T.ReachesWithin fuel (restriction.history start) (restriction.history final) := by
  induction reach with
  | refl fuel history => exact .refl fuel _
  | step joint isLegal realized rest induction =>
      simpa only [Nat.add_comm] using (restriction.reachesWithin_step isLegal realized).trans
        induction

theorem historyReaches_history {start final : E.History} (reach : E.HistoryReaches start final) :
    T.HistoryReaches (restriction.history start) (restriction.history final) :=
  let ⟨fuel, within⟩ := reach
  ⟨fuel, restriction.reachesWithin_history within⟩

/-- Every ancestor of an embedded history is itself embedded. -/
theorem exists_of_historyReaches {ancestor : T.History} {final : E.History}
    (reach : T.HistoryReaches ancestor (restriction.history final)) :
    ∃ start, restriction.history start = ancestor ∧ E.HistoryReaches start final := by
  obtain ⟨fuel, within⟩ := reach
  have shorter : ancestor.trace.length ≤ final.trace.length :=
    by rw [← restriction.length final]; exact within.trace_length_le
  obtain ⟨start, steps, length, reaches⟩ := E.exists_ancestor_of_le final shorter
  exact ⟨start, ReachesWithin.eq_start_of_same_length (restriction.reachesWithin_history reaches)
    within ((restriction.length start).trans length), steps, reaches⟩

/-- The embedding of histories reflects reachability. -/
theorem historyReaches_history_iff {start final : E.History} :
    T.HistoryReaches (restriction.history start) (restriction.history final) ↔
      E.HistoryReaches start final := by
  refine ⟨fun reach => ?_, restriction.historyReaches_history⟩
  obtain ⟨other, same, reaches⟩ := restriction.exists_of_historyReaches reach
  rwa [restriction.history.injective same] at reaches

/-- Play passes through an embedded history exactly when its source play passes
through the original. -/
theorem cone_preimage (start : E.History) :
    restriction.history ⁻¹' {final | T.HistoryReaches (restriction.history start) final} =
      {final | E.HistoryReaches start final} :=
  Set.ext fun _ => restriction.historyReaches_history_iff

/-- No embedded play passes through a history of a retained site that takes a
new action. -/
theorem cone_preimage_eq_empty (who : ι) (site : M.InformationSite who)
    (history : N.InformationHistory who (restriction.site who site).1)
    (outside : history ∉ Set.range (restriction.informationHistory who site)) :
    restriction.history ⁻¹' {final | T.HistoryReaches history.1 final} = ∅ := by
  ext final
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro reach
  obtain ⟨start, same, -⟩ := restriction.exists_of_historyReaches reach
  have observed : M.infoOf who start.trace = site.1 := by
    apply (restriction.information who).injective
    rw [← restriction.observed, same]
    exact history.2
  exact outside ⟨⟨start, observed⟩, Subtype.ext same⟩

/-- Play passes through a retained site exactly when its source play passes
through the original site. -/
theorem passage_preimage (who : ι) (site : M.InformationSite who) :
    restriction.history ⁻¹' {final | ∃ history, N.infoOf who history.trace =
        (restriction.site who site).1 ∧ T.HistoryReaches history final} =
      {final | ∃ history, M.infoOf who history.trace = site.1 ∧
        E.HistoryReaches history final} := by
  ext final
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ancestor, observed, reach⟩
    obtain ⟨start, rfl, reaches⟩ := restriction.exists_of_historyReaches reach
    refine ⟨start, (restriction.information who).injective ?_, reaches⟩
    rw [← restriction.observed]
    exact observed
  · rintro ⟨start, observed, reaches⟩
    refine ⟨restriction.history start, ?_, restriction.historyReaches_history reaches⟩
    rw [restriction.observed, observed]
    rfl


end GameTheory.Protocol.InformationModel.ActionRestriction
