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

end GameTheory.Protocol.InformationModel.ActionRestriction
