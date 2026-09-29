/-
# Finite decision information

Finitely many legal histories give finitely many decision sites, finite menus
at each of them, and finitely many outcomes of every legal transition from a
reachable history. The ambient information-state carrier may be infinite:
information values that no history reaches never matter.
-/

import GameTheory.Protocol.DecisionRecall

noncomputable section

namespace GameTheory.Protocol

namespace ExecutionProtocol

variable {ι : Type*} (E : ExecutionProtocol ι)

/-- Every legal transition from a nonterminal history has finitely many
outcomes. Transitions from states that no history reaches are unconstrained. -/
def FiniteTransitions : Prop :=
  ∀ history : E.History, ¬ E.terminal history.state →
    ∀ draw : {joint : ∀ i, Option (E.Action i) // E.Legal history.state joint},
      (E.step history.state draw).support.Finite

variable {E}

/-- Finitely many legal histories bound every reachable transition: distinct
outcomes of one transition extend its history to distinct histories. -/
theorem FiniteTransitions.of_finite_history [Finite E.History] : E.FiniteTransitions := by
  intro history _ draw
  let extend (target : (E.step history.state draw).support) : E.History :=
    history.extend draw.2 target.2
  have injective : Function.Injective extend := fun first second same =>
    Subtype.ext (congrArg ExecutionProtocol.History.state same)
  exact Set.finite_coe_iff.mp (Finite.of_injective extend injective)

/-- A finite state carrier bounds every transition. -/
theorem FiniteTransitions.of_finite_state [Finite E.State] : E.FiniteTransitions :=
  fun _ _ _ => Set.toFinite _

/-- Joint actions presented as a profile, so that one coordinate is replaced
through the profile API. -/
private abbrev jointSignature (E : ExecutionProtocol ι) : GameSignature ι where
  Strategy i := Option (E.Action i)
  Outcome := Unit

/-- The last joint action recorded by a history, if any. -/
private def lastJoint : E.History → Option (∀ i, Option (E.Action i))
  | ⟨_, .start⟩ => none
  | ⟨_, .extend _ joint _ _⟩ => some joint

end ExecutionProtocol

namespace InformationModel

variable {ι : Type*} {E : ExecutionProtocol ι} (M : InformationModel E)

/-- Finitely many legal histories give finitely many decision sites. -/
instance InformationSite.finite [Finite E.History] (who : ι) :
    Finite (M.InformationSite who) := by
  let witness (site : M.InformationSite who) : E.History := site.2.choose.1
  apply Finite.of_injective witness
  intro first second same
  apply Subtype.ext
  exact first.2.choose.2.symm.trans
    ((congrArg (fun history : E.History => M.infoOf who history.trace) same).trans
      second.2.choose.2)

/-- Finitely many legal histories allow only finitely many choices at a
decision site: distinct choices extend one site history to distinct histories. -/
instance InformationSite.finite_choice [Finite E.History] (who : ι)
    (site : M.InformationSite who) : Finite (M.Choice who site.1) := by
  classical
  obtain ⟨history, running, _⟩ := site.2
  obtain ⟨base, baseLegal⟩ := E.exists_legal running
  let joint (choice : M.Choice who site.1) : ∀ player, Option (E.Action player) :=
    Profile.update (sig := ExecutionProtocol.jointSignature E) base who choice.1
  have legal (choice : M.Choice who site.1) : E.Legal history.1.state (joint choice) := by
    apply ExecutionProtocol.legal_of_legalOption running
    intro player
    by_cases same : player = who
    · subst player
      simp only [joint, Profile.update_same]
      apply (M.menu_adequate _ history.1.trace choice.1).mp
      rw [history.2]
      exact choice.2
    · simp only [joint, Profile.update_of_ne _ _ same]
      exact ExecutionProtocol.legalOption_of_legal baseLegal player
  let extend (choice : M.Choice who site.1) : E.History :=
    history.1.extend (legal choice)
      (E.step history.1.state ⟨joint choice, legal choice⟩).support_nonempty.choose_spec
  apply Finite.of_injective extend
  intro first second same
  have joints := congrArg ExecutionProtocol.lastJoint same
  simp only [extend, ExecutionProtocol.History.extend, ExecutionProtocol.lastJoint,
    Option.some.injEq] at joints
  apply Subtype.ext
  simpa only [joint, Profile.update_same] using congrFun joints who

/-- At a nonterminal history every menu is finite when menus at decision sites
are: an active player is at a decision site, and an inactive player has a
single choice. -/
theorem finite_choice_of_nonterminal
    [∀ who (site : M.InformationSite who), Finite (M.Choice who site.1)]
    (history : E.History) (hterm : ¬ E.terminal history.state) (who : ι) :
    Finite (M.Choice who (M.infoOf who history.trace)) := by
  by_cases hactive : E.active history.state who
  · obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history hterm hactive
    rw [← same]
    infer_instance
  · have := M.subsingleton_choice_of_not_active history.trace hactive
    infer_instance

/-- Finitely many players with finite menus at decision sites have finitely
many legal joint actions at every nonterminal history. -/
theorem finite_legalJoint [Finite ι]
    [∀ who (site : M.InformationSite who), Finite (M.Choice who site.1)]
    (history : E.History) (hterm : ¬ E.terminal history.state) :
    Finite {joint : ∀ i, Option (E.Action i) // E.Legal history.state joint} := by
  have (i : ι) := M.finite_choice_of_nonterminal history hterm i
  let draws (joint : {joint : ∀ i, Option (E.Action i) // E.Legal history.state joint}) :
      (i : ι) → M.Choice i (M.infoOf i history.trace) := fun i =>
    ⟨joint.1 i, (M.menu_adequate i history.trace (joint.1 i)).mpr
      (ExecutionProtocol.legalOption_of_legal joint.2 i)⟩
  apply Finite.of_injective draws
  intro first second same
  apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun same i)

end InformationModel

end GameTheory.Protocol
