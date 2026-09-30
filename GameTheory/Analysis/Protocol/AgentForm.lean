/-
# The agent normal form of a protocol

An agent chooses one legal action at one information value of one player.
Agents play the protocol with the policies their choices assemble, and the
outcome is terminal play. Independent mixed agent choices induce exactly
ordinary behavioral terminal play whenever no information value is revisited
with a consequential choice. A unilateral agent deviation changes exactly one
local law of the player's behavioral policy.

Primary reference: R. Selten, “Reexamination of the Perfectness Concept for
Equilibrium Points in Extensive Games,” *International Journal of Game
Theory* 4 (1975).
-/

import GameTheory.Core.Form
import GameTheory.Protocol.BehavioralTerminal
import GameTheory.Protocol.PolicyRandomization
import GameTheory.Protocol.Strategic

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type*} {E : ExecutionProtocol ι} (M : InformationModel E)

/-- The agents at the listed information values of each player. -/
abbrev InformationAgent (sites : (who : ι) → Finset (M.InfoState who)) :=
  Σ who, {info // info ∈ sites who}

/-- Agents choose legal actions at their information values; outcomes are
complete histories. -/
abbrev informationAgentSignature (sites : (who : ι) → Finset (M.InfoState who)) :
    GameSignature (M.InformationAgent sites) where
  Strategy agent := M.Choice agent.1 agent.2.1
  Outcome := E.History

/-- Assemble a player's policy from its agents' choices, with a fallback at
unlisted information values. -/
def agentPolicy (sites : (who : ι) → Finset (M.InfoState who))
    (fallback : (who : ι) → M.Policy who)
    (actions : (agent : M.InformationAgent sites) → M.Choice agent.1 agent.2.1)
    (who : ι) : M.Policy who := by
  classical
  exact FiniteAssignment.resolve (fallback who) (sites who) (fun info => actions ⟨who, info⟩)

/-- **The agent normal form.** Each agent chooses a legal action at its
information value, and the outcome is terminal play of the assembled
policies. -/
def informationAgentForm (sites : (who : ι) → Finset (M.InfoState who))
    (fallback : (who : ι) → M.Policy who) (certificate : E.WellFoundedHistories)
    [Fintype ι] : GameForm (M.InformationAgent sites) where
  sig := M.informationAgentSignature sites
  play actions := M.runBehavioralTerminalFrom certificate
    (fun who => (M.agentPolicy sites fallback actions who).toBehavioral) E.initHistory

/-- Assemble behavioral policies from mixed agent laws, with the fallback at
unlisted information values. -/
def agentBehavior (sites : (who : ι) → Finset (M.InfoState who))
    (fallback : (who : ι) → M.Policy who)
    (laws : (agent : M.InformationAgent sites) → PMF (M.Choice agent.1 agent.2.1)) :
    Profile M.behavioralSignature := by
  classical
  exact fun who info =>
    if present : info ∈ sites who then laws ⟨who, ⟨info, present⟩⟩
    else PMF.pure (fallback who info)

@[simp] theorem agentBehavior_at (sites : (who : ι) → Finset (M.InfoState who))
    (fallback : (who : ι) → M.Policy who)
    (laws : (agent : M.InformationAgent sites) → PMF (M.Choice agent.1 agent.2.1))
    (agent : M.InformationAgent sites) :
    M.agentBehavior sites fallback laws agent.1 agent.2.1 = laws agent := by
  simp only [agentBehavior, dite_eq_left agent.2.2]

private theorem pi_sigma [Fintype ι] {Index : ι → Type*} [∀ who, Fintype (Index who)]
    {Value : (Σ who, Index who) → Type*}
    (laws : (agent : Σ who, Index who) → PMF (Value agent)) :
    (independentProduct laws).map (fun actions who info => actions ⟨who, info⟩) =
      independentProduct (fun who => independentProduct (fun info => laws ⟨who, info⟩)) := by
  classical
  have injective : Function.Injective
      (fun (actions : (agent : Σ who, Index who) → Value agent) who info =>
        actions ⟨who, info⟩) := by
    intro first second same
    funext agent
    exact congrFun (congrFun same agent.1) agent.2
  ext actions
  refine (pmf_map_apply_of_injective (independentProduct laws) injective
    (fun agent => actions agent.1 agent.2)).trans ?_
  simp only [independentProduct_apply, Fintype.prod_sigma]

/-- **Agent realization.** When no information value is revisited with a
consequential choice and the listed values cover every nonterminal history
within a horizon bounding play, mixed agent play is behavioral terminal play
of the assembled laws. -/
theorem informationAgentForm_mixed_play [Fintype ι]
    (sites : (who : ι) → Finset (M.InfoState who))
    (fallback : (who : ι) → M.Policy who) (certificate : E.WellFoundedHistories)
    {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (once : M.ActsOnceWhereItMatters) (covered : M.CoversInformationSites sites bound)
    (laws : (agent : M.InformationAgent sites) → PMF (M.Choice agent.1 agent.2.1)) :
    (M.informationAgentForm sites fallback certificate).mixed.play laws =
      M.runBehavioralTerminalFrom certificate (M.agentBehavior sites fallback laws)
        E.initHistory := by
  classical
  let assemble : ((agent : M.InformationAgent sites) → M.Choice agent.1 agent.2.1) →
      Profile M.strategicSignature := fun actions who =>
    FiniteAssignment.resolve (fallback who) (sites who) (fun info => actions ⟨who, info⟩)
  have policyLaw : (independentProduct laws).map assemble = independentProduct (fun who =>
      (M.agentBehavior sites fallback laws who).toMixedWithin M (sites who) (fallback who)) := by
    calc
      _ = ((independentProduct laws).map (fun actions who info => actions ⟨who, info⟩)).map
          (fun plans who => FiniteAssignment.resolve (fallback who) (sites who) (plans who)) := by
            rw [PMF.map_comp]
            rfl
      _ = (independentProduct (fun who => independentProduct (fun info => laws ⟨who, info⟩))).map
          (fun plans who => FiniteAssignment.resolve (fallback who) (sites who) (plans who)) :=
            congrArg
              (PMF.map (fun plans who =>
                FiniteAssignment.resolve (fallback who) (sites who) (plans who)))
              (pi_sigma (Index := fun who => {info // info ∈ sites who})
                (Value := fun agent => M.Choice agent.1 agent.2.1) laws)
      _ = independentProduct (fun who => (independentProduct (fun info => laws ⟨who, info⟩)).map
          (FiniteAssignment.resolve (fallback who) (sites who))) :=
            independentProduct_map (fun who => independentProduct fun info => laws ⟨who, info⟩)
              (fun who => FiniteAssignment.resolve (fallback who) (sites who))
      _ = _ := by
        congr 1
        funext who
        rw [BehavioralPolicy.toMixedWithin_eq_sampleOn, FiniteAssignment.sampleOn]
        congr 1
        congr 1
        funext info
        exact (M.agentBehavior_at sites fallback laws ⟨who, info⟩).symm
  have pure (actions : (agent : M.InformationAgent sites) → M.Choice agent.1 agent.2.1) :
      (M.informationAgentForm sites fallback certificate).play actions =
        M.runFrom (assemble actions) bound E.initHistory := by
    change M.runBehavioralTerminalFrom certificate _ E.initHistory = _
    rw [M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded,
      runBehavioralFrom_toBehavioral]
    rfl
  calc
    _ = (independentProduct laws).bind
        (fun actions => M.runFrom (assemble actions) bound E.initHistory) := by
      refine (GameTheory.GameForm.mixed_play (M.informationAgentForm sites fallback certificate)
        laws).trans ?_
      exact bind_congr_on_support _ fun actions _ => pure actions
    _ = ((independentProduct laws).map assemble).bind
        (fun profile => M.runFrom profile bound E.initHistory) := by rw [PMF.bind_map]; rfl
    _ = M.runMixed (fun who =>
        (M.agentBehavior sites fallback laws who).toMixedWithin M (sites who) (fallback who))
          bound :=
      congrArg (fun distribution => distribution.bind
        (fun profile => M.runFrom profile bound E.initHistory)) policyLaw
    _ = M.runBehavioral (M.agentBehavior sites fallback laws) bound :=
      M.runMixed_toMixedWithin once sites _ fallback bound covered
    _ = _ := (M.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded
      _ E.initHistory).symm

/-- A unilateral agent deviation changes exactly one local law of the
player's behavioral policy. -/
theorem agentBehavior_update [DecidableEq ι] [∀ who, DecidableEq (M.InfoState who)]
    (sites : (who : ι) → Finset (M.InfoState who))
    (fallback : (who : ι) → M.Policy who)
    (laws : (agent : M.InformationAgent sites) → PMF (M.Choice agent.1 agent.2.1))
    (agent : M.InformationAgent sites) (replacement : PMF (M.Choice agent.1 agent.2.1)) :
    M.agentBehavior sites fallback
        (Profile.update (sig := (M.informationAgentSignature sites).mixed) laws agent
          replacement) =
      Profile.update (sig := M.behavioralSignature) (M.agentBehavior sites fallback laws)
        agent.1 ((M.agentBehavior sites fallback laws agent.1).withLaw agent.2.1 replacement) := by
  classical
  funext who info
  by_cases samePlayer : who = agent.1
  · subst who
    rw [Profile.update_same]
    by_cases sameInfo : info = agent.2.1
    · subst info
      rw [M.agentBehavior_at sites fallback _ agent, Profile.update_same,
        BehavioralPolicy.withLaw_self]
    · rw [BehavioralPolicy.withLaw_of_ne _ _ _ sameInfo]
      unfold agentBehavior
      split
      · rename_i present
        apply Profile.update_of_ne
        intro equal
        have same := eq_of_heq (Sigma.mk.inj equal).2
        exact sameInfo (congrArg Subtype.val same)
      · rfl
  · rw [Profile.update_of_ne _ _ samePlayer]
    unfold agentBehavior
    split
    · rename_i present
      apply Profile.update_of_ne
      intro equal
      exact samePlayer (congrArg Sigma.fst equal)
    · rfl

end GameTheory.Protocol.InformationModel
