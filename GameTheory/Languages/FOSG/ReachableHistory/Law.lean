/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Languages.Bridges.FOSG.ObsModelCore
import GameTheory.Languages.FOSG.Compile
import GameTheory.Languages.FOSG.Execution
import GameTheory.Concepts.Foundations.DeviationSimulation
import GameTheory.Theorems.Kuhn.BehavioralToMixedCore
import GameTheory.Theorems.Kuhn.MixedToBehavioralCore
import GameTheory.Languages.FOSG.ReachableHistory.ObsModelFacts

namespace GameTheory

namespace FOSG

namespace Kuhn

open ObsModelCoreBridge

attribute [local instance] Fintype.ofFinite

open scoped BigOperators

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
variable (G : FOSG ι W Act PrivObs PubObs)

open Classical in
/-- If a pure-run trace weight is insensitive to player `i`'s action at the
current projected reachable information state, then reweighting the
reachable-history behavioral-to-mixed product law by that trace weight leaves
the marginal distribution at the projected information state equal to the
original behavioral law. -/
theorem reachableHistoryBehavioralToMixedStrategy_factorAt_of_ignores
    [Fintype ι] [Fintype G.History] [∀ j, Fintype (Option (Act j))]
    (hLeg : G.LegalObservable) (i : ι)
    (β : G.ReachableLegalBehavioralStrategy i)
    (n : Nat) (ss : List G.History)
    (π₀ : (toReachableHistoryObsModelCore G hLeg).PureProfile)
    (hign :
      Math.PMFProduct.Ignores
        (A := fun s : G.ReachableInfoState i => ReachableInfoLegalMove G i s)
        ((toReachableHistoryObsModelCore G hLeg).projectStates i ss)
        (fun πᵢ : (toReachableHistoryObsModelCore G hLeg).LocalStrategy i =>
          Math.ParameterizedChain.pureRun
            ((toReachableHistoryObsModelCore G hLeg).pureStep)
            (toReachableHistoryObsModelCore G hLeg).init n
            (Function.update π₀ i πᵢ) ss)) :
    Math.ProbabilityMassFunction.pushforward
        (Math.ProbabilityMassFunction.reweightPMF
          (reachableHistoryBehavioralToMixedStrategy (G := G) hLeg i β)
          (fun πᵢ : (toReachableHistoryObsModelCore G hLeg).LocalStrategy i =>
            Math.ParameterizedChain.pureRun
              ((toReachableHistoryObsModelCore G hLeg).pureStep)
              (toReachableHistoryObsModelCore G hLeg).init n
              (Function.update π₀ i πᵢ) ss))
        (fun πᵢ => πᵢ ((toReachableHistoryObsModelCore G hLeg).projectStates i ss)) =
      liftReachableHistoryBehavioralStrategy (G := G) hLeg i β
        ((toReachableHistoryObsModelCore G hLeg).projectStates i ss) := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  letI : Fintype (O.InfoState i) :=
    ReachableHistoryNative.reachableHistoryInfoStateFintype (G := G) hLeg i
  letI : ∀ s : G.ReachableInfoState i, Fintype (ReachableInfoLegalMove G i s) :=
    fun _ => by
      dsimp [ReachableInfoLegalMove]
      infer_instance
  have hCtop :
      (∑ πᵢ : O.LocalStrategy i,
        reachableHistoryBehavioralToMixedStrategy (G := G) hLeg i β πᵢ *
          Math.ParameterizedChain.pureRun O.pureStep O.init n
            (Function.update π₀ i πᵢ) ss) ≠ ⊤ := by
    exact Math.ProbabilityMassFunction.sum_mul_pmf_ne_top
      (reachableHistoryBehavioralToMixedStrategy (G := G) hLeg i β)
      (fun πᵢ : O.LocalStrategy i =>
        Math.ParameterizedChain.pureRun O.pureStep O.init n
          (Function.update π₀ i πᵢ) ss)
      (fun πᵢ => PMF.coe_le_one _ ss)
  change Math.ProbabilityMassFunction.pushforward
      (Math.ProbabilityMassFunction.reweightPMF
        (Math.PMFProduct.pmfPi (liftReachableHistoryBehavioralStrategy (G := G) hLeg i β))
        (fun πᵢ : O.LocalStrategy i =>
          Math.ParameterizedChain.pureRun O.pureStep O.init n
            (Function.update π₀ i πᵢ) ss))
      (fun s => s (O.projectStates i ss)) =
    liftReachableHistoryBehavioralStrategy (G := G) hLeg i β (O.projectStates i ss)
  exact Math.PMFProduct.reweightPMF_pmfPi_push_coord_of_ignores'
    (A := fun s : G.ReachableInfoState i => ReachableInfoLegalMove G i s)
    (σ := liftReachableHistoryBehavioralStrategy (G := G) hLeg i β)
    (j := (O.projectStates i ss))
    (w := fun πᵢ : O.LocalStrategy i =>
      Math.ParameterizedChain.pureRun O.pureStep O.init n
        (Function.update π₀ i πᵢ) ss)
    hign hCtop

/-- Local posterior for the constructive B→M strategy on a supported
reachable-history trace. -/
theorem reachableHistoryBehavioralToMixedStrategy_factorAt
    [Fintype ι] [Fintype G.History] [∀ j, Fintype (Option (Act j))]
    (hLeg : G.LegalObservable) (i : ι)
    (β : G.ReachableLegalBehavioralStrategy i)
    (n : Nat) (ss : List G.History)
    (π₀ : (toReachableHistoryObsModelCore G hLeg).PureProfile)
    (hreach :
      Math.ParameterizedChain.pureRun
        ((toReachableHistoryObsModelCore G hLeg).pureStep)
        (toReachableHistoryObsModelCore G hLeg).init n π₀ ss ≠ 0) :
    Math.ProbabilityMassFunction.pushforward
        (Math.ProbabilityMassFunction.reweightPMF
          (reachableHistoryBehavioralToMixedStrategy (G := G) hLeg i β)
          (fun πᵢ : (toReachableHistoryObsModelCore G hLeg).LocalStrategy i =>
            Math.ParameterizedChain.pureRun
              ((toReachableHistoryObsModelCore G hLeg).pureStep)
              (toReachableHistoryObsModelCore G hLeg).init n
              (Function.update π₀ i πᵢ) ss))
        (fun πᵢ => πᵢ ((toReachableHistoryObsModelCore G hLeg).projectStates i ss)) =
      liftReachableHistoryBehavioralStrategy (G := G) hLeg i β
        ((toReachableHistoryObsModelCore G hLeg).projectStates i ss) := by
  exact reachableHistoryBehavioralToMixedStrategy_factorAt_of_ignores
    (G := G) hLeg i β n ss π₀
    (reachableHistory_current_coord_ignores_of_reachable
      (G := G) hLeg hreach i)

/-- Lift a reachable FOSG pure profile into the reachable-history Kuhn model. -/
noncomputable def liftReachableHistoryPureProfile
    (hLeg : G.LegalObservable)
    (π : _root_.GameTheory.FOSG.ReachableLegalPureProfile G) :
    (toReachableHistoryObsModelCore G hLeg).PureProfile :=
  fun i => liftReachableHistoryPureStrategy (G := G) hLeg i (π i)

/-- Native final-history law induced by a reachable pure profile. -/
noncomputable def reachableHistoryOutcomeDistPureProfile
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) (k : Nat)
    (π : _root_.GameTheory.FOSG.ReachableLegalPureProfile G) :
    PMF G.History :=
  reachableHistoryOutcomeDistPure (G := G) hLeg k
    (liftReachableHistoryPureProfile (G := G) hLeg π)

/-- Lift a reachable independent mixed profile into the reachable-history Kuhn
model. -/
noncomputable def liftReachableHistoryMixedProfile
    (hLeg : G.LegalObservable)
    (μ : ReachableMixedProfile (G := G)) :
    ∀ i, PMF ((toReachableHistoryObsModelCore G hLeg).LocalStrategy i) :=
  fun i =>
    Math.ProbabilityMassFunction.pushforward (μ i)
      (liftReachableHistoryPureStrategy (G := G) hLeg i)

theorem liftReachableHistoryMixedProfile_joint
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (μ : ReachableMixedProfile (G := G)) :
    Math.PMFProduct.pmfPi (liftReachableHistoryMixedProfile (G := G) hLeg μ) =
      Math.ProbabilityMassFunction.pushforward
        (reachableMixedProfileJoint (G := G) μ)
        (liftReachableHistoryPureProfile (G := G) hLeg) := by
  classical
  rw [reachableMixedProfileJoint]
  change Math.PMFProduct.pmfPi
      (fun i => Math.ProbabilityMassFunction.pushforward (μ i)
        (liftReachableHistoryPureStrategy (G := G) hLeg i)) =
    Math.ProbabilityMassFunction.pushforward (Math.PMFProduct.pmfPi μ)
      (fun π => fun i => liftReachableHistoryPureStrategy (G := G) hLeg i (π i))
  exact (Math.PMFProduct.pmfPi_push_coordwise μ
    (fun i => liftReachableHistoryPureStrategy (G := G) hLeg i)).symm

@[simp] theorem reachableHistoryOutcomeDistPure_liftReachableHistoryPureProfile
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) (k : Nat)
    (π : _root_.GameTheory.FOSG.ReachableLegalPureProfile G) :
    reachableHistoryOutcomeDistPure (G := G) hLeg k
        (liftReachableHistoryPureProfile (G := G) hLeg π) =
      reachableHistoryOutcomeDistPureProfile (G := G) hLeg k π := by
  rfl

theorem reachableHistoryPureStepDist_eq_runDistFrom_one
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    [DecidablePred G.terminal]
    (hLeg : G.LegalObservable)
    (π : _root_.GameTheory.FOSG.ReachableLegalPureProfile G)
    (ss : List G.History) :
    let O := toReachableHistoryObsModelCore G hLeg
    O.stepDist (O.pureToBehavioral (liftReachableHistoryPureProfile (G := G) hLeg π)) ss =
      History.runDistFrom G (G.legalPureToBehavioral π.extend) 1 (O.lastState ss) := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  let h : G.History := O.lastState ss
  let aStep : ∀ i, ReachableInfoLegalMove G i (G.reachableInfoStateOfHistory i h) :=
    O.castJointAction ss
      (fun i => liftReachableHistoryPureProfile (G := G) hLeg π i (O.projectStates i ss))
  let raw : JointAction Act := fun i => (aStep i).1
  have hraw_of_not_terminal :
      ¬ G.terminal h.lastState → G.legal h.lastState raw := by
    intro hterm
    rw [G.legal_iff_forall]
    refine ⟨hterm, ?_⟩
    intro i
    have haiInfo :
        raw i ∈ G.availableMovesAtInfoState i
          (G.reachableInfoStateOfHistory i h).1 := (aStep i).2
    have hai : raw i ∈ G.availableMoves h i := by
      have hEq := G.availableMovesAtInfoState_eq_of_history hLeg i h
      exact hEq ▸ haiInfo
    simpa [FOSG.mem_availableMoves_iff, raw] using hai
  have hstep :
      O.stepDist (O.pureToBehavioral
          (liftReachableHistoryPureProfile (G := G) hLeg π)) ss =
        O.step h aStep := by
    simp [O, h, aStep, ObsModelCore.stepDist, ObsModelCore.jointActionDist,
      ObsModelCore.pureToBehavioral, Math.PMFProduct.pmfPi_pure]
  change O.stepDist (O.pureToBehavioral
      (liftReachableHistoryPureProfile (G := G) hLeg π)) ss =
    History.runDistFrom G (G.legalPureToBehavioral π.extend) 1 h
  rw [hstep]
  by_cases hterm : G.terminal h.lastState
  · rw [History.runDistFrom_succ_terminal
      (G := G) (σ := G.legalPureToBehavioral π.extend) (n := 0) (h := h) hterm]
    change (toReachableHistoryObsModelCore G hLeg).machine.step h aStep = PMF.pure h
    dsimp [toReachableHistoryObsModelCore]
    rw [dif_pos hterm]
  · have hraw : G.legal h.lastState raw := hraw_of_not_terminal hterm
    have hjoint :
        G.jointActionDist (G.legalPureToBehavioral π.extend) h = PMF.pure raw := by
      unfold FOSG.jointActionDist
      rw [show
          (fun i => (G.legalPureToBehavioral π.extend).toProfile i (h.playerView i)) =
            fun i => PMF.pure (raw i) by
        funext i
        change PMF.pure (π.extend.toProfile i (h.playerView i)) =
          PMF.pure (raw i)
        congr
        rw [show raw i = π.toProfile i (G.reachableInfoStateOfHistory i h) by
          dsimp [raw, aStep]
          rw [reachableHistory_castJointAction_val (G := G) hLeg ss
            (fun i => liftReachableHistoryPureProfile (G := G) hLeg π i
              ((toReachableHistoryObsModelCore G hLeg).projectStates i ss)) i]
          rw [reachableHistory_projectStates_eq_last (G := G) hLeg i ss]
          rfl]
        change (π.toProfile i).extend (h.playerView i) =
          π.toProfile i (G.reachableInfoStateOfHistory i h)
        exact _root_.GameTheory.FOSG.ReachablePureStrategy.extend_apply_history
          (G := G) (i := i) (σ := π.toProfile i) h]
      exact Math.PMFProduct.pmfPi_pure raw
    have hlegalActionLaw :
        G.legalActionLaw (G.legalPureToBehavioral π.extend) h hterm =
          PMF.pure ⟨raw, hraw⟩ := by
      ext a
      rw [G.legalActionLaw_apply]
      rw [hjoint]
      by_cases ha : a = ⟨raw, hraw⟩
      · subst a
        simp
      · have hval : a.1 ≠ raw := by
          intro hval
          exact ha (Subtype.ext hval)
        simp [PMF.pure_apply, hval, ha]
    rw [History.runDistFrom_succ_nonterminal
      (G := G) (σ := G.legalPureToBehavioral π.extend) (n := 0) (h := h) hterm]
    rw [hlegalActionLaw, PMF.pure_bind]
    simp only [History.runDistFrom_zero]
    change (toReachableHistoryObsModelCore G hLeg).machine.step h aStep =
      (G.transition h.lastState ⟨raw, hraw⟩).bind
        (fun dst => PMF.pure (h.extendByOutcome ⟨raw, hraw⟩ dst))
    dsimp [toReachableHistoryObsModelCore]
    rw [dif_neg hterm]
    simp only [PMF.map]
    congr 1

theorem reachableHistoryOutcomeDistPureProfile_eq_runDist
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    [DecidablePred G.terminal]
    (hLeg : G.LegalObservable) (k : Nat)
    (π : _root_.GameTheory.FOSG.ReachableLegalPureProfile G) :
    reachableHistoryOutcomeDistPureProfile (G := G) hLeg k π =
      G.runDist k (G.legalPureToBehavioral π.extend) := by
  classical
  induction k with
  | zero =>
      simp [reachableHistoryOutcomeDistPureProfile, reachableHistoryOutcomeDistPure,
        FOSG.runDist, ObsModelCore.runDistPure, ObsModelCore.runDist,
        ObsModelCore.lastState, toReachableHistoryObsModelCore]
  | succ k ih =>
      let O := toReachableHistoryObsModelCore G hLeg
      let β := O.pureToBehavioral (liftReachableHistoryPureProfile (G := G) hLeg π)
      let σ := G.legalPureToBehavioral π.extend
      change (O.runDist (k + 1) β).bind (fun ss => PMF.pure (O.lastState ss)) =
        History.runDistFrom G σ (k + 1) (History.nil G)
      rw [← History.runDistFrom_bind_runDistFrom
        (G := G) σ k 1 (History.nil G)]
      have ih' :
          (O.runDist k β).bind (fun ss => PMF.pure (O.lastState ss)) =
            History.runDistFrom G σ k (History.nil G) := by
        change ((O.runDistPure k (liftReachableHistoryPureProfile (G := G) hLeg π)).bind
            fun ss => PMF.pure (O.lastState ss)) =
          History.runDistFrom G σ k (History.nil G)
        exact ih
      rw [← ih']
      simp only [ObsModelCore.runDist, Math.TraceRun.traceRun]
      rw [PMF.bind_bind, PMF.bind_bind]
      congr 1
      funext ss
      rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_map]
      conv_lhs =>
        arg 2
        ext t
        simp [Function.comp_def, ObsModelCore.lastState_append_singleton]
      rw [reachableHistoryPureStepDist_eq_runDistFrom_one
        (G := G) hLeg π ss]
      simp [O, σ]

/-- Legal fallback for reachable information states, used only at states not
reached by any pure profile in the core M→B construction. -/
noncomputable def reachableLegalFallbackBehavioral
    (hLeg : G.LegalObservable) :
    (toReachableHistoryObsModelCore G hLeg).BehavioralProfile := by
  classical
  exact fun i v =>
    PMF.pure (reachableInfoLegalMoveDefault G i v)

/-- Erase legal-move subtypes from a legal-core reachable behavioral profile. -/
noncomputable def eraseReachableHistoryBehavioral
    (hLeg : G.LegalObservable)
    (β : (toReachableHistoryObsModelCore G hLeg).BehavioralProfile) :
    G.ReachableBehavioralProfile :=
  fun i s => PMF.map (fun a : ReachableInfoLegalMove G i s => a.1) (β i s)

theorem reachableHistoryBehavioralJointActionDist_map_val
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (βcore : (toReachableHistoryObsModelCore G hLeg).BehavioralProfile)
    (β : G.ReachableLegalBehavioralProfile)
    (hβ : β.toProfile = eraseReachableHistoryBehavioral (G := G) hLeg βcore)
    (ss : List G.History) :
    let O := toReachableHistoryObsModelCore G hLeg
    let h : G.History := O.lastState ss
    Math.ProbabilityMassFunction.pushforward
        (O.jointActionDist βcore ss)
        (fun a : ∀ i, ReachableInfoLegalMove G i (O.currentObs i (O.projectStates i ss)) =>
          fun i => (a i).1) =
      G.jointActionDist β.extend h := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  let h : G.History := O.lastState ss
  have hmarg :
      ∀ i,
        Math.ProbabilityMassFunction.pushforward
            (βcore i (O.projectStates i ss))
            (fun a : ReachableInfoLegalMove G i (O.projectStates i ss) => a.1) =
          β.extend.toProfile i (h.playerView i) := by
    intro i
    calc
      Math.ProbabilityMassFunction.pushforward
          (βcore i (O.projectStates i ss))
          (fun a : ReachableInfoLegalMove G i (O.projectStates i ss) => a.1)
        = Math.ProbabilityMassFunction.pushforward
            (βcore i (G.reachableInfoStateOfHistory i h))
            (fun a : ReachableInfoLegalMove G i
                (G.reachableInfoStateOfHistory i h) => a.1) := by
            rw [reachableHistory_projectStates_eq_last (G := G) hLeg i ss]
      _ = (eraseReachableHistoryBehavioral (G := G) hLeg βcore i)
            (G.reachableInfoStateOfHistory i h) := rfl
      _ = β.toProfile i (G.reachableInfoStateOfHistory i h) := by
            rw [← congrFun hβ i]
      _ = β.extend.toProfile i (h.playerView i) := by
            symm
            exact _root_.GameTheory.FOSG.ReachableBehavioralStrategy.extend_apply_history
              (G := G) (i := i) (σ := β.toProfile i) h
  change Math.ProbabilityMassFunction.pushforward
      (Math.PMFProduct.pmfPi (fun i => βcore i (O.projectStates i ss)))
      (fun a => fun i => (a i).1) =
    Math.PMFProduct.pmfPi (fun i => β.extend.toProfile i (h.playerView i))
  rw [Math.PMFProduct.pmfPi_push_coordwise]
  congr
  funext i
  exact hmarg i

theorem reachableHistoryBehavioralStepDist_eq_runDistFrom_one
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    [DecidablePred G.terminal]
    (hLeg : G.LegalObservable)
    (βcore : (toReachableHistoryObsModelCore G hLeg).BehavioralProfile)
    (β : G.ReachableLegalBehavioralProfile)
    (hβ : β.toProfile = eraseReachableHistoryBehavioral (G := G) hLeg βcore)
    (ss : List G.History) :
    let O := toReachableHistoryObsModelCore G hLeg
    O.stepDist βcore ss =
      History.runDistFrom G β.extend 1 (O.lastState ss) := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  let h : G.History := O.lastState ss
  let rawOf :
      (∀ i, ReachableInfoLegalMove G i (O.currentObs i (O.projectStates i ss))) →
        JointAction Act :=
    fun a i => (a i).1
  let runRaw : JointAction Act → PMF G.History := fun raw =>
    if hraw : G.legal h.lastState raw then
      (G.transition h.lastState ⟨raw, hraw⟩).bind
        (fun dst => PMF.pure (h.extendByOutcome ⟨raw, hraw⟩ dst))
    else
      PMF.pure h
  change O.stepDist βcore ss = History.runDistFrom G β.extend 1 h
  by_cases hterm : G.terminal h.lastState
  · rw [History.runDistFrom_succ_terminal
      (G := G) (σ := β.extend) (n := 0) (h := h) hterm]
    change (O.jointActionDist βcore ss).bind
        (fun a => O.step h (O.castJointAction ss a)) = PMF.pure h
    have hstep :
        ∀ a, O.step h (O.castJointAction ss a) = PMF.pure h := by
      intro a
      change (toReachableHistoryObsModelCore G hLeg).machine.step h
          (O.castJointAction ss a) = PMF.pure h
      dsimp [toReachableHistoryObsModelCore]
      rw [dif_pos hterm]
    rw [show
        (fun a => O.step h (O.castJointAction ss a)) =
          fun _ => PMF.pure h by
        funext a
        exact hstep a]
    simp
  · rw [History.runDistFrom_succ_nonterminal
      (G := G) (σ := β.extend) (n := 0) (h := h) hterm]
    have hleft :
        O.stepDist βcore ss =
          (Math.ProbabilityMassFunction.pushforward
              (O.jointActionDist βcore ss) rawOf).bind runRaw := by
      change O.stepDist βcore ss =
        (PMF.map rawOf (O.jointActionDist βcore ss)).bind runRaw
      rw [PMF.bind_map]
      change (O.jointActionDist βcore ss).bind
          (fun a => O.step h (O.castJointAction ss a)) =
        (O.jointActionDist βcore ss).bind (runRaw ∘ rawOf)
      apply congrArg
      funext a
      have hraw :
          G.legal h.lastState (rawOf a) := by
        rw [G.legal_iff_forall]
        refine ⟨hterm, ?_⟩
        intro i
        have haiInfo :
            rawOf a i ∈ G.availableMovesAtInfoState i
              (G.reachableInfoStateOfHistory i h).1 := by
          dsimp [rawOf]
          have hai :
              (a i).1 ∈ G.availableMovesAtInfoState i
                (O.projectStates i ss).1 := (a i).2
          simpa [O, h, reachableHistory_projectStates_eq_last (G := G) hLeg i ss] using hai
        have hai : rawOf a i ∈ G.availableMoves h i := by
          have hEq := G.availableMovesAtInfoState_eq_of_history hLeg i h
          exact hEq ▸ haiInfo
        simpa [FOSG.mem_availableMoves_iff] using hai
      dsimp [runRaw]
      change (toReachableHistoryObsModelCore G hLeg).machine.step h
          (O.castJointAction ss a) =
        if hraw' : G.legal h.lastState (rawOf a) then
          (G.transition h.lastState ⟨rawOf a, hraw'⟩).bind
            (fun dst => PMF.pure (h.extendByOutcome ⟨rawOf a, hraw'⟩ dst))
        else PMF.pure h
      dsimp [toReachableHistoryObsModelCore]
      rw [dif_neg hterm, dif_pos hraw]
      congr 1
      · funext dst
        apply congrArg (fun act => h.extendByOutcome act dst)
        apply Subtype.ext
        funext i
        exact reachableHistory_castJointAction_val (G := G) hLeg ss a i
      · congr 1
        apply Subtype.ext
        funext i
        exact reachableHistory_castJointAction_val (G := G) hLeg ss a i
    rw [hleft]
    rw [reachableHistoryBehavioralJointActionDist_map_val
      (G := G) hLeg βcore β hβ ss]
    change (G.jointActionDist β.extend h).bind runRaw =
      (G.legalActionLaw β.extend h hterm).bind
        (fun a =>
          (G.transition h.lastState a).bind
            (fun dst => PMF.pure (h.extendByOutcome a dst)))
    rw [← G.legalActionLaw_bind_eq_jointActionDist_bind β.extend h hterm runRaw]
    apply congrArg
    funext a
    dsimp [runRaw]
    rw [dif_pos a.2]

theorem reachableHistoryOutcomeDist_eq_runDist
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    [DecidablePred G.terminal]
    (hLeg : G.LegalObservable) (k : Nat)
    (βcore : (toReachableHistoryObsModelCore G hLeg).BehavioralProfile)
    (β : G.ReachableLegalBehavioralProfile)
    (hβ : β.toProfile = eraseReachableHistoryBehavioral (G := G) hLeg βcore) :
    reachableHistoryOutcomeDist (G := G) hLeg k βcore =
      G.runDist k β.extend := by
  classical
  induction k with
  | zero =>
      simp [reachableHistoryOutcomeDist, FOSG.runDist, ObsModelCore.runDist,
        ObsModelCore.lastState, toReachableHistoryObsModelCore]
  | succ k ih =>
      let O := toReachableHistoryObsModelCore G hLeg
      let σ := β.extend
      change (O.runDist (k + 1) βcore).bind (fun ss => PMF.pure (O.lastState ss)) =
        History.runDistFrom G σ (k + 1) (History.nil G)
      rw [← History.runDistFrom_bind_runDistFrom
        (G := G) σ k 1 (History.nil G)]
      have ih' :
          (O.runDist k βcore).bind (fun ss => PMF.pure (O.lastState ss)) =
            History.runDistFrom G σ k (History.nil G) := by
        simpa [reachableHistoryOutcomeDist, FOSG.runDist, O, σ] using ih
      rw [← ih']
      simp only [ObsModelCore.runDist, Math.TraceRun.traceRun]
      rw [PMF.bind_bind, PMF.bind_bind]
      congr 1
      funext ss
      rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_map]
      conv_lhs =>
        arg 2
        ext t
        simp [Function.comp_def, ObsModelCore.lastState_append_singleton]
      rw [reachableHistoryBehavioralStepDist_eq_runDistFrom_one
        (G := G) hLeg βcore β hβ ss]
      simp [O, σ]

theorem eraseReachableHistoryBehavioral_isLegal
    (hLeg : G.LegalObservable)
    (β : (toReachableHistoryObsModelCore G hLeg).BehavioralProfile) :
    ∀ i, G.IsLegalReachableBehavioralStrategy i
      (eraseReachableHistoryBehavioral (G := G) hLeg β i) := by
  classical
  intro i h oi hoi
  unfold eraseReachableHistoryBehavioral at hoi
  rcases (PMF.mem_support_map_iff _ _ _).mp hoi with ⟨a, _ha, haoi⟩
  have haiInfo :
      a.1 ∈ G.availableMovesAtInfoState i
        (G.reachableInfoStateOfHistory i h).1 := a.2
  have hai : a.1 ∈ G.availableMoves h i := by
    have hEq := G.availableMovesAtInfoState_eq_of_history hLeg i h
    exact hEq ▸ haiInfo
  simpa [← haoi] using hai

/-- Reachable-history M→B witness with legal fallback at unreached reachable
information states. -/
noncomputable def reachableLegalHistoryMixedToBehavioral
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (μ : ReachableMixedProfile (G := G)) :
    (toReachableHistoryObsModelCore G hLeg).BehavioralProfile :=
  ObsModelCore.mixedToBehavioralProfileWithFallback
    (O := toReachableHistoryObsModelCore G hLeg)
    (liftReachableHistoryMixedProfile (G := G) hLeg μ)
    (reachableLegalFallbackBehavioral (G := G) hLeg)

open Classical in
/-- Canonical legal reachable FOSG behavioral profile realizing a mixed profile
over legal reachable pure strategies.

The core M→B construction produces legal-move subtypes. This definition erases
those subtypes back to native reachable FOSG strategies and packages the
legality proof. -/
noncomputable def reachableMixedToLegalBehavioral
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (μ : ReachableMixedProfile (G := G)) :
    G.ReachableLegalBehavioralProfile := by
  let βcore := reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ
  let βraw := eraseReachableHistoryBehavioral (G := G) hLeg βcore
  have hβlegal :
      ∀ i, G.IsLegalReachableBehavioralStrategy i (βraw i) :=
    eraseReachableHistoryBehavioral_isLegal (G := G) hLeg βcore
  exact fun i => ⟨βraw i, hβlegal i⟩

@[simp] theorem reachableMixedToLegalBehavioral_toProfile
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (μ : ReachableMixedProfile (G := G)) :
    (reachableMixedToLegalBehavioral (G := G) hLeg μ).toProfile =
      eraseReachableHistoryBehavioral (G := G) hLeg
        (reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ) := by
  rfl

open Classical in
theorem reachableLegalHistoryMixedToBehavioral_historyOutcomeDist
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (hMass : ReachableHistoryStepMassInvariant (G := G) hLeg)
    (hFactor : ReachableHistoryStepSupportFactorization (G := G) hLeg)
    (hLocal : ∀ i, ReachableHistoryActionPosteriorLocal (G := G) hLeg i)
    (μ : ReachableMixedProfile (G := G))
    (k : Nat) :
    reachableHistoryOutcomeDist (G := G) hLeg k
        (reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ) =
      (reachableMixedProfileJoint (G := G) μ).bind
        (fun π => reachableHistoryOutcomeDistPureProfile (G := G) hLeg k π) := by
  letI : ∀ i, Fintype ((toReachableHistoryObsModelCore G hLeg).InfoState i) :=
    ReachableHistoryNative.reachableHistoryInfoStateFintype (G := G) hLeg
  letI : ∀ i, Fintype ((toReachableHistoryObsModelCore G hLeg).LocalStrategy i) :=
    ReachableHistoryNative.reachableHistoryLocalStrategyFintype (G := G) hLeg
  letI : ∀ i (o : G.ReachableInfoState i), Nonempty (ReachableInfoLegalMove G i o) :=
    fun i o => ⟨reachableInfoLegalMoveDefault G i o⟩
  have hβ :=
    ObsModelCore.mixedToBehavioralProfileWithFallback_runDist
      (O := toReachableHistoryObsModelCore G hLeg)
      hMass hFactor
      (fun i => by
        simpa [ReachableHistoryActionPosteriorLocal] using hLocal i)
      (liftReachableHistoryMixedProfile (G := G) hLeg μ)
      (reachableLegalFallbackBehavioral (G := G) hLeg) k
  unfold reachableHistoryOutcomeDist reachableLegalHistoryMixedToBehavioral
  rw [hβ, PMF.bind_bind]
  change
    (Math.PMFProduct.pmfPi (liftReachableHistoryMixedProfile (G := G) hLeg μ)).bind
        (fun π => reachableHistoryOutcomeDistPure (G := G) hLeg k π) =
      (reachableMixedProfileJoint (G := G) μ).bind
        (fun π => reachableHistoryOutcomeDistPureProfile (G := G) hLeg k π)
  have hJoint :=
    liftReachableHistoryMixedProfile_joint (G := G) hLeg μ
  rw [hJoint]
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_map]
  rfl

open Classical in
/-- **Kuhn's theorem, mixed -> behavioral direction for legal reachable FOSG
strategy spaces.**

This is the bounded-history-friendly M→B theorem: it needs finiteness of
`G.History`, not finiteness of the full `G.InfoState i = List ...` type. The
strategy space is already legal, so no separate support-legality assumption is
needed. -/
theorem reachable_mixed_to_behavioral
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (μ : ReachableMixedProfile (G := G))
    (k : Nat) :
    ∃ β : (toReachableHistoryObsModelCore G hLeg).BehavioralProfile,
      reachableHistoryOutcomeDist (G := G) hLeg k β =
        (reachableMixedProfileJoint (G := G) μ).bind
          (fun π => reachableHistoryOutcomeDistPureProfile (G := G) hLeg k π) := by
  letI : ∀ i, Fintype ((toReachableHistoryObsModelCore G hLeg).InfoState i) :=
    ReachableHistoryNative.reachableHistoryInfoStateFintype (G := G) hLeg
  letI : ∀ i, Fintype ((toReachableHistoryObsModelCore G hLeg).LocalStrategy i) :=
    ReachableHistoryNative.reachableHistoryLocalStrategyFintype (G := G) hLeg
  refine ⟨reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ, ?_⟩
  exact reachableLegalHistoryMixedToBehavioral_historyOutcomeDist
    (G := G) hLeg
    (reachableHistory_stepMassInvariant (G := G) hLeg)
    (reachableHistory_stepSupportFactorization (G := G) hLeg)
    (reachableHistory_actionPosteriorLocal (G := G) hLeg) μ k

open Classical in
/-- FOSG-facing form of the legal reachable M→B theorem.

The distributional statement is over the canonical legal core profile. Its
erasure is packaged as a legal reachable FOSG behavioral profile. -/
theorem reachable_mixed_to_legal_behavioral
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (μ : ReachableMixedProfile (G := G))
    (k : Nat) :
    ∃ βcore : (toReachableHistoryObsModelCore G hLeg).BehavioralProfile,
    ∃ β : G.ReachableLegalBehavioralProfile,
      β.toProfile = eraseReachableHistoryBehavioral (G := G) hLeg βcore ∧
      reachableHistoryOutcomeDist (G := G) hLeg k βcore =
        (reachableMixedProfileJoint (G := G) μ).bind
          (fun π => reachableHistoryOutcomeDistPureProfile (G := G) hLeg k π) := by
  letI : ∀ i, Fintype ((toReachableHistoryObsModelCore G hLeg).InfoState i) :=
    ReachableHistoryNative.reachableHistoryInfoStateFintype (G := G) hLeg
  letI : ∀ i, Fintype ((toReachableHistoryObsModelCore G hLeg).LocalStrategy i) :=
    ReachableHistoryNative.reachableHistoryLocalStrategyFintype (G := G) hLeg
  obtain ⟨βcore, hβcore⟩ :=
    reachable_mixed_to_behavioral (G := G) hLeg μ k
  let βraw := eraseReachableHistoryBehavioral (G := G) hLeg βcore
  have hβlegal :
      ∀ i, G.IsLegalReachableBehavioralStrategy i (βraw i) :=
    eraseReachableHistoryBehavioral_isLegal (G := G) hLeg βcore
  let β : G.ReachableLegalBehavioralProfile :=
    fun i => ⟨βraw i, hβlegal i⟩
  refine ⟨βcore, β, ?_, hβcore⟩
  rfl

open Classical in
/-- Native FOSG form of the legal reachable M→B theorem.

An independent mixed profile over legal reachable pure strategies is realized
by a legal reachable behavioral profile with the same finite-horizon
distribution over FOSG histories. -/
theorem reachable_mixed_to_legal_behavioral_runDist
    [Fintype ι] [Fintype G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    (hLeg : G.LegalObservable)
    (μ : ReachableMixedProfile (G := G))
    (k : Nat) :
    ∃ β : G.ReachableLegalBehavioralProfile,
      G.runDist k β.extend =
        (reachableMixedProfileJoint (G := G) μ).bind
          (fun π => G.runDist k (G.legalPureToBehavioral π.extend)) := by
  obtain ⟨βcore, β, hβ, hdist⟩ :=
    reachable_mixed_to_legal_behavioral (G := G) hLeg μ k
  refine ⟨β, ?_⟩
  have hrun :=
    reachableHistoryOutcomeDist_eq_runDist
      (G := G) hLeg k βcore β hβ
  rw [← hrun, hdist]
  congr
  funext π
  exact reachableHistoryOutcomeDistPureProfile_eq_runDist (G := G) hLeg k π

open Classical in
/-- Native finite-horizon law for the canonical legal reachable M→B witness. -/
theorem reachableMixedToLegalBehavioral_runDist
    [Fintype ι] [Fintype G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    (hLeg : G.LegalObservable)
    (μ : ReachableMixedProfile (G := G))
    (k : Nat) :
    G.runDist k (reachableMixedToLegalBehavioral (G := G) hLeg μ).extend =
      (reachableMixedProfileJoint (G := G) μ).bind
        (fun π => G.runDist k (G.legalPureToBehavioral π.extend)) := by
  have hcore :=
    reachableLegalHistoryMixedToBehavioral_historyOutcomeDist
      (G := G) hLeg
      (reachableHistory_stepMassInvariant (G := G) hLeg)
      (reachableHistory_stepSupportFactorization (G := G) hLeg)
      (reachableHistory_actionPosteriorLocal (G := G) hLeg) μ k
  have hrun :=
    reachableHistoryOutcomeDist_eq_runDist
      (G := G) hLeg k
      (reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ)
      (reachableMixedToLegalBehavioral (G := G) hLeg μ)
      (reachableMixedToLegalBehavioral_toProfile (G := G) hLeg μ)
  rw [← hrun, hcore]
  congr
  funext π
  exact reachableHistoryOutcomeDistPureProfile_eq_runDist (G := G) hLeg k π

open Classical in
/-- Replacing `who`'s reachable mixed component by the mixed pure strategy
induced by a legal behavioral strategy gives the same finite-horizon native run
law as the canonical reachable M→B behavioral realization of the updated mixed
profile. -/
theorem reachable_mixed_to_canonical_behavioral_unilateral_deviation_runDist
    [Fintype ι] [Fintype G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    (hLeg : G.LegalObservable)
    (k : Nat)
    (μ : ReachableMixedProfile (G := G))
    (who : ι)
    (βwho' : G.ReachableLegalBehavioralStrategy who) :
    let μwho' := reachableLegalBehavioralToMixed (G := G) hLeg who βwho'
    (reachableMixedProfileJoint (G := G) (Function.update μ who μwho')).bind
      (fun π => G.runDist k (G.legalPureToBehavioral π.extend)) =
    G.runDist k
      (reachableMixedToLegalBehavioral
        (G := G) hLeg
        (Function.update μ who μwho')).extend := by
  classical
  let μwho' := reachableLegalBehavioralToMixed (G := G) hLeg who βwho'
  exact (reachableMixedToLegalBehavioral_runDist
      (G := G) hLeg (Function.update μ who μwho') k).symm

open Classical in
/-- The canonical reachable M→B profile after replacing `who`'s mixed component
has the same reachable-history trace law as the profile that keeps the original
canonical M→B profile for the opponents and plugs in the target behavioral
deviation for `who`. -/
theorem reachableLegalHistoryMixedToBehavioral_unilateral_deviation_runDist
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (k : Nat)
    (μ : ReachableMixedProfile (G := G))
    (who : ι)
    (βwho' : G.ReachableLegalBehavioralStrategy who) :
    let μwho' := reachableLegalBehavioralToMixed (G := G) hLeg who βwho'
    let βsrc :=
      reachableLegalHistoryMixedToBehavioral (G := G) hLeg
        (Function.update μ who μwho')
    let βtgt :=
      Function.update (reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ)
        who (liftReachableHistoryBehavioralStrategy (G := G) hLeg who βwho')
    (toReachableHistoryObsModelCore G hLeg).runDist k βsrc =
      (toReachableHistoryObsModelCore G hLeg).runDist k βtgt := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  let μwho' := reachableLegalBehavioralToMixed (G := G) hLeg who βwho'
  let μ' : ReachableMixedProfile (G := G) := Function.update μ who μwho'
  let βsrc :=
    reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ'
  let βorig :=
    reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ
  let βtgt : O.BehavioralProfile :=
    Function.update βorig who
      (liftReachableHistoryBehavioralStrategy (G := G) hLeg who βwho')
  let μcore := liftReachableHistoryMixedProfile (G := G) hLeg μ
  let μcore' := liftReachableHistoryMixedProfile (G := G) hLeg μ'
  let fallback := reachableLegalFallbackBehavioral (G := G) hLeg
  letI : ∀ i, Fintype (O.InfoState i) :=
    ReachableHistoryNative.reachableHistoryInfoStateFintype (G := G) hLeg
  letI : ∀ i, Fintype (O.LocalStrategy i) :=
    ReachableHistoryNative.reachableHistoryLocalStrategyFintype (G := G) hLeg
  letI : ∀ i (o : G.ReachableInfoState i), Nonempty (ReachableInfoLegalMove G i o) :=
    fun i o => ⟨reachableInfoLegalMoveDefault G i o⟩
  have hsrcRun :
      O.runDist k βsrc = O.runDist k βtgt := by
    apply ObsModelCore.runDist_congr (O := O) (β₁ := βsrc) (β₂ := βtgt)
    intro m q ss hss
    have hβsrcLaw :
        O.runDist m βsrc =
          (Math.PMFProduct.pmfPi μcore').bind (O.runDistPure m) := by
      have h :=
        ObsModelCore.mixedToBehavioralProfileWithFallback_runDist
          (O := O)
          (reachableHistory_stepMassInvariant (G := G) hLeg)
          (reachableHistory_stepSupportFactorization (G := G) hLeg)
          (fun i => by
            simpa [ReachableHistoryActionPosteriorLocal] using
              reachableHistory_actionPosteriorLocal (G := G) hLeg i)
          μcore' fallback m
      simpa [βsrc, reachableLegalHistoryMixedToBehavioral, μcore', fallback, O] using h
    have hmix : ((Math.PMFProduct.pmfPi μcore').bind (O.runDistPure m)) ss ≠ 0 := by
      rw [← hβsrcLaw]
      exact hss
    have hmixSum :
        ∑ π : O.PureProfile,
          Math.PMFProduct.pmfPi μcore' π * O.runDistPure m π ss ≠ 0 := by
      simpa only [PMF.bind_apply, tsum_fintype] using hmix
    obtain ⟨πw, _hπwMem, hπwProd⟩ :=
      Finset.exists_ne_zero_of_sum_ne_zero hmixSum
    have hπw : O.runDistPure m πw ss ≠ 0 :=
      right_ne_zero_of_mul hπwProd
    have hπwPure :
        Math.ParameterizedChain.pureRun O.pureStep O.init m πw ss ≠ 0 := by
      simpa [ObsModelCore.runDistPure_eq_pureRun] using hπw
    have hsrcFactor :
        βsrc q (O.projectStates q ss) =
          ObsModelCore.mixedToBehavioralFactorAt (O := O)
            μcore' q m ss πw := by
      have h :=
        ObsModelCore.mixedToBehavioralProfileWithFallback_eq_factorAt
          (O := O)
          (fun i => by
            simpa [ReachableHistoryActionPosteriorLocal] using
              reachableHistory_actionPosteriorLocal (G := G) hLeg i)
          μcore' fallback q m ss πw hπwPure
      simpa [βsrc, reachableLegalHistoryMixedToBehavioral, μcore', fallback, O] using h
    by_cases hq : q = who
    · subst q
      have hwhoFactor :
          ObsModelCore.mixedToBehavioralFactorAt (O := O)
              μcore' who m ss πw =
            liftReachableHistoryBehavioralStrategy (G := G) hLeg who βwho'
              (O.projectStates who ss) := by
        have h :=
          reachableHistoryBehavioralToMixedStrategy_factorAt
            (G := G) hLeg who βwho' m ss πw hπwPure
        dsimp [ObsModelCore.mixedToBehavioralFactorAt, μcore',
          liftReachableHistoryMixedProfile, μ', μwho', O]
        rw [Function.update_self]
        have hliftPush :
            Math.ProbabilityMassFunction.pushforward
                (reachableLegalBehavioralToMixed (G := G) hLeg who βwho')
                (liftReachableHistoryPureStrategy (G := G) hLeg who) =
              reachableHistoryBehavioralToMixedStrategy (G := G) hLeg who βwho' := by
          simp [Math.ProbabilityMassFunction.pushforward,
            reachableLegalBehavioralToMixed_lift (G := G) hLeg who βwho']
        rw [hliftPush]
        exact h
      have htgt :
          βtgt who (O.projectStates who ss) =
            liftReachableHistoryBehavioralStrategy (G := G) hLeg who βwho'
              (O.projectStates who ss) := by
        simp [βtgt]
      exact hsrcFactor.trans (hwhoFactor.trans htgt.symm)
    · have horigFactor :
          βorig q (O.projectStates q ss) =
            ObsModelCore.mixedToBehavioralFactorAt (O := O)
              μcore q m ss πw := by
        have h :=
          ObsModelCore.mixedToBehavioralProfileWithFallback_eq_factorAt
            (O := O)
            (fun i => by
              simpa [ReachableHistoryActionPosteriorLocal] using
                reachableHistory_actionPosteriorLocal (G := G) hLeg i)
            μcore fallback q m ss πw hπwPure
        simpa [βorig, reachableLegalHistoryMixedToBehavioral, μcore, fallback, O] using h
      have hfactorEq :
          ObsModelCore.mixedToBehavioralFactorAt (O := O)
              μcore' q m ss πw =
            ObsModelCore.mixedToBehavioralFactorAt (O := O)
              μcore q m ss πw := by
        simp [ObsModelCore.mixedToBehavioralFactorAt, μcore', μcore,
          liftReachableHistoryMixedProfile, μ', hq, O]
      calc
        βsrc q (O.projectStates q ss)
            = ObsModelCore.mixedToBehavioralFactorAt (O := O)
                μcore' q m ss πw := hsrcFactor
        _ = ObsModelCore.mixedToBehavioralFactorAt (O := O)
                μcore q m ss πw := hfactorEq
        _ = βorig q (O.projectStates q ss) := horigFactor.symm
        _ = βtgt q (O.projectStates q ss) := by
              simp [βtgt, hq]
  simpa [O, μwho', μ', βsrc, βorig, βtgt] using hsrcRun

theorem reachable_unilateral_target_toProfile
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (μ : ReachableMixedProfile (G := G))
    (who : ι)
    (βwho' : G.ReachableLegalBehavioralStrategy who) :
    let βcore :=
      Function.update (reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ)
        who (liftReachableHistoryBehavioralStrategy (G := G) hLeg who βwho')
    let β : G.ReachableLegalBehavioralProfile :=
      Function.update (reachableMixedToLegalBehavioral (G := G) hLeg μ)
        who βwho'
    β.toProfile = eraseReachableHistoryBehavioral (G := G) hLeg βcore := by
  classical
  let βcore :=
    Function.update (reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ)
      who (liftReachableHistoryBehavioralStrategy (G := G) hLeg who βwho')
  let β : G.ReachableLegalBehavioralProfile :=
    Function.update (reachableMixedToLegalBehavioral (G := G) hLeg μ)
      who βwho'
  funext i s
  by_cases hi : i = who
  · subst i
    change (Function.update (reachableMixedToLegalBehavioral (G := G) hLeg μ)
          who βwho' who).1 s =
      PMF.map (fun a : ReachableInfoLegalMove G who s => a.1)
        ((Function.update (reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ)
          who (liftReachableHistoryBehavioralStrategy (G := G) hLeg who βwho')) who s)
    rw [Function.update_self, Function.update_self]
    simpa [Math.ProbabilityMassFunction.pushforward] using
      (erase_liftReachableHistoryBehavioralStrategy
        (G := G) hLeg who βwho' s).symm
  · change (Function.update (reachableMixedToLegalBehavioral (G := G) hLeg μ)
          who βwho' i).1 s =
      PMF.map (fun a : ReachableInfoLegalMove G i s => a.1)
        ((Function.update (reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ)
          who (liftReachableHistoryBehavioralStrategy (G := G) hLeg who βwho')) i s)
    rw [Function.update_of_ne hi, Function.update_of_ne hi]
    exact congrFun (congrFun
      (reachableMixedToLegalBehavioral_toProfile (G := G) hLeg μ) i) s

open Classical in
/-- A unilateral reachable behavioral deviation by `who` is simulated on the
mixed side by replacing only `who`'s mixed component with
`reachableLegalBehavioralToMixed hLeg who βwho'`. The resulting mixed profile
and the behavioral profile obtained by updating only `who` have the same
finite-horizon native run law. -/
theorem reachable_mixed_to_behavioral_unilateral_deviation_runDist_eq
    [Fintype ι] [Fintype G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    (hLeg : G.LegalObservable)
    (k : Nat)
    (μ : ReachableMixedProfile (G := G))
    (who : ι)
    (βwho' : G.ReachableLegalBehavioralStrategy who) :
    let μwho' := reachableLegalBehavioralToMixed (G := G) hLeg who βwho'
    (reachableMixedProfileJoint (G := G) (Function.update μ who μwho')).bind
      (fun π => G.runDist k (G.legalPureToBehavioral π.extend)) =
    G.runDist k
      (GameTheory.FOSG.ReachableLegalBehavioralProfile.extend
        ((Function.update
            (reachableMixedToLegalBehavioral (G := G) hLeg μ)
            who βwho') : G.ReachableLegalBehavioralProfile)) := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  let μwho' := reachableLegalBehavioralToMixed (G := G) hLeg who βwho'
  let μ' : ReachableMixedProfile (G := G) := Function.update μ who μwho'
  let βsrcCore := reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ'
  let βtgtCore :=
    Function.update (reachableLegalHistoryMixedToBehavioral (G := G) hLeg μ)
      who (liftReachableHistoryBehavioralStrategy (G := G) hLeg who βwho')
  let βtgt : G.ReachableLegalBehavioralProfile :=
    Function.update (reachableMixedToLegalBehavioral (G := G) hLeg μ)
      who βwho'
  have hsrcBridge :
      reachableHistoryOutcomeDist (G := G) hLeg k βsrcCore =
        G.runDist k
          (reachableMixedToLegalBehavioral (G := G) hLeg μ').extend :=
    reachableHistoryOutcomeDist_eq_runDist
      (G := G) hLeg k βsrcCore
      (reachableMixedToLegalBehavioral (G := G) hLeg μ')
      (by
        simp [βsrcCore, μ',
          reachableMixedToLegalBehavioral_toProfile (G := G) hLeg μ'])
  have hcoreTrace :
      O.runDist k βsrcCore =
        O.runDist k βtgtCore := by
    simpa [O, μwho', μ', βsrcCore, βtgtCore] using
      reachableLegalHistoryMixedToBehavioral_unilateral_deviation_runDist
        (G := G) hLeg k μ who βwho'
  have hcoreOutcome :
      reachableHistoryOutcomeDist (G := G) hLeg k βsrcCore =
        reachableHistoryOutcomeDist (G := G) hLeg k βtgtCore := by
    unfold reachableHistoryOutcomeDist
    rw [hcoreTrace]
  have htgtProfile :
      βtgt.toProfile = eraseReachableHistoryBehavioral (G := G) hLeg βtgtCore := by
    simpa [βtgt, βtgtCore] using
      reachable_unilateral_target_toProfile
        (G := G) hLeg μ who βwho'
  have htgtBridge :
      reachableHistoryOutcomeDist (G := G) hLeg k βtgtCore =
        G.runDist k (GameTheory.FOSG.ReachableLegalBehavioralProfile.extend βtgt) :=
    reachableHistoryOutcomeDist_eq_runDist
      (G := G) hLeg k βtgtCore βtgt htgtProfile
  calc
    (reachableMixedProfileJoint (G := G) μ').bind
        (fun π => G.runDist k (G.legalPureToBehavioral π.extend))
        = G.runDist k
            (reachableMixedToLegalBehavioral (G := G) hLeg μ').extend := by
            exact (reachableMixedToLegalBehavioral_runDist
              (G := G) hLeg μ' k).symm
    _ = reachableHistoryOutcomeDist (G := G) hLeg k βsrcCore := hsrcBridge.symm
    _ = reachableHistoryOutcomeDist (G := G) hLeg k βtgtCore := hcoreOutcome
    _ = G.runDist k βtgt.extend := htgtBridge

open Classical in
/-- Existential form of `reachable_mixed_to_behavioral_unilateral_deviation_runDist_eq`. -/
theorem reachable_mixed_to_behavioral_unilateral_deviation_runDist
    [Fintype ι] [Fintype G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    (hLeg : G.LegalObservable)
    (k : Nat)
    (μ : ReachableMixedProfile (G := G))
    (who : ι)
    (βwho' : G.ReachableLegalBehavioralStrategy who) :
    ∃ μwho' : PMF (G.ReachableLegalPureStrategy who),
      (reachableMixedProfileJoint (G := G) (Function.update μ who μwho')).bind
        (fun π => G.runDist k (G.legalPureToBehavioral π.extend)) =
      G.runDist k
        (GameTheory.FOSG.ReachableLegalBehavioralProfile.extend
          ((Function.update
              (reachableMixedToLegalBehavioral (G := G) hLeg μ)
              who βwho') : G.ReachableLegalBehavioralProfile)) := by
  refine ⟨reachableLegalBehavioralToMixed (G := G) hLeg who βwho', ?_⟩
  exact reachable_mixed_to_behavioral_unilateral_deviation_runDist_eq
    (G := G) hLeg k μ who βwho'

noncomputable def reachableLegalPureStrategyDefault
    (hLeg : G.LegalObservable) (i : ι) :
    G.ReachableLegalPureStrategy i := by
  refine ⟨fun s => (reachableInfoLegalMoveDefault G i s).1, ?_⟩
  intro h
  have hinfo :
      (reachableInfoLegalMoveDefault G i
          (G.reachableInfoStateOfHistory i h)).1 ∈
        G.availableMovesAtInfoState i (G.reachableInfoStateOfHistory i h).1 :=
    (reachableInfoLegalMoveDefault G i
      (G.reachableInfoStateOfHistory i h)).2
  have hEq := G.availableMovesAtInfoState_eq_of_history hLeg i h
  exact hEq ▸ hinfo

noncomputable def reachableDefaultMixedProfile
    (hLeg : G.LegalObservable) :
    ReachableMixedProfile (G := G) :=
  fun i => PMF.pure (reachableLegalPureStrategyDefault (G := G) hLeg i)

/-- The player-`i` component of the canonical reachable mixed-to-behavioral map
as a function of player `i`'s mixed pure strategy alone. -/
noncomputable def reachableMixedToLegalBehavioralStrategy
    [Fintype ι] [Fintype G.History] [∀ j, Fintype (Option (Act j))]
    (hLeg : G.LegalObservable) (i : ι)
    (μi : PMF (G.ReachableLegalPureStrategy i)) :
    G.ReachableLegalBehavioralStrategy i :=
  reachableMixedToLegalBehavioral (G := G) hLeg
    (Function.update (reachableDefaultMixedProfile (G := G) hLeg) i μi) i

@[simp] theorem reachableMixedToLegalBehavioralStrategy_eq_component
    [Fintype ι] [Fintype G.History] [∀ j, Fintype (Option (Act j))]
    (hLeg : G.LegalObservable)
    (μ : ReachableMixedProfile (G := G)) (i : ι) :
    reachableMixedToLegalBehavioralStrategy (G := G) hLeg i (μ i) =
      reachableMixedToLegalBehavioral (G := G) hLeg μ i := by
  classical
  apply Subtype.ext
  funext s
  unfold reachableMixedToLegalBehavioralStrategy reachableMixedToLegalBehavioral
    reachableLegalHistoryMixedToBehavioral eraseReachableHistoryBehavioral
    ObsModelCore.mixedToBehavioralProfileWithFallback
    ObsModelCore.mixedToBehavioralFactorAt liftReachableHistoryMixedProfile
  simp

noncomputable def reachableMixedPureGameFormAtHorizon
    [Fintype ι] [Fintype G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    (k : Nat) : GameForm ι where
  Strategy := fun i => PMF (G.ReachableLegalPureStrategy i)
  Outcome := G.History
  outcomeKernel := fun μ =>
    (reachableMixedProfileJoint (G := G) μ).bind
      (fun π => G.runDist k (G.legalPureToBehavioral π.extend))

noncomputable def reachableBehavioralGameFormAtHorizon
    [Fintype ι] [Fintype G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    (k : Nat) : GameForm ι where
  Strategy := fun i => G.ReachableLegalBehavioralStrategy i
  Outcome := G.History
  outcomeKernel := fun β =>
    G.runDist k (GameTheory.FOSG.ReachableLegalBehavioralProfile.extend β)

open Classical in
/-- Reachable Kuhn simulation for unilateral deviations. -/
noncomputable def reachableKuhnNashDeviationSimulation
    [Fintype ι] [Fintype G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    (hLeg : G.LegalObservable) (k : Nat) :
    GameForm.NashDeviationSimulation
      (reachableMixedPureGameFormAtHorizon (G := G) k)
      (reachableBehavioralGameFormAtHorizon (G := G) k)
      G.History :=
  GameForm.NashDeviationSimulation.ofFunctionalRealization
    ({ observe := id })
    ({ observe := id })
    (fun μ => reachableMixedToLegalBehavioral (G := G) hLeg μ)
    (by
      intro μ
      simp only [GameForm.OutcomeView.law, reachableMixedPureGameFormAtHorizon,
        reachableBehavioralGameFormAtHorizon]
      rw [PMF.map_id, PMF.map_id]
      exact (reachableMixedToLegalBehavioral_runDist (G := G) hLeg μ k).symm)
    (by
      intro μ who βwho'
      refine ⟨reachableLegalBehavioralToMixed (G := G) hLeg who βwho', ?_⟩
      simp only [GameForm.OutcomeView.law, reachableMixedPureGameFormAtHorizon,
        reachableBehavioralGameFormAtHorizon]
      rw [PMF.map_id, PMF.map_id]
      exact reachable_mixed_to_behavioral_unilateral_deviation_runDist_eq
        (G := G) hLeg k μ who βwho')

open Classical in
/-- Ready-made Nash transport for the finite-horizon reachable Kuhn
mixed-pure-to-behavioral presentation. -/
theorem reachableKuhn_target_nashFor_of_source_nashFor
    [Fintype ι] [Fintype G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    (hLeg : G.LegalObservable) (k : Nat)
    (μ : (reachableMixedPureGameFormAtHorizon (G := G) k).Profile)
    {prefΩ : ι → PMF G.History → PMF G.History → Prop}
    (hN :
      (reachableMixedPureGameFormAtHorizon (G := G) k).IsNashFor
        (GameForm.observedPref
          (reachableKuhnNashDeviationSimulation (G := G) hLeg k).viewG
          prefΩ) μ) :
    (reachableBehavioralGameFormAtHorizon (G := G) k).IsNashFor
      (GameForm.observedPref
        (reachableKuhnNashDeviationSimulation (G := G) hLeg k).viewH
        prefΩ)
      (reachableMixedToLegalBehavioral (G := G) hLeg μ) := by
  exact GameForm.NashDeviationSimulation.target_nash_of_source_nash
    (reachableKuhnNashDeviationSimulation (G := G) hLeg k) rfl hN

open Classical in
/-- Reachable Kuhn simulation for coarse-correlated deviations. -/
noncomputable def reachableKuhnCoarseCorrelatedDeviationSimulation
    [Fintype ι] [Fintype G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    (hLeg : G.LegalObservable) (k : Nat) :
    GameForm.DeviationFamilySimulation
      (reachableMixedPureGameFormAtHorizon (G := G) k)
      (reachableBehavioralGameFormAtHorizon (G := G) k)
      G.History
      (reachableMixedPureGameFormAtHorizon (G := G) k).constantDeviationProfileFamily
      (reachableBehavioralGameFormAtHorizon (G := G) k).constantDeviationProfileFamily :=
  GameForm.DeviationFamilySimulation.ofConstantProfileMap
    ({ observe := id })
    ({ observe := id })
    (fun μ => reachableMixedToLegalBehavioral (G := G) hLeg μ)
    (by
      intro μ
      simp only [GameForm.OutcomeView.law, reachableMixedPureGameFormAtHorizon,
        reachableBehavioralGameFormAtHorizon]
      rw [PMF.map_id, PMF.map_id]
      exact (reachableMixedToLegalBehavioral_runDist (G := G) hLeg μ k).symm)
    (by
      intro who βwho'Dev
      let βwho' : G.ReachableLegalBehavioralStrategy who := βwho'Dev
      let μwho' := reachableLegalBehavioralToMixed (G := G) hLeg who βwho'
      refine ⟨μwho', ?_⟩
      intro μ
      simp only [GameForm.OutcomeView.law, reachableMixedPureGameFormAtHorizon,
        reachableBehavioralGameFormAtHorizon, μwho']
      rw [PMF.map_id, PMF.map_id]
      exact reachable_mixed_to_behavioral_unilateral_deviation_runDist_eq
        (G := G) hLeg k μ who βwho')

open Classical in
/-- Reachable Kuhn simulation for correlated deviations. -/
noncomputable def reachableKuhnCorrelatedDeviationSimulation
    [Fintype ι] [Fintype G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    (hLeg : G.LegalObservable) (k : Nat) :
    GameForm.DeviationFamilySimulation
      (reachableMixedPureGameFormAtHorizon (G := G) k)
      (reachableBehavioralGameFormAtHorizon (G := G) k)
      G.History
      (reachableMixedPureGameFormAtHorizon (G := G) k).recommendationDeviationFamily
      (reachableBehavioralGameFormAtHorizon (G := G) k).recommendationDeviationFamily :=
  GameForm.DeviationFamilySimulation.ofRecommendationProfileMap
    ({ observe := id })
    ({ observe := id })
    (fun μ => reachableMixedToLegalBehavioral (G := G) hLeg μ)
    (by
      intro μ
      simp only [GameForm.OutcomeView.law, reachableMixedPureGameFormAtHorizon,
        reachableBehavioralGameFormAtHorizon]
      rw [PMF.map_id, PMF.map_id]
      exact (reachableMixedToLegalBehavioral_runDist (G := G) hLeg μ k).symm)
    (by
      intro who devH
      let devG : PMF (G.ReachableLegalPureStrategy who) →
          PMF (G.ReachableLegalPureStrategy who) := fun μwho =>
        let βrec : (reachableBehavioralGameFormAtHorizon (G := G) k).Strategy who :=
          reachableMixedToLegalBehavioralStrategy (G := G) hLeg who μwho
        let βdev : G.ReachableLegalBehavioralStrategy who := devH βrec
        reachableLegalBehavioralToMixed (G := G) hLeg who βdev
      refine ⟨devG, ?_⟩
      intro μ
      simp only [GameForm.OutcomeView.law, GameForm.deviateProfileFn,
        reachableMixedPureGameFormAtHorizon, reachableBehavioralGameFormAtHorizon,
        devG]
      rw [PMF.map_id, PMF.map_id]
      have hrec :
          reachableMixedToLegalBehavioralStrategy (G := G) hLeg who (μ who) =
            reachableMixedToLegalBehavioral (G := G) hLeg μ who :=
        reachableMixedToLegalBehavioralStrategy_eq_component (G := G) hLeg μ who
      simpa [hrec] using
        reachable_mixed_to_behavioral_unilateral_deviation_runDist_eq
          (G := G) hLeg k μ who
          (devH (reachableMixedToLegalBehavioral (G := G) hLeg μ who)))

theorem reachable_mixed_to_legal_behavioral_mapped_runDist
    [Fintype ι] [Fintype G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    (hLeg : G.LegalObservable)
    (μ : ReachableMixedProfile (G := G))
    (k : Nat) (project : G.History → Ω) :
    ∃ β : G.ReachableLegalBehavioralProfile,
      PMF.map project (G.runDist k β.extend) =
        (reachableMixedProfileJoint (G := G) μ).bind
          (fun π =>
            PMF.map project
              (reachableHistoryOutcomeDistPureProfile (G := G) hLeg k π)) := by
  obtain ⟨β, hdist⟩ :=
    reachable_mixed_to_legal_behavioral_runDist
      (G := G) hLeg μ k
  refine ⟨β, ?_⟩
  rw [hdist, PMF.map_bind]
  congr
  funext π
  rw [← reachableHistoryOutcomeDistPureProfile_eq_runDist
    (G := G) hLeg k π]

/-- Restrict an independent mixed profile over total legal pure strategies to
reachable information states. -/
noncomputable def legalPureMixedProfileRestrictReachable
    (μ : ∀ i, PMF (G.LegalPureStrategy i)) :
    ReachableMixedProfile (G := G) :=
  fun i => PMF.map (fun σ : G.LegalPureStrategy i => σ.restrictReachable) (μ i)

/-- Restrict a total legal pure profile to reachable information states. -/
noncomputable def legalPureProfileRestrictReachable
    (π : G.LegalPureProfile) : G.ReachableLegalPureProfile :=
  fun i => (π i).restrictReachable

/-- Restrict a total legal behavioral profile to reachable information states. -/
noncomputable def legalBehavioralProfileRestrictReachable
    (β : G.LegalBehavioralProfile) : G.ReachableLegalBehavioralProfile :=
  fun i => (β i).restrictReachable

theorem legalPureMixedProfileRestrictReachable_joint
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    [∀ i, Finite (G.LegalPureStrategy i)]
    (μ : ∀ i, PMF (G.LegalPureStrategy i)) :
    reachableMixedProfileJoint
        (G := G) (legalPureMixedProfileRestrictReachable (G := G) μ) =
      PMF.map (legalPureProfileRestrictReachable (G := G))
        (Math.PMFProduct.pmfPi μ) := by
  classical
  change Math.PMFProduct.pmfPi
      (fun i => PMF.map
        (fun σ : G.LegalPureStrategy i => σ.restrictReachable) (μ i)) =
    PMF.map
      (fun π => fun i => (π i).restrictReachable)
      (Math.PMFProduct.pmfPi μ)
  exact (Math.PMFProduct.pmfPi_push_coordwise μ
    (fun i σ => σ.restrictReachable)).symm

/-- Extending the reachable restriction of a total legal pure profile is
run-equivalent to the original total pure profile. -/
theorem legalPureProfileRestrictReachable_extend_runDist
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    [DecidablePred G.terminal]
    (π : G.LegalPureProfile) (k : Nat) :
    G.runDist k
        (G.legalPureToBehavioral
          ((legalPureProfileRestrictReachable (G := G) π).extend)) =
      G.runDist k (G.legalPureToBehavioral π) := by
  apply G.runDist_congr
  intro h i
  change PMF.pure
      (((legalPureProfileRestrictReachable (G := G) π).extend.toProfile i)
        (h.playerView i)) =
    PMF.pure (π.toProfile i (h.playerView i))
  congr 1
  change ((π i).restrictReachable).1.extend (h.playerView i) =
    (π i).1 (h.playerView i)
  exact ReachablePureStrategy.extend_apply_history
    (G := G) ((π i).restrictReachable).1 h

theorem legalBehavioralProfileRestrictReachable_extend_runDist
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    [DecidablePred G.terminal]
    (β : G.LegalBehavioralProfile) (k : Nat) :
    G.runDist k (legalBehavioralProfileRestrictReachable (G := G) β).extend =
      G.runDist k β := by
  apply G.runDist_congr
  intro h i
  change (((β i).restrictReachable).1.extend (h.playerView i)) =
    (β i).1 (h.playerView i)
  exact ReachableBehavioralStrategy.extend_apply_history
    (G := G) ((β i).restrictReachable).1 h

open Classical in
/-- Native total FOSG form of the legal M→B theorem.

An independent mixed profile over total legal pure strategies is realized by a
total legal behavioral profile with the same finite-horizon distribution over
FOSG histories. Internally the proof restricts to reachable information states,
uses `reachable_mixed_to_legal_behavioral_runDist`, and extends the behavioral
witness back to the ordinary total FOSG strategy space. -/
theorem mixed_legalPure_to_legalBehavioral_runDist
    [Fintype ι] [Finite G.History]
    [∀ i, Fintype (Option (Act i))] [DecidablePred G.terminal]
    [∀ i, Finite (G.LegalPureStrategy i)]
    (hLeg : G.LegalObservable)
    (μ : ∀ i, PMF (G.LegalPureStrategy i))
    (k : Nat) :
    ∃ β : G.LegalBehavioralProfile,
      G.runDist k β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun π => G.runDist k (G.legalPureToBehavioral π)) := by
  letI : ∀ i, Fintype (G.LegalPureStrategy i) :=
    fun i => Fintype.ofFinite (G.LegalPureStrategy i)
  let μR := legalPureMixedProfileRestrictReachable (G := G) μ
  obtain ⟨βR, hβR⟩ :=
    reachable_mixed_to_legal_behavioral_runDist
      (G := G) hLeg μR k
  refine ⟨βR.extend, ?_⟩
  rw [hβR]
  rw [legalPureMixedProfileRestrictReachable_joint (G := G) μ]
  rw [PMF.bind_map]
  congr
  funext π
  exact legalPureProfileRestrictReachable_extend_runDist (G := G) π k


end Kuhn

end FOSG

end GameTheory
