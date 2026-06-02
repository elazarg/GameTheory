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
import GameTheory.Languages.FOSG.Native.History

namespace GameTheory

namespace FOSG

namespace Kuhn

open ObsModelCoreBridge

attribute [local instance] Fintype.ofFinite

open scoped BigOperators

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
variable (G : FOSG ι W Act PrivObs PubObs)


/-- Native-history pure profile for the FOSG Kuhn semantics. -/
abbrev HistoryPureProfile : Type :=
  (toHistoryObsModelCore G).PureProfile

/-- Native-history behavioral profile for the FOSG Kuhn semantics. -/
abbrev HistoryBehavioralProfile : Type :=
  (toHistoryObsModelCore G).BehavioralProfile

/-- Lift a native FOSG pure strategy into the native-history Kuhn model. -/
noncomputable def liftHistoryPureStrategy
    (i : ι) (π : PureStrategy (G := G) i) :
    (toHistoryObsModelCore G).LocalStrategy i := by
  intro v
  exact π v

/-- Lift a native FOSG pure profile into the native-history Kuhn model. -/
noncomputable def liftHistoryPureProfile
    (π : _root_.GameTheory.FOSG.PureProfile G) :
    HistoryPureProfile (G := G) :=
  fun i => liftHistoryPureStrategy (G := G) i (π i)

/-- Lift a native independent mixed profile into the native-history Kuhn model. -/
noncomputable def liftHistoryMixedProfile
    (μ : MixedProfile (G := G)) : ∀ i, PMF ((toHistoryObsModelCore G).LocalStrategy i) :=
  fun i => Math.ProbabilityMassFunction.pushforward (μ i) (liftHistoryPureStrategy (G := G) i)

/-- Product sampling commutes with the native-to-history-core pure-profile lift. -/
theorem liftHistoryMixedProfile_joint
    [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Option (Act i))]
    (μ : MixedProfile (G := G)) :
    Math.PMFProduct.pmfPi (liftHistoryMixedProfile (G := G) μ) =
      Math.ProbabilityMassFunction.pushforward
        (mixedProfileJoint (G := G) μ) (liftHistoryPureProfile (G := G)) := by
  classical
  rw [mixedProfileJoint]
  change Math.PMFProduct.pmfPi
      (fun i => Math.ProbabilityMassFunction.pushforward
        (μ i) (liftHistoryPureStrategy (G := G) i)) =
    Math.ProbabilityMassFunction.pushforward (Math.PMFProduct.pmfPi μ)
      (fun π => fun i => liftHistoryPureStrategy (G := G) i (π i))
  exact (Math.PMFProduct.pmfPi_push_coordwise μ
    (fun i => liftHistoryPureStrategy (G := G) i)).symm

/-- Final native history extracted from a native-history Kuhn trace. -/
noncomputable def historyTraceLast
    (ss : List G.History) : G.History :=
  (toHistoryObsModelCore G).lastState ss

/-- Native final-history law induced by the history-state Kuhn execution model. -/
noncomputable def historyOutcomeDist
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (k : Nat) (β : HistoryBehavioralProfile (G := G)) : PMF G.History :=
  ((toHistoryObsModelCore G).runDist k β).bind
    (fun ss => PMF.pure (historyTraceLast (G := G) ss))

/-- Native final-history law induced by a pure profile in the history-state
Kuhn execution model. -/
noncomputable def historyOutcomeDistPure
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (k : Nat) (π : HistoryPureProfile (G := G)) : PMF G.History :=
  ((toHistoryObsModelCore G).runDistPure k π).bind
    (fun ss => PMF.pure (historyTraceLast (G := G) ss))

/-- FOSG-side name for step-mass invariance on the native-history Kuhn model. -/
abbrev HistoryStepMassInvariant
    [Fintype ι] [∀ i, Fintype (Option (Act i))] : Prop :=
  ObsModelCore.StepMassInvariant (toHistoryObsModelCore G)

/-- FOSG-side name for support factorization on the native-history Kuhn model. -/
abbrev HistoryStepSupportFactorization
    [Fintype ι] [∀ i, Fintype (Option (Act i))] : Prop :=
  ObsModelCore.StepSupportFactorization (toHistoryObsModelCore G)

/-- FOSG-side name for posterior locality on the native-history Kuhn model. -/
abbrev HistoryActionPosteriorLocal
    [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Option (Act i))]
    (i : ι) : Prop :=
  ObsModelCore.ActionPosteriorLocal (toHistoryObsModelCore G) i

open Classical in
/-- **Kuhn's theorem, mixed -> behavioral direction for FOSGs, native-history form.**

Every independent native mixed profile over FOSG pure strategies is realized by
a behavioral profile with the same final native-history law in the
history-state Kuhn semantics. -/
theorem mixed_to_behavioral_native_history
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hMass : HistoryStepMassInvariant (G := G))
    (hFactor : HistoryStepSupportFactorization (G := G))
    (hLocal : ∀ i, HistoryActionPosteriorLocal (G := G) i)
    (μ : MixedProfile (G := G))
    (k : Nat) :
    ∃ β : HistoryBehavioralProfile (G := G),
      historyOutcomeDist (G := G) k β =
        (mixedProfileJoint (G := G) μ).bind
          (fun π => historyOutcomeDistPure (G := G) k
            (liftHistoryPureProfile (G := G) π)) := by
  letI : ∀ i, Fintype ((toHistoryObsModelCore G).InfoState i) :=
    HistoryNative.historyInfoStateFintype (G := G)
  letI : ∀ i (o : G.InfoState i), Nonempty (Option (Act i)) := fun _ _ => ⟨none⟩
  obtain ⟨β, hβ⟩ :=
    ObsModelCore.kuhn_mixed_to_behavioral_semantic
      (O := toHistoryObsModelCore G)
      hMass hFactor hLocal (liftHistoryMixedProfile (G := G) μ) k
  refine ⟨β, ?_⟩
  unfold historyOutcomeDist historyOutcomeDistPure
  rw [hβ, PMF.bind_bind, liftHistoryMixedProfile_joint (G := G) μ]
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_map]
  rfl

/-- A lifted native pure profile has the same native-history outcome law as
its native pure behavioral profile. -/
@[simp] theorem historyOutcomeDistPure_liftHistoryPureProfile
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (k : Nat) (π : _root_.GameTheory.FOSG.PureProfile G) :
    historyOutcomeDistPure (G := G) k (liftHistoryPureProfile (G := G) π) =
      historyOutcomeDist (G := G) k (G.pureToBehavioral π) := by
  rfl

open Classical in
/-- **Kuhn's theorem, mixed -> behavioral direction for FOSGs.**

This is the native FOSG-facing M→B theorem.  Every independent mixed profile
over native per-player pure strategies is realized by a native behavioral
profile with the same final native-history law in the history-state Kuhn
semantics.  The core `ObsModelCore` construction is used only internally. -/
theorem mixed_to_behavioral
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hMass : HistoryStepMassInvariant (G := G))
    (hFactor : HistoryStepSupportFactorization (G := G))
    (hLocal : ∀ i, HistoryActionPosteriorLocal (G := G) i)
    (μ : MixedProfile (G := G))
    (k : Nat) :
    ∃ β : BehavioralProfile (G := G),
      historyOutcomeDist (G := G) k β =
        (mixedProfileJoint (G := G) μ).bind
          (fun π => historyOutcomeDist (G := G) k (G.pureToBehavioral π)) := by
  obtain ⟨β, hβ⟩ :=
    mixed_to_behavioral_native_history (G := G) hMass hFactor hLocal μ k
  refine ⟨β, ?_⟩
  simpa using hβ

open Classical in
/-- Pointwise native final-history form of FOSG Kuhn M→B. -/
theorem mixed_to_behavioral_historyProb
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hMass : HistoryStepMassInvariant (G := G))
    (hFactor : HistoryStepSupportFactorization (G := G))
    (hLocal : ∀ i, HistoryActionPosteriorLocal (G := G) i)
    (μ : MixedProfile (G := G))
    (k : Nat) :
    ∃ β : BehavioralProfile (G := G),
      ∀ h : G.History,
        historyOutcomeDist (G := G) k β h =
          ((mixedProfileJoint (G := G) μ).bind
            (fun π => historyOutcomeDist (G := G) k (G.pureToBehavioral π))) h := by
  obtain ⟨β, hβ⟩ :=
    mixed_to_behavioral (G := G) hMass hFactor hLocal μ k
  exact ⟨β, fun h => congrFun (congrArg DFunLike.coe hβ) h⟩

open Classical in
/-- Native finite-event form of FOSG Kuhn M→B for final histories. -/
theorem mixed_to_behavioral_historyMassOn
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hMass : HistoryStepMassInvariant (G := G))
    (hFactor : HistoryStepSupportFactorization (G := G))
    (hLocal : ∀ i, HistoryActionPosteriorLocal (G := G) i)
    (μ : MixedProfile (G := G))
    (k : Nat) (hs : Finset G.History) :
    ∃ β : BehavioralProfile (G := G),
      (∑ h ∈ hs, historyOutcomeDist (G := G) k β h) =
        ∑ h ∈ hs,
          ((mixedProfileJoint (G := G) μ).bind
            (fun π => historyOutcomeDist (G := G) k (G.pureToBehavioral π))) h := by
  obtain ⟨β, hβ⟩ :=
    mixed_to_behavioral_historyProb (G := G) hMass hFactor hLocal μ k
  refine ⟨β, ?_⟩
  refine Finset.sum_congr rfl ?_
  intro h hh
  exact hβ h

/-! ### Legal native mixed-to-behavioral witnesses -/

/-- A native mixed profile is legal when each player's mixed strategy supports
only legal pure strategies. -/
def IsLegalMixedProfile
    (μ : MixedProfile (G := G)) : Prop :=
  ∀ i (πi : PureStrategy (G := G) i),
    πi ∈ (μ i).support → G.IsLegalPureStrategy i πi

/-- A legal fallback behavioral profile, used only at information states that
are not reached by any pure profile in the core M→B construction. -/
noncomputable def legalFallbackBehavioral
    (_hLeg : G.LegalObservable) : BehavioralProfile (G := G) := by
  classical
  exact fun i v =>
    if h : ∃ oi : Option (Act i), oi ∈ G.availableMovesAtInfoState i v then
      PMF.pure h.choose
    else
      PMF.pure none

theorem legalFallbackBehavioral_isLegal
    (hLeg : G.LegalObservable) :
    G.IsLegalBehavioralProfile (legalFallbackBehavioral (G := G) hLeg) := by
  classical
  intro i h oi hoi
  unfold legalFallbackBehavioral at hoi
  have hex : ∃ oi : Option (Act i), oi ∈ G.availableMovesAtInfoState i (h.playerView i) := by
    rcases availableMoves_nonempty (G := G) h i with ⟨oi, hoi⟩
    exact ⟨oi, G.mem_availableMovesAtInfoState_of_history h hoi⟩
  rw [dif_pos hex] at hoi
  have hoi_eq : oi = hex.choose := by
    rw [PMF.mem_support_iff] at hoi
    by_contra hne
    apply hoi
    simp [PMF.pure_apply, hne]
  have hchosen : hex.choose ∈ G.availableMovesAtInfoState i (h.playerView i) :=
    hex.choose_spec
  have hEq := G.availableMovesAtInfoState_eq_of_history hLeg i h
  rw [hoi_eq]
  exact hEq ▸ hchosen

/-- Native FOSG M→B witness with a legal fallback at unreached information
states. -/
noncomputable def legalHistoryMixedToBehavioral
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (μ : MixedProfile (G := G)) :
    BehavioralProfile (G := G) :=
  ObsModelCore.mixedToBehavioralProfileWithFallback
    (O := toHistoryObsModelCore G)
    (liftHistoryMixedProfile (G := G) μ)
    (legalFallbackBehavioral (G := G) hLeg)

open Classical in
theorem legalHistoryMixedToBehavioral_historyOutcomeDist
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (hMass : HistoryStepMassInvariant (G := G))
    (hFactor : HistoryStepSupportFactorization (G := G))
    (hLocal : ∀ i, HistoryActionPosteriorLocal (G := G) i)
    (μ : MixedProfile (G := G))
    (k : Nat) :
    historyOutcomeDist (G := G) k (legalHistoryMixedToBehavioral (G := G) hLeg μ) =
      (mixedProfileJoint (G := G) μ).bind
        (fun π => historyOutcomeDist (G := G) k (G.pureToBehavioral π)) := by
  letI : ∀ i, Fintype ((toHistoryObsModelCore G).InfoState i) :=
    HistoryNative.historyInfoStateFintype (G := G)
  letI : ∀ i (o : G.InfoState i), Nonempty (Option (Act i)) := fun _ _ => ⟨none⟩
  have hβ :=
    ObsModelCore.mixedToBehavioralProfileWithFallback_runDist
      (O := toHistoryObsModelCore G)
      hMass hFactor hLocal (liftHistoryMixedProfile (G := G) μ)
      (legalFallbackBehavioral (G := G) hLeg) k
  unfold historyOutcomeDist legalHistoryMixedToBehavioral
  rw [hβ, PMF.bind_bind, liftHistoryMixedProfile_joint (G := G) μ]
  rw [Math.ProbabilityMassFunction.pushforward, PMF.bind_map]
  change (mixedProfileJoint (G := G) μ).bind
      (fun π => historyOutcomeDistPure (G := G) k (liftHistoryPureProfile (G := G) π)) =
    (mixedProfileJoint (G := G) μ).bind
      (fun π => historyOutcomeDist (G := G) k (G.pureToBehavioral π))
  congr 1

open Classical in
theorem legalHistoryMixedToBehavioral_isLegal
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (hLocal : ∀ i, HistoryActionPosteriorLocal (G := G) i)
    (μ : MixedProfile (G := G))
    (hμ : IsLegalMixedProfile (G := G) μ) :
    G.IsLegalBehavioralProfile (legalHistoryMixedToBehavioral (G := G) hLeg μ) := by
  letI : ∀ i, Fintype ((toHistoryObsModelCore G).InfoState i) :=
    HistoryNative.historyInfoStateFintype (G := G)
  intro i h oi hoi
  by_cases hex : ∃ (n : Nat) (ss : List G.History) (π₀ : HistoryPureProfile (G := G)),
      (toHistoryObsModelCore G).projectStates i ss = h.playerView i ∧
      Math.ParameterizedChain.pureRun
        ((toHistoryObsModelCore G).pureStep) (toHistoryObsModelCore G).init n π₀ ss ≠ 0
  · rcases hex with ⟨n, ss, π₀, hproj, hreach⟩
    have hEq :=
      ObsModelCore.mixedToBehavioralProfileWithFallback_eq_factorAt
        (O := toHistoryObsModelCore G) hLocal (liftHistoryMixedProfile (G := G) μ)
        (legalFallbackBehavioral (G := G) hLeg) i n ss π₀ hreach
    have hEq' :
        legalHistoryMixedToBehavioral (G := G) hLeg μ i (h.playerView i) =
          ObsModelCore.mixedToBehavioralFactorAt
            (O := toHistoryObsModelCore G) (liftHistoryMixedProfile (G := G) μ)
            i n ss π₀ := by
      have hEq'' := hEq
      rwa [hproj] at hEq''
    have hfactor :
        oi ∈ (ObsModelCore.mixedToBehavioralFactorAt
          (O := toHistoryObsModelCore G) (liftHistoryMixedProfile (G := G) μ)
          i n ss π₀).support := by
      rwa [hEq'] at hoi
    rcases Math.PMFProduct.pushforward_support_fibre
        (Math.ProbabilityMassFunction.reweightPMF (liftHistoryMixedProfile (G := G) μ i)
          (fun πᵢ => Math.ParameterizedChain.pureRun ((toHistoryObsModelCore G).pureStep)
            (toHistoryObsModelCore G).init n (Function.update π₀ i πᵢ) ss))
        (fun πᵢ => πᵢ ((toHistoryObsModelCore G).projectStates i ss)) oi hfactor with
      ⟨πiCore, hπiAction, hπiReweight⟩
    have hπiCoreSupp :
        πiCore ∈ (liftHistoryMixedProfile (G := G) μ i).support :=
      Math.ProbabilityMassFunction.reweightPMF_support_subset _ _ hπiReweight
    rcases Math.PMFProduct.pushforward_support_fibre
        (μ i) (liftHistoryPureStrategy (G := G) i) πiCore hπiCoreSupp with
      ⟨πi, hπiLift, hπiSupp⟩
    have hval : πi (h.playerView i) = oi := by
      have hact : πiCore ((toHistoryObsModelCore G).projectStates i ss) = oi := hπiAction
      rw [← hπiLift] at hact
      rw [hproj] at hact
      simpa [liftHistoryPureStrategy] using hact
    rw [← hval]
    exact hμ i πi hπiSupp h
  · have hfb :
        legalHistoryMixedToBehavioral (G := G) hLeg μ i (h.playerView i) =
          legalFallbackBehavioral (G := G) hLeg i (h.playerView i) := by
      unfold legalHistoryMixedToBehavioral ObsModelCore.mixedToBehavioralProfileWithFallback
      rw [dif_neg hex]
    rw [hfb] at hoi
    exact legalFallbackBehavioral_isLegal (G := G) hLeg i h hoi

open Classical in
/-- **Kuhn's theorem, mixed -> legal behavioral direction for FOSGs.**

If the independent native mixed profile supports only legal pure strategies,
then the native M→B behavioral witness is a legal behavioral profile. -/
theorem mixed_to_legal_behavioral
    [Fintype ι]
    [∀ i, Fintype (G.InfoState i)]
    [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    (hMass : HistoryStepMassInvariant (G := G))
    (hFactor : HistoryStepSupportFactorization (G := G))
    (hLocal : ∀ i, HistoryActionPosteriorLocal (G := G) i)
    (μ : MixedProfile (G := G))
    (hμ : IsLegalMixedProfile (G := G) μ)
    (k : Nat) :
    ∃ β : G.LegalBehavioralProfile,
      historyOutcomeDist (G := G) k β.toProfile =
        (mixedProfileJoint (G := G) μ).bind
          (fun π => historyOutcomeDist (G := G) k (G.pureToBehavioral π)) := by
  let βraw := legalHistoryMixedToBehavioral (G := G) hLeg μ
  have hβlegal : G.IsLegalBehavioralProfile βraw :=
    legalHistoryMixedToBehavioral_isLegal (G := G) hLeg hLocal μ hμ
  let β : G.LegalBehavioralProfile := fun i => ⟨βraw i, hβlegal i⟩
  refine ⟨β, ?_⟩
  change historyOutcomeDist (G := G) k βraw = _
  exact legalHistoryMixedToBehavioral_historyOutcomeDist
    (G := G) hLeg hMass hFactor hLocal μ k

/-! ### Legal reachable-history mixed-to-behavioral witnesses -/

/-- Legal optional moves at a reachable information state.

This is the canonical local action carrier for bounded-history FOSG Kuhn
semantics: strategic actions are exactly FOSG moves available at the player's
current reachable information state. -/
abbrev ReachableInfoLegalMove
    (G : FOSG ι W Act PrivObs PubObs) (i : ι)
    (s : G.ReachableInfoState i) : Type :=
  { oi : Option (Act i) // oi ∈ G.availableMovesAtInfoState i s.1 }

theorem reachable_availableMoves_nonempty
    (h : G.History) (i : ι) :
    ∃ oi : Option (Act i), oi ∈ G.availableMoves h i := by
  exact availableMoves_nonempty (G := G) h i

/-- Default legal move at a reachable information state. Used only as the
fallback at unreached strategic states in the generic core construction. -/
noncomputable def reachableInfoLegalMoveDefault
    (G : FOSG ι W Act PrivObs PubObs) (i : ι)
    (s : G.ReachableInfoState i) :
    ReachableInfoLegalMove G i s := by
  classical
  let h := s.2.choose
  have hs : h.playerView i = s.1 := by
    simpa [h] using s.2.choose_spec
  let oi := Classical.choose (reachable_availableMoves_nonempty (G := G) h i)
  have hoi : oi ∈ G.availableMoves h i :=
    Classical.choose_spec (reachable_availableMoves_nonempty (G := G) h i)
  refine ⟨oi, ?_⟩
  have hat : oi ∈ G.availableMovesAtInfoState i (h.playerView i) :=
    G.mem_availableMovesAtInfoState_of_history h hoi
  simpa [hs] using hat

/-- Independent mixed profile over legal reachable pure strategies. This is the
finite strategy space for bounded-history FOSGs whose full `InfoState` type need
not be finite. The legality is in the carrier, not an external support
predicate. -/
abbrev ReachableMixedProfile : Type :=
  ∀ i, PMF (G.ReachableLegalPureStrategy i)

noncomputable instance reachableLegalPureStrategyFintype
    [Fintype G.History] [Fintype (Option (Act i))] :
    Fintype (G.ReachableLegalPureStrategy i) := by
  classical
  dsimp [_root_.GameTheory.FOSG.ReachableLegalPureStrategy,
    _root_.GameTheory.FOSG.ReachablePureStrategy]
  infer_instance

noncomputable instance reachableInfoStateDecidableEq
    [Fintype G.History] (i : ι) : DecidableEq (G.ReachableInfoState i) :=
  Classical.decEq _

/-- Joint law induced by a reachable independent mixed profile. -/
noncomputable abbrev reachableMixedProfileJoint
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (μ : ReachableMixedProfile (G := G)) :
    PMF (_root_.GameTheory.FOSG.ReachableLegalPureProfile G) :=
  Math.PMFProduct.pmfPi μ

/-- Legal reachable-history Kuhn execution model.

The machine state is a realized FOSG history and the strategic observations are
reachable FOSG information states. Local actions are legal-move subtypes at the
current reachable information state, so illegal FOSG moves are not represented
as strategic actions. Terminal histories are absorbing because no legal FOSG
transition exists there. -/
noncomputable def toReachableHistoryObsModelCore
    (G : FOSG ι W Act PrivObs PubObs) (hLeg : G.LegalObservable) :
    ObsModelCore ι G.History (fun i => G.ReachableInfoState i)
      (fun i s => ReachableInfoLegalMove G i s) where
  infoState := fun _ => InfoStateCore.identity _
  observe := fun i h => G.reachableInfoStateOfHistory i h
  machine :=
    { init := History.nil G
      step := fun h a => by
        classical
        by_cases hterm : G.terminal h.lastState
        · exact PMF.pure h
        · let raw : JointAction Act := fun i => (a i).1
          have hraw : G.legal h.lastState raw := by
            rw [G.legal_iff_forall]
            refine ⟨hterm, ?_⟩
            intro i
            have haiInfo :
                (a i).1 ∈ G.availableMovesAtInfoState i
                  (G.reachableInfoStateOfHistory i h).1 := (a i).2
            have hai : (a i).1 ∈ G.availableMoves h i := by
              have hEq := G.availableMovesAtInfoState_eq_of_history hLeg i h
              exact hEq ▸ haiInfo
            simpa [FOSG.mem_availableMoves_iff] using hai
          exact (G.transition h.lastState ⟨raw, hraw⟩).map
            (fun dst => h.extendByOutcome ⟨raw, hraw⟩ dst) }

namespace ReachableHistoryNative

variable (G : FOSG ι W Act PrivObs PubObs)

noncomputable instance reachableHistoryInfoStateFintype
    [Fintype G.History] (hLeg : G.LegalObservable) :
    ∀ i, Fintype ((toReachableHistoryObsModelCore G hLeg).InfoState i) := by
  intro i
  simpa [toReachableHistoryObsModelCore, ObsModelCore.InfoState] using
    (inferInstance : Fintype (G.ReachableInfoState i))

noncomputable instance reachableInfoLegalMoveFintype
    [∀ i, Fintype (Option (Act i))]
    (i : ι) (s : G.ReachableInfoState i) :
    Fintype (ReachableInfoLegalMove G i s) := by
  classical
  dsimp [ReachableInfoLegalMove]
  infer_instance

noncomputable instance reachableHistoryLocalStrategyFintype
    [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) :
    ∀ i, Fintype ((toReachableHistoryObsModelCore G hLeg).LocalStrategy i) := by
  intro i
  dsimp [ObsModelCore.LocalStrategy]
  infer_instance

end ReachableHistoryNative

end Kuhn

end FOSG

end GameTheory
