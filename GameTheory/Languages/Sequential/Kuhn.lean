import GameTheory.Languages.Sequential.Compile
import GameTheory.Model.Lemmas.HistoryCover
import GameTheory.Theorems.Kuhn

/-!
# GameTheory.Languages.Sequential.Kuhn

Kuhn reduction lemmas for compiled sequential protocols.

This file is intentionally thin. It packages the structural equivalence between
native protocol SOS and the compiled `InfoModel` presentation, so later ports of
Kuhn/Zermelo-style theorems can depend on one semantic interface.
-/

namespace GameTheory.Languages.Sequential

open GameTheory.Sequential
open GameTheory.Theorems

variable {n : Nat} {S V A Sig : Type}

/-- Finite public-phase alphabet relevant to a concrete protocol. -/
noncomputable def publicPhaseAlphabet
    (G : GameTheory.Protocol n S V A Sig) : Finset PublicPhase :=
  ((Finset.range G.rounds.length).biUnion fun k =>
    ({PublicPhase.signal k, PublicPhase.action k} : Finset PublicPhase)) ∪
    {PublicPhase.terminal}

/-- Canonical finite local-history cover for compiled sequential protocols up to
depth `k`, assuming a finite view alphabet. -/
noncomputable def canonicalHistoryCover
    (G : GameTheory.Protocol n S V A Sig)
    [Fintype V]
    (k : Nat) :
    ∀ i, Finset ((compileInfoOn G).LocalTrace i) := by
  classical
  intro i
  exact
    ((InfoModel.listsUpToLength (publicPhaseAlphabet G) (k + 1)).product
      (InfoModel.listsUpToLength (Finset.univ : Finset (Option V)) (k + 1))).image
      (fun p => (p.1, p.2))

private inductive ValidConfig (G : GameTheory.Protocol n S V A Sig) :
    Config G → Prop where
  | signal (k : Nat) (s : S) :
      G.rounds[k]? ≠ none → ValidConfig G (.signal k s)
  | action (k : Nat) (s : S) (sig : JointSignal n Sig) :
      G.rounds[k]? ≠ none → ValidConfig G (.action k s sig)
  | terminal (s : S) : ValidConfig G (.terminal s)

private theorem initialConfig_valid (G : GameTheory.Protocol n S V A Sig) :
    ValidConfig G (initialConfig G) := by
  unfold initialConfig
  by_cases h0 : G.rounds[0]? = none
  · simpa [h0] using (ValidConfig.terminal (G := G) G.init)
  · simpa [h0] using (ValidConfig.signal (G := G) 0 G.init h0)

private theorem validConfig_of_step
    (G : GameTheory.Protocol n S V A Sig)
    {a : JointControl n A} {src dst : Config G}
    (h : Step G a src dst) :
    ValidConfig G dst := by
  cases h with
  | sample hRound _ =>
      exact ValidConfig.action _ _ _ (by simp [hRound])
  | act_more _ _ hNext =>
      exact ValidConfig.signal _ _ (by simp [hNext])
  | act_last _ _ hLast =>
      exact ValidConfig.terminal _

private theorem mem_valid_of_reachStateTrace
    (G : GameTheory.Protocol n S V A Sig)
    {ss : List (Config G)}
    (hr : Semantics.SM.ReachStateTrace (compileInfoOn G).toSM ss) :
    ∀ c ∈ ss, ValidConfig G c := by
  let rec go
      {ss : List (Config G)}
      (hr : Semantics.SM.ReachStateTrace (compileInfoOn G).toSM ss) :
      ∀ c ∈ ss, ValidConfig G c :=
    match hr with
    | .nil => by
        intro c hc
        have hc' : c = initialConfig G := by simpa using hc
        subst hc'
        exact initialConfig_valid G
    | .snoc hr' _ hstep => by
        intro c hc
        rw [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact go hr' c hc
        · exact validConfig_of_step G hstep
  exact go hr

private theorem publicPhase_mem_alphabet_of_valid
    (G : GameTheory.Protocol n S V A Sig)
    {c : Config G}
    (hc : ValidConfig G c) :
    publicPhase c ∈ publicPhaseAlphabet G := by
  classical
  cases hc with
  | signal k s hk =>
      rcases Option.ne_none_iff_exists'.mp hk with ⟨r, hr⟩
      have hklt : k < G.rounds.length := by
        exact (List.getElem?_eq_some_iff.mp hr).1
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨k, Finset.mem_range.mpr hklt, ?_⟩
      simp
  | action k s sig hk =>
      rcases Option.ne_none_iff_exists'.mp hk with ⟨r, hr⟩
      have hklt : k < G.rounds.length := by
        exact (List.getElem?_eq_some_iff.mp hr).1
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨k, Finset.mem_range.mpr hklt, ?_⟩
      simp
  | terminal s =>
      apply Finset.mem_union_right
      simp

/-- The canonical bounded-history cover is sufficient for the compiled
sequential protocol up to horizon `k`. -/
theorem canonicalHistoryCover_spec
    (G : GameTheory.Protocol n S V A Sig)
    [Fintype V]
    (k : Nat) :
    (compileInfoOn G).CoversHistoriesUpTo (canonicalHistoryCover G k) k := by
  classical
  intro i ss hr hlen
  have hvalid : ∀ c ∈ ss, ValidConfig G c :=
    mem_valid_of_reachStateTrace G hr
  apply Finset.mem_image.mpr
  refine ⟨((compileInfoOn G).projectPublic ss, (compileInfoOn G).projectPrivate i ss), ?_, rfl⟩
  simp only [compileInfoOn, InfoModel.projectPublic, InfoModel.projectPrivate]
  refine Finset.mem_product.mpr ?_
  refine ⟨?_, ?_⟩
  · apply InfoModel.mem_listsUpToLength_of_forall_mem
    · simpa using hlen
    · intro x hx
      rcases List.mem_map.mp hx with ⟨c, hc, rfl⟩
      exact publicPhase_mem_alphabet_of_valid G (hvalid c hc)
  · apply InfoModel.mem_listsUpToLength_of_forall_mem
    · simpa [InfoModel.projectPrivate] using hlen
    · intro x hx
      exact Finset.mem_univ x

/-- The compiled protocol machine has exactly the native SOS transition relation. -/
theorem step_iff
    (G : GameTheory.Protocol n S V A Sig)
    (a : JointControl n A)
    (src dst : Config G) :
    (compileInfoOn G).step a src dst ↔ Step G a src dst :=
  compile_step_iff G a src dst

/-- Reachability in the compiled machine is exactly native SOS reachability. -/
theorem reach_iff
    (G : GameTheory.Protocol n S V A Sig)
    (ha : List (JointControl n A))
    (src dst : Config G) :
    Semantics.Transition.ReachBy (compileInfoOn G).step ha src dst ↔
      ReachBy G ha src dst :=
  compile_reach_iff G ha src dst

/-- The compiled information model exposes the native public phase. -/
theorem publicView_eq
    (G : GameTheory.Protocol n S V A Sig)
    (c : Config G) :
    (compileInfoOn G).publicView c = publicPhase c :=
  compile_publicView_eq_publicPhase G c

/-- The compiled information model exposes the native local observation. -/
theorem observe_eq
    (G : GameTheory.Protocol n S V A Sig)
    (i : Fin n) (c : Config G) :
    (compileInfoOn G).observe i c = observe G i c :=
  compile_observe_eq_observe G i c

/-- The remaining finite-horizon language-specific obligation for the restricted
Kuhn reduction: a finite local-history cover for the compiled protocol up to
horizon `k`. -/
abbrev compiledHistoryCover
    (G : GameTheory.Protocol n S V A Sig)
    (k : Nat)
    (H : ∀ i, Finset ((compileInfoOn G).LocalTrace i)) : Prop :=
  (compileInfoOn G).CoversHistoriesUpTo H k

/-- Ambient full-history mixed-to-behavioral Kuhn reduction for the compiled
sequential semantics.

This is the honest reduction boundary currently available: once a sequential
protocol has been compiled into an `InfoModel` together with a stochastic
`Execution.Dynamics`, the generic mixed-to-behavioral theorem applies directly
under the same finiteness and perfect-recall obligations required by the
generic theorem. -/
theorem kuhn_mixed_to_behavioral_of_compiled_fullTraceFinite
    (G : GameTheory.Protocol n S V A Sig)
    (D : Execution.Dynamics (compileInfoOn G))
    (k : Nat)
    [∀ i, Finite ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := compileInfoOn G) i)]
    [Fintype (Option A)]
    (hPR : (compileInfoOn G).PerfectRecall) :
    KuhnMixedToBehavioralViaOutcome
      (Execution.BehavioralProfile (compileInfoOn G))
      (InfoModel.MixedProfile (I := compileInfoOn G))
      (Execution.PureProfile (compileInfoOn G))
      (compileInfoOn G).Outcome
      (InfoModel.mixedJoint (I := compileInfoOn G))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  simpa using
    (GameTheory.Theorems.kuhn_mixed_to_behavioral
      (I := compileInfoOn G) (D := D) (k := k) hPR)

/-- Ambient full-history Kuhn reduction for the compiled sequential semantics.

This packages the generic `InfoModel` Kuhn theorem without adding any
language-specific proof burden beyond supplying the compiled dynamics and the
generic theorem's own finiteness/perfect-recall hypotheses. -/
theorem kuhn_complete_of_compiled_fullTraceFinite
    (G : GameTheory.Protocol n S V A Sig)
    (D : Execution.Dynamics (compileInfoOn G))
    (k : Nat)
    [∀ i, Fintype ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := compileInfoOn G) i)]
    [Fintype (Option A)]
    (hPR : (compileInfoOn G).PerfectRecall) :
    KuhnCompleteViaOutcome
      (Execution.BehavioralProfile (compileInfoOn G))
      (InfoModel.MixedProfile (I := compileInfoOn G))
      (Execution.PureProfile (compileInfoOn G))
      (compileInfoOn G).Outcome
      (mixedOfBehavioralCanonical (I := compileInfoOn G))
      (InfoModel.mixedJoint (I := compileInfoOn G))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  simpa using
    (GameTheory.Theorems.kuhn_complete
      (I := compileInfoOn G) (D := D) (k := k) hPR)

/-- Restricted finite-cover mixed-to-behavioral reduction for compiled
sequential protocols. This is the honest generic reduction boundary for finite
horizons: one supplies a finite local-history cover `H` and step-independence on
the restricted profile space, rather than pretending the ambient `List × List`
history type is finite. -/
theorem kuhn_mixed_to_behavioral_of_compiled_restricted
    (G : GameTheory.Protocol n S V A Sig)
    (D : Execution.Dynamics (compileInfoOn G))
    (k : Nat)
    (H : ∀ i, Finset ((compileInfoOn G).LocalTrace i))
    [∀ i, DecidableEq ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype ((compileInfoOn G).RestrictedLocalCoord H i)]
    [∀ i, Fintype ((compileInfoOn G).RestrictedLocalPure H i)]
    [Fintype (Option A)]
    (hStepIndep : ∀ μ n, (compileInfoOn G).RestrictedStepIndependence D H μ n) :
    KuhnMixedToBehavioralViaOutcome
      ((compileInfoOn G).RestrictedBehavioralProfile H)
      ((compileInfoOn G).RestrictedMixedProfile H)
      ((compileInfoOn G).RestrictedPureProfile H)
      (compileInfoOn G).Outcome
      ((compileInfoOn G).restrictedMixedJointRaw H)
      (GameTheory.Theorems.evalRestrictedBehavioral (I := compileInfoOn G) D k H)
      (GameTheory.Theorems.evalRestrictedPure (I := compileInfoOn G) D k H) := by
  simpa using
    (GameTheory.Theorems.kuhn_mixed_to_behavioral_restricted
      (I := compileInfoOn G) (D := D) (k := k) H hStepIndep)

/-- Cover-based mixed-to-behavioral Kuhn reduction for compiled sequential
protocols. This lifts the restricted finite-cover theorem back to ordinary
compiled profiles using the generic cover invariance layer. -/
theorem kuhn_mixed_to_behavioral_of_compiled_via_cover
    (G : GameTheory.Protocol n S V A Sig)
    (D : Execution.Dynamics (compileInfoOn G))
    (k : Nat)
    (H : ∀ i, Finset ((compileInfoOn G).LocalTrace i))
    [∀ i, DecidableEq ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype ((compileInfoOn G).RestrictedLocalCoord H i)]
    [∀ i, Fintype ((compileInfoOn G).RestrictedLocalPure H i)]
    [∀ i, Finite ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := compileInfoOn G) i)]
    [Fintype (Option A)]
    (hCover : compiledHistoryCover G k H)
    (hStepIndep : ∀ μ n, (compileInfoOn G).RestrictedStepIndependence D H μ n) :
    KuhnMixedToBehavioralViaOutcome
      (Execution.BehavioralProfile (compileInfoOn G))
      (InfoModel.MixedProfile (I := compileInfoOn G))
      (Execution.PureProfile (compileInfoOn G))
      (compileInfoOn G).Outcome
      (InfoModel.mixedJoint (I := compileInfoOn G))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  simpa [compiledHistoryCover] using
    (GameTheory.Theorems.kuhn_mixed_to_behavioral_via_cover
      (I := compileInfoOn G) (D := D) (k := k) H hCover hStepIndep)

/-- Restricted finite-cover Kuhn reduction for compiled sequential protocols. -/
theorem kuhn_complete_of_compiled_restricted
    (G : GameTheory.Protocol n S V A Sig)
    (D : Execution.Dynamics (compileInfoOn G))
    (k : Nat)
    (H : ∀ i, Finset ((compileInfoOn G).LocalTrace i))
    [∀ i, DecidableEq ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype ((compileInfoOn G).RestrictedLocalCoord H i)]
    [∀ i, Fintype ((compileInfoOn G).RestrictedLocalPure H i)]
    [Fintype (Option A)]
    (hStepIndep : ∀ μ n, (compileInfoOn G).RestrictedStepIndependence D H μ n) :
    KuhnCompleteViaOutcome
      ((compileInfoOn G).RestrictedBehavioralProfile H)
      ((compileInfoOn G).RestrictedMixedProfile H)
      ((compileInfoOn G).RestrictedPureProfile H)
      (compileInfoOn G).Outcome
      (GameTheory.Theorems.mixedOfBehavioralCanonicalRestricted (I := compileInfoOn G) H)
      ((compileInfoOn G).restrictedMixedJointRaw H)
      (GameTheory.Theorems.evalRestrictedBehavioral (I := compileInfoOn G) D k H)
      (GameTheory.Theorems.evalRestrictedPure (I := compileInfoOn G) D k H) := by
  simpa using
    (GameTheory.Theorems.kuhn_complete_restricted
      (I := compileInfoOn G) (D := D) (k := k) H hStepIndep)

/-- Cover-based full Kuhn reduction for compiled sequential protocols. -/
theorem kuhn_complete_of_compiled_via_cover
    (G : GameTheory.Protocol n S V A Sig)
    (D : Execution.Dynamics (compileInfoOn G))
    (k : Nat)
    (H : ∀ i, Finset ((compileInfoOn G).LocalTrace i))
    [∀ i, DecidableEq ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype ((compileInfoOn G).RestrictedLocalCoord H i)]
    [∀ i, Fintype ((compileInfoOn G).RestrictedLocalPure H i)]
    [∀ i, Finite ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := compileInfoOn G) i)]
    [Fintype (Option A)]
    (hCover : compiledHistoryCover G k H)
    (hStepIndep : ∀ μ n, (compileInfoOn G).RestrictedStepIndependence D H μ n) :
    KuhnCompleteViaOutcome
      (Execution.BehavioralProfile (compileInfoOn G))
      (InfoModel.MixedProfile (I := compileInfoOn G))
      (Execution.PureProfile (compileInfoOn G))
      (compileInfoOn G).Outcome
      (mixedOfBehavioralCanonical (I := compileInfoOn G))
      (InfoModel.mixedJoint (I := compileInfoOn G))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  simpa [compiledHistoryCover] using
    (GameTheory.Theorems.kuhn_complete_via_cover
      (I := compileInfoOn G) (D := D) (k := k) H hCover hStepIndep)

/-- Canonical-cover mixed-to-behavioral reduction for compiled sequential
protocols. The finite cover is the bounded list-enumeration built from the
finite public-phase alphabet and the finite view alphabet. -/
theorem kuhn_mixed_to_behavioral_of_compiled
    (G : GameTheory.Protocol n S V A Sig)
    [Fintype V]
    (D : Execution.Dynamics (compileInfoOn G))
    (k : Nat)
    [∀ i, DecidableEq ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype ((compileInfoOn G).RestrictedLocalCoord (canonicalHistoryCover G k) i)]
    [∀ i, Fintype ((compileInfoOn G).RestrictedLocalPure (canonicalHistoryCover G k) i)]
    [∀ i, Finite ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := compileInfoOn G) i)]
    [Fintype (Option A)]
    (hStepIndep :
      ∀ μ n,
        (compileInfoOn G).RestrictedStepIndependence D (canonicalHistoryCover G k) μ n) :
    KuhnMixedToBehavioralViaOutcome
      (Execution.BehavioralProfile (compileInfoOn G))
      (InfoModel.MixedProfile (I := compileInfoOn G))
      (Execution.PureProfile (compileInfoOn G))
      (compileInfoOn G).Outcome
      (InfoModel.mixedJoint (I := compileInfoOn G))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  exact kuhn_mixed_to_behavioral_of_compiled_via_cover
    (G := G) (D := D) (k := k) (H := canonicalHistoryCover G k)
    (hCover := canonicalHistoryCover_spec G k)
    hStepIndep

/-- Canonical-cover full Kuhn reduction for compiled sequential protocols. -/
theorem kuhn_complete_of_compiled
    (G : GameTheory.Protocol n S V A Sig)
    [Fintype V]
    (D : Execution.Dynamics (compileInfoOn G))
    (k : Nat)
    [∀ i, DecidableEq ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype ((compileInfoOn G).RestrictedLocalCoord (canonicalHistoryCover G k) i)]
    [∀ i, Fintype ((compileInfoOn G).RestrictedLocalPure (canonicalHistoryCover G k) i)]
    [∀ i, Finite ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype ((compileInfoOn G).LocalTrace i)]
    [∀ i, Fintype (InfoModel.LocalPure (I := compileInfoOn G) i)]
    [Fintype (Option A)]
    (hStepIndep :
      ∀ μ n,
        (compileInfoOn G).RestrictedStepIndependence D (canonicalHistoryCover G k) μ n) :
    KuhnCompleteViaOutcome
      (Execution.BehavioralProfile (compileInfoOn G))
      (InfoModel.MixedProfile (I := compileInfoOn G))
      (Execution.PureProfile (compileInfoOn G))
      (compileInfoOn G).Outcome
      (mixedOfBehavioralCanonical (I := compileInfoOn G))
      (InfoModel.mixedJoint (I := compileInfoOn G))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  exact kuhn_complete_of_compiled_via_cover
    (G := G) (D := D) (k := k) (H := canonicalHistoryCover G k)
    (hCover := canonicalHistoryCover_spec G k)
    hStepIndep

end GameTheory.Languages.Sequential
