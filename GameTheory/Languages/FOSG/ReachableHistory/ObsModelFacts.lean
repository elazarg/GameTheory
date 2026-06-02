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
import GameTheory.Languages.FOSG.ReachableHistory.Native

namespace GameTheory

namespace FOSG

namespace Kuhn

open ObsModelCoreBridge

attribute [local instance] Fintype.ofFinite

open scoped BigOperators

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
variable (G : FOSG ι W Act PrivObs PubObs)


/-- Native final-history law induced by the reachable-history Kuhn execution
model. -/
noncomputable def reachableHistoryOutcomeDist
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) (k : Nat)
    (β : (toReachableHistoryObsModelCore G hLeg).BehavioralProfile) :
    PMF G.History :=
  ((toReachableHistoryObsModelCore G hLeg).runDist k β).bind
    (fun ss => PMF.pure ((toReachableHistoryObsModelCore G hLeg).lastState ss))

/-- Native final-history law induced by a pure profile in the reachable-history
Kuhn execution model. -/
noncomputable def reachableHistoryOutcomeDistPure
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) (k : Nat)
    (π : (toReachableHistoryObsModelCore G hLeg).PureProfile) :
    PMF G.History :=
  ((toReachableHistoryObsModelCore G hLeg).runDistPure k π).bind
    (fun ss => PMF.pure ((toReachableHistoryObsModelCore G hLeg).lastState ss))

/-- Reachable FOSG-side name for step-mass invariance on the native-history
Kuhn model. -/
abbrev ReachableHistoryStepMassInvariant
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) : Prop :=
  ObsModelCore.StepMassInvariant (toReachableHistoryObsModelCore G hLeg)

/-- Reachable FOSG-side name for support factorization on the native-history
Kuhn model. -/
abbrev ReachableHistoryStepSupportFactorization
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) : Prop :=
  ObsModelCore.StepSupportFactorization (toReachableHistoryObsModelCore G hLeg)

/-- Reachable FOSG-side name for posterior locality on the native-history Kuhn
model. -/
abbrev ReachableHistoryActionPosteriorLocal
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) (i : ι) : Prop :=
  ObsModelCore.ActionPosteriorLocal (toReachableHistoryObsModelCore G hLeg) i

theorem reachableInfoLegalMove_eq_none_of_terminal
    (hLeg : G.LegalObservable) {h : G.History} (hterm : G.terminal h.lastState)
    (i : ι) (a : ReachableInfoLegalMove G i (G.reachableInfoStateOfHistory i h)) :
    a.1 = none := by
  have haiInfo :
      a.1 ∈ G.availableMovesAtInfoState i
        (G.reachableInfoStateOfHistory i h).1 := a.2
  have hai : a.1 ∈ G.availableMoves h i := by
    have hEq := G.availableMovesAtInfoState_eq_of_history hLeg i h
    exact hEq ▸ haiInfo
  have hactive : i ∉ G.active h.lastState := by
    rw [G.active_eq_empty_of_terminal hterm]
    simp
  cases ha : a.1 with
  | none => rfl
  | some ai =>
      have hloc : G.locallyLegalAtState h.lastState i (some ai) := by
        simpa [FOSG.mem_availableMoves_iff, ha] using hai
      exact False.elim (hactive hloc.1)

theorem reachableHistory_stepActionDeterminism
    (hLeg : G.LegalObservable) :
    ObsModelCore.StepActionDeterminism (toReachableHistoryObsModelCore G hLeg) := by
  classical
  intro h t a a' ha ha'
  by_cases hterm : G.terminal h.lastState
  · funext i
    apply Subtype.ext
    rw [reachableInfoLegalMove_eq_none_of_terminal (G := G) hLeg hterm i (a i),
      reachableInfoLegalMove_eq_none_of_terminal (G := G) hLeg hterm i (a' i)]
  · let raw : JointAction Act := fun i => (a i).1
    let raw' : JointAction Act := fun i => (a' i).1
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
      simpa [FOSG.mem_availableMoves_iff, raw] using hai
    have hraw' : G.legal h.lastState raw' := by
      rw [G.legal_iff_forall]
      refine ⟨hterm, ?_⟩
      intro i
      have haiInfo :
          (a' i).1 ∈ G.availableMovesAtInfoState i
            (G.reachableInfoStateOfHistory i h).1 := (a' i).2
      have hai : (a' i).1 ∈ G.availableMoves h i := by
        have hEq := G.availableMovesAtInfoState_eq_of_history hLeg i h
        exact hEq ▸ haiInfo
      simpa [FOSG.mem_availableMoves_iff, raw'] using hai
    have haMap : ((G.transition h.lastState ⟨raw, hraw⟩).map
        (fun dst => h.extendByOutcome ⟨raw, hraw⟩ dst)) t ≠ 0 := by
      have hstep :
          (toReachableHistoryObsModelCore G hLeg).step h a =
            (G.transition h.lastState ⟨raw, hraw⟩).map
              (fun dst => h.extendByOutcome ⟨raw, hraw⟩ dst) := by
        change (if hterm' : G.terminal h.lastState then PMF.pure h else
            (G.transition h.lastState ⟨(fun i => (a i).1), by
              change G.legal h.lastState raw
              exact hraw⟩).map
              (fun dst => h.extendByOutcome ⟨(fun i => (a i).1), by
                change G.legal h.lastState raw
                exact hraw⟩ dst)) =
          (G.transition h.lastState ⟨raw, hraw⟩).map
            (fun dst => h.extendByOutcome ⟨raw, hraw⟩ dst)
        rw [dif_neg hterm]
      rwa [← hstep]
    have ha'Map : ((G.transition h.lastState ⟨raw', hraw'⟩).map
        (fun dst => h.extendByOutcome ⟨raw', hraw'⟩ dst)) t ≠ 0 := by
      have hstep :
          (toReachableHistoryObsModelCore G hLeg).step h a' =
            (G.transition h.lastState ⟨raw', hraw'⟩).map
              (fun dst => h.extendByOutcome ⟨raw', hraw'⟩ dst) := by
        change (if hterm' : G.terminal h.lastState then PMF.pure h else
            (G.transition h.lastState ⟨(fun i => (a' i).1), by
              change G.legal h.lastState raw'
              exact hraw'⟩).map
              (fun dst => h.extendByOutcome ⟨(fun i => (a' i).1), by
                change G.legal h.lastState raw'
                exact hraw'⟩ dst)) =
          (G.transition h.lastState ⟨raw', hraw'⟩).map
            (fun dst => h.extendByOutcome ⟨raw', hraw'⟩ dst)
        rw [dif_neg hterm]
      rwa [← hstep]
    have haMem : t ∈ ((G.transition h.lastState ⟨raw, hraw⟩).map
        (fun dst => h.extendByOutcome ⟨raw, hraw⟩ dst)).support :=
      (PMF.mem_support_iff _ _).mpr haMap
    have ha'Mem : t ∈ ((G.transition h.lastState ⟨raw', hraw'⟩).map
        (fun dst => h.extendByOutcome ⟨raw', hraw'⟩ dst)).support :=
      (PMF.mem_support_iff _ _).mpr ha'Map
    rcases (PMF.mem_support_map_iff _ _ _).mp haMem with ⟨dst, hdst, ht⟩
    rcases (PMF.mem_support_map_iff _ _ _).mp ha'Mem with ⟨dst', hdst', ht'⟩
    have hsupp : G.transition h.lastState ⟨raw, hraw⟩ dst ≠ 0 := by
      simpa [PMF.mem_support_iff] using hdst
    have hsupp' : G.transition h.lastState ⟨raw', hraw'⟩ dst' ≠ 0 := by
      simpa [PMF.mem_support_iff] using hdst'
    have hsteps :
        (h.snoc ⟨raw, hraw⟩ dst hsupp).steps =
          (h.snoc ⟨raw', hraw'⟩ dst' hsupp').steps := by
      have htEq :
          h.snoc ⟨raw, hraw⟩ dst hsupp =
            h.snoc ⟨raw', hraw'⟩ dst' hsupp' := by
        calc
          h.snoc ⟨raw, hraw⟩ dst hsupp = t := by
            rw [← ht]
            exact (History.extendByOutcome_of_support
              (h := h) (a := ⟨raw, hraw⟩) (dst := dst) hsupp).symm
          _ = h.snoc ⟨raw', hraw'⟩ dst' hsupp' := by
            rw [← ht']
            exact History.extendByOutcome_of_support
              (h := h) (a := ⟨raw', hraw'⟩) (dst := dst') hsupp'
      exact congrArg History.steps htEq
    have hlast :
        (⟨h.lastState, ⟨raw, hraw⟩, dst, hsupp⟩ : G.Step) =
          ⟨h.lastState, ⟨raw', hraw'⟩, dst', hsupp'⟩ := by
      simpa using List.append_cancel_left hsteps
    have hrawEq : raw = raw' := by
      exact congrArg (fun e : G.Step => e.act.1) hlast
    funext i
    apply Subtype.ext
    exact congrFun hrawEq i

theorem reachableHistory_stepMassInvariant
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) :
    ReachableHistoryStepMassInvariant (G := G) hLeg :=
  (reachableHistory_stepActionDeterminism (G := G) hLeg).toMassInvariant

theorem reachableHistory_stepSupportFactorization
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) :
    ReachableHistoryStepSupportFactorization (G := G) hLeg :=
  (reachableHistory_stepActionDeterminism (G := G) hLeg).toSupportFactorization

theorem playerViewFrom_cons_eq_cons_view
    (i : ι) {e e' : G.Step} {es es' : List G.Step}
    (h :
      History.playerViewFrom (G := G) i (e :: es) =
        History.playerViewFrom (G := G) i (e' :: es')) :
    e.playerView i = e'.playerView i ∧
      History.playerViewFrom (G := G) i es =
        History.playerViewFrom (G := G) i es' := by
  unfold History.playerViewFrom at h
  unfold Step.playerView at h
  cases he : e.ownAction? i with
  | none =>
      cases he' : e'.ownAction? i with
      | none =>
          simp only [he, he', List.cons_append, List.nil_append, List.cons.injEq] at h
          exact ⟨by simp [Step.playerView, he, he', h.1], h.2⟩
      | some ai' =>
          simp only [he, he', List.cons_append, List.nil_append, List.cons.injEq] at h
          cases h.1
  | some ai =>
      cases he' : e'.ownAction? i with
      | none =>
          simp only [he, he', List.cons_append, List.nil_append, List.cons.injEq] at h
          cases h.1
      | some ai' =>
          simp only [he, he', List.cons_append, List.nil_append, List.cons.injEq] at h
          exact ⟨by simp [Step.playerView, he, he', h.1, h.2.1], h.2.2⟩

theorem playerViewFrom_cons_eq_cons_action
    (i : ι) {e e' : G.Step} {es es' : List G.Step}
    (h :
      History.playerViewFrom (G := G) i (e :: es) =
        History.playerViewFrom (G := G) i (e' :: es')) :
    e.ownAction? i = e'.ownAction? i ∧
      History.playerViewFrom (G := G) i es =
        History.playerViewFrom (G := G) i es' := by
  unfold History.playerViewFrom at h
  unfold Step.playerView at h
  cases he : e.ownAction? i with
  | none =>
      cases he' : e'.ownAction? i with
      | none =>
          simp only [he, he', List.cons_append, List.nil_append, List.cons.injEq] at h
          exact ⟨rfl, h.2⟩
      | some ai' =>
          simp only [he, he', List.cons_append, List.nil_append, List.cons.injEq] at h
          cases h.1
  | some ai =>
      cases he' : e'.ownAction? i with
      | none =>
          simp only [he, he', List.cons_append, List.nil_append, List.cons.injEq] at h
          cases h.1
      | some ai' =>
          simp only [he, he', List.cons_append, List.nil_append, List.cons.injEq] at h
          exact ⟨by cases h.1; rfl, h.2.2⟩

theorem playerViewFrom_cons_ne_nil
    (i : ι) (e : G.Step) (es : List G.Step) :
    History.playerViewFrom (G := G) i (e :: es) ≠ [] := by
  intro h
  have hpos : 0 < (History.playerViewFrom (G := G) i (e :: es)).length := by
    unfold History.playerViewFrom
    simp [Step.playerView_length_pos (G := G) e i]
  simp [h] at hpos

theorem playerViewFrom_append_singleton_ne_nil
    (i : ι) (es : List G.Step) (e : G.Step) :
    History.playerViewFrom (G := G) i (es ++ [e]) ≠ [] := by
  cases es with
  | nil =>
      simpa using playerViewFrom_cons_ne_nil (G := G) i e []
  | cons e₀ es =>
      simpa using playerViewFrom_cons_ne_nil (G := G) i e₀ (es ++ [e])

theorem playerViewFrom_append_singleton_eq
    (i : ι) {es es' : List G.Step} {e e' : G.Step}
    (h :
      History.playerViewFrom (G := G) i (es ++ [e]) =
        History.playerViewFrom (G := G) i (es' ++ [e'])) :
    History.playerViewFrom (G := G) i es =
        History.playerViewFrom (G := G) i es' ∧
      e.ownAction? i = e'.ownAction? i := by
  revert es'
  induction es with
  | nil =>
      intro es' h
      cases es' with
      | nil =>
          have h' :
              History.playerViewFrom (G := G) i (e :: []) =
                History.playerViewFrom (G := G) i (e' :: []) := by
            simpa using h
          have hres := playerViewFrom_cons_eq_cons_action (G := G) i h'
          exact ⟨rfl, hres.1⟩
      | cons e₀ es' =>
          have h' :
              History.playerViewFrom (G := G) i (e :: []) =
                History.playerViewFrom (G := G) i (e₀ :: (es' ++ [e'])) := by
            simpa using h
          have hres := playerViewFrom_cons_eq_cons_action (G := G) i h'
          exact False.elim
            (playerViewFrom_append_singleton_ne_nil (G := G) i es' e'
              (by simpa using hres.2.symm))
  | cons e₀ es ih =>
      intro es' h
      cases es' with
      | nil =>
          have h' :
              History.playerViewFrom (G := G) i (e₀ :: (es ++ [e])) =
                History.playerViewFrom (G := G) i (e' :: []) := by
            simpa using h
          have hres := playerViewFrom_cons_eq_cons_action (G := G) i h'
          exact False.elim
            (playerViewFrom_append_singleton_ne_nil (G := G) i es e
              (by simpa using hres.2))
      | cons e₀' es' =>
          have h' :
              History.playerViewFrom (G := G) i (e₀ :: (es ++ [e])) =
                History.playerViewFrom (G := G) i (e₀' :: (es' ++ [e'])) := by
            simpa using h
          have hres := playerViewFrom_cons_eq_cons_view (G := G) i h'
          have htail := ih (es' := es') hres.2
          exact ⟨by
            unfold History.playerViewFrom
            rw [hres.1, htail.1],
            htail.2⟩

theorem publicViewFrom_length (es : List G.Step) :
    (History.publicViewFrom (G := G) es).length = es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp [History.publicViewFrom, ih]

theorem publicView_length (h : G.History) :
    h.publicView.length = h.steps.length := by
  simpa [History.publicView] using publicViewFrom_length (G := G) h.steps

theorem reachableInfoLegalMove_eq_none_of_terminal_view_eq
    (hLeg : G.LegalObservable) {h h' : G.History} (hterm : G.terminal h.lastState)
    (i : ι) (hview : h.playerView i = h'.playerView i)
    (a' : ReachableInfoLegalMove G i (G.reachableInfoStateOfHistory i h')) :
    a'.1 = none := by
  have haiInfo :
      a'.1 ∈ G.availableMovesAtInfoState i
        (G.reachableInfoStateOfHistory i h').1 := a'.2
  have hai' : a'.1 ∈ G.availableMoves h' i := by
    have hEq := G.availableMovesAtInfoState_eq_of_history hLeg i h'
    exact hEq ▸ haiInfo
  have hEqMoves : G.availableMoves h i = G.availableMoves h' i :=
    G.availableMoves_eq_of_playerView_eq hLeg i hview
  have hai : a'.1 ∈ G.availableMoves h i := by
    exact hEqMoves.symm ▸ hai'
  have hactive : i ∉ G.active h.lastState := by
    rw [G.active_eq_empty_of_terminal hterm]
    simp
  cases ha : a'.1 with
  | none => rfl
  | some ai =>
      have hloc : G.locallyLegalAtState h.lastState i (some ai) := by
        simpa [FOSG.mem_availableMoves_iff, ha] using hai
      exact False.elim (hactive hloc.1)

theorem reachableInfoLegalMove_subsingleton_of_terminal
    (hLeg : G.LegalObservable) {h : G.History} (hterm : G.terminal h.lastState)
    (i : ι) :
    Subsingleton (ReachableInfoLegalMove G i (G.reachableInfoStateOfHistory i h)) := by
  refine ⟨fun a b => ?_⟩
  apply Subtype.ext
  rw [reachableInfoLegalMove_eq_none_of_terminal (G := G) hLeg hterm i a,
    reachableInfoLegalMove_eq_none_of_terminal (G := G) hLeg hterm i b]

theorem reachableHistory_projectStates_eq_last
    (hLeg : G.LegalObservable) (i : ι) (ss : List G.History) :
    (toReachableHistoryObsModelCore G hLeg).projectStates i ss =
      G.reachableInfoStateOfHistory i
        ((toReachableHistoryObsModelCore G hLeg).lastState ss) := by
  simpa [toReachableHistoryObsModelCore, ObsModelCore.currentObs] using
    (toReachableHistoryObsModelCore G hLeg).currentObs_projectStates i ss

theorem reachableInfoLegalMove_cast_val
    {i : ι} {s t : G.ReachableInfoState i} (h : s = t)
    (a : ReachableInfoLegalMove G i s) :
    ((h ▸ a : ReachableInfoLegalMove G i t).1) = a.1 := by
  cases h
  rfl

theorem reachableInfoLegalMove_cast_currentObs_val
    (hLeg : G.LegalObservable) {i : ι}
    {v v' : (toReachableHistoryObsModelCore G hLeg).InfoState i}
    (h : v = v')
    (a : ReachableInfoLegalMove G i
      ((toReachableHistoryObsModelCore G hLeg).currentObs i v')) :
    ((h ▸ a :
      ReachableInfoLegalMove G i
        ((toReachableHistoryObsModelCore G hLeg).currentObs i v)).1) = a.1 := by
  subst h
  rfl

theorem subst_heq_fosg {α : Type} {P : α → Type} {a b : α}
    (h : a = b) (x : P b) : HEq (h ▸ x : P a) x := by
  subst h
  rfl

theorem reachableHistory_castJointAction_val
    (hLeg : G.LegalObservable) (ss : List G.History)
    (a : ∀ i, ReachableInfoLegalMove G i
      ((toReachableHistoryObsModelCore G hLeg).currentObs i
        ((toReachableHistoryObsModelCore G hLeg).projectStates i ss)))
    (i : ι) :
    ((toReachableHistoryObsModelCore G hLeg).castJointAction ss a i).1 = (a i).1 := by
  change
    ((((toReachableHistoryObsModelCore G hLeg).currentObs_projectStates i ss) ▸ a i :
      ReachableInfoLegalMove G i
        ((toReachableHistoryObsModelCore G hLeg).observe i
          ((toReachableHistoryObsModelCore G hLeg).lastState ss))).1) = (a i).1
  exact reachableInfoLegalMove_cast_val (G := G)
    ((toReachableHistoryObsModelCore G hLeg).currentObs_projectStates i ss) (a i)

theorem projectActions_snoc_eq
    (h : G.History) (i : ι) (a : G.LegalAction h.lastState)
    (dst : W) (support : G.transition h.lastState a dst ≠ 0) :
    (h.snoc a dst support).projectActions i =
      h.projectActions i ++
        match a.1 i with
        | some ai => [ai]
        | none => [] := by
  cases ha : a.1 i with
  | none =>
      rw [History.projectActions, History.playerView_snoc, List.filterMap_append]
      have hstep :
          ((⟨h.lastState, a, dst, support⟩ : G.Step).playerView i) =
            [PlayerEvent.obs ((⟨h.lastState, a, dst, support⟩ : G.Step).privateObs i)
              (⟨h.lastState, a, dst, support⟩ : G.Step).publicObs] :=
        Step.playerView_of_none (G := G) _ i ha
      change h.projectActions i ++
          List.filterMap PlayerEvent.actionPart
            ((⟨h.lastState, a, dst, support⟩ : G.Step).playerView i) =
        h.projectActions i ++ []
      rw [hstep]
      simp [PlayerEvent.actionPart]
  | some ai =>
      rw [History.projectActions, History.playerView_snoc, List.filterMap_append]
      have hstep :
          ((⟨h.lastState, a, dst, support⟩ : G.Step).playerView i) =
            [PlayerEvent.act ai,
              PlayerEvent.obs ((⟨h.lastState, a, dst, support⟩ : G.Step).privateObs i)
                (⟨h.lastState, a, dst, support⟩ : G.Step).publicObs] :=
        Step.playerView_of_some (G := G) _ i ha
      change h.projectActions i ++
          List.filterMap PlayerEvent.actionPart
            ((⟨h.lastState, a, dst, support⟩ : G.Step).playerView i) =
        h.projectActions i ++ [ai]
      rw [hstep]
      simp [PlayerEvent.actionPart]

theorem sourceView_and_ownAction_eq_of_target_view_eq
    {h h' t t' : G.History}
    {raw : JointAction Act} {raw' : JointAction Act}
    {hraw : G.legal h.lastState raw} {hraw' : G.legal h'.lastState raw'}
    {dst dst' : W}
    {hsupp : G.transition h.lastState ⟨raw, hraw⟩ dst ≠ 0}
    {hsupp' : G.transition h'.lastState ⟨raw', hraw'⟩ dst' ≠ 0}
    (ht : t = h.snoc ⟨raw, hraw⟩ dst hsupp)
    (ht' : t' = h'.snoc ⟨raw', hraw'⟩ dst' hsupp')
    (i : ι)
    (hdst : t.playerView i = t'.playerView i) :
    h.playerView i = h'.playerView i ∧ raw i = raw' i := by
  rw [ht, ht'] at hdst
  let e : G.Step := ⟨h.lastState, ⟨raw, hraw⟩, dst, hsupp⟩
  let e' : G.Step := ⟨h'.lastState, ⟨raw', hraw'⟩, dst', hsupp'⟩
  have hview :
      History.playerViewFrom (G := G) i (h.steps ++ [e]) =
        History.playerViewFrom (G := G) i (h'.steps ++ [e']) := by
    simpa [History.playerView, History.snoc, e, e'] using hdst
  have hres := playerViewFrom_append_singleton_eq (G := G) i hview
  constructor
  · simpa [History.playerView] using hres.1
  · simpa [e, e', Step.ownAction?] using hres.2

theorem reachableHistory_pureStep_snoc
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    {π : (toReachableHistoryObsModelCore G hLeg).PureProfile}
    {ss : List G.History} {t : G.History}
    (hsrc : ¬ G.terminal
      ((toReachableHistoryObsModelCore G hLeg).lastState ss).lastState)
    (hstep : (toReachableHistoryObsModelCore G hLeg).pureStep π ss t ≠ 0) :
    ∃ (raw : JointAction Act)
      (hraw : G.legal
        ((toReachableHistoryObsModelCore G hLeg).lastState ss).lastState raw)
      (dst : W)
      (hsupp : G.transition
        ((toReachableHistoryObsModelCore G hLeg).lastState ss).lastState
          ⟨raw, hraw⟩ dst ≠ 0),
      (∀ j, raw j =
        ((toReachableHistoryObsModelCore G hLeg).castJointAction ss
          (fun j => π j ((toReachableHistoryObsModelCore G hLeg).projectStates j ss)) j).1) ∧
      t = ((toReachableHistoryObsModelCore G hLeg).lastState ss).snoc
        ⟨raw, hraw⟩ dst hsupp := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  let h : G.History := O.lastState ss
  let aStep : ∀ j, ReachableInfoLegalMove G j (G.reachableInfoStateOfHistory j h) :=
    O.castJointAction ss (fun j => π j (O.projectStates j ss))
  let raw : JointAction Act := fun j => (aStep j).1
  have hraw : G.legal h.lastState raw := by
    rw [G.legal_iff_forall]
    refine ⟨hsrc, ?_⟩
    intro j
    have hajInfo :
        (aStep j).1 ∈ G.availableMovesAtInfoState j
          (G.reachableInfoStateOfHistory j h).1 := (aStep j).2
    have haj : (aStep j).1 ∈ G.availableMoves h j := by
      have hEq := G.availableMovesAtInfoState_eq_of_history hLeg j h
      exact hEq ▸ hajInfo
    simpa [FOSG.mem_availableMoves_iff, raw] using haj
  have hstepO : O.step h aStep t ≠ 0 := by
    have h' := hstep
    rw [ObsModelCore.pureStep_eq] at h'
    simpa [O, h, aStep] using h'
  have hmap : ((G.transition h.lastState ⟨raw, hraw⟩).map
      (fun dst => h.extendByOutcome ⟨raw, hraw⟩ dst)) t ≠ 0 := by
    have hstepEq :
        O.step h aStep =
          (G.transition h.lastState ⟨raw, hraw⟩).map
            (fun dst => h.extendByOutcome ⟨raw, hraw⟩ dst) := by
      change (if hterm' : G.terminal h.lastState then PMF.pure h else
          (G.transition h.lastState ⟨(fun j => (aStep j).1), by
            change G.legal h.lastState raw
            exact hraw⟩).map
            (fun dst => h.extendByOutcome ⟨(fun j => (aStep j).1), by
              change G.legal h.lastState raw
              exact hraw⟩ dst)) =
        (G.transition h.lastState ⟨raw, hraw⟩).map
          (fun dst => h.extendByOutcome ⟨raw, hraw⟩ dst)
      rw [dif_neg hsrc]
    rwa [← hstepEq]
  have hmem : t ∈ ((G.transition h.lastState ⟨raw, hraw⟩).map
      (fun dst => h.extendByOutcome ⟨raw, hraw⟩ dst)).support :=
    (PMF.mem_support_iff _ _).mpr hmap
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with ⟨dst, hdst, ht⟩
  have hsupp : G.transition h.lastState ⟨raw, hraw⟩ dst ≠ 0 := by
    simpa [PMF.mem_support_iff] using hdst
  refine ⟨raw, hraw, dst, hsupp, ?_, ?_⟩
  · intro j
    rfl
  · rw [← ht]
    exact History.extendByOutcome_of_support
      (h := h) (a := ⟨raw, hraw⟩) (dst := dst) hsupp

theorem reachableHistory_source_nonterminal_of_target_nonterminal
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable)
    {π : (toReachableHistoryObsModelCore G hLeg).PureProfile}
    {ss : List G.History} {t : G.History}
    (hstep : (toReachableHistoryObsModelCore G hLeg).pureStep π ss t ≠ 0)
    (ht : ¬ G.terminal t.lastState) :
    ¬ G.terminal
      ((toReachableHistoryObsModelCore G hLeg).lastState ss).lastState := by
  classical
  intro hterm
  let O := toReachableHistoryObsModelCore G hLeg
  let h : G.History := O.lastState ss
  have hstepO : O.step h
      (O.castJointAction ss (fun j => π j (O.projectStates j ss))) t ≠ 0 := by
    have h' := hstep
    rw [ObsModelCore.pureStep_eq] at h'
    simpa [O, h] using h'
  have hpure : O.step h
      (O.castJointAction ss (fun j => π j (O.projectStates j ss))) = PMF.pure h := by
    change (if hterm' : G.terminal h.lastState then PMF.pure h else _) = PMF.pure h
    rw [dif_pos hterm]
  have htEq : t = h := by
    have htmem : t ∈ (PMF.pure h).support := by
      rw [← hpure]
      exact (PMF.mem_support_iff _ _).mpr hstepO
    simpa using htmem
  exact ht (by simpa [htEq, h] using hterm)

theorem reachableHistory_pureRun_last_steps_length_le
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) (n : Nat)
    {π : (toReachableHistoryObsModelCore G hLeg).PureProfile}
    {ss : List G.History}
    (h :
      Math.ParameterizedChain.pureRun
        ((toReachableHistoryObsModelCore G hLeg).pureStep)
        (toReachableHistoryObsModelCore G hLeg).init n π ss ≠ 0) :
    ((toReachableHistoryObsModelCore G hLeg).lastState ss).steps.length ≤ n := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  induction n generalizing ss with
  | zero =>
      have hss : ss = [O.init] := by
        by_contra hne
        exact h (by simp [Math.ParameterizedChain.pureRun,
          Math.TraceRun.traceRun, PMF.pure_apply, O, hne])
      rw [hss]
      rfl
  | succ m ih =>
      rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
      · exact absurd (Math.ParameterizedChain.pureRun_succ_nil _ _ _ _) h
      simp only [List.concat_eq_append] at h ⊢
      have hp :
          Math.ParameterizedChain.pureRun O.pureStep O.init m π p ≠ 0 := by
        exact left_ne_zero_of_mul
          (Math.ParameterizedChain.pureRun_succ_append O.pureStep O.init m π p t ▸ h)
      have ht : O.pureStep π p t ≠ 0 := by
        exact right_ne_zero_of_mul
          (Math.ParameterizedChain.pureRun_succ_append O.pureStep O.init m π p t ▸ h)
      have hplen : (O.lastState p).steps.length ≤ m := ih hp
      by_cases hterm : G.terminal (O.lastState p).lastState
      · have hstepO : O.step (O.lastState p)
            (O.castJointAction p (fun j => π j (O.projectStates j p))) t ≠ 0 := by
          have ht' := ht
          rw [ObsModelCore.pureStep_eq] at ht'
          simpa [O] using ht'
        have hpure : O.step (O.lastState p)
            (O.castJointAction p (fun j => π j (O.projectStates j p))) =
              PMF.pure (O.lastState p) := by
          change (if hterm' : G.terminal (O.lastState p).lastState then
              PMF.pure (O.lastState p) else _) = PMF.pure (O.lastState p)
          rw [dif_pos hterm]
        have htEq : t = O.lastState p := by
          have htmem : t ∈ (PMF.pure (O.lastState p)).support := by
            rw [← hpure]
            exact (PMF.mem_support_iff _ _).mpr hstepO
          simpa using htmem
        rw [show O.lastState (p ++ [t]) = t by simp [O, ObsModelCore.lastState], htEq]
        exact Nat.le_trans hplen (Nat.le_succ m)
      · rcases reachableHistory_pureStep_snoc (G := G) hLeg hterm ht with
          ⟨raw, hraw, dst, hsupp, _hrawEq, htEq⟩
        rw [show O.lastState (p ++ [t]) = t by simp [O, ObsModelCore.lastState], htEq]
        simp [History.snoc]
        omega

theorem reachableHistory_pureStep_component_eq
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) (i : ι)
    {π π' : (toReachableHistoryObsModelCore G hLeg).PureProfile}
    {p p' : List G.History} {t t' : G.History}
    (hobs_t :
      (toReachableHistoryObsModelCore G hLeg).projectStates i (p ++ [t]) =
        (toReachableHistoryObsModelCore G hLeg).projectStates i (p' ++ [t']))
    (hstep : (toReachableHistoryObsModelCore G hLeg).pureStep π p t ≠ 0)
    (hstep' : (toReachableHistoryObsModelCore G hLeg).pureStep π' p' t' ≠ 0)
    (hnt : ¬ G.terminal t.lastState)
    (hnt' : ¬ G.terminal t'.lastState) :
    ∃ hobs_p :
      (toReachableHistoryObsModelCore G hLeg).projectStates i p =
        (toReachableHistoryObsModelCore G hLeg).projectStates i p',
      π i ((toReachableHistoryObsModelCore G hLeg).projectStates i p) =
        hobs_p ▸ π' i ((toReachableHistoryObsModelCore G hLeg).projectStates i p') := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  have hsrc : ¬ G.terminal (O.lastState p).lastState :=
    reachableHistory_source_nonterminal_of_target_nonterminal (G := G) hLeg hstep hnt
  have hsrc' : ¬ G.terminal (O.lastState p').lastState :=
    reachableHistory_source_nonterminal_of_target_nonterminal (G := G) hLeg hstep' hnt'
  rcases reachableHistory_pureStep_snoc (G := G) hLeg hsrc hstep with
    ⟨raw, hraw, dst, hsupp, hraw_prof, ht⟩
  rcases reachableHistory_pureStep_snoc (G := G) hLeg hsrc' hstep' with
    ⟨raw', hraw', dst', hsupp', hraw'_prof, ht'⟩
  have htargetInfo :
      G.reachableInfoStateOfHistory i t =
        G.reachableInfoStateOfHistory i t' := by
    have h₁ := reachableHistory_projectStates_eq_last (G := G) hLeg i (p ++ [t])
    have h₂ := reachableHistory_projectStates_eq_last (G := G) hLeg i (p' ++ [t'])
    simpa [O, ObsModelCore.lastState] using h₁.symm.trans (hobs_t.trans h₂)
  have htargetView : t.playerView i = t'.playerView i :=
    congrArg Subtype.val htargetInfo
  have hsrcOwn := sourceView_and_ownAction_eq_of_target_view_eq (G := G)
    (h := O.lastState p) (h' := O.lastState p') (t := t) (t' := t')
    (raw := raw) (raw' := raw') (hraw := hraw) (hraw' := hraw')
    (dst := dst) (dst' := dst') (hsupp := hsupp) (hsupp' := hsupp')
    ht ht' i htargetView
  have hsourceInfo :
      G.reachableInfoStateOfHistory i (O.lastState p) =
        G.reachableInfoStateOfHistory i (O.lastState p') :=
    Subtype.ext hsrcOwn.1
  have hobs_p :
      O.projectStates i p = O.projectStates i p' := by
    have h₁ := reachableHistory_projectStates_eq_last (G := G) hLeg i p
    have h₂ := reachableHistory_projectStates_eq_last (G := G) hLeg i p'
    exact h₁.trans (hsourceInfo.trans h₂.symm)
  refine ⟨hobs_p, ?_⟩
  have hval : (π i (O.projectStates i p)).1 =
      (π' i (O.projectStates i p')).1 := by
    have hrawEq : raw i = raw' i := hsrcOwn.2
    rw [hraw_prof i, hraw'_prof i,
      reachableHistory_castJointAction_val (G := G) hLeg p
        (fun j => π j (O.projectStates j p)) i,
      reachableHistory_castJointAction_val (G := G) hLeg p'
        (fun j => π' j (O.projectStates j p')) i] at hrawEq
    exact hrawEq
  cases hπi : π i (O.projectStates i p) with
  | mk x hx =>
      cases hπi' : π' i (O.projectStates i p') with
      | mk y hy =>
          simp only [hπi, hπi'] at hval
          subst y
          apply Subtype.ext
          rw [reachableInfoLegalMove_cast_currentObs_val (G := G) hLeg hobs_p ⟨x, hy⟩]

theorem reachableHistory_pureRun_update_obs_local_nonterminal
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) (n : Nat) (i : ι)
    {π₀ π₀' : (toReachableHistoryObsModelCore G hLeg).PureProfile}
    {ss₁ ss₂ : List G.History}
    (hobs_i :
      (toReachableHistoryObsModelCore G hLeg).projectStates i ss₁ =
        (toReachableHistoryObsModelCore G hLeg).projectStates i ss₂)
    (h₁ :
      Math.ParameterizedChain.pureRun
        ((toReachableHistoryObsModelCore G hLeg).pureStep)
        (toReachableHistoryObsModelCore G hLeg).init n π₀ ss₁ ≠ 0)
    (h₂ :
      Math.ParameterizedChain.pureRun
        ((toReachableHistoryObsModelCore G hLeg).pureStep)
        (toReachableHistoryObsModelCore G hLeg).init n π₀' ss₂ ≠ 0)
    (hnt₁ : ¬ G.terminal
      ((toReachableHistoryObsModelCore G hLeg).lastState ss₁).lastState)
    (hnt₂ : ¬ G.terminal
      ((toReachableHistoryObsModelCore G hLeg).lastState ss₂).lastState)
    (πᵢ : (toReachableHistoryObsModelCore G hLeg).LocalStrategy i) :
    Math.ParameterizedChain.pureRun
        ((toReachableHistoryObsModelCore G hLeg).pureStep)
        (toReachableHistoryObsModelCore G hLeg).init n
        (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
      Math.ParameterizedChain.pureRun
        ((toReachableHistoryObsModelCore G hLeg).pureStep)
        (toReachableHistoryObsModelCore G hLeg).init n
        (Function.update π₀' i πᵢ) ss₂ ≠ 0 := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  induction n generalizing ss₁ ss₂ with
  | zero =>
      simp only [Math.ParameterizedChain.pureRun, ne_eq] at h₁ h₂ ⊢
      exact ⟨fun _ => h₂, fun _ => h₁⟩
  | succ m ih =>
      rcases List.eq_nil_or_concat ss₁ with rfl | ⟨p₁, t₁, rfl⟩
      · exact absurd (Math.ParameterizedChain.pureRun_succ_nil _ _ _ _) h₁
      rcases List.eq_nil_or_concat ss₂ with rfl | ⟨p₂, t₂, rfl⟩
      · exact absurd (Math.ParameterizedChain.pureRun_succ_nil _ _ _ _) h₂
      simp only [List.concat_eq_append] at hobs_i h₁ h₂ hnt₁ hnt₂ ⊢
      have hntt₁ : ¬ G.terminal t₁.lastState := by
        simpa [O, ObsModelCore.lastState] using hnt₁
      have hntt₂ : ¬ G.terminal t₂.lastState := by
        simpa [O, ObsModelCore.lastState] using hnt₂
      have hp₁ :
          Math.ParameterizedChain.pureRun O.pureStep O.init m π₀ p₁ ≠ 0 :=
        left_ne_zero_of_mul (Math.ParameterizedChain.pureRun_succ_append .. ▸ h₁)
      have hp₂ :
          Math.ParameterizedChain.pureRun O.pureStep O.init m π₀' p₂ ≠ 0 :=
        left_ne_zero_of_mul (Math.ParameterizedChain.pureRun_succ_append .. ▸ h₂)
      have ht₁ : O.pureStep π₀ p₁ t₁ ≠ 0 :=
        right_ne_zero_of_mul (Math.ParameterizedChain.pureRun_succ_append .. ▸ h₁)
      have ht₂ : O.pureStep π₀' p₂ t₂ ≠ 0 :=
        right_ne_zero_of_mul (Math.ParameterizedChain.pureRun_succ_append .. ▸ h₂)
      rcases reachableHistory_pureStep_component_eq (G := G) hLeg i
          hobs_i ht₁ ht₂ hntt₁ hntt₂ with
        ⟨hobs_p, hforced⟩
      have hpnt₁ : ¬ G.terminal (O.lastState p₁).lastState :=
        reachableHistory_source_nonterminal_of_target_nonterminal (G := G) hLeg ht₁ hntt₁
      have hpnt₂ : ¬ G.terminal (O.lastState p₂).lastState :=
        reachableHistory_source_nonterminal_of_target_nonterminal (G := G) hLeg ht₂ hntt₂
      rw [ObsModelCore.pureRun_succ_nonzero_iff
            (O := O) (reachableHistory_stepActionDeterminism (G := G) hLeg) m h₁,
          ObsModelCore.pureRun_succ_nonzero_iff
            (O := O) (reachableHistory_stepActionDeterminism (G := G) hLeg) m h₂]
      have hact_transfer :
          (∀ j, Function.update π₀ i πᵢ j (O.projectStates j p₁) =
            π₀ j (O.projectStates j p₁)) ↔
          (∀ j, Function.update π₀' i πᵢ j (O.projectStates j p₂) =
            π₀' j (O.projectStates j p₂)) := by
        constructor
        · intro h j
          by_cases hij : j = i
          · subst j
            rw [Function.update_self]
            have h_i := h i
            rw [Function.update_self] at h_i
            have hforced_heq :
                HEq (π₀ i (O.projectStates i p₁)) (π₀' i (O.projectStates i p₂)) :=
              (heq_of_eq hforced).trans
                (subst_heq_fosg
                  (P := fun v => ReachableInfoLegalMove G i (O.currentObs i v))
                  hobs_p (π₀' i (O.projectStates i p₂)))
            exact eq_of_heq
              ((congr_arg_heq πᵢ hobs_p).symm.trans
                ((heq_of_eq h_i).trans hforced_heq))
          · exact congrFun (Function.update_of_ne hij πᵢ π₀') (O.projectStates j p₂)
        · intro h j
          by_cases hij : j = i
          · subst j
            rw [Function.update_self]
            have h_i := h i
            rw [Function.update_self] at h_i
            have hforced_heq :
                HEq (π₀ i (O.projectStates i p₁)) (π₀' i (O.projectStates i p₂)) :=
              (heq_of_eq hforced).trans
                (subst_heq_fosg
                  (P := fun v => ReachableInfoLegalMove G i (O.currentObs i v))
                  hobs_p (π₀' i (O.projectStates i p₂)))
            exact eq_of_heq
              ((congr_arg_heq πᵢ hobs_p).trans
                ((heq_of_eq h_i).trans hforced_heq.symm))
          · exact congrFun (Function.update_of_ne hij πᵢ π₀) (O.projectStates j p₁)
      constructor
      · intro h
        exact ⟨(ih hobs_p hp₁ hp₂ hpnt₁ hpnt₂).mp h.1, hact_transfer.mp h.2⟩
      · intro h
        exact ⟨(ih hobs_p hp₁ hp₂ hpnt₁ hpnt₂).mpr h.1, hact_transfer.mpr h.2⟩

theorem reachableHistory_pureRun_nonterminal_last_steps_length
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) (n : Nat)
    {π : (toReachableHistoryObsModelCore G hLeg).PureProfile}
    {ss : List G.History}
    (h :
      Math.ParameterizedChain.pureRun
        ((toReachableHistoryObsModelCore G hLeg).pureStep)
        (toReachableHistoryObsModelCore G hLeg).init n π ss ≠ 0)
    (hnt : ¬ G.terminal
      ((toReachableHistoryObsModelCore G hLeg).lastState ss).lastState) :
    ((toReachableHistoryObsModelCore G hLeg).lastState ss).steps.length = n := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  induction n generalizing ss with
  | zero =>
      have hss : ss = [O.init] := by
        by_contra hne
        exact h (by simp [Math.ParameterizedChain.pureRun, PMF.pure_apply, O, hne])
      rw [hss]
      change (History.nil G).steps.length = 0
      rfl
  | succ m ih =>
      rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
      · exact absurd (Math.ParameterizedChain.pureRun_succ_nil _ _ _ _) h
      simp only [List.concat_eq_append] at h hnt ⊢
      have hntt : ¬ G.terminal t.lastState := by
        simpa [O, ObsModelCore.lastState] using hnt
      have hp :
          Math.ParameterizedChain.pureRun O.pureStep O.init m π p ≠ 0 :=
        left_ne_zero_of_mul (Math.ParameterizedChain.pureRun_succ_append .. ▸ h)
      have ht : O.pureStep π p t ≠ 0 :=
        right_ne_zero_of_mul (Math.ParameterizedChain.pureRun_succ_append .. ▸ h)
      have hpnt : ¬ G.terminal (O.lastState p).lastState :=
        reachableHistory_source_nonterminal_of_target_nonterminal (G := G) hLeg ht hntt
      rcases reachableHistory_pureStep_snoc (G := G) hLeg hpnt ht with
        ⟨raw, hraw, dst, hsupp, _, htEq⟩
      have hprefix := ih hp hpnt
      rw [show O.lastState (p ++ [t]) = t by simp [O, ObsModelCore.lastState], htEq]
      simp [hprefix]

theorem reachableHistory_repeated_projectStates_subsingleton
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) {n : Nat}
    {π : (toReachableHistoryObsModelCore G hLeg).PureProfile}
    {ss : List G.History}
    (hreach :
      Math.ParameterizedChain.pureRun
        ((toReachableHistoryObsModelCore G hLeg).pureStep)
        (toReachableHistoryObsModelCore G hLeg).init n π ss ≠ 0)
    (i : ι) {j : Nat} (hj : j < n)
    (heq :
      (toReachableHistoryObsModelCore G hLeg).projectStates i (ss.take (j + 1)) =
        (toReachableHistoryObsModelCore G hLeg).projectStates i ss) :
    Subsingleton
      (ReachableInfoLegalMove G i
        ((toReachableHistoryObsModelCore G hLeg).projectStates i (ss.take (j + 1)))) := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  have hprefixReach :
      Math.ParameterizedChain.pureRun O.pureStep O.init j π (ss.take (j + 1)) ≠ 0 := by
    exact Math.ParameterizedChain.pureRun_take_nonzero
      O.pureStep O.init n π ss hreach j (by omega)
  have hprefixLen :
      (O.lastState (ss.take (j + 1))).steps.length ≤ j :=
    reachableHistory_pureRun_last_steps_length_le (G := G) hLeg j hprefixReach
  by_cases hterm : G.terminal (O.lastState ss).lastState
  · have hsub :
        Subsingleton
          (ReachableInfoLegalMove G i (G.reachableInfoStateOfHistory i (O.lastState ss))) :=
      reachableInfoLegalMove_subsingleton_of_terminal (G := G) hLeg hterm i
    have hps :
        O.projectStates i (ss.take (j + 1)) =
          G.reachableInfoStateOfHistory i (O.lastState ss) := by
      exact heq.trans (reachableHistory_projectStates_eq_last (G := G) hLeg i ss)
    simpa [O, hps] using hsub
  · exfalso
    have hfinalLen :
        (O.lastState ss).steps.length = n :=
      reachableHistory_pureRun_nonterminal_last_steps_length
        (G := G) hLeg n hreach hterm
    have hprefixInfo :
        G.reachableInfoStateOfHistory i (O.lastState (ss.take (j + 1))) =
          G.reachableInfoStateOfHistory i (O.lastState ss) := by
      have hp :=
        reachableHistory_projectStates_eq_last (G := G) hLeg i (ss.take (j + 1))
      have hf := reachableHistory_projectStates_eq_last (G := G) hLeg i ss
      exact hp.symm.trans (heq.trans hf)
    have hview :
        (O.lastState (ss.take (j + 1))).playerView i =
          (O.lastState ss).playerView i :=
      congrArg Subtype.val hprefixInfo
    have hpub :=
      History.publicView_eq_of_playerView_eq (G := G) i hview
    have hstepsEq :
        (O.lastState (ss.take (j + 1))).steps.length =
          (O.lastState ss).steps.length := by
      have hlen := congrArg List.length hpub
      simpa [publicView_length (G := G) (O.lastState (ss.take (j + 1))),
        publicView_length (G := G) (O.lastState ss)] using hlen
    omega

theorem reachableHistory_current_coord_ignores_of_reachable
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) {n : Nat}
    {π₀ : (toReachableHistoryObsModelCore G hLeg).PureProfile}
    {ss : List G.History}
    (hreach :
      Math.ParameterizedChain.pureRun
        ((toReachableHistoryObsModelCore G hLeg).pureStep)
        (toReachableHistoryObsModelCore G hLeg).init n π₀ ss ≠ 0)
    (i : ι) :
    Math.PMFProduct.Ignores
      (A := fun s : G.ReachableInfoState i => ReachableInfoLegalMove G i s)
      ((toReachableHistoryObsModelCore G hLeg).projectStates i ss)
      (fun πᵢ : (toReachableHistoryObsModelCore G hLeg).LocalStrategy i =>
        Math.ParameterizedChain.pureRun
          ((toReachableHistoryObsModelCore G hLeg).pureStep)
          (toReachableHistoryObsModelCore G hLeg).init n
          (Function.update π₀ i πᵢ) ss) := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  intro πᵢ a
  let v := O.projectStates i ss
  let πᵢ' : O.LocalStrategy i := Function.update πᵢ v a
  let π₁ : O.PureProfile := Function.update π₀ i πᵢ'
  let π₂ : O.PureProfile := Function.update π₀ i πᵢ
  have hlen : ss.length = n + 1 :=
    Math.ParameterizedChain.pureRun_length O.pureStep O.init n π₀ ss hreach
  have hagree :
      ∀ (j : Nat), j < n → ∀ q : ι,
        π₁ q (O.projectStates q (ss.take (j + 1))) =
          π₂ q (O.projectStates q (ss.take (j + 1))) := by
    intro j hj q
    by_cases hqi : q = i
    · subst q
      dsimp [π₁, π₂]
      rw [Function.update_self, Function.update_self]
      by_cases hv :
          O.projectStates i (ss.take (j + 1)) = v
      · have hsub :
            Subsingleton
              (ReachableInfoLegalMove G i (O.projectStates i (ss.take (j + 1)))) :=
          reachableHistory_repeated_projectStates_subsingleton
            (G := G) hLeg hreach i hj (by simpa [O, v] using hv)
        have hsub' :
            Subsingleton
              (ReachableInfoLegalMove G i
                (O.currentObs i (O.projectStates i (ss.take (j + 1))))) := by
          simpa [O, toReachableHistoryObsModelCore, ObsModelCore.currentObs] using hsub
        letI := hsub'
        exact Subsingleton.elim _ _
      · exact Function.update_of_ne hv a πᵢ
    · dsimp [π₁, π₂]
      rw [Function.update_of_ne hqi, Function.update_of_ne hqi]
  have hrun :=
    ObsModelCore.runDistPure_congr_on_trace
      (O := O) (π₁ := π₁) (π₂ := π₂) (n := n) (ss := ss) hlen hagree
  simpa [π₁, π₂, πᵢ', v, ObsModelCore.runDistPure_eq_pureRun] using hrun

theorem reachableHistory_obsLocalFeasibility
    [Fintype ι] [Finite G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) (i : ι) :
    ObsModelCore.ObsLocalFeasibility (toReachableHistoryObsModelCore G hLeg) i := by
  classical
  let O := toReachableHistoryObsModelCore G hLeg
  intro n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ hsub πᵢ
  have hnt₁ : ¬ G.terminal (O.lastState ss₁).lastState := by
    intro hterm
    have hsub' :
        Subsingleton (ReachableInfoLegalMove G i (O.currentObs i (O.projectStates i ss₁))) := by
      have hps := reachableHistory_projectStates_eq_last (G := G) hLeg i ss₁
      simpa [O, hps] using
        reachableInfoLegalMove_subsingleton_of_terminal (G := G) hLeg hterm i
    exact hsub hsub'
  have hinfo :
      G.reachableInfoStateOfHistory i (O.lastState ss₁) =
        G.reachableInfoStateOfHistory i (O.lastState ss₂) := by
    have h₁p := reachableHistory_projectStates_eq_last (G := G) hLeg i ss₁
    have h₂p := reachableHistory_projectStates_eq_last (G := G) hLeg i ss₂
    exact h₁p.symm.trans (hobs.trans h₂p)
  have hview : (O.lastState ss₁).playerView i = (O.lastState ss₂).playerView i :=
    congrArg Subtype.val hinfo
  have hnt₂ : ¬ G.terminal (O.lastState ss₂).lastState := by
    intro hterm
    have hsub' :
        Subsingleton (ReachableInfoLegalMove G i (O.currentObs i (O.projectStates i ss₁))) := by
      have hsubLast :
          Subsingleton
            (ReachableInfoLegalMove G i
              (G.reachableInfoStateOfHistory i (O.lastState ss₁))) := by
        refine ⟨fun a b => ?_⟩
        apply Subtype.ext
        rw [reachableInfoLegalMove_eq_none_of_terminal_view_eq
              (G := G) hLeg hterm i hview.symm a,
            reachableInfoLegalMove_eq_none_of_terminal_view_eq
              (G := G) hLeg hterm i hview.symm b]
      have hps := reachableHistory_projectStates_eq_last (G := G) hLeg i ss₁
      simpa [O, hps] using hsubLast
    exact hsub hsub'
  have hsteps₁ :=
    reachableHistory_pureRun_nonterminal_last_steps_length (G := G) hLeg n₁ h₁ hnt₁
  have hsteps₂ :=
    reachableHistory_pureRun_nonterminal_last_steps_length (G := G) hLeg n₂ h₂ hnt₂
  have hhistLen :
      (O.lastState ss₁).steps.length = (O.lastState ss₂).steps.length := by
    have hpub := History.publicView_eq_of_playerView_eq (G := G) i hview
    have hlen := congrArg List.length hpub
    simpa [publicView_length (G := G) (O.lastState ss₁),
      publicView_length (G := G) (O.lastState ss₂)] using hlen
  have hn : n₁ = n₂ := by
    rw [← hsteps₁, ← hsteps₂]
    exact hhistLen
  have h₂' :
      Math.ParameterizedChain.pureRun
        ((toReachableHistoryObsModelCore G hLeg).pureStep)
        (toReachableHistoryObsModelCore G hLeg).init n₁ π₀' ss₂ ≠ 0 := by
    rwa [hn]
  simpa [hn] using
    reachableHistory_pureRun_update_obs_local_nonterminal
      (G := G) hLeg n₁ i hobs h₁ h₂' hnt₁ hnt₂ πᵢ

theorem reachableHistory_actionPosteriorLocal
    [Fintype ι] [Fintype G.History] [∀ i, Fintype (Option (Act i))]
    (hLeg : G.LegalObservable) :
    ∀ i, ReachableHistoryActionPosteriorLocal (G := G) hLeg i := by
  classical
  intro i
  letI := ReachableHistoryNative.reachableHistoryInfoStateFintype (G := G) hLeg
  letI := ReachableHistoryNative.reachableInfoLegalMoveFintype (G := G)
  exact ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility
    (O := toReachableHistoryObsModelCore G hLeg)
    (reachableHistory_stepMassInvariant (G := G) hLeg) i
    (reachableHistory_obsLocalFeasibility (G := G) hLeg i)

theorem ownAction_eq_of_source_target_view_eq
    {h h' t t' : G.History}
    {raw : JointAction Act} {raw' : JointAction Act}
    {hraw : G.legal h.lastState raw} {hraw' : G.legal h'.lastState raw'}
    {dst dst' : W}
    {hsupp : G.transition h.lastState ⟨raw, hraw⟩ dst ≠ 0}
    {hsupp' : G.transition h'.lastState ⟨raw', hraw'⟩ dst' ≠ 0}
    (ht : t = h.snoc ⟨raw, hraw⟩ dst hsupp)
    (ht' : t' = h'.snoc ⟨raw', hraw'⟩ dst' hsupp')
    (i : ι)
    (hsrc : h.playerView i = h'.playerView i)
    (hdst : t.playerView i = t'.playerView i) :
    raw i = raw' i := by
  have hacts := History.projectActions_eq_of_playerView_eq (G := G) i hdst
  rw [ht, ht',
    projectActions_snoc_eq (G := G) h i ⟨raw, hraw⟩ dst hsupp,
    projectActions_snoc_eq (G := G) h' i ⟨raw', hraw'⟩ dst' hsupp'] at hacts
  have hsrcActs : h.projectActions i = h'.projectActions i :=
    History.projectActions_eq_of_playerView_eq (G := G) i hsrc
  rw [hsrcActs] at hacts
  have htail :
      (match raw i with | some ai => [ai] | none => []) =
        (match raw' i with | some ai => [ai] | none => []) := by
    exact List.append_cancel_left hacts
  cases hrawi : raw i with
  | none =>
      cases hraw'i : raw' i with
      | none => rfl
      | some ai' =>
          simp [hrawi, hraw'i] at htail
  | some ai =>
      cases hraw'i : raw' i with
      | none =>
          simp [hrawi, hraw'i] at htail
      | some ai' =>
          simp [hrawi, hraw'i] at htail
          simp [htail]


/-- Lift a legal reachable FOSG pure strategy into the legal reachable-history
Kuhn model. -/
noncomputable def liftReachableHistoryPureStrategy
    (hLeg : G.LegalObservable) (i : ι)
    (π : G.ReachableLegalPureStrategy i) :
    (toReachableHistoryObsModelCore G hLeg).LocalStrategy i := by
  intro s
  let h := s.2.choose
  have hs : h.playerView i = s.1 := by
    simpa [h] using s.2.choose_spec
  have hsEq : G.reachableInfoStateOfHistory i h = s := by
    exact Subtype.ext hs
  have hraw : π.1 s ∈ G.availableMoves h i := by
    simpa [hsEq] using π.2 h
  refine ⟨π.1 s, ?_⟩
  have hat : π.1 s ∈ G.availableMovesAtInfoState i (h.playerView i) :=
    G.mem_availableMovesAtInfoState_of_history h hraw
  simpa [hs] using hat

/-- Lift a legal reachable FOSG behavioral strategy into the legal
reachable-history Kuhn model. -/
noncomputable def reachableInfoLegalMoveOfBehavioralSupport
    (_hLeg : G.LegalObservable) (i : ι)
    (β : G.ReachableLegalBehavioralStrategy i)
    (s : G.ReachableInfoState i)
    (oi : Option (Act i)) (hoi : oi ∈ (β.1 s).support) :
    ReachableInfoLegalMove G i s := by
  refine ⟨oi, ?_⟩
  let h := s.2.choose
  have hs : h.playerView i = s.1 := by
    simpa [h] using s.2.choose_spec
  have hsEq : G.reachableInfoStateOfHistory i h = s := by
    exact Subtype.ext hs
  have hraw : oi ∈ G.availableMoves h i := by
    exact β.2 h (oi := oi) (by simpa [hsEq] using hoi)
  have hat : oi ∈ G.availableMovesAtInfoState i (h.playerView i) :=
    G.mem_availableMovesAtInfoState_of_history h hraw
  simpa [hs] using hat

noncomputable def liftReachableHistoryBehavioralStrategy
    (_hLeg : G.LegalObservable) (i : ι)
    (β : G.ReachableLegalBehavioralStrategy i) :
    ∀ s : G.ReachableInfoState i, PMF (ReachableInfoLegalMove G i s) := by
  classical
  intro s
  exact (β.1 s).bindOnSupport fun oi hoi =>
    PMF.pure
      (reachableInfoLegalMoveOfBehavioralSupport (G := G) _hLeg i β s oi hoi)

@[simp] theorem erase_liftReachableHistoryBehavioralStrategy
    (hLeg : G.LegalObservable) (i : ι)
    (β : G.ReachableLegalBehavioralStrategy i)
    (s : G.ReachableInfoState i) :
    Math.ProbabilityMassFunction.pushforward
        (liftReachableHistoryBehavioralStrategy (G := G) hLeg i β s)
        (fun a : ReachableInfoLegalMove G i s => a.1) =
      β.1 s := by
  classical
  let p := β.1 s
  let default : ReachableInfoLegalMove G i s := reachableInfoLegalMoveDefault G i s
  let f : Option (Act i) → PMF (ReachableInfoLegalMove G i s) := fun oi =>
    if h : oi ∈ p.support then
      PMF.pure
        (reachableInfoLegalMoveOfBehavioralSupport (G := G) hLeg i β s oi h)
    else
      PMF.pure default
  have hlift :
      liftReachableHistoryBehavioralStrategy (G := G) hLeg i β s =
        p.bind f := by
    calc
      liftReachableHistoryBehavioralStrategy (G := G) hLeg i β s =
          p.bindOnSupport (fun oi _hoi => f oi) := by
            unfold liftReachableHistoryBehavioralStrategy
            dsimp [p, f]
            apply congrArg
            funext oi hoi
            simp [hoi]
      _ = p.bind f := PMF.bindOnSupport_eq_bind p f
  rw [Math.ProbabilityMassFunction.pushforward, hlift, PMF.map_bind]
  have hbind :
      p.bind (fun oi =>
          PMF.map (fun a : ReachableInfoLegalMove G i s => a.1) (f oi)) =
        p.bind PMF.pure := by
    exact Math.ProbabilityMassFunction.bind_congr_on_support
      p _ _ (fun oi hoi => by
        dsimp [f]
        rw [dif_pos hoi, PMF.pure_map]
        rfl)
  rw [hbind, PMF.bind_pure]

/-- Erase a legal reachable-history pure strategy back to a native legal
reachable FOSG pure strategy. -/
noncomputable def eraseReachableHistoryPureStrategy
    (hLeg : G.LegalObservable) (i : ι)
    (π : (toReachableHistoryObsModelCore G hLeg).LocalStrategy i) :
    G.ReachableLegalPureStrategy i := by
  refine ⟨fun s => (π s).1, ?_⟩
  intro h
  have haiInfo :
      (π (G.reachableInfoStateOfHistory i h)).1 ∈
        G.availableMovesAtInfoState i (G.reachableInfoStateOfHistory i h).1 :=
    (π (G.reachableInfoStateOfHistory i h)).2
  have hEq := G.availableMovesAtInfoState_eq_of_history hLeg i h
  exact hEq ▸ haiInfo

@[simp] theorem liftReachableHistoryPureStrategy_erase
    (hLeg : G.LegalObservable) (i : ι)
    (π : (toReachableHistoryObsModelCore G hLeg).LocalStrategy i) :
    liftReachableHistoryPureStrategy (G := G) hLeg i
        (eraseReachableHistoryPureStrategy (G := G) hLeg i π) =
      π := by
  funext s
  apply Subtype.ext
  rfl

/-- The single-player mixed pure strategy induced by a legal reachable
behavioral strategy in the reachable-history core model. -/
noncomputable def reachableHistoryBehavioralToMixedStrategy
    [Fintype G.History]
    (hLeg : G.LegalObservable) (i : ι) [Fintype (Option (Act i))]
    (β : G.ReachableLegalBehavioralStrategy i) :
    PMF ((toReachableHistoryObsModelCore G hLeg).LocalStrategy i) := by
  classical
  letI : Fintype ((toReachableHistoryObsModelCore G hLeg).InfoState i) :=
    ReachableHistoryNative.reachableHistoryInfoStateFintype (G := G) hLeg i
  letI : ∀ s : G.ReachableInfoState i, Fintype (ReachableInfoLegalMove G i s) :=
    fun _ => by
      dsimp [ReachableInfoLegalMove]
      infer_instance
  exact Math.PMFProduct.pmfPi
    (liftReachableHistoryBehavioralStrategy (G := G) hLeg i β)

/-- Push the reachable-history behavioral-to-mixed law back to legal reachable
pure strategies by erasing the core local-strategy wrapper. -/
noncomputable def reachableLegalBehavioralToMixed
    [Fintype G.History]
    (hLeg : G.LegalObservable) (i : ι) [Fintype (Option (Act i))]
    (β : G.ReachableLegalBehavioralStrategy i) :
    PMF (G.ReachableLegalPureStrategy i) :=
  PMF.map (eraseReachableHistoryPureStrategy (G := G) hLeg i)
    (reachableHistoryBehavioralToMixedStrategy (G := G) hLeg i β)

@[simp] theorem reachableLegalBehavioralToMixed_lift
    [Fintype G.History]
    (hLeg : G.LegalObservable) (i : ι) [Fintype (Option (Act i))]
    (β : G.ReachableLegalBehavioralStrategy i) :
    PMF.map (liftReachableHistoryPureStrategy (G := G) hLeg i)
        (reachableLegalBehavioralToMixed (G := G) hLeg i β) =
      reachableHistoryBehavioralToMixedStrategy (G := G) hLeg i β := by
  classical
  unfold reachableLegalBehavioralToMixed
  rw [PMF.map_comp]
  change PMF.map
      ((liftReachableHistoryPureStrategy (G := G) hLeg i) ∘
        (eraseReachableHistoryPureStrategy (G := G) hLeg i))
      (reachableHistoryBehavioralToMixedStrategy (G := G) hLeg i β) =
    reachableHistoryBehavioralToMixedStrategy (G := G) hLeg i β
  have hfun :
      ((liftReachableHistoryPureStrategy (G := G) hLeg i) ∘
        (eraseReachableHistoryPureStrategy (G := G) hLeg i)) = id := by
    funext π
    exact liftReachableHistoryPureStrategy_erase (G := G) hLeg i π
  rw [hfun, PMF.map_id]

/-- Lift a legal reachable FOSG behavioral profile into the legal
reachable-history Kuhn model. -/
noncomputable def liftReachableHistoryBehavioralProfile
    (hLeg : G.LegalObservable)
    (β : G.ReachableLegalBehavioralProfile) :
    (toReachableHistoryObsModelCore G hLeg).BehavioralProfile :=
  fun i => liftReachableHistoryBehavioralStrategy (G := G) hLeg i (β i)


end Kuhn

end FOSG

end GameTheory
