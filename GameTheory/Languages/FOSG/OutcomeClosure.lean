import Math.OutcomeClosure
import GameTheory.Languages.FOSG.Compile

/-!
# Outcome closure for FOSG histories

This file specializes `Math.OutcomeClosure.ValueProcess` to native FOSG
execution.  A client supplies a continuation value on histories and proves
that one nonterminal FOSG step preserves it.  The generic closure theorem then
identifies the observed finite-horizon run distribution with that value.
-/

set_option autoImplicit false

namespace GameTheory

namespace FOSG

open Math.OutcomeClosure

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

namespace History

variable {G : FOSG ι W Act PrivObs PubObs}
variable {Ω : Type*}

/-- One stopped FOSG history step induced by a legal behavioral profile.
Terminal histories self-loop; nonterminal histories sample a legal joint action
and then the FOSG transition kernel, extending the realized history. -/
noncomputable def valueStep
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (σ : G.LegalBehavioralProfile) (h : G.History) : PMF G.History := by
  classical
  by_cases hterm : G.terminal h.lastState
  · exact PMF.pure h
  · exact
      (G.legalActionLaw σ h hterm).bind fun a =>
        (G.transition h.lastState a).bind fun dst =>
          PMF.pure (h.extendByOutcome a dst)

@[simp] theorem valueStep_terminal
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (σ : G.LegalBehavioralProfile) (h : G.History)
    (hterm : G.terminal h.lastState) :
    valueStep (G := G) σ h = PMF.pure h := by
  classical
  simp [valueStep, hterm]

@[simp] theorem valueStep_nonterminal
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (σ : G.LegalBehavioralProfile) (h : G.History)
    (hterm : ¬ G.terminal h.lastState) :
    valueStep (G := G) σ h =
      (G.legalActionLaw σ h hterm).bind fun a =>
        (G.transition h.lastState a).bind fun dst =>
          PMF.pure (h.extendByOutcome a dst) := by
  classical
  simp [valueStep, hterm]

/-- Continuation-value data for a FOSG history process.  The key client-facing
field is `step_value`: one nonterminal FOSG step preserves the semantic value. -/
structure OutcomeValue
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    (σ : G.LegalBehavioralProfile) (Ω : Type*) where
  rank : G.History → Nat
  observe : G.History → Ω
  value : G.History → PMF Ω
  terminal_of_rank_zero :
    ∀ h, rank h = 0 → G.terminal h.lastState
  terminal_value :
    ∀ h, G.terminal h.lastState → value h = PMF.pure (observe h)
  step_value :
    ∀ h (hterm : ¬ G.terminal h.lastState),
      (G.legalActionLaw σ h hterm).bind
          (fun a =>
            (G.transition h.lastState a).bind
              (fun dst => value (h.extendByOutcome a dst))) =
        value h
  step_rank :
    ∀ h (_hterm : ¬ G.terminal h.lastState)
      (a : G.LegalAction h.lastState) (dst : W),
      G.transition h.lastState a dst ≠ 0 →
        rank (h.extendByOutcome a dst) + 1 = rank h

namespace OutcomeValue

/-- Build FOSG continuation-value data by projecting histories into an
external semantic machine.  This is useful when a concrete language has its
own executable state and value semantics: the client proves only that one
nonterminal FOSG step, after projection, agrees with the semantic step. -/
noncomputable def ofProjectedStep
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    {σ : G.LegalBehavioralProfile} {S Ω : Type*}
    (rank : G.History → Nat)
    (observe : G.History → Ω)
    (project : G.History → S)
    (semanticStep : S → PMF S)
    (semanticValue : S → PMF Ω)
    (terminal_of_rank_zero :
      ∀ h, rank h = 0 → G.terminal h.lastState)
    (terminal_value :
      ∀ h, G.terminal h.lastState →
        semanticValue (project h) = PMF.pure (observe h))
    (semantic_step_value :
      ∀ h (_hterm : ¬ G.terminal h.lastState),
        (semanticStep (project h)).bind semanticValue =
          semanticValue (project h))
    (project_step :
      ∀ h (hterm : ¬ G.terminal h.lastState),
        (G.legalActionLaw σ h hterm).bind
            (fun a =>
              (G.transition h.lastState a).bind
                (fun dst =>
                  PMF.pure (project (h.extendByOutcome a dst)))) =
          semanticStep (project h))
    (step_rank :
      ∀ h (_hterm : ¬ G.terminal h.lastState)
        (a : G.LegalAction h.lastState) (dst : W),
        G.transition h.lastState a dst ≠ 0 →
          rank (h.extendByOutcome a dst) + 1 = rank h) :
    OutcomeValue (G := G) σ Ω where
  rank := rank
  observe := observe
  value := fun h => semanticValue (project h)
  terminal_of_rank_zero := terminal_of_rank_zero
  terminal_value := terminal_value
  step_value := by
    intro h hterm
    calc
      (G.legalActionLaw σ h hterm).bind
          (fun a =>
            (G.transition h.lastState a).bind
              (fun dst =>
                semanticValue (project (h.extendByOutcome a dst)))) =
        ((G.legalActionLaw σ h hterm).bind
            (fun a =>
              (G.transition h.lastState a).bind
                (fun dst =>
                  PMF.pure (project (h.extendByOutcome a dst))))).bind
          semanticValue := by
            symm
            rw [PMF.bind_bind]
            congr 1
            funext a
            rw [PMF.bind_bind]
            simp only [PMF.pure_bind]
      _ = (semanticStep (project h)).bind semanticValue := by
            rw [project_step h hterm]
      _ = semanticValue (project h) := semantic_step_value h hterm
  step_rank := step_rank

/-- Build FOSG continuation-value data from a value function on world states.

This is the common case for language compilers whose observed outcome is a
projection of the terminal state, and whose ranking function also depends only
on the current state. -/
noncomputable def ofLastStateValue
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    {σ : G.LegalBehavioralProfile}
    (rankState : W → Nat)
    (observeState : W → Ω)
    (stateValue : W → PMF Ω)
    (terminal_of_rank_zero :
      ∀ w, rankState w = 0 → G.terminal w)
    (terminal_value :
      ∀ w, G.terminal w → stateValue w = PMF.pure (observeState w))
    (step_value :
      ∀ (h : G.History) (hterm : ¬ G.terminal h.lastState),
        (G.legalActionLaw σ h hterm).bind
            (fun a =>
              (G.transition h.lastState a).bind
                (fun dst =>
                  stateValue (h.extendByOutcome a dst).lastState)) =
          stateValue h.lastState)
    (step_rank :
      ∀ (h : G.History) (_hterm : ¬ G.terminal h.lastState)
        (a : G.LegalAction h.lastState) (dst : W),
        G.transition h.lastState a dst ≠ 0 →
          rankState dst + 1 = rankState h.lastState) :
    OutcomeValue (G := G) σ Ω where
  rank := fun h => rankState h.lastState
  observe := fun h => observeState h.lastState
  value := fun h => stateValue h.lastState
  terminal_of_rank_zero := by
    intro h hrank
    exact terminal_of_rank_zero h.lastState hrank
  terminal_value := by
    intro h hterm
    exact terminal_value h.lastState hterm
  step_value := step_value
  step_rank := by
    intro h hterm a dst hsupp
    simpa [History.extendByOutcome_of_support
      (h := h) (a := a) (dst := dst) hsupp] using
      step_rank h hterm a dst hsupp

/-- Lift preservation of a projected semantic step to preservation of a state
value under one FOSG history step. -/
theorem stateStepValue_of_projectedStep
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    {σ : G.LegalBehavioralProfile} {S Ω : Type*}
    (project : W → S)
    (semanticStep : S → PMF S)
    (semanticValue : S → PMF Ω)
    (stateValue : W → PMF Ω)
    (value_project :
      ∀ w, semanticValue (project w) = stateValue w)
    (semantic_step_value :
      ∀ s, (semanticStep s).bind semanticValue = semanticValue s)
    (project_step :
      ∀ (h : G.History) (hterm : ¬ G.terminal h.lastState),
        (G.legalActionLaw σ h hterm).bind
            (fun a => PMF.map project (G.transition h.lastState a)) =
          semanticStep (project h.lastState)) :
    ∀ (h : G.History) (hterm : ¬ G.terminal h.lastState),
      (G.legalActionLaw σ h hterm).bind
          (fun a =>
            (G.transition h.lastState a).bind
              (fun dst =>
                stateValue (h.extendByOutcome a dst).lastState)) =
        stateValue h.lastState := by
  intro h hterm
  have hproject :
      (G.legalActionLaw σ h hterm).bind
          (fun a =>
            (G.transition h.lastState a).bind
              (fun dst =>
                stateValue (h.extendByOutcome a dst).lastState)) =
        (G.legalActionLaw σ h hterm).bind
          (fun a => (G.transition h.lastState a).bind stateValue) := by
    refine Math.ProbabilityMassFunction.bind_congr_on_support
      (G.legalActionLaw σ h hterm) _ _ ?_
    intro a _ha
    refine Math.ProbabilityMassFunction.bind_congr_on_support
      (G.transition h.lastState a) _ _ ?_
    intro dst hdst
    have hsupp : G.transition h.lastState a dst ≠ 0 := by
      simpa [PMF.mem_support_iff] using hdst
    rw [History.extendByOutcome_of_support
      (h := h) (a := a) (dst := dst) hsupp]
    simp
  calc
    (G.legalActionLaw σ h hterm).bind
        (fun a =>
          (G.transition h.lastState a).bind
            (fun dst =>
              stateValue (h.extendByOutcome a dst).lastState)) =
      (G.legalActionLaw σ h hterm).bind
        (fun a => (G.transition h.lastState a).bind stateValue) := hproject
    _ =
      ((G.legalActionLaw σ h hterm).bind
          (fun a => PMF.map project (G.transition h.lastState a))).bind
        semanticValue := by
          rw [PMF.bind_bind]
          congr 1
          funext a
          simp [PMF.map, PMF.bind_bind, value_project]
    _ =
      (semanticStep (project h.lastState)).bind semanticValue := by
        rw [project_step h hterm]
    _ =
      semanticValue (project h.lastState) :=
        semantic_step_value (project h.lastState)
    _ = stateValue h.lastState := value_project h.lastState

/-- Build state-based FOSG continuation-value data when the semantic step is
proved after projecting the FOSG world into an external state machine. -/
noncomputable def ofProjectedLastStateStep
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    {σ : G.LegalBehavioralProfile} {S Ω : Type*}
    (rankState : W → Nat)
    (observeState : W → Ω)
    (project : W → S)
    (semanticStep : S → PMF S)
    (semanticValue : S → PMF Ω)
    (stateValue : W → PMF Ω)
    (terminal_of_rank_zero :
      ∀ w, rankState w = 0 → G.terminal w)
    (terminal_value :
      ∀ w, G.terminal w → stateValue w = PMF.pure (observeState w))
    (value_project :
      ∀ w, semanticValue (project w) = stateValue w)
    (semantic_step_value :
      ∀ s, (semanticStep s).bind semanticValue = semanticValue s)
    (project_step :
      ∀ (h : G.History) (hterm : ¬ G.terminal h.lastState),
        (G.legalActionLaw σ h hterm).bind
            (fun a => PMF.map project (G.transition h.lastState a)) =
          semanticStep (project h.lastState))
    (step_rank :
      ∀ (h : G.History) (_hterm : ¬ G.terminal h.lastState)
        (a : G.LegalAction h.lastState) (dst : W),
        G.transition h.lastState a dst ≠ 0 →
          rankState dst + 1 = rankState h.lastState) :
    OutcomeValue (G := G) σ Ω :=
  ofLastStateValue
    (G := G)
    (σ := σ)
    rankState
    observeState
    stateValue
    terminal_of_rank_zero
    terminal_value
    (stateStepValue_of_projectedStep
      (G := G)
      (σ := σ)
      project
      semanticStep
      semanticValue
      stateValue
      value_project
      semantic_step_value
      project_step)
    step_rank

/-- Convert FOSG continuation-value data to the generic stopped-process
abstraction. -/
noncomputable def toValueProcess
    [Fintype ι] [∀ i, Fintype (Option (Act i))]
    {σ : G.LegalBehavioralProfile} (R : OutcomeValue (G := G) σ Ω) :
    Math.OutcomeClosure.ValueProcess G.History Ω where
  terminal := fun h => G.terminal h.lastState
  step := valueStep (G := G) σ
  rank := R.rank
  observe := R.observe
  value := R.value
  terminal_of_rank_zero := R.terminal_of_rank_zero
  terminal_value := R.terminal_value
  step_value := by
    intro h hterm
    calc
      (valueStep (G := G) σ h).bind R.value =
          ((G.legalActionLaw σ h hterm).bind fun a =>
            (G.transition h.lastState a).bind fun dst =>
              PMF.pure (h.extendByOutcome a dst)).bind R.value := by
            rw [valueStep_nonterminal (G := G) σ h hterm]
      _ =
          (G.legalActionLaw σ h hterm).bind
            (fun a =>
              (G.transition h.lastState a).bind
                (fun dst => R.value (h.extendByOutcome a dst))) := by
            rw [PMF.bind_bind]
            congr 1
            funext a
            rw [PMF.bind_bind]
            simp only [PMF.pure_bind]
      _ = R.value h := R.step_value h hterm
  step_rank := by
    intro h h' hterm hsupp
    rw [valueStep_nonterminal (G := G) σ h hterm] at hsupp
    have hsuppMem := (PMF.mem_support_iff _ _).2 hsupp
    rw [PMF.mem_support_bind_iff] at hsuppMem
    rcases hsuppMem with ⟨a, _ha, hh'⟩
    rw [PMF.mem_support_bind_iff] at hh'
    rcases hh' with ⟨dst, hdst, hpure⟩
    have hhEq : h' = h.extendByOutcome a dst := by
      simpa using hpure
    subst h'
    exact R.step_rank h hterm a dst
      (by simpa [PMF.mem_support_iff] using hdst)

theorem runDistFrom_eq_run
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    {σ : G.LegalBehavioralProfile} (R : OutcomeValue (G := G) σ Ω) :
    ∀ n h,
      History.runDistFrom G σ n h =
        R.toValueProcess.run n h := by
  intro n
  induction n with
  | zero =>
      intro h
      rfl
  | succ n ih =>
      intro h
      by_cases hterm : G.terminal h.lastState
      · rw [History.runDistFrom_succ_terminal (G := G) σ n h hterm]
        exact (R.toValueProcess.run_terminal (n + 1) hterm).symm
      · rw [History.runDistFrom_succ_nonterminal (G := G) σ n h hterm]
        rw [R.toValueProcess.run_succ_nonterminal n hterm]
        change
          ((G.legalActionLaw σ h hterm).bind fun a =>
            (G.transition h.lastState a).bind fun dst =>
              History.runDistFrom G σ n (h.extendByOutcome a dst)) =
            (valueStep (G := G) σ h).bind (R.toValueProcess.run n)
        rw [valueStep_nonterminal (G := G) σ h hterm]
        rw [PMF.bind_bind]
        congr 1
        funext a
        rw [PMF.bind_bind]
        congr 1
        funext dst
        rw [PMF.pure_bind]
        exact ih (h.extendByOutcome a dst)

/-- FOSG history outcome-closure theorem from an arbitrary prefix history. -/
theorem map_observe_runDistFrom_eq_value
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    {σ : G.LegalBehavioralProfile} (R : OutcomeValue (G := G) σ Ω)
    (n : Nat) (h : G.History) (hn : R.rank h ≤ n) :
    PMF.map R.observe (History.runDistFrom G σ n h) = R.value h := by
  rw [R.runDistFrom_eq_run n h]
  exact R.toValueProcess.map_observe_run_eq_value n h hn

/-- FOSG history outcome-closure theorem from the initial history. -/
theorem map_observe_runDist_eq_value
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    {σ : G.LegalBehavioralProfile} (R : OutcomeValue (G := G) σ Ω)
    (n : Nat) (hn : R.rank (History.nil G) ≤ n) :
    PMF.map R.observe (G.runDist n σ) = R.value (History.nil G) := by
  exact R.map_observe_runDistFrom_eq_value n (History.nil G) hn

end OutcomeValue

end History

end FOSG

end GameTheory
