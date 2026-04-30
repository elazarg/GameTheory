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
