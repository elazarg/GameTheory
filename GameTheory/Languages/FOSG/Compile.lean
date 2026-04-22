import GameTheory.Core.KernelGame
import GameTheory.Languages.FOSG.Execution

/-!
# GameTheory.Languages.FOSG.Compile

Compilation of FOSGs into `KernelGame`.

The induced `KernelGame` uses legal behavioral strategies as the strategy sets
and terminal realized histories as outcomes. Since `KernelGame` expects a PMF
on outcomes, this bridge is available under an explicit normalization
assumption on the terminal-history mass function.
-/

namespace GameTheory

open Math.Probability
open scoped BigOperators

namespace FOSG

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}

namespace History

variable {G : FOSG ι W Act PrivObs PubObs}

/-- Total history extension by a legal action and candidate destination. If the
transition mass is zero, the history is left unchanged; this branch contributes
zero mass inside the induced PMF kernels. -/
noncomputable def extendByOutcome
    (h : G.History) (a : G.LegalAction h.lastState) (dst : W) : G.History :=
  if hsupp : G.transition h.lastState a dst ≠ 0 then h.snoc a dst hsupp else h

theorem extendByOutcome_of_support
    (h : G.History) (a : G.LegalAction h.lastState) (dst : W)
    (hsupp : G.transition h.lastState a dst ≠ 0) :
    h.extendByOutcome a dst = h.snoc a dst hsupp := by
  simp [extendByOutcome, hsupp]

theorem extendByOutcome_of_no_support
    (h : G.History) (a : G.LegalAction h.lastState) (dst : W)
    (hsupp : G.transition h.lastState a dst = 0) :
    h.extendByOutcome a dst = h := by
  simp [extendByOutcome, hsupp]

theorem extendByOutcome_isPrefix
    (h : G.History) (a : G.LegalAction h.lastState) (dst : W) :
    h.IsPrefix (h.extendByOutcome a dst) := by
  by_cases hsupp : G.transition h.lastState a dst = 0
  · rw [extendByOutcome_of_no_support (h := h) (a := a) (dst := dst) hsupp]
    exact h.prefix_refl
  · rw [extendByOutcome_of_support (h := h) (a := a) (dst := dst) hsupp]
    exact h.prefix_snoc a dst hsupp

open Classical in
theorem extendByOutcome_prefix_canonical_imp
    (pref : G.History) (e : G.Step) (es : List G.Step)
    (hchain : G.StepChainFrom pref.lastState (e :: es))
    (a : G.LegalAction pref.lastState) (dst : W)
    (hsupp : G.transition pref.lastState a dst ≠ 0)
    (hPrefix :
      (pref.extendByOutcome a dst).IsPrefix
        (pref.extendBySteps (e :: es) hchain)) :
    a = hchain.1 ▸ e.act ∧ dst = e.dst := by
  cases e with
  | mk src act dst' support =>
      rcases hchain with ⟨hsrc, htail⟩
      cases hsrc
      rcases hPrefix with ⟨suffix, hsuffix⟩
      have hsteps :
          (G.lastStateFrom G.init pref.steps = pref.lastState ∧ HEq act a ∧ dst' = dst) ∧
            es = suffix := by
        simpa [History.extendByOutcome_of_support (h := pref) (a := a) (dst := dst) hsupp,
          History.extendBySteps] using hsuffix
      rcases hsteps with ⟨⟨-, hactEq, hdstEq⟩, -⟩
      exact ⟨eq_of_heq hactEq |>.symm, hdstEq.symm⟩

theorem extendByOutcome_eq_appendStep_of_head
    (pref : G.History) (e : G.Step) (es : List G.Step)
    (hchain : G.StepChainFrom pref.lastState (e :: es)) :
    pref.extendByOutcome (hchain.1 ▸ e.act) e.dst = pref.appendStep e hchain.1 := by
  cases e with
  | mk src act dst support =>
      rcases hchain with ⟨hsrc, htail⟩
      cases hsrc
      have hsupp : G.transition pref.lastState act dst ≠ 0 := by
        simpa using support
      rw [History.extendByOutcome_of_support (h := pref) (a := act) (dst := dst) hsupp]
      rfl

/-- The prefix history obtained from the first `n` realized steps of `h`. -/
def initialSegment (h : G.History) (n : Nat) : G.History :=
  { steps := h.steps.take n
    chain := by
      have hchain :
          G.StepChainFrom G.init (h.steps.take n ++ h.steps.drop n) := by
        simpa [List.take_append_drop] using h.chain
      simpa using StepChainFrom.left hchain }

@[simp] theorem initialSegment_steps (h : G.History) (n : Nat) :
    (h.initialSegment n).steps = h.steps.take n := rfl

theorem initialSegment_isPrefix (h : G.History) (n : Nat) :
    (h.initialSegment n).IsPrefix h := by
  refine ⟨h.steps.drop n, ?_⟩
  simp [initialSegment, List.take_append_drop]

theorem initialSegment_length
    (h : G.History) {n : Nat} (hn : n ≤ h.steps.length) :
    (h.initialSegment n).steps.length = n := by
  simp [initialSegment, List.length_take, hn]

/-- Horizon-bounded run distribution on realized histories induced by a legal
behavioral profile. Terminal histories absorb. -/
noncomputable def runDistFrom
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) : Nat → G.History → PMF G.History
  | 0, h => PMF.pure h
  | n + 1, h =>
      if hterm : G.terminal h.lastState then
        PMF.pure h
      else
        (G.legalActionLaw σ h hterm).bind fun a =>
          (G.transition h.lastState a).bind fun dst =>
            runDistFrom G σ n (h.extendByOutcome a dst)

@[simp] theorem runDistFrom_zero
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) (h : G.History) :
    runDistFrom G σ 0 h = PMF.pure h := rfl

@[simp] theorem runDistFrom_succ_terminal
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) (n : Nat) (h : G.History)
    (hterm : G.terminal h.lastState) :
    runDistFrom G σ (n + 1) h = PMF.pure h := by
  simp [runDistFrom, hterm]

@[simp] theorem runDistFrom_succ_nonterminal
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) (n : Nat) (h : G.History)
    (hterm : ¬ G.terminal h.lastState) :
    runDistFrom G σ (n + 1) h =
      (G.legalActionLaw σ h hterm).bind fun a =>
          (G.transition h.lastState a).bind fun dst =>
            runDistFrom G σ n (h.extendByOutcome a dst) := by
  simp [runDistFrom, hterm]

open Classical in
theorem runDistFrom_eq_zero_of_exactHorizon_not_prefix
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    {k : Nat} (hExact : ∀ h : G.History, h.IsTerminal ↔ h.steps.length = k)
    (σ : G.LegalBehavioralProfile) :
    ∀ (n : Nat) (pref target : G.History),
      pref.steps.length + n = k →
      ¬ pref.IsPrefix target →
      History.runDistFrom G σ n pref target = 0
  | 0, pref, target, hk, hnot => by
      have hneq : target ≠ pref := by
        intro hEq
        apply hnot
        simpa [hEq] using pref.prefix_refl
      simp [History.runDistFrom, PMF.pure_apply, hneq]
  | n + 1, pref, target, hk, hnot => by
      have hprefNotTerm : ¬ G.terminal pref.lastState := by
        intro hterm
        have : pref.steps.length = k := (hExact pref).1 hterm
        omega
      rw [History.runDistFrom_succ_nonterminal (σ := σ) (n := n) (h := pref) hprefNotTerm]
      rw [PMF.bind_apply, tsum_fintype]
      suffices houter :
          ∑ a : G.LegalAction pref.lastState,
            (G.legalActionLaw σ pref hprefNotTerm) a *
              ∑ dst : W,
                (G.transition pref.lastState a) dst *
                  History.runDistFrom G σ n (pref.extendByOutcome a dst) target = 0 by
        simpa using houter
      refine Finset.sum_eq_zero ?_
      intro a _
      suffices hinner :
          ∑ dst : W,
            (G.transition pref.lastState a) dst *
              History.runDistFrom G σ n (pref.extendByOutcome a dst) target = 0 by
        rw [hinner]
        simp
      refine Finset.sum_eq_zero ?_
      intro dst _
      by_cases hsupp : G.transition pref.lastState a dst = 0
      · simp [hsupp]
      · have hk' : (pref.extendByOutcome a dst).steps.length + n = k := by
          rw [History.extendByOutcome_of_support (h := pref) (a := a) (dst := dst) hsupp]
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk
        have hnot' : ¬ (pref.extendByOutcome a dst).IsPrefix target := by
          intro hPrefix
          have hpref' := History.extendByOutcome_isPrefix (h := pref) a dst
          exact hnot (History.prefix_trans hpref' hPrefix)
        rw [runDistFrom_eq_zero_of_exactHorizon_not_prefix
          (G := G) hExact (σ := σ) n
          (pref := pref.extendByOutcome a dst) (target := target) hk' hnot']
        simp

end History

/-- Exact-horizon predicate for FOSGs: terminal histories are exactly those of
length `k`. -/
def ExactHorizon
    (G : FOSG ι W Act PrivObs PubObs) (k : Nat) : Prop :=
  ∀ h : G.History, h.IsTerminal ↔ h.steps.length = k

/-- Bounded-horizon predicate for FOSGs: every realized history of length `k`
is terminal. Terminal histories may occur earlier and then absorb in the
horizon-bounded run semantics. -/
def BoundedHorizon
    (G : FOSG ι W Act PrivObs PubObs) (k : Nat) : Prop :=
  ∀ h : G.History, h.steps.length = k → h.IsTerminal

theorem exactHorizon_iff
    {G : FOSG ι W Act PrivObs PubObs} {k : Nat}
    (hExact : G.ExactHorizon k) (h : G.History) :
    h.IsTerminal ↔ h.steps.length = k :=
  hExact h

theorem ExactHorizon.bounded
    {G : FOSG ι W Act PrivObs PubObs} {k : Nat}
    (hExact : G.ExactHorizon k) : G.BoundedHorizon k := by
  intro h hh
  exact (hExact h).2 hh

open Classical in
theorem runDistFrom_eq_zero_of_length_gt
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) :
    ∀ (n : Nat) (pref target : G.History),
      pref.steps.length + n < target.steps.length →
      History.runDistFrom G σ n pref target = 0
  | 0, pref, target, hlt => by
      have hneq : target ≠ pref := by
        intro hEq
        have : pref.steps.length < pref.steps.length := by
          simp [hEq] at hlt
        exact (Nat.lt_irrefl _ this).elim
      simp [History.runDistFrom, PMF.pure_apply, hneq]
  | n + 1, pref, target, hlt => by
      by_cases hterm : G.terminal pref.lastState
      · rw [History.runDistFrom_succ_terminal (G := G) (σ := σ) (n := n) (h := pref) hterm]
        have hneq : target ≠ pref := by
          intro hEq
          have : pref.steps.length < pref.steps.length := by
            simp [hEq] at hlt
          exact (Nat.lt_irrefl _ this).elim
        simp [PMF.pure_apply, hneq]
      · rw [History.runDistFrom_succ_nonterminal (G := G) (σ := σ) (n := n) (h := pref) hterm]
        rw [PMF.bind_apply, tsum_fintype]
        refine Finset.sum_eq_zero ?_
        intro a _
        rw [PMF.bind_apply, tsum_fintype]
        suffices hinner :
            ∑ dst : W,
              (G.transition pref.lastState a) dst *
                History.runDistFrom G σ n (pref.extendByOutcome a dst) target = 0 by
          rw [hinner]
          simp
        refine Finset.sum_eq_zero ?_
        intro dst _
        by_cases hsupp : G.transition pref.lastState a dst = 0
        · simp [hsupp]
        · have hlt' : (pref.extendByOutcome a dst).steps.length + n < target.steps.length := by
            rw [History.extendByOutcome_of_support (h := pref) (a := a) (dst := dst) hsupp]
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
          rw [runDistFrom_eq_zero_of_length_gt (G := G) (σ := σ) n
            (pref := pref.extendByOutcome a dst) (target := target) hlt']
          simp

open Classical in
theorem runDistFrom_eq_zero_of_nonterminal_target_lt
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) :
    ∀ (n : Nat) (pref target : G.History),
      ¬ target.IsTerminal →
      target.steps.length < pref.steps.length + n →
      History.runDistFrom G σ n pref target = 0
  | 0, pref, target, hnotTerm, hlt => by
      have hneq : target ≠ pref := by
        intro hEq
        have : pref.steps.length < pref.steps.length := by
          simp [hEq] at hlt
        exact (Nat.lt_irrefl _ this).elim
      simp [History.runDistFrom, PMF.pure_apply, hneq]
  | n + 1, pref, target, hnotTerm, hlt => by
      by_cases hterm : G.terminal pref.lastState
      · rw [History.runDistFrom_succ_terminal (G := G) (σ := σ) (n := n) (h := pref) hterm]
        have hneq : target ≠ pref := by
          intro hEq
          apply hnotTerm
          simpa [History.IsTerminal, hEq] using hterm
        simp [PMF.pure_apply, hneq]
      · rw [History.runDistFrom_succ_nonterminal (G := G) (σ := σ) (n := n) (h := pref) hterm]
        rw [PMF.bind_apply, tsum_fintype]
        refine Finset.sum_eq_zero ?_
        intro a _
        rw [PMF.bind_apply, tsum_fintype]
        suffices hinner :
            ∑ dst : W,
              (G.transition pref.lastState a) dst *
                History.runDistFrom G σ n (pref.extendByOutcome a dst) target = 0 by
          rw [hinner]
          simp
        refine Finset.sum_eq_zero ?_
        intro dst _
        by_cases hsupp : G.transition pref.lastState a dst = 0
        · simp [hsupp]
        · have hlt' : target.steps.length < (pref.extendByOutcome a dst).steps.length + n := by
            rw [History.extendByOutcome_of_support (h := pref) (a := a) (dst := dst) hsupp]
            simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hlt
          rw [runDistFrom_eq_zero_of_nonterminal_target_lt (G := G) (σ := σ) n
            (pref := pref.extendByOutcome a dst) (target := target) hnotTerm hlt']
          simp

open Classical in
theorem runDistFrom_eq_zero_of_exactHorizon_length_ne
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    {k : Nat} (hExact : G.ExactHorizon k)
    (σ : G.LegalBehavioralProfile) :
    ∀ (n : Nat) (pref target : G.History),
      pref.steps.length + n = k →
      target.steps.length ≠ k →
      History.runDistFrom G σ n pref target = 0
  | 0, pref, target, hk, hlen => by
      have hprefTerm : pref.IsTerminal := (hExact pref).2 hk
      have hneq : target ≠ pref := by
        intro hEq
        apply hlen
        simpa [hEq] using hk
      simp [History.runDistFrom, PMF.pure_apply, hneq]
  | n + 1, pref, target, hk, hlen => by
      have hprefNotTerm : ¬ G.terminal pref.lastState := by
        intro hterm
        have : pref.steps.length = k := (hExact pref).1 hterm
        omega
      rw [History.runDistFrom_succ_nonterminal (σ := σ) (n := n) (h := pref) hprefNotTerm]
      rw [PMF.bind_apply, tsum_fintype]
      refine Finset.sum_eq_zero ?_
      intro a _
      rw [PMF.bind_apply, tsum_fintype]
      suffices hinner :
          ∑ dst : W,
            (G.transition pref.lastState a) dst *
              History.runDistFrom G σ n (pref.extendByOutcome a dst) target = 0 by
        rw [hinner]
        simp
      refine Finset.sum_eq_zero ?_
      intro dst _
      by_cases hsupp : G.transition pref.lastState a dst = 0
      · simp [hsupp]
      · have hk' : (pref.extendByOutcome a dst).steps.length + n = k := by
          rw [History.extendByOutcome_of_support (h := pref) (a := a) (dst := dst) hsupp]
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk
        have hzero :=
          runDistFrom_eq_zero_of_exactHorizon_length_ne
            (G := G) hExact (σ := σ) n
            (pref := pref.extendByOutcome a dst) (target := target) hk' hlen
        rw [hzero]
        simp

/-- Horizon-bounded run distribution on realized histories from the initial
history. -/
noncomputable def runDist
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (k : Nat) (σ : G.LegalBehavioralProfile) : PMF G.History :=
  History.runDistFrom G σ k (History.nil G)

@[simp] theorem runDist_zero
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) :
    G.runDist 0 σ = PMF.pure (History.nil G) := rfl

theorem runDist_eq_zero_of_exactHorizon_length_ne
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    {k : Nat} (hExact : G.ExactHorizon k)
    (σ : G.LegalBehavioralProfile) (h : G.History)
    (hlen : h.steps.length ≠ k) :
    G.runDist k σ h = 0 := by
  simpa [runDist, History.nil] using
    runDistFrom_eq_zero_of_exactHorizon_length_ne (G := G) hExact (σ := σ) k
      (pref := History.nil G) (target := h) (by simp) hlen

theorem runDist_eq_zero_of_length_gt
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (k : Nat) (σ : G.LegalBehavioralProfile) (h : G.History)
    (hlt : k < h.steps.length) :
    G.runDist k σ h = 0 := by
  simpa [runDist, History.nil] using
    runDistFrom_eq_zero_of_length_gt (G := G) (σ := σ) k
      (pref := History.nil G) (target := h) (by simpa using hlt)

theorem runDist_eq_zero_of_nonterminal_of_boundedHorizon
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (σ : G.LegalBehavioralProfile) (h : G.History)
    (hnotTerm : ¬ h.IsTerminal) :
    G.runDist k σ h = 0 := by
  by_cases hlen : h.steps.length = k
  · exact (hnotTerm (hBound h hlen)).elim
  · have hlt_or_gt := lt_or_gt_of_ne hlen
    cases hlt_or_gt with
    | inl hlt =>
        simpa [runDist, History.nil] using
          runDistFrom_eq_zero_of_nonterminal_target_lt (G := G) (σ := σ) k
            (pref := History.nil G) (target := h) hnotTerm (by simpa using hlt)
    | inr hgt =>
        exact G.runDist_eq_zero_of_length_gt k σ h hgt

theorem runDist_support_isTerminal_of_boundedHorizon
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (σ : G.LegalBehavioralProfile) (h : G.History)
    (hsupp : h ∈ (G.runDist k σ).support) :
    h.IsTerminal := by
  by_contra hnot
  have hmass : G.runDist k σ h ≠ 0 := (PMF.mem_support_iff _ _).1 hsupp
  exact hmass (G.runDist_eq_zero_of_nonterminal_of_boundedHorizon hBound σ h hnot)

open Classical in
theorem runDistFrom_eq_zero_of_terminal_not_prefix
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) :
    ∀ (n : Nat) (pref target : G.History),
      target.IsTerminal →
      target.steps.length ≤ pref.steps.length + n →
      ¬ pref.IsPrefix target →
      History.runDistFrom G σ n pref target = 0
  | 0, pref, target, hterm, hlen, hnot => by
      have hneq : target ≠ pref := by
        intro hEq
        apply hnot
        simpa [hEq] using pref.prefix_refl
      simp [History.runDistFrom, PMF.pure_apply, hneq]
  | n + 1, pref, target, hterm, hlen, hnot => by
      by_cases hprefTerm : G.terminal pref.lastState
      · rw [History.runDistFrom_succ_terminal (G := G) (σ := σ) (n := n) (h := pref) hprefTerm]
        have hneq : target ≠ pref := by
          intro hEq
          apply hnot
          simpa [hEq] using pref.prefix_refl
        simp [PMF.pure_apply, hneq]
      · rw [History.runDistFrom_succ_nonterminal (G := G) (σ := σ) (n := n) (h := pref) hprefTerm]
        rw [PMF.bind_apply, tsum_fintype]
        refine Finset.sum_eq_zero ?_
        intro a _
        rw [PMF.bind_apply, tsum_fintype]
        suffices hinner :
            ∑ dst : W,
              (G.transition pref.lastState a) dst *
                History.runDistFrom G σ n (pref.extendByOutcome a dst) target = 0 by
          rw [hinner]
          simp
        refine Finset.sum_eq_zero ?_
        intro dst _
        by_cases hsupp : G.transition pref.lastState a dst = 0
        · simp [hsupp]
        · have hnot' : ¬ (pref.extendByOutcome a dst).IsPrefix target := by
            intro hPrefix
            exact hnot <|
              History.prefix_trans (History.extendByOutcome_isPrefix (h := pref) a dst) hPrefix
          have hlen' : target.steps.length ≤ (pref.extendByOutcome a dst).steps.length + n := by
            rw [History.extendByOutcome_of_support (h := pref) (a := a) (dst := dst) hsupp]
            simp [Nat.add_assoc, Nat.add_comm] at hlen ⊢
            omega
          rw [runDistFrom_eq_zero_of_terminal_not_prefix
            (G := G) (σ := σ) n (pref := pref.extendByOutcome a dst)
            (target := target) hterm hlen' hnot']
          simp

open Classical in
theorem runDistFrom_eq_probFrom_of_terminal_target
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (σ : G.LegalBehavioralProfile) :
    ∀ (pref : G.History) (es : List G.Step)
      (hchain : G.StepChainFrom pref.lastState es) (slack : Nat),
      (pref.extendBySteps es hchain).IsTerminal →
      History.runDistFrom G σ (es.length + slack) pref (pref.extendBySteps es hchain) =
        History.probFrom (G := G) σ.toProfile pref es hchain
  | pref, [], hchain, 0, hterm => by
      have hprefTerm : pref.IsTerminal := by
        simpa [History.extendBySteps] using hterm
      simp [History.probFrom]
  | pref, [], hchain, slack + 1, hterm => by
      have hprefTerm : pref.IsTerminal := by
        simpa [History.extendBySteps] using hterm
      rw [show ([] : List G.Step).length + (slack + 1) = slack + 1 by simp]
      rw [History.runDistFrom_succ_terminal (G := G) (σ := σ) (n := slack) (h := pref) hprefTerm]
      simp [History.probFrom]
  | pref, e :: es, hchain, slack, hterm => by
      rcases hchain with ⟨hsrc, htail⟩
      let pref' : G.History := pref.appendStep e hsrc
      let a₀ : G.LegalAction pref.lastState := hsrc ▸ e.act
      have htail' : G.StepChainFrom pref'.lastState es := by
        simpa [pref'] using htail
      have hprefNotTerm : ¬ pref.IsTerminal := pref.not_isTerminal_of_legalAction a₀
      rw [show (e :: es).length + slack = es.length + slack + 1 by
        simp [Nat.add_left_comm, Nat.add_comm]]
      rw [History.runDistFrom_succ_nonterminal
        (G := G) (σ := σ) (n := es.length + slack) (h := pref) hprefNotTerm]
      rw [PMF.bind_apply, tsum_fintype]
      simp_rw [PMF.bind_apply, tsum_fintype]
      have hrec :
          History.runDistFrom G σ (es.length + slack) pref'
              (History.extendBySteps pref' es htail') =
            History.probFrom (G := G) σ.toProfile pref' es htail' := by
        simpa [pref'] using
          runDistFrom_eq_probFrom_of_terminal_target
            (G := G) (σ := σ) pref' es htail' slack
            (by simpa [History.extendBySteps, pref'] using hterm)
      have houter_zero :
          ∀ a : G.LegalAction pref.lastState, a ≠ a₀ →
            ∑ dst : W,
              (G.transition pref.lastState a) dst *
                History.runDistFrom G σ (es.length + slack) (pref.extendByOutcome a dst)
                  (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩) = 0 := by
        intro a hne
        refine Finset.sum_eq_zero ?_
        intro dst _
        by_cases hsupp : G.transition pref.lastState a dst = 0
        · simp [hsupp]
        · have hnotPrefix : ¬ (pref.extendByOutcome a dst).IsPrefix
              (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩) := by
            intro hPrefix
            rcases History.extendByOutcome_prefix_canonical_imp
                (pref := pref) (e := e) (es := es) (hchain := ⟨hsrc, htail⟩)
                (a := a) (dst := dst) hsupp hPrefix with ⟨ha, _⟩
            exact hne ha
          have hlen' :
              (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩).steps.length ≤
                (pref.extendByOutcome a dst).steps.length + (es.length + slack) := by
            rw [History.extendByOutcome_of_support (h := pref) (a := a) (dst := dst) hsupp]
            simp [History.extendBySteps, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          rw [runDistFrom_eq_zero_of_terminal_not_prefix
            (G := G) (σ := σ) (n := es.length + slack)
            (pref := pref.extendByOutcome a dst)
            (target := pref.extendBySteps (e :: es) ⟨hsrc, htail⟩)
            hterm hlen' hnotPrefix]
          simp
      have hinner_a₀ :
          ∑ dst : W,
            (G.transition pref.lastState a₀) dst *
              History.runDistFrom G σ (es.length + slack) (pref.extendByOutcome a₀ dst)
                (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩)
            =
          (G.transition pref.lastState a₀) e.dst *
            History.runDistFrom G σ (es.length + slack) pref'
              (History.extendBySteps pref' es htail') := by
        let f : W → ENNReal := fun dst =>
          (G.transition pref.lastState a₀) dst *
            History.runDistFrom G σ (es.length + slack) (pref.extendByOutcome a₀ dst)
              (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩)
        change ∑ dst : W, f dst = (G.transition pref.lastState a₀) e.dst *
          History.runDistFrom G σ (es.length + slack) pref' (History.extendBySteps pref' es htail')
        have hsum : ∑ dst : W, f dst = f e.dst := by
          refine Finset.sum_eq_single e.dst ?_ ?_
          · intro dst _ hdst
            by_cases hsupp : G.transition pref.lastState a₀ dst = 0
            · simp [f, hsupp]
            · have hnotPrefix : ¬ (pref.extendByOutcome a₀ dst).IsPrefix
                  (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩) := by
                intro hPrefix
                rcases History.extendByOutcome_prefix_canonical_imp
                    (pref := pref) (e := e) (es := es) (hchain := ⟨hsrc, htail⟩)
                    (a := a₀) (dst := dst) hsupp hPrefix with ⟨_, hdst'⟩
                exact hdst hdst'
              have hlen' :
                  (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩).steps.length ≤
                    (pref.extendByOutcome a₀ dst).steps.length + (es.length + slack) := by
                rw [History.extendByOutcome_of_support (h := pref) (a := a₀) (dst := dst) hsupp]
                simp [History.extendBySteps, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
              have hzero :=
                runDistFrom_eq_zero_of_terminal_not_prefix
                  (G := G) (σ := σ) (n := es.length + slack)
                  (pref := pref.extendByOutcome a₀ dst)
                  (target := pref.extendBySteps (e :: es) ⟨hsrc, htail⟩)
                  hterm hlen' hnotPrefix
              simpa [f, History.extendBySteps, pref'] using
                congrArg (fun x => (G.transition pref.lastState a₀) dst * x) hzero
          · simp [f]
        rw [hsum]
        unfold f
        rw [History.extendByOutcome_eq_appendStep_of_head
          (pref := pref) (e := e) (es := es) (hchain := ⟨hsrc, htail⟩)]
        simp [History.extendBySteps, pref']
      have houter_single :
          ∑ a : G.LegalAction pref.lastState,
            (G.legalActionLaw σ pref hprefNotTerm) a *
              ∑ dst : W,
                (G.transition pref.lastState a) dst *
                  History.runDistFrom G σ (es.length + slack) (pref.extendByOutcome a dst)
                    (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩)
          =
          (G.legalActionLaw σ pref hprefNotTerm) a₀ *
            ∑ dst : W,
              (G.transition pref.lastState a₀) dst *
                History.runDistFrom G σ (es.length + slack) (pref.extendByOutcome a₀ dst)
                  (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩) := by
        refine Finset.sum_eq_single a₀ ?_ ?_
        · intro a _ hne
          rw [houter_zero a hne]
          simp
        · simp
      calc
        ∑ a : G.LegalAction pref.lastState,
            (G.legalActionLaw σ pref hprefNotTerm) a *
              ∑ dst : W,
                (G.transition pref.lastState a) dst *
                  History.runDistFrom G σ (es.length + slack) (pref.extendByOutcome a dst)
                    (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩)
          =
          (G.legalActionLaw σ pref hprefNotTerm) a₀ *
            ∑ dst : W,
              (G.transition pref.lastState a₀) dst *
                History.runDistFrom G σ (es.length + slack) (pref.extendByOutcome a₀ dst)
                  (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩) := houter_single
        _ =
          (G.legalActionLaw σ pref hprefNotTerm) a₀ *
            ((G.transition pref.lastState a₀) e.dst *
              History.runDistFrom G σ (es.length + slack) pref'
                (History.extendBySteps pref' es htail')) := by
              rw [hinner_a₀]
        _ =
          G.stepProb σ.toProfile pref e *
            History.probFrom (G := G) σ.toProfile pref' es htail' := by
              rw [hrec, G.legalActionLaw_apply σ pref hprefNotTerm a₀]
              rw [G.jointActionDist_apply]
              cases e with
              | mk src act dst support =>
                  cases hsrc
                  change
                    (∏ x, (σ.toProfile x (pref.playerView x)) (act.1 x)) *
                        ((G.transition (G.lastStateFrom G.init pref.steps) act) dst *
                          History.probFrom (G := G) σ.toProfile
                            (pref.appendStep
                              { src := G.lastStateFrom G.init pref.steps
                                act := act
                                dst := dst
                                support := support } rfl) es htail') =
                      G.stepProb σ.toProfile pref
                        { src := G.lastStateFrom G.init pref.steps
                          act := act
                          dst := dst
                          support := support } *
                        History.probFrom (G := G) σ.toProfile
                          (pref.appendStep
                            { src := G.lastStateFrom G.init pref.steps
                              act := act
                              dst := dst
                              support := support } rfl) es htail'
                  simp [FOSG.stepProb, FOSG.stepActionProb, FOSG.Step.ownAction?, mul_assoc]
        _ = History.probFrom (G := G) σ.toProfile pref (e :: es) ⟨hsrc, htail⟩ := by
              simp [History.probFrom, pref']

theorem runDist_support_isTerminal_of_exactHorizon
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    {k : Nat} (hExact : G.ExactHorizon k)
    (σ : G.LegalBehavioralProfile) (h : G.History)
    (hsupp : h ∈ (G.runDist k σ).support) :
    h.IsTerminal := by
  have hmass : G.runDist k σ h ≠ 0 := by
    exact (PMF.mem_support_iff _ _).1 hsupp
  have hlen : h.steps.length = k := by
    by_contra hne
    exact hmass (G.runDist_eq_zero_of_exactHorizon_length_ne hExact σ h hne)
  exact (hExact h).2 hlen

open Classical in
theorem runDistFrom_eq_probFrom_of_exactHorizon
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    {k : Nat} (hExact : G.ExactHorizon k)
    (σ : G.LegalBehavioralProfile) :
    ∀ (pref : G.History) (es : List G.Step)
      (hchain : G.StepChainFrom pref.lastState es),
      pref.steps.length + es.length = k →
      History.runDistFrom G σ es.length pref (pref.extendBySteps es hchain) =
        History.probFrom (G := G) σ.toProfile pref es hchain
  | pref, [], hchain, hk => by
      simp [History.probFrom, History.extendBySteps]
  | pref, e :: es, hchain, hk => by
      rcases hchain with ⟨hsrc, htail⟩
      let pref' : G.History := pref.appendStep e hsrc
      let a₀ : G.LegalAction pref.lastState := hsrc ▸ e.act
      let htail' : G.StepChainFrom pref'.lastState es := by
        simpa [pref'] using htail
      have hprefNotTerm : ¬ G.terminal pref.lastState := by
        intro hterm
        have hlenEq : pref.steps.length = k := (hExact pref).1 hterm
        have hk' : pref.steps.length + (es.length + 1) = k := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk
        omega
      have hkTail : pref'.steps.length + es.length = k := by
        have hk' : pref.steps.length + (es.length + 1) = k := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk
        rw [show pref'.steps.length = pref.steps.length + 1 by simp [pref']]
        omega
      have hrec :=
        runDistFrom_eq_probFrom_of_exactHorizon
          (G := G) hExact σ pref' es (by simpa [pref'] using htail) hkTail
      rw [show List.length (e :: es) = es.length + 1 by simp]
      rw [History.runDistFrom_succ_nonterminal
        (G := G) (σ := σ) (n := es.length) (h := pref) hprefNotTerm]
      rw [PMF.bind_apply, tsum_fintype]
      simp_rw [PMF.bind_apply, tsum_fintype]
      have houter_zero :
          ∀ a : G.LegalAction pref.lastState, a ≠ a₀ →
            ∑ dst : W,
              (G.transition pref.lastState a) dst *
                History.runDistFrom G σ es.length (pref.extendByOutcome a dst)
                  (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩) = 0 := by
        intro a hne
        refine Finset.sum_eq_zero ?_
        intro dst _
        by_cases hsupp : G.transition pref.lastState a dst = 0
        · simp [hsupp]
        · have hnotPrefix : ¬ (pref.extendByOutcome a dst).IsPrefix
              (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩) := by
            intro hPrefix
            rcases History.extendByOutcome_prefix_canonical_imp
                (pref := pref) (e := e) (es := es) (hchain := ⟨hsrc, htail⟩)
                (a := a) (dst := dst) hsupp hPrefix with ⟨ha, _⟩
            exact hne ha
          have hk' : (pref.extendByOutcome a dst).steps.length + es.length = k := by
            have hk'' : pref.steps.length + (es.length + 1) = k := by
              simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk
            have hlenExt : (pref.extendByOutcome a dst).steps.length = pref.steps.length + 1 := by
              rw [History.extendByOutcome_of_support (h := pref) (a := a) (dst := dst) hsupp]
              simp
            rw [hlenExt]
            omega
          rw [History.runDistFrom_eq_zero_of_exactHorizon_not_prefix
            (G := G) hExact (σ := σ) (n := es.length)
            (pref := pref.extendByOutcome a dst)
            (target := pref.extendBySteps (e :: es) ⟨hsrc, htail⟩) hk' hnotPrefix]
          simp
      have hinner_a₀ :
          ∑ dst : W,
            (G.transition pref.lastState a₀) dst *
              History.runDistFrom G σ es.length (pref.extendByOutcome a₀ dst)
                (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩)
            =
          (G.transition pref.lastState a₀) e.dst *
            History.runDistFrom G σ es.length pref'
              (History.extendBySteps pref' es htail') := by
        let f : W → ENNReal := fun dst =>
          (G.transition pref.lastState a₀) dst *
            History.runDistFrom G σ es.length (pref.extendByOutcome a₀ dst)
              (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩)
        change ∑ dst : W, f dst = (G.transition pref.lastState a₀) e.dst *
          History.runDistFrom G σ es.length pref' (History.extendBySteps pref' es htail')
        have hsum :
            ∑ dst : W, f dst = f e.dst := by
          refine Finset.sum_eq_single e.dst ?_ ?_
          · intro dst _ hdst
            by_cases hsupp : G.transition pref.lastState a₀ dst = 0
            · simp [f, hsupp]
            · have hnotPrefix : ¬ (pref.extendByOutcome a₀ dst).IsPrefix
                  (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩) := by
                intro hPrefix
                rcases History.extendByOutcome_prefix_canonical_imp
                    (pref := pref) (e := e) (es := es) (hchain := ⟨hsrc, htail⟩)
                    (a := a₀) (dst := dst) hsupp hPrefix with ⟨_, hdst'⟩
                exact hdst hdst'
              have hk' : (pref.extendByOutcome a₀ dst).steps.length + es.length = k := by
                have hk'' : pref.steps.length + (es.length + 1) = k := by
                  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk
                have hlenExt :
                    (pref.extendByOutcome a₀ dst).steps.length =
                      pref.steps.length + 1 := by
                  rw [History.extendByOutcome_of_support (h := pref) (a := a₀) (dst := dst) hsupp]
                  simp
                rw [hlenExt]
                omega
              have hzero :=
                History.runDistFrom_eq_zero_of_exactHorizon_not_prefix
                  (G := G) hExact (σ := σ) (n := es.length)
                  (pref := pref.extendByOutcome a₀ dst)
                  (target := pref.extendBySteps (e :: es) ⟨hsrc, htail⟩) hk' hnotPrefix
              simpa [f, History.extendBySteps, pref'] using
                congrArg (fun x => (G.transition pref.lastState a₀) dst * x) hzero
          · simp [f]
        rw [hsum]
        unfold f
        rw [History.extendByOutcome_eq_appendStep_of_head
          (pref := pref) (e := e) (es := es) (hchain := ⟨hsrc, htail⟩)]
        simp [History.extendBySteps, pref']
      have houter_single :
          ∑ a : G.LegalAction pref.lastState,
            (G.legalActionLaw σ pref hprefNotTerm) a *
              ∑ dst : W,
                (G.transition pref.lastState a) dst *
                  History.runDistFrom G σ es.length (pref.extendByOutcome a dst)
                    (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩)
          =
          (G.legalActionLaw σ pref hprefNotTerm) a₀ *
            ∑ dst : W,
              (G.transition pref.lastState a₀) dst *
                History.runDistFrom G σ es.length (pref.extendByOutcome a₀ dst)
                  (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩) := by
        refine Finset.sum_eq_single a₀ ?_ ?_
        · intro a _ hne
          rw [houter_zero a hne]
          simp
        · simp
      calc
        ∑ a : G.LegalAction pref.lastState,
            (G.legalActionLaw σ pref hprefNotTerm) a *
              ∑ dst : W,
                (G.transition pref.lastState a) dst *
                  History.runDistFrom G σ es.length (pref.extendByOutcome a dst)
                    (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩)
          =
          (G.legalActionLaw σ pref hprefNotTerm) a₀ *
            ∑ dst : W,
              (G.transition pref.lastState a₀) dst *
                History.runDistFrom G σ es.length (pref.extendByOutcome a₀ dst)
                  (pref.extendBySteps (e :: es) ⟨hsrc, htail⟩) := houter_single
        _ =
          (G.legalActionLaw σ pref hprefNotTerm) a₀ *
            ((G.transition pref.lastState a₀) e.dst *
              History.runDistFrom G σ es.length pref'
                (History.extendBySteps pref' es htail')) := by
              rw [hinner_a₀]
        _ =
          G.stepProb σ.toProfile pref e * History.probFrom σ.toProfile pref' es htail' := by
              rw [hrec, G.legalActionLaw_apply σ pref hprefNotTerm a₀]
              rw [G.jointActionDist_apply]
              cases e with
              | mk src act dst support =>
                  cases hsrc
                  change
                    (∏ x, (σ.toProfile x (pref.playerView x)) (act.1 x)) *
                        ((G.transition (G.lastStateFrom G.init pref.steps) act) dst *
                          History.probFrom σ.toProfile
                            (pref.appendStep
                              { src := G.lastStateFrom G.init pref.steps
                                act := act
                                dst := dst
                                support := support } rfl) es htail') =
                      G.stepProb σ.toProfile pref
                        { src := G.lastStateFrom G.init pref.steps
                          act := act
                          dst := dst
                          support := support } *
                        History.probFrom σ.toProfile
                          (pref.appendStep
                            { src := G.lastStateFrom G.init pref.steps
                              act := act
                              dst := dst
                              support := support } rfl) es htail'
                  simp [FOSG.stepProb, FOSG.stepActionProb, FOSG.Step.ownAction?, mul_assoc]
        _ = History.probFrom σ.toProfile pref (e :: es) ⟨hsrc, htail⟩ := by
              simp [History.probFrom, pref']

theorem runDist_eq_terminalWeight_of_exactHorizon
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    {k : Nat} (hExact : G.ExactHorizon k)
    (σ : G.LegalBehavioralProfile) (h : G.History) :
    G.runDist k σ h = History.terminalWeight (G := G) σ.toProfile h := by
  by_cases hlen : h.steps.length = k
  · have hterm : h.IsTerminal := (hExact h).2 hlen
    rw [History.terminalWeight_of_terminal (σ := σ.toProfile) hterm]
    rw [hlen.symm]
    simpa [runDist, History.prob, History.extendBySteps_eq] using
      runDistFrom_eq_probFrom_of_exactHorizon
        (G := G) hExact σ (History.nil G) h.steps
        (by
          have hchain0 := h.chain
          simpa [History.lastState, History.nil] using hchain0)
        (by simp [hlen])
  · rw [History.terminalWeight_of_not_terminal (σ := σ.toProfile)]
    · exact G.runDist_eq_zero_of_exactHorizon_length_ne hExact σ h hlen
    · intro hterm
      exact hlen ((hExact h).1 hterm)

theorem terminal_length_le_of_boundedHorizon
    {G : FOSG ι W Act PrivObs PubObs}
    {k : Nat} (hBound : G.BoundedHorizon k)
    (h : G.History) (_hterm : h.IsTerminal) :
    h.steps.length ≤ k := by
  by_contra hgt
  have hgt' : k < h.steps.length := Nat.lt_of_not_ge hgt
  let pref := h.initialSegment k
  have hprefLen : pref.steps.length = k := by
    exact h.initialSegment_length (Nat.le_of_lt hgt')
  have hprefTerm : pref.IsTerminal := hBound pref hprefLen
  have hchainSplit : G.StepChainFrom G.init (h.steps.take k ++ h.steps.drop k) := by
    simpa [List.take_append_drop] using h.chain
  have hdrop_nonempty : h.steps.drop k ≠ [] := by
    intro hnil
    have hlenDrop : 0 < (h.steps.drop k).length := by
      simpa [List.length_drop] using Nat.sub_pos_of_lt hgt'
    simp [hnil] at hlenDrop
  cases hdrop : h.steps.drop k with
  | nil =>
      exact (hdrop_nonempty hdrop).elim
  | cons e es =>
      have hchainAppend : G.StepChainFrom G.init (h.steps.take k ++ e :: es) := by
        simpa [hdrop] using hchainSplit
      have hsuffix : G.StepChainFrom (G.lastStateFrom G.init (h.steps.take k)) (e :: es) :=
        StepChainFrom.right hchainAppend
      have hsrc : e.src = pref.lastState := by
        simpa [pref, History.lastState] using hsuffix.1
      have hlegal : G.LegalAction pref.lastState := hsrc ▸ e.act
      exact (pref.not_isTerminal_of_legalAction hlegal) hprefTerm

theorem runDist_eq_terminalWeight_of_boundedHorizon
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (σ : G.LegalBehavioralProfile) (h : G.History) :
    G.runDist k σ h = History.terminalWeight (G := G) σ.toProfile h := by
  by_cases hterm : h.IsTerminal
  · rw [History.terminalWeight_of_terminal (σ := σ.toProfile) hterm]
    have hle : h.steps.length ≤ k := G.terminal_length_le_of_boundedHorizon hBound h hterm
    let slack : Nat := k - h.steps.length
    have hk : h.steps.length + slack = k := Nat.add_sub_of_le hle
    rw [← hk, runDist]
    simpa [History.prob, History.extendBySteps_eq] using
      runDistFrom_eq_probFrom_of_terminal_target
        (G := G) (σ := σ) (pref := History.nil G) (es := h.steps)
        (hchain := by
          have hchain0 := h.chain
          simpa [History.lastState, History.nil] using hchain0)
        (slack := slack) (by simpa [History.extendBySteps_eq] using hterm)
  · rw [History.terminalWeight_of_not_terminal (σ := σ.toProfile) hterm]
    exact G.runDist_eq_zero_of_nonterminal_of_boundedHorizon hBound σ h hterm

/-- The terminal-history mass function normalizes to a probability law on
legal behavioral profiles. -/
def HasNormalizedTerminalLaw
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal] : Prop := by
  classical
  exact ∀ σ : G.LegalBehavioralProfile,
    ∑ h : G.History, History.terminalWeight (G := G) σ.toProfile h = 1

section
variable [∀ i, Finite (Option (Act i))] [Finite W]

theorem hasNormalizedTerminalLaw_of_exactHorizon
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι]
    [Fintype G.History] [DecidablePred G.terminal]
    {k : Nat} (hExact : G.ExactHorizon k) :
    G.HasNormalizedTerminalLaw := by
  let _ : Fintype W := Fintype.ofFinite W
  let _ : ∀ i, Fintype (Option (Act i)) := fun i => Fintype.ofFinite (Option (Act i))
  intro σ
  calc
    ∑ h : G.History, History.terminalWeight (G := G) σ.toProfile h
      = ∑ h : G.History, G.runDist k σ h := by
          refine Finset.sum_congr rfl ?_
          intro h _
          symm
          exact G.runDist_eq_terminalWeight_of_exactHorizon hExact σ h
    _ = 1 := by
          have := PMF.tsum_coe (G.runDist k σ)
          simpa [tsum_fintype] using this

theorem hasNormalizedTerminalLaw_of_boundedHorizon
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι]
    [Fintype G.History] [DecidablePred G.terminal]
    {k : Nat} (hBound : G.BoundedHorizon k) :
    G.HasNormalizedTerminalLaw := by
  let _ : Fintype W := Fintype.ofFinite W
  let _ : ∀ i, Fintype (Option (Act i)) := fun i => Fintype.ofFinite (Option (Act i))
  intro σ
  calc
    ∑ h : G.History, History.terminalWeight (G := G) σ.toProfile h
      = ∑ h : G.History, G.runDist k σ h := by
          refine Finset.sum_congr rfl ?_
          intro h _
          symm
          exact G.runDist_eq_terminalWeight_of_boundedHorizon hBound σ h
    _ = 1 := by
          have := PMF.tsum_coe (G.runDist k σ)
          simpa [tsum_fintype] using this

end

/-- The terminal-history law induced by a legal behavioral profile, assuming
normalization. -/
noncomputable def terminalLawPMF
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw)
    (σ : G.LegalBehavioralProfile) : PMF G.History := by
  classical
  exact PMF.ofFintype
    (fun h => History.terminalWeight (G := G) σ.toProfile h)
    (hNorm σ)

@[simp] theorem terminalLawPMF_apply
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw)
    (σ : G.LegalBehavioralProfile) (h : G.History) :
    G.terminalLawPMF hNorm σ h = History.terminalWeight (G := G) σ.toProfile h := by
  simp [terminalLawPMF, PMF.ofFintype_apply]

theorem terminalLawPMF_eq_runDist_of_boundedHorizon
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [Fintype G.History] [DecidablePred G.terminal]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (σ : G.LegalBehavioralProfile) :
    G.terminalLawPMF (G.hasNormalizedTerminalLaw_of_boundedHorizon hBound) σ = G.runDist k σ := by
  ext h
  rw [G.terminalLawPMF_apply, ← G.runDist_eq_terminalWeight_of_boundedHorizon hBound σ h]

theorem terminalLawPMF_eq_runDist_of_exactHorizon
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [Fintype G.History] [DecidablePred G.terminal]
    {k : Nat} (hExact : G.ExactHorizon k)
    (σ : G.LegalBehavioralProfile) :
    G.terminalLawPMF (G.hasNormalizedTerminalLaw_of_exactHorizon hExact) σ = G.runDist k σ := by
  ext h
  rw [G.terminalLawPMF_apply, G.runDist_eq_terminalWeight_of_exactHorizon hExact σ h]

/-- The `KernelGame` induced by a FOSG whose terminal-history law normalizes on
legal behavioral profiles. -/
noncomputable def toKernelGame
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw) : KernelGame ι where
  Strategy := fun i => G.LegalBehavioralStrategy i
  Outcome := G.History
  utility := fun h i => History.utility h i
  outcomeKernel := fun σ => G.terminalLawPMF hNorm σ

@[simp] theorem toKernelGame_outcomeKernel
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw)
    (σ : G.LegalBehavioralProfile) :
    (G.toKernelGame hNorm).outcomeKernel σ = G.terminalLawPMF hNorm σ := rfl

/-- Expected utility in the induced `KernelGame` is exactly the terminal-history
sum computed from the native FOSG execution semantics. -/
theorem toKernelGame_eu_eq
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [Fintype G.History] [DecidablePred G.terminal]
    (hNorm : G.HasNormalizedTerminalLaw)
    (σ : G.LegalBehavioralProfile) (i : ι) :
    (G.toKernelGame hNorm).eu σ i =
      ∑ h : G.History,
        (History.terminalWeight (G := G) σ.toProfile h).toReal * History.utility h i := by
  rw [KernelGame.eu]
  simp [toKernelGame, terminalLawPMF, expect_eq_sum]

/-- Canonical finite-horizon compilation of a FOSG to `KernelGame`, using the
native history run distribution after exactly `k` steps. This does not require
any terminal-law normalization assumption. -/
noncomputable def toKernelGameAtHorizon
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (k : Nat) : KernelGame ι where
  Strategy := fun i => G.LegalBehavioralStrategy i
  Outcome := G.History
  utility := fun h i => History.utility h i
  outcomeKernel := fun σ => G.runDist k σ

@[simp] theorem toKernelGameAtHorizon_outcomeKernel
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal]
    (k : Nat) (σ : G.LegalBehavioralProfile) :
    (G.toKernelGameAtHorizon k).outcomeKernel σ = G.runDist k σ := rfl

theorem toKernelGameAtHorizon_eu_eq
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal] [Fintype G.History]
    (k : Nat) (σ : G.LegalBehavioralProfile) (i : ι) :
    (G.toKernelGameAtHorizon k).eu σ i =
      ∑ h : G.History, (G.runDist k σ h).toReal * History.utility h i := by
  rw [KernelGame.eu]
  simp [toKernelGameAtHorizon, expect_eq_sum]

/-- Bounded-horizon compilation for FOSGs whose histories are all terminal by
depth `k`. This keeps the horizon run law as the outcome kernel and packages
terminal support as a theorem. -/
noncomputable abbrev toKernelGameOfBoundedHorizon
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [Fintype G.History] [DecidablePred G.terminal]
    {k : Nat} (hBound : G.BoundedHorizon k) : KernelGame ι :=
  G.toKernelGame (G.hasNormalizedTerminalLaw_of_boundedHorizon hBound)

@[simp] theorem toKernelGameOfBoundedHorizon_outcomeKernel
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [Fintype G.History] [DecidablePred G.terminal]
    {k : Nat} (hBound : G.BoundedHorizon k) (σ : G.LegalBehavioralProfile) :
    (G.toKernelGameOfBoundedHorizon hBound).outcomeKernel σ = G.runDist k σ := by
  simpa [toKernelGameOfBoundedHorizon] using
    G.terminalLawPMF_eq_runDist_of_boundedHorizon hBound σ

theorem toKernelGameOfBoundedHorizon_support_isTerminal
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [Fintype G.History] [DecidablePred G.terminal]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (σ : G.LegalBehavioralProfile) (h : G.History)
    (hsupp : h ∈ ((G.toKernelGameOfBoundedHorizon hBound).outcomeKernel σ).support) :
    h.IsTerminal := by
  have hsupp0 : ((G.toKernelGameOfBoundedHorizon hBound).outcomeKernel σ) h ≠ 0 := by
    simpa [PMF.mem_support_iff] using hsupp
  have hsupp' : (G.runDist k σ) h ≠ 0 := by
    rw [← G.toKernelGameOfBoundedHorizon_outcomeKernel hBound σ]
    exact hsupp0
  exact G.runDist_support_isTerminal_of_boundedHorizon hBound σ h hsupp'

theorem toKernelGameOfBoundedHorizon_eu_eq
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [Fintype G.History] [DecidablePred G.terminal]
    {k : Nat} (hBound : G.BoundedHorizon k)
    (σ : G.LegalBehavioralProfile) (i : ι) :
    (G.toKernelGameOfBoundedHorizon hBound).eu σ i =
      ∑ h : G.History, (G.runDist k σ h).toReal * History.utility h i := by
  rw [G.toKernelGame_eu_eq (G.hasNormalizedTerminalLaw_of_boundedHorizon hBound) σ i]
  refine Finset.sum_congr rfl ?_
  intro h _
  rw [← G.runDist_eq_terminalWeight_of_boundedHorizon hBound σ h]

/-- Exact-horizon compilation of a FOSG to `KernelGame`. This uses the generic
terminal-law compile together with the derived normalization proof from
`ExactHorizon`. -/
noncomputable abbrev toKernelGameOfExactHorizon
    (G : FOSG ι W Act PrivObs PubObs)
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [Fintype G.History] [DecidablePred G.terminal]
    {k : Nat} (hExact : G.ExactHorizon k) : KernelGame ι :=
  G.toKernelGame (G.hasNormalizedTerminalLaw_of_exactHorizon hExact)

@[simp] theorem toKernelGameOfExactHorizon_outcomeKernel
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [Fintype G.History] [DecidablePred G.terminal]
    {k : Nat} (hExact : G.ExactHorizon k) (σ : G.LegalBehavioralProfile) :
    (G.toKernelGameOfExactHorizon hExact).outcomeKernel σ = G.runDist k σ := by
  simpa [toKernelGameOfExactHorizon] using
    G.terminalLawPMF_eq_runDist_of_exactHorizon hExact σ

theorem toKernelGameOfExactHorizon_support_isTerminal
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [Fintype G.History] [DecidablePred G.terminal]
    {k : Nat} (hExact : G.ExactHorizon k)
    (σ : G.LegalBehavioralProfile) (h : G.History)
    (hsupp : h ∈ ((G.toKernelGameOfExactHorizon hExact).outcomeKernel σ).support) :
    h.IsTerminal := by
  have hsupp0 : ((G.toKernelGameOfExactHorizon hExact).outcomeKernel σ) h ≠ 0 := by
    simpa [PMF.mem_support_iff] using hsupp
  have hsupp' : (G.runDist k σ) h ≠ 0 := by
    rw [← G.terminalLawPMF_eq_runDist_of_exactHorizon hExact σ]
    simpa [toKernelGameOfExactHorizon] using hsupp0
  exact G.runDist_support_isTerminal_of_exactHorizon hExact σ h hsupp'

theorem toKernelGameOfExactHorizon_eu_eq
    {G : FOSG ι W Act PrivObs PubObs}
    [Fintype ι] [∀ i, Fintype (Option (Act i))] [Fintype W]
    [DecidablePred G.terminal] [Fintype G.History]
    {k : Nat} (hExact : G.ExactHorizon k)
    (σ : G.LegalBehavioralProfile) (i : ι) :
    (G.toKernelGameOfExactHorizon hExact).eu σ i =
      ∑ h : G.History, (G.runDist k σ h).toReal * History.utility h i := by
  rw [G.toKernelGame_eu_eq (G.hasNormalizedTerminalLaw_of_exactHorizon hExact) σ i]
  refine Finset.sum_congr rfl ?_
  intro h _
  rw [G.runDist_eq_terminalWeight_of_exactHorizon hExact σ h]

end FOSG

end GameTheory
