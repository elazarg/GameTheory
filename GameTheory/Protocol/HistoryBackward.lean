/-
# Deterministic terminal histories

The historywise terminal law is the point-mass specialization of the general
well-founded randomized law. Its values and one-shot properties use that law.
-/

import GameTheory.Protocol.RandomizedBackward

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace ExecutionProtocol

variable (E)

/-- The deterministic terminal-history law specializes the randomized law to
point-mass choices. -/
def historyBackwardLaw (certificate : E.WellFoundedPlay)
    (chooser : E.HistoryChooser) : E.History → PMF E.History :=
  E.randomizedBackwardLaw certificate chooser.toRandomized

open Classical in
theorem historyBackwardLaw_eq (certificate : E.WellFoundedPlay)
    (chooser : E.HistoryChooser) (history : E.History) :
    E.historyBackwardLaw certificate chooser history =
      if hterm : E.terminal history.state then PMF.pure history
      else
        let chosen := chooser history hterm
        (E.step history.state chosen).bindOnSupport fun _target realized =>
          E.historyBackwardLaw certificate chooser
            (history.extend chosen.2 realized) := by
  rw [historyBackwardLaw, E.randomizedBackwardLaw_eq]
  by_cases hterm : E.terminal history.state
  · simp only [dite_eq_left hterm]
  · simp only [dite_eq_right hterm, HistoryChooser.toRandomized, PMF.pure_bind]

theorem historyBackwardLaw_of_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {history : E.History} (hterm : E.terminal history.state) :
    E.historyBackwardLaw certificate chooser history = PMF.pure history := by
  rw [historyBackwardLaw_eq, dite_eq_left hterm]

theorem historyBackwardLaw_of_not_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {history : E.History} (hterm : ¬ E.terminal history.state) :
    E.historyBackwardLaw certificate chooser history =
      (E.step history.state (chooser history hterm)).bindOnSupport
        fun _target realized =>
          E.historyBackwardLaw certificate chooser
            (history.extend (chooser history hterm).2 realized) := by
  rw [historyBackwardLaw_eq, dite_eq_right hterm]

/-- Rewrite the nonterminal law using an equal chosen joint action without
exposing dependent legality proofs at callers. -/
theorem historyBackwardLaw_of_not_terminal_of_chooser_eq
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {history : E.History} (hterm : ¬ E.terminal history.state)
    (chosen : { joint : ∀ i, Option (E.Action i) //
      E.Legal history.state joint })
    (hchosen : chooser history hterm = chosen) :
    E.historyBackwardLaw certificate chooser history =
      (E.step history.state chosen).bindOnSupport fun _target realized =>
        E.historyBackwardLaw certificate chooser
          (history.extend chosen.2 realized) := by
  calc
    E.historyBackwardLaw certificate chooser history =
        (E.step history.state (chooser history hterm)).bindOnSupport
          fun _target realized => E.historyBackwardLaw certificate chooser
            (history.extend (chooser history hterm).2 realized) :=
      E.historyBackwardLaw_of_not_terminal hterm
    _ = (E.step history.state chosen).bindOnSupport
          fun _target realized => E.historyBackwardLaw certificate chooser
            (history.extend chosen.2 realized) :=
      congrArg (fun selected : { joint : ∀ i, Option (E.Action i) //
        E.Legal history.state joint } =>
        (E.step history.state selected).bindOnSupport fun _target realized =>
          E.historyBackwardLaw certificate chooser
            (history.extend selected.2 realized)) hchosen

/-- Every supported outcome of the well-founded history law is terminal. -/
theorem historyBackwardLaw_support_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    (history : E.History) :
    ∀ final ∈ (E.historyBackwardLaw certificate chooser history).support,
      E.terminal final.state := by
  exact E.randomizedBackwardLaw_support_terminal history

/-- Boundedness only on terminal histories is sufficient for any well-founded
history chooser's real payoff to be defined. -/
theorem payoffIntegrable_historyBackwardLaw_of_bounded_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {payoff : E.History → ℝ} {C : ℝ}
    (hbound : ∀ final, E.terminal final.state → |payoff final| ≤ C)
    (history : E.History) :
    PayoffIntegrable (E.historyBackwardLaw certificate chooser history) payoff := by
  exact E.payoffIntegrable_randomizedBackwardLaw_of_bounded_terminal hbound history

/-- Finite support at each legal transition also makes every well-founded
terminal payoff integrable, without any bound on the payoff itself. -/
theorem payoffIntegrable_historyBackwardLaw_of_finite_step_support
    {certificate : E.WellFoundedPlay}
    (hfinite : ∀ (history : E.History) (_hterm : ¬ E.terminal history.state)
      (chosen : {joint : ∀ i, Option (E.Action i) //
        E.Legal history.state joint}),
      (E.step history.state chosen).support.Finite)
    (chooser : E.HistoryChooser) (payoff : E.History → ℝ)
    (history : E.History) :
    PayoffIntegrable (E.historyBackwardLaw certificate chooser history) payoff := by
  induction history using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ current ih =>
      by_cases hterm : E.terminal current.state
      · rw [E.historyBackwardLaw_of_terminal hterm]
        exact payoffIntegrable_pure current payoff
      · rw [E.historyBackwardLaw_of_not_terminal hterm]
        exact payoffIntegrable_bindOnSupport_of_finite_support
          (E.step current.state (chooser current hterm))
          (fun _target realized => E.historyBackwardLaw certificate chooser
            (current.extend (chooser current hterm).2 realized)) payoff
          (hfinite current hterm (chooser current hterm))
          (fun _target realized =>
            ih (current.extend (chooser current hterm).2 realized)
              ⟨(chooser current hterm).1,
                (chooser current hterm).2, realized⟩)

/-- A history chooser has stopped at this fuel when the forward law contains
only terminal histories. -/
def StopsHistoryWithin (chooser : E.HistoryChooser)
    (horizon : ℕ) (history : E.History) : Prop :=
  ∀ final ∈ (E.runHistoryFor chooser horizon history).support,
    E.terminal final.state

theorem stopsHistoryWithin_of_bound {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (chooser : E.HistoryChooser) (history : E.History) :
    E.StopsHistoryWithin chooser bound history := by
  intro final reached
  have randomized := reached
  rw [← E.runRandomizedFor_toRandomized] at randomized
  rcases E.runRandomizedFor_terminal_or_length _ _ _ _ randomized with stopped | consumed
  · exact stopped
  · exact bounded final.state final.trace (by omega)

/-- The well-founded history law agrees with any forward run that has stopped. -/
theorem historyBackwardLaw_eq_runHistoryFor
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {horizon : ℕ} {history : E.History}
    (hstop : E.StopsHistoryWithin chooser horizon history) :
    E.historyBackwardLaw certificate chooser history =
      E.runHistoryFor chooser horizon history := by
  have hstopRandomized :
      ∀ final ∈
        (E.runRandomizedFor chooser.toRandomized horizon history).support,
        E.terminal final.state := by
    unfold StopsHistoryWithin at hstop
    simpa only [E.runRandomizedFor_toRandomized] using hstop
  simpa only [historyBackwardLaw, E.runRandomizedFor_toRandomized] using
    (E.randomizedBackwardLaw_eq_runRandomizedFor hstopRandomized)

/-- A real history value requires finite integrability under its terminal law. -/
def historyBackwardValue (certificate : E.WellFoundedPlay)
    (chooser : E.HistoryChooser) (payoff : E.History → ℝ)
    (history : E.History)
    (hintegrable : PayoffIntegrable
      (E.historyBackwardLaw certificate chooser history) payoff) : ℝ :=
  expect (E.historyBackwardLaw certificate chooser history) payoff hintegrable

theorem historyBackwardValue_of_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {payoff : E.History → ℝ} {history : E.History}
    (hterm : E.terminal history.state)
    (hintegrable : PayoffIntegrable
      (E.historyBackwardLaw certificate chooser history) payoff) :
    E.historyBackwardValue certificate chooser payoff history hintegrable =
      payoff history := by
  have hpure : PayoffIntegrable (PMF.pure history) payoff := by
    rw [← E.historyBackwardLaw_of_terminal hterm]
    exact hintegrable
  unfold historyBackwardValue expect
  rw [E.historyBackwardLaw_of_terminal hterm]
  exact expect_pure history payoff hpure

/-- Numerical history Bellman equation on supported realized successors.
The source law guard supplies the conditional and outer guards. -/
theorem historyBackwardValue_of_not_terminal
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {payoff : E.History → ℝ} {history : E.History}
    (hterm : ¬ E.terminal history.state)
    (hsource : PayoffIntegrable
      (E.historyBackwardLaw certificate chooser history) payoff)
    (successorValue : E.State → ℝ)
    (hvalue : ∀ target, ∀ realized :
      target ∈ (E.step history.state (chooser history hterm)).support,
      ∀ hchild : PayoffIntegrable
        (E.historyBackwardLaw certificate chooser
          (history.extend (chooser history hterm).2 realized)) payoff,
        successorValue target =
          E.historyBackwardValue certificate chooser payoff
            (history.extend (chooser history hterm).2 realized) hchild) :
    ∃ houter : PayoffIntegrable
        (E.step history.state (chooser history hterm)) successorValue,
      E.historyBackwardValue certificate chooser payoff history hsource =
        expect (E.step history.state (chooser history hterm))
          successorValue houter := by
  let chosen := chooser history hterm
  let p := E.step history.state chosen
  let q : ∀ target, target ∈ p.support → PMF E.History :=
    fun _target realized =>
      E.historyBackwardLaw certificate chooser (history.extend chosen.2 realized)
  have hbind : PayoffIntegrable (p.bindOnSupport q) payoff := by
    rw [← E.historyBackwardLaw_of_not_terminal hterm]
    exact hsource
  have hcond : ∀ target, ∀ realized : target ∈ p.support,
      successorValue target = expect (q target realized) payoff
        (payoffIntegrable_bindOnSupport_conditional_on_support
          p q payoff hbind target realized) := by
    intro target realized
    exact hvalue target realized _
  let houter := payoffIntegrable_bindOnSupport_conditionalValue_on_support
    p q payoff hbind successorValue hcond
  refine ⟨houter, ?_⟩
  have htower := expect_bindOnSupport_tower_on_support
    p q payoff hbind successorValue hcond
  unfold historyBackwardValue expect at htower ⊢
  rw [E.historyBackwardLaw_of_not_terminal hterm]
  exact htower

theorem historyBackwardValue_eq_expect_runHistoryFor
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {payoff : E.History → ℝ} {horizon : ℕ} {history : E.History}
    (hstop : E.StopsHistoryWithin chooser horizon history)
    (hback : PayoffIntegrable
      (E.historyBackwardLaw certificate chooser history) payoff)
    (hrun : PayoffIntegrable (E.runHistoryFor chooser horizon history) payoff) :
    E.historyBackwardValue certificate chooser payoff history hback =
      expect (E.runHistoryFor chooser horizon history) payoff hrun := by
  unfold historyBackwardValue expect
  rw [E.historyBackwardLaw_eq_runHistoryFor hstop]

theorem historyBackwardValue_eq_expect_runHistoryFor_guarded
    {certificate : E.WellFoundedPlay} {chooser : E.HistoryChooser}
    {payoff : E.History → ℝ} {horizon : ℕ} {history : E.History}
    (hstop : E.StopsHistoryWithin chooser horizon history)
    (hback : PayoffIntegrable
      (E.historyBackwardLaw certificate chooser history) payoff) :
    ∃ hrun : PayoffIntegrable (E.runHistoryFor chooser horizon history) payoff,
      E.historyBackwardValue certificate chooser payoff history hback =
        expect (E.runHistoryFor chooser horizon history) payoff hrun := by
  let hrun : PayoffIntegrable (E.runHistoryFor chooser horizon history) payoff := by
    rw [← E.historyBackwardLaw_eq_runHistoryFor hstop]
    exact hback
  exact ⟨hrun, E.historyBackwardValue_eq_expect_runHistoryFor hstop hback hrun⟩

/-- Unbounded reachability between histories, expressed through the existing
finite path witness rather than a second transition relation. -/
def HistoryReaches (start target : E.History) : Prop :=
  ∃ fuel, E.ReachesWithin fuel start target

theorem HistoryReaches.refl (history : E.History) :
    E.HistoryReaches history history :=
  ⟨0, .refl 0 history⟩

theorem HistoryReaches.step {start target : E.History}
    {joint : ∀ i, Option (E.Action i)}
    (isLegal : E.Legal start.state joint)
    {reached : E.State}
    (realized :
      reached ∈ (E.step start.state ⟨joint, isLegal⟩).support)
    (rest : E.HistoryReaches (start.extend isLegal realized) target) :
    E.HistoryReaches start target := by
  rcases rest with ⟨fuel, hrest⟩
  exact ⟨fuel + 1, .step joint isLegal realized hrest⟩

/-- Choosers agreeing on the reachable history cone have the same terminal law. -/
theorem historyBackwardLaw_congr_of_reaches
    {certificate : E.WellFoundedPlay}
    {first second : E.HistoryChooser} :
    ∀ start : E.History,
      (∀ later, E.HistoryReaches start later →
        ∀ hterm : ¬ E.terminal later.state,
          first later hterm = second later hterm) →
      E.historyBackwardLaw certificate first start =
        E.historyBackwardLaw certificate second start := by
  intro start
  induction start using
      (E.wellFounded_historySuccessor certificate).induction with
  | _ history ih =>
      intro hagree
      by_cases hterm : E.terminal history.state
      · rw [E.historyBackwardLaw_of_terminal hterm,
          E.historyBackwardLaw_of_terminal hterm]
      · rw [E.historyBackwardLaw_of_not_terminal hterm,
          E.historyBackwardLaw_of_not_terminal hterm,
          hagree history (HistoryReaches.refl E history) hterm]
        apply bindOnSupport_congr
        intro target realized
        let chosen := second history hterm
        exact ih (history.extend chosen.2 realized)
          ⟨chosen.1, chosen.2, realized⟩
          (fun later hreach =>
            hagree later (HistoryReaches.step E chosen.2 realized hreach))

theorem historyBackwardValue_congr_of_reaches
    {certificate : E.WellFoundedPlay}
    {first second : E.HistoryChooser}
    {payoff : E.History → ℝ} (start : E.History)
    (hagree : ∀ later, E.HistoryReaches start later →
      ∀ hterm : ¬ E.terminal later.state,
        first later hterm = second later hterm)
    (hfirst : PayoffIntegrable (E.historyBackwardLaw certificate first start) payoff)
    (hsecond : PayoffIntegrable (E.historyBackwardLaw certificate second start) payoff) :
    E.historyBackwardValue certificate first payoff start hfirst =
      E.historyBackwardValue certificate second payoff start hsecond := by
  unfold historyBackwardValue expect
  rw [E.historyBackwardLaw_congr_of_reaches start hagree]

end ExecutionProtocol


end GameTheory.Protocol
