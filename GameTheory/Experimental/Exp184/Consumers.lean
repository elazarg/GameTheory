module

public import GameTheory.Experimental.Exp184.Composition
public import GameTheory.Experimental.Exp184.Controls
public import GameTheory.Tests.Backward

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.DynamicChoice

open GameTheory.Math GameTheory.Math.Probability GameTheory.Tests
open GameTheory.Protocol ExecutionProtocol

/-- Every prescribed conditional law makes success possible, including the
genuinely stochastic continuation at the false signal. -/
theorem possibility_conditionally_optimal (signal : Bool) :
    IsOptimalOn (fun _ : Bool => True)
      (fun first second => Potential.supportPreference ()
        (branch signal first) (branch signal second)) (menu signal) signal := by
  refine ⟨trivial, fun _ _ => trivial, fun _ _ => Or.inl ?_⟩
  cases signal
  · exact Potential.true_mem_supportFairLaw
  · simp [branch]

/-- The direct conditional theorem supplies whole-policy optimality for a
preference already proved not to have a real expected-utility representation. -/
theorem possibility_whole_optimal :
    IsOptimalOn (fun _ : Bool → Bool => True)
      (fun first second => Potential.supportPreference () (play first) (play second))
      {policy | ∀ signal ∈ prior.support, policy signal ∈ menu signal} id := by
  apply conditional_optimal prior branch (fun _ => True)
    (Potential.supportPreference ()) menu id
  · exact fun signal _ => possibility_conditionally_optimal signal
  · trivial
  · exact fun _ _ => trivial
  · intro alternative _ comparisons
    exact supportPreference_bind prior _ _ comparisons

/-- Weak mixture preservation does not imply preservation of a strict
comparison when a common continuation is added with positive probability. -/
theorem possibility_strict_cancellation_fails :
    Rank.strict (Potential.supportPreference ()) (PMF.pure true) (PMF.pure false) ∧
    ¬ Rank.strict (Potential.supportPreference ())
      (mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure true) (PMF.pure true))
      (mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure false) (PMF.pure true)) := by
  constructor
  · simp [Rank.strict, Potential.supportPreference]
  · intro strict
    apply strict.2
    exact Or.inl (mem_support_mix_right _ _ _ (by norm_num) (by simp))

namespace Sequential

open GameTheory.Tests.Backward

def success : Spot → Bool
  | .grabbed => true
  | _ => false

def prefers (first second : PMF Spot) : Prop :=
  Potential.supportPreference () (first.map success) (second.map success)

theorem prefers_reflexive (law : PMF Spot) : prefers law law := by
  exact Classical.em (true ∈ (law.map success).support)

theorem prefers_transitive (first middle last : PMF Spot)
    (one : prefers first middle) (two : prefers middle last) : prefers first last := by
  rcases one with present | absent
  · exact Or.inl present
  · rcases two with present | absentLast
    · exact False.elim (absent present)
    · exact Or.inr absentLast

theorem prefers_bind (law : PMF Spot) (first second : Spot → PMF Spot)
    (comparisons : ∀ state ∈ law.support, prefers (first state) (second state)) :
    prefers (law.bind first) (law.bind second) := by
  change Potential.supportPreference () ((law.bind first).map success)
    ((law.bind second).map success)
  simp only [PMF.map_bind]
  exact supportPreference_bind law _ _ comparisons

/-- At either genuine nonterminal site, the grab policy makes success
possible. Chance remains a real fair mixture at the root. -/
theorem grab_oneShot_optimal (state : Spot) (nonterminal : ¬ probe.terminal state) :
    IsOptimalOn (fun _ => True)
      (fun first second => prefers
        ((probe.step state first).bind (probe.backwardLaw probe_wellFoundedPlay (policy .grab)))
        ((probe.step state second).bind (probe.backwardLaw probe_wellFoundedPlay (policy .grab))))
      Set.univ (policy .grab state nonterminal) := by
  refine ⟨trivial, fun _ _ => trivial, fun _ _ => ?_⟩
  change true ∈ (((probe.step state (policy .grab state nonterminal)).bind
    (probe.backwardLaw probe_wellFoundedPlay (policy .grab))).map success).support ∨ _
  apply Or.inl
  rw [← probe.backwardLaw_of_not_terminal_bind nonterminal]
  cases state with
  | flip =>
      rw [backwardLaw_flip, mix_map]
      exact mem_support_mix_left _ _ _ (by norm_num) (by simp [success, Move.outcome])
  | pick => simp [backwardLaw_pick, Move.outcome, success]
  | grabbed => exact False.elim (nonterminal (Or.inl rfl))
  | passed => exact False.elim (nonterminal (Or.inr rfl))

/-- The same raw comparison law drives a second composition client: actual
well-founded protocol laws, against every state-aware competing chooser. -/
theorem grab_whole_optimal (state : Spot) :
    IsOptimalOn (fun _ : probe.Chooser => True)
      (fun first second => prefers
        (probe.backwardLaw probe_wellFoundedPlay first state)
        (probe.backwardLaw probe_wellFoundedPlay second state)) Set.univ (policy .grab) := by
  apply backward_optimal probe_wellFoundedPlay (policy .grab) (fun _ => True) prefers
    (fun law _ => prefers_reflexive law) prefers_transitive
    (fun _ _ => trivial) grab_oneShot_optimal
  intro source nonterminal other _ _ comparisons
  exact prefers_bind (probe.step source (other source nonterminal)) _ _ comparisons

end Sequential

end GameTheory.Experimental.DynamicChoice
