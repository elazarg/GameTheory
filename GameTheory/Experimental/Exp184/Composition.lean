module

/-
# Conditional comparisons and backward composition

Direct hypotheses separate comparison preservation under an actual prior from
admissibility of whole policies. Conditional evaluation-domain membership alone
does not establish that a mixture has a defined value.
-/

public import GameTheory.Protocol.Backward

@[expose] public section

namespace GameTheory.Experimental.DynamicChoice

open GameTheory.Math GameTheory.Protocol

/-- Conditional optimality composes when actual whole laws are admissible and
the actual prior preserves the comparisons. Off-support choices are irrelevant.
As with `IsOptimalOn`, incumbent membership is a separate feasibility question. -/
theorem conditional_optimal
    {Signal Action Outcome : Type*} (prior : PMF Signal)
    (outcome : Signal → Action → PMF Outcome)
    (admissible : PMF Outcome → Prop) (prefers : PMF Outcome → PMF Outcome → Prop)
    (allowed : Signal → Set Action) (chosen : Signal → Action)
    (conditional : ∀ signal ∈ prior.support,
      IsOptimalOn (fun action => admissible (outcome signal action))
        (fun first second => prefers (outcome signal first) (outcome signal second))
        (allowed signal) (chosen signal))
    (chosen_defined : admissible (prior.bind fun signal => outcome signal (chosen signal)))
    (alternatives_defined : ∀ alternative : Signal → Action,
      (∀ signal ∈ prior.support, alternative signal ∈ allowed signal) →
      admissible (prior.bind fun signal => outcome signal (alternative signal)))
    (compose : ∀ alternative : Signal → Action,
      (∀ signal ∈ prior.support, alternative signal ∈ allowed signal) →
      (∀ signal ∈ prior.support,
        prefers (outcome signal (chosen signal)) (outcome signal (alternative signal))) →
      prefers (prior.bind fun signal => outcome signal (chosen signal))
        (prior.bind fun signal => outcome signal (alternative signal))) :
    IsOptimalOn
      (fun policy => admissible (prior.bind fun signal => outcome signal (policy signal)))
      (fun first second => prefers (prior.bind fun signal => outcome signal (first signal))
        (prior.bind fun signal => outcome signal (second signal)))
      {policy | ∀ signal ∈ prior.support, policy signal ∈ allowed signal} chosen := by
  refine ⟨chosen_defined, alternatives_defined, fun alternative offered => ?_⟩
  exact compose alternative offered fun signal supported =>
    (conditional signal supported).2.2 _ (offered signal supported)

/-- Well-founded one-shot comparisons compose without a numerical score.
Admissibility of actual whole-policy laws is explicit, independently of the
guards on the one-shot laws. Comparison closure is needed only for actual
alternative transitions and their two continuation kernels. -/
theorem backward_optimal
    {ι : Type*} {E : ExecutionProtocol ι} (certificate : E.WellFoundedPlay)
    (optimal : E.Chooser) (admissible : PMF E.State → Prop)
    (prefers : PMF E.State → PMF E.State → Prop)
    (reflexive : ∀ law, admissible law → prefers law law)
    (transitive : ∀ first middle last, prefers first middle →
      prefers middle last → prefers first last)
    (whole_defined : ∀ chooser state, admissible (E.backwardLaw certificate chooser state))
    (conditional : ∀ state (nonterminal : ¬ E.terminal state),
      IsOptimalOn
        (fun choice => admissible
          ((E.step state choice).bind (E.backwardLaw certificate optimal)))
        (fun first second => prefers
          ((E.step state first).bind (E.backwardLaw certificate optimal))
          ((E.step state second).bind (E.backwardLaw certificate optimal)))
        Set.univ (optimal state nonterminal))
    (compose : ∀ state (nonterminal : ¬ E.terminal state) (other : E.Chooser),
      admissible ((E.step state (other state nonterminal)).bind
        (E.backwardLaw certificate optimal)) →
      admissible ((E.step state (other state nonterminal)).bind
        (E.backwardLaw certificate other)) →
      (∀ next ∈ (E.step state (other state nonterminal)).support,
        prefers (E.backwardLaw certificate optimal next)
          (E.backwardLaw certificate other next)) →
      prefers ((E.step state (other state nonterminal)).bind
        (E.backwardLaw certificate optimal))
        ((E.step state (other state nonterminal)).bind
          (E.backwardLaw certificate other))) :
    ∀ state, IsOptimalOn
      (fun chooser => admissible (E.backwardLaw certificate chooser state))
      (fun first second => prefers (E.backwardLaw certificate first state)
        (E.backwardLaw certificate second state)) Set.univ optimal := by
  intro state
  refine ⟨whole_defined optimal state, fun other _ => whole_defined other state, ?_⟩
  intro other _
  induction state using certificate.induction with
  | _ state ih =>
      by_cases stopped : E.terminal state
      · rw [E.backwardLaw_of_terminal stopped, E.backwardLaw_of_terminal stopped]
        apply reflexive
        simpa only [E.backwardLaw_of_terminal stopped] using whole_defined optimal state
      · have one := conditional state stopped
        have other_defined : admissible
            ((E.step state (other state stopped)).bind
              (E.backwardLaw certificate other)) := by
          rw [← E.backwardLaw_of_not_terminal_bind stopped]
          exact whole_defined other state
        have improved := compose state stopped other
          (one.2.1 _ (Set.mem_univ _)) other_defined
          (fun next supported => ih next
            ⟨(other state stopped).1, (other state stopped).2, supported⟩)
        rw [E.backwardLaw_of_not_terminal_bind stopped,
          E.backwardLaw_of_not_terminal_bind stopped]
        exact transitive _ _ _ (one.2.2 _ (Set.mem_univ _)) improved

end GameTheory.Experimental.DynamicChoice
