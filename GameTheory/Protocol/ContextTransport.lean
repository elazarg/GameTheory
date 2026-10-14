module

/-
# Optimality under outcome-law coverage

Matching the chosen outcome law and covering every allowed target alternative
by an allowed source alternative transports guarded context optimality.
Existence of all compared expectations is transported with the inequality;
no assumption of finite values is needed.
-/

public import GameTheory.Protocol.Context

@[expose] public section

noncomputable section

namespace GameTheory.Protocol.Context
open GameTheory.Math.Probability

/-- Outcome-law coverage transports optimality, including existence of expectations. -/
theorem IsLocallyOptimal.of_outcome_coverage {Source Target Outcome : Type*}
    {source : Context Source Outcome} {target : Context Target Outcome}
    {sourceAllowed : Set Source} {targetAllowed : Set Target}
    {chosen : Source} {compiled : Target}
    (optimal : source.IsLocallyOptimal sourceAllowed chosen)
    (payoff : target.continuation = source.continuation)
    (honest : target.outcome compiled = source.outcome chosen)
    (coverage : ∀ alternative ∈ targetAllowed, ∃ original ∈ sourceAllowed,
      target.outcome alternative = source.outcome original) :
    target.IsLocallyOptimal targetAllowed compiled := by
  refine ⟨?_, ?_, ?_⟩
  · change HasExpectation (target.outcome compiled) target.continuation
    rw [payoff, honest]
    exact optimal.1
  · intro alternative allowed
    obtain ⟨original, used, same⟩ := coverage alternative allowed
    change HasExpectation (target.outcome alternative) target.continuation
    rw [payoff, same]
    exact optimal.2.1 original used
  · intro alternative allowed
    obtain ⟨original, used, same⟩ := coverage alternative allowed
    change extendedExpect (target.outcome alternative) target.continuation ≤
      extendedExpect (target.outcome compiled) target.continuation
    rw [payoff, same, honest]
    exact optimal.2.2 original used

end GameTheory.Protocol.Context
