module

/-
# Explicit chance transitions

In an extensive-form presentation with explicit Nature nodes, choosing a
player's action determines the next state. Stochastic transitions occur at
states with no active player. This property is a certificate on a protocol,
not a restriction built into general stochastic execution semantics.
-/

public import GameTheory.Protocol.History

@[expose] public section

namespace GameTheory.Protocol.ExecutionProtocol

universe uι

variable {ι : Type uι} (E : ExecutionProtocol ι)

/-- At every reachable state with an active player, each legal joint action
has a deterministic successor. Random draws are represented by separate
states with no active player. -/
def HasExplicitChance : Prop :=
  ∀ history : E.History, (∃ who, E.active history.state who) →
    ∀ joint : {joint // E.Legal history.state joint},
      ∃ target, E.step history.state joint = PMF.pure target

/-- Two possible successors of one legal player action refute an
explicit-chance presentation. -/
theorem not_hasExplicitChance_of_distinct_supported
    (history : E.History) (active : ∃ who, E.active history.state who)
    (joint : {joint // E.Legal history.state joint})
    {first second : E.State} (distinct : first ≠ second)
    (firstSupported : first ∈ (E.step history.state joint).support)
    (secondSupported : second ∈ (E.step history.state joint).support) :
    ¬ E.HasExplicitChance := by
  intro explicit
  obtain ⟨target, deterministic⟩ := explicit history active joint
  rw [deterministic, PMF.mem_support_pure_iff] at firstSupported secondSupported
  exact distinct (firstSupported.trans secondSupported.symm)

end GameTheory.Protocol.ExecutionProtocol
