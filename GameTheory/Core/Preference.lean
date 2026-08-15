/-
# Preferences over finite outcome laws

The probability-free relation algebra lives in `GameTheory.Core.Rank`.
This module supplies the specialization used by equilibrium theory: agents
compare finite laws over outcomes. Only the definitions that genuinely inspect
laws—convexity under mixing and pullback along an outcome relabeling—belong
here.

Preferences remain explicit arguments, never typeclass instances. The
orientation

`weaklyPrefers agent preferred alternative`

means that `agent` weakly prefers `preferred` to `alternative`.
-/

import GameTheory.Core.Rank
import GameTheory.Math.Probability.FinDist

namespace GameTheory

open GameTheory.Math.Probability

universe ua uα uo uo'

/-- A weak preference over outcome laws, held by each agent. -/
abbrev WeakPreference (Agent : Type ua) (Outcome : Type uo) :=
  Ranking Agent (FinDist Outcome)

namespace Preference

variable
  {Agent : Type ua} {α : Type uα}
  {Outcome : Type uo} {Outcome' : Type uo'}

/-- A preference respects mixing: comparing two pairs the same way compares
their mixtures the same way. Expected utility satisfies it, and it is what
makes a solution concept defined by comparing laws a convex set. Nothing forces
a weak preference to be convex, so it is a hypothesis rather than a field. -/
def Convex (weaklyPrefers : WeakPreference Agent Outcome) : Prop :=
  ∀ (agent : Agent) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (firstPreferred firstAlternative secondPreferred secondAlternative :
      FinDist Outcome),
    weaklyPrefers agent firstPreferred firstAlternative →
    weaklyPrefers agent secondPreferred secondAlternative →
      weaklyPrefers agent
        (FinDist.mix t h0 h1 firstPreferred secondPreferred)
        (FinDist.mix t h0 h1 firstAlternative secondAlternative)

/-- Pull a preference back along an outcome relabeling. -/
def comapOutcome
    (relabel : Outcome → Outcome')
    (weaklyPrefers : WeakPreference Agent Outcome') :
    WeakPreference Agent Outcome :=
  fun agent preferred alternative =>
    weaklyPrefers agent
      (preferred.map relabel)
      (alternative.map relabel)

@[simp]
theorem comapOutcome_apply
    (relabel : Outcome → Outcome')
    (weaklyPrefers : WeakPreference Agent Outcome')
    (agent : Agent) (preferred alternative : FinDist Outcome) :
    comapOutcome relabel weaklyPrefers agent preferred alternative =
      weaklyPrefers agent
        (preferred.map relabel)
        (alternative.map relabel) :=
  rfl

end Preference

end GameTheory
