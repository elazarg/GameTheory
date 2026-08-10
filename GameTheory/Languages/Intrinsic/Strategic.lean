/-
# Strategic form of a selected intrinsic closed-loop solution

A uniquely solvable intrinsic model at a caller-supplied nature value already
has a deterministic strategic outcome: the complete configuration containing
its selected fixed point.  This leaf compiles that outcome to the canonical
static core. Utilities remain external, and equilibrium remains ordinary
`IsNash`.

No temporal execution, nature lottery, mixed strategy, or intrinsic-specific
solution predicate is introduced here.
-/

import GameTheory.Languages.Intrinsic.Solution
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Languages.Intrinsic.Model

open GameTheory.Probability

universe uAgent uNature uDecision

/-- Intrinsic agents own their complete information-local decision rules; the
outcome retains the selected closed-loop configuration. -/
abbrev strategicSignature
    (M : Model.{uAgent, uNature, uDecision}) : GameSignature M.Agent where
  Strategy := M.PureStrategy
  Outcome := M.Configuration

/-- Compile one fixed nature state by selecting the certified unique
closed-loop solution. -/
@[reducible]
def toGameForm (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (nature : M.Nature) : GameForm M.Agent where
  sig := M.strategicSignature
  play profile := FinDist.pure
    ⟨nature, M.solution solvable profile nature⟩

@[simp]
theorem toGameForm_play (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (nature : M.Nature)
    (profile : M.PureProfile) :
    (M.toGameForm solvable nature).play profile =
      FinDist.pure ⟨nature, M.solution solvable profile nature⟩ := rfl

/-- Canonical Nash is exactly comparison of the re-solved configuration after
one intrinsic agent replaces its complete decision rule. -/
theorem isNash_toGameForm_iff
    (M : Model.{uAgent, uNature, uDecision})
    (solvable : M.IsSolvable) (nature : M.Nature)
    [DecidableEq M.Agent] (utility : M.Configuration → M.Agent → ℝ)
    (profile : M.PureProfile) :
    IsNash (M.toGameForm solvable nature) (euPreference utility) profile ↔
      ∀ who replacement,
        utility
            ⟨nature, M.solution solvable
              (Profile.update (sig := M.strategicSignature)
                profile who replacement) nature⟩ who ≤
          utility ⟨nature, M.solution solvable profile nature⟩ who := by
  rw [isNash_iff]
  simp only [euPreference_apply, expectedUtility_pure]

end GameTheory.Languages.Intrinsic.Model
