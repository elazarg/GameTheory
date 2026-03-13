import GameTheory.Languages.MAID.CompileObs
import GameTheory.Theorems.Kuhn

/-!
# GameTheory.Languages.MAID.Kuhn

Kuhn reduction lemmas for compiled MAIDs via `ObsModelCore`.

## Main results

- `kuhn_behavioral_to_mixed_compiledPR` : B→M direction via `compileObsCoreModelPR`,
  under `NoNontrivialInfoStateRepeat` (which holds for well-formed MAIDs)

## Architecture

**B→M** uses `compileObsCoreModelPR`, which compiles MAIDs with observation-dependent
action types (`CompiledMAIDAct`). Under perfect recall, at most one infoset per player
is active at any frontier step, and `NoNontrivialInfoStateRepeat` holds because each
decision node is processed exactly once in the frontier evaluation.

**M→B** requires linearized compilation (one node per step) to satisfy
`StepSupportFactorization`, since the simultaneous frontier compilation has
multiple players acting at once. This is planned but not yet implemented.
-/

namespace GameTheory.Languages.MAID

open _root_.MAID
open GameTheory.Theorems

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

section KuhnBToM

variable (S : Struct Player n) (sem : Sem S)

/-- The compiled PR ObsModelCore for a MAID. -/
noncomputable abbrev compiledPRObs (S : Struct Player n) (sem : Sem S) :=
  compileObsCoreModelPR S sem

/-- **Kuhn B→M for compiled MAIDs (PR model)**: behavioral strategies can be
realized as product mixed strategies, given the no-nontrivial-info-state-repeat
condition.

Under perfect recall, this condition holds automatically because each
decision node is processed exactly once in the frontier evaluation. -/
theorem kuhn_behavioral_to_mixed_compiledPR
    [∀ p, Fintype ((compiledPRObs S sem).InfoState p)]
    [∀ p, Fintype ((compiledPRObs S sem).LocalStrategy p)]
    (hNR : (compiledPRObs S sem).NoNontrivialInfoStateRepeat)
    (β : ObsModelCore.BehavioralProfile (compiledPRObs S sem)) (k : Nat) :
    (compiledPRObs S sem).runDist k β =
      ((compiledPRObs S sem).behavioralToMixedJoint β).bind
        ((compiledPRObs S sem).runDistPure k) :=
  ObsModelCore.kuhn_behavioral_to_mixed hNR β k

/-- `NoNontrivialInfoStateRepeat` holds for the PR-compiled MAID: each decision
node is processed exactly once in the topological frontier evaluation, so the
same nontrivial infoset `some I` cannot appear at two positions on a trace. -/
theorem noNontrivialInfoStateRepeat_compiledPR
    (hPR : S.PerfectRecall) :
    (compiledPRObs S sem).NoNontrivialInfoStateRepeat := by
  sorry

end KuhnBToM

end GameTheory.Languages.MAID
