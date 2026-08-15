/-
EFG-facing one-shot deviation integration test.

The already-hostile two-decision perfect-recall EFG is also well founded. This
discharges the EFG wrapper's structural hypotheses on an actual multi-step
game; the Protocol test separately retains the profitable off-path deviation.
-/

import GameTheory.Languages.EFG.SubgamePerfect
import GameTheory.Tests.EFGKuhn

noncomputable section

namespace GameTheory.Tests.EFGSubgamePerfect

open GameTheory GameTheory.Languages GameTheory.Protocol
open GameTheory.Math.Probability
open GameTheory.Protocol.ExecutionProtocol
open GameTheory.Tests.Randomized

def twiceRank : Round → ℕ
  | .start => 2
  | .after _ => 1
  | .done _ _ => 0

theorem twiceRank_decreases
    (source target : Round)
    (hsuccessor : twice.Successor target source) :
    twiceRank target < twiceRank source := by
  rcases hsuccessor with ⟨joint, isLegal, htarget⟩
  cases source with
  | start =>
      cases hchoice : joint () with
      | none =>
          simp [twice, hchoice, FinDist.mem_support_pure] at htarget
          subst target
          norm_num [twiceRank]
      | some vote =>
          cases vote <;>
            simp [twice, hchoice, FinDist.mem_support_pure] at htarget <;>
            subst target <;>
            norm_num [twiceRank]
  | after first =>
      cases hchoice : joint () with
      | none =>
          simp [twice, hchoice, FinDist.mem_support_pure] at htarget
          subst target
          norm_num [twiceRank]
      | some vote =>
          cases vote <;>
            simp [twice, hchoice, FinDist.mem_support_pure] at htarget <;>
            subst target <;>
            norm_num [twiceRank]
  | done first second =>
      exact False.elim (isLegal.1 (by simp [Round.stopped]))

theorem twice_wellFoundedPlay : twice.WellFoundedPlay :=
  wellFoundedPlay_of_rank twiceRank twiceRank_decreases

end GameTheory.Tests.EFGSubgamePerfect

namespace GameTheory.Tests.EFGSubgamePerfect

open GameTheory GameTheory.Languages GameTheory.Protocol

/-- The EFG surface reduces directly to the canonical historywise Protocol
equivalence on a two-decision perfect-recall game. -/
theorem oneShotDeviation_iff_historywiseOptimal
    (profile : Profile EFGKuhn.recallGame.strategicSignature)
    (utility : EFGKuhn.recallGame.History → Unit → ℝ) :
    EFGKuhn.recallGame.IsHistorywiseOptimal
        twice_wellFoundedPlay profile utility ↔
      EFGKuhn.recallGame.HasNoProfitableOneShotDeviation
        twice_wellFoundedPlay profile utility :=
  EFGKuhn.recallGame.isHistorywiseOptimal_iff_hasNoProfitableOneShotDeviation
    EFGKuhn.recallGame_actsOnce twice_wellFoundedPlay profile utility

end GameTheory.Tests.EFGSubgamePerfect
