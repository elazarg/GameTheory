/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalNashDispatch
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

/-!
# The exact gate for returning a causal escaping tail

The tail-escape branch already contains all data needed to retain its literal
causal atom after one cap--Nash prefix.  The sole extra datum is a cap--Nash
root whose absorption charge spends the tail excess, with positive survival.

This file packages that exact implication.  It is intentionally a gate, not
a producer: an all-Continue cap root has zero absorption and therefore cannot
meet a strict return selection.  No terminal law, semantic point, or suffix
chronology is replaced in the statement.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- **Causal tail-escape return gate.**

Prefix the actual escaped continuation by an exact Nash root against its
behavioral cap.  If that same root spends enough of the escape to enter the
requested minimum-debt neighborhood and retains positive joint Continue
mass, then the original positive suffix atom survives literally one stage
later.  Thus the absorption-spend selection is the only missing premise;
semantic return and causal-law retention require no further compactness or
reprojection.
-/
theorem capNashTailEscapeReturnSelection_retains_causalSuffixAtom
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (continuation : (quittingGame reward).BehaviorProfile)
    (root : iota → PMF Bool) (stage : ℕ)
    (terminal : {S : Finset iota // S.Nonempty})
    (tolerance : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hselection : IsQuittingCapNashResetReturnSelection
      (reward := reward) minimum
        (quittingTerminalSemanticPair reward continuation) root tolerance)
    (hcontinue : 0 < quittingStationaryContinueMass root)
    (hatom : 0 < quittingStageCoalitionMass
      reward continuation stage terminal) :
    let returnedProfile :=
      quittingRootThenContinuationProfile reward root continuation
    quittingTerminalSemanticPair reward returnedProfile ∈
        quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward returnedProfile) ∧
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward returnedProfile) ≤
        quittingTerminalSemanticDebtSum minimum + tolerance ∧
      quittingStageCoalitionMass reward returnedProfile (stage + 1) terminal =
        quittingStationaryContinueMass root *
          quittingStageCoalitionMass reward continuation stage terminal ∧
      0 < quittingStageCoalitionMass
        reward returnedProfile (stage + 1) terminal := by
  dsimp only
  let tail := quittingTerminalSemanticPair reward continuation
  let returned := quittingTerminalSemanticPrefix reward root tail
  have hsemantic : quittingTerminalSemanticPair reward
      (quittingRootThenContinuationProfile reward root continuation) =
        returned := by
    simpa only [tail, returned] using
      quittingTerminalSemanticPair_rootThenContinuation
        reward root continuation hM hreward
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward continuation
  have hreturnedCarrier : returned ∈
      quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root tail hM hreward htailCarrier
  have hminimumReturned : quittingTerminalSemanticDebtSum minimum ≤
      quittingTerminalSemanticDebtSum returned :=
    hminimum returned hreturnedCarrier
  have hnear : quittingTerminalSemanticDebtSum returned ≤
      quittingTerminalSemanticDebtSum minimum + tolerance :=
    (capNashReturnSelection_iff_tailEscape_prefix_nearMinimum
      (reward := reward) minimum tail root tolerance hselection.1).1 hselection
  have hstage := quittingStageCoalitionMass_rootThenContinuation_succ
    reward root continuation stage terminal
  have hstagePositive : 0 < quittingStageCoalitionMass reward
      (quittingRootThenContinuationProfile reward root continuation)
        (stage + 1) terminal := by
    rw [hstage]
    exact mul_pos hcontinue hatom
  rw [hsemantic]
  exact ⟨hreturnedCarrier, hminimumReturned, hnear, hstage, hstagePositive⟩

end GameTheory
