/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Projective.AnchoredSingletonLCP
import Math.LinearProgramming.SingletonLCP

/-!
# Playerwise normalization for quitting-game LCP classifications

The two LCP papers used by the classification layer normalize every player's
payoff from quitting alone to zero.  In the repository model the payoff from
never terminating is fixed to zero, so subtracting the solo baseline from
*every* payoff does not stay inside that model: the translated never payoff is
`-r_i({i})`.

This file therefore keeps the translated object as a terminal table together
with an explicit never payoff.  It proves that its singleton matrix is exactly
the already existing projective comparison matrix

`M i j = r_i({j}) - r_i({i})`,

and that its translated never payoff is the zero-anchor affine LCP direction.
It also provides a generic transport theorem for any semantic predicate whose
playerwise-translation invariance has been supplied explicitly.  Ordinary
terminal-Nash invariance is proved concretely in `StrategicTransport.lean`.
-/

noncomputable section

namespace GameTheory
namespace QuittingLCPClassification

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A quitting payoff table in the literature's slightly larger model, where
nontermination may have a nonzero payoff. -/
@[ext]
structure QuittingPayoffTable (ι : Type) [Fintype ι] [DecidableEq ι] where
  terminal : {S : Finset ι // S.Nonempty} → Payoff ι
  never : Payoff ι

/-- The repository table viewed in the larger model: terminal rewards are
unchanged and the never payoff is zero. -/
def repositoryQuittingPayoffTable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingPayoffTable ι where
  terminal := reward
  never := 0

/-- Add one constant to every payoff of each player, including nontermination. -/
def QuittingPayoffTable.translate
    (table : QuittingPayoffTable ι) (shift : Payoff ι) :
    QuittingPayoffTable ι where
  terminal := fun S who => table.terminal S who + shift who
  never := fun who => table.never who + shift who

/-- A semantic property of payoff tables is invariant under playerwise
translation when adding arbitrary player constants preserves it in both
directions.  This is the exact abstract adapter needed for source notions that
are not yet represented by repository strategy types. -/
def IsQuittingPayoffTranslationInvariant
    (property : QuittingPayoffTable ι → Prop) : Prop :=
  ∀ (table : QuittingPayoffTable ι) (shift : Payoff ι),
    property (table.translate shift) ↔ property table

/-- Player `who`'s baseline payoff from quitting alone. -/
def quittingSoloBaseline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who : ι) : ℝ :=
  reward (quittingProjectiveSingletonTerminal who) who

/-- The source-normalized table, obtained by subtracting each receiver's own
solo payoff from all of that receiver's outcomes. -/
def normalizedQuittingPayoffTable
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingPayoffTable ι :=
  (repositoryQuittingPayoffTable reward).translate
    (fun who => -quittingSoloBaseline reward who)

/-- Any explicitly translation-invariant semantic property holds for the
normalized table exactly when it holds for the original repository table. -/
theorem translationInvariant_normalized_iff_repository
    (property : QuittingPayoffTable ι → Prop)
    (hinvariant : IsQuittingPayoffTranslationInvariant property)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    property (normalizedQuittingPayoffTable reward) ↔
      property (repositoryQuittingPayoffTable reward) := by
  simpa [normalizedQuittingPayoffTable] using
    hinvariant (repositoryQuittingPayoffTable reward)
      (fun who => -quittingSoloBaseline reward who)

/-- Row `who`, column `owner` of the literature singleton matrix. -/
def QuittingPayoffTable.singletonMatrix
    (table : QuittingPayoffTable ι) (who owner : ι) : ℝ :=
  table.terminal (quittingProjectiveSingletonTerminal owner) who

@[simp] theorem normalizedQuittingPayoffTable_solo
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    (normalizedQuittingPayoffTable reward).terminal
        (quittingProjectiveSingletonTerminal who) who = 0 := by
  simp [normalizedQuittingPayoffTable, QuittingPayoffTable.translate,
    repositoryQuittingPayoffTable, quittingSoloBaseline]

/-- The normalized singleton matrix is definitionally the repository's
projective comparison matrix, with receiver rows and sole-quitter columns. -/
theorem normalized_singletonMatrix_eq_projectiveLCPMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) :
    (normalizedQuittingPayoffTable reward).singletonMatrix who owner =
      quittingProjectiveLCPMatrix reward who owner := by
  simp [QuittingPayoffTable.singletonMatrix, normalizedQuittingPayoffTable,
    QuittingPayoffTable.translate, repositoryQuittingPayoffTable,
    quittingSoloBaseline, quittingProjectiveLCPMatrix]

/-- The same matrix is the older game-facing singleton matrix from
`Math.LinearProgramming.SingletonLCP`. -/
theorem normalized_singletonMatrix_eq_quittingSingletonMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (who owner : ι) :
    (normalizedQuittingPayoffTable reward).singletonMatrix who owner =
      Math.LinearProgramming.quittingSingletonMatrix reward who owner := by
  simp [QuittingPayoffTable.singletonMatrix, normalizedQuittingPayoffTable,
    QuittingPayoffTable.translate, repositoryQuittingPayoffTable,
    quittingSoloBaseline, Math.LinearProgramming.quittingSingletonMatrix]

/-- The translated never payoff is precisely the zero-anchor affine direction
in the anchored projective LCP. -/
theorem normalized_never_eq_zeroAnchorDirection
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    (normalizedQuittingPayoffTable reward).never who =
      quittingAnchoredProjectiveLCPDirection reward 0 who := by
  simp [normalizedQuittingPayoffTable, QuittingPayoffTable.translate,
    repositoryQuittingPayoffTable, quittingSoloBaseline,
    quittingAnchoredProjectiveLCPDirection]

/-- Translating the normalized terminal reward back by the solo baseline
recovers the original terminal reward pointwise. -/
theorem normalized_terminal_add_baseline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (S : {S : Finset ι // S.Nonempty}) (who : ι) :
    (normalizedQuittingPayoffTable reward).terminal S who +
        quittingSoloBaseline reward who = reward S who := by
  simp [normalizedQuittingPayoffTable, QuittingPayoffTable.translate,
    repositoryQuittingPayoffTable, quittingSoloBaseline]

/-- Translating the normalized never payoff back by the same baseline recovers
the repository's zero nontermination payoff. -/
theorem normalized_never_add_baseline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    (normalizedQuittingPayoffTable reward).never who +
        quittingSoloBaseline reward who = 0 := by
  simp [normalizedQuittingPayoffTable, QuittingPayoffTable.translate,
    repositoryQuittingPayoffTable, quittingSoloBaseline]

/-- Canonical matrix used by the LCP gate. -/
def normalizedSoloMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : ι → ι → ℝ :=
  fun who owner =>
    (normalizedQuittingPayoffTable reward).singletonMatrix who owner

@[simp] theorem normalizedSoloMatrix_diagonal
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    normalizedSoloMatrix reward who who = 0 := by
  exact normalizedQuittingPayoffTable_solo reward who

/-- Public bridge to the existing projective matrix. -/
theorem normalizedSoloMatrix_eq_projectiveLCPMatrix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    normalizedSoloMatrix reward = quittingProjectiveLCPMatrix reward := by
  funext who owner
  exact normalized_singletonMatrix_eq_projectiveLCPMatrix reward who owner

end QuittingLCPClassification
end GameTheory
