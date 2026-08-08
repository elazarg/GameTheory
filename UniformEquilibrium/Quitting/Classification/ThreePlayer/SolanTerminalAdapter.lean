/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.ThreePlayer.SolanSourceStatement

/-!
# From Solan target bounds to terminal approximate Nash

This module contains the source-independent algebraic adapter.  A prescribed
terminal payoff at least `target - δ`, together with a cap `target + δ` on
every unilateral deviation, is terminal `2δ`-Nash.  Halving the source error
therefore gives terminal approximate Nash profiles at every requested
accuracy.

The conditional theorems in this file depend only on the proposition
`SolanThreePlayerQuittingConclusion`; only the final specialization invokes the
external declaration from `SolanSourceStatement.lean`.
-/

noncomputable section

namespace GameTheory

open StochasticGame

/-- Solan's target bounds also pin the prescribed terminal payoff within the
same error of the fixed target.  The upper bound is obtained by taking the
player's prescribed strategy itself as the unilateral deviation. -/
theorem SolanTerminalTargetBounds.abs_terminalPayoff_sub_le
    {reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)}
    {target : Payoff (Fin 3)} {δ : ℝ}
    {profile : (quittingGame reward).BehaviorProfile}
    (h : SolanTerminalTargetBounds reward target δ profile)
    (who : Fin 3) :
    |quittingTerminalPayoff reward profile who - target who| ≤ δ := by
  rw [abs_le]
  constructor
  · have hon := h.1 who
    linarith
  · have hupper :
        quittingTerminalPayoff reward profile who ≤ target who + δ := by
      simpa using h.2 who (profile who)
    linarith

/-- Solan's two target inequalities imply terminal approximate Nash, with the
sharp elementary loss of a factor two. -/
theorem SolanTerminalTargetBounds.isεAsymptoticNash
    {reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)}
    {target : Payoff (Fin 3)} {δ : ℝ}
    {profile : (quittingGame reward).BehaviorProfile}
    (h : SolanTerminalTargetBounds reward target δ profile) :
    (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) (2 * δ) profile := by
  intro who dev
  have hon := h.1 who
  have hdev := h.2 who dev
  linarith

/-- A supplied faithful Solan conclusion produces terminal approximate Nash
profiles at every positive accuracy.  The source tolerance is chosen as
`ε / 2`, so the factor-two adapter spends exactly the requested error. -/
theorem SolanThreePlayerQuittingConclusion.terminalNash_all_errors
    {reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)}
    (hSolan : SolanThreePlayerQuittingConclusion reward) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile := by
  intro ε hε
  obtain ⟨target, htarget⟩ := hSolan
  have hhalf : 0 < ε / 2 := by linarith
  obtain ⟨profile, hprofile⟩ := htarget (ε / 2) hhalf
  refine ⟨profile, ?_⟩
  intro who dev
  have hon := hprofile.1 who
  have hdev := hprofile.2 who dev
  linarith

/-- **Source-backed terminal existence for every three-player quitting table.**

This is the exact producer theorem consumed by the existing
terminal-to-uniform selection waist.  Its only non-kernel dependency is the
single named Solan source declaration. -/
theorem threePlayerQuittingGame_exists_terminalNash_all_errors
    (reward : {S : Finset (Fin 3) // S.Nonempty} → Payoff (Fin 3)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ profile : (quittingGame reward).BehaviorProfile,
        (quittingGame reward).IsεAsymptoticNash
          (quittingTerminalPayoff reward) ε profile :=
  (solan1999_threePlayerQuitting_terminalTargetBounds reward).terminalNash_all_errors

end GameTheory
