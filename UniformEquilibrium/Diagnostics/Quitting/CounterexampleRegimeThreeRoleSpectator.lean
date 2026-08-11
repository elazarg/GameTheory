/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSmallPlayers
import UniformEquilibrium.Diagnostics.Quitting.MinimalFinCounterexample
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNegativeVertexGerm
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlayerDeletion

/-!
# The fourth-player spectator cannot be deletion-inert

The unmatched reset/incidence separator uses three player labels.  In a
four-player counterexample the remaining player need not occur in that local
packet.  This file records the exact obstruction to treating that player as
an inert spectator: at the negative singleton/punishment gate, the player
must have a strict insertion gain on some nonempty opponent coalition.

Indeed, otherwise the coalition-toggle deletion theorem makes `Never` a
universal best response for the spectator and preserves the ambient positive
terminal exploitability gap after deleting it.  The resulting three-player
game contradicts unconditional three-player existence.
-/

noncomputable section

namespace GameTheory

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

namespace QuittingCounterexampleRegime

/-- Deleting one player from a four-player type leaves exactly three
players. -/
theorem card_quittingDeletedPlayer_eq_three_of_card_eq_four
    (owner : iota) (hcard : Fintype.card iota = 4) :
    Fintype.card (QuittingDeletedPlayer owner) = 3 := by
  rw [Fintype.card_subtype_compl (fun who : iota => who = owner)]
  simp [hcard]

/-- **Four-player spectator obstruction.**  In a four-player counterexample,
any player at the negative singleton/punishment gate has a strict profitable
insertion into some nonempty opponent coalition.  Thus the fourth label left
outside a local debtor/receiver/quitter packet cannot be discarded as a
universal-`Never` spectator at this gate. -/
theorem exists_strict_owner_toggle_of_card_eq_four
    (regime : QuittingCounterexampleRegime reward)
    (hcard : Fintype.card iota = 4) (owner : iota)
    (hsolo : reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue reward owner)
    (hchi : quittingPunishmentValue reward owner ≤ 0) :
    ∃ (quitters : Finset iota) (hquitters : quitters.Nonempty),
      owner ∉ quitters ∧
        reward ⟨quitters, hquitters⟩ owner <
          reward
            ⟨insert owner quitters,
              Finset.insert_nonempty owner quitters⟩ owner := by
  rcases exists_strict_owner_toggle_or_exact_playerDeletion
      reward owner regime.terminalGap_pos regime.terminalExploitability
        hsolo hchi with htoggle | ⟨_, hgap, _⟩
  · exact htoggle
  · let reducedReward := quittingDeletePlayerReward reward owner
    have hgap' : HasTerminalExploitabilityGap reducedReward
        regime.terminalGap := hgap
    have hno : ¬ ∃ payoff : Payoff (QuittingDeletedPlayer owner),
        (quittingGame reducedReward).IsUniformEquilibriumPayoff none payoff :=
      (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
        reducedReward).2
          ⟨regime.terminalGap, regime.terminalGap_pos, hgap'⟩
    exact False.elim (hno
      (quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three
        (card_quittingDeletedPlayer_eq_three_of_card_eq_four owner hcard)
        reducedReward))

/-- Every player of a four-player counterexample is protected from deletion
by a positive punishment value, an incoming singleton collision toggle, or
an outgoing nonempty-coalition toggle. -/
theorem positivePunishment_or_incomingSingletonToggle_or_ownerToggle_of_card_eq_four
    (regime : QuittingCounterexampleRegime reward)
    (hcard : Fintype.card iota = 4) (owner : iota) :
    0 < quittingPunishmentValue reward owner ∨
      (∃ other, other ≠ owner ∧
        quittingSoloReward reward owner other <
          quittingSingletonCollisionReward reward owner other) ∨
      ∃ (quitters : Finset iota) (hquitters : quitters.Nonempty),
        owner ∉ quitters ∧
          reward ⟨quitters, hquitters⟩ owner <
            reward
              ⟨insert owner quitters,
                Finset.insert_nonempty owner quitters⟩ owner := by
  rcases regime.strictJoiner_or_soloReward_lt_punishmentValue owner with
    hincoming | hsolo
  · exact Or.inr (Or.inl hincoming)
  · by_cases hchi : quittingPunishmentValue reward owner ≤ 0
    · exact Or.inr (Or.inr
        (regime.exists_strict_owner_toggle_of_card_eq_four
          hcard owner hsolo hchi))
    · exact Or.inl (lt_of_not_ge hchi)

end QuittingCounterexampleRegime

namespace MinimalFinQuittingCounterexample

/-- **Every negative-gate player of a cardinal-minimal counterexample is
toggle-essential.**  This is the arbitrary-cardinality version of the
four-player spectator obstruction.  Minimality rules out the exact deletion
branch, so every player which would otherwise be universal-`Never` must
strictly gain by joining some nonempty opponent coalition.

The witness coalition may contain any number of other players.  In
particular, this theorem does not claim that the toggle is supported on a
previously selected debtor/receiver/quitter triple. -/
theorem exists_strict_owner_toggle_at_negative_gate
    (minimal : MinimalFinQuittingCounterexample)
    (owner : Fin minimal.playerCount)
    (hsolo : minimal.reward (quittingSingletonTerminal owner) owner <
      quittingPunishmentValue minimal.reward owner)
    (hchi : quittingPunishmentValue minimal.reward owner ≤ 0) :
    ∃ (quitters : Finset (Fin minimal.playerCount))
        (hquitters : quitters.Nonempty),
      owner ∉ quitters ∧
        minimal.reward ⟨quitters, hquitters⟩ owner <
          minimal.reward
            ⟨insert owner quitters,
              Finset.insert_nonempty owner quitters⟩ owner := by
  rcases exists_strict_owner_toggle_or_exact_playerDeletion
      minimal.reward owner minimal.regime.terminalGap_pos
        minimal.regime.terminalExploitability hsolo hchi with
    htoggle | ⟨hnonempty, hgap, hcard⟩
  · exact htoggle
  · letI : Nonempty (QuittingDeletedPlayer owner) := hnonempty
    let reducedReward := quittingDeletePlayerReward minimal.reward owner
    have hgap' : HasTerminalExploitabilityGap reducedReward
        minimal.regime.terminalGap := hgap
    have hno : ¬ ∃ payoff : Payoff (QuittingDeletedPlayer owner),
        (quittingGame reducedReward).IsUniformEquilibriumPayoff none payoff :=
      (not_exists_uniformEquilibriumPayoff_iff_exists_terminalExploitabilityGap
        reducedReward).2
          ⟨minimal.regime.terminalGap,
            minimal.regime.terminalGap_pos, hgap'⟩
    have hcard' : Fintype.card (QuittingDeletedPlayer owner) <
        minimal.playerCount := by
      simpa using hcard
    exact False.elim (hno
      (minimal.exists_uniformEquilibriumPayoff_of_card_lt hcard'
        reducedReward))

/-- **Directed essentiality of every spare player.**  Every player of a
cardinal-minimal counterexample participates in one of three obstructions:
its punishment value is positive; another player strictly gains by joining
its singleton exit; or it strictly gains by joining a nonempty opponent
coalition.

Compared with the preceding numerical passport, the middle branch is now an
actual two-player terminal toggle.  The last branch can still have an
arbitrarily large background coalition, and neither toggle is asserted to be
co-realized with a selected reset/incidence packet. -/
theorem positivePunishment_or_incomingSingletonToggle_or_ownerToggle
    (minimal : MinimalFinQuittingCounterexample)
    (owner : Fin minimal.playerCount) :
    0 < quittingPunishmentValue minimal.reward owner ∨
      (∃ other, other ≠ owner ∧
        quittingSoloReward minimal.reward owner other <
          quittingSingletonCollisionReward minimal.reward owner other) ∨
      ∃ (quitters : Finset (Fin minimal.playerCount))
          (hquitters : quitters.Nonempty),
        owner ∉ quitters ∧
          minimal.reward ⟨quitters, hquitters⟩ owner <
            minimal.reward
              ⟨insert owner quitters,
                Finset.insert_nonempty owner quitters⟩ owner := by
  rcases minimal.regime.strictJoiner_or_soloReward_lt_punishmentValue owner
      with hincoming | hsolo
  · exact Or.inr (Or.inl hincoming)
  · by_cases hchi : quittingPunishmentValue minimal.reward owner ≤ 0
    · exact Or.inr (Or.inr
        (minimal.exists_strict_owner_toggle_at_negative_gate
          owner hsolo hchi))
    · exact Or.inl (lt_of_not_ge hchi)

end MinimalFinQuittingCounterexample

end GameTheory
