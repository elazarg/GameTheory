/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.PlayerReindexNaturality
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSmallPlayers
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticConcentratedSingletonStrategicCompression

/-!
# Minimal finite counterexamples to quitting-game uniform equilibrium

This module gives the classical cardinality-minimal normal form for a
hypothetical finite quitting-game counterexample.  A counterexample may be
reindexed onto `Fin n`, where `4 ≤ n`, and `n` may be chosen so that every
quitting game on a smaller nonempty finite player type has a
uniform-equilibrium payoff.

It also defines restriction of a reward table to a finite set of retained
players.  Minimality solves every nonempty proper restriction as a quitting
game in its own right.  This statement is intentionally fenced at the
restricted game: it supplies neither payoff coordinates for excluded players
nor inequalities deterring an excluded player from joining a quitter
coalition.  Those are separate extension obligations.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [DecidableEq ι]

/-- Restrict a quitting reward table to a finite set of retained players.
Coalitions are included into the ambient player type, while payoff coordinates
are restricted to retained players. -/
def quittingRewardRestrict
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι) :
    {T : Finset {i // i ∈ players} // T.Nonempty} →
      Payoff {i // i ∈ players} :=
  fun T who ↦
    reward
      ⟨T.1.map (Function.Embedding.subtype (fun i ↦ i ∈ players)),
        Finset.map_nonempty.mpr T.2⟩
      who.1

omit [DecidableEq ι] in
/-- Evaluation of a restricted reward table is evaluation of the ambient
table on the included coalition and player. -/
@[simp] theorem quittingRewardRestrict_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (players : Finset ι)
    (T : {T : Finset {i // i ∈ players} // T.Nonempty})
    (who : {i // i ∈ players}) :
    quittingRewardRestrict reward players T who =
      reward
        ⟨T.1.map (Function.Embedding.subtype (fun i ↦ i ∈ players)),
          Finset.map_nonempty.mpr T.2⟩
        who.1 :=
  rfl

/-- There is a combined quitting counterexample regime on the canonical
`n`-player type. -/
def HasQuittingCounterexampleAtCard (n : ℕ) : Prop :=
  ∃ reward : {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n),
    Nonempty (QuittingCounterexampleRegime reward)

/-- A cardinality-minimal finite quitting-game counterexample in canonical
coordinates.  Minimality is stated directly in terms of the combined regime;
the nonexistence characterization turns it into equilibrium existence below. -/
structure MinimalFinQuittingCounterexample where
  /-- Number of players in the minimal counterexample. -/
  playerCount : ℕ
  /-- Canonically indexed terminal reward table. -/
  reward : {S : Finset (Fin playerCount) // S.Nonempty} →
    Payoff (Fin playerCount)
  /-- The table is a genuine counterexample regime. -/
  regime : QuittingCounterexampleRegime reward
  /-- Small-player existence forces at least four players. -/
  four_le_playerCount : 4 ≤ playerCount
  /-- No smaller canonical player cardinality carries a counterexample
  regime. -/
  minimal : ∀ m, m < playerCount → ¬ HasQuittingCounterexampleAtCard m

/-- If any finite nonempty quitting counterexample exists, then a
cardinality-minimal one exists on `Fin n`. -/
theorem exists_minimalFinQuittingCounterexample
    [Fintype ι] [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcounterexample : Nonempty (QuittingCounterexampleRegime reward)) :
    Nonempty MinimalFinQuittingCounterexample := by
  classical
  have hcanonical : Nonempty (QuittingCounterexampleRegime
      (quittingRewardReindex (Fintype.equivFin ι) reward)) :=
    (nonempty_counterexampleRegime_reindex_fin_iff reward).2 hcounterexample
  have hexists : ∃ n, HasQuittingCounterexampleAtCard n :=
    ⟨Fintype.card ι, _, hcanonical⟩
  let n := Nat.find hexists
  have hn : HasQuittingCounterexampleAtCard n := Nat.find_spec hexists
  obtain ⟨minimalReward, ⟨minimalRegime⟩⟩ := hn
  have hfour : 4 ≤ n := by
    have hcard := minimalRegime.three_lt_card
    simp only [Fintype.card_fin] at hcard
    omega
  refine ⟨{
    playerCount := n
    reward := minimalReward
    regime := minimalRegime
    four_le_playerCount := hfour
    minimal := ?_ }⟩
  intro m hm hcounter
  have hleast : n ≤ m := Nat.find_min' hexists hcounter
  omega

namespace MinimalFinQuittingCounterexample

/-- Every quitting game on a smaller nonempty finite player type has a
uniform-equilibrium payoff.  Player reindexing is used only to compare its
cardinality with the canonical minimal table. -/
theorem exists_uniformEquilibriumPayoff_of_card_lt
    (minimal : MinimalFinQuittingCounterexample)
    {κ : Type} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (hcard : Fintype.card κ < minimal.playerCount)
    (reward : {S : Finset κ // S.Nonempty} → Payoff κ) :
    ∃ payoff : Payoff κ,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  have hregime : Nonempty (QuittingCounterexampleRegime reward) :=
    (not_exists_uniformEquilibriumPayoff_iff_nonempty_counterexampleRegime
      reward).1 hno
  have hcanonical : Nonempty (QuittingCounterexampleRegime
      (quittingRewardReindex (Fintype.equivFin κ) reward)) :=
    (nonempty_counterexampleRegime_reindex_fin_iff reward).2 hregime
  exact minimal.minimal (Fintype.card κ) hcard ⟨_, hcanonical⟩

/-- Every nonempty proper player restriction of a minimal table has a
uniform-equilibrium payoff for the retained-player game.

This theorem does **not** extend that equilibrium to the ambient game: no
claim is made about excluded-player payoffs or deviations in which an
excluded player joins the quitting coalition. -/
theorem properRestriction_exists_uniformEquilibriumPayoff
    (minimal : MinimalFinQuittingCounterexample)
    (players : Finset (Fin minimal.playerCount))
    (hplayers : players.Nonempty) (hproper : players ≠ Finset.univ) :
    ∃ payoff : Payoff {i // i ∈ players},
      (quittingGame
        (quittingRewardRestrict minimal.reward players)).IsUniformEquilibriumPayoff
          none payoff := by
  letI : Nonempty {i // i ∈ players} := hplayers.to_subtype
  apply minimal.exists_uniformEquilibriumPayoff_of_card_lt
  simpa using (Finset.card_lt_iff_ne_univ players).2 hproper

/-- Exact deletion at the retained terminal gap is impossible in a
cardinality-minimal counterexample.  The deleted table would have a positive
terminal exploitability gap on a strictly smaller nonempty player type,
where minimality supplies a uniform-equilibrium payoff. -/
theorem not_hasQuittingExactPlayerDeletionAtGap
    (minimal : MinimalFinQuittingCounterexample)
    (owner : Fin minimal.playerCount) :
    ¬ HasQuittingExactPlayerDeletionAtGap minimal.reward owner
      minimal.regime.terminalGap := by
  rintro ⟨hdeletedNonempty, hdeletedGap, hcard⟩
  letI : Nonempty (QuittingDeletedPlayer owner) := hdeletedNonempty
  have hcard' : Fintype.card (QuittingDeletedPlayer owner) <
      minimal.playerCount := by
    simpa using hcard
  have hpayoff := minimal.exists_uniformEquilibriumPayoff_of_card_lt hcard'
    (quittingDeletePlayerReward minimal.reward owner)
  exact
    (quittingGame_not_exists_uniformEquilibriumPayoff_of_terminalExploitabilityGap
      (quittingDeletePlayerReward minimal.reward owner)
      minimal.regime.terminalGap_pos hdeletedGap) hpayoff

/-- On a cardinality-minimal counterexample, the stopping-law singleton
orientation has only the common static atomic-toggle handoff.  The deletion
arm of the general compression is eliminated by minimality rather than
retained as a second leaf. -/
theorem stoppingLawSingletonStrategicOrientation_atomicHandoff
    (minimal : MinimalFinQuittingCounterexample)
    {frontier : QuittingCounterexampleStoppingLawFrontier minimal.regime}
    (packet : QuittingStoppingLawVanishingDebtRectangleSequence frontier)
    (horientation :
      HasQuittingStoppingLawSingletonStrategicOrientation packet) :
    HasQuittingStaticAtomicToggleHandoff minimal.reward := by
  rcases minimal.regime.stoppingLawSingletonStrategicOrientation_compress
      packet horientation with hatomic | hdeletion
  · exact hatomic
  · exact False.elim
      (minimal.not_hasQuittingExactPlayerDeletionAtGap packet.observer
        hdeletion)

end MinimalFinQuittingCounterexample

end GameTheory
