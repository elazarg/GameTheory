/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.GroupTheory.Perm.Fin
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlayerDeletion

/-!
# Essentiality passports do not imply bounded player compression

The cardinal-minimal essentiality passport says that each player is covered
by positive punishment, an incoming singleton join, or an outgoing coalition
toggle.  Taken by itself, this is only a local covering condition.  It does
not bound the size of a witness-closed player kernel.

This file records the sharp finite obstruction.  On `Fin n`, let the selected
singleton witness of `owner` be `finRotate n owner`.  Every player has a
distinct witness, but every nonempty subset closed under selected witnesses
is the whole `n`-cycle.  Hence for arbitrary `n ≥ 5` there is no nonempty
witness-closed kernel of cardinality at most four.

The obstruction is realized by an actual quitting reward table: the joiner
`finRotate n owner` strictly gains when joining the singleton `{owner}`.
Thus the supplied passport alone cannot justify deletion, freezing, merging,
or a four-player role quotient.  A successful compression theorem must use
additional co-realized quantitative data—such as blocker charge, debt
transport, or punishment provenance—not merely the existence of one passport
witness per player.

This is not a family of quitting-game counterexamples.  It is a regression
against deriving bounded compression from the passport alone.
-/

noncomputable section

namespace GameTheory

open Equiv

/-- The singleton-witness part of the essentiality passport, with one selected
incoming joiner for every owner. -/
structure QuittingSingletonEssentialityGraph (ι : Type) where
  witness : ι → ι
  witness_ne : ∀ owner, witness owner ≠ owner

/-- A player set is closed under its selected essentiality witnesses. -/
def QuittingSingletonEssentialityGraph.WitnessClosed
    {ι : Type} [DecidableEq ι]
    (graph : QuittingSingletonEssentialityGraph ι) (players : Finset ι) : Prop :=
  ∀ owner ∈ players, graph.witness owner ∈ players

/-- The cyclic singleton-essentiality passport on `Fin n`. -/
def quittingCyclicSingletonEssentialityGraph
    (n : ℕ) (hn : 2 ≤ n) : QuittingSingletonEssentialityGraph (Fin n) where
  witness := finRotate n
  witness_ne := by
    intro owner
    have hmem : owner ∈ (finRotate n).support := by
      rw [support_finRotate_of_le hn]
      simp
    exact Equiv.Perm.mem_support.mp hmem

/-- Every nonempty witness-closed subset of one cyclic passport is the entire
player set. -/
theorem witnessClosed_eq_univ_of_cyclicSingletonEssentiality
    {n : ℕ} (hn : 2 ≤ n) (players : Finset (Fin n))
    (hnonempty : players.Nonempty)
    (hclosed :
      (quittingCyclicSingletonEssentialityGraph n hn).WitnessClosed players) :
    players = Finset.univ := by
  obtain ⟨source, hsource⟩ := hnonempty
  apply Finset.eq_univ_of_forall
  intro target
  let cycle := finRotate n
  have hcycle : cycle.IsCycle := isCycle_finRotate_of_le hn
  have hsourceMove : cycle source ≠ source := by
    have hmem : source ∈ cycle.support := by
      dsimp [cycle]
      rw [support_finRotate_of_le hn]
      simp
    exact Equiv.Perm.mem_support.mp hmem
  have htargetMove : cycle target ≠ target := by
    have hmem : target ∈ cycle.support := by
      dsimp [cycle]
      rw [support_finRotate_of_le hn]
      simp
    exact Equiv.Perm.mem_support.mp hmem
  obtain ⟨power, hpower⟩ :=
    Equiv.Perm.IsCycle.exists_pow_eq hcycle hsourceMove htargetMove
  have hpowMem : ∀ exponent : ℕ, (cycle ^ exponent) source ∈ players := by
    intro exponent
    induction exponent with
    | zero => simpa using hsource
    | succ exponent ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        exact hclosed ((cycle ^ exponent) source) ih
  rw [← hpower]
  exact hpowMem power

/-- In particular, an `n ≥ 5` cyclic passport has no nonempty
witness-closed kernel of size at most four. -/
theorem four_lt_card_of_cyclicSingleton_witnessClosed
    {n : ℕ} (hn : 5 ≤ n) (players : Finset (Fin n))
    (hnonempty : players.Nonempty)
    (hclosed :
      (quittingCyclicSingletonEssentialityGraph n (by omega)).WitnessClosed
        players) :
    4 < players.card := by
  have hall := witnessClosed_eq_univ_of_cyclicSingletonEssentiality
    (n := n) (by omega) players hnonempty hclosed
  rw [hall, Finset.card_univ, Fintype.card_fin]
  omega

/-- Seeding the kernel with a debtor/receiver/quitter triple does not help:
for `n ≥ 5` no witness-closed set containing those three roles has cardinality
at most four. -/
theorem not_exists_four_witnessClosed_kernel_containing_roles
    {n : ℕ} (hn : 5 ≤ n) (debtor receiver quitter : Fin n) :
    ¬ ∃ players : Finset (Fin n),
      ({debtor, receiver, quitter} : Finset (Fin n)) ⊆ players ∧
        (quittingCyclicSingletonEssentialityGraph n (by omega)).WitnessClosed
          players ∧
        players.card ≤ 4 := by
  rintro ⟨players, hroles, hclosed, hcard⟩
  have hdebtor : debtor ∈ players := hroles (by simp)
  have hlarge := four_lt_card_of_cyclicSingleton_witnessClosed hn players
    ⟨debtor, hdebtor⟩ hclosed
  omega

/-! ## Realization by a quitting reward table -/

/-- The nonempty two-player terminal coalition. -/
def quittingPairTerminal {ι : Type} [DecidableEq ι] (first second : ι) :
    {S : Finset ι // S.Nonempty} :=
  ⟨{first, second}, by simp⟩

/-- Reward table realizing the cyclic singleton witnesses.  Player `joiner`
gets one exactly on the pair consisting of itself and its predecessor in the
cycle, and zero on every other terminal coalition. -/
def quittingCyclicSingletonJoinReward (n : ℕ) :
    {S : Finset (Fin n) // S.Nonempty} → Payoff (Fin n) :=
  fun terminal joiner =>
    if terminal.val =
        {(finRotate n).symm joiner, joiner} then 1 else 0

/-- Every edge of the cyclic abstract passport is a literal strict singleton
join in the realized quitting reward table. -/
theorem quittingCyclicSingletonJoinReward_strict_witness
    {n : ℕ} (hn : 2 ≤ n) (owner : Fin n) :
    let joiner := finRotate n owner
    joiner ≠ owner ∧
      quittingCyclicSingletonJoinReward n (quittingSingletonTerminal owner)
          joiner <
        quittingCyclicSingletonJoinReward n
          (quittingPairTerminal owner joiner) joiner := by
  let joiner := finRotate n owner
  have hjoiner : joiner ≠ owner := by
    have hmem : owner ∈ (finRotate n).support := by
      rw [support_finRotate_of_le hn]
      simp
    exact Equiv.Perm.mem_support.mp hmem
  refine ⟨hjoiner, ?_⟩
  have hpred : (finRotate n).symm joiner = owner := by
    dsimp only [joiner]
    exact Equiv.symm_apply_apply (finRotate n) owner
  have hsingletonNe : ({owner} : Finset (Fin n)) ≠ {owner, joiner} := by
    intro heq
    have : joiner ∈ ({owner} : Finset (Fin n)) := by
      rw [heq]
      simp
    exact hjoiner (by simpa using this)
  have hpairEq : ({owner, joiner} : Finset (Fin n)) =
      {(finRotate n).symm joiner, joiner} := by
    rw [hpred]
  have hsingletonNe' : ({owner} : Finset (Fin n)) ≠
      {(finRotate n).symm joiner, joiner} := by
    rw [hpred]
    exact hsingletonNe
  change (if ({owner} : Finset (Fin n)) =
      {(finRotate n).symm joiner, joiner} then 1 else 0) <
    if ({owner, joiner} : Finset (Fin n)) =
      {(finRotate n).symm joiner, joiner} then 1 else 0
  rw [if_neg hsingletonNe', if_pos hpairEq]
  norm_num

/-- Game-facing unbounded-passport family: for every `n ≥ 5` there is an
actual `n`-player quitting reward table with a selected strict singleton join
for every player, while every nonempty set closed under those selected joins
has more than four players. -/
theorem exists_unbounded_quittingSingletonPassport_no_fourKernel
    (n : ℕ) (hn : 5 ≤ n) :
    let reward := quittingCyclicSingletonJoinReward n
    let graph := quittingCyclicSingletonEssentialityGraph n (by omega)
    (∀ owner,
      let joiner := graph.witness owner
      joiner ≠ owner ∧
        reward (quittingSingletonTerminal owner) joiner <
          reward (quittingPairTerminal owner joiner) joiner) ∧
      ∀ players : Finset (Fin n), players.Nonempty →
        graph.WitnessClosed players → 4 < players.card := by
  dsimp only
  constructor
  · intro owner
    exact quittingCyclicSingletonJoinReward_strict_witness (by omega) owner
  · intro players hnonempty hclosed
    exact four_lt_card_of_cyclicSingleton_witnessClosed hn players
      hnonempty hclosed

end GameTheory
