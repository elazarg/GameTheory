/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.GroupTheory.Perm.Fin
import UniformEquilibrium.Quitting.Stationary.MinMax

/-!
# Passive-background compression needs more than an essentiality passport

This file records a finite reward-table obstruction behind the passive-
background compression question.  Let `next` be a fixed-point-free
permutation of the players.  For each player `who`, put

* `P who = univ \ {who, next who}`;
* `Q who = univ \ {next who}`.

The `who` coordinate pays `-1` on exactly `P who` and `Q who`, is otherwise
the modular indicator `1/2 * 1_{next who in S}`, and receives a small positive
bonus only at the full coalition.

The construction is not a quitting-game counterexample.  It is a regression
against deriving player compression from terminal essentiality data alone.
The negative pair gives exact behavioral punishment value `-1`; the only
strict owner-insertion gain is the full-coalition bonus; one blocker square
uses the `card ι - 2` player punishment pit as its background; and the
codimension-one coalitions `Q who` distinguish every player incidence, so an
exact incidence quotient cannot merge two roles.
-/

noncomputable section

namespace GameTheory

open Equiv
open Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair

namespace QuittingPassiveBackgroundCompressionRegression

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The codimension-two punishment pit of `who`. -/
def punishmentPit (next : ι ≃ ι) (who : ι) : Finset ι :=
  (Finset.univ.erase who).erase (next who)

/-- The punishment pit after `who` joins: only `next who` is omitted. -/
def punishmentJoin (next : ι ≃ ι) (who : ι) : Finset ι :=
  Finset.univ.erase (next who)

/-- The raw set reward, extended to the empty coalition for convenient
finite Boolean calculations. -/
def rawReward (next : ι ≃ ι) (bonus : ι → ℝ)
    (terminal : Finset ι) (who : ι) : ℝ :=
  if terminal = punishmentPit next who ∨
      terminal = punishmentJoin next who then
    -1
  else
    (if next who ∈ terminal then (1 / 2 : ℝ) else 0) +
      if terminal = Finset.univ then bonus who else 0

/-- The cyclic-omission terminal reward table. -/
def reward (next : ι ≃ ι) (bonus : ι → ℝ) :
    {S : Finset ι // S.Nonempty} → Payoff ι :=
  fun terminal who => rawReward next bonus terminal.1 who

theorem card_punishmentJoin (next : ι ≃ ι) (who : ι) :
    (punishmentJoin next who).card = Fintype.card ι - 1 := by
  simp [punishmentJoin]

theorem card_punishmentPit (next : ι ≃ ι) (who : ι)
    (hmove : next who ≠ who) :
    (punishmentPit next who).card = Fintype.card ι - 2 := by
  rw [punishmentPit, Finset.card_erase_of_mem]
  · simp only [Finset.card_erase_of_mem (Finset.mem_univ who),
      Finset.card_univ]
    omega
  · simpa using hmove

theorem who_notMem_punishmentPit (next : ι ≃ ι) (who : ι) :
    who ∉ punishmentPit next who := by
  simp [punishmentPit]

theorem next_notMem_punishmentPit (next : ι ≃ ι) (who : ι) :
    next who ∉ punishmentPit next who := by
  simp [punishmentPit]

theorem next_notMem_punishmentJoin (next : ι ≃ ι) (who : ι) :
    next who ∉ punishmentJoin next who := by
  simp [punishmentJoin]

theorem insert_who_punishmentPit (next : ι ≃ ι) (who : ι)
    (hmove : next who ≠ who) :
    insert who (punishmentPit next who) = punishmentJoin next who := by
  ext player
  simp only [punishmentPit, punishmentJoin, Finset.mem_insert,
    Finset.mem_erase, Finset.mem_univ]
  by_cases hplayer : player = who
  · subst player
    exact ⟨fun _ => ⟨Ne.symm hmove, trivial⟩, fun _ => Or.inl rfl⟩
  · simp [hplayer]

theorem erase_who_punishmentPit (next : ι ≃ ι) (who : ι) :
    (punishmentPit next who).erase who = punishmentPit next who := by
  exact Finset.erase_eq_of_notMem (who_notMem_punishmentPit next who)

@[simp] theorem rawReward_punishmentPit (next : ι ≃ ι)
    (bonus : ι → ℝ) (who : ι) :
    rawReward next bonus (punishmentPit next who) who = -1 := by
  simp [rawReward]

@[simp] theorem rawReward_punishmentJoin (next : ι ≃ ι)
    (bonus : ι → ℝ) (who : ι) :
    rawReward next bonus (punishmentJoin next who) who = -1 := by
  simp [rawReward]

/-- The two displayed coalitions are the only terminal incidences attaining
the lower reward `-1`.  This is the exact incidence rigidity behind the
punishment construction. -/
theorem rawReward_eq_neg_one_iff (next : ι ≃ ι) (bonus : ι → ℝ)
    (hbonus : ∀ player, 0 ≤ bonus player) (terminal : Finset ι) (who : ι) :
    rawReward next bonus terminal who = -1 ↔
      terminal = punishmentPit next who ∨
        terminal = punishmentJoin next who := by
  simp only [rawReward]
  by_cases hexception : terminal = punishmentPit next who ∨
      terminal = punishmentJoin next who
  · simp [hexception]
  · rw [if_neg hexception]
    have hnonneg : 0 ≤
        (if next who ∈ terminal then (1 / 2 : ℝ) else 0) +
          if terminal = Finset.univ then bonus who else 0 := by
      specialize hbonus who
      split_ifs <;> norm_num <;> linarith
    constructor
    · intro h
      linarith
    · exact fun h => (hexception h).elim

/-- Among coalitions containing the punished player, `Q who` is the unique
negative pit; `P who` cannot contain `who`. -/
theorem rawReward_eq_neg_one_of_owner_mem_iff (next : ι ≃ ι)
    (bonus : ι → ℝ) (hbonus : ∀ player, 0 ≤ bonus player)
    (terminal : Finset ι) (who : ι) (hwho : who ∈ terminal) :
    rawReward next bonus terminal who = -1 ↔
      terminal = punishmentJoin next who := by
  rw [rawReward_eq_neg_one_iff next bonus hbonus]
  constructor
  · rintro (hpit | hjoin)
    · exact (who_notMem_punishmentPit next who (hpit ▸ hwho)).elim
    · exact hjoin
  · exact Or.inr

theorem punishmentPit_nonempty (next : ι ≃ ι) (who : ι)
    (hcard : 3 ≤ Fintype.card ι) (hmove : next who ≠ who) :
    (punishmentPit next who).Nonempty := by
  rw [← Finset.card_pos, card_punishmentPit next who hmove]
  omega

theorem who_mem_punishmentJoin (next : ι ≃ ι) (who : ι)
    (hmove : next who ≠ who) :
    who ∈ punishmentJoin next who := by
  simp [punishmentJoin, Ne.symm hmove]

theorem insert_next_punishmentPit (next : ι ≃ ι) (who : ι)
    (hmove : next who ≠ who) :
    insert (next who) (punishmentPit next who) = Finset.univ.erase who := by
  exact Finset.insert_erase (by simp [hmove])

theorem insert_next_punishmentJoin (next : ι ≃ ι) (who : ι) :
    insert (next who) (punishmentJoin next who) = Finset.univ := by
  ext player
  simp [punishmentJoin]

theorem erase_who_punishmentJoin (next : ι ≃ ι) (who : ι) :
    (punishmentJoin next who).erase who = punishmentPit next who := by
  ext player
  simp [punishmentJoin, punishmentPit, and_comm]

theorem insert_who_eq_punishmentJoin_iff (next : ι ≃ ι) (who : ι)
    (terminal : Finset ι) (hmove : next who ≠ who)
    (hnotMem : who ∉ terminal) :
    insert who terminal = punishmentJoin next who ↔
      terminal = punishmentPit next who := by
  have hmem := who_mem_punishmentJoin next who hmove
  have hiff := Finset.erase_eq_iff_eq_insert hmem hnotMem
  rw [erase_who_punishmentJoin next who] at hiff
  exact ⟨fun h => (hiff.mpr h.symm).symm,
    fun h => (hiff.mp h.symm).symm⟩

theorem insert_who_eq_univ_iff (who : ι) (terminal : Finset ι)
    (hnotMem : who ∉ terminal) :
    insert who terminal = Finset.univ ↔ terminal = Finset.univ.erase who := by
  have hiff := Finset.erase_eq_iff_eq_insert (Finset.mem_univ who) hnotMem
  exact ⟨fun h => (hiff.mpr h.symm).symm,
    fun h => (hiff.mp h.symm).symm⟩

theorem rawReward_univ (next : ι ≃ ι) (bonus : ι → ℝ) (who : ι) :
    rawReward next bonus Finset.univ who = 1 / 2 + bonus who := by
  have hnePit : (Finset.univ : Finset ι) ≠ punishmentPit next who := by
    intro h
    have hmem : next who ∈ (punishmentPit next who) := by
      rw [← h]
      simp
    exact next_notMem_punishmentPit next who hmem
  have hneJoin : (Finset.univ : Finset ι) ≠ punishmentJoin next who := by
    intro h
    have hmem : next who ∈ (punishmentJoin next who) := by
      rw [← h]
      simp
    exact next_notMem_punishmentJoin next who hmem
  simp [rawReward, hnePit, hneJoin]

theorem rawReward_univ_erase (next : ι ≃ ι) (bonus : ι → ℝ)
    (who : ι) (hmove : next who ≠ who) :
    rawReward next bonus (Finset.univ.erase who) who = 1 / 2 := by
  have hnePit : Finset.univ.erase who ≠ punishmentPit next who := by
    intro h
    have hmem : next who ∈ Finset.univ.erase who := by simp [hmove]
    rw [h] at hmem
    exact next_notMem_punishmentPit next who hmem
  have hneJoin : Finset.univ.erase who ≠ punishmentJoin next who := by
    intro h
    have hwho : who ∈ punishmentJoin next who :=
      who_mem_punishmentJoin next who hmove
    rw [← h] at hwho
    simp at hwho
  have hneUniv : Finset.univ.erase who ≠ (Finset.univ : Finset ι) := by
    intro h
    have hwho : who ∈ (Finset.univ.erase who : Finset ι) := by
      rw [h]
      simp
    simp at hwho
  simp [rawReward, hnePit, hneJoin, hneUniv, hmove]

/-- Away from the pit and the full opponent set, inserting the owner changes
nothing.  Together with the next two lemmas, this is the exact uniqueness of
the construction's positive owner-insertion toggle. -/
theorem rawReward_insert_owner_eq (next : ι ≃ ι) (bonus : ι → ℝ)
    (who : ι) (terminal : Finset ι) (hmove : next who ≠ who)
    (hnotMem : who ∉ terminal)
    (hnePit : terminal ≠ punishmentPit next who)
    (hneFull : terminal ≠ Finset.univ.erase who) :
    rawReward next bonus (insert who terminal) who =
      rawReward next bonus terminal who := by
  have hneJoin : terminal ≠ punishmentJoin next who := by
    intro h
    exact hnotMem (h ▸ who_mem_punishmentJoin next who hmove)
  have hneUniv : terminal ≠ (Finset.univ : Finset ι) := by
    intro h
    exact hnotMem (h ▸ Finset.mem_univ who)
  have hinsertNePit : insert who terminal ≠ punishmentPit next who := by
    intro h
    exact who_notMem_punishmentPit next who (h ▸ Finset.mem_insert_self who terminal)
  have hinsertNeJoin : insert who terminal ≠ punishmentJoin next who := by
    exact fun h => hnePit ((insert_who_eq_punishmentJoin_iff next who terminal
      hmove hnotMem).mp h)
  have hinsertNeUniv : insert who terminal ≠ (Finset.univ : Finset ι) := by
    exact fun h => hneFull ((insert_who_eq_univ_iff who terminal hnotMem).mp h)
  simp [rawReward, hnePit, hneJoin, hneUniv, hinsertNePit,
    hinsertNeJoin, hinsertNeUniv, hmove]

theorem rawReward_insert_owner_pit (next : ι ≃ ι) (bonus : ι → ℝ)
    (who : ι) (hmove : next who ≠ who) :
    rawReward next bonus (insert who (punishmentPit next who)) who =
      rawReward next bonus (punishmentPit next who) who := by
  rw [insert_who_punishmentPit next who hmove]
  simp

theorem rawReward_insert_owner_full (next : ι ≃ ι) (bonus : ι → ℝ)
    (who : ι) (hmove : next who ≠ who) :
    rawReward next bonus
        (insert who (Finset.univ.erase who)) who =
      rawReward next bonus (Finset.univ.erase who) who + bonus who := by
  rw [(insert_who_eq_univ_iff who (Finset.univ.erase who) (by simp)).mpr rfl,
    rawReward_univ, rawReward_univ_erase next bonus who hmove]

/-- The full opponent coalition is the unique strict owner-insertion toggle. -/
theorem rawReward_insert_owner_lt_iff (next : ι ≃ ι) (bonus : ι → ℝ)
    (who : ι) (terminal : Finset ι) (hmove : next who ≠ who)
    (hbonus : 0 < bonus who) (hnotMem : who ∉ terminal) :
    rawReward next bonus terminal who <
        rawReward next bonus (insert who terminal) who ↔
      terminal = Finset.univ.erase who := by
  constructor
  · intro hgain
    by_contra hneFull
    by_cases hnePit : terminal = punishmentPit next who
    · subst terminal
      rw [rawReward_insert_owner_pit next bonus who hmove] at hgain
      exact (lt_irrefl _ hgain)
    · rw [rawReward_insert_owner_eq next bonus who terminal hmove hnotMem
        hnePit hneFull] at hgain
      exact lt_irrefl _ hgain
  · intro hterminal
    subst terminal
    rw [rawReward_insert_owner_full next bonus who hmove]
    linarith

/-- In particular, sufficiently large instances have no strict singleton-
join edges: adding a player to another player's singleton is far below the
unique full-coalition toggle. -/
theorem rawReward_pair_eq_singleton (next : ι ≃ ι) (bonus : ι → ℝ)
    (owner joiner : ι) (hcard : 5 ≤ Fintype.card ι)
    (hmove : next joiner ≠ joiner) (hne : joiner ≠ owner) :
    rawReward next bonus ({owner, joiner} : Finset ι) joiner =
      rawReward next bonus ({owner} : Finset ι) joiner := by
  have hnotMem : joiner ∉ ({owner} : Finset ι) := by simpa using hne
  have hnePit : ({owner} : Finset ι) ≠ punishmentPit next joiner := by
    intro h
    have hcardEq := congrArg Finset.card h
    rw [Finset.card_singleton, card_punishmentPit next joiner hmove] at hcardEq
    omega
  have hneFull : ({owner} : Finset ι) ≠ Finset.univ.erase joiner := by
    intro h
    have hcardEq := congrArg Finset.card h
    simp only [Finset.card_singleton, Finset.card_erase_of_mem
      (Finset.mem_univ joiner), Finset.card_univ] at hcardEq
    omega
  have hpair : ({owner, joiner} : Finset ι) = {joiner, owner} := by
    ext player
    simp [or_comm]
  rw [hpair]
  exact rawReward_insert_owner_eq next bonus joiner ({owner} : Finset ι)
    hmove hnotMem hnePit hneFull

/-- The selected Boolean square has the entire punishment pit as its passive
background and curl exactly equal to the full-coalition bonus. -/
theorem blockerSquare_curl (next : ι ≃ ι) (bonus : ι → ℝ)
    (who : ι) (hmove : next who ≠ who) :
    rawReward next bonus Finset.univ who -
        rawReward next bonus (insert who (punishmentPit next who)) who -
        rawReward next bonus (insert (next who) (punishmentPit next who)) who +
        rawReward next bonus (punishmentPit next who) who =
      bonus who := by
  rw [insert_who_punishmentPit next who hmove,
    insert_next_punishmentPit next who hmove, rawReward_univ,
    rawReward_punishmentJoin, rawReward_univ_erase next bonus who hmove,
    rawReward_punishmentPit]
  ring

/-- On coalitions smaller than the codimension-two pit, the reward is just
the modular successor-incidence coordinate. -/
theorem rawReward_eq_modular_of_card_lt (next : ι ≃ ι) (bonus : ι → ℝ)
    (who : ι) (terminal : Finset ι) (hmove : next who ≠ who)
    (hcard : terminal.card < Fintype.card ι - 2) :
    rawReward next bonus terminal who =
      if next who ∈ terminal then 1 / 2 else 0 := by
  have hnePit : terminal ≠ punishmentPit next who := by
    intro h
    rw [h, card_punishmentPit next who hmove] at hcard
    omega
  have hneJoin : terminal ≠ punishmentJoin next who := by
    intro h
    rw [h, card_punishmentJoin] at hcard
    omega
  have hneUniv : terminal ≠ (Finset.univ : Finset ι) := by
    intro h
    rw [h, Finset.card_univ] at hcard
    omega
  simp [rawReward, hnePit, hneJoin, hneUniv]

/-- Boolean curl of one payoff coordinate over a square. -/
def booleanCurl (next : ι ≃ ι) (bonus : ι → ℝ) (who first second : ι)
    (background : Finset ι) : ℝ :=
  rawReward next bonus (insert first (insert second background)) who -
    rawReward next bonus (insert first background) who -
    rawReward next bonus (insert second background) who +
    rawReward next bonus background who

/-- Any square supported on fewer than `card ι - 2` players has zero curl. -/
theorem booleanCurl_eq_zero_of_support_card_lt (next : ι ≃ ι)
    (bonus : ι → ℝ) (who first second : ι) (background : Finset ι)
    (hmove : next who ≠ who) (hfirstSecond : first ≠ second)
    (hcard : (insert first (insert second background)).card <
      Fintype.card ι - 2) :
    booleanCurl next bonus who first second background = 0 := by
  have card_lt (terminal : Finset ι)
      (hsubset : terminal ⊆ insert first (insert second background)) :
      terminal.card < Fintype.card ι - 2 :=
    lt_of_le_of_lt (Finset.card_le_card hsubset) hcard
  rw [booleanCurl,
    rawReward_eq_modular_of_card_lt next bonus who
      (insert first (insert second background)) hmove (card_lt _ (by rfl)),
    rawReward_eq_modular_of_card_lt next bonus who
      (insert first background) hmove
        (card_lt _ (by
          intro player hplayer
          rw [Finset.mem_insert] at hplayer
          rcases hplayer with rfl | hplayer
          · simp
          · simp [hplayer])),
    rawReward_eq_modular_of_card_lt next bonus who
      (insert second background) hmove
        (card_lt _ (by
          intro player hplayer
          rw [Finset.mem_insert] at hplayer
          rcases hplayer with rfl | hplayer
          · simp
          · simp [hplayer])),
    rawReward_eq_modular_of_card_lt next bonus who background hmove
      (card_lt _ (by
        intro player hplayer
        simp only [Finset.mem_insert]
        exact Or.inr (Or.inr hplayer)))]
  by_cases hbackground : next who ∈ background
  · simp [hbackground]
  · by_cases hfirst : next who = first
    · by_cases hsecond : next who = second
      · exact (hfirstSecond (hfirst ▸ hsecond)).elim
      · simp_all
    · by_cases hsecond : next who = second
      · simp_all
      · simp [hbackground, hfirst, hsecond]

/-- Consequently every nonzero blocker square uses at least `card ι - 2`
players. -/
theorem card_sub_two_le_support_of_booleanCurl_ne_zero (next : ι ≃ ι)
    (bonus : ι → ℝ) (who first second : ι) (background : Finset ι)
    (hmove : next who ≠ who) (hfirstSecond : first ≠ second)
    (hcurl : booleanCurl next bonus who first second background ≠ 0) :
    Fintype.card ι - 2 ≤
      (insert first (insert second background)).card := by
  by_contra hnot
  exact hcurl (booleanCurl_eq_zero_of_support_card_lt next bonus who first
    second background hmove hfirstSecond (by omega))

/-! ## Deleting a member of the passive background -/

theorem punishmentPit_subset_punishmentJoin (next : ι ≃ ι) (who : ι) :
    punishmentPit next who ⊆ punishmentJoin next who := by
  intro player hplayer
  simp only [punishmentPit, punishmentJoin, Finset.mem_erase,
    Finset.mem_univ] at hplayer ⊢
  exact ⟨hplayer.1, trivial⟩

/-- If a coalition omits even one member of the selected pit, all three
exceptional coalitions (`P`, `Q`, and `univ`) disappear. -/
theorem rawReward_of_omits_punishmentPit_member (next : ι ≃ ι)
    (bonus : ι → ℝ) (who background : ι) (terminal : Finset ι)
    (hbackground : background ∈ punishmentPit next who)
    (homit : background ∉ terminal) :
    rawReward next bonus terminal who =
      if next who ∈ terminal then 1 / 2 else 0 := by
  have hnePit : terminal ≠ punishmentPit next who := by
    intro h
    exact homit (h ▸ hbackground)
  have hbackgroundJoin : background ∈ punishmentJoin next who :=
    punishmentPit_subset_punishmentJoin next who hbackground
  have hneJoin : terminal ≠ punishmentJoin next who := by
    intro h
    exact homit (h ▸ hbackgroundJoin)
  have hneUniv : terminal ≠ (Finset.univ : Finset ι) := by
    intro h
    exact homit (h ▸ Finset.mem_univ background)
  simp [rawReward, hnePit, hneJoin, hneUniv]

/-- Embed a terminal coalition after deleting `background` back into the
original player set. -/
def liftDeletedCoalition (background : ι)
    (terminal : Finset {player : ι // player ≠ background}) : Finset ι :=
  terminal.map ⟨Subtype.val, Subtype.val_injective⟩

omit [Fintype ι] [DecidableEq ι] in
theorem background_notMem_liftDeletedCoalition (background : ι)
    (terminal : Finset {player : ι // player ≠ background}) :
    background ∉ liftDeletedCoalition background terminal := by
  simp [liftDeletedCoalition]

/-- The terminal table obtained by genuinely restricting the player type
after deleting one background player. -/
def deletedReward (next : ι ≃ ι) (bonus : ι → ℝ) (background : ι) :
    {S : Finset {player : ι // player ≠ background} // S.Nonempty} →
      Payoff {player : ι // player ≠ background} :=
  fun terminal who =>
    rawReward next bonus (liftDeletedCoalition background terminal.1) who.1

/-- The active player survives deletion of a member of its pit. -/
def retainedPlayer (next : ι ≃ ι) (who background : ι)
    (hbackground : background ∈ punishmentPit next who) :
    {player : ι // player ≠ background} :=
  ⟨who, by
    intro h
    subst background
    exact who_notMem_punishmentPit next who hbackground⟩

theorem deletedReward_active_nonneg (next : ι ≃ ι) (bonus : ι → ℝ)
    (who background : ι)
    (hbackground : background ∈ punishmentPit next who)
    (terminal :
      {S : Finset {player : ι // player ≠ background} // S.Nonempty}) :
    0 ≤ deletedReward next bonus background terminal
      (retainedPlayer next who background hbackground) := by
  rw [deletedReward]
  change 0 ≤ rawReward next bonus
    (liftDeletedCoalition background terminal.1) who
  rw [rawReward_of_omits_punishmentPit_member next bonus who background
    (liftDeletedCoalition background terminal.1) hbackground
    (background_notMem_liftDeletedCoalition background terminal.1)]
  split_ifs <;> norm_num

theorem deletedReward_active_singleton_eq_zero (next : ι ≃ ι)
    (bonus : ι → ℝ) (who background : ι)
    (hmove : next who ≠ who)
    (hbackground : background ∈ punishmentPit next who) :
    quittingSetReward (deletedReward next bonus background)
        ({retainedPlayer next who background hbackground} :
          Finset {player : ι // player ≠ background})
        (retainedPlayer next who background hbackground) = 0 := by
  rw [quittingSetReward_of_nonempty _ (Finset.singleton_nonempty _)]
  change rawReward next bonus
      (liftDeletedCoalition background
        ({retainedPlayer next who background hbackground} :
          Finset {player : ι // player ≠ background})) who = 0
  rw [rawReward_of_omits_punishmentPit_member next bonus who background _
    hbackground (background_notMem_liftDeletedCoalition background _)]
  simp [liftDeletedCoalition, retainedPlayer, hmove]

/-- Deleting any member of `who`'s codimension-two pit raises that fixed
active player's full behavioral punishment value from `-1` to `0`. -/
theorem deleted_punishmentValue_eq_zero (next : ι ≃ ι) (bonus : ι → ℝ)
    (who background : ι) (hmove : next who ≠ who)
    (hbackground : background ∈ punishmentPit next who) :
    quittingPunishmentValue (deletedReward next bonus background)
        (retainedPlayer next who background hbackground) = 0 := by
  rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
  apply le_antisymm
  · have hupper := quittingPunishmentValue_le_max_solo
      (deletedReward next bonus background)
      (retainedPlayer next who background hbackground)
    rw [quittingPunishmentValue_eq_stationaryPunishmentValue,
      deletedReward_active_singleton_eq_zero next bonus who background hmove
        hbackground, max_eq_left (le_refl 0)] at hupper
    exact hupper
  · haveI : Nonempty
        ({player : ι // player ≠ background} → PMF Bool) :=
      ⟨fun _ => PMF.pure false⟩
    apply le_ciInf
    intro root
    exact le_quittingStationaryUnilateralCap_of_forall_le
      (deletedReward next bonus background)
      (retainedPlayer next who background hbackground) (le_refl 0)
      (fun terminal => deletedReward_active_nonneg next bonus who background
        hbackground terminal) root

/-- The pure pit row gives both of `who`'s membership toggles value `-1`. -/
theorem punishmentPit_unilateralCap (next : ι ≃ ι) (bonus : ι → ℝ)
    (who : ι) (hcard : 3 ≤ Fintype.card ι) (hmove : next who ≠ who) :
    quittingStationaryUnilateralCap (reward next bonus)
        (quittingPureSetRoot (punishmentPit next who)) who = -1 := by
  have hjoin : (punishmentJoin next who).Nonempty := by
    rw [← Finset.card_pos, card_punishmentJoin]
    omega
  rw [quittingStationaryUnilateralCap_pureSetRoot,
    insert_who_punishmentPit next who hmove,
    erase_who_punishmentPit]
  rw [quittingSetReward_of_nonempty _ hjoin]
  rw [quittingSetReward_of_nonempty _
      (punishmentPit_nonempty next who hcard hmove)]
  simp [reward]

/-- Every coordinate of the table is at least `-1`. -/
theorem neg_one_le_reward (next : ι ≃ ι) (bonus : ι → ℝ)
    (hbonus : ∀ who, 0 ≤ bonus who)
    (terminal : {S : Finset ι // S.Nonempty}) (who : ι) :
    (-1 : ℝ) ≤ reward next bonus terminal who := by
  simp only [reward, rawReward]
  specialize hbonus who
  split_ifs <;> norm_num <;> linarith

/-- The pit row attains the full behavioral punishment value.  This uses the
stationary-minmax theorem, so the conclusion covers arbitrary
history-dependent opponent plans and replies. -/
theorem punishmentValue_eq_neg_one (next : ι ≃ ι) (bonus : ι → ℝ)
    (hbonus : ∀ who, 0 ≤ bonus who)
    (who : ι) (hcard : 3 ≤ Fintype.card ι) (hmove : next who ≠ who) :
    quittingPunishmentValue (reward next bonus) who = -1 := by
  rw [quittingPunishmentValue_eq_stationaryPunishmentValue]
  apply le_antisymm
  · have hupper := quittingStationaryPunishmentValue_le
      (reward next bonus) who (quittingPureSetRoot (punishmentPit next who))
    rwa [punishmentPit_unilateralCap next bonus who hcard hmove] at hupper
  · haveI : Nonempty (ι → PMF Bool) := ⟨fun _ => PMF.pure false⟩
    apply le_ciInf
    intro root
    exact le_quittingStationaryUnilateralCap_of_forall_le
      (reward next bonus) who (by norm_num)
      (fun terminal => neg_one_le_reward next bonus hbonus terminal who) root

/-- Quantitative deletion sensitivity: under nonnegative bonuses the original
punishment is `-1`, while every pit-member deletion changes it to `0`. -/
theorem punishmentValue_jump_under_background_deletion
    (next : ι ≃ ι) (bonus : ι → ℝ) (hbonus : ∀ player, 0 ≤ bonus player)
    (who background : ι) (hcard : 3 ≤ Fintype.card ι)
    (hmove : next who ≠ who)
    (hbackground : background ∈ punishmentPit next who) :
    quittingPunishmentValue (deletedReward next bonus background)
        (retainedPlayer next who background hbackground) -
      quittingPunishmentValue (reward next bonus) who = 1 := by
  rw [deleted_punishmentValue_eq_zero next bonus who background hmove
      hbackground,
    punishmentValue_eq_neg_one next bonus hbonus who hcard hmove]
  norm_num

/-- The codimension-one omission coalitions give distinct incidence
fingerprints.  Any exact role quotient preserving membership in every
`punishmentJoin who` therefore cannot merge two players. -/
theorem eq_of_same_punishmentJoin_incidence (next : ι ≃ ι) {first second : ι}
    (hincidence : ∀ who,
      (first ∈ punishmentJoin next who ↔
        second ∈ punishmentJoin next who)) :
    first = second := by
  have h := hincidence (next.symm first)
  simp [punishmentJoin] at h
  exact h.symm

/-- Equivalently, distinct players are separated by one punishment-join
coalition. -/
theorem exists_punishmentJoin_separating (next : ι ≃ ι)
    {first second : ι} (hne : first ≠ second) :
    ∃ who, first ∉ punishmentJoin next who ∧
      second ∈ punishmentJoin next who := by
  refine ⟨next.symm first, ?_, ?_⟩
  · simp [punishmentJoin]
  · simpa [punishmentJoin] using hne.symm

/-! ## Explicit unbounded cyclic instances -/

theorem finRotate_ne_self {n : ℕ} (hn : 2 ≤ n) (who : Fin n) :
    finRotate n who ≠ who := by
  have hmem : who ∈ (finRotate n).support := by
    rw [support_finRotate_of_le hn]
    simp
  exact Equiv.Perm.mem_support.mp hmem

/-- For every `n ≥ 3`, the cyclic omission table has punishment value `-1`
for every player. -/
theorem cyclic_punishmentValue_eq_neg_one {n : ℕ} (hn : 3 ≤ n)
    (bonus : Fin n → ℝ) (hbonus : ∀ player, 0 ≤ bonus player)
    (who : Fin n) :
    quittingPunishmentValue (reward (finRotate n) bonus) who = -1 := by
  exact punishmentValue_eq_neg_one (finRotate n) bonus hbonus who
    (by simpa using hn) (finRotate_ne_self (by omega) who)

/-- The canonical cyclic blocker square has background size `n - 2` and
curl equal to its owner's bonus. -/
theorem cyclic_blockerSquare_large_background {n : ℕ} (hn : 3 ≤ n)
    (bonus : Fin n → ℝ) (who : Fin n) :
    (punishmentPit (finRotate n) who).card = n - 2 ∧
      rawReward (finRotate n) bonus Finset.univ who -
          rawReward (finRotate n) bonus
            (insert who (punishmentPit (finRotate n) who)) who -
          rawReward (finRotate n) bonus
            (insert (finRotate n who) (punishmentPit (finRotate n) who)) who +
          rawReward (finRotate n) bonus
            (punishmentPit (finRotate n) who) who = bonus who := by
  constructor
  · simpa using card_punishmentPit (finRotate n) who
      (finRotate_ne_self (by omega) who)
  · exact blockerSquare_curl (finRotate n) bonus who
      (finRotate_ne_self (by omega) who)

/-- At every size `n ≥ 5`, no nonzero Boolean square of the cyclic table can
be supported on four players once `n - 2 > 4`; in general its support has at
least `n - 2` players. -/
theorem cyclic_card_sub_two_le_support_of_booleanCurl_ne_zero
    {n : ℕ} (bonus : Fin n → ℝ) (who first second : Fin n)
    (background : Finset (Fin n)) (hn : 2 ≤ n)
    (hfirstSecond : first ≠ second)
    (hcurl : booleanCurl (finRotate n) bonus who first second background ≠ 0) :
    n - 2 ≤ (insert first (insert second background)).card := by
  simpa using card_sub_two_le_support_of_booleanCurl_ne_zero
    (finRotate n) bonus who first second background
    (finRotate_ne_self hn who) hfirstSecond hcurl

end QuittingPassiveBackgroundCompressionRegression

end GameTheory
