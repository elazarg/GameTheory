/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.PMFProduct
import GameTheory.Concepts.Stochastic.Models.Quitting.Game
import UniformEquilibrium.Quitting.Classification.TwoPlayer.Existence
import UniformEquilibrium.Quitting.Classification.ThreePlayer.Existence

/-!
# Player reindexing for quitting games

Uniform-equilibrium existence in a quitting game is a property of the terminal
reward table only up to a relabeling of the players.  This module makes that
transport precise.  A player-type equivalence `e : ι ≃ κ` induces, coalition by
coalition and stage by stage, an equivalence between the data of the quitting
game of a reward table on `ι` and the data of the quitting game of the
transported table on `κ`: nonempty quitter coalitions, states, joint
quit/continue actions, finite histories, and behavior profiles all transport
componentwise.  The transition kernel and the stage payoff commute with the
transport, hence so do the history law and every finite-horizon average
payoff, and uniform-equilibrium existence transfers along `e`.

The payoff of the module is the pair of small-cardinality corollaries: the
machine-checked two-player (`Bool`) and three-player (`Fin 3`) existence
theorems become existence for *every* finite player type with exactly two or
exactly three elements.

## Main definitions

* `quittingCoalitionEquiv`, `quittingStateEquiv`, `quittingActEquiv`,
  `quittingHistEquiv` — componentwise transport of quitting-game data along a
  player equivalence
* `quittingRewardReindex` — the transported terminal reward table
* `quittingProfilePullback` — behavior profiles of the reindexed game pulled
  back to the original player type

## Main results

* `histDist_quittingProfilePullback` — the finite-history law transports along
  the history equivalence
* `finiteAveragePayoff_quittingProfilePullback` — every finite-horizon average
  payoff is preserved by the pullback, player by player
* `quittingGame_exists_uniformEquilibriumPayoff_of_reindex` — existence of a
  uniform-equilibrium payoff transports along any player equivalence
* `quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two` and
  `quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three` — every
  finite quitting game with exactly two or exactly three players has a
  uniform-equilibrium payoff
-/

noncomputable section

namespace Math
namespace PMFProduct

open scoped BigOperators

/-- Pushing an independent product of identically typed factors forward along
an equivalence of profiles that acts by precomposition with `e.symm` reindexes
the factor family along `e.symm`.  The profile equivalence `E` is abstract and
constrained only pointwise, so call sites keep control of its syntactic
form. -/
theorem pmfPi_map_precompEquiv {ι κ B : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (E : (ι → B) ≃ (κ → B)) (hE : ∀ a j, E a j = a (e.symm j))
    (x : ι → PMF B) :
    PMF.map E (pmfPi (A := fun _ : ι => B) x) =
      pmfPi (A := fun _ : κ => B) (fun j => x (e.symm j)) := by
  have hEsymm : ∀ (b : κ → B) (i : ι), E.symm b i = b (e i) := by
    intro b i
    have hb := hE (E.symm b) (e i)
    rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply] at hb
    exact hb.symm
  ext b
  rw [ProbabilityMassFunction.map_equiv_apply, pmfPi_apply, pmfPi_apply]
  refine Fintype.prod_equiv e _ _ fun i => ?_
  simp [hEsymm]

end PMFProduct
end Math

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι κ : Type}

/-! ## Componentwise transport of quitting-game data

A player equivalence `e : ι ≃ κ` acts on every layer of a quitting game's
data.  None of the equivalences below needs finiteness or decidable equality
of the player types. -/

/-- Transport of nonempty quitter coalitions along a player equivalence:
map the coalition forward through `e`. -/
def quittingCoalitionEquiv (e : ι ≃ κ) :
    {S : Finset ι // S.Nonempty} ≃ {T : Finset κ // T.Nonempty} where
  toFun S := ⟨S.1.map e.toEmbedding, Finset.map_nonempty.mpr S.2⟩
  invFun T := ⟨T.1.map e.symm.toEmbedding, Finset.map_nonempty.mpr T.2⟩
  left_inv S := by
    refine Subtype.ext ?_
    refine Finset.ext fun i => ?_
    simp [Finset.mem_map_equiv]
  right_inv T := by
    refine Subtype.ext ?_
    refine Finset.ext fun j => ?_
    simp [Finset.mem_map_equiv]

/-- The transported coalition is the image of the original coalition. -/
@[simp] theorem quittingCoalitionEquiv_coe (e : ι ≃ κ)
    (S : {S : Finset ι // S.Nonempty}) :
    (quittingCoalitionEquiv e S : Finset κ) = S.1.map e.toEmbedding :=
  rfl

/-- The pulled-back coalition is the preimage of the original coalition. -/
@[simp] theorem quittingCoalitionEquiv_symm_coe (e : ι ≃ κ)
    (T : {T : Finset κ // T.Nonempty}) :
    ((quittingCoalitionEquiv e).symm T : Finset ι) = T.1.map e.symm.toEmbedding :=
  rfl

/-- Transport of a quitting-game terminal reward table along a player
equivalence: the transported table, read at a coalition `T` of new-type
players and a new-type player `j`, is the original table read at the
pulled-back coalition and the pulled-back player. -/
def quittingRewardReindex (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    {T : Finset κ // T.Nonempty} → Payoff κ :=
  fun T j => reward ((quittingCoalitionEquiv e).symm T) (e.symm j)

/-- Evaluation of the transported reward table. -/
@[simp] theorem quittingRewardReindex_apply (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (T : {T : Finset κ // T.Nonempty}) (j : κ) :
    quittingRewardReindex e reward T j =
      reward ((quittingCoalitionEquiv e).symm T) (e.symm j) :=
  rfl

/-- Transport of quitting-game states along a player equivalence: the active
state maps to the active state, and an absorbed state maps to absorption at
the transported coalition. -/
def quittingStateEquiv (e : ι ≃ κ) :
    Option {S : Finset ι // S.Nonempty} ≃ Option {T : Finset κ // T.Nonempty} where
  toFun := Option.map (quittingCoalitionEquiv e)
  invFun := Option.map (quittingCoalitionEquiv e).symm
  left_inv s := by
    cases s with
    | none => rfl
    | some S => simp
  right_inv s := by
    cases s with
    | none => rfl
    | some T => simp

/-- The state transport fixes the active state. -/
@[simp] theorem quittingStateEquiv_none (e : ι ≃ κ) :
    quittingStateEquiv e none = none :=
  rfl

/-- The state transport sends absorption at `S` to absorption at the
transported coalition. -/
@[simp] theorem quittingStateEquiv_some (e : ι ≃ κ)
    (S : {S : Finset ι // S.Nonempty}) :
    quittingStateEquiv e (some S) = some (quittingCoalitionEquiv e S) :=
  rfl

/-- The inverse state transport fixes the active state. -/
@[simp] theorem quittingStateEquiv_symm_none (e : ι ≃ κ) :
    (quittingStateEquiv e).symm none = none :=
  rfl

/-- The inverse state transport pulls an absorbed state back coalitionwise. -/
@[simp] theorem quittingStateEquiv_symm_some (e : ι ≃ κ)
    (T : {T : Finset κ // T.Nonempty}) :
    (quittingStateEquiv e).symm (some T) =
      some ((quittingCoalitionEquiv e).symm T) :=
  rfl

/-- Transport of joint quit/continue profiles along a player equivalence: the
transported profile plays at `j` what the original profile plays at
`e.symm j`. -/
def quittingActEquiv (e : ι ≃ κ) : (ι → Bool) ≃ (κ → Bool) where
  toFun a := fun j => a (e.symm j)
  invFun b := fun i => b (e i)
  left_inv a := by
    funext i
    simp
  right_inv b := by
    funext j
    simp

/-- Evaluation of a transported joint action. -/
@[simp] theorem quittingActEquiv_apply (e : ι ≃ κ) (a : ι → Bool) (j : κ) :
    quittingActEquiv e a j = a (e.symm j) :=
  rfl

/-- Evaluation of a pulled-back joint action. -/
@[simp] theorem quittingActEquiv_symm_apply (e : ι ≃ κ) (b : κ → Bool) (i : ι) :
    (quittingActEquiv e).symm b i = b (e i) :=
  rfl

section GameTransport

variable [Fintype ι] [Fintype κ]

/-- The quitter set of a transported joint action is the image of the
original quitter set under the player equivalence. -/
theorem quittingActEquiv_quitterSet (e : ι ≃ κ) (a : ι → Bool) :
    Finset.filter (fun j => quittingActEquiv e a j = true) Finset.univ =
      (Finset.filter (fun i => a i = true) Finset.univ).map e.toEmbedding := by
  refine Finset.ext fun j => ?_
  simp [Finset.mem_map_equiv]

/-- **The transition kernel commutes with player reindexing.**  Transporting
the state and the joint action and then stepping the reindexed game is
stepping the original game and pushing the state distribution forward. -/
theorem quittingGame_transition_reindex (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (s : (quittingGame reward).State) (a : ι → Bool) :
    (quittingGame (quittingRewardReindex e reward)).transition
        (quittingStateEquiv e s) (quittingActEquiv e a) =
      PMF.map (quittingStateEquiv e) ((quittingGame reward).transition s a) := by
  cases s with
  | some S =>
      change PMF.pure (some (quittingCoalitionEquiv e S)) =
        PMF.map (quittingStateEquiv e) (PMF.pure (some S))
      exact (PMF.pure_map (⇑(quittingStateEquiv e)) (some S)).symm
  | none =>
      change
        (if hq : (Finset.filter (fun j => quittingActEquiv e a j = true)
            Finset.univ).Nonempty then
          PMF.pure (some ⟨Finset.filter (fun j => quittingActEquiv e a j = true)
            Finset.univ, hq⟩)
        else PMF.pure none) =
        PMF.map (quittingStateEquiv e)
          (if hq : (Finset.filter (fun i => a i = true) Finset.univ).Nonempty then
            PMF.pure (some ⟨Finset.filter (fun i => a i = true) Finset.univ, hq⟩)
          else PMF.pure none)
      rw [quittingActEquiv_quitterSet e a]
      by_cases hne : (Finset.filter (fun i => a i = true) Finset.univ).Nonempty
      · have hmap : ((Finset.filter (fun i => a i = true) Finset.univ).map
            e.toEmbedding).Nonempty := Finset.map_nonempty.mpr hne
        rw [dif_pos hne, dif_pos hmap]
        exact (PMF.pure_map (⇑(quittingStateEquiv e)) (some ⟨_, hne⟩)).symm
      · have hmap : ¬ ((Finset.filter (fun i => a i = true) Finset.univ).map
            e.toEmbedding).Nonempty :=
          fun hcontra => hne (Finset.map_nonempty.mp hcontra)
        rw [dif_neg hne, dif_neg hmap]
        exact (PMF.pure_map (⇑(quittingStateEquiv e)) none).symm

/-- **The stage payoff commutes with player reindexing.**  The reindexed game
pays the transported player at the transported state and action exactly what
the original game pays the original player. -/
theorem quittingGame_stagePayoff_reindex (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (s : (quittingGame reward).State) (a : ι → Bool) (who : ι) :
    (quittingGame (quittingRewardReindex e reward)).stagePayoff
        (quittingStateEquiv e s) (quittingActEquiv e a) (e who) =
      (quittingGame reward).stagePayoff s a who := by
  cases s with
  | none => rfl
  | some S =>
      change quittingRewardReindex e reward (quittingCoalitionEquiv e S) (e who) =
        reward S who
      rw [quittingRewardReindex_apply, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]

/-- Transport of finite histories of the quitting game along a player
equivalence: transport every recorded state and joint action and the current
state. -/
def quittingHistEquiv (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (t : ℕ) :
    (quittingGame reward).Hist t ≃
      (quittingGame (quittingRewardReindex e reward)).Hist t where
  toFun h :=
    (fun k => (quittingStateEquiv e (h.1 k).1, quittingActEquiv e (h.1 k).2),
      quittingStateEquiv e h.2)
  invFun h' :=
    (fun k => ((quittingStateEquiv e).symm (h'.1 k).1,
        (quittingActEquiv e).symm (h'.1 k).2),
      (quittingStateEquiv e).symm h'.2)
  left_inv h := by
    refine Prod.ext (funext fun k => ?_) (by simp)
    simp
  right_inv h' := by
    refine Prod.ext (funext fun k => ?_) (by simp)
    simp

/-- Stage records of a transported history. -/
@[simp] theorem quittingHistEquiv_apply_fst (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {t : ℕ}
    (h : (quittingGame reward).Hist t) (k : Fin t) :
    (quittingHistEquiv e reward t h).1 k =
      (quittingStateEquiv e (h.1 k).1, quittingActEquiv e (h.1 k).2) :=
  rfl

/-- Current state of a transported history. -/
@[simp] theorem quittingHistEquiv_apply_snd (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {t : ℕ}
    (h : (quittingGame reward).Hist t) :
    (quittingHistEquiv e reward t h).2 = quittingStateEquiv e h.2 :=
  rfl

/-- Stage records of a pulled-back history. -/
@[simp] theorem quittingHistEquiv_symm_apply_fst (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {t : ℕ}
    (h' : (quittingGame (quittingRewardReindex e reward)).Hist t) (k : Fin t) :
    ((quittingHistEquiv e reward t).symm h').1 k =
      ((quittingStateEquiv e).symm (h'.1 k).1,
        (quittingActEquiv e).symm (h'.1 k).2) :=
  rfl

/-- Current state of a pulled-back history. -/
@[simp] theorem quittingHistEquiv_symm_apply_snd (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {t : ℕ}
    (h' : (quittingGame (quittingRewardReindex e reward)).Hist t) :
    ((quittingHistEquiv e reward t).symm h').2 =
      (quittingStateEquiv e).symm h'.2 :=
  rfl

/-- Transporting a one-stage extension of a history is the one-stage extension
of the transported history by the transported stage. -/
theorem quittingHistEquiv_snoc (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) {t : ℕ}
    (h : (quittingGame reward).Hist t) (a : (quittingGame reward).JointAct)
    (s' : (quittingGame reward).State) :
    quittingHistEquiv e reward (t + 1)
        ((Fin.snoc h.1 (h.2, a), s') : (quittingGame reward).Hist (t + 1)) =
      (Fin.snoc (quittingHistEquiv e reward t h).1
          ((quittingHistEquiv e reward t h).2, quittingActEquiv e a),
        quittingStateEquiv e s') := by
  refine Prod.ext (funext fun k => ?_) rfl
  rw [quittingHistEquiv_apply_fst]
  dsimp only
  cases k using Fin.lastCases with
  | last =>
      rw [Fin.snoc_last, Fin.snoc_last]
      rfl
  | cast k =>
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
      rfl

/-- Pull a behavior profile of the reindexed quitting game back to the
original player type: player `i` plays after a history what `e i` plays after
the transported history. -/
def quittingProfilePullback (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ' : (quittingGame (quittingRewardReindex e reward)).BehaviorProfile) :
    (quittingGame reward).BehaviorProfile :=
  fun i t h => σ' (e i) t (quittingHistEquiv e reward t h)

/-- The joint mixed action of the pulled-back profile pushes forward, along
the action transport, to the joint mixed action of the original profile at
the transported history. -/
theorem stageActionDist_quittingProfilePullback (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ' : (quittingGame (quittingRewardReindex e reward)).BehaviorProfile)
    {t : ℕ} (h : (quittingGame reward).Hist t) :
    PMF.map (quittingActEquiv e)
        ((quittingGame reward).stageActionDist
          (quittingProfilePullback e reward σ') h) =
      (quittingGame (quittingRewardReindex e reward)).stageActionDist σ'
        (quittingHistEquiv e reward t h) := by
  refine (pmfPi_map_precompEquiv (B := Bool) e (quittingActEquiv e)
    (fun _ _ => rfl)
    (fun i => quittingProfilePullback e reward σ' i t h)).trans ?_
  change pmfPi (fun j => quittingProfilePullback e reward σ' (e.symm j) t h) =
    (quittingGame (quittingRewardReindex e reward)).stageActionDist σ'
      (quittingHistEquiv e reward t h)
  have harg : (fun j => quittingProfilePullback e reward σ' (e.symm j) t h) =
      fun j : κ => σ' j t (quittingHistEquiv e reward t h) := by
    funext j
    change σ' (e (e.symm j)) t (quittingHistEquiv e reward t h) =
      σ' j t (quittingHistEquiv e reward t h)
    rw [Equiv.apply_symm_apply]
  rw [harg]
  rfl

/-- One-step transport of the history law: mapping the one-stage extension
distribution of the pulled-back profile through the history transport gives
the one-stage extension distribution of the original profile at the
transported history. -/
theorem quittingHistEquiv_map_historyStep (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ' : (quittingGame (quittingRewardReindex e reward)).BehaviorProfile)
    {t : ℕ} (h : (quittingGame reward).Hist t) :
    PMF.map (quittingHistEquiv e reward (t + 1))
        (((quittingGame reward).stageActionDist
            (quittingProfilePullback e reward σ') h).bind fun a =>
          ((quittingGame reward).transition h.2 a).bind fun s' =>
            PMF.pure
              ((Fin.snoc h.1 (h.2, a), s') :
                (quittingGame reward).Hist (t + 1))) =
      ((quittingGame (quittingRewardReindex e reward)).stageActionDist σ'
          (quittingHistEquiv e reward t h)).bind fun b =>
        ((quittingGame (quittingRewardReindex e reward)).transition
            (quittingHistEquiv e reward t h).2 b).bind fun s'' =>
          PMF.pure
            ((Fin.snoc (quittingHistEquiv e reward t h).1
                ((quittingHistEquiv e reward t h).2, b), s'') :
              (quittingGame (quittingRewardReindex e reward)).Hist (t + 1)) := by
  have hinner : ∀ a : (quittingGame reward).JointAct,
      PMF.map (quittingHistEquiv e reward (t + 1))
          (((quittingGame reward).transition h.2 a).bind fun s' =>
            PMF.pure
              ((Fin.snoc h.1 (h.2, a), s') :
                (quittingGame reward).Hist (t + 1))) =
        ((quittingGame (quittingRewardReindex e reward)).transition
            (quittingHistEquiv e reward t h).2 (quittingActEquiv e a)).bind
          fun s'' =>
            PMF.pure
              ((Fin.snoc (quittingHistEquiv e reward t h).1
                  ((quittingHistEquiv e reward t h).2, quittingActEquiv e a),
                  s'') :
                (quittingGame (quittingRewardReindex e reward)).Hist (t + 1)) := by
    intro a
    have htrans : (quittingGame (quittingRewardReindex e reward)).transition
        (quittingHistEquiv e reward t h).2 (quittingActEquiv e a) =
          PMF.map (quittingStateEquiv e)
            ((quittingGame reward).transition h.2 a) :=
      quittingGame_transition_reindex e reward h.2 a
    refine (PMF.map_bind _ _ _).trans ?_
    refine Eq.trans ?_ (congrFun (congrArg PMF.bind htrans.symm) _)
    refine Eq.trans ?_ (PMF.bind_map _ _ _).symm
    refine congrArg (PMF.bind ((quittingGame reward).transition h.2 a))
      (funext fun s' => ?_)
    exact (PMF.pure_map (⇑(quittingHistEquiv e reward (t + 1))) _).trans
      (congrArg PMF.pure (quittingHistEquiv_snoc e reward h a s'))
  refine (PMF.map_bind _ _ _).trans ?_
  refine Eq.trans (congrArg
      (PMF.bind ((quittingGame reward).stageActionDist
        (quittingProfilePullback e reward σ') h))
      (funext hinner)) ?_
  exact (PMF.bind_map _ _ _).symm.trans
    (congrFun (congrArg PMF.bind
      (stageActionDist_quittingProfilePullback e reward σ' h))
      fun b =>
        ((quittingGame (quittingRewardReindex e reward)).transition
            (quittingHistEquiv e reward t h).2 b).bind fun s'' =>
          PMF.pure
            ((Fin.snoc (quittingHistEquiv e reward t h).1
                ((quittingHistEquiv e reward t h).2, b), s'') :
              (quittingGame (quittingRewardReindex e reward)).Hist (t + 1)))

/-- **Transport of the history law.**  At every horizon, the distribution of
transported histories under the pulled-back profile is the history
distribution of the original profile in the reindexed game. -/
theorem histDist_quittingProfilePullback (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ' : (quittingGame (quittingRewardReindex e reward)).BehaviorProfile)
    (T : ℕ) :
    PMF.map (quittingHistEquiv e reward T)
        ((quittingGame reward).histDist
          (quittingProfilePullback e reward σ') none T) =
      (quittingGame (quittingRewardReindex e reward)).histDist σ' none T := by
  induction T with
  | zero =>
      simp only [histDist_zero, PMF.pure_map]
      refine congrArg PMF.pure ?_
      exact Prod.ext (funext fun k => Fin.elim0 k) rfl
  | succ t ih =>
      rw [histDist_succ, histDist_succ, PMF.map_bind, ← ih, PMF.bind_map]
      congr 1
      funext h
      simp only [Function.comp_apply]
      exact quittingHistEquiv_map_historyStep e reward σ' h

/-- The total payoff of the transported player along a transported history is
the total payoff of the original player along the original history. -/
theorem totalPayoff_quittingHistEquiv (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) {t : ℕ}
    (h : (quittingGame reward).Hist t) :
    (quittingGame (quittingRewardReindex e reward)).totalPayoff (e who)
        (quittingHistEquiv e reward t h) =
      (quittingGame reward).totalPayoff who h := by
  unfold StochasticGame.totalPayoff
  refine Finset.sum_congr rfl fun k _ => ?_
  exact quittingGame_stagePayoff_reindex e reward (h.1 k).1 (h.1 k).2 who

/-- **Transport of finite-horizon average payoffs.**  In the reindexed game
under `σ'`, player `e who` earns at every horizon exactly what player `who`
earns in the original game under the pulled-back profile. -/
theorem finiteAveragePayoff_quittingProfilePullback (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ' : (quittingGame (quittingRewardReindex e reward)).BehaviorProfile)
    (T : ℕ) (who : ι) :
    (quittingGame (quittingRewardReindex e reward)).finiteAveragePayoff
        none T σ' (e who) =
      (quittingGame reward).finiteAveragePayoff none T
        (quittingProfilePullback e reward σ') who := by
  unfold StochasticGame.finiteAveragePayoff
  congr 1
  rw [← histDist_quittingProfilePullback e reward σ' T, expect_map]
  congr 1
  funext h
  exact totalPayoff_quittingHistEquiv e reward who h

section EquilibriumTransport

variable [DecidableEq ι] [DecidableEq κ]

/-- Pulling back a unilaterally updated profile updates the pulled-back
profile at the corresponding player with the pulled-back deviation. -/
theorem quittingProfilePullback_update (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (σ' : (quittingGame (quittingRewardReindex e reward)).BehaviorProfile)
    (who : ι)
    (dev' : (quittingGame (quittingRewardReindex e reward)).BehaviorStrategy
      (e who)) :
    quittingProfilePullback e reward (Function.update σ' (e who) dev') =
      Function.update (quittingProfilePullback e reward σ') who
        (fun t h => dev' t (quittingHistEquiv e reward t h)) := by
  funext i
  by_cases hi : i = who
  · subst hi
    rw [Function.update_self]
    funext t h
    change Function.update σ' (e i) dev' (e i) t
        (quittingHistEquiv e reward t h) =
      dev' t (quittingHistEquiv e reward t h)
    rw [Function.update_self]
  · rw [Function.update_of_ne hi]
    funext t h
    change Function.update σ' (e who) dev' (e i) t
        (quittingHistEquiv e reward t h) =
      σ' (e i) t (quittingHistEquiv e reward t h)
    rw [Function.update_of_ne (fun heq => hi (e.injective heq))]

/-- **Player-reindexing transport for the quitting conjecture.**  If the
quitting game of the transported reward table has a uniform-equilibrium
payoff from the active state, then so does the quitting game of the original
table: pull every profile back along the equivalence and read the payoff
vector through `e`.  Every unilateral deviation of the original game is the
pullback of a unilateral deviation of the reindexed game with the same
finite-horizon average payoffs, so the Nash inequalities transfer with the
same horizon threshold. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_reindex (e : ι ≃ κ)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hκ : ∃ payoff : Payoff κ,
      (quittingGame (quittingRewardReindex e reward)).IsUniformEquilibriumPayoff
        none payoff) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  obtain ⟨v', hv'⟩ := hκ
  refine ⟨fun who => v' (e who), ?_⟩
  intro ε hε
  obtain ⟨σ', T₀, hσ'⟩ := hv' ε hε
  refine ⟨quittingProfilePullback e reward σ', T₀, fun T hT => ?_⟩
  obtain ⟨hNash, hclose⟩ := hσ' T hT
  constructor
  · intro who dev
    have hdev := hNash (e who)
      (fun t h' => dev t ((quittingHistEquiv e reward t).symm h'))
    have hdevEq := finiteAveragePayoff_quittingProfilePullback e reward
      (Function.update σ' (e who)
        (fun t h' => dev t ((quittingHistEquiv e reward t).symm h'))) T who
    have hpullEq : quittingProfilePullback e reward
        (Function.update σ' (e who)
          (fun t h' => dev t ((quittingHistEquiv e reward t).symm h'))) =
        Function.update (quittingProfilePullback e reward σ') who dev := by
      rw [quittingProfilePullback_update]
      refine congrArg
        (Function.update (quittingProfilePullback e reward σ') who) ?_
      funext t h
      rw [Equiv.symm_apply_apply]
    rw [hpullEq] at hdevEq
    have hon := finiteAveragePayoff_quittingProfilePullback e reward σ' T who
    rw [hon, hdevEq] at hdev
    exact hdev
  · intro who
    have hon := finiteAveragePayoff_quittingProfilePullback e reward σ' T who
    rw [← hon]
    exact hclose (e who)

end EquilibriumTransport

end GameTransport

/-! ## Existence at small player cardinalities

The two concrete capstones — existence over `Bool` and over `Fin 3` — extend
to every finite player type of the same cardinality by transporting along an
enumeration. -/

section SmallCardinalities

variable [Fintype ι] [DecidableEq ι]

/-- **Every finite quitting game with exactly two players has a
uniform-equilibrium payoff**, by transporting the unconditional `Bool`
existence theorem along any enumeration of the player type. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_two
    (hcard : Fintype.card ι = 2)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have e : ι ≃ Bool := (Fintype.equivFinOfCardEq hcard).trans finTwoEquiv
  exact quittingGame_exists_uniformEquilibriumPayoff_of_reindex e reward
    (QuittingTwoPlayerExistence.quittingGame_exists_uniformEquilibriumPayoff_twoPlayer
      (quittingRewardReindex e reward))

/-- **Every finite quitting game with exactly three players has a
uniform-equilibrium payoff**, by transporting the unconditional `Fin 3`
existence theorem along any enumeration of the player type. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_card_eq_three
    (hcard : Fintype.card ι = 3)
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  have e : ι ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  exact quittingGame_exists_uniformEquilibriumPayoff_of_reindex e reward
    (quittingGame_exists_uniformEquilibriumPayoff_threePlayer
      (quittingRewardReindex e reward))

end SmallCardinalities

end GameTheory
