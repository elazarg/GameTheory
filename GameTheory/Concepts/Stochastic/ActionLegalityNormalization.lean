/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.MultiRound.StochasticGame

/-!
# Action-legality normalization for stochastic games

`StochasticGame.Act` is one action set per player, shared by every state
(see the scope note on that field).  A textbook stochastic game may instead
give each player a *state-dependent* legal action set.  This file carries
out the padding reduction promised in that scope note and repeated in
`UniformExistenceConjecture.lean`: give every player every action at every
state, and let an illegal action carry the payoff and transition of some
fixed legal one, so a `StochasticGame` together with a legality predicate
models the state-dependent presentation without a new game type.

No new game structure is defined.  `Legal` singles out, at each state, the
actions each player is actually allowed to use; the *normalized* stage data
is just `G.stagePayoff`/`G.transition` precomposed with a map that replaces
each illegal action component by a chosen legal one.  The normalized data
agrees with the original on jointly legal action profiles, and a legal
Markov profile that is an ε-Nash equilibrium of the normalized stage game at
every state is an ε-Nash equilibrium of the legality-constrained stage game
(deviations restricted to legal actions).  The converse direction is not
addressed here.

## Main definitions

* `StochasticGame.normalizeAct` — replace illegal action components by a
  chosen legal action
* `StochasticGame.normStagePayoff` / `StochasticGame.normTransition` — the
  normalized stage payoff and transition kernel
* `StochasticGame.IsLegalMarkovProfile` — a Markov profile using only legal
  actions
* `StochasticGame.IsεLegalMarkovNash` — ε-Markov-Nash of the
  legality-constrained stage game (deviations restricted to legal actions)
* `StochasticGame.IsεNormalizedMarkovNash` — ε-Markov-Nash of the normalized
  stage game (deviations range over the full padded action set)

## Main results

* `StochasticGame.normalizeAct_of_jointlyLegal` — normalization is the
  identity on jointly legal action profiles
* `StochasticGame.normStagePayoff_of_jointlyLegal` /
  `StochasticGame.normTransition_of_jointlyLegal` — the normalized stage
  data agrees with the original there
* `StochasticGame.isεLegalMarkovNash_of_normalized` — a legal Markov profile
  that is ε-Nash for the normalized stage game at every state is ε-Nash for
  the legality-constrained stage game
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

namespace StochasticGame

variable {ι : Type} (G : StochasticGame ι)
  (Legal : G.State → ∀ i, G.Act i → Prop)
  (hLegal : ∀ s i, ∃ a, Legal s i a)

open Classical in
/-- Normalize a joint action at state `s`: keep every legal component, and
replace every illegal component by a fixed legal action chosen at `(s, i)`
(via `hLegal`). -/
def normalizeAct (s : G.State) (a : ∀ i, G.Act i) : ∀ i, G.Act i :=
  fun i => if Legal s i (a i) then a i else Classical.choose (hLegal s i)

open Classical in
/-- Stage payoff of the normalized game: `G.stagePayoff` applied to the
action profile with every illegal component replaced by a legal one. -/
def normStagePayoff (s : G.State) (a : ∀ i, G.Act i) (who : ι) : ℝ :=
  G.stagePayoff s (G.normalizeAct Legal hLegal s a) who

open Classical in
/-- Transition kernel of the normalized game: `G.transition` applied to the
action profile with every illegal component replaced by a legal one. -/
def normTransition (s : G.State) (a : ∀ i, G.Act i) : PMF G.State :=
  G.transition s (G.normalizeAct Legal hLegal s a)

open Classical in
/-- On a jointly legal action profile, normalization changes nothing. -/
theorem normalizeAct_of_jointlyLegal {s : G.State} {a : ∀ i, G.Act i}
    (h : ∀ i, Legal s i (a i)) :
    G.normalizeAct Legal hLegal s a = a := by
  funext i
  unfold normalizeAct
  rw [if_pos (h i)]

/-- On a jointly legal action profile, the normalized stage payoff agrees
with the original stage payoff. -/
theorem normStagePayoff_of_jointlyLegal {s : G.State} {a : ∀ i, G.Act i}
    (h : ∀ i, Legal s i (a i)) (who : ι) :
    G.normStagePayoff Legal hLegal s a who = G.stagePayoff s a who := by
  unfold normStagePayoff
  rw [normalizeAct_of_jointlyLegal G Legal hLegal h]

/-- On a jointly legal action profile, the normalized transition kernel
agrees with the original transition kernel. -/
theorem normTransition_of_jointlyLegal {s : G.State} {a : ∀ i, G.Act i}
    (h : ∀ i, Legal s i (a i)) :
    G.normTransition Legal hLegal s a = G.transition s a := by
  unfold normTransition
  rw [normalizeAct_of_jointlyLegal G Legal hLegal h]

/-- A Markov profile `σ` uses only legal actions: at every state, every
player's prescribed action is legal there. -/
def IsLegalMarkovProfile (σ : G.MarkovProfile) : Prop :=
  ∀ s i, Legal s i (σ i s)

open Classical in
/-- ε-Markov-Nash equilibrium of the **legality-constrained** stage game: no
player can gain more than `ε` by unilaterally deviating to another *legal*
action at any single state. -/
def IsεLegalMarkovNash (ε : ℝ) (σ : G.MarkovProfile) : Prop :=
  ∀ (s : G.State) (who : ι) (a' : G.Act who), Legal s who a' →
    G.stagePayoff s (fun i => σ i s) who + ε ≥
      G.stagePayoff s (Function.update (fun i => σ i s) who a') who

open Classical in
/-- ε-Markov-Nash equilibrium of the **normalized** stage game: no player can
gain more than `ε` by unilaterally deviating to any action of the (padded)
action set `G.Act who` — illegal deviations are normalized away, so this
ranges over the full action set, not just the legal one. -/
def IsεNormalizedMarkovNash (ε : ℝ) (σ : G.MarkovProfile) : Prop :=
  ∀ (s : G.State) (who : ι) (a' : G.Act who),
    G.normStagePayoff Legal hLegal s (fun i => σ i s) who + ε ≥
      G.normStagePayoff Legal hLegal s
        (Function.update (fun i => σ i s) who a') who

open Classical in
/-- **One direction of the legality-normalization correspondence.**  A legal
Markov profile that is an ε-Nash equilibrium of the normalized stage game at
every state is an ε-Nash equilibrium of the legality-constrained stage game:
restricting attention to legal deviations only tightens the requirement, and
on jointly legal profiles the normalized and original stage payoffs agree
(`normStagePayoff_of_jointlyLegal`). -/
theorem isεLegalMarkovNash_of_normalized {ε : ℝ} {σ : G.MarkovProfile}
    (hσLegal : G.IsLegalMarkovProfile Legal σ)
    (hσNash : G.IsεNormalizedMarkovNash Legal hLegal ε σ) :
    G.IsεLegalMarkovNash Legal ε σ := by
  intro s who a' ha'
  have hupdateLegal :
      ∀ i, Legal s i (Function.update (fun i => σ i s) who a' i) := by
    intro i
    by_cases hi : i = who
    · subst hi
      simpa using ha'
    · simpa [Function.update_of_ne hi] using hσLegal s i
  have hN := hσNash s who a'
  rw [normStagePayoff_of_jointlyLegal G Legal hLegal (fun i => hσLegal s i)]
    at hN
  rw [normStagePayoff_of_jointlyLegal G Legal hLegal hupdateLegal] at hN
  exact hN

end StochasticGame

end GameTheory
