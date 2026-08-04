/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ActionLegalityNormalization

/-!
# The Markov-level converse of action-legality normalization, and its limits

`ActionLegalityNormalization.lean` proves one direction of the padding
correspondence between the legality-constrained stage game and its
state-independent, normalized presentation: a legal Markov profile that is
`ε`-Nash of the *normalized* stage game (`IsεNormalizedMarkovNash`) is `ε`-Nash
of the *legality-constrained* stage game (`IsεLegalMarkovNash`). Its docstring
leaves the converse open, and `docs/uniform-equilibrium/PIPELINE.md`
(`LEAN-F0-1`) records a specific suspected obstruction to it: histories record
the *raw* joint action played (`StageRecord = Fin t → State × JointAct`,
`Basic.lean`), so padding normalizes payoffs and transitions but leaves
illegal action labels observable, and distinct illegal actions collapsing onto
the same legal one could stay distinguishable in the history, serving as
costless public signals that enlarge the set of history-dependent equilibria.

## The point

That obstruction cannot be instantiated against `IsεLegalMarkovNash` /
`IsεNormalizedMarkovNash`, the Markov-level notions actually defined in
`ActionLegalityNormalization.lean`, for two independent reasons:

1. `MarkovStrategy` (`StochasticGame.lean`) is `State → Act`: a Markov
   strategy takes no history argument at all, so nothing expressible at this
   level can condition on which action label was played at an earlier stage.
   There is no channel for a signal to be received.
2. Even granting a channel, `normalizeAct` maps *every* illegal action at
   `(s, i)` to the *same* fixed legal fallback `Classical.choose (hLegal s i)`
   — one fallback per `(s, i)`, not one per illegal action. So distinct
   illegal actions are not merely payoff-equivalent to *some* legal action
   pointwise: `normStagePayoff` cannot distinguish them from each other at
   all (`normStagePayoff_update_eq_of_not_legal` below). There is no "which
   illegal action" information for a stage-level comparison to leak in the
   first place.

Consequently the converse is not just unobstructed by the label-leakage
mechanism at this level — it is provable outright, and this file proves it
(`isεNormalizedMarkovNash_of_legal`).

**This does not discharge `LEAN-F0-1`.** The pipeline's blocking concern is
about the behaviour-strategy notion (`IsUniformEquilibriumPayoff` /
`IsεHorizonNash` in `Uniform.lean`), built on `BehaviorProfile`/`Hist`
(`Basic.lean`), where strategies *do* take the full history — including raw
played actions — as input, and payoffs *are* aggregated across stages with a
genuine continuation. That is where the label-leakage mechanism could in
principle enlarge the equilibrium set; the positive result here, being
confined to Markov profiles and single-stage comparisons, says nothing about
it. Deciding that question needs a normalized `StochasticGame` built from
`normStagePayoff`/`normTransition` together with a legality-constrained
analogue of `IsUniformEquilibriumPayoff` restricted to legal behavior
profiles — neither of which exists in the repository today — and is a
separate, larger piece of work.

## Main results

* `StochasticGame.normStagePayoff_update_eq_of_not_legal` — no two illegal
  deviations at a state are ever distinguishable to `normStagePayoff`
* `StochasticGame.isεNormalizedMarkovNash_of_legal` — **the Markov-level
  converse**: a legal, `ε`-Legal-Markov-Nash profile is `ε`-Normalized-Markov-
  Nash
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

namespace StochasticGame

variable {ι : Type} (G : StochasticGame ι)
  (Legal : G.State → ∀ i, G.Act i → Prop)
  (hLegal : ∀ s i, ∃ a, Legal s i a)

open Classical in
/-- No two illegal deviations at a state are ever distinguishable to
`normStagePayoff`: both normalize to the same fixed legal fallback chosen by
`hLegal`. This is the structural reason the illegal-action-label-as-signal
mechanism cannot arise at the Markov, single-stage level — there is no
"which illegal action" information for `normStagePayoff` to carry. -/
theorem normStagePayoff_update_eq_of_not_legal {s : G.State}
    (a : ∀ i, G.Act i) (who : ι) {a₁ a₂ : G.Act who} (h₁ : ¬ Legal s who a₁)
    (h₂ : ¬ Legal s who a₂) (i : ι) :
    G.normStagePayoff Legal hLegal s (Function.update a who a₁) i =
      G.normStagePayoff Legal hLegal s (Function.update a who a₂) i := by
  unfold normStagePayoff
  congr 1
  unfold normalizeAct
  funext j
  by_cases hj : j = who
  · subst hj
    simp [h₁, h₂]
  · simp [Function.update_of_ne hj]

open Classical in
/-- **The Markov-level converse of the legality-normalization
correspondence.** A legal Markov profile that is `ε`-Nash of the
legality-constrained stage game is `ε`-Nash of the normalized stage game: a
legal deviation `a'` normalizes to itself, so its normalized payoff is the raw
payoff already covered by legal-Nash; an illegal deviation `a'` normalizes to
the fixed legal fallback `Classical.choose (hLegal s who)` regardless of
which illegal action `a'` is, so its normalized payoff equals the raw payoff
of deviating to that fallback, again already covered by legal-Nash (the
fallback is itself legal). -/
theorem isεNormalizedMarkovNash_of_legal {ε : ℝ} {σ : G.MarkovProfile}
    (hσLegal : G.IsLegalMarkovProfile Legal σ)
    (hσNash : G.IsεLegalMarkovNash Legal ε σ) :
    G.IsεNormalizedMarkovNash Legal hLegal ε σ := by
  intro s who a'
  have hbase : G.normStagePayoff Legal hLegal s (fun i => σ i s) who =
      G.stagePayoff s (fun i => σ i s) who :=
    G.normStagePayoff_of_jointlyLegal Legal hLegal (fun i => hσLegal s i) who
  by_cases ha' : Legal s who a'
  · have hdev : G.normStagePayoff Legal hLegal s
        (Function.update (fun i => σ i s) who a') who =
        G.stagePayoff s (Function.update (fun i => σ i s) who a') who := by
      apply G.normStagePayoff_of_jointlyLegal
      intro i
      by_cases hi : i = who
      · subst hi
        simpa using ha'
      · simpa [Function.update_of_ne hi] using hσLegal s i
    rw [hbase, hdev]
    exact hσNash s who a' ha'
  · set a₀ := Classical.choose (hLegal s who) with ha₀def
    have ha₀ : Legal s who a₀ := Classical.choose_spec (hLegal s who)
    have hdev : G.normStagePayoff Legal hLegal s
        (Function.update (fun i => σ i s) who a') who =
        G.stagePayoff s (Function.update (fun i => σ i s) who a₀) who := by
      unfold normStagePayoff
      congr 1
      unfold normalizeAct
      funext i
      by_cases hi : i = who
      · subst hi
        simp [ha', ha₀def]
      · simp [Function.update_of_ne hi, hσLegal s i]
    rw [hbase, hdev]
    exact hσNash s who a₀ ha₀

end StochasticGame

end GameTheory
