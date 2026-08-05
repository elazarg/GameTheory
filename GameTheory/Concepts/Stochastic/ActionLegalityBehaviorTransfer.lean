/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ActionLegalityNormalization
import GameTheory.Concepts.Stochastic.Uniform

/-!
# The padded game and the behaviour-level legality transfer, restricted to legal play

`ActionLegalityNormalization.lean` normalizes a *stage*: `normStagePayoff`/
`normTransition` replace illegal action components before evaluating
`G.stagePayoff`/`G.transition`, and the Markov-level correspondence between
the legality-constrained stage game and its normalization is proved there and
in `ActionLegalityMarkovConverse.lean`.  Neither file assembles the
normalization into an actual `StochasticGame` value, and neither reaches the
behaviour-strategy machinery (`BehaviorProfile`/`Hist`/`histDist`) of
`Basic.lean` / `Uniform.lean`, which is what
`StochasticGame.IsUniformEquilibriumPayoff` is built on.  This file does both.

## What closes

* `StochasticGame.normalizedGame` — deliverable (1): the padding construction
  itself, an actual `StochasticGame` value with `Act := G.Act` (already
  state-independent) and every action legal everywhere.
* `StochasticGame.finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile`
  — deliverable (2), lifted from a single stage to whole trajectories: a
  behavior profile that **unconditionally** plays only legal actions (at
  every history it is fed, reachable or not) induces the *same* history
  distribution and the *same* finite-horizon payoffs in `G` and in its
  padding.  No history-observability argument is needed for this lemma: an
  unconditionally-legal profile never plays an illegal-looking action, so
  there is nothing for the padded game's bookkeeping to disagree with `G`
  about.
* `StochasticGame.isεLegalHorizonNash_normalizedGame_iff` and
  `StochasticGame.isLegalUniformEquilibriumPayoff_normalizedGame_iff` —
  deliverable (3)'s two-directional transfer, for the notions
  `IsεLegalHorizonNash` / `IsLegalUniformEquilibriumPayoff` defined below:
  ε-Nash (resp. uniform equilibrium payoff) **against legal deviations only,
  by a profile that is itself unconditionally legal** transfers in both
  directions between `G` and `G.normalizedGame`.  This is a genuine two-sided
  iff, not a one-sided containment: restricting both the prescribed profile
  and every deviation to legality on both sides of the correspondence makes
  the two notions the same mathematical object by deliverable (2), so nothing
  is lost either way.

## What does not close, and exactly why

The consequence the padding reduction is supposed to deliver is stronger:
take the **unrestricted** witness that the general conjecture
(`exists_uniformDeviationCapConstructor`, stated for arbitrary
state-independent games and hence applicable to `G.normalizedGame` once
proved) would hand back, and produce a *legal* equilibrium of `G`.  That
witness `σ` is an arbitrary `BehaviorProfile` with no legality guarantee at
all, on-path or under deviation, so this needs the converse of
`isεLegalHorizonNash_normalizedGame_iff`'s restricted statement: from an
**unrestricted** `(G.normalizedGame ...).IsεHorizonNash s₀ T ε σ`, produce a
legal profile with matching (or matching-up-to-`ε`) legal-restricted Nash
behaviour in `G`.

The natural repair is projection: replace `σ`'s output at every `(i, t, h)`
by its normalization, `σ♮ i t h := (σ i t h).map (normalize1 h.2 i)`, which is
unconditionally legal by construction.  This repair does **not** go through,
and the reason is a specific, checkable failure of a coupling argument, not
just the general "labels are a public signal" intuition recorded in
`ActionLegalityMarkovConverse.lean`.

Concretely: relating `(G.normalizedGame ...).histDist σ♮ s₀ t` to
`(G.normalizedGame ...).histDist σ s₀ t` by induction on `t` requires, at the
inductive step, evaluating `σ♮` (equivalently `σ`) at a history `h` drawn from
`histDist σ♮ s₀ t` — which, by the induction hypothesis, is *already*
normalized (all-legal), i.e. `h = normalizeHist h₀` for some raw `h₀` in the
support of `histDist σ s₀ t`.  But `σ♮ i t h := (σ i t h).map (normalize1 h.2
i)` looks up `σ` **at `h` itself** (the normalized history), not at the raw
`h₀` that `σ`'s own trajectory would have produced.  Since `normalizeAct` is
generally non-injective (many raw histories collapse to the same normalized
one), there is no way to recover `h₀` from `h`, and an arbitrary `σ` need not
satisfy `σ i t (normalizeHist h₀) = σ i t h₀` — nothing forces a profile to be
insensitive to whether the history it is fed carries raw or already-legal
labels. So `σ♮`'s own induced trajectory is not controlled by `σ`'s cap
property at all past the first stage, and the projection carries no
guarantee forward.  This is the exact mechanism behind the informal
"illegal labels are a costless public signal" diagnosis in
`ActionLegalityMarkovConverse.lean`: it is not merely that opponents *could*
react to a raw illegal label, it is that **no expression built from `σ`
alone can even be evaluated at the history a legality-respecting profile
would actually reach**, because that history was never in `σ`'s domain of
observed behaviour to begin with.

Fixing this needs a strategy space that is *structurally* insensitive to
illegal labels — the "normalized-action histories" repair the pipeline
identifies as load-bearing, where a strategy only ever observes a legal
history and the *type* rules out feeding it a raw one. That is a
substantially larger undertaking (redefining `Hist`/`histDist` themselves, not
just adding a legality side-condition on `BehaviorProfile`) and is not
attempted here. Consequently `UniformExistenceConjecture.lean`'s scope note
is unchanged by this file: the conjecture is still formally stated for the
state-independent class only.

## Main definitions

* `StochasticGame.normalizedGame` — the padded game: same state and action
  types, normalized stage payoff and transition, every action legal
  everywhere
* `StochasticGame.IsLegalBehaviorStrategy` / `IsLegalBehaviorProfile` — a
  strategy/profile that plays only legal actions, unconditionally on every
  history it could be fed
* `StochasticGame.IsεLegalHorizonNash` — ε-Nash of the `T`-stage game,
  restricted on both sides to legal play: legal prescribed profile, legal
  deviations only
* `StochasticGame.IsLegalUniformEquilibriumPayoff` — the legal-play uniform
  equilibrium payoff notion built on `IsεLegalHorizonNash`

## Main results

* `StochasticGame.jointlyLegal_of_mem_support_stageActionDist` — an
  unconditionally legal profile's joint action at any history is jointly
  legal
* `StochasticGame.legal_of_mem_support_histDist` — every stage recorded in a
  history reached under a legal profile is itself legal
* `StochasticGame.histDist_normalizedGame_eq_of_isLegalBehaviorProfile` /
  `totalPayoff_normalizedGame_eq_of_isLegalBehaviorProfile` /
  `finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile` —
  deliverable (2): exact trajectory, per-history payoff, and finite-average
  payoff agreement between `G` and `G.normalizedGame` for legal profiles
* `StochasticGame.isεLegalHorizonNash_normalizedGame_iff` /
  `isLegalUniformEquilibriumPayoff_normalizedGame_iff` — deliverable (3): the
  two-directional legal-play transfer
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

variable {ι : Type} (G : StochasticGame ι)
  (Legal : G.State → ∀ i, G.Act i → Prop)
  (hLegal : ∀ s i, ∃ a, Legal s i a)
variable [Fintype ι] [DecidableEq ι]

-- ============================================================================
-- Deliverable (1): the padding construction as a `StochasticGame` value
-- ============================================================================

/-- **The padding construction.**  The state-independent, everywhere-legal
game obtained from `G` and a legality predicate: same states and (already
state-independent) actions, stage payoff and transition given by the
normalized stage data of `ActionLegalityNormalization.lean`, so every action
is legal everywhere and an illegal action carries the payoff and transition
of the fixed legal fallback chosen by `hLegal`. -/
@[reducible] def normalizedGame : StochasticGame ι where
  State := G.State
  Act := G.Act
  stagePayoff := G.normStagePayoff Legal hLegal
  transition := G.normTransition Legal hLegal
  discount := G.discount
  discount_nonneg := G.discount_nonneg
  discount_lt_one := G.discount_lt_one

-- ============================================================================
-- Legal behavior strategies and profiles
-- ============================================================================

/-- A behavior strategy that plays only legal actions, **unconditionally**:
at every history it might be fed, reachable or not, its recommended action is
legal at that history's current state. -/
def IsLegalBehaviorStrategy (i : ι) (τ : G.BehaviorStrategy i) : Prop :=
  ∀ (t : ℕ) (h : G.Hist t) (a : G.Act i), a ∈ (τ t h).support → Legal h.2 i a

/-- A behavior profile all of whose players' strategies are unconditionally
legal. -/
def IsLegalBehaviorProfile (σ : G.BehaviorProfile) : Prop :=
  ∀ i, G.IsLegalBehaviorStrategy Legal i (σ i)

omit [Fintype ι] in
/-- Replacing one player's strategy in a legal profile by another legal
strategy keeps the profile legal. -/
theorem isLegalBehaviorProfile_update {σ : G.BehaviorProfile}
    (hσ : G.IsLegalBehaviorProfile Legal σ) {who : ι} {dev : G.BehaviorStrategy who}
    (hdev : G.IsLegalBehaviorStrategy Legal who dev) :
    G.IsLegalBehaviorProfile Legal (Function.update σ who dev) := by
  intro i
  by_cases hi : i = who
  · subst hi
    simpa using hdev
  · simpa [Function.update_of_ne hi] using hσ i

omit [DecidableEq ι] in
/-- Under an unconditionally legal profile, the joint action drawn at any
history is jointly legal: every player's component is legal, at every
history, regardless of whether that history itself is reachable. -/
theorem jointlyLegal_of_mem_support_stageActionDist {σ : G.BehaviorProfile}
    (hσ : G.IsLegalBehaviorProfile Legal σ) {t : ℕ} {h : G.Hist t}
    {a : G.JointAct} (ha : a ∈ (G.stageActionDist σ h).support) (i : ι) :
    Legal h.2 i (a i) := by
  have h0 : (G.stageActionDist σ h) a ≠ 0 := ha
  unfold stageActionDist at h0
  rw [Math.PMFProduct.pmfPi_apply] at h0
  have hi := (Finset.prod_ne_zero_iff.mp h0) i (Finset.mem_univ i)
  exact hσ i t h (a i) hi

-- ============================================================================
-- Deliverable (2): trajectory-level agreement for legal profiles
-- ============================================================================

omit [DecidableEq ι] in
/-- **Trajectory agreement.**  For an unconditionally legal profile, the
padded game's history distribution is *exactly* the original game's: at every
step the drawn joint action is jointly legal (by
`jointlyLegal_of_mem_support_stageActionDist`), where the padded and original
transition kernels already agree
(`normTransition_of_jointlyLegal`). No coupling or history-projection
argument is needed, because the profile never plays an illegal-looking
action for either game's bookkeeping to disagree about. -/
theorem histDist_normalizedGame_eq_of_isLegalBehaviorProfile
    {σ : G.BehaviorProfile} (hσ : G.IsLegalBehaviorProfile Legal σ)
    (s₀ : G.State) :
    ∀ t : ℕ, (G.normalizedGame Legal hLegal).histDist σ s₀ t = G.histDist σ s₀ t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [(G.normalizedGame Legal hLegal).histDist_succ, G.histDist_succ, ih]
    apply Math.ProbabilityMassFunction.bind_congr_on_support
    intro h _
    apply Math.ProbabilityMassFunction.bind_congr_on_support
    intro a ha
    have hjointly : ∀ i, Legal h.2 i (a i) :=
      G.jointlyLegal_of_mem_support_stageActionDist Legal hσ ha
    have htrans : (G.normalizedGame Legal hLegal).transition h.2 a = G.transition h.2 a := by
      change G.normTransition Legal hLegal h.2 a = G.transition h.2 a
      exact G.normTransition_of_jointlyLegal Legal hLegal hjointly
    rw [htrans]

omit [DecidableEq ι] in
/-- Every stage recorded in a history reached under a legal profile is
itself a jointly legal stage: legality of the past propagates alongside
legality of the newly drawn action at each step. -/
theorem legal_of_mem_support_histDist {σ : G.BehaviorProfile}
    (hσ : G.IsLegalBehaviorProfile Legal σ) (s₀ : G.State) :
    ∀ (t : ℕ) {h : G.Hist t}, h ∈ (G.histDist σ s₀ t).support →
      ∀ (k : Fin t) (i : ι), Legal (h.1 k).1 i ((h.1 k).2 i) := by
  intro t
  induction t with
  | zero => intro _ _ k; exact k.elim0
  | succ t ih =>
    intro h hh k i
    obtain ⟨h', hh', a, ha, s', -, rfl⟩ := (G.mem_support_histDist_succ σ s₀ t h).mp hh
    rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
    · simpa [Fin.snoc_castSucc] using ih hh' k' i
    · simpa [Fin.snoc_last] using
        G.jointlyLegal_of_mem_support_stageActionDist Legal hσ ha i

omit [DecidableEq ι] in
/-- On a history reached under a legal profile, the padded game's total
payoff agrees with the original's: every recorded stage is jointly legal, so
`normStagePayoff_of_jointlyLegal` applies term by term. -/
theorem totalPayoff_normalizedGame_eq_of_isLegalBehaviorProfile
    {σ : G.BehaviorProfile} (hσ : G.IsLegalBehaviorProfile Legal σ)
    (s₀ : G.State) (t : ℕ) (who : ι) {h : G.Hist t}
    (hh : h ∈ (G.histDist σ s₀ t).support) :
    (G.normalizedGame Legal hLegal).totalPayoff who h = G.totalPayoff who h := by
  unfold totalPayoff
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := G.legal_of_mem_support_histDist Legal hσ s₀ t hh k
  change G.normStagePayoff Legal hLegal (h.1 k).1 (h.1 k).2 who =
    G.stagePayoff (h.1 k).1 (h.1 k).2 who
  exact G.normStagePayoff_of_jointlyLegal Legal hLegal hk who

omit [DecidableEq ι] in
/-- **Deliverable (2), payoff form.**  For an unconditionally legal profile,
the padded game's finite-horizon average payoff equals the original game's,
exactly, at every horizon. -/
theorem finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile
    {σ : G.BehaviorProfile} (hσ : G.IsLegalBehaviorProfile Legal σ)
    (s₀ : G.State) (T : ℕ) (who : ι) :
    (G.normalizedGame Legal hLegal).finiteAveragePayoff s₀ T σ who =
      G.finiteAveragePayoff s₀ T σ who := by
  unfold finiteAveragePayoff
  rw [G.histDist_normalizedGame_eq_of_isLegalBehaviorProfile Legal hLegal hσ s₀ T]
  congr 1
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro h hh
  exact G.totalPayoff_normalizedGame_eq_of_isLegalBehaviorProfile Legal hLegal hσ s₀ T who hh

-- ============================================================================
-- Deliverable (3): the two-directional transfer, restricted to legal play
-- ============================================================================

/-- ε-Nash of the `T`-stage game, restricted on both sides to legal play: the
prescribed profile is unconditionally legal, and no unilateral replacement by
a legal strategy gains more than `ε`.  This is the legality-constrained
analogue of `IsεHorizonNash` that the padding reduction can actually
transfer (see the module docstring for what a fully unrestricted version
would additionally need). -/
def IsεLegalHorizonNash (s₀ : G.State) (T : ℕ) (ε : ℝ) (σ : G.BehaviorProfile) : Prop :=
  G.IsLegalBehaviorProfile Legal σ ∧
    ∀ who (dev : G.BehaviorStrategy who), G.IsLegalBehaviorStrategy Legal who dev →
      G.finiteAveragePayoff s₀ T σ who + ε ≥
        G.finiteAveragePayoff s₀ T (Function.update σ who dev) who

/-- **The behaviour-level legal-play transfer, both directions.**  Restricted
to a legal prescribed profile and legal deviations on both sides, ε-Nash of
the `T`-stage game transfers exactly between `G` and its padding: by
deliverable (2), `G` and `G.normalizedGame` agree exactly on the on-path and
every legally-deviated payoff, so the two `IsεLegalHorizonNash` statements are
literally about the same numbers. -/
theorem isεLegalHorizonNash_normalizedGame_iff
    (s₀ : G.State) (T : ℕ) (ε : ℝ) (σ : G.BehaviorProfile) :
    (G.normalizedGame Legal hLegal).IsεLegalHorizonNash Legal s₀ T ε σ ↔
      G.IsεLegalHorizonNash Legal s₀ T ε σ := by
  constructor
  · rintro ⟨hσL, hcap⟩
    refine ⟨hσL, fun who dev hdev => ?_⟩
    have h := hcap who dev hdev
    rwa [G.finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile Legal hLegal
        hσL s₀ T who,
      G.finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile Legal hLegal
        (G.isLegalBehaviorProfile_update Legal hσL hdev) s₀ T who] at h
  · rintro ⟨hσL, hcap⟩
    refine ⟨hσL, fun who dev hdev => ?_⟩
    rw [G.finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile Legal hLegal hσL s₀ T who,
      G.finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile Legal hLegal
        (G.isLegalBehaviorProfile_update Legal hσL hdev) s₀ T who]
    exact hcap who dev hdev

/-- The legal-play uniform equilibrium payoff notion: for every `ε > 0`, a
horizon threshold and a legal profile that is `ε`-Nash against legal
deviations at every longer horizon, with payoff within `ε` of `v`. -/
def IsLegalUniformEquilibriumPayoff (s₀ : G.State) (v : Payoff ι) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ (σ : G.BehaviorProfile) (T₀ : ℕ), ∀ T, T₀ ≤ T →
    G.IsεLegalHorizonNash Legal s₀ T ε σ ∧
      ∀ who, |G.finiteAveragePayoff s₀ T σ who - v who| ≤ ε

/-- **Deliverable (3), uniform-payoff form.**  A legal-play uniform
equilibrium payoff transfers, in both directions, between `G` and its
padding.  This is the restricted analogue of the transfer
`UniformExistenceConjecture.lean`'s scope note anticipates; the module
docstring records precisely what more is needed to reach the unrestricted
statement that file actually wants. -/
theorem isLegalUniformEquilibriumPayoff_normalizedGame_iff
    (s₀ : G.State) (v : Payoff ι) :
    (G.normalizedGame Legal hLegal).IsLegalUniformEquilibriumPayoff Legal s₀ v ↔
      G.IsLegalUniformEquilibriumPayoff Legal s₀ v := by
  constructor
  · intro h ε hε
    obtain ⟨σ, T₀, hσ⟩ := h ε hε
    refine ⟨σ, T₀, fun T hT => ?_⟩
    obtain ⟨hnash, happrox⟩ := hσ T hT
    have hnash' := (G.isεLegalHorizonNash_normalizedGame_iff Legal hLegal s₀ T ε σ).mp hnash
    refine ⟨hnash', fun who => ?_⟩
    have happrox' := happrox who
    rw [G.finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile Legal hLegal
      hnash'.1 s₀ T who] at happrox'
    exact happrox'
  · intro h ε hε
    obtain ⟨σ, T₀, hσ⟩ := h ε hε
    refine ⟨σ, T₀, fun T hT => ?_⟩
    obtain ⟨hnash, happrox⟩ := hσ T hT
    have hnash' := (G.isεLegalHorizonNash_normalizedGame_iff Legal hLegal s₀ T ε σ).mpr hnash
    refine ⟨hnash', fun who => ?_⟩
    rw [G.finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile Legal hLegal
      hnash.1 s₀ T who]
    exact happrox who

end StochasticGame

end GameTheory
