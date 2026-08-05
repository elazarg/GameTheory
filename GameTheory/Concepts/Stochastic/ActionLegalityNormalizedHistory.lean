/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.ActionLegalityBehaviorTransfer

/-!
# Normalized histories: a quotient of `Hist` that cannot see illegal labels

`ActionLegalityBehaviorTransfer.lean` records why the padding reduction's
unrestricted converse does not close by projecting an arbitrary behavior
profile through `normalizeAct`: histories record the *raw* joint action, so
the projected profile's own trajectory is not controlled by the original
profile's cap property, since `normalizeAct` is non-injective and the raw
predecessor of an already-normalized history cannot be recovered. This file
builds the repair that module's docstring identifies as load-bearing: a
strategy space that is *structurally* insensitive to illegal labels, added
additively (`Hist`, `StageRecord`, `histDist` in `Basic.lean` are untouched).

## The quotient, and why a subtype

`normalizeHist` applies `normalizeAct` to every recorded stage of a history
(the current state is untouched, since `Legal` has no opinion about it). Its
image -- equivalently its fixed points (`normalizeHist_idem`), equivalently
the histories every one of whose recorded stages is already jointly legal
(`IsNormalizedHist`) -- is packaged as `NormalizedHist`, a **subtype** of
`Hist t`, not a `Quotient`. Idempotence gives every "same normalization"
class a canonical representative already living in `Hist t` -- its common
normalization -- so a `Quotient` by the corresponding `Setoid` would carry
the same information through an extra layer of `Quotient.mk`/`Quotient.lift`
bookkeeping with no descriptive gain; downstream statements about `histDist`,
`totalPayoff`, etc. stay inside the existing machinery instead of needing it
re-derived for a fresh quotient type.

## What closes

**Deliverable (1).** `NormalizedHist`, with `normalizeHist` as the retraction
`Hist t → Hist t` onto it and `IsNormalizedHist` as the membership predicate;
`normalizeHist_idem` / `isNormalizedHist_normalizeHist` /
`normalizeHist_eq_self_of_isNormalizedHist` show the three descriptions
(image, fixed points, jointly-legal-throughout) agree.

**Deliverable (2), the mathematical heart.** `normHistStep_eq_of_normalizeHist_eq`:
in the padded game, two raw histories with the same normalization induce the
literally *same* one-stage normalized continuation -- not merely the same
continuation in distribution -- for a profile that cannot read the discarded
labels (`IsNormHistInvariantProfile`). Packaged across a whole trajectory as
`map_normalizeHist_histDist_normalizedGame_succ`: the padded game's history
distribution, pushed forward along `normalizeHist`, satisfies the *same*
one-step recursion as `histDist` itself, so the pushed-forward trajectory is
generated entirely by `normHistStep`, never by `σ`'s behaviour off the
normalized-history diagonal. This is unconditional on the profile in one
respect: `totalPayoff_normalizedGame_normalizeHist_eq` shows the padded
game's payoff bookkeeping already cannot see the raw label, for *any*
profile, since `normStagePayoff` applies `normalizeAct` (idempotently) no
matter what is fed to it.

**Deliverable (3).** `IsNormHistInvariant` / `IsNormHistInvariantProfile` are
the "cannot read the discarded labels" profiles; `isNormHistInvariant_iff`
shows invariance is exactly factoring through `normalizeHist`. This is made
literal at the level of `NormalizedHist` itself: `ofNormHistStrategy` /
`toNormHistStrategy` are mutually inverse
(`isNormHistInvariant_iff_exists_ofNormHistStrategy`) between invariant
strategies and strategies whose domain *is* `NormalizedHist`, so an invariant
strategy is, up to this equivalence, literally a strategy of the
legality-constrained game that was never offered a raw label to begin with.
At the profile level, `isLegalBehaviorProfile_and_isNormHistInvariantProfile_iff`
shows a profile is simultaneously legal and invariant iff it arises by
precomposing *some* legal profile of the original game with the
normalization retraction -- the promised correspondence with profiles of the
legality-constrained game.

## What does not close, and exactly why

Deliverable (4) does **not** close, even under the strengthened hypothesis
that every player of the *prescribed* profile is normalized-history-invariant.
`normalizeAct_eq_of_forall_ne` / `normStagePayoff_eq_of_component_eq` /
`normTransition_eq_of_component_eq` show precisely how far the "raw label is
free" mechanism reaches unconditionally: at a *single* stage, replacing one
player's raw action by any other with the same normalization (holding
everyone else's action fixed) changes neither the padded game's stage payoff
nor its transition -- this is the one-shot content underlying the whole
padding reduction, and it needs no invariance hypothesis at all.

It does not extend to a multi-stage Nash cap. `IsεHorizonNash`/
`IsεLegalHorizonNash` quantify the deviator over *whole* behavior strategies,
which are exactly as unrestricted as the profile `σ` whose projection failed
in `ActionLegalityBehaviorTransfer.lean`. Making the *opponents* invariant
does not fix this: bounding an arbitrary deviator `dev`'s payoff by a legal
one still needs a strategy `dev'` matching `dev`'s payoff, and the natural
candidate -- `dev`'s own output normalized, `dev' t h := (dev t h).map
(normalize1 h.2 who)` -- is evaluated, along *its own* induced trajectory, at
raw histories that are already normalized. Recovering the value `dev` would
have taken at the corresponding raw predecessor is exactly the non-injective
inversion `ActionLegalityBehaviorTransfer.lean` already refutes, and *this*
occurrence of the obstruction is not rescued by opponent invariance, because
it lives entirely inside the deviator's own strategy, not in how opponents
react to it.

The mechanism that could plausibly still close this is not a pointwise
projection at all: the one-shot facts above make a deviator's raw label
*payoff-irrelevant* whenever opponents do not react to it, which suggests
`dev`'s achievable payoff should equal some normalized-history-measurable
strategy's payoff via a **disintegration** argument (condition `dev`'s own
realized action on the *normalized* history reached so far, rather than
project pointwise) instead of a pointwise re-evaluation. The repository
already carries generic conditional-probability infrastructure that such an
argument would presumably build on (`Math.ProbabilityMassFunction.pmfCond`,
`condOn`, `iterCondOn`), but assembling it into an actual equal-payoff
witness, verified inductively across every horizon, is a substantial
undertaking of its own and is not attempted here: this file neither proves
deliverable (4) nor exhibits a separating counterexample refuting it.
Deliverable (4) is left **open**, one precise level deeper than where
`ActionLegalityBehaviorTransfer.lean` left it: the obstruction is now
located inside the deviator's own strategy specifically, independent of
whatever the opponents do.

## Main definitions

* `StochasticGame.normalizeStage` / `StochasticGame.normalizeHist` --
  stagewise normalization of a recorded stage / a whole history
* `StochasticGame.IsNormalizedHist` / `StochasticGame.NormalizedHist` --
  deliverable (1): the membership predicate and the subtype
* `StochasticGame.IsNormHistInvariant` /
  `StochasticGame.IsNormHistInvariantProfile` -- deliverable (3): strategies
  and profiles that cannot read the discarded labels
* `StochasticGame.normHistStep` -- the one-step kernel of the normalized
  trajectory process used in deliverable (2)
* `StochasticGame.ofNormHistStrategy` / `StochasticGame.toNormHistStrategy` --
  deliverable (3): the two directions between `NormalizedHist`-domain
  strategies and invariant `BehaviorStrategy`s

## Main results

* `StochasticGame.normalizeHist_idem` -- `normalizeHist` is idempotent
* `StochasticGame.normHistStep_eq_of_normalizeHist_eq` -- deliverable (2)'s
  one-stage heart
* `StochasticGame.map_normalizeHist_histDist_normalizedGame_succ` --
  deliverable (2) across a whole trajectory
* `StochasticGame.totalPayoff_normalizedGame_normalizeHist_eq` -- the padded
  game's payoff bookkeeping is unconditionally normalization-blind
* `StochasticGame.isNormHistInvariant_iff_exists_ofNormHistStrategy` --
  deliverable (3)'s correspondence at the level of `NormalizedHist` itself
* `StochasticGame.isLegalBehaviorProfile_and_isNormHistInvariantProfile_iff`
  -- deliverable (3)'s correspondence at the profile level
* `StochasticGame.normStagePayoff_eq_of_component_eq` /
  `StochasticGame.normTransition_eq_of_component_eq` -- deliverable (4)'s
  one-shot content, and exactly as far as this file gets
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

open Math.Probability

variable {ι : Type} (G : StochasticGame ι)
  (Legal : G.State → ∀ i, G.Act i → Prop)
  (hLegal : ∀ s i, ∃ a, Legal s i a)

-- ============================================================================
-- Deliverable (1): normalized histories
-- ============================================================================

open Classical in
/-- Normalize a single recorded stage: keep the state it was visited at, and
replace the recorded joint action by its normalization there. -/
def normalizeStage (e : G.State × G.JointAct) : G.State × G.JointAct :=
  (e.1, G.normalizeAct Legal hLegal e.1 e.2)

/-- Stagewise normalization of a history: normalize every recorded stage's
joint action against the state it was recorded at; the current state is
untouched (`Legal` has no opinion about states). -/
def normalizeHist {t : ℕ} (h : G.Hist t) : G.Hist t :=
  (fun k => G.normalizeStage Legal hLegal (h.1 k), h.2)

@[simp] theorem normalizeHist_snd {t : ℕ} (h : G.Hist t) :
    (G.normalizeHist Legal hLegal h).2 = h.2 :=
  rfl

/-- The empty history has nothing to normalize. -/
theorem normalizeHist_zero (h : G.Hist 0) : G.normalizeHist Legal hLegal h = h := by
  obtain ⟨rec, s⟩ := h
  refine Prod.ext ?_ rfl
  funext k
  exact k.elim0

/-- `normalizeAct`'s output is always legal: either it kept a legal action,
or it fell back to the legal witness `hLegal` supplies. -/
theorem legal_normalizeAct (s : G.State) (a : G.JointAct) (i : ι) :
    Legal s i (G.normalizeAct Legal hLegal s a i) := by
  unfold normalizeAct
  split_ifs with h
  · exact h
  · exact Classical.choose_spec (hLegal s i)

/-- `normalizeAct` is idempotent: its own output is already jointly legal
(`legal_normalizeAct`), so normalizing it again changes nothing. -/
theorem normalizeAct_idem (s : G.State) (a : G.JointAct) :
    G.normalizeAct Legal hLegal s (G.normalizeAct Legal hLegal s a) =
      G.normalizeAct Legal hLegal s a :=
  G.normalizeAct_of_jointlyLegal Legal hLegal
    (fun i => G.legal_normalizeAct Legal hLegal s a i)

/-- `normalizeStage` is idempotent. -/
theorem normalizeStage_idem (e : G.State × G.JointAct) :
    G.normalizeStage Legal hLegal (G.normalizeStage Legal hLegal e) =
      G.normalizeStage Legal hLegal e := by
  change (e.1, G.normalizeAct Legal hLegal e.1 (G.normalizeAct Legal hLegal e.1 e.2)) =
    (e.1, G.normalizeAct Legal hLegal e.1 e.2)
  rw [G.normalizeAct_idem]

/-- `normalizeHist` is idempotent: normalizing an already-normalized history
changes nothing further. -/
theorem normalizeHist_idem {t : ℕ} (h : G.Hist t) :
    G.normalizeHist Legal hLegal (G.normalizeHist Legal hLegal h) =
      G.normalizeHist Legal hLegal h := by
  obtain ⟨rec, s⟩ := h
  refine Prod.ext ?_ rfl
  funext k
  exact G.normalizeStage_idem Legal hLegal (rec k)

/-- Normalization commutes with appending a completed stage: normalizing the
extended history normalizes the earlier stages exactly as before, and
normalizes the freshly appended stage against its own recorded state. -/
theorem normalizeHist_snoc {t : ℕ} (h : G.Hist t) (a : G.JointAct) (s' : G.State) :
    G.normalizeHist Legal hLegal
        ((Fin.snoc h.1 (h.2, a), s') : G.Hist (t + 1)) =
      (Fin.snoc (G.normalizeHist Legal hLegal h).1
          (h.2, G.normalizeAct Legal hLegal h.2 a), s') := by
  unfold normalizeHist
  refine Prod.ext ?_ rfl
  funext k
  rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | rfl
  · simp [normalizeStage, Fin.snoc_castSucc]
  · simp [normalizeStage, Fin.snoc_last]

/-- A history is **normalized**: every recorded stage's joint action is
already jointly legal there. Equivalently (below) the image, and the fixed
points, of `normalizeHist`. -/
def IsNormalizedHist {t : ℕ} (h : G.Hist t) : Prop :=
  ∀ (k : Fin t) (i : ι), Legal (h.1 k).1 i ((h.1 k).2 i)

/-- Every `normalizeHist`-image history is normalized. -/
theorem isNormalizedHist_normalizeHist {t : ℕ} (h : G.Hist t) :
    G.IsNormalizedHist Legal (G.normalizeHist Legal hLegal h) :=
  fun k i => G.legal_normalizeAct Legal hLegal (h.1 k).1 (h.1 k).2 i

/-- A normalized history is a fixed point of `normalizeHist`: with every
recorded stage already legal, `normalizeAct` changes nothing
(`normalizeAct_of_jointlyLegal`). -/
theorem normalizeHist_eq_self_of_isNormalizedHist {t : ℕ} {h : G.Hist t}
    (hh : G.IsNormalizedHist Legal h) :
    G.normalizeHist Legal hLegal h = h := by
  obtain ⟨rec, s⟩ := h
  refine Prod.ext ?_ rfl
  funext k
  exact Prod.ext rfl (G.normalizeAct_of_jointlyLegal Legal hLegal (hh k))

/-- **Deliverable (1): normalized histories, as a subtype of `Hist t`.**
The image of `Hist t` under stagewise `normalizeAct` -- equivalently the
fixed points of `normalizeHist` (`isNormalizedHist_normalizeHist`,
`normalizeHist_eq_self_of_isNormalizedHist`). A subtype, not a `Quotient`:
see the module docstring for why. -/
def NormalizedHist (t : ℕ) : Type := {h : G.Hist t // G.IsNormalizedHist Legal h}

-- ============================================================================
-- Deliverable (2): trajectory factoring, for label-blind profiles
-- ============================================================================

variable [Fintype ι]

omit [Fintype ι] in
/-- A behavior strategy is **normalized-history-invariant**: it cannot tell
apart two raw histories with the same normalization, i.e. it never reads the
labels normalization discards. -/
def IsNormHistInvariant (i : ι) (τ : G.BehaviorStrategy i) : Prop :=
  ∀ (t : ℕ) (h h' : G.Hist t),
    G.normalizeHist Legal hLegal h = G.normalizeHist Legal hLegal h' → τ t h = τ t h'

omit [Fintype ι] in
/-- A behavior profile all of whose players' strategies are
normalized-history-invariant. -/
def IsNormHistInvariantProfile (σ : G.BehaviorProfile) : Prop :=
  ∀ i, G.IsNormHistInvariant Legal hLegal i (σ i)

omit [Fintype ι] in
/-- Invariance restated as factoring through `normalizeHist`: a strategy is
invariant iff its value at any history equals its value at that history's
normalization. -/
theorem isNormHistInvariant_iff (i : ι) (τ : G.BehaviorStrategy i) :
    G.IsNormHistInvariant Legal hLegal i τ ↔
      ∀ (t : ℕ) (h : G.Hist t), τ t h = τ t (G.normalizeHist Legal hLegal h) := by
  constructor
  · intro hτ t h
    exact hτ t h (G.normalizeHist Legal hLegal h) (G.normalizeHist_idem Legal hLegal h).symm
  · intro hτ t h h' he
    rw [hτ t h, hτ t h', he]

omit [Fintype ι] in
/-- An invariant strategy's value at a raw history equals its value at that
history's normalization. -/
theorem IsNormHistInvariant.apply_normalizeHist {i : ι} {τ : G.BehaviorStrategy i}
    (hτ : G.IsNormHistInvariant Legal hLegal i τ) {t : ℕ} (h : G.Hist t) :
    τ t (G.normalizeHist Legal hLegal h) = τ t h :=
  hτ t (G.normalizeHist Legal hLegal h) h (G.normalizeHist_idem Legal hLegal h)

/-- For an invariant profile, the joint mixed-action distribution at a raw
history equals the one at that history's normalization. -/
theorem stageActionDist_eq_of_normalizeHist_eq
    {σ : G.BehaviorProfile} (hσ : G.IsNormHistInvariantProfile Legal hLegal σ)
    {t : ℕ} {h h' : G.Hist t}
    (he : G.normalizeHist Legal hLegal h = G.normalizeHist Legal hLegal h') :
    (G.normalizedGame Legal hLegal).stageActionDist σ h =
      (G.normalizedGame Legal hLegal).stageActionDist σ h' := by
  unfold stageActionDist
  congr 1
  funext i
  exact hσ i t h h' he

open Classical in
/-- One padded-game stage from `h`, recorded and immediately normalized: the
one-step kernel of the normalized-history process that deliverable (2) shows
the padded game's `histDist`, pushed forward along `normalizeHist`, actually
follows. -/
def normHistStep (σ : G.BehaviorProfile) {t : ℕ} (h : G.Hist t) :
    PMF (G.Hist (t + 1)) :=
  ((G.normalizedGame Legal hLegal).stageActionDist σ h).bind fun a =>
    ((G.normalizedGame Legal hLegal).transition h.2 a).bind fun s' =>
      PMF.pure (G.normalizeHist Legal hLegal (Fin.snoc h.1 (h.2, a), s'))

/-- **Deliverable (2), the mathematical heart.** Two raw histories with the
same normalization carry the same continuation behaviour, for a profile that
cannot read the discarded labels: `normHistStep` does not merely agree in
distribution on `h` and `h'`, it is the *same* value, because normalization
keeps the current state (`h.2 = h'.2`), `stageActionDist` already agrees by
invariance, and `normalizeHist_snoc` shows the freshly recorded, normalized
continuation depends on `h` only through `(normalizeHist h).1` and `h.2`. -/
theorem normHistStep_eq_of_normalizeHist_eq
    {σ : G.BehaviorProfile} (hσ : G.IsNormHistInvariantProfile Legal hLegal σ)
    {t : ℕ} {h h' : G.Hist t}
    (he : G.normalizeHist Legal hLegal h = G.normalizeHist Legal hLegal h') :
    G.normHistStep Legal hLegal σ h = G.normHistStep Legal hLegal σ h' := by
  have hstate : h.2 = h'.2 := by
    have h2 := congrArg Prod.snd he
    simpa using h2
  have hrec : (G.normalizeHist Legal hLegal h).1 = (G.normalizeHist Legal hLegal h').1 :=
    congrArg Prod.fst he
  have expand : ∀ g : G.Hist t, G.normHistStep Legal hLegal σ g =
      ((G.normalizedGame Legal hLegal).stageActionDist σ g).bind fun a =>
        ((G.normalizedGame Legal hLegal).transition g.2 a).bind fun s' =>
          PMF.pure ((Fin.snoc (G.normalizeHist Legal hLegal g).1
            (g.2, G.normalizeAct Legal hLegal g.2 a), s') : G.Hist (t + 1)) := by
    intro g
    unfold normHistStep
    congr 1
    funext a
    congr 1
    funext s'
    rw [G.normalizeHist_snoc]
  rw [expand h, expand h', G.stageActionDist_eq_of_normalizeHist_eq Legal hLegal hσ he,
    hstate, hrec]

/-- `normHistStep` from a history equals `normHistStep` from its
normalization: an instance of `normHistStep_eq_of_normalizeHist_eq` via
idempotence. -/
theorem normHistStep_normalizeHist
    {σ : G.BehaviorProfile} (hσ : G.IsNormHistInvariantProfile Legal hLegal σ)
    {t : ℕ} (h : G.Hist t) :
    G.normHistStep Legal hLegal σ (G.normalizeHist Legal hLegal h) =
      G.normHistStep Legal hLegal σ h :=
  G.normHistStep_eq_of_normalizeHist_eq Legal hLegal hσ (G.normalizeHist_idem Legal hLegal h)

/-- The base case of deliverable (2): the empty history is its own
normalization, so there is nothing to push forward. -/
theorem map_normalizeHist_histDist_normalizedGame_zero
    (σ : G.BehaviorProfile) (s₀ : G.State) :
    PMF.map (G.normalizeHist Legal hLegal)
        ((G.normalizedGame Legal hLegal).histDist σ s₀ 0) =
      (G.normalizedGame Legal hLegal).histDist σ s₀ 0 := by
  rw [histDist_zero, PMF.pure_map, G.normalizeHist_zero]

/-- **Deliverable (2), packaged across a trajectory.** The padded game's
history distribution, pushed forward along `normalizeHist`, satisfies
exactly the same one-step recursion as `histDist` itself: it is generated by
`normHistStep`, never by `σ`'s behaviour off the normalized-history
diagonal. -/
theorem map_normalizeHist_histDist_normalizedGame_succ
    {σ : G.BehaviorProfile} (hσ : G.IsNormHistInvariantProfile Legal hLegal σ)
    (s₀ : G.State) (t : ℕ) :
    PMF.map (G.normalizeHist Legal hLegal)
        ((G.normalizedGame Legal hLegal).histDist σ s₀ (t + 1)) =
      (PMF.map (G.normalizeHist Legal hLegal)
          ((G.normalizedGame Legal hLegal).histDist σ s₀ t)).bind
        (G.normHistStep Legal hLegal σ) := by
  rw [(G.normalizedGame Legal hLegal).histDist_succ, PMF.map_bind]
  have hpt : (fun h : G.Hist t =>
      PMF.map (G.normalizeHist Legal hLegal)
        (((G.normalizedGame Legal hLegal).stageActionDist σ h).bind fun a =>
          ((G.normalizedGame Legal hLegal).transition h.2 a).bind fun s' =>
            PMF.pure ((Fin.snoc h.1 (h.2, a), s') : G.Hist (t + 1)))) =
      G.normHistStep Legal hLegal σ ∘ G.normalizeHist Legal hLegal := by
    funext h
    change PMF.map (G.normalizeHist Legal hLegal)
        (((G.normalizedGame Legal hLegal).stageActionDist σ h).bind fun a =>
          ((G.normalizedGame Legal hLegal).transition h.2 a).bind fun s' =>
            PMF.pure ((Fin.snoc h.1 (h.2, a), s') : G.Hist (t + 1))) =
      G.normHistStep Legal hLegal σ (G.normalizeHist Legal hLegal h)
    rw [G.normHistStep_normalizeHist Legal hLegal hσ h]
    unfold normHistStep
    rw [PMF.map_bind]
    congr 1
    funext a
    rw [PMF.map_bind]
    congr 1
    funext s'
    exact PMF.pure_map _ _
  rw [hpt]
  exact (PMF.bind_map ((G.normalizedGame Legal hLegal).histDist σ s₀ t)
    (G.normalizeHist Legal hLegal) (G.normHistStep Legal hLegal σ)).symm

omit [Fintype ι] in
/-- **Structural, unconditional on the profile.** The padded game's
`totalPayoff` cannot distinguish a history from its normalization:
`normStagePayoff` already applies `normalizeAct`, and `normalizeAct` is
idempotent, so renormalizing every recorded stage changes nothing it
contributes to any player's total. -/
theorem totalPayoff_normalizedGame_normalizeHist_eq (who : ι) {t : ℕ} (h : G.Hist t) :
    (G.normalizedGame Legal hLegal).totalPayoff who (G.normalizeHist Legal hLegal h) =
      (G.normalizedGame Legal hLegal).totalPayoff who h := by
  unfold totalPayoff
  refine Finset.sum_congr rfl fun k _ => ?_
  change G.normStagePayoff Legal hLegal (h.1 k).1
      (G.normalizeAct Legal hLegal (h.1 k).1 (h.1 k).2) who =
    G.normStagePayoff Legal hLegal (h.1 k).1 (h.1 k).2 who
  unfold normStagePayoff
  rw [G.normalizeAct_idem]

/-- The padded game's finite-horizon average payoff, for *any* profile, is
computable from the pushed-forward, normalized-history-only trajectory: the
payoff bookkeeping is always normalization-blind, whether or not the profile
generating the trajectory is. -/
theorem finiteAveragePayoff_normalizedGame_eq_expect_map_normalizeHist
    (σ : G.BehaviorProfile) (s₀ : G.State) (T : ℕ) (who : ι) :
    (G.normalizedGame Legal hLegal).finiteAveragePayoff s₀ T σ who =
      (T : ℝ)⁻¹ * expect
        (PMF.map (G.normalizeHist Legal hLegal)
          ((G.normalizedGame Legal hLegal).histDist σ s₀ T))
        ((G.normalizedGame Legal hLegal).totalPayoff who) := by
  unfold finiteAveragePayoff
  rw [expect_map]
  congr 1
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro h _
  exact (G.totalPayoff_normalizedGame_normalizeHist_eq Legal hLegal who h).symm

-- ============================================================================
-- Deliverable (3): the correspondence with legality-constrained profiles
-- ============================================================================

omit [Fintype ι] in
/-- Lift a strategy defined directly on `NormalizedHist` -- one that cannot
even be *handed* a raw history carrying discarded labels, since its domain
already excludes them -- to a full `BehaviorStrategy`: feed it the
normalization of whatever raw history it is handed. -/
def ofNormHistStrategy {i : ι} (τ : ∀ t : ℕ, G.NormalizedHist Legal t → PMF (G.Act i)) :
    G.BehaviorStrategy i :=
  fun t h => τ t ⟨G.normalizeHist Legal hLegal h, G.isNormalizedHist_normalizeHist Legal hLegal h⟩

omit [Fintype ι] in
/-- The other direction: restrict a full strategy to `NormalizedHist`, simply
by forgetting that its input is already normalized. -/
def toNormHistStrategy {i : ι} (τ : G.BehaviorStrategy i) :
    ∀ t : ℕ, G.NormalizedHist Legal t → PMF (G.Act i) :=
  fun t hn => τ t hn.1

omit [Fintype ι] in
/-- Every strategy obtained by `ofNormHistStrategy` is automatically
normalized-history-invariant: it never even sees a raw history, only its
normalization. -/
theorem isNormHistInvariant_ofNormHistStrategy {i : ι}
    (τ : ∀ t : ℕ, G.NormalizedHist Legal t → PMF (G.Act i)) :
    G.IsNormHistInvariant Legal hLegal i (G.ofNormHistStrategy Legal hLegal τ) :=
  fun _ _ _ he => congrArg (τ _) (Subtype.ext he)

omit [Fintype ι] in
/-- Restricting an invariant strategy to `NormalizedHist` and lifting it back
recovers the original strategy: `apply_normalizeHist` is exactly the missing
step. -/
theorem ofNormHistStrategy_toNormHistStrategy {i : ι} {τ : G.BehaviorStrategy i}
    (hτ : G.IsNormHistInvariant Legal hLegal i τ) :
    G.ofNormHistStrategy Legal hLegal (G.toNormHistStrategy Legal τ) = τ := by
  funext t h
  exact IsNormHistInvariant.apply_normalizeHist G Legal hLegal hτ h

omit [Fintype ι] in
/-- Lifting a `NormalizedHist`-domain strategy and restricting it back
recovers the original: on a normalized history, `normalizeHist` is the
identity (`normalizeHist_eq_self_of_isNormalizedHist`). -/
theorem toNormHistStrategy_ofNormHistStrategy {i : ι}
    (τ : ∀ t : ℕ, G.NormalizedHist Legal t → PMF (G.Act i)) :
    G.toNormHistStrategy Legal (G.ofNormHistStrategy Legal hLegal τ) = τ := by
  funext t hn
  obtain ⟨h, hh⟩ := hn
  change τ t ⟨G.normalizeHist Legal hLegal h, G.isNormalizedHist_normalizeHist Legal hLegal h⟩ =
    τ t ⟨h, hh⟩
  congr 1
  exact Subtype.ext (G.normalizeHist_eq_self_of_isNormalizedHist Legal hLegal hh)

omit [Fintype ι] in
/-- **Deliverable (3), per strategy: normalized-history-measurable profiles
correspond exactly to invariant behavior strategies.** `ofNormHistStrategy`
and `toNormHistStrategy` are mutually inverse on, respectively, all of
`∀ t, NormalizedHist t → PMF (Act i)` and the invariant strategies -- an
honest equivalence, not merely a one-sided containment. -/
theorem isNormHistInvariant_iff_exists_ofNormHistStrategy {i : ι} (τ : G.BehaviorStrategy i) :
    G.IsNormHistInvariant Legal hLegal i τ ↔
      ∃ τ' : ∀ t : ℕ, G.NormalizedHist Legal t → PMF (G.Act i),
        τ = G.ofNormHistStrategy Legal hLegal τ' := by
  constructor
  · intro hτ
    exact ⟨G.toNormHistStrategy Legal τ,
      (G.ofNormHistStrategy_toNormHistStrategy Legal hLegal hτ).symm⟩
  · rintro ⟨τ', rfl⟩
    exact G.isNormHistInvariant_ofNormHistStrategy Legal hLegal τ'

omit [Fintype ι] in
/-- **Deliverable (3): normalized-history-measurable, legal profiles
correspond to profiles of the legality-constrained game.** Precomposing any
legal behavior profile with `normalizeHist` yields a legal,
normalized-history-invariant profile (legality is preserved since the output
at the normalized history is untouched; invariance is automatic since
`normalizeHist` is idempotent); conversely, every legal invariant profile
already arises this way, from itself. -/
theorem isLegalBehaviorProfile_and_isNormHistInvariantProfile_iff
    (σ : G.BehaviorProfile) :
    (G.IsLegalBehaviorProfile Legal σ ∧ G.IsNormHistInvariantProfile Legal hLegal σ) ↔
      ∃ ρ : G.BehaviorProfile, G.IsLegalBehaviorProfile Legal ρ ∧
        σ = fun i t h => ρ i t (G.normalizeHist Legal hLegal h) := by
  constructor
  · rintro ⟨hleg, hinv⟩
    refine ⟨σ, hleg, ?_⟩
    funext i t h
    exact (IsNormHistInvariant.apply_normalizeHist G Legal hLegal (hinv i) h).symm
  · rintro ⟨ρ, hleg, rfl⟩
    refine ⟨fun i t h a ha => hleg i t (G.normalizeHist Legal hLegal h) a ha, fun i t h h' he => ?_⟩
    change ρ i t (G.normalizeHist Legal hLegal h) = ρ i t (G.normalizeHist Legal hLegal h')
    rw [he]

-- ============================================================================
-- Deliverable (4): the one-shot content, and exactly where it stops
-- ============================================================================

omit [Fintype ι] in
open Classical in
/-- **The one-shot content of the padding reduction, made precise at the
joint-action level.** Changing a single player's raw action, while keeping
its normalization fixed and every other player's action fixed, does not
change the normalized joint action at all: `normalizeAct` acts
componentwise (`normalizeAct s a i` depends only on `a i`), so agreement
elsewhere plus agreement of the normalized `who`-component forces agreement
of the whole normalized profile. This is exactly the fact that would make a
raw illegal label "free" if nothing downstream could tell two normalizations
apart -- it needs no invariance hypothesis, and it is exactly as far as the
one-shot mechanism reaches (see the module docstring for why it does not
extend to a multi-stage Nash cap). -/
theorem normalizeAct_eq_of_forall_ne (s : G.State) (a a' : G.JointAct) (who : ι)
    (hother : ∀ i, i ≠ who → a i = a' i)
    (hself : G.normalizeAct Legal hLegal s a who = G.normalizeAct Legal hLegal s a' who) :
    G.normalizeAct Legal hLegal s a = G.normalizeAct Legal hLegal s a' := by
  funext i
  by_cases hi : i = who
  · subst hi
    exact hself
  · unfold normalizeAct
    rw [hother i hi]

omit [Fintype ι] in
/-- The padded game's stage payoff inherits the one-shot, componentwise
insensitivity of `normalizeAct_eq_of_forall_ne`. -/
theorem normStagePayoff_eq_of_component_eq (s : G.State) (a a' : G.JointAct) (who : ι)
    (hother : ∀ i, i ≠ who → a i = a' i)
    (hself : G.normalizeAct Legal hLegal s a who = G.normalizeAct Legal hLegal s a' who)
    (i : ι) :
    G.normStagePayoff Legal hLegal s a i = G.normStagePayoff Legal hLegal s a' i := by
  unfold normStagePayoff
  rw [G.normalizeAct_eq_of_forall_ne Legal hLegal s a a' who hother hself]

omit [Fintype ι] in
/-- The padded game's transition kernel inherits the same one-shot,
componentwise insensitivity. -/
theorem normTransition_eq_of_component_eq (s : G.State) (a a' : G.JointAct) (who : ι)
    (hother : ∀ i, i ≠ who → a i = a' i)
    (hself : G.normalizeAct Legal hLegal s a who = G.normalizeAct Legal hLegal s a' who) :
    G.normTransition Legal hLegal s a = G.normTransition Legal hLegal s a' := by
  unfold normTransition
  rw [G.normalizeAct_eq_of_forall_ne Legal hLegal s a a' who hother hself]

end StochasticGame

end GameTheory
