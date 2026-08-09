/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.Transform.ActionLegality.NormalizedHistory

/-!
# Disintegrating a deviator against its own normalized-history marginal

`ActionLegalityNormalizedHistory.lean` localizes the last obstruction to the
padding reduction's unrestricted converse (`LEAN-F0-1`) inside the deviator's
own strategy: an arbitrary deviator `dev` may read raw, discarded labels, and
projecting its output pointwise fails because the projected profile's own
induced trajectory only ever visits already-normalized histories, at which
`dev`'s raw value is unrecoverable. That file names the mechanism that could
still close it -- disintegration: condition `dev`'s *realized* action on the
normalized history reached so far, instead of re-evaluating `dev` at the
wrong (already-normalized) input. This file builds it.

## The construction

Fix a background profile `ρ` (played by every player other than the deviator
`who`) and an arbitrary, unrestricted `dev : G.BehaviorStrategy who`. At time
`t`, `jointDevDist` is the joint law of the raw history reached under
`Function.update ρ who dev` and `dev`'s own realized action there.
`devMarginal` disintegrates this joint law against the normalized history --
using `Math.ProbabilityMassFunction.condOn`, whose own null-mass fallback
(return the law unconditioned) makes this well-defined at *every* normalized
history, including ones the trajectory never reaches. `disintegratedDev`
additionally collapses any residual illegal mass onto a fixed legal fallback
(`legalizeAct`), and `devPrime` lifts the result to a full `BehaviorStrategy`
via `ofNormHistStrategy`, which is automatically label-blind.

## What closes

**Deliverable (1).** `devPrime`, well-defined at every normalized history
including probability-zero ones, with no side condition beyond the section's
finiteness hypotheses (needed for `condOn`'s disintegration identities, not
for the construction itself).

**Deliverable (2).** `isNormHistInvariant_devPrime` (label-blindness, free
from `ofNormHistStrategy`) and `isLegalBehaviorStrategy_devPrime` (legality,
from `legalizeAct`'s range).

**Deliverable (3), for a label-blind *and legal* background profile `ρ`.**
`histDist_devPrime_eq_map_normalizeHist_histDist_dev`: `devPrime`'s own raw
trajectory equals `dev`'s trajectory pushed forward along `normalizeHist`,
proved by induction on the horizon. The inductive step assembles
`Math.ProbabilityMassFunction.bind_pushforward_condOn` (the disintegration
identity for a `condOn`-conditioned bind), `pmfPi_update_bind` (the "Fubini"
step isolating the deviator's own coordinate), and the crux lemma
`pmfPi_update_bind_normOneStage_eq_legalizeAct` (the deviator's raw,
possibly-illegal action is invisible one step later, since the padded game's
transition and the outer `normalizeHist` both renormalize it). Since the
padded game's payoff bookkeeping is already normalization-blind for any
profile (`totalPayoff_normalizedGame_normalizeHist_eq`), the trajectory
equality gives *exact* payoff agreement (`finiteAveragePayoff_devPrime_eq`)
at every horizon and for every player -- strictly more than the "at least"
the row asks for.

**Deliverable (4), conditionally, in two parts.**
`isεLegalHorizonNash_of_isεHorizonNash_normalizedGame` transfers a
label-blind legal `ρ`'s *unrestricted*-deviation padded-game cap to
`G.IsεLegalHorizonNash` -- but, reported honestly, this direction turns out
**not** to need `devPrime` at all: an already-legal deviator's padded- and
original-game payoffs already coincide, so the unrestricted hypothesis
instantiated directly at that deviator suffices. `devPrime` earns its keep in
the second, strictly stronger part:
`finiteAveragePayoff_devPrime_le_of_isεHorizonNash_normalizedGame` shows that
for a **literally arbitrary** (unrestricted, possibly illegal, possibly
raw-label-reading) deviator `dev` -- no restriction on the deviator class
anywhere in the argument -- its *disintegrated, legal* counterpart `devPrime`
is capped in the **original** game's own bookkeeping. This says the padded
game's unrestricted cap is actually achieved by a genuine legal strategy of
`G`, for every unrestricted deviation, not only already-legal ones.
`isLegalUniformEquilibriumPayoff_of_witness` assembles both into the
row's target shape: a label-blind, legal, per-accuracy witness of the padded
game's uniform equilibrium payoff yields `G.IsLegalUniformEquilibriumPayoff`.

## What does not close, and exactly where

Deliverable (4) as stated in the pipeline is unconditional: an arbitrary
*unrestricted* witness of `(G.normalizedGame ...).IsUniformEquilibriumPayoff`
-- not already known label-blind or legal -- should yield a legal witness of
`G.IsLegalUniformEquilibriumPayoff`. That is **not** established here, and
the reason is localized precisely, one level past where
`ActionLegalityNormalizedHistory.lean` left it.

The inductive argument behind deliverable (3) needs the *background* profile
`ρ` -- every player other than the deviator being disintegrated -- to already
be normalized-history-invariant: `stageActionDist_eq_of_normalizeHist_eq`
supplies the one identity that lets the whole one-stage kernel be rewritten as
a function of the normalized history alone, and it has that invariance
hypothesis on the *whole* profile it is applied to. Disintegrating one
player's strategy while every other coordinate is held at an unrestricted,
possibly non-invariant profile does not repair this: the induction's "the
one-stage kernel depends on the raw history only through its normalization"
step fails exactly at the coordinates that were not disintegrated, since nothing
constrains what they leak about the discarded labels. So obtaining an
invariant-and-legal witness *from an arbitrary unrestricted one* would need
disintegrating *every* coordinate simultaneously against a background that is
itself already invariant -- circular as stated -- confirming, with a precise
technical reason rather than only the non-convexity argument already on
record, that this route is closed: restricting only the prescribed profile
does kill the channel, but the converse must transport an arbitrary
padded-game equilibrium, while invariance transports only invariant ones.
This file does not attempt to route around that; deliverable (4) here is stated
honestly as *conditional* on a label-blind, legal `ρ`, which the row already
flags as a permitted strengthening of the *prescribed* profile only.

## Side conditions

`condOn`'s clean disintegration identities
(`Math.ProbabilityMassFunction.bind_pushforward_condOn`) need `Finite`
carriers. The section accordingly assumes `Finite G.State` and
`Finite (G.Act i)` for every `i`, on top of the ambient `Fintype ι`; these are
not used anywhere in `ActionLegalityNormalizedHistory.lean` and are recorded
here as the side condition this file specifically needs.

## Main definitions

* `StochasticGame.legalizeAct` -- the single-player specialization of
  `normalizeAct`'s componentwise formula
* `StochasticGame.jointDevDist` -- the joint law of the raw history and the
  deviator's realized action there
* `StochasticGame.devMarginal` / `StochasticGame.disintegratedDev` --
  deliverable (1): the disintegrated, legalized conditional law
* `StochasticGame.devPrime` -- deliverable (1), lifted to a full
  `BehaviorStrategy`

## Main results

* `StochasticGame.isNormHistInvariant_devPrime` /
  `StochasticGame.isLegalBehaviorStrategy_devPrime` -- deliverable (2)
* `StochasticGame.histDist_devPrime_eq_map_normalizeHist_histDist_dev` /
  `StochasticGame.finiteAveragePayoff_devPrime_eq` -- deliverable (3)
* `StochasticGame.isεLegalHorizonNash_of_isεHorizonNash_normalizedGame` /
  `StochasticGame.finiteAveragePayoff_devPrime_le_of_isεHorizonNash_normalizedGame` /
  `StochasticGame.isLegalUniformEquilibriumPayoff_of_witness` --
  deliverable (4), conditional on a label-blind legal background profile
-/

noncomputable section

namespace GameTheory

namespace StochasticGame

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} (G : StochasticGame ι)
  (Legal : G.State → ∀ i, G.Act i → Prop)
  (hLegal : ∀ s i, ∃ a, Legal s i a)

-- ============================================================================
-- A single-player specialization of `normalizeAct`
-- ============================================================================

open Classical in
/-- Replace a single player's action by a fixed legal fallback if it is not
already legal at the given state: the single-coordinate content of
`normalizeAct`'s componentwise formula, usable without first assembling a
full joint action. -/
def legalizeAct (s : G.State) (i : ι) (a : G.Act i) : G.Act i :=
  if Legal s i a then a else Classical.choose (hLegal s i)

open Classical in
/-- `legalizeAct`'s output is always legal. -/
theorem legal_legalizeAct (s : G.State) (i : ι) (a : G.Act i) :
    Legal s i (G.legalizeAct Legal hLegal s i a) := by
  unfold legalizeAct
  split_ifs with h
  · exact h
  · exact Classical.choose_spec (hLegal s i)

/-- `normalizeAct`'s componentwise formula is literally `legalizeAct` applied
to that component. -/
theorem normalizeAct_apply_eq_legalizeAct (s : G.State) (a : ∀ i, G.Act i) (i : ι) :
    G.normalizeAct Legal hLegal s a i = G.legalizeAct Legal hLegal s i (a i) :=
  rfl

open Classical in
/-- `legalizeAct` fixes actions that are already legal. -/
theorem legalizeAct_of_legal {s : G.State} {i : ι} {a : G.Act i} (h : Legal s i a) :
    G.legalizeAct Legal hLegal s i a = a := by
  unfold legalizeAct
  rw [if_pos h]

/-- `legalizeAct` is idempotent: its own output is already legal
(`legal_legalizeAct`), so legalizing it again changes nothing. -/
theorem legalizeAct_idem (s : G.State) (i : ι) (a : G.Act i) :
    G.legalizeAct Legal hLegal s i (G.legalizeAct Legal hLegal s i a) =
      G.legalizeAct Legal hLegal s i a :=
  G.legalizeAct_of_legal Legal hLegal (G.legal_legalizeAct Legal hLegal s i a)

-- ============================================================================
-- Deliverable (1): the disintegrated deviation
-- ============================================================================

variable [Fintype ι] [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)]

/-- The joint law, at time `t`, of the raw history reached under
`Function.update ρ who dev` and the deviator `dev`'s own realized action
there. -/
def jointDevDist (ρ : G.BehaviorProfile) (who : ι) (dev : G.BehaviorStrategy who)
    (s₀ : G.State) (t : ℕ) : PMF (G.Hist t × G.Act who) :=
  ((G.normalizedGame Legal hLegal).histDist (Function.update ρ who dev) s₀ t).bind
    fun h => (dev t h).map fun a => (h, a)

/-- The deviator's disintegrated (but not yet legalized) marginal action law:
the law of `dev`'s realized action conditioned on the raw history at time `t`
normalizing to `hn`. `condOn`'s own null-mass fallback (return the law
unconditioned) makes this well-defined at every normalized history, including
ones of probability zero. -/
def devMarginal (ρ : G.BehaviorProfile) (who : ι) (dev : G.BehaviorStrategy who)
    (s₀ : G.State) (t : ℕ) (hn : G.NormalizedHist Legal t) : PMF (G.Act who) :=
  PMF.map Prod.snd
    (condOn (G.jointDevDist Legal hLegal ρ who dev s₀ t)
      (fun p => G.normalizeHist Legal hLegal p.1) hn.1)

/-- **Deliverable (1).** The disintegrated deviation: `devMarginal`, with any
residual illegal mass collapsed onto a fixed legal fallback via
`legalizeAct`, so the result is always legal (deliverable (2)). -/
def disintegratedDev (ρ : G.BehaviorProfile) (who : ι) (dev : G.BehaviorStrategy who)
    (s₀ : G.State) : ∀ t : ℕ, G.NormalizedHist Legal t → PMF (G.Act who) :=
  fun t hn =>
    (G.devMarginal Legal hLegal ρ who dev s₀ t hn).map
      (G.legalizeAct Legal hLegal hn.1.2 who)

/-- **Deliverable (1), lifted to a full behavior strategy.** Label-blind by
construction: `ofNormHistStrategy`'s domain is already `NormalizedHist`, so
`devPrime` never even sees the raw labels `dev` might read. -/
def devPrime (ρ : G.BehaviorProfile) (who : ι) (dev : G.BehaviorStrategy who)
    (s₀ : G.State) : G.BehaviorStrategy who :=
  G.ofNormHistStrategy Legal hLegal (G.disintegratedDev Legal hLegal ρ who dev s₀)

-- ============================================================================
-- Deliverable (2): label-blind and legal
-- ============================================================================

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- **Deliverable (2), label-blindness.** Immediate from `ofNormHistStrategy`:
`devPrime` only ever consumes the normalized history. -/
theorem isNormHistInvariant_devPrime (ρ : G.BehaviorProfile) (who : ι)
    (dev : G.BehaviorStrategy who) (s₀ : G.State) :
    G.IsNormHistInvariant Legal hLegal who (G.devPrime Legal hLegal ρ who dev s₀) :=
  G.isNormHistInvariant_ofNormHistStrategy Legal hLegal _

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- **Deliverable (2), legality.** `devPrime`'s output always factors through
`legalizeAct`, whose range is legal (`legal_legalizeAct`) at the fed
history's own state (`normalizeHist` does not touch the state,
`normalizeHist_snd`). -/
theorem isLegalBehaviorStrategy_devPrime (ρ : G.BehaviorProfile) (who : ι)
    (dev : G.BehaviorStrategy who) (s₀ : G.State) :
    G.IsLegalBehaviorStrategy Legal who (G.devPrime Legal hLegal ρ who dev s₀) := by
  intro t h a ha
  unfold devPrime ofNormHistStrategy disintegratedDev at ha
  simp only [PMF.mem_support_map_iff] at ha
  obtain ⟨b, -, rfl⟩ := ha
  have hleg := G.legal_legalizeAct Legal hLegal
    (G.normalizeHist Legal hLegal h).2 who b
  rwa [G.normalizeHist_snd] at hleg

-- ============================================================================
-- Deliverable (3): payoff agreement against a label-blind, legal background
-- ============================================================================

open Math.PMFProduct

/-- Sampling a coordinate mixture and immediately overwriting that same
coordinate with a fixed value discards the sample: the joint law is the same
as fixing that coordinate directly, for any downstream use `F`. The
"disintegrate the deviator's own coordinate" identity used below is really
this fact plus `pmfPi_update_bind` (the deviator's coordinate is sampled
first, and everything else only cares about its normalization). -/
theorem pmfPi_bind_update_const {A : ι → Type} (σ : ∀ i, PMF (A i)) (j : ι)
    (d : PMF (A j)) (x : A j) {β : Type} (F : (∀ i, A i) → PMF β) :
    (pmfPi (Function.update σ j d)).bind (fun act => F (Function.update act j x)) =
      (pmfPi (Function.update σ j (PMF.pure x))).bind F := by
  have hpure :
      (pmfPi (Function.update σ j d)).bind
          (fun act => PMF.pure (Function.update act j x)) =
        pmfPi (Function.update σ j (PMF.pure x)) := by
    rw [pmfPi_bind_update_pure (Function.update σ j d) j x, Function.update_idem]
  have hstep : (pmfPi (Function.update σ j d)).bind (fun act => F (Function.update act j x)) =
      ((pmfPi (Function.update σ j d)).bind
        (fun act => PMF.pure (Function.update act j x))).bind F := by
    rw [PMF.bind_bind]
    simp
  rw [hstep, hpure]

/-- One padded-game stage from a *normalized* history `h`, given a raw joint
action `a` played there, immediately renormalized. Both `dev`'s and
`devPrime`'s one-stage continuations reduce to this, driven by different laws
for the joint action. -/
def normOneStage {t : ℕ} (h : G.Hist t) (a : G.JointAct) : PMF (G.Hist (t + 1)) :=
  PMF.map (G.normalizeHist Legal hLegal)
    (((G.normalizedGame Legal hLegal).transition h.2 a).bind fun s' =>
      PMF.pure ((Fin.snoc h.1 (h.2, a), s') : G.Hist (t + 1)))

omit [Fintype ι] [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- Replacing player `who`'s raw action by any other with the same
`legalizeAct` value, holding every other player's action fixed, does not
change `normOneStage`. The single-coordinate specialization of
`normalizeAct_eq_of_forall_ne` (the one-shot content of the padding
reduction), chained through the transition kernel and `normalizeHist_snoc`;
no invariance hypothesis is needed here, matching the module docstring of
`ActionLegalityNormalizedHistory`. -/
theorem normOneStage_eq_of_component_eq
    {t : ℕ} (h : G.Hist t) (a a' : G.JointAct) (who : ι)
    (hother : ∀ i, i ≠ who → a i = a' i)
    (hself : G.legalizeAct Legal hLegal h.2 who (a who) =
      G.legalizeAct Legal hLegal h.2 who (a' who)) :
    G.normOneStage Legal hLegal h a = G.normOneStage Legal hLegal h a' := by
  have hself' : G.normalizeAct Legal hLegal h.2 a who =
      G.normalizeAct Legal hLegal h.2 a' who := by
    rw [G.normalizeAct_apply_eq_legalizeAct, G.normalizeAct_apply_eq_legalizeAct]
    exact hself
  have hnorm : G.normalizeAct Legal hLegal h.2 a = G.normalizeAct Legal hLegal h.2 a' :=
    G.normalizeAct_eq_of_forall_ne Legal hLegal h.2 a a' who hother hself'
  have htrans : (G.normalizedGame Legal hLegal).transition h.2 a =
      (G.normalizedGame Legal hLegal).transition h.2 a' :=
    G.normTransition_eq_of_component_eq Legal hLegal h.2 a a' who hother hself'
  unfold normOneStage
  rw [PMF.map_bind, PMF.map_bind, htrans]
  congr 1
  funext s'
  rw [PMF.pure_map, PMF.pure_map, G.normalizeHist_snoc, G.normalizeHist_snoc, hnorm]

/-- A joint action drawn with player `who`'s coordinate pinned to `a` has
`who`-coordinate exactly `a` wherever it has positive probability. -/
theorem eq_of_mem_support_pmfPi_update_pure {A : ι → Type} (σ : ∀ i, PMF (A i))
    (who : ι) (a : A who) {act : ∀ i, A i}
    (hact : act ∈ (pmfPi (Function.update σ who (PMF.pure a))).support) :
    act who = a := by
  classical
  by_contra hne
  have hzero : pmfPi (Function.update σ who (PMF.pure a)) act = 0 := by
    rw [pmfPi_apply]
    apply Finset.prod_eq_zero (Finset.mem_univ who)
    rw [Function.update_self, PMF.pure_apply, if_neg hne]
  exact (PMF.mem_support_iff _ act).mp hact hzero

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- **The crux of deliverable (3).** Binding a product law with player
`who`'s coordinate pinned to a raw action `a`, through `normOneStage`,
depends on `a` only through `legalizeAct`: the illegal residue is invisible
downstream, since `normOneStage` itself renormalizes. -/
theorem pmfPi_update_bind_normOneStage_eq_legalizeAct
    {t : ℕ} (h : G.Hist t) (σ : ∀ i, PMF (G.Act i)) (who : ι) (a : G.Act who) :
    (pmfPi (Function.update σ who (PMF.pure a))).bind (G.normOneStage Legal hLegal h) =
      (pmfPi (Function.update σ who
          (PMF.pure (G.legalizeAct Legal hLegal h.2 who a)))).bind
        (G.normOneStage Legal hLegal h) := by
  have hpoint : ∀ act ∈ (pmfPi (Function.update σ who (PMF.pure a))).support,
      G.normOneStage Legal hLegal h act =
        G.normOneStage Legal hLegal h
          (Function.update act who (G.legalizeAct Legal hLegal h.2 who a)) := by
    intro act hact
    have hactWho : act who = a := eq_of_mem_support_pmfPi_update_pure σ who a hact
    apply G.normOneStage_eq_of_component_eq
    · intro i hi
      rw [Function.update_of_ne hi]
    · rw [hactWho, Function.update_self, G.legalizeAct_idem]
  rw [Math.ProbabilityMassFunction.bind_congr_on_support _ _ _ hpoint,
    pmfPi_bind_update_const σ who (PMF.pure a)
      (G.legalizeAct Legal hLegal h.2 who a) (G.normOneStage Legal hLegal h)]

omit [Fintype ι] [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- `normOneStage` depends on the prefix history only through its
normalization: chaining `normalizeHist_snoc` at the fresh action and
`normalizeHist_idem` at the prefix. -/
theorem normOneStage_normalizeHist {t : ℕ} (h : G.Hist t) (a : G.JointAct) :
    G.normOneStage Legal hLegal h a =
      G.normOneStage Legal hLegal (G.normalizeHist Legal hLegal h) a := by
  have hstate : (G.normalizeHist Legal hLegal h).2 = h.2 := G.normalizeHist_snd Legal hLegal h
  simp only [normOneStage, hstate, PMF.map_bind]
  congr 1
  funext s'
  have hstep : G.normalizeHist Legal hLegal
      ((Fin.snoc (G.normalizeHist Legal hLegal h).1 (h.2, a), s') : G.Hist (t + 1)) =
      ((Fin.snoc (G.normalizeHist Legal hLegal h).1 (h.2, G.normalizeAct Legal hLegal h.2 a), s')
        : G.Hist (t + 1)) := by
    have h0 := G.normalizeHist_snoc Legal hLegal (G.normalizeHist Legal hLegal h) a s'
    rwa [hstate, G.normalizeHist_idem] at h0
  rw [PMF.pure_map, PMF.pure_map, G.normalizeHist_snoc, hstep]

omit [Fintype ι] [DecidableEq ι] [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- Pushing an all-already-normalized-support law forward along `normalizeHist`
does not change it: `normalizeHist` is the identity on every point of the
support. -/
theorem map_normalizeHist_eq_self_of_forall_mem_support {t : ℕ} {μ : PMF (G.Hist t)}
    (hμ : ∀ h ∈ μ.support, G.IsNormalizedHist Legal h) :
    PMF.map (G.normalizeHist Legal hLegal) μ = μ := by
  rw [← PMF.bind_pure_comp]
  conv_rhs => rw [← PMF.bind_pure (p := μ)]
  apply Math.ProbabilityMassFunction.bind_congr_on_support
  intro h hh
  simp only [Function.comp_apply]
  rw [G.normalizeHist_eq_self_of_isNormalizedHist Legal hLegal (hμ h hh)]

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- `jointDevDist`'s first-coordinate marginal is the raw trajectory under
`Function.update ρ who dev`, as its name promises. -/
theorem map_fst_jointDevDist (ρ : G.BehaviorProfile) (who : ι) (dev : G.BehaviorStrategy who)
    (s₀ : G.State) (t : ℕ) :
    PMF.map Prod.fst (G.jointDevDist Legal hLegal ρ who dev s₀ t) =
      (G.normalizedGame Legal hLegal).histDist (Function.update ρ who dev) s₀ t := by
  unfold jointDevDist
  rw [PMF.map_bind]
  have hstep : ∀ h : G.Hist t, PMF.map Prod.fst ((dev t h).map fun a => (h, a)) = PMF.pure h := by
    intro h
    rw [PMF.map_comp]
    change PMF.map (Function.const (G.Act who) h) (dev t h) = PMF.pure h
    exact PMF.map_const (dev t h) h
  simp_rw [hstep]
  exact PMF.bind_pure _

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- Reshaping `μ.bind (fun h => (dev t h).bind (K h))` via `jointDevDist`'s
joint law of the history and the deviator's own action: sampling the
deviator's realized action jointly with the reached history first, then
applying `K`, is the same process. -/
theorem bind_dev_eq_bind_jointDevDist (ρ : G.BehaviorProfile) (who : ι)
    (dev : G.BehaviorStrategy who) (s₀ : G.State) (t : ℕ) {γ : Type}
    (K : G.Hist t → G.Act who → PMF γ) :
    ((G.normalizedGame Legal hLegal).histDist (Function.update ρ who dev) s₀ t).bind
        (fun h => (dev t h).bind (K h)) =
      (G.jointDevDist Legal hLegal ρ who dev s₀ t).bind (fun p => K p.1 p.2) := by
  unfold jointDevDist
  rw [PMF.bind_bind]
  apply Math.ProbabilityMassFunction.bind_congr_on_support
  intro h _
  rw [PMF.bind_map]
  rfl

/-- The one-stage kernel from a raw history `h`, given player `who`'s raw
action `a_who`, with the background profile `ρ` supplying every other
player's (history-dependent) mixed action. -/
def oppOneStage (ρ : G.BehaviorProfile) (who : ι) {t : ℕ} (h : G.Hist t)
    (a_who : G.Act who) : PMF (G.Hist (t + 1)) :=
  (pmfPi (Function.update (fun i => ρ i t h) who (PMF.pure a_who))).bind
    (G.normOneStage Legal hLegal h)

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- For a label-blind background profile, `oppOneStage` depends on the raw
history only through its normalization: every other player's mixed action
already factors through `normalizeHist` (`IsNormHistInvariant`), and
`normOneStage` itself does too (`normOneStage_normalizeHist`). -/
theorem oppOneStage_normalizeHist (ρ : G.BehaviorProfile) (who : ι)
    (hρinv : G.IsNormHistInvariantProfile Legal hLegal ρ)
    {t : ℕ} (h : G.Hist t) (a_who : G.Act who) :
    G.oppOneStage Legal hLegal ρ who h a_who =
      G.oppOneStage Legal hLegal ρ who (G.normalizeHist Legal hLegal h) a_who := by
  unfold oppOneStage
  have hfam : (Function.update (fun i => ρ i t h) who (PMF.pure a_who)) =
      (Function.update (fun i => ρ i t (G.normalizeHist Legal hLegal h)) who
        (PMF.pure a_who)) := by
    funext i
    by_cases hi : i = who
    · subst hi
      simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
      exact (IsNormHistInvariant.apply_normalizeHist G Legal hLegal (hρinv i) h).symm
  rw [hfam]
  congr 1
  funext a
  exact G.normOneStage_normalizeHist Legal hLegal h a

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- Unfold the deviating profile's stage action law at `h` into a bind over
`dev`'s own action, followed by `oppOneStage`: the "Fubini" step
(`pmfPi_update_bind`) plus the definition of `oppOneStage`. -/
theorem stageActionDist_update_bind_normOneStage (ρ : G.BehaviorProfile) (who : ι)
    (dev : G.BehaviorStrategy who) {t : ℕ} (h : G.Hist t) :
    ((G.normalizedGame Legal hLegal).stageActionDist (Function.update ρ who dev) h).bind
        (G.normOneStage Legal hLegal h) =
      (dev t h).bind (G.oppOneStage Legal hLegal ρ who h) := by
  have hsad : (G.normalizedGame Legal hLegal).stageActionDist (Function.update ρ who dev) h =
      pmfPi (Function.update (fun i => ρ i t h) who (dev t h)) := by
    change pmfPi (fun i => (Function.update ρ who dev) i t h) = _
    congr 1
    funext i
    by_cases hi : i = who
    · subst hi
      simp
    · simp [Function.update_of_ne hi]
  rw [hsad, pmfPi_update_bind]
  unfold oppOneStage
  rw [PMF.bind_bind]

/-- **The disintegration identity, assembled.** The bind over `dev`'s own
realized action, played against the raw trajectory, equals the bind over
`dev`'s *disintegrated* marginal law, played against the *normalized*
trajectory -- the mathematical heart of deliverable (3). Uses the
`condOn`/`pushforward` disintegration identity
(`bind_pushforward_condOn`) at the level of the joint law of history and
realized action. -/
theorem bind_dev_bind_oppOneStage_eq (ρ : G.BehaviorProfile) (who : ι)
    (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hρinv : G.IsNormHistInvariantProfile Legal hLegal ρ) (t : ℕ) :
    ((G.normalizedGame Legal hLegal).histDist (Function.update ρ who dev) s₀ t).bind
        (fun h => (dev t h).bind (G.oppOneStage Legal hLegal ρ who h)) =
      (PMF.map (G.normalizeHist Legal hLegal)
          ((G.normalizedGame Legal hLegal).histDist (Function.update ρ who dev) s₀ t)).bind
        (fun hn => (G.devMarginal Legal hLegal ρ who dev s₀ t
            ⟨G.normalizeHist Legal hLegal hn,
              G.isNormalizedHist_normalizeHist Legal hLegal hn⟩).bind
          (G.oppOneStage Legal hLegal ρ who hn)) := by
  rw [G.bind_dev_eq_bind_jointDevDist Legal hLegal ρ who dev s₀ t
    (fun h a => G.oppOneStage Legal hLegal ρ who h a)]
  have hgeq : (fun p : G.Hist t × G.Act who => G.oppOneStage Legal hLegal ρ who p.1 p.2) =
      (fun p : G.Hist t × G.Act who =>
        G.oppOneStage Legal hLegal ρ who (G.normalizeHist Legal hLegal p.1) p.2) :=
    funext fun p => G.oppOneStage_normalizeHist Legal hLegal ρ who hρinv p.1 p.2
  rw [hgeq, Math.ProbabilityMassFunction.bind_pushforward_condOn
    (μ := G.jointDevDist Legal hLegal ρ who dev s₀ t)
    (proj := fun p => G.normalizeHist Legal hLegal p.1)
    (g := fun p => G.oppOneStage Legal hLegal ρ who (G.normalizeHist Legal hLegal p.1) p.2)]
  have hpush : Math.ProbabilityMassFunction.pushforward
      (G.jointDevDist Legal hLegal ρ who dev s₀ t) (fun p => G.normalizeHist Legal hLegal p.1) =
      PMF.map (G.normalizeHist Legal hLegal)
        ((G.normalizedGame Legal hLegal).histDist (Function.update ρ who dev) s₀ t) := by
    have hcomp : PMF.map (G.normalizeHist Legal hLegal)
        (PMF.map Prod.fst (G.jointDevDist Legal hLegal ρ who dev s₀ t)) =
        PMF.map (G.normalizeHist Legal hLegal ∘ Prod.fst)
          (G.jointDevDist Legal hLegal ρ who dev s₀ t) :=
      PMF.map_comp Prod.fst (G.jointDevDist Legal hLegal ρ who dev s₀ t)
        (G.normalizeHist Legal hLegal)
    rw [G.map_fst_jointDevDist Legal hLegal ρ who dev s₀ t] at hcomp
    exact hcomp.symm
  rw [hpush]
  apply Math.ProbabilityMassFunction.bind_congr_on_support
  intro hn hhn
  have hnorm_hn : G.IsNormalizedHist Legal hn := by
    simp only [PMF.mem_support_map_iff] at hhn
    obtain ⟨h0, -, rfl⟩ := hhn
    exact G.isNormalizedHist_normalizeHist Legal hLegal h0
  have hidem : G.normalizeHist Legal hLegal hn = hn :=
    G.normalizeHist_eq_self_of_isNormalizedHist Legal hLegal hnorm_hn
  have hsub : (⟨G.normalizeHist Legal hLegal hn, G.isNormalizedHist_normalizeHist Legal hLegal hn⟩ :
      G.NormalizedHist Legal t) = ⟨hn, hnorm_hn⟩ :=
    Subtype.ext hidem
  rw [hsub]
  have hmass : Math.ProbabilityMassFunction.pushforward
      (G.jointDevDist Legal hLegal ρ who dev s₀ t) (fun p => G.normalizeHist Legal hLegal p.1)
      hn ≠ 0 := by
    rw [hpush]
    exact hhn
  have hcongr : ∀ p ∈ (Math.ProbabilityMassFunction.condOn
      (G.jointDevDist Legal hLegal ρ who dev s₀ t)
      (fun p => G.normalizeHist Legal hLegal p.1) hn).support,
      G.oppOneStage Legal hLegal ρ who (G.normalizeHist Legal hLegal p.1) p.2 =
        G.oppOneStage Legal hLegal ρ who hn p.2 := by
    intro p hp
    rw [Math.ProbabilityMassFunction.condOn_support_project _ _ _ hmass hp]
  rw [Math.ProbabilityMassFunction.bind_congr_on_support _ _ _ hcongr]
  unfold devMarginal
  rw [PMF.bind_map]
  rfl

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- `oppOneStage`'s dependence on the deviator's own action factors through
`legalizeAct`: the direct restatement of the crux lemma
(`pmfPi_update_bind_normOneStage_eq_legalizeAct`) in `oppOneStage`'s own
vocabulary. -/
theorem oppOneStage_eq_legalizeAct (ρ : G.BehaviorProfile) (who : ι) {t : ℕ} (h : G.Hist t)
    (a : G.Act who) :
    G.oppOneStage Legal hLegal ρ who h a =
      G.oppOneStage Legal hLegal ρ who h (G.legalizeAct Legal hLegal h.2 who a) :=
  G.pmfPi_update_bind_normOneStage_eq_legalizeAct Legal hLegal h (fun i => ρ i t h) who a

/-- **Deliverable (3), the main induction.** `devPrime`'s own raw trajectory
in the padded game equals `dev`'s raw trajectory pushed forward along
`normalizeHist`, for a label-blind *and* legal background profile `ρ`. -/
theorem histDist_devPrime_eq_map_normalizeHist_histDist_dev
    (ρ : G.BehaviorProfile) (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hρinv : G.IsNormHistInvariantProfile Legal hLegal ρ)
    (hρleg : G.IsLegalBehaviorProfile Legal ρ) :
    ∀ t : ℕ, (G.normalizedGame Legal hLegal).histDist
        (Function.update ρ who (G.devPrime Legal hLegal ρ who dev s₀)) s₀ t =
      PMF.map (G.normalizeHist Legal hLegal)
        ((G.normalizedGame Legal hLegal).histDist (Function.update ρ who dev) s₀ t) := by
  intro t
  induction t with
  | zero =>
    rw [histDist_zero, histDist_zero, PMF.pure_map, G.normalizeHist_zero]
  | succ t ih =>
    have hdevPleg : G.IsLegalBehaviorStrategy Legal who (G.devPrime Legal hLegal ρ who dev s₀) :=
      G.isLegalBehaviorStrategy_devPrime Legal hLegal ρ who dev s₀
    have hρ'leg : G.IsLegalBehaviorProfile Legal
        (Function.update ρ who (G.devPrime Legal hLegal ρ who dev s₀)) :=
      G.isLegalBehaviorProfile_update Legal hρleg hdevPleg
    have hnormS : ∀ h' ∈ ((G.normalizedGame Legal hLegal).histDist
        (Function.update ρ who (G.devPrime Legal hLegal ρ who dev s₀)) s₀ (t + 1)).support,
        G.IsNormalizedHist Legal h' :=
      fun h' hh' k i =>
        (G.normalizedGame Legal hLegal).legal_of_mem_support_histDist Legal hρ'leg s₀ (t + 1)
          hh' k i
    rw [← G.map_normalizeHist_eq_self_of_forall_mem_support Legal hLegal hnormS,
      (G.normalizedGame Legal hLegal).histDist_succ, ih, PMF.map_bind,
      (G.normalizedGame Legal hLegal).histDist_succ, PMF.map_bind]
    have hunfold : ∀ (τ : G.BehaviorProfile) (h : G.Hist t),
        PMF.map (G.normalizeHist Legal hLegal)
          (((G.normalizedGame Legal hLegal).stageActionDist τ h).bind fun a =>
            ((G.normalizedGame Legal hLegal).transition h.2 a).bind fun s' =>
              PMF.pure ((Fin.snoc h.1 (h.2, a), s') : G.Hist (t + 1))) =
          ((G.normalizedGame Legal hLegal).stageActionDist τ h).bind
            (G.normOneStage Legal hLegal h) := by
      intro τ h
      rw [PMF.map_bind]
      rfl
    simp_rw [hunfold, G.stageActionDist_update_bind_normOneStage Legal hLegal ρ who dev,
      G.stageActionDist_update_bind_normOneStage Legal hLegal ρ who
        (G.devPrime Legal hLegal ρ who dev s₀)]
    rw [G.bind_dev_bind_oppOneStage_eq Legal hLegal ρ who dev s₀ hρinv t]
    apply Math.ProbabilityMassFunction.bind_congr_on_support
    intro h hh
    have hhnorm : G.IsNormalizedHist Legal h := by
      simp only [PMF.mem_support_map_iff] at hh
      obtain ⟨h0, -, rfl⟩ := hh
      exact G.isNormalizedHist_normalizeHist Legal hLegal h0
    have hidem : G.normalizeHist Legal hLegal h = h :=
      G.normalizeHist_eq_self_of_isNormalizedHist Legal hLegal hhnorm
    have hsub : (⟨G.normalizeHist Legal hLegal h, G.isNormalizedHist_normalizeHist Legal hLegal h⟩ :
        G.NormalizedHist Legal t) = ⟨h, hhnorm⟩ :=
      Subtype.ext hidem
    rw [hsub]
    have hdevPrime : G.devPrime Legal hLegal ρ who dev s₀ t h =
        (G.devMarginal Legal hLegal ρ who dev s₀ t ⟨h, hhnorm⟩).map
          (G.legalizeAct Legal hLegal h.2 who) := by
      change G.disintegratedDev Legal hLegal ρ who dev s₀ t
          ⟨G.normalizeHist Legal hLegal h, G.isNormalizedHist_normalizeHist Legal hLegal h⟩ = _
      rw [hsub]
      rfl
    rw [hdevPrime, PMF.bind_map]
    apply Math.ProbabilityMassFunction.bind_congr_on_support
    intro b _
    exact (G.oppOneStage_eq_legalizeAct Legal hLegal ρ who h b).symm

/-- **Deliverable (3), payoff form.** `devPrime` earns *exactly* what `dev`
earns against a label-blind, legal background profile, at every horizon and
for every player -- strictly more than the "at least" the row asks for.
Combines the trajectory equality with the padded game's payoff bookkeeping
being unconditionally normalization-blind
(`totalPayoff_normalizedGame_normalizeHist_eq`). -/
theorem finiteAveragePayoff_devPrime_eq
    (ρ : G.BehaviorProfile) (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (hρinv : G.IsNormHistInvariantProfile Legal hLegal ρ)
    (hρleg : G.IsLegalBehaviorProfile Legal ρ) (T : ℕ) (whoPlayer : ι) :
    (G.normalizedGame Legal hLegal).finiteAveragePayoff s₀ T
        (Function.update ρ who (G.devPrime Legal hLegal ρ who dev s₀)) whoPlayer =
      (G.normalizedGame Legal hLegal).finiteAveragePayoff s₀ T
        (Function.update ρ who dev) whoPlayer := by
  unfold finiteAveragePayoff
  rw [G.histDist_devPrime_eq_map_normalizeHist_histDist_dev Legal hLegal ρ who dev s₀
    hρinv hρleg T]
  congr 1
  rw [Math.Probability.expect_map]
  apply Math.ProbabilityMassFunction.expect_congr_on_support
  intro h _
  exact G.totalPayoff_normalizedGame_normalizeHist_eq Legal hLegal whoPlayer h

-- ============================================================================
-- Deliverable (4): the conditional consequence
-- ============================================================================

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- The legal-deviation half of deliverable (4) does *not* need `devPrime` at
all: an already-legal deviator's padded-game and original-game payoffs
already coincide (`finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile`),
so the unrestricted cap hypothesis, instantiated directly at that deviator,
suffices. Recorded to make precise exactly where disintegration is (and is
not) load-bearing. -/
theorem isεLegalHorizonNash_of_isεHorizonNash_normalizedGame
    (ρ : G.BehaviorProfile) (s₀ : G.State) (T : ℕ) (ε : ℝ)
    (hρleg : G.IsLegalBehaviorProfile Legal ρ)
    (hcap : (G.normalizedGame Legal hLegal).IsεHorizonNash s₀ T ε ρ) :
    G.IsεLegalHorizonNash Legal s₀ T ε ρ := by
  refine ⟨hρleg, fun who dev hdevleg => ?_⟩
  have hupdleg : G.IsLegalBehaviorProfile Legal (Function.update ρ who dev) :=
    G.isLegalBehaviorProfile_update Legal hρleg hdevleg
  rw [← G.finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile
      Legal hLegal hρleg s₀ T who,
    ← G.finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile
      Legal hLegal hupdleg s₀ T who]
  exact hcap who dev

/-- **Deliverable (4), where `devPrime` is genuinely load-bearing.** For a
label-blind, legal `ρ` witnessing an *unrestricted*-deviation cap of the
padded game -- quantified over literally every `BehaviorStrategy`, exactly as
unrestricted as `IsεHorizonNash` itself, with no restriction imposed on the
deviator anywhere in this argument -- every such deviator's *disintegrated,
legal* counterpart is capped in the **original** game's own bookkeeping.
This is strictly more than `isεLegalHorizonNash_of_isεHorizonNash_normalizedGame`
supplies: it shows the padded game's unrestricted cap is achieved by an
actual legal strategy of `G`, for *every* unrestricted deviation, not only
already-legal ones. -/
theorem finiteAveragePayoff_devPrime_le_of_isεHorizonNash_normalizedGame
    (ρ : G.BehaviorProfile) (who : ι) (dev : G.BehaviorStrategy who) (s₀ : G.State)
    (T : ℕ) (ε : ℝ)
    (hρinv : G.IsNormHistInvariantProfile Legal hLegal ρ)
    (hρleg : G.IsLegalBehaviorProfile Legal ρ)
    (hcap : (G.normalizedGame Legal hLegal).IsεHorizonNash s₀ T ε ρ) :
    G.finiteAveragePayoff s₀ T (Function.update ρ who (G.devPrime Legal hLegal ρ who dev s₀))
        who ≤ G.finiteAveragePayoff s₀ T ρ who + ε := by
  have hdevPleg : G.IsLegalBehaviorStrategy Legal who (G.devPrime Legal hLegal ρ who dev s₀) :=
    G.isLegalBehaviorStrategy_devPrime Legal hLegal ρ who dev s₀
  have hupdleg : G.IsLegalBehaviorProfile Legal
      (Function.update ρ who (G.devPrime Legal hLegal ρ who dev s₀)) :=
    G.isLegalBehaviorProfile_update Legal hρleg hdevPleg
  rw [← G.finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile
      Legal hLegal hupdleg s₀ T who,
    G.finiteAveragePayoff_devPrime_eq Legal hLegal ρ who dev s₀ hρinv hρleg T who]
  have hcapdev := hcap who dev
  rw [G.finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile Legal hLegal hρleg s₀ T who]
    at hcapdev
  linarith

omit [Finite G.State] [∀ i, Finite (G.Act i)] in
/-- **Deliverable (4), the conditional consequence.** If the padded game's
uniform equilibrium payoff at `v` is witnessed, at every accuracy, by a
profile that is *both* label-blind and legal -- the strengthening of the
*prescribed* profile this row explicitly permits -- then `v` is a genuine
legal uniform equilibrium payoff of the *original* game. What this does
**not** discharge: producing such a witness from an arbitrary *unrestricted*
one, which the module docstring localizes as a separate obstruction. -/
theorem isLegalUniformEquilibriumPayoff_of_witness
    (s₀ : G.State) (v : Payoff ι)
    (hwit : ∀ ε : ℝ, 0 < ε → ∃ (σ : G.BehaviorProfile) (T₀ : ℕ),
      G.IsNormHistInvariantProfile Legal hLegal σ ∧ G.IsLegalBehaviorProfile Legal σ ∧
        ∀ T, T₀ ≤ T → (G.normalizedGame Legal hLegal).IsεHorizonNash s₀ T ε σ ∧
          ∀ who, |(G.normalizedGame Legal hLegal).finiteAveragePayoff s₀ T σ who - v who| ≤ ε) :
    G.IsLegalUniformEquilibriumPayoff Legal s₀ v := by
  intro ε hε
  obtain ⟨σ, T₀, hσinv, hσleg, hσ⟩ := hwit ε hε
  refine ⟨σ, T₀, fun T hT => ?_⟩
  obtain ⟨hcap, happrox⟩ := hσ T hT
  refine ⟨G.isεLegalHorizonNash_of_isεHorizonNash_normalizedGame Legal hLegal σ s₀ T ε hσleg hcap,
    fun who => ?_⟩
  have h := happrox who
  rwa [G.finiteAveragePayoff_normalizedGame_eq_of_isLegalBehaviorProfile
    Legal hLegal hσleg s₀ T who] at h

end StochasticGame

end GameTheory
