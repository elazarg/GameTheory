/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.FinitePublicTerminalNashPerturbation
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.FirstHitStoppingRule

/-!
# Producing delayed child-obstacle closeness from child certificates

`FiniteRankedTerminalChildCoverage.ObstacleCloseness` is the one hypothesis
of the fixed-depth composition chain that was assumed rather than derived:
it says that the three delayed child obstacles (`lowerObstacle`,
`upperObstacle`, `deviationObstacle` of `delayedData`) sit within
`childError` of the fixed child-target obstacle at every terminal public
history.  `FinitePublicTerminalNashPerturbation` *consumes* that structure;
nothing produced it.

This file produces it, from the child adaptive-potential witnesses alone.

## The mechanism

A `FiniteRankedTerminalChildCoverage` requires its stopping rule to select
the endpoint at the common depth (`selector_eq_last`).  Hence the realized
stopped suffix of every complete public history is *empty*
(`rootOnlineStoppedPath_eq_append_empty_of_selector_eq_last`), and the
delayed obstacle at a terminal history is exactly the selected child
system's time-zero potential at its own entry state
(`lowerObstacle_eq_child_initial` and its two twins).  That value is
compared with the child target by the `lower_initial` / `upper_initial` /
`deviation_initial` fields of `AdaptivePotentialSystemAt`, which are bounded
by the family accuracy.  No error is lost: the produced closeness constant
is the family accuracy `childError` itself, not a multiple of it.  The
finite-time `3 * error` triples of
`AdaptivePotentialFiniteTimeTargetBounds` are therefore not needed here;
they bound potentials at *positive* times, whereas the terminal coverage
only ever evaluates the child witnesses at time zero.

## What is proved

* `lowerObstacle_eq_child_initial`, `upperObstacle_eq_child_initial`,
  `deviationObstacle_eq_child_initial` — the exact pointwise identities.
* `abs_lowerObstacle_sub_targetObstacle_le` and twins — the three closeness
  bounds in exactly the shape of the `ObstacleCloseness` fields.
* `obstacleCloseness` — the producer: the literal
  `coverage.ObstacleCloseness family` structure, for *every* family, with no
  extra hypothesis.
* `delayedObstacleClosure` and `delayedObstacleClosure_of_certificates` —
  the end-to-end chain: childwise adaptive-potential certificates alone
  give a `2 * childError`-equilibrium of the unchanged backward-Nash
  selection for the three actual delayed obstacles, together with the three
  `childError` root anchors at the endogenous parent target.
* `lowerObstacle_close_iff` and `not_lowerObstacle_close_of_lt` (and twins)
  — sharpness: closeness at a bound holds *iff* every observed child's
  time-zero gap is below that bound, so no bound smaller than a realized
  child gap can be produced.
* `terminalOnlineStoppingRule`, `canonicalStateCoverage` and
  `nonempty_finiteRankedTerminalChildCoverage` — the coverage hypothesis is
  inhabited for every finite-state game and every depth, so the producer is
  not vacuous; `canonicalStateCoverage_obstacleCloseness` and
  `canonicalStateCoverage_delayedObstacleClosure_of_certificates` run the
  whole chain on that inhabited coverage.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.PMFProduct Math.Probability
open Math.ProbabilityMassFunction

variable {ι Child : Type} {G : StochasticGame ι}

/-! ### Inhabiting the terminal coverage

The producer below is unconditional in the child family, so its content
depends on `FiniteRankedTerminalChildCoverage` being inhabited at all.  It
is: the never-stopping first-hit region supplies a complete online rule
whose view is empty before the fuel and whose selector is the endpoint, and
observing the terminal state itself supplies a total legal child
assignment. -/

/-- Persistence of the never-stopping online view, in the normalized form
where the stopped base already sits at the fuel endpoint. -/
theorem firstHitOnlineView_never_persistent_last
    (fuel suffixLength : ℕ)
    (base : G.Hist fuel) (suffix : G.Hist suffixLength)
    (hstart : suffix.StartsAt base.2) :
    G.firstHitOnlineView (neverPublicStop G) fuel
        (fuel + suffixLength) (G.appendHist base suffix) =
      some
        (G.onlineStoppedPathOfAppend
          (⟨Fin.last fuel, base⟩ : G.BoundedStoppedHistory fuel)
          suffix) := by
  have hle : fuel ≤ fuel + suffixLength := Nat.le_add_right _ _
  unfold firstHitOnlineView
  rw [dif_pos hle]
  refine congrArg some ?_
  refine OnlineStoppedPath.eq_of_base_eq_of_reconstructs
    (G.appendHist base suffix) ?_
    (G.rootOnlineStoppedPath_sound _ hle (G.appendHist base suffix)).2
    rfl
  change
    G.selectedStoppedHistory
        (G.firstHitStopSelector (neverPublicStop G) fuel)
        (G.boundedHistoryPrefix (G.appendHist base suffix)
          ⟨fuel, Nat.lt_succ_of_le hle⟩) =
      (⟨Fin.last fuel, base⟩ : G.BoundedStoppedHistory fuel)
  rw [G.boundedHistoryPrefix_appendHist base suffix hstart]
  change
    (⟨G.firstHitStopSelector (neverPublicStop G) fuel base,
        G.boundedHistoryPrefix base
          (G.firstHitStopSelector (neverPublicStop G) fuel base)⟩ :
        G.BoundedStoppedHistory fuel) =
      (⟨Fin.last fuel, base⟩ : G.BoundedStoppedHistory fuel)
  rw [G.firstHitStopSelector_never fuel base,
    G.boundedHistoryPrefix_last_eq]

/-- The online causal stopping rule that never fires before the common
horizon.  Its selector is the mandatory endpoint. -/
def terminalOnlineStoppingRule (G : StochasticGame ι) (fuel : ℕ) :
    G.OnlineCausalBoundedStoppingRule fuel where
  selector := G.firstHitStopSelector (neverPublicStop G) fuel
  causal := G.firstHitStopSelector_causal (neverPublicStop G) fuel
  view := G.firstHitOnlineView (neverPublicStop G) fuel
  reconstructs := fun _ history path hview =>
    G.firstHitOnlineView_returned_sound
      (neverPublicStop G) history path hview
  base_occurs := fun _ history path hview =>
    G.firstHitOnlineView_returned_base_occurs
      (neverPublicStop G) history path hview
  persistent := by
    intro base hoccurs suffixLength suffix hstart
    obtain ⟨length, history⟩ := base
    have hoccurs' :
        G.firstHitOnlineView (neverPublicStop G) fuel length.val
            history =
          some
            (G.onlineStoppedPathOfAppend
              (⟨length, history⟩ : G.BoundedStoppedHistory fuel)
              (G.emptyHist history.2)) := hoccurs
    have hlen : fuel ≤ length.val := by
      by_contra hlt
      rw [
        G.firstHitOnlineView_never_of_lt fuel (not_le.mp hlt) history
      ] at hoccurs'
      simp only [reduceCtorEq] at hoccurs'
    have hlast : length = Fin.last fuel :=
      Fin.ext (le_antisymm (Nat.lt_succ_iff.mp length.isLt) hlen)
    subst hlast
    exact
      G.firstHitOnlineView_never_persistent_last fuel suffixLength
        history suffix hstart
  complete := by
    intro time htime history
    simp [firstHitOnlineView, htime]

/-- Every finite-state game admits a ranked terminal child coverage at every
depth: never stop before the horizon, and let each terminal history observe
its own state as the child.

This is what makes the producer below non-vacuous. -/
def canonicalStateCoverage (G : StochasticGame ι) [Fintype G.State]
    (fuel : ℕ) (initial : G.State) :
    G.FiniteRankedTerminalChildCoverage (Child := G.State) id fuel where
  rule := G.terminalOnlineStoppingRule fuel
  initial := initial
  observe := fun base => base.2.2
  entry_eq := fun _ => rfl
  parentRank := 1
  childRank := fun _ => 0
  childRank_lt := fun _ => Nat.zero_lt_one
  view_eq_none_of_lt := fun _ history htime =>
    G.firstHitOnlineView_never_of_lt fuel htime history
  selector_eq_last := fun history =>
    G.firstHitStopSelector_never fuel history

/-- The fixed-depth composition chain is not vacuous: its coverage
hypothesis is inhabited for every finite-state game and every depth. -/
theorem nonempty_finiteRankedTerminalChildCoverage
    (G : StochasticGame ι) [Fintype G.State]
    (fuel : ℕ) (initial : G.State) :
    Nonempty
      (G.FiniteRankedTerminalChildCoverage (Child := G.State) id fuel) :=
  ⟨G.canonicalStateCoverage fuel initial⟩

namespace DelayedFullHorizonChildEnvelopeData

variable
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] [Fintype Child]
    {entry : Child → G.State} {childTarget : Child → Payoff ι}
    {childError : ℝ} {fuel : ℕ}
    (data :
      G.DelayedFullHorizonChildEnvelopeData
        entry childTarget childError fuel)

/-- When the online rule stops exactly at the common horizon, the realized
stopped suffix is empty, so the delayed obstacle reads the selected child's
potential at time zero and at the terminal state.

This is the only place where `selector_eq_last` is used; everything else in
this file is bookkeeping on top of it. -/
theorem stoppedPotentialObstacle_of_selector_eq_last
    (childPotential :
      G.BoundedStoppedHistory fuel → G.HistoryPotential)
    (history : G.Hist fuel)
    (hlast : data.rule.selector history = Fin.last fuel) :
    data.stoppedPotentialObstacle childPotential history =
      childPotential
        (⟨Fin.last fuel, history⟩ : G.BoundedStoppedHistory fuel)
        0 (G.emptyHist history.2) :=
  congrArg
    (fun path : G.OnlineStoppedPath fuel fuel =>
      childPotential path.base path.suffixLength path.suffix)
    (G.rootOnlineStoppedPath_eq_append_empty_of_selector_eq_last
      data.rule.selector history hlast)

end DelayedFullHorizonChildEnvelopeData

namespace FiniteRankedTerminalChildCoverage

variable
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)]
    [Fintype Child]
    {entry : Child → G.State} {childTarget : Child → Payoff ι}
    {childError : ℝ} {fuel : ℕ}
    (coverage : G.FiniteRankedTerminalChildCoverage entry fuel)
    (family :
      G.FiniteChildAdaptivePotentialFamily
        entry childTarget childError)

/-! ### Per-child anchoring of the three delayed obstacles -/

/-- The delayed lower obstacle at a terminal public history is exactly the
selected child witness's initial lower potential. -/
theorem lowerObstacle_eq_child_initial
    (history : G.Hist fuel) (who : ι) :
    (coverage.delayedData family).lowerObstacle history who =
      (family.system (coverage.terminalChild history)).lowerPotential
        who 0 (G.emptyHist (entry (coverage.terminalChild history))) := by
  refine Eq.trans
    ((coverage.delayedData family).stoppedPotentialObstacle_of_selector_eq_last
      (family.stoppedLowerPotential coverage.observe who) history
      (coverage.selector_eq_last history)) ?_
  exact congrArg
    (fun state =>
      (family.system (coverage.terminalChild history)).lowerPotential
        who 0 (G.emptyHist state))
    (coverage.entry_eq ⟨Fin.last fuel, history⟩)

/-- The delayed upper obstacle at a terminal public history is exactly the
selected child witness's initial upper potential. -/
theorem upperObstacle_eq_child_initial
    (history : G.Hist fuel) (who : ι) :
    (coverage.delayedData family).upperObstacle history who =
      (family.system (coverage.terminalChild history)).upperPotential
        who 0 (G.emptyHist (entry (coverage.terminalChild history))) := by
  refine Eq.trans
    ((coverage.delayedData family).stoppedPotentialObstacle_of_selector_eq_last
      (family.stoppedUpperPotential coverage.observe who) history
      (coverage.selector_eq_last history)) ?_
  exact congrArg
    (fun state =>
      (family.system (coverage.terminalChild history)).upperPotential
        who 0 (G.emptyHist state))
    (coverage.entry_eq ⟨Fin.last fuel, history⟩)

/-- The delayed deviation obstacle at a terminal public history is exactly
the selected child witness's initial deviation potential. -/
theorem deviationObstacle_eq_child_initial
    (history : G.Hist fuel) (who : ι) :
    (coverage.delayedData family).deviationObstacle history who =
      (family.system (coverage.terminalChild history)).deviationPotential
        who 0 (G.emptyHist (entry (coverage.terminalChild history))) := by
  refine Eq.trans
    ((coverage.delayedData family).stoppedPotentialObstacle_of_selector_eq_last
      (family.stoppedDeviationPotential coverage.observe who) history
      (coverage.selector_eq_last history)) ?_
  exact congrArg
    (fun state =>
      (family.system (coverage.terminalChild history)).deviationPotential
        who 0 (G.emptyHist state))
    (coverage.entry_eq ⟨Fin.last fuel, history⟩)

/-- The lower closeness gap is exactly the selected child's initial lower
target gap. -/
theorem abs_lowerObstacle_sub_targetObstacle
    (history : G.Hist fuel) (who : ι) :
    |(coverage.delayedData family).lowerObstacle history who -
        coverage.targetObstacle childTarget history who| =
      |(family.system (coverage.terminalChild history)).lowerPotential
            who 0
            (G.emptyHist (entry (coverage.terminalChild history))) -
          childTarget (coverage.terminalChild history) who| :=
  congrArg (fun value =>
      |value - childTarget (coverage.terminalChild history) who|)
    (coverage.lowerObstacle_eq_child_initial family history who)

/-- The upper closeness gap is exactly the selected child's initial upper
target gap. -/
theorem abs_upperObstacle_sub_targetObstacle
    (history : G.Hist fuel) (who : ι) :
    |(coverage.delayedData family).upperObstacle history who -
        coverage.targetObstacle childTarget history who| =
      |(family.system (coverage.terminalChild history)).upperPotential
            who 0
            (G.emptyHist (entry (coverage.terminalChild history))) -
          childTarget (coverage.terminalChild history) who| :=
  congrArg (fun value =>
      |value - childTarget (coverage.terminalChild history) who|)
    (coverage.upperObstacle_eq_child_initial family history who)

/-- The deviation closeness gap is exactly the selected child's initial
deviation target gap. -/
theorem abs_deviationObstacle_sub_targetObstacle
    (history : G.Hist fuel) (who : ι) :
    |(coverage.delayedData family).deviationObstacle history who -
        coverage.targetObstacle childTarget history who| =
      |(family.system (coverage.terminalChild history)).deviationPotential
            who 0
            (G.emptyHist (entry (coverage.terminalChild history))) -
          childTarget (coverage.terminalChild history) who| :=
  congrArg (fun value =>
      |value - childTarget (coverage.terminalChild history) who|)
    (coverage.deviationObstacle_eq_child_initial family history who)

/-- Tier-one anchoring, lower obstacle: exactly the `lower` field shape of
`ObstacleCloseness`. -/
theorem abs_lowerObstacle_sub_targetObstacle_le
    (history : G.Hist fuel) (who : ι) :
    |(coverage.delayedData family).lowerObstacle history who -
        coverage.targetObstacle childTarget history who| ≤
      childError := by
  rw [coverage.abs_lowerObstacle_sub_targetObstacle family history who]
  exact (family.system (coverage.terminalChild history)).lower_initial who

/-- Tier-one anchoring, upper obstacle: exactly the `upper` field shape of
`ObstacleCloseness`. -/
theorem abs_upperObstacle_sub_targetObstacle_le
    (history : G.Hist fuel) (who : ι) :
    |(coverage.delayedData family).upperObstacle history who -
        coverage.targetObstacle childTarget history who| ≤
      childError := by
  rw [coverage.abs_upperObstacle_sub_targetObstacle family history who]
  exact (family.system (coverage.terminalChild history)).upper_initial who

/-- Tier-one anchoring, deviation obstacle: exactly the `deviation` field
shape of `ObstacleCloseness`. -/
theorem abs_deviationObstacle_sub_targetObstacle_le
    (history : G.Hist fuel) (who : ι) :
    |(coverage.delayedData family).deviationObstacle history who -
        coverage.targetObstacle childTarget history who| ≤
      childError := by
  rw [coverage.abs_deviationObstacle_sub_targetObstacle family history who]
  exact
    (family.system (coverage.terminalChild history)).deviation_initial who

/-! ### The producer -/

/-- **Producer.**  Every finite child adaptive-potential family at accuracy
`childError` satisfies the delayed-obstacle closeness assumed by
`FiniteRankedTerminalChildNashClosure`, with no additional hypothesis.

The literal structure is produced; the closeness constant is the family
accuracy itself. -/
theorem obstacleCloseness : coverage.ObstacleCloseness family where
  lower := fun history who =>
    coverage.abs_lowerObstacle_sub_targetObstacle_le family history who
  upper := fun history who =>
    coverage.abs_upperObstacle_sub_targetObstacle_le family history who
  deviation := fun history who =>
    coverage.abs_deviationObstacle_sub_targetObstacle_le family history who

/-! ### End-to-end chain -/

/-- Everything the fixed-depth composition chain concludes about the delayed
child obstacles, once closeness is available.

The first three fields are the incentive-safety statements of
`FinitePublicTerminalNashPerturbation`: the *unchanged* backward-Nash
selection of the fixed child-target obstacle is a `2 * childError`
equilibrium for each actual delayed obstacle.  The last three are the root
anchors of `FiniteRankedTerminalChildNashClosure` at the endogenous parent
target. -/
structure DelayedObstacleClosure : Prop where
  lowerEquilibrium : ∀ (who : ι) (deviation : G.BehaviorStrategy who),
    expect
        (G.histDist
          (Function.update (coverage.selection childTarget) who deviation)
          coverage.initial fuel)
        (fun history =>
          (coverage.delayedData family).lowerObstacle history who) ≤
      expect
        (G.histDist (coverage.selection childTarget) coverage.initial fuel)
        (fun history =>
          (coverage.delayedData family).lowerObstacle history who) +
        2 * childError
  upperEquilibrium : ∀ (who : ι) (deviation : G.BehaviorStrategy who),
    expect
        (G.histDist
          (Function.update (coverage.selection childTarget) who deviation)
          coverage.initial fuel)
        (fun history =>
          (coverage.delayedData family).upperObstacle history who) ≤
      expect
        (G.histDist (coverage.selection childTarget) coverage.initial fuel)
        (fun history =>
          (coverage.delayedData family).upperObstacle history who) +
        2 * childError
  deviationEquilibrium : ∀ (who : ι) (deviation : G.BehaviorStrategy who),
    expect
        (G.histDist
          (Function.update (coverage.selection childTarget) who deviation)
          coverage.initial fuel)
        (fun history =>
          (coverage.delayedData family).deviationObstacle history who) ≤
      expect
        (G.histDist (coverage.selection childTarget) coverage.initial fuel)
        (fun history =>
          (coverage.delayedData family).deviationObstacle history who) +
        2 * childError
  lowerAnchor : ∀ who : ι,
    |(coverage.delayedData family).lowerPotential
          who 0 (G.emptyHist coverage.initial) -
        coverage.parentTarget childTarget who| ≤
      childError
  upperAnchor : ∀ who : ι,
    |(coverage.delayedData family).upperPotential
          who 0 (G.emptyHist coverage.initial) -
        coverage.parentTarget childTarget who| ≤
      childError
  deviationAnchor : ∀ who : ι,
    |(coverage.delayedData family).prescribedDeviationRoot who -
        coverage.parentTarget childTarget who| ≤
      childError

/-- **The chain closes.**  A finite child adaptive-potential family at
accuracy `childError` alone yields the complete delayed-obstacle
conclusion: the unchanged backward-Nash selection is a
`2 * childError`-equilibrium for the three actual delayed obstacles, and
each delayed root sits within `childError` of the endogenous parent
target. -/
theorem delayedObstacleClosure :
    coverage.DelayedObstacleClosure family where
  lowerEquilibrium := fun who deviation =>
    coverage.selection_lowerObstacle_deviation_le family
      (coverage.obstacleCloseness family) who deviation
  upperEquilibrium := fun who deviation =>
    coverage.selection_upperObstacle_deviation_le family
      (coverage.obstacleCloseness family) who deviation
  deviationEquilibrium := fun who deviation =>
    coverage.selection_deviationObstacle_deviation_le family
      (coverage.obstacleCloseness family) who deviation
  lowerAnchor := fun who =>
    coverage.lower_root_close_parentTarget family
      (coverage.obstacleCloseness family) who
  upperAnchor := fun who =>
    coverage.upper_root_close_parentTarget family
      (coverage.obstacleCloseness family) who
  deviationAnchor := fun who =>
    coverage.prescribedDeviationRoot_close_parentTarget family
      (coverage.obstacleCloseness family) who

/-- **End-to-end corollary from certificates only.**  Childwise
adaptive-potential *certificates* at a common accuracy — the existential
interface, with no chosen witnesses — already give the whole delayed
conclusion for the canonically chosen family. -/
theorem delayedObstacleClosure_of_certificates
    (certificates : ∀ child,
      G.IsAdaptivePotentialCertificateAt
        (entry child) (childTarget child) childError) :
    coverage.DelayedObstacleClosure
      (FiniteChildAdaptivePotentialFamily.ofCertificates
        (G := G) certificates) :=
  coverage.delayedObstacleClosure _

/-- Certificate-level form of the producer itself. -/
theorem obstacleCloseness_of_certificates
    (certificates : ∀ child,
      G.IsAdaptivePotentialCertificateAt
        (entry child) (childTarget child) childError) :
    coverage.ObstacleCloseness
      (FiniteChildAdaptivePotentialFamily.ofCertificates
        (G := G) certificates) :=
  coverage.obstacleCloseness _

/-! ### Sharpness of the produced constant -/

/-- Closeness of the delayed lower obstacle at *any* bound is equivalent to
the corresponding bound on every observed child's initial lower gap.  The
produced constant is therefore exactly the realized supremum: it cannot be
lowered. -/
theorem lowerObstacle_close_iff {bound : ℝ} :
    (∀ (history : G.Hist fuel) (who : ι),
        |(coverage.delayedData family).lowerObstacle history who -
          coverage.targetObstacle childTarget history who| ≤ bound) ↔
      ∀ (history : G.Hist fuel) (who : ι),
        |(family.system (coverage.terminalChild history)).lowerPotential
              who 0
              (G.emptyHist (entry (coverage.terminalChild history))) -
            childTarget (coverage.terminalChild history) who| ≤ bound := by
  constructor
  · intro close history who
    rw [← coverage.abs_lowerObstacle_sub_targetObstacle family history who]
    exact close history who
  · intro close history who
    rw [coverage.abs_lowerObstacle_sub_targetObstacle family history who]
    exact close history who

/-- Same equivalence for the upper obstacle. -/
theorem upperObstacle_close_iff {bound : ℝ} :
    (∀ (history : G.Hist fuel) (who : ι),
        |(coverage.delayedData family).upperObstacle history who -
          coverage.targetObstacle childTarget history who| ≤ bound) ↔
      ∀ (history : G.Hist fuel) (who : ι),
        |(family.system (coverage.terminalChild history)).upperPotential
              who 0
              (G.emptyHist (entry (coverage.terminalChild history))) -
            childTarget (coverage.terminalChild history) who| ≤ bound := by
  constructor
  · intro close history who
    rw [← coverage.abs_upperObstacle_sub_targetObstacle family history who]
    exact close history who
  · intro close history who
    rw [coverage.abs_upperObstacle_sub_targetObstacle family history who]
    exact close history who

/-- Same equivalence for the deviation obstacle. -/
theorem deviationObstacle_close_iff {bound : ℝ} :
    (∀ (history : G.Hist fuel) (who : ι),
        |(coverage.delayedData family).deviationObstacle history who -
          coverage.targetObstacle childTarget history who| ≤ bound) ↔
      ∀ (history : G.Hist fuel) (who : ι),
        |(family.system (coverage.terminalChild history)).deviationPotential
              who 0
              (G.emptyHist (entry (coverage.terminalChild history))) -
            childTarget (coverage.terminalChild history) who| ≤ bound := by
  constructor
  · intro close history who
    rw [← coverage.abs_deviationObstacle_sub_targetObstacle
      family history who]
    exact close history who
  · intro close history who
    rw [coverage.abs_deviationObstacle_sub_targetObstacle
      family history who]
    exact close history who

/-- **Falsifier.**  One observed child whose initial lower potential misses
its own target by more than `bound` refutes lower closeness at `bound`.

Taking `bound < childError` for a family whose certificate gap is attained
shows the producer's constant is tight: no smaller uniform bound is
derivable from the family data. -/
theorem not_lowerObstacle_close_of_lt
    {bound : ℝ} (history : G.Hist fuel) (who : ι)
    (gap : bound <
      |(family.system (coverage.terminalChild history)).lowerPotential
            who 0
            (G.emptyHist (entry (coverage.terminalChild history))) -
          childTarget (coverage.terminalChild history) who|) :
    ¬∀ (base : G.Hist fuel) (player : ι),
        |(coverage.delayedData family).lowerObstacle base player -
          coverage.targetObstacle childTarget base player| ≤ bound := by
  intro close
  exact absurd
    ((coverage.lowerObstacle_close_iff family).mp close history who)
    (not_le.mpr gap)

/-- Falsifier for the upper obstacle. -/
theorem not_upperObstacle_close_of_lt
    {bound : ℝ} (history : G.Hist fuel) (who : ι)
    (gap : bound <
      |(family.system (coverage.terminalChild history)).upperPotential
            who 0
            (G.emptyHist (entry (coverage.terminalChild history))) -
          childTarget (coverage.terminalChild history) who|) :
    ¬∀ (base : G.Hist fuel) (player : ι),
        |(coverage.delayedData family).upperObstacle base player -
          coverage.targetObstacle childTarget base player| ≤ bound := by
  intro close
  exact absurd
    ((coverage.upperObstacle_close_iff family).mp close history who)
    (not_le.mpr gap)

/-- Falsifier for the deviation obstacle. -/
theorem not_deviationObstacle_close_of_lt
    {bound : ℝ} (history : G.Hist fuel) (who : ι)
    (gap : bound <
      |(family.system (coverage.terminalChild history)).deviationPotential
            who 0
            (G.emptyHist (entry (coverage.terminalChild history))) -
          childTarget (coverage.terminalChild history) who|) :
    ¬∀ (base : G.Hist fuel) (player : ι),
        |(coverage.delayedData family).deviationObstacle base player -
          coverage.targetObstacle childTarget base player| ≤ bound := by
  intro close
  exact absurd
    ((coverage.deviationObstacle_close_iff family).mp close history who)
    (not_le.mpr gap)

/-- A negative bound is always refuted as soon as one terminal public
history and one player exist: the produced closeness constant can never be
driven below zero. -/
theorem not_lowerObstacle_close_of_neg
    {bound : ℝ} (history : G.Hist fuel) (who : ι) (hbound : bound < 0) :
    ¬∀ (base : G.Hist fuel) (player : ι),
        |(coverage.delayedData family).lowerObstacle base player -
          coverage.targetObstacle childTarget base player| ≤ bound :=
  coverage.not_lowerObstacle_close_of_lt family history who
    (lt_of_lt_of_le hbound (abs_nonneg _))

end FiniteRankedTerminalChildCoverage

/-! ### The producer on an inhabited coverage -/

section CanonicalCoverage

variable
    [Fintype ι] [DecidableEq ι]
    [∀ who, Fintype (G.Act who)]
    [∀ who, Nonempty (G.Act who)] [Fintype G.State]
    {stateTarget : G.State → Payoff ι} {stateError : ℝ}

/-- The producer is inhabited-nonvacuous: on the canonical coverage of any
finite-state game, every family of state-indexed child witnesses really does
satisfy the delayed-obstacle closeness. -/
theorem canonicalStateCoverage_obstacleCloseness
    (fuel : ℕ) (initial : G.State)
    (family :
      G.FiniteChildAdaptivePotentialFamily
        (Child := G.State) id stateTarget stateError) :
    (G.canonicalStateCoverage fuel initial).ObstacleCloseness family :=
  (G.canonicalStateCoverage fuel initial).obstacleCloseness family

/-- The whole delayed chain, on an inhabited coverage, from childwise
adaptive-potential certificates alone. -/
theorem canonicalStateCoverage_delayedObstacleClosure_of_certificates
    (fuel : ℕ) (initial : G.State)
    (certificates : ∀ state : G.State,
      G.IsAdaptivePotentialCertificateAt
        state (stateTarget state) stateError) :
    (G.canonicalStateCoverage fuel initial).DelayedObstacleClosure
      (FiniteChildAdaptivePotentialFamily.ofCertificates
        (G := G) (entry := id) certificates) :=
  (G.canonicalStateCoverage fuel initial).delayedObstacleClosure _

end CanonicalCoverage

end StochasticGame
end GameTheory
