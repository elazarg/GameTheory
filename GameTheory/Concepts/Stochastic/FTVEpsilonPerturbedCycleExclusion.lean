/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FTVCyclicAdmissibleCycle
import GameTheory.Concepts.Stochastic.QuittingSoloQuitterEquilibrium

/-!
# The published `ε`-perturbation excludes period-one and period-three cycles

The `ε`-bonus perturbation (`ε > 0`) of the
Flesch--Thuijsman--Vrieze three-player table already formalized in
`FTVCyclicAdmissibleCycle.lean`,

`r({1}) = (1, 3, 0)`, `r({1,2}) = (1+ε, 0, 1)`,
`r({2}) = (0, 1, 3)`, `r({2,3}) = (1, 1+ε, 0)`,
`r({3}) = (3, 0, 1)`, `r({1,3}) = (0, 1, 1+ε)`,
`r({1,2,3}) = (0, 0, 0)`,

has positive solo values (so it is not zero-solo) and admits no admissible
absorbing quitting cycle at period one or at period three.  This file proves
those two facts, reusing the unperturbed table's machinery rather than
rebuilding it.

## What this does not do

It does **not** show the weight admits no cycle at *any* period; that is the
published Theorem 2.1 (Solan 2001) in its bounded form, and it is
unformalized here.  Nothing below states or implies it.

## Scope of the two period-one results

Two period-one theorems are proved.  `not_quittingSoloQuitterCriterion_ftvRewardEps`
is the literal fence recorded in `FRONTIER.md` and in the hand computation:
the repository's own name for the classical affine no-join condition,
`QuittingSoloQuitterCriterion`, fails at every coordinate and every rate.

The stronger `not_isQuittingCyclicContinuationBlock_of_isolated` goes past that
named sufficient condition to the actual carrier predicate
`IsQuittingCyclicContinuationBlock` itself: **no period-one block whose single
row isolates one coordinate as the sole possible quitter is admissible**, for
*every* choice of owner, absorbing hazard, and terminal vector -- not merely
for the specific rate-`p` row family the no-join condition tests.  It does
**not** cover period-one rows at which two or three coordinates mix between
quit and continue simultaneously; the repository has no period-one Nash
machinery for that shape, so that case is open.

## Scope of the period-three result

`not_isQuittingCyclicContinuationBlock_ftvBlock_ftvRewardEps` shows that
`FTVCyclicAdmissibleCycle.ftvBlock` -- the *exact same* three-phase block data
that is an admissible cyclic continuation for the unperturbed table -- is
**not** an `IsQuittingCyclicContinuationBlock` for the `ε`-perturbed table, at
any `ε > 0`.  This is a statement about *that one block*, reproducing the
hand computation's preemption mechanism exactly: recomputing the deviation
payoff from the repository's own `quittingRootQuitPayoff`/
`quittingRootContinuePayoff` gives `½·(1+ε) + ½·1 = 1 + ε/2` against a
continuation payoff of `1`, a strictly profitable deviation of size `ε/2`.  It
is **not** a claim that every period-three block fails; other period-three
blocks for this weight are not examined here.
-/

noncomputable section

namespace GameTheory
namespace FTVEpsilonPerturbedCycleExclusion

open Math.Probability Math.ProbabilityMassFunction
open FTVCyclicMinimality
open FTVCyclicMinimality.ExactCyclicPacket (standardPromise)
open FTVCyclicAdmissibleCycle (ftvReward ftvReward_singletonTerminal phaseRoot halfCoin
  halfCoin_true_toReal halfCoin_false_toReal phaseSimplexRoot phasePoint ftvBlock
  quittingRootOfSimplex_phaseSimplexRoot)

/-! ## The cyclic predecessor -/

/-- The cyclic predecessor on the three FTV phases: the inverse of
`FTVCyclicMinimality.nextThree`. -/
def prevThree : Player → Player := ![2, 0, 1]

@[simp] theorem nextThree_prevThree (i : Player) : nextThree (prevThree i) = i := by
  fin_cases i <;> rfl

@[simp] theorem prevThree_nextThree (i : Player) : prevThree (nextThree i) = i := by
  fin_cases i <;> rfl

theorem prevThree_ne (i : Player) : prevThree i ≠ i := by fin_cases i <;> decide

/-! ## The weight -/

/-- The `ε`-perturbation of the FTV table: the unperturbed weight
(`FTVCyclicAdmissibleCycle.ftvReward`) plus a bonus `ε` at coordinate `who`
exactly when the quitting coalition is `who`'s own cyclic pair
`{who, nextThree who}`.  This reproduces the published table: e.g. at
`quitters = {0,1}` the bonus fires at `who = 0` (since `{0,1} = {0,
nextThree 0}`), giving `r_0({0,1}) = 1 + ε` while `r_1({0,1})` and
`r_2({0,1})` are untouched -- exactly `r({1,2}) = (1+ε, 0, 1)` in the
paper's `1`-indexed players. -/
def ftvRewardEps (ε : ℝ) (quitters : {S : Finset Player // S.Nonempty}) :
    Payoff Player :=
  fun who =>
    ftvReward quitters who + (if quitters.1 = {who, nextThree who} then ε else 0)

/-- At `ε = 0` the perturbed weight is literally the unperturbed one. -/
@[simp] theorem ftvRewardEps_zero : ftvRewardEps 0 = ftvReward := by
  funext quitters who
  simp [ftvRewardEps]

/-! ## Deliverable 1: not zero-solo -/

/-- The perturbation never touches a singleton coalition, so every solo value
is exactly the unperturbed one. -/
theorem ftvRewardEps_singletonTerminal (ε : ℝ) (who : Player) :
    ftvRewardEps ε (quittingSingletonTerminal who) who = 1 := by
  have hbonus : ¬ (({who} : Finset Player) = {who, nextThree who}) := by
    fin_cases who <;> decide
  simp only [ftvRewardEps, quittingSingletonTerminal, hbonus, if_false, add_zero]
  rw [show (⟨{who}, Finset.singleton_nonempty who⟩ :
      {S : Finset Player // S.Nonempty}) = quittingSingletonTerminal who from rfl,
    ftvReward_singletonTerminal]
  exact soloReward_self who

/-- **Deliverable 1.** The `ε`-perturbed weight is not zero-solo: every solo
value equals `1 > 0`. -/
theorem not_isQuittingZeroSolo_ftvRewardEps (ε : ℝ) :
    ¬ IsQuittingZeroSolo (ftvRewardEps ε) := by
  intro hzero
  have h := hzero 0
  rw [ftvRewardEps_singletonTerminal] at h
  norm_num at h

/-! ## Numeric facts feeding both period-one and period-three results -/

/-- Every solo value of the perturbed weight is `1`, matching the unperturbed
table: perturbation only ever touches two-quitter coalitions. -/
theorem ftvRewardEps_soloSelf (ε : ℝ) (i : Player) :
    quittingSoloReward (ftvRewardEps ε) i i = 1 :=
  ftvRewardEps_singletonTerminal ε i

/-- The unperturbed collision reward at the pair `{i, prevThree i}`, read at
its non-bonus coordinate `prevThree i`, is `1` for every `i`: this is the
`r_j({i,j}) = 1` entry the hand computation reads off the printed table. -/
theorem ftvReward_collision_prevThree (i : Player) :
    quittingSingletonCollisionReward ftvReward i (prevThree i) = 1 := by
  fin_cases i <;> rfl

/-- The perturbed collision reward at `{i, prevThree i}`, read at `prevThree
i`, carries the bonus: `{i, prevThree i} = {prevThree i, nextThree
(prevThree i)}` since `nextThree (prevThree i) = i`, so this is exactly the
coordinate the bonus targets. -/
theorem ftvRewardEps_collision_prevThree (ε : ℝ) (i : Player) :
    quittingSingletonCollisionReward (ftvRewardEps ε) i (prevThree i) = 1 + ε := by
  have hcond : (({i, prevThree i} : Finset Player) =
      {prevThree i, nextThree (prevThree i)}) := by
    rw [nextThree_prevThree]; exact Finset.pair_comm i (prevThree i)
  have hbase := ftvReward_collision_prevThree i
  unfold quittingSingletonCollisionReward at hbase ⊢
  unfold ftvRewardEps
  dsimp only
  rw [if_pos hcond]
  linarith [hbase]

/-- The unperturbed solo reward `r_j({i})` at `j = prevThree i` is `0`, for
every `i`: this is the printed table's `r_j({i}) = 0` entry that anchors the
right-hand side of the no-join inequality at each of the three coordinates. -/
theorem ftvReward_soloOther_prevThree (i : Player) :
    quittingSoloReward ftvReward i (prevThree i) = 0 := by
  fin_cases i <;> rfl

/-- The perturbation never touches a singleton coalition, so the previous
fact survives unchanged for the perturbed weight. -/
theorem ftvRewardEps_soloOther_prevThree (ε : ℝ) (i : Player) :
    quittingSoloReward (ftvRewardEps ε) i (prevThree i) = 0 := by
  have hbonus : ¬ (({i} : Finset Player) = {prevThree i, nextThree (prevThree i)}) := by
    rw [nextThree_prevThree]
    fin_cases i <;> decide
  change ftvRewardEps ε (quittingSingletonTerminal i) (prevThree i) = 0
  simp only [ftvRewardEps, quittingSingletonTerminal, hbonus, if_false, add_zero]
  rw [show (⟨{i}, Finset.singleton_nonempty i⟩ :
      {S : Finset Player // S.Nonempty}) = quittingSingletonTerminal i from rfl,
    ftvReward_singletonTerminal]
  fin_cases i <;> rfl

/-! ## Deliverable 2: no period-one cycle -/

/-- **The affine no-join condition fails at every coordinate, for every
non-negative rate.**  `QuittingSoloQuitterCriterion` is the repository's own
name (`QuittingSoloQuitterEquilibrium.lean`) for the classical affine
no-join condition of `FRONTIER.md`.  Tested at owner `i` against opponent
`j = prevThree i`, it reads `(1-p)·r_j({j}) + p·r_j({i,j}) ≤ r_j({i})`, i.e.
`(1-p)·1 + p·(1+ε) ≤ 0`, i.e. `1 + p·ε ≤ 0` -- false for every `p ≥ 0` once
`ε ≥ 0`.  Stated at every `i`, matching the cyclic symmetry of the hand
computation. -/
theorem not_quittingSoloQuitterCriterion_ftvRewardEps
    (ε : ℝ) (hε : 0 ≤ ε) (i : Player) (p : ℝ) (hp : 0 ≤ p) :
    ¬ QuittingSoloQuitterCriterion (ftvRewardEps ε) i p := by
  intro hcrit
  have hfail := hcrit (prevThree i) (prevThree_ne i)
  rw [ftvRewardEps_soloSelf, ftvRewardEps_collision_prevThree,
    ftvRewardEps_soloOther_prevThree] at hfail
  nlinarith [mul_nonneg hp hε]

/-- **Deliverable 2, strongest form.**  No period-one block whose row
isolates a single coordinate as the sole possible quitter is an admissible
cyclic-continuation block for the perturbed weight -- for *every* owner,
*every* absorbing hazard, and *every* terminal vector, not merely against the
specific rate-`p` family the no-join criterion tests.  The value recursion
forces `terminal` to equal the owner's own solo reward (the unique fixed
point of an absorbing row,
`quittingCyclicContinuation_unique_of_absorbing_period_one`); against that
forced value, exact endpoint Nash is equivalent to
`QuittingSoloQuitterCriterion`
(`isεQuittingRootEndpointNash_soloStationaryRoot_iff`), which always fails by
`not_quittingSoloQuitterCriterion_ftvRewardEps`.

This does **not** cover period-one rows at which two or three coordinates
mix between quit and continue simultaneously: the repository has no
period-one Nash machinery for that shape, so blocks of that form are outside
this theorem's scope. -/
theorem not_isQuittingCyclicContinuationBlock_of_isolated
    (ε : ℝ) (hε : 0 ≤ ε) (owner : Player) (hazard : PMF Bool)
    (habsorb : 0 < (hazard true).toReal) (terminal : Payoff Player)
    (block : QuittingFiniteNashBellmanPath Player 1)
    (hroot : quittingRootOfSimplex (block 0).2 =
      quittingSoloStationaryRoot owner hazard) :
    ¬ IsQuittingCyclicContinuationBlock (ftvRewardEps ε) terminal 1 block := by
  intro hblock
  have hfixed := quittingCyclicContinuationBlock_one_fixed (ftvRewardEps ε)
    terminal block hblock
  rw [hroot] at hfixed
  have habsorbMass : 0 < quittingRootAbsorptionMass
      (quittingSoloStationaryRoot owner hazard) := by
    rw [quittingRootAbsorptionMass_soloStationaryRoot]; exact habsorb
  have hterminal : terminal = quittingSoloReward (ftvRewardEps ε) owner :=
    quittingCyclicContinuation_unique_of_absorbing_period_one (ftvRewardEps ε)
      terminal (quittingSoloReward (ftvRewardEps ε) owner)
      (quittingSoloStationaryRoot owner hazard) hfixed
      (quittingRootSuccessorPayoff_soloStationaryRoot_self (ftvRewardEps ε)
        owner hazard).symm habsorbMass
  have hlast : (block (Fin.succ 0)).1 = terminal := hblock.1.2.1
  have hcast : Fin.castSucc (0 : Fin 1) = (0 : Fin 2) := rfl
  have hnash := (hblock.1.2.2 0).2
  rw [hcast, hlast, hroot, hterminal,
    isεQuittingRootEndpointNash_soloStationaryRoot_iff] at hnash
  have hsum := quittingSoloHazardMass_add hazard
  have hfail := hnash (prevThree owner) (prevThree_ne owner)
  rw [ftvRewardEps_soloSelf, ftvRewardEps_collision_prevThree,
    ftvRewardEps_soloOther_prevThree] at hfail
  nlinarith [mul_nonneg (hazard true).toReal_nonneg hε]

/-! ## Deliverable 3: the unperturbed period-three block fails -/

/-- The phase-`c` row is exactly the solo-stationary root at owner `c` with
the fair-coin hazard. -/
theorem phaseRoot_eq_soloStationaryRoot (c : Player) :
    phaseRoot c = quittingSoloStationaryRoot c halfCoin := by
  funext who
  by_cases h : who = c
  · subst h; simp [phaseRoot, quittingSoloStationaryRoot]
  · simp [phaseRoot, quittingSoloStationaryRoot, h]

/-- The continuation promise for phase `c`'s edge, read at the silent
"creditor" coordinate `prevThree c`, is `2` at every phase. -/
theorem standardPromise_value (c : Player) :
    standardPromise (nextThree c) (prevThree c) = 2 := by
  fin_cases c <;> rfl

/-- **The exact `ε/2` deviation, recomputed from the repository's own
endpoint formulas.**  At phase `c`, deviating the silent coordinate
`prevThree c` to sure-quit against owner `c` mixing at `1/2` pays
`½·r_{prevThree c}({prevThree c}) + ½·r_{prevThree c}({c, prevThree c}) =
½·1 + ½·(1+ε) = 1 + ε/2`; continuing pays `½·r_{prevThree c}({c}) +
½·(promise) = ½·0 + ½·2 = 1`.  The gap is exactly `ε/2`, reproducing the
hand computation. -/
theorem quittingRootEndpointDifference_phaseRoot_eps (ε : ℝ) (c : Player) :
    quittingRootEndpointDifference (ftvRewardEps ε) (standardPromise (nextThree c))
        (phaseRoot c) (prevThree c) = ε / 2 := by
  rw [phaseRoot_eq_soloStationaryRoot]
  unfold quittingRootEndpointDifference
  rw [quittingRootQuitPayoff_soloStationaryRoot_other (ftvRewardEps ε) (prevThree_ne c),
    quittingRootContinuePayoff_soloStationaryRoot_other (ftvRewardEps ε) (prevThree_ne c),
    ftvRewardEps_soloSelf, ftvRewardEps_collision_prevThree,
    ftvRewardEps_soloOther_prevThree, standardPromise_value,
    halfCoin_true_toReal, halfCoin_false_toReal]
  ring

/-- **The phase-`c` row fails exact (`ε = 0`) endpoint Nash for the
perturbed weight, at any `ε > 0`.**  The silent coordinate `prevThree c`
strictly prefers to deviate, by exactly `ε/2`. -/
theorem not_isεQuittingRootEndpointNash_phaseRoot_eps
    (ε : ℝ) (hε : 0 < ε) (c : Player) :
    ¬ IsεQuittingRootEndpointNash (ftvRewardEps ε) (standardPromise (nextThree c)) 0
      (phaseRoot c) := by
  intro hnash
  have hdiff := quittingRootEndpointDifference_phaseRoot_eps ε c
  have hcontinueMass : (phaseRoot c (prevThree c) false).toReal = 1 := by
    rw [phaseRoot_eq_soloStationaryRoot,
      quittingSoloStationaryRoot_apply_other (prevThree_ne c)]
    simp
  have hbound := (hnash (prevThree c)).1
  rw [hcontinueMass, one_mul, hdiff] at hbound
  linarith

/-- **Deliverable 3.**  `FTVCyclicAdmissibleCycle.ftvBlock` -- the *exact
same* three-phase block that is an admissible cyclic-continuation block for
the unperturbed table -- is **not** an `IsQuittingCyclicContinuationBlock`
for the `ε`-perturbed weight, at any `ε > 0`.  Only phase `0`'s edge is
examined; this is a statement about *this specific block*, not about every
period-three block for this weight. -/
theorem not_isQuittingCyclicContinuationBlock_ftvBlock_ftvRewardEps
    (ε : ℝ) (hε : 0 < ε) :
    ¬ IsQuittingCyclicContinuationBlock (ftvRewardEps ε) namedTarget 3 ftvBlock := by
  intro hblock
  have hedge : IsQuittingNashBellmanEdge (ftvRewardEps ε) (phasePoint 0) (phasePoint 1) :=
    hblock.1.2.2 (0 : Fin 3)
  apply not_isεQuittingRootEndpointNash_phaseRoot_eps ε hε 0
  have hnash := hedge.2
  simp only [phasePoint, quittingRootOfSimplex_phaseSimplexRoot] at hnash
  exact hnash

end FTVEpsilonPerturbedCycleExclusion
end GameTheory
