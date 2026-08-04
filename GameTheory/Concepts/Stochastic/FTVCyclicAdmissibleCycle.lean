/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.FTVCyclicMinimality
import GameTheory.Concepts.Stochastic.QuittingZeroSoloDisjunct

/-!
# The canonical three-player quitting table goes through the cycle reduction

`FTVCyclicMinimality` carries the Flesch--Thuijsman--Vrieze three-player
quitting table

`r({0}) = (1, 3, 0)`, `r({1}) = (0, 1, 3)`, `r({2}) = (3, 0, 1)`,
`r({0,1}) = (1, 0, 1)`, `r({0,2}) = (0, 1, 1)`, `r({1,2}) = (1, 1, 0)`,
`r({0,1,2}) = (0, 0, 0)`,

together with the exact three-phase packet `standardPacket`: at phase `c`
coordinate `c` quits with probability `1/2` and the other two are silent, and
the promise word is `(1,2,1) → (1,1,2) → (2,1,1) → (1,2,1)`.  That file proves
the *value recursion* of the packet and its rigidity, but never connects it to
the quitting game itself.

This file makes the connection and runs the table through the landed
absorbing-cycle reduction of `QuittingZeroSoloDisjunct`:

* `ftvBlock_isQuittingCyclicContinuationBlock` — the three phases assemble into
  an `IsQuittingCyclicContinuationBlock` for the terminal vector `(1,2,1)`.
  The value clause is the packet's own `q1` (`standardPromise_recursion`); what
  is added here is the per-stage *exact* endpoint-Nash certificate
  (`endpointDifference_phaseRoot`, `isZeroEndpointNash_phaseRoot`) and the
  absorption clause (all-continue mass `1/2` at every phase, so `1/8` around
  the cycle).
* `isQuittingCycleAdmissible_ftvBlockCycle` — admissibility, on the
  nonnegative-solo branch: every solo weight of this table is `1 > 0`.
* `isUniformEquilibriumPayoff_namedTarget` — the conclusion, with the payoff
  identified as `(1, 2, 1)`.

## Why this table

It is the standard witness that stationary strategies are not enough: it has
no stationary `ε`-equilibrium for small `ε` (Flesch--Thuijsman--Vrieze,
*Cyclic Markov equilibria in stochastic games*, IJGT 26(3), 303--314, 1997,
Theorem 3.2; the abstract's unqualified "(ε > 0)" reading is loose -- payoffs
lie in `[0,3]`, so every stationary profile is trivially a `3`-equilibrium,
and only the small-`ε` reading is correct -- see the record at
`ideas/UniformEquilibriumLiterature/` in
`FTVCyclicGameHasNoStationaryApproximateEquilibria.md`).  So it is exactly the
case the absorbing-cycle carrier was built for, and it is a case where
admissibility is *automatic* rather than assumed.

## Scale

No rescaling is used.  Every bound consumed downstream is
`quittingRewardBound reward = ∑_S ∑_i |r_S(i)|`, the table's own canonical
bound, and the cycle notions are scale-homogeneous; nothing in the chain from
`IsQuittingCyclicContinuationBlock` to `IsUniformEquilibriumPayoff` assumes a
reward bound of `1`.  The only place a numeric bound is needed is membership in
`quittingNashBellmanBox (quittingRewardBound ftvReward)`, which asks for
`|promise| ≤ quittingRewardBound ftvReward`; the promise entries are at most
`2` and `three_le_quittingRewardBound` supplies `3 ≤ quittingRewardBound
ftvReward` from a single table entry.

## What this does not claim

Nothing here says the cycle is the *only* equilibrium, nor that `(1,2,1)` is
the only uniform-equilibrium payoff.  The nonexistence of a stationary
`ε`-equilibrium for this table is *not* formalized here; it is the reason the
table is interesting, not a hypothesis or a conclusion of anything below.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace FTVCyclicAdmissibleCycle

open StochasticGame Filter Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction
open FTVCyclicMinimality
open FTVCyclicMinimality.ExactCyclicPacket (standardPacket standardPromise
  standardQuitProb nextPhase_three survivalProbability_singleRole
  terminalExpectation_singleRole)

/-! ## The table as a quitting weight -/

/-- The FTV terminal table presented on nonempty quitter sets, the shape the
quitting game consumes.  It is `FTVCyclicMinimality.terminalReward` read
through the indicator of the quitter set. -/
def ftvReward (quitters : {S : Finset Player // S.Nonempty}) : Payoff Player :=
  terminalReward fun who ↦ decide (who ∈ quitters.1)

/-- The presentation is faithful: on the quitter set of a pure action row the
weight is the original `FTVCyclicMinimality` row. -/
theorem ftvReward_quitters (action : Player → Bool)
    (h : (quittingQuitters action).Nonempty) :
    ftvReward ⟨quittingQuitters action, h⟩ = terminalReward action := by
  have hind : (fun who ↦ decide (who ∈ quittingQuitters action)) = action := by
    funext who
    by_cases hwho : action who
    · simp [quittingQuitters, hwho]
    · simp [quittingQuitters, hwho]
  change terminalReward (fun who ↦ decide (who ∈ quittingQuitters action)) = _
  rw [hind]

/-- Solo quitting pays the original solo reward vector. -/
@[simp] theorem ftvReward_singletonTerminal (who : Player) :
    ftvReward (quittingSingletonTerminal who) = soloReward who := by
  fin_cases who <;> rfl

/-- The one-stage row payoff of the FTV weight against a continuation. -/
theorem quittingRootPayoff_ftv (tail : Payoff Player) (action : Player → Bool)
    (who : Player) :
    quittingRootPayoff ftvReward tail action who =
      if (quittingQuitters action).Nonempty then terminalReward action who
      else tail who := by
  unfold quittingRootPayoff
  by_cases h : (quittingQuitters action).Nonempty
  · rw [dif_pos h, if_pos h]
    exact congrFun (ftvReward_quitters action h) who
  · rw [dif_neg h, if_neg h]

/-- A displayed three-coordinate action row has a quitter exactly when one of
its coordinates is `true`. -/
theorem quittingQuitters_vec_nonempty (a b d : Bool) :
    (quittingQuitters ![a, b, d]).Nonempty ↔ a = true ∨ b = true ∨ d = true := by
  constructor
  · rintro ⟨who, hwho⟩
    fin_cases who <;> simp_all [quittingQuitters]
  · rintro (ha | hb | hd)
    · exact ⟨0, by simp [quittingQuitters, ha]⟩
    · exact ⟨1, by simp [quittingQuitters, hb]⟩
    · exact ⟨2, by simp [quittingQuitters, hd]⟩

/-- The one-stage row payoff on a displayed action row, with the absorption
test already decided.  This is the form the phase computations consume. -/
@[simp] theorem quittingRootPayoff_ftv_vec (tail : Payoff Player) (a b d : Bool)
    (who : Player) :
    quittingRootPayoff ftvReward tail ![a, b, d] who =
      if a || b || d then terminalReward ![a, b, d] who else tail who := by
  rw [quittingRootPayoff_ftv]
  refine if_congr ?_ rfl rfl
  rw [quittingQuitters_vec_nonempty]
  cases a <;> cases b <;> cases d <;> simp

/-! ## The three phase rows -/

/-- Fubini expansion of a product of three Boolean mixed actions. -/
theorem expect_pmfPi_fin3_bool (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma 0) fun a ↦
        expect (sigma 1) fun b ↦
          expect (sigma 2) fun d ↦ f ![a, b, d] := by
  classical
  have h0 : Function.update sigma 0 (sigma 0) = sigma :=
    Function.update_eq_self 0 sigma
  rw [← h0, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 0))
  funext a
  have h1 : Function.update (Function.update sigma 0 (PMF.pure a)) 1 (sigma 1) =
      Function.update sigma 0 (PMF.pure a) := by
    funext who
    fin_cases who <;> simp
  rw [← h1, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 1))
  funext b
  have h2 : Function.update
      (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
      2 (sigma 2) =
      Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b) := by
    funext who
    fin_cases who <;> simp
  rw [← h2, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma 2))
  funext d
  have hpure : Function.update
      (Function.update (Function.update sigma 0 (PMF.pure a)) 1 (PMF.pure b))
      2 (PMF.pure d) = fun who ↦ PMF.pure (![a, b, d] who) := by
    funext who
    fin_cases who <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

/-- The fair quit/continue coin, reusing the repository's Boolean coin. -/
def halfCoin : PMF Bool :=
  QuittingBoundedSurgeryDescentCounterexample.coin (1 / 2) (by norm_num)
    (by norm_num)

@[simp] theorem halfCoin_true_toReal : (halfCoin true).toReal = 1 / 2 := by
  simp [halfCoin]

@[simp] theorem halfCoin_false_toReal : (halfCoin false).toReal = 1 / 2 := by
  norm_num [halfCoin]

@[simp] theorem expect_halfCoin (f : Bool → ℝ) :
    expect halfCoin f = 1 / 2 * f true + 1 / 2 * f false := by
  rw [expect_eq_sum, Fintype.sum_bool, halfCoin_true_toReal, halfCoin_false_toReal]

@[simp] theorem pureFalse_false_toReal :
    ((PMF.pure false : PMF Bool) false).toReal = 1 := by simp

@[simp] theorem pureFalse_true_toReal :
    ((PMF.pure false : PMF Bool) true).toReal = 0 := by simp

/-- At phase `c` coordinate `c` quits with probability one half and the other
two coordinates are silent.  This is `standardQuitProb c` read as a product of
Boolean laws; see `phaseRoot_quitProbability`. -/
def phaseRoot (c : Player) : Player → PMF Bool :=
  fun who ↦ if who = c then halfCoin else PMF.pure false

/-- The phase rows carry exactly the packet's quitting matrix. -/
theorem phaseRoot_quitProbability (c who : Player) :
    (phaseRoot c who true).toReal = standardQuitProb c who := by
  fin_cases c <;> fin_cases who <;> simp [phaseRoot, standardQuitProb]

/-! ## The value recursion, imported from the packet -/

/-- The packet's `(Q1)` at the standard data, in the form the quitting-game
Bellman step produces: half the solo reward of the active coordinate plus half
the promise at the next phase.  Nothing is recomputed here; this is
`standardPacket.q1` with the two `singleRole` evaluations applied. -/
theorem standardPromise_recursion (c : Player) :
    standardPromise c =
      (1 / 2 : ℝ) • soloReward c + (1 / 2 : ℝ) • standardPromise (nextThree c) := by
  have h := standardPacket.q1 c
  change standardPromise c =
    survivalProbability (fun who ↦ if who = c then (1 / 2 : ℝ) else 0) •
        standardPromise (nextPhase 3 c) +
      terminalExpectation (fun who ↦ if who = c then (1 / 2 : ℝ) else 0) at h
  rw [survivalProbability_singleRole, terminalExpectation_singleRole,
    nextPhase_three] at h
  rw [h, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  exact add_comm _ _

/-- **The one-stage Bellman step of a phase row.**  At phase `c` only two
events have positive probability: coordinate `c` quits alone, or nobody quits,
each with probability one half. -/
theorem quittingRootSuccessorPayoff_phaseRoot (c : Player) (tail : Payoff Player) :
    quittingRootSuccessorPayoff ftvReward tail (phaseRoot c) =
      (1 / 2 : ℝ) • soloReward c + (1 / 2 : ℝ) • tail := by
  funext who
  change quittingRootExpectedPayoff ftvReward tail (phaseRoot c) who = _
  unfold quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool]
  fin_cases c <;> fin_cases who <;>
    simp [phaseRoot, terminalReward, soloReward, Matrix.cons_val_two,
      expect_pure]

/-! ## The exact endpoint-Nash certificate -/

/-- **The exact endpoint gaps of a phase row against the promise word.**  The
active coordinate `c` is exactly indifferent; its cyclic successor strictly
prefers to continue, by `3/2`; the third coordinate is again exactly
indifferent.  All three gaps are `≤ 0`, which is exactly what exact endpoint
Nash asks of the two silent coordinates, and the active one's gap is `0`, which
is what it asks of a coordinate mixing strictly inside. -/
theorem endpointDifference_phaseRoot (c who : Player) :
    quittingRootEndpointDifference ftvReward (standardPromise (nextThree c))
        (phaseRoot c) who =
      if who = nextThree c then -(3 / 2 : ℝ) else 0 := by
  unfold quittingRootEndpointDifference quittingRootQuitPayoff
    quittingRootContinuePayoff quittingRootExpectedPayoff
  rw [expect_pmfPi_fin3_bool, expect_pmfPi_fin3_bool]
  fin_cases c <;> fin_cases who <;>
    simp [phaseRoot, terminalReward, standardPromise, nextThree,
      Matrix.cons_val_two, expect_pure] <;> norm_num

/-- The gaps are nonpositive at every coordinate. -/
theorem endpointDifference_phaseRoot_nonpos (c who : Player) :
    quittingRootEndpointDifference ftvReward (standardPromise (nextThree c))
      (phaseRoot c) who ≤ 0 := by
  rw [endpointDifference_phaseRoot]
  split <;> norm_num

/-- The active coordinate is exactly indifferent. -/
theorem endpointDifference_phaseRoot_self (c : Player) :
    quittingRootEndpointDifference ftvReward (standardPromise (nextThree c))
      (phaseRoot c) c = 0 := by
  rw [endpointDifference_phaseRoot]
  fin_cases c <;> simp [nextThree]

/-- **The phase row is exactly (`ε = 0`) endpoint Nash against the next
promise.** -/
theorem isZeroEndpointNash_phaseRoot (c : Player) :
    IsεQuittingRootEndpointNash ftvReward (standardPromise (nextThree c)) 0
      (phaseRoot c) := by
  intro who
  rw [endpointDifference_phaseRoot]
  fin_cases c <;> fin_cases who <;> simp [phaseRoot, nextThree] <;> norm_num

/-! ## Absorption and opponent survival -/

/-- Every phase row absorbs with probability one half. -/
theorem quittingRootAbsorptionMass_phaseRoot (c : Player) :
    quittingRootAbsorptionMass (phaseRoot c) = 1 / 2 := by
  rw [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability, Fin.prod_univ_three]
  fin_cases c <;> simp [phaseRoot] <;> norm_num

/-- The deleted (opponent) survival mass of a phase row: `1` at the active
coordinate, `1/2` at the two silent ones. -/
theorem fixedOpponentsContinueMass_phaseRoot (c who : Player) :
    quittingStationaryFixedOpponentsContinueMass (phaseRoot c) who =
      if who = c then 1 else 1 / 2 := by
  change quittingStationaryContinueMass
    (Function.update (phaseRoot c) who (PMF.pure false)) = _
  rw [quittingStationaryContinueMass_eq_prod_continueProbability,
    Fin.prod_univ_three]
  fin_cases c <;> fin_cases who <;> simp [phaseRoot]

/-! ## The block -/

/-- Simplex presentation of the phase row. -/
def phaseSimplexRoot (c : Player) : QuittingRootSimplex Player :=
  fun who ↦ stdSimplexEquiv (phaseRoot c who)

@[simp] theorem quittingRootOfSimplex_phaseSimplexRoot (c : Player) :
    quittingRootOfSimplex (phaseSimplexRoot c) = phaseRoot c := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (phaseRoot c who)

/-- The displayed Nash--Bellman point of phase `c`. -/
def phasePoint (c : Player) : QuittingNashBellmanPoint Player :=
  (standardPromise c, phaseSimplexRoot c)

/-- **The length-three cyclic block**: phases `0, 1, 2` and then back to the
displayed value of phase `0`, which is the anchored terminal vector. -/
def ftvBlock : QuittingFiniteNashBellmanPath Player 3 :=
  ![phasePoint 0, phasePoint 1, phasePoint 2, phasePoint 0]

/-- The table's canonical reward bound dominates `3`, hence dominates every
promise entry.  Read off one entry of one row; the exact value of the bound is
irrelevant. -/
theorem three_le_quittingRewardBound : (3 : ℝ) ≤ quittingRewardBound ftvReward := by
  have h := abs_reward_le_quittingRewardBound ftvReward
    (quittingSingletonTerminal 0) 1
  rw [ftvReward_singletonTerminal] at h
  simpa [soloReward] using h

theorem phasePoint_mem_box (c : Player) :
    phasePoint c ∈ quittingNashBellmanBox (quittingRewardBound ftvReward) := by
  have h3 := three_le_quittingRewardBound
  change standardPromise c ∈
    Set.Icc (fun _ : Player ↦ -(quittingRewardBound ftvReward))
      (fun _ ↦ quittingRewardBound ftvReward)
  constructor
  · intro who
    fin_cases c <;> fin_cases who <;> simp [standardPromise] <;> linarith
  · intro who
    fin_cases c <;> fin_cases who <;> simp [standardPromise] <;> linarith

/-- Every stage of the block is an exact Nash--Bellman edge: the value clause
is the packet's recursion, the Nash clause the endpoint certificate. -/
theorem isEdge_phasePoint (c : Player)
    (tailPoint : QuittingNashBellmanPoint Player)
    (htail : tailPoint.1 = standardPromise (nextThree c)) :
    IsQuittingNashBellmanEdge ftvReward (phasePoint c) tailPoint := by
  constructor
  · change standardPromise c = quittingRootSuccessorPayoff ftvReward tailPoint.1
      (quittingRootOfSimplex (phaseSimplexRoot c))
    rw [htail, quittingRootOfSimplex_phaseSimplexRoot,
      quittingRootSuccessorPayoff_phaseRoot]
    exact standardPromise_recursion c
  · change IsεQuittingRootEndpointNash ftvReward tailPoint.1 0
      (quittingRootOfSimplex (phaseSimplexRoot c))
    rw [htail, quittingRootOfSimplex_phaseSimplexRoot]
    exact isZeroEndpointNash_phaseRoot c

/-- **The FTV table's three-phase block is an absorbing cyclic continuation
block for the named target `(1, 2, 1)`.** -/
theorem ftvBlock_isQuittingCyclicContinuationBlock :
    IsQuittingCyclicContinuationBlock ftvReward namedTarget 3 ftvBlock := by
  refine ⟨⟨?_, ?_, ?_⟩, rfl, ⟨0, ?_⟩⟩
  · intro time
    fin_cases time <;> exact phasePoint_mem_box _
  · rfl
  · intro time
    fin_cases time
    · exact isEdge_phasePoint 0 _ rfl
    · exact isEdge_phasePoint 1 _ rfl
    · exact isEdge_phasePoint 2 _ rfl
  · change 0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex (phaseSimplexRoot 0))
    rw [quittingRootOfSimplex_phaseSimplexRoot,
      quittingRootAbsorptionMass_phaseRoot]
    norm_num

/-- The block's cycle of rows is exactly the three phase rows. -/
@[simp] theorem quittingCyclicContinuationBlockCycle_ftvBlock (stage : Fin 3) :
    quittingCyclicContinuationBlockCycle 2 ftvBlock stage = phaseRoot stage := by
  fin_cases stage <;>
    exact quittingRootOfSimplex_phaseSimplexRoot _

/-! ## Admissibility is automatic here -/

/-- **Admissibility, on the nonnegative-solo branch.**  A mismatch can be
nonzero only at a coordinate whose deleted survival product around the cycle is
`1` *and* whose solo weight is strictly negative.  Every solo weight of this
table is `soloReward who who = 1 > 0`, so the second branch of
`IsQuittingCycleZeroDeviationMismatchAt` closes every coordinate outright and
the cycle's survival products are never inspected. -/
theorem isQuittingCycleAdmissible_ftvBlockCycle :
    IsQuittingCycleAdmissible ftvReward
      (quittingCyclicContinuationBlockCycle 2 ftvBlock) := by
  intro who
  refine Or.inr ?_
  rw [ftvReward_singletonTerminal, soloReward_self]
  norm_num

/-- The joint all-continue mass around the whole cycle is `1/8`: three
independent stages each surviving with probability `1/2`.  This is the
quantitative content of the block's absorption clause. -/
theorem prod_continueMass_ftvBlockCycle :
    (∏ stage : Fin 3, quittingStationaryContinueMass
      (quittingCyclicContinuationBlockCycle 2 ftvBlock stage)) = 1 / 8 := by
  have hmass : ∀ c : Player, quittingStationaryContinueMass (phaseRoot c) = 1 / 2 := by
    intro c
    have h := quittingRootAbsorptionMass_phaseRoot c
    rw [quittingRootAbsorptionMass] at h
    linarith
  rw [Fin.prod_univ_three]
  simp only [quittingCyclicContinuationBlockCycle_ftvBlock, hmass]
  norm_num

/-- The contracting branch happens to hold here as well: the deleted survival
product at every coordinate is `1/4`.  Recorded for contrast with the surgery
table of `QuittingAdmissibleCycleTerminalEquilibrium`, where the contracting
branch genuinely fails and only the solo branch is available. -/
theorem prod_fixedOpponentsContinueMass_ftvBlockCycle (who : Player) :
    (∏ stage : Fin 3, quittingStationaryFixedOpponentsContinueMass
      (quittingCyclicContinuationBlockCycle 2 ftvBlock stage) who) = 1 / 4 := by
  rw [Fin.prod_univ_three]
  simp only [quittingCyclicContinuationBlockCycle_ftvBlock,
    fixedOpponentsContinueMass_phaseRoot]
  fin_cases who <;> simp <;> norm_num

/-! ## The conclusion -/

/-- The table is **not** zero-solo, so the other disjunct of the reduction does
not apply to it: every solo weight is `1 > 0`. -/
theorem not_isQuittingZeroSolo_ftvReward : ¬ IsQuittingZeroSolo ftvReward := by
  intro hzero
  have h := hzero 0
  rw [ftvReward_singletonTerminal, soloReward_self] at h
  norm_num at h

/-- The FTV weight admits an admissible absorbing quitting cycle. -/
theorem hasAdmissibleAbsorbingQuittingCycle_ftvReward :
    HasAdmissibleAbsorbingQuittingCycle ftvReward :=
  ⟨namedTarget, 2, ftvBlock, ftvBlock_isQuittingCyclicContinuationBlock,
    isQuittingCycleAdmissible_ftvBlockCycle⟩

/-- The periodic profile generated by the block, started at phase zero. -/
def ftvCyclicProfile : (quittingGame ftvReward).BehaviorProfile :=
  quittingCyclicContinuationBlockProfile ftvReward 2 ftvBlock 0

/-- The periodic profile is an *exact* terminal Nash profile, against all
behavioral deviations. -/
theorem isZeroAsymptoticNash_ftvCyclicProfile :
    (quittingGame ftvReward).IsεAsymptoticNash
      (quittingTerminalPayoff ftvReward) 0 ftvCyclicProfile :=
  isZeroAsymptoticNash_quittingCyclicContinuationBlockProfile ftvReward
    namedTarget 2 ftvBlock ftvBlock_isQuittingCyclicContinuationBlock
    isQuittingCycleAdmissible_ftvBlockCycle 0

/-- Its realized terminal payoff is the named target `(1, 2, 1)`. -/
theorem quittingTerminalPayoff_ftvCyclicProfile :
    quittingTerminalPayoff ftvReward ftvCyclicProfile = namedTarget :=
  quittingTerminalPayoff_quittingCyclicContinuationBlockProfile ftvReward
    namedTarget 2 ftvBlock ftvBlock_isQuittingCyclicContinuationBlock

/-- **The canonical hard three-player quitting table has the uniform
equilibrium payoff `(1, 2, 1)`.**

`HEADLINE` — the first instance of the Flesch--Thuijsman--Vrieze table being
discharged through the absorbing-cycle carrier: the three-phase cycle of
`FTVCyclicMinimality.standardPacket` is an absorbing exact Nash--Bellman block
whose deviation mismatch vanishes automatically (every solo weight is `1 > 0`),
so `exists_uniformEquilibriumPayoff_of_admissible_quittingCyclicContinuationBlock`
applies and the realized payoff is the packet's named target.

What it does **not** cover: it says nothing about uniqueness of this payoff, it
does not formalize the classical fact that this table has no stationary
`ε`-equilibrium, and it is an instance rather than a step toward completeness
of the zero-solo/cycle disjunction, which remains open. -/
theorem isUniformEquilibriumPayoff_namedTarget :
    (quittingGame ftvReward).IsUniformEquilibriumPayoff none namedTarget := by
  have huniform := quittingGame_isUniformEquilibriumPayoff_of_terminalNash_exact
    ftvReward ftvCyclicProfile isZeroAsymptoticNash_ftvCyclicProfile
  rwa [quittingTerminalPayoff_ftvCyclicProfile] at huniform

/-- Existential form, obtained from the disjunctive reduction itself. -/
theorem exists_uniformEquilibriumPayoff_ftvReward :
    ∃ payoff : Payoff Player,
      (quittingGame ftvReward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle ftvReward
    (Or.inr hasAdmissibleAbsorbingQuittingCycle_ftvReward)

end FTVCyclicAdmissibleCycle
end GameTheory
