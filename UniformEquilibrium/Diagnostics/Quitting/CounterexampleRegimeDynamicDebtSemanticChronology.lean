/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeExhaustiveFrontier
import UniformEquilibrium.Quitting.Boundary.Holonomy.InfiniteBehavioralTailEvaluation
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtCapCarrier
import UniformEquilibrium.Quitting.Debt.Dynamic.FiniteDynamicDebtChains
import UniformEquilibrium.Quitting.Root.TerminalSemanticPair
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# Semantic chronology of the counterexample exact-D tail

The augmented pair `(value, value + debt)` of every exact dynamic-debt edge
obeys the literal terminal-semantic prefix equation.  The displayed root is
an exact Nash root against the successor prescribed value.

For the independently optimized finite chains, each fixed preterminal row is
the semantic pair of its executable all-Continue completion.  Passing to the
projective limit at one fixed time therefore puts every selected tail pair in
the closed terminal-semantic carrier.  A separate chronological limit puts
the all-Continue self-loop pair in the carrier.  No interchange of these two
limits is used.

Consequently the stopping-law frontier minimum is bounded above by the debt
sum of every tail row and by the limiting self-loop debt sum.  These are only
one-sided comparisons: the finite exact-D selector minimizes a maximum debt
coordinate over finite zero-boundary chains, whereas the frontier minimizes
total semantic debt over the full carrier.  Nothing here identifies either
tail point as a minimizer.
-/

noncomputable section

namespace GameTheory

open Filter Set StochasticGame Math.Probability Math.ProbabilityMassFunction
open Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Every exact-D edge is a literal semantic prefix -/

/-- Forget the displayed simplex root and augment prescribed value by exact
dynamic debt. -/
def quittingDynamicDebtSemanticPair (point : QuittingDebtPoint ι) :
    QuittingTerminalSemanticPair ι :=
  (point.1.1, quittingDynamicDebtCap point)

omit [DecidableEq ι] in
@[simp]
theorem quittingDynamicDebtSemanticPair_debt
    (point : QuittingDebtPoint ι) (who : ι) :
    quittingTerminalSemanticDebt (quittingDynamicDebtSemanticPair point) who =
      point.2 who := by
  simp [quittingDynamicDebtSemanticPair, quittingTerminalSemanticDebt,
    quittingDynamicDebtCap_apply]

omit [DecidableEq ι] in
/-- Semanticization is continuous; in particular it may be applied after a
fixed-time projective limit. -/
theorem continuous_quittingDynamicDebtSemanticPair :
    Continuous (quittingDynamicDebtSemanticPair :
      QuittingDebtPoint ι → QuittingTerminalSemanticPair ι) := by
  exact (continuous_fst.comp continuous_fst).prodMk
    continuous_quittingDynamicDebtCap

/-- Exact algebraic bridge: every dynamic-debt edge becomes precisely the
terminal-semantic prefix of its successor.  Nonnegativity is not needed for
this identity. -/
theorem quittingDynamicDebtSemanticPair_eq_prefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor) :
    quittingDynamicDebtSemanticPair current =
      quittingTerminalSemanticPrefix reward
        (quittingRootOfSimplex current.1.2)
        (quittingDynamicDebtSemanticPair successor) := by
  apply Prod.ext
  · exact hedge.1.1
  · funext who
    change quittingDynamicDebtCap current who =
      max
        (quittingRootQuitPayoff reward successor.1.1
          (quittingRootOfSimplex current.1.2) who)
        (quittingRootContinuePayoff reward
          (Function.update successor.1.1 who
            (quittingDynamicDebtCap successor who))
          (quittingRootOfSimplex current.1.2) who)
    rw [quittingDynamicDebtCap_eq_max_endpoints reward current successor hedge who,
      quittingDynamicDebtCap_apply,
      quittingRootContinuePayoff_update_add]
    unfold quittingRootOpponentContinueMass
    rw [quittingDebtOpponentContinueMass_eq_stationary]

/-- The root on an exact dynamic-debt edge is exact Nash against the
successor's prescribed value. -/
theorem quittingDynamicDebtEdge_exactNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor) :
    IsεQuittingRootNash reward successor.1.1 0
      (quittingRootOfSimplex current.1.2) := by
  exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward successor.1.1 (quittingRootOfSimplex current.1.2)).mp hedge.1.2

/-- Provenance-preserving edge package.  A boxed/nonnegative successor is a
semantic successor with nonnegative debt, and the edge supplies both the
literal prefix identity and exact root Nash. -/
theorem quittingDynamicDebtEdge_semanticPrefixChronology
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current successor : QuittingDebtPoint ι)
    (hedge : IsQuittingDynamicDebtEdge reward current successor)
    (hsuccessorDebt : ∀ who, 0 ≤ successor.2 who) :
    quittingDynamicDebtSemanticPair current =
        quittingTerminalSemanticPrefix reward
          (quittingRootOfSimplex current.1.2)
          (quittingDynamicDebtSemanticPair successor) ∧
      IsεQuittingRootNash reward
        (quittingDynamicDebtSemanticPair successor).1 0
          (quittingRootOfSimplex current.1.2) ∧
      ∀ who, 0 ≤ quittingTerminalSemanticDebt
        (quittingDynamicDebtSemanticPair successor) who := by
  exact ⟨quittingDynamicDebtSemanticPair_eq_prefix
      reward current successor hedge,
    quittingDynamicDebtEdge_exactNash reward current successor hedge,
    fun who => by simpa using hsuccessorDebt who⟩

/-! ## Finite all-Continue completions -/

omit [Fintype ι] [DecidableEq ι] in
theorem quittingPhaseSwitchRoots_allContinue_eq_of_allContinue_from_semantic
    (roots : ℕ → ι → PMF Bool) (cutoff : ℕ)
    (htail : ∀ time, cutoff ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool)) :
    quittingPhaseSwitchRoots roots (fun _ => quittingAllContinueRoot) cutoff =
      roots := by
  funext time
  by_cases htime : time < cutoff
  · rw [quittingPhaseSwitchRoots_of_lt roots _ htime]
  · rw [quittingPhaseSwitchRoots_of_le roots _ (Nat.not_lt.mp htime),
      htail time (Nat.not_lt.mp htime)]

/-- Time-translated semantic identification of the finite dynamic debt of a
zero-boundary exact policy completed by all-Continue. -/
theorem quittingFiniteDynamicDebt_eq_terminalSemanticDebt_suffix_completion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (start fuel : ℕ) (hfuel : 0 < fuel)
    (htail : ∀ time, start + fuel ≤ time →
      roots time = (quittingAllContinueRoot : ι → PMF Bool))
    (hterminal : value (start + fuel) = 0)
    (hpolicy : ∀ time, start ≤ time → time < start + fuel →
      value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time))
    (who : ι) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingFiniteDynamicDebt reward roots who (fun time => value time who)
        (quittingPositiveSingletonDebtCap reward who) start fuel =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootSequenceProfile reward roots start)) who := by
  let shiftedRoots : ℕ → ι → PMF Bool := fun time => roots (start + time)
  let shiftedValue : ℕ → Payoff ι := fun time => value (start + time)
  let never : ℕ → ι → PMF Bool := fun _ => quittingAllContinueRoot
  let cap : ℝ := max 0 (reward (quittingSingletonTerminal who) who)
  have hshiftTail : ∀ time, fuel ≤ time →
      shiftedRoots time = (quittingAllContinueRoot : ι → PMF Bool) := by
    intro time htime
    exact htail (start + time) (Nat.add_le_add_left htime start)
  have hphaseRoots :
      quittingPhaseSwitchRoots shiftedRoots never fuel = shiftedRoots := by
    exact quittingPhaseSwitchRoots_allContinue_eq_of_allContinue_from_semantic
      shiftedRoots fuel hshiftTail
  have hphaseProfile :
      quittingPhaseSwitchProfile reward shiftedRoots never fuel =
        quittingInfinitePathProfile reward shiftedRoots := by
    unfold quittingPhaseSwitchProfile quittingInfinitePathProfile
    rw [hphaseRoots]
  have htailBest :
      QuittingBoundaryHolonomy.behavioralTailEnvelopeBoundary reward never who =
        cap := by
    unfold QuittingBoundaryHolonomy.behavioralTailEnvelopeBoundary
    simpa [never, cap, quittingElementaryCapRoots] using
      (quittingRootSequenceBestResponseValue_elementaryCap_never
        (ι := ι) reward who hM hreward)
  have hlength : fuel - 1 + 1 = fuel :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hfuel))
  have hbest :=
    quittingPhaseSwitch_bestResponseAt_eq_continuationBestResponse
      reward shiftedRoots never fuel hfuel who hM hreward
  rw [hphaseProfile] at hbest
  unfold QuittingBoundaryHolonomy.boundaryEnvelopeAt at hbest
  rw [quittingFiniteBoundaryHolonomy_bestResponse_eval, hlength,
    htailBest] at hbest
  have hshiftTerminal : shiftedValue fuel = 0 := by
    simpa [shiftedValue] using hterminal
  have hterminalWho : shiftedValue fuel who = 0 := congrFun hshiftTerminal who
  have hdynamic :=
    prescribed_add_quittingFiniteDynamicDebt_eq_bestResponse
      reward shiftedRoots who (fun time => shiftedValue time who)
        (quittingPositiveSingletonDebtCap reward who) 0 fuel
  have hdynamic' :
      shiftedValue 0 who +
          quittingFiniteDynamicDebt reward shiftedRoots who
            (fun time => shiftedValue time who)
            (quittingPositiveSingletonDebtCap reward who) 0 fuel =
        quittingFiniteTerminalBestResponseValue reward shiftedRoots who cap
          0 fuel := by
    simpa [quittingPositiveSingletonDebtCap, cap, hterminalWho] using hdynamic
  have hshiftPolicy : ∀ time, time < fuel →
      shiftedValue time = quittingRootSuccessorPayoff reward
        (shiftedValue (time + 1)) (shiftedRoots time) := by
    intro time htime
    apply hpolicy (start + time)
    · omega
    · omega
  have hprescribed :
      quittingTerminalPayoff reward
          (quittingInfinitePathProfile reward shiftedRoots) who =
        shiftedValue 0 who := by
    exact congrFun
      (quittingTerminalPayoff_finiteExactChainProfile
        reward shiftedRoots shiftedValue fuel hshiftTail hshiftTerminal
          hshiftPolicy) who
  have hzero :
      quittingFiniteDynamicDebt reward shiftedRoots who
          (fun time => shiftedValue time who)
          (quittingPositiveSingletonDebtCap reward who) 0 fuel =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingInfinitePathProfile reward shiftedRoots)) who := by
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair
    dsimp
    linarith
  rw [quittingFiniteDynamicDebt_shift reward roots who
    (fun time => value time who)
    (quittingPositiveSingletonDebtCap reward who) start fuel]
  rw [quittingRootSequenceProfile_eq_shift reward roots start]
  exact hzero

/-- Every preterminal production debt coordinate is the literal semantic
debt of the executable continuation restarted at that row. -/
theorem quittingFiniteNashBellmanPathDynamicDebt_eq_terminalSemanticDebt_completion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (who : ι) (time : ℕ) (htime : time < cutoff) :
    quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who time =
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward
          (quittingRootSequenceProfile reward
            (quittingFiniteNashBellmanPathRoots cutoff path) time)) who := by
  let roots := quittingFiniteNashBellmanPathRoots cutoff path
  let value := quittingFiniteNashBellmanPathValue cutoff path
  have hsum : time + (cutoff - time) = cutoff :=
    Nat.add_sub_of_le htime.le
  have hsuffix :=
    quittingFiniteDynamicDebt_eq_terminalSemanticDebt_suffix_completion
      reward roots value time (cutoff - time) (Nat.sub_pos_of_lt htime)
      (fun later hlater => by
        apply quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
          cutoff path later
        simpa [hsum] using hlater)
      (by
        simpa [value, hsum] using
          (quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
            reward cutoff path hpath))
      (fun later _htimeLater hlater => by
        apply quittingFiniteNashBellmanPathValue_eq_successor
          reward cutoff path hpath later
        simpa [hsum] using hlater)
      who (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
  simpa [quittingFiniteNashBellmanPathDynamicDebt, roots, value] using hsuffix

/-- At every preterminal row, semanticization of the production exact-D
point is literally the terminal semantic pair of the restarted executable
all-Continue completion. -/
theorem quittingFiniteNashBellmanPathDynamicDebtSemanticPair_eq_completion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) (path : QuittingFiniteNashBellmanPath ι cutoff)
    (hpath : path ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff)
    (time : ℕ) (htime : time < cutoff) :
    quittingDynamicDebtSemanticPair
        (quittingFiniteNashBellmanPathDynamicDebtPoint
          reward cutoff path time) =
      quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (quittingFiniteNashBellmanPathRoots cutoff path) time) := by
  let roots := quittingFiniteNashBellmanPathRoots cutoff path
  let value := quittingFiniteNashBellmanPathValue cutoff path
  have hselected :=
    eq_quittingRootSequenceTerminalValue_of_finite_zeroBoundary
      reward roots value cutoff
      (quittingFiniteNashBellmanPathRoots_eq_allContinue_of_cutoff_le
        cutoff path)
      (quittingFiniteNashBellmanPathValue_eq_zero_at_cutoff
        reward cutoff path hpath)
      (quittingFiniteNashBellmanPathValue_eq_successor
        reward cutoff path hpath)
  have hpayoff :
      (fun observer => quittingTerminalPayoff reward
        (quittingRootSequenceProfile reward roots time) observer) =
        (path ⟨time, Nat.lt_succ_of_lt htime⟩).1 := by
    funext observer
    change quittingRootSequenceTerminalValue reward roots observer time = _
    rw [← congrFun (hselected time htime.le) observer]
    exact congrFun
      (quittingFiniteNashBellmanPathValue_of_lt cutoff path time htime)
      observer
  have hdebt : ∀ observer,
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff path observer time =
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward
            (quittingRootSequenceProfile reward roots time)) observer := by
    intro observer
    exact quittingFiniteNashBellmanPathDynamicDebt_eq_terminalSemanticDebt_completion
      reward cutoff path hpath observer time htime
  unfold quittingDynamicDebtSemanticPair
    quittingFiniteNashBellmanPathDynamicDebtPoint
  rw [dif_pos htime.le]
  apply Prod.ext
  · exact hpayoff.symm
  · funext observer
    change quittingDynamicDebtCap
        ((path ⟨time, Nat.lt_succ_of_lt htime⟩,
          fun who => quittingFiniteNashBellmanPathDynamicDebt
            reward cutoff path who time) : QuittingDebtPoint ι) observer =
      quittingContinuationBestResponseValue reward
        (quittingRootSequenceProfile reward roots time) observer
    rw [quittingDynamicDebtCap_apply]
    change (path ⟨time, Nat.lt_succ_of_lt htime⟩).1 observer +
        quittingFiniteNashBellmanPathDynamicDebt reward cutoff path observer time =
      quittingContinuationBestResponseValue reward
        (quittingRootSequenceProfile reward roots time) observer
    rw [← hpayoff]
    have h := hdebt observer
    unfold quittingTerminalSemanticDebt quittingTerminalSemanticPair at h
    dsimp at h
    linarith

/-! ## The selected projective tail and its all-Continue limit -/

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
variable {regime : QuittingCounterexampleRegime reward}

namespace QuittingCounterexampleSeamWitness

variable (seam : QuittingCounterexampleSeamWitness regime)

/-- Each fixed-time projective exact-D tail point is a literal point of the
terminal-semantic carrier.  The finite cutoff limit is taken with `time`
fixed. -/
theorem dynamicDebtSemanticPair_tail_mem_carrier (time : ℕ) :
    quittingDynamicDebtSemanticPair (seam.tail time) ∈
      quittingTerminalSemanticCarrier reward := by
  letI : Nonempty ι := regime.nonempty_players
  have hpoint : Tendsto (fun family ↦
      quittingFiniteMinMaxDynamicDebtTail reward (seam.subseq family) time)
      atTop (nhds (seam.tail time)) := by
    exact ((continuous_apply time).tendsto seam.tail).comp
      seam.projective_limit
  have hsemantic : Tendsto (fun family ↦ quittingDynamicDebtSemanticPair
      (quittingFiniteMinMaxDynamicDebtTail reward
        (seam.subseq family) time)) atTop
      (nhds (quittingDynamicDebtSemanticPair (seam.tail time))) :=
    (continuous_quittingDynamicDebtSemanticPair.tendsto
      (seam.tail time)).comp hpoint
  have hcutoff : ∀ᶠ family in atTop, time < seam.subseq family := by
    filter_upwards
      [seam.subseq_strict.tendsto_atTop.eventually_ge_atTop (time + 1)]
      with family hfamily
    omega
  have hfinite : ∀ᶠ family in atTop,
      quittingDynamicDebtSemanticPair
          (quittingFiniteMinMaxDynamicDebtTail reward
            (seam.subseq family) time) ∈
        quittingTerminalSemanticCarrier reward := by
    filter_upwards [hcutoff] with family htime
    unfold quittingFiniteMinMaxDynamicDebtTail
    rw [quittingFiniteNashBellmanPathDynamicDebtSemanticPair_eq_completion
      reward (seam.subseq family)
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward (seam.subseq family))
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
        reward (seam.subseq family)) time htime]
    apply subset_closure
    exact ⟨quittingRootSequenceProfile reward
        (quittingFiniteNashBellmanPathRoots (seam.subseq family)
          (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
            reward (seam.subseq family))) time, rfl⟩
  exact isClosed_closure.mem_of_tendsto hsemantic hfinite

/-- Every chronological tail edge is a state-matched terminal-semantic
prefix between literal carrier points, with exact root Nash at the displayed
root and a nonnegative successor debt. -/
theorem dynamicDebtSemanticPair_tail_chronology (time : ℕ) :
    quittingDynamicDebtSemanticPair (seam.tail time) ∈
        quittingTerminalSemanticCarrier reward ∧
      quittingDynamicDebtSemanticPair (seam.tail (time + 1)) ∈
        quittingTerminalSemanticCarrier reward ∧
      quittingDynamicDebtSemanticPair (seam.tail time) =
        quittingTerminalSemanticPrefix reward
          (quittingRootOfSimplex (seam.tail time).1.2)
          (quittingDynamicDebtSemanticPair (seam.tail (time + 1))) ∧
      IsεQuittingRootNash reward (seam.tail (time + 1)).1.1 0
        (quittingRootOfSimplex (seam.tail time).1.2) := by
  have hchronology := quittingDynamicDebtEdge_semanticPrefixChronology
    reward (seam.tail time) (seam.tail (time + 1)) (seam.tail_edge time)
      (seam.tail_mem (time + 1)).2.1
  exact ⟨seam.dynamicDebtSemanticPair_tail_mem_carrier time,
    seam.dynamicDebtSemanticPair_tail_mem_carrier (time + 1),
    hchronology.1, hchronology.2.1⟩

/-- The all-Continue limiting value/debt pair, with its debt reinterpreted as
the gap between prescribed value and augmented envelope. -/
def limitDynamicDebtSemanticPair : QuittingTerminalSemanticPair ι :=
  (seam.limit.value, seam.limit.value + seam.limit.debt)

@[simp]
theorem limitDynamicDebtSemanticPair_debt (who : ι) :
    quittingTerminalSemanticDebt seam.limitDynamicDebtSemanticPair who =
      seam.limit.debt who := by
  simp [limitDynamicDebtSemanticPair, quittingTerminalSemanticDebt]

/-- The chronological tail semantic pairs converge to the all-Continue
semantic pair.  This is a second, separate limit after fixed-time carrier
membership has already been proved. -/
theorem dynamicDebtSemanticPair_tail_tendsto :
    Tendsto (fun time ↦ quittingDynamicDebtSemanticPair (seam.tail time))
      atTop (nhds seam.limitDynamicDebtSemanticPair) := by
  have hvalue : Tendsto (fun time ↦ (seam.tail time).1.1) atTop
      (nhds seam.limit.value) :=
    tendsto_pi_nhds.2 seam.value_tendsto
  have hcap : Tendsto
      (fun time ↦ quittingDynamicDebtCap (seam.tail time)) atTop
      (nhds (seam.limit.value + seam.limit.debt)) := by
    apply tendsto_pi_nhds.2
    intro who
    simpa [quittingDynamicDebtCap_apply] using
      (seam.value_tendsto who).add (seam.debt_tendsto who)
  change Tendsto
    (fun time ↦ ((seam.tail time).1.1,
      quittingDynamicDebtCap (seam.tail time))) atTop
    (nhds (seam.limit.value, seam.limit.value + seam.limit.debt))
  simpa only [nhds_prod_eq] using hvalue.prodMk hcap

/-- The all-Continue chronological limit is itself a literal point of the
closed terminal-semantic carrier. -/
theorem limitDynamicDebtSemanticPair_mem_carrier :
    seam.limitDynamicDebtSemanticPair ∈
      quittingTerminalSemanticCarrier reward := by
  exact isClosed_closure.mem_of_tendsto
    seam.dynamicDebtSemanticPair_tail_tendsto
      (Filter.Eventually.of_forall
        seam.dynamicDebtSemanticPair_tail_mem_carrier)

/-- The limiting semantic carrier point is a literal all-Continue prefix
fixed point, inherited from the exact dynamic-debt self-loop. -/
theorem limitDynamicDebtSemanticPair_allContinue_prefix :
    seam.limitDynamicDebtSemanticPair =
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot
        seam.limitDynamicDebtSemanticPair := by
  have h := quittingDynamicDebtSemanticPair_eq_prefix reward
    (((seam.limit.value, quittingAllContinueSimplexRoot), seam.limit.debt) :
      QuittingDebtPoint ι)
    (((seam.limit.value, quittingAllContinueSimplexRoot), seam.limit.debt) :
      QuittingDebtPoint ι) seam.limit.exactSelfLoop
  have hpair : quittingDynamicDebtSemanticPair
      (((seam.limit.value, quittingAllContinueSimplexRoot), seam.limit.debt) :
        QuittingDebtPoint ι) = seam.limitDynamicDebtSemanticPair := by
    apply Prod.ext
    · rfl
    · funext who
      simp [quittingDynamicDebtSemanticPair, quittingDynamicDebtCap_apply,
        limitDynamicDebtSemanticPair]
  rw [hpair] at h
  simpa [quittingRootOfSimplex_allContinueSimplexRoot] using h

/-- The limiting all-Continue root is exact Nash against the limiting
prescribed value. -/
theorem limitDynamicDebtSemanticPair_allContinue_nash :
    IsεQuittingRootNash reward seam.limitDynamicDebtSemanticPair.1 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
  have h := quittingDynamicDebtEdge_exactNash reward
    (((seam.limit.value, quittingAllContinueSimplexRoot), seam.limit.debt) :
      QuittingDebtPoint ι)
    (((seam.limit.value, quittingAllContinueSimplexRoot), seam.limit.debt) :
      QuittingDebtPoint ι) seam.limit.exactSelfLoop
  simpa [limitDynamicDebtSemanticPair,
    quittingRootOfSimplex_allContinueSimplexRoot] using h

end QuittingCounterexampleSeamWitness

namespace QuittingCounterexampleStoppingLawFrontier

variable (frontier : QuittingCounterexampleStoppingLawFrontier regime)

/-- The independent frontier minimum is no larger than the total exact debt
of any chronological projective-tail point.  This does not assert equality.
-/
theorem baseDebtSum_le_seamTailDebtSum (time : ℕ) :
    quittingTerminalSemanticDebtSum frontier.base ≤
      ∑ who, (frontier.seam.tail time).2 who := by
  have h := frontier.base_minimum
    (quittingDynamicDebtSemanticPair (frontier.seam.tail time))
    (frontier.seam.dynamicDebtSemanticPair_tail_mem_carrier time)
  simpa [quittingTerminalSemanticDebtSum] using h

/-- The independent frontier minimum is no larger than the total debt of the
all-Continue chronological limit.  Again, no minimizer identification or
reverse inequality is claimed. -/
theorem baseDebtSum_le_seamLimitDebtSum :
    quittingTerminalSemanticDebtSum frontier.base ≤
      ∑ who, frontier.seam.limit.debt who := by
  have h := frontier.base_minimum
    frontier.seam.limitDynamicDebtSemanticPair
    frontier.seam.limitDynamicDebtSemanticPair_mem_carrier
  simpa [quittingTerminalSemanticDebtSum] using h

end QuittingCounterexampleStoppingLawFrontier

end GameTheory
