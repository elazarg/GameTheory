/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.ConditionedProductPurification
import UniformEquilibrium.Quitting.Paths.InfinitePathCompiler
import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification

/-!
# Strategic purification of conditioned singleton rows

Conditioning a positive-survival quitting tail on eventual absorption changes
the hazard of a singleton-support row.  The Bellman identity survives this
change unconditionally, but endpoint incentives do not in general.

There is one exact strategic regime.  Suppose the phantom boundary is tight
at every player's solo-quitting payoff.  For the active owner, exact mixing in
the source row pins the conditioned continuation to that same boundary.  For
an inactive player, multiplication by the remaining eventual-absorption mass
identifies the conditioned joining residual with the original joining
residual.  Its sign is therefore preserved.

The main theorem packages these two identities: an interior exact-Nash solo
row remains an exact-Nash product row after conditioning.  This is specific to
singleton support.  With two active source marginals, exact product
purification is ruled out by `ConditionedProductPurification` unless the
phantom boundary was already absent.
-/

noncomputable section

namespace GameTheory

open Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- If a coordinate of the original continuation equals the corresponding
phantom-boundary coordinate, conditioning leaves that coordinate fixed. -/
theorem quittingTailConditionedValue_eq_boundary_of_value_eq_boundary
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (time : ℕ) (who : ι)
    (hpositive : 0 < quittingTailEventualAbsorption roots time)
    (hvalue : value time who = boundary who) :
    quittingTailConditionedValue roots value boundary time who =
      boundary who := by
  unfold quittingTailConditionedValue
  rw [hvalue]
  have hsurvival : quittingJointSurvivalLimit roots time =
      1 - quittingTailEventualAbsorption roots time := by
    unfold quittingTailEventualAbsorption
    ring
  rw [hsurvival]
  field_simp [hpositive.ne']
  ring

/-- At an inactive coordinate whose phantom boundary is the player's solo
payoff, the conditioned solo-row residual is exactly the source residual
divided by the remaining eventual-absorption mass.  The multiplication form
records the identity without division. -/
theorem quittingTailEventualAbsorption_mul_endpointDifference_conditionedSolo_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι) (time : ℕ) {owner other : ι}
    (hne : other ≠ owner) (hazard : PMF Bool)
    (hroot : roots time = quittingSoloStationaryRoot owner hazard)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (htight : boundary other = quittingSoloReward reward other other) :
    let ratio := (hazard true).toReal /
      quittingTailEventualAbsorption roots time
    let conditionedRoot := quittingSoloStationaryRoot owner
      (quittingHazardCoin ratio
        (div_nonneg ENNReal.toReal_nonneg hcurrent.le)
        (by
          have hweights := quittingTailConditionedWeights_mem_unitInterval
            roots time hnext.le hcurrent
          have hweight : quittingTailConditionedAbsorptionWeight roots time =
              ratio := by
            unfold quittingTailConditionedAbsorptionWeight ratio
            rw [hroot, quittingRootAbsorptionMass_soloStationaryRoot]
          rw [← hweight]
          exact hweights.1.2))
    quittingTailEventualAbsorption roots time *
        quittingRootEndpointDifference reward
          (quittingTailConditionedValue roots value boundary (time + 1))
          conditionedRoot other =
      quittingRootEndpointDifference reward (value (time + 1))
        (roots time) other := by
  dsimp only
  have heventual :=
    quittingTailEventualAbsorption_eq_absorption_add_continue_mul_succ
      roots time
  rw [hroot, quittingRootAbsorptionMass_soloStationaryRoot,
    quittingStationaryContinueMass_solo] at heventual
  have hsourceFormula :
      quittingRootEndpointDifference reward (value (time + 1))
          (roots time) other =
        (hazard false).toReal *
            (quittingSoloReward reward other other - value (time + 1) other) +
          (hazard true).toReal *
            (quittingSingletonCollisionReward reward owner other -
              quittingSoloReward reward owner other) := by
    rw [hroot, quittingRootEndpointDifference,
      quittingRootQuitPayoff_soloStationaryRoot_other reward hne,
      quittingRootContinuePayoff_soloStationaryRoot_other reward hne]
    ring
  rw [hsourceFormula]
  rw [quittingRootEndpointDifference_conditionedSolo_other reward hne]
  unfold quittingTailConditionedValue
  have hsurvival : quittingJointSurvivalLimit roots (time + 1) =
      1 - quittingTailEventualAbsorption roots (time + 1) := by
    unfold quittingTailEventualAbsorption
    ring
  rw [hsurvival, htight]
  field_simp [hcurrent.ne', hnext.ne']
  have hsum := quittingSoloHazardMass_add hazard
  have hfalse : (hazard false).toReal = 1 - (hazard true).toReal := by
    linarith
  rw [heventual, hfalse]
  ring

/-- **Exact strategic singleton purification.**  Let one source row be an
interior solo-quitter exact-Nash row.  If the phantom boundary is tight at
every player's own singleton reward, conditioning the tail on eventual
absorption produces an ordinary solo product root which simultaneously:

* realizes the conditioned nonempty-coalition law;
* satisfies the exact conditioned Bellman equation; and
* remains exact endpoint Nash against the conditioned successor.

The boundary-tightness hypothesis is the precise gate.  Without it, strict
plateau slack can subsidize a conditionally nonviable inactive coordinate and
the residual-rescaling identity above acquires an uncontrolled boundary
term. -/
theorem exists_conditionedSingletonProductRoot_step_isEndpointNash_of_tightBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (time : ℕ) (owner : ι) (hazard : PMF Bool)
    (hroot : roots time = quittingSoloStationaryRoot owner hazard)
    (hquit : 0 < (hazard true).toReal)
    (hcontinue : 0 < (hazard false).toReal)
    (hcurrent : 0 < quittingTailEventualAbsorption roots time)
    (hnext : 0 < quittingTailEventualAbsorption roots (time + 1))
    (htight : ∀ who, boundary who = quittingSoloReward reward who who) :
    ∃ conditionedRoot : ι → PMF Bool,
      IsQuittingConditionedProductPurification
          (roots time) conditionedRoot
          (quittingTailEventualAbsorption roots time) ∧
        quittingTailConditionedValue roots value boundary time =
          quittingRootSuccessorPayoff reward
            (quittingTailConditionedValue roots value boundary (time + 1))
            conditionedRoot ∧
        IsεQuittingRootEndpointNash reward
          (quittingTailConditionedValue roots value boundary (time + 1)) 0
          conditionedRoot := by
  let scale := quittingTailEventualAbsorption roots time
  let ratio := (hazard true).toReal / scale
  have hweight : quittingTailConditionedAbsorptionWeight roots time = ratio := by
    unfold quittingTailConditionedAbsorptionWeight ratio scale
    rw [hroot, quittingRootAbsorptionMass_soloStationaryRoot]
  have hweights := quittingTailConditionedWeights_mem_unitInterval
    roots time hnext.le hcurrent
  have hratioNonneg : 0 ≤ ratio := by
    rw [← hweight]
    exact hweights.1.1
  have hratioOne : ratio ≤ 1 := by
    rw [← hweight]
    exact hweights.1.2
  let conditionedRoot := quittingSoloStationaryRoot owner
    (quittingHazardCoin ratio hratioNonneg hratioOne)
  have hphysicalRoot :
      IsQuittingConditionedProductPurification
          (roots time) conditionedRoot scale ∧
        quittingTailConditionedValue roots value boundary time =
          quittingRootSuccessorPayoff reward
            (quittingTailConditionedValue roots value boundary (time + 1))
            conditionedRoot := by
    constructor
    · rw [hroot]
      exact conditionedProductPurification_solo owner hazard scale
        hcurrent hratioOne
    · have hhazardPositive : 0 < (hazard true).toReal := hquit
      have hdelivery :
          quittingRootConditionalAbsorbingDelivery reward (roots time) =
            quittingSoloReward reward owner := by
        rw [hroot]
        exact quittingRootConditionalAbsorbingDelivery_solo
          reward owner hazard hhazardPositive
      have hcontinuation :
          quittingTailConditionedContinuationWeight roots time =
            1 - ratio := by
        have hsum := quittingTailConditionedWeights_add roots time hcurrent
        rw [hweight] at hsum
        linarith
      have hstep := quittingTailConditionedValue_step
        roots value boundary hpolicy time (by simpa [hroot] using hquit)
          hcurrent hnext
      rw [quittingRootSuccessorPayoff_solo]
      funext who
      have hstepWho := congrFun hstep who
      change quittingTailConditionedValue roots value boundary time who = _
      simp only [quittingHazardCoin_true_toReal,
        quittingHazardCoin_false_toReal]
      rw [hweight, hdelivery, hcontinuation] at hstepWho
      exact hstepWho
  refine ⟨conditionedRoot, hphysicalRoot.1, hphysicalRoot.2, ?_⟩
  intro who
  by_cases hwho : who = owner
  · subst who
    have hsource := hnash time owner
    have hsourceDifference :
        quittingRootEndpointDifference reward (value (time + 1))
          (roots time) owner = 0 := by
      have hcontinueRoot :
          (roots time owner false).toReal = (hazard false).toReal := by
        rw [hroot]
        simp [quittingSoloStationaryRoot]
      have hquitRoot :
          (roots time owner true).toReal = (hazard true).toReal := by
        rw [hroot]
        simp [quittingSoloStationaryRoot]
      rw [hcontinueRoot] at hsource
      rw [hquitRoot] at hsource
      have hnonneg : 0 ≤ quittingRootEndpointDifference reward
          (value (time + 1)) (roots time) owner := by
        nlinarith
      have hnonpos : quittingRootEndpointDifference reward
          (value (time + 1)) (roots time) owner ≤ 0 := by
        nlinarith
      exact le_antisymm hnonpos hnonneg
    have hvalueNext : value (time + 1) owner = boundary owner := by
      rw [hroot, quittingRootEndpointDifference,
        quittingRootQuitPayoff_soloStationaryRoot_owner,
        quittingRootContinuePayoff_soloStationaryRoot_owner]
        at hsourceDifference
      rw [← htight owner] at hsourceDifference
      linarith
    have hconditionedNext :
        quittingTailConditionedValue roots value boundary (time + 1) owner =
          boundary owner :=
      quittingTailConditionedValue_eq_boundary_of_value_eq_boundary
        roots value boundary (time + 1) owner hnext hvalueNext
    have hdifference : quittingRootEndpointDifference reward
        (quittingTailConditionedValue roots value boundary (time + 1))
        conditionedRoot owner = 0 := by
      unfold conditionedRoot
      rw [quittingRootEndpointDifference_conditionedSolo_owner,
        hconditionedNext, htight owner]
      ring
    rw [hdifference]
    constructor <;> simp
  · have hsource : quittingRootEndpointDifference reward (value (time + 1))
        (roots time) who ≤ 0 := by
      have hlocal := (hnash time who).1
      have hcontinueRoot : (roots time who false).toReal = 1 := by
        rw [hroot, quittingSoloStationaryRoot_apply_other hwho]
        simp
      rwa [hcontinueRoot, one_mul] at hlocal
    have hrescale :=
      quittingTailEventualAbsorption_mul_endpointDifference_conditionedSolo_other
        reward roots value boundary time hwho hazard hroot hcurrent hnext
          (htight who)
    have hdifference : quittingRootEndpointDifference reward
        (quittingTailConditionedValue roots value boundary (time + 1))
        conditionedRoot who ≤ 0 := by
      dsimp only [conditionedRoot]
      dsimp only at hrescale
      nlinarith
    have hcontinueRoot : (conditionedRoot who false).toReal = 1 := by
      unfold conditionedRoot
      rw [quittingSoloStationaryRoot_apply_other hwho]
      simp
    have hquitRoot : (conditionedRoot who true).toReal = 0 := by
      unfold conditionedRoot
      rw [quittingSoloStationaryRoot_apply_other hwho]
      simp
    rw [hcontinueRoot, hquitRoot, one_mul, zero_mul]
    exact ⟨hdifference, by norm_num⟩

/-- Rowwise strategic singleton purification assembles along the whole
conditioned chronology.  Hence a tail consisting of interior solo rows and
having a coordinatewise solo-tight phantom boundary has no remaining local
product or endpoint-Nash defect.  Any obstruction to compiling this path is
global, notably failure of a playerwise opponent-survival clock. -/
theorem exists_conditionedSingletonProductRoot_path_isEndpointNash_of_tightBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (owner : ℕ → ι) (hazard : ℕ → PMF Bool)
    (hroot : ∀ time,
      roots time = quittingSoloStationaryRoot (owner time) (hazard time))
    (hquit : ∀ time, 0 < (hazard time true).toReal)
    (hcontinue : ∀ time, 0 < (hazard time false).toReal)
    (heventual : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (htight : ∀ who, boundary who = quittingSoloReward reward who who) :
    ∃ conditionedRoots : ℕ → ι → PMF Bool,
      ∀ time,
        IsQuittingConditionedProductPurification
            (roots time) (conditionedRoots time)
            (quittingTailEventualAbsorption roots time) ∧
          quittingTailConditionedValue roots value boundary time =
            quittingRootSuccessorPayoff reward
              (quittingTailConditionedValue roots value boundary (time + 1))
              (conditionedRoots time) ∧
          IsεQuittingRootEndpointNash reward
            (quittingTailConditionedValue roots value boundary (time + 1)) 0
            (conditionedRoots time) := by
  have hstage : ∀ time, ∃ conditionedRoot : ι → PMF Bool,
      IsQuittingConditionedProductPurification
          (roots time) conditionedRoot
          (quittingTailEventualAbsorption roots time) ∧
        quittingTailConditionedValue roots value boundary time =
          quittingRootSuccessorPayoff reward
            (quittingTailConditionedValue roots value boundary (time + 1))
            conditionedRoot ∧
        IsεQuittingRootEndpointNash reward
          (quittingTailConditionedValue roots value boundary (time + 1)) 0
          conditionedRoot := by
    intro time
    exact
      exists_conditionedSingletonProductRoot_step_isEndpointNash_of_tightBoundary
        reward roots value boundary hpolicy hnash time
          (owner time) (hazard time) (hroot time) (hquit time)
          (hcontinue time) (heventual time) (heventual (time + 1)) htight
  choose conditionedRoots hconditionedRoots using hstage
  exact ⟨conditionedRoots, hconditionedRoots⟩

/-- **Counterexample restriction on the tight singleton stratum.**  Suppose
an exact tail consists entirely of interior solo rows, its phantom boundary
is every player's own singleton payoff, and the original values converge to
that boundary.  If the game has no uniform-equilibrium payoff, then the
strategically purified conditioned path must retain a positive deleted-player
survival clock for some player and some start.

Equivalently, local atomic conditioning is completely harmless on this
stratum; only an owner-monopoly obstruction to the nonperiodic infinite-path
compiler can remain. -/
theorem exists_conditionedSingletonProductRoot_path_with_opponentSurvivalObstruction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (value : ℕ → Payoff ι)
    (boundary : Payoff ι)
    (hpolicy : ∀ time, value time =
      quittingRootSuccessorPayoff reward (value (time + 1)) (roots time))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (value (time + 1)) 0 (roots time))
    (owner : ℕ → ι) (hazard : ℕ → PMF Bool)
    (hroot : ∀ time,
      roots time = quittingSoloStationaryRoot (owner time) (hazard time))
    (hquit : ∀ time, 0 < (hazard time true).toReal)
    (hcontinue : ∀ time, 0 < (hazard time false).toReal)
    (heventual : ∀ time,
      0 < quittingTailEventualAbsorption roots time)
    (htight : ∀ who, boundary who = quittingSoloReward reward who who)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal who, |reward terminal who| ≤ M)
    (hboundary : ∀ who,
      Filter.Tendsto (fun time ↦ value time who) Filter.atTop
        (nhds (boundary who)))
    (hnoUniform : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    ∃ conditionedRoots : ℕ → ι → PMF Bool,
      (∀ time,
        IsQuittingConditionedProductPurification
            (roots time) (conditionedRoots time)
            (quittingTailEventualAbsorption roots time) ∧
          quittingTailConditionedValue roots value boundary time =
            quittingRootSuccessorPayoff reward
              (quittingTailConditionedValue roots value boundary (time + 1))
              (conditionedRoots time) ∧
          IsεQuittingRootEndpointNash reward
            (quittingTailConditionedValue roots value boundary (time + 1)) 0
            (conditionedRoots time)) ∧
        ∃ who start, ¬ Filter.Tendsto
          (quittingOpponentSurvivalWeight conditionedRoots who start)
          Filter.atTop (nhds 0) := by
  obtain ⟨conditionedRoots, hconditioned⟩ :=
    exists_conditionedSingletonProductRoot_path_isEndpointNash_of_tightBoundary
      reward roots value boundary hpolicy hnash owner hazard hroot hquit
        hcontinue heventual htight
  refine ⟨conditionedRoots, hconditioned, ?_⟩
  by_contra hnoObstruction
  push Not at hnoObstruction
  have hvalueBound : ∀ time who,
      |quittingTailConditionedValue roots value boundary time who| ≤ M := by
    intro time who
    exact abs_quittingTailConditionedValue_le
      roots value boundary hpolicy hM hreward hboundary time
        (heventual time) who
  have hrootNash : ∀ time,
      IsεQuittingRootNash reward
        (quittingTailConditionedValue roots value boundary (time + 1)) 0
        (conditionedRoots time) := by
    intro time
    exact
      (isεQuittingRootEndpointNash_iff_isεQuittingRootNash reward
        (quittingTailConditionedValue roots value boundary (time + 1)) 0
        (conditionedRoots time)).1 (hconditioned time).2.2
  have huniform :=
    infinitePath_isUniformEquilibriumPayoff_of_survival_tendsto_zero
      reward conditionedRoots
        (quittingTailConditionedValue roots value boundary)
        hnoObstruction hM hreward hvalueBound
        (fun time ↦ (hconditioned time).2.1) hrootNash
  exact hnoUniform
    ⟨quittingTailConditionedValue roots value boundary 0, huniform⟩

/-! ## Atomic monopoly limit -/

/-- Exact endpoint Nash is closed under a positive-rate solo limit.  This is
the finite-dimensional step used by the unique-infinite-owner atomic branch:
once the late tail converges to the owner's singleton payoff vector, the
limiting positive solo rate is a genuine stationary endpoint equilibrium. -/
theorem isEndpointNash_soloRate_of_tendsto
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (rate : ℕ → ℝ) (tail : ℕ → Payoff ι) (limitRate : ℝ)
    (hrateNonneg : ∀ time, 0 ≤ rate time)
    (hrateOne : ∀ time, rate time ≤ 1)
    (hlimitNonneg : 0 ≤ limitRate) (hlimitOne : limitRate ≤ 1)
    (hrate : Filter.Tendsto rate Filter.atTop (nhds limitRate))
    (htail : Filter.Tendsto tail Filter.atTop
      (nhds (quittingSoloReward reward owner)))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (tail time) 0
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin (rate time)
            (hrateNonneg time) (hrateOne time)))) :
    IsεQuittingRootEndpointNash reward (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner
        (quittingHazardCoin limitRate hlimitNonneg hlimitOne)) := by
  apply isεQuittingRootEndpointNash_soloStationaryRoot
  intro other hother
  have htailOther : Filter.Tendsto (fun time ↦ tail time other) Filter.atTop
      (nhds (quittingSoloReward reward owner other)) :=
    (continuous_apply other).tendsto
      (quittingSoloReward reward owner) |>.comp htail
  let residual : ℕ → ℝ := fun time ↦
    (1 - rate time) *
        (quittingSoloReward reward other other - tail time other) +
      rate time *
        (quittingSingletonCollisionReward reward owner other -
          quittingSoloReward reward owner other)
  have hresidualNonpos : ∀ time, residual time ≤ 0 := by
    intro time
    have hlocal := (hnash time other).1
    have hcontinue :
        ((quittingSoloStationaryRoot owner
          (quittingHazardCoin (rate time)
            (hrateNonneg time) (hrateOne time))) other false).toReal = 1 := by
      rw [quittingSoloStationaryRoot_apply_other hother]
      simp
    rw [hcontinue, one_mul] at hlocal
    rw [quittingRootEndpointDifference_conditionedSolo_other reward hother]
      at hlocal
    simpa only [residual] using hlocal
  have hresidual : Filter.Tendsto residual Filter.atTop
      (nhds ((1 - limitRate) *
          (quittingSoloReward reward other other -
            quittingSoloReward reward owner other) +
        limitRate *
          (quittingSingletonCollisionReward reward owner other -
            quittingSoloReward reward owner other))) := by
    unfold residual
    exact ((tendsto_const_nhds.sub hrate).mul
      (tendsto_const_nhds.sub htailOther)).add
        (hrate.mul tendsto_const_nhds)
  have hlimitResidual :
      (1 - limitRate) *
          (quittingSoloReward reward other other -
            quittingSoloReward reward owner other) +
        limitRate *
          (quittingSingletonCollisionReward reward owner other -
            quittingSoloReward reward owner other) ≤ 0 :=
    le_of_tendsto' hresidual hresidualNonpos
  rw [quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
  linarith

/-- **Unique atomic owner restriction.**  If a positive conditioned solo
rate is obtained as a limit and the associated continuations converge to the
owner's singleton payoff vector, then absence of a uniform equilibrium forces
that owner's own singleton payoff to be strictly negative.

For a nonnegative owner payoff, closed endpoint Nash supplies the inactive
joining criterion at the limiting rate, and the existing owner-solo terminal
compiler gives a uniform equilibrium immediately. -/
theorem soloReward_owner_neg_of_noUniform_of_atomicSoloLimit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (rate : ℕ → ℝ) (tail : ℕ → Payoff ι) (limitRate : ℝ)
    (hrateNonneg : ∀ time, 0 ≤ rate time)
    (hrateOne : ∀ time, rate time ≤ 1)
    (hlimitPositive : 0 < limitRate) (hlimitOne : limitRate ≤ 1)
    (hrate : Filter.Tendsto rate Filter.atTop (nhds limitRate))
    (htail : Filter.Tendsto tail Filter.atTop
      (nhds (quittingSoloReward reward owner)))
    (hnash : ∀ time,
      IsεQuittingRootEndpointNash reward (tail time) 0
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin (rate time)
            (hrateNonneg time) (hrateOne time))))
    (hnoUniform : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    quittingSoloReward reward owner owner < 0 := by
  have hlimitNash := isEndpointNash_soloRate_of_tendsto
    reward owner rate tail limitRate hrateNonneg hrateOne
      hlimitPositive.le hlimitOne hrate htail hnash
  have hinactive :=
    (isεQuittingRootEndpointNash_soloStationaryRoot_iff reward owner
      (quittingHazardCoin limitRate hlimitPositive.le hlimitOne)).1 hlimitNash
  by_contra hnotNegative
  have howner : 0 ≤ quittingSoloReward reward owner owner :=
    le_of_not_gt hnotNegative
  have huniform := isUniformEquilibriumPayoff_soloReward_of_inactive
    reward owner
      (quittingHazardCoin limitRate hlimitPositive.le hlimitOne)
      (by simpa using hlimitPositive) howner hinactive
  exact hnoUniform ⟨quittingSoloReward reward owner, huniform⟩

end GameTheory
