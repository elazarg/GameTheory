/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingVariableMeshSchedule
import GameTheory.Concepts.Stochastic.QuittingInfinitePathSupersolution

/-!
# Variable singleton-flow meshes on nonperiodic paths

Each coarse singleton arc receives its own positive subdivision length.  The
flattened path has exact policy evaluation and exact prescribed Continue at
every microstage.  Immediate Quit loses at most the current micro-hazard times
a uniform collision-surplus bound.

The decisive preservation statement is at coarse boundaries: the product of
the microstage opponent-continuation factors in block `t` is exactly the
original coarse factor.  Thus qualitative opponent-survival convergence is
unchanged by arbitrarily long, nonuniform finite subdivisions.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Coarse and micro roots -/

/-- Singleton roots of the unsubdivided coarse path. -/
def quittingVariableSingletonCoarseRoot
    (owner : ℕ → ι) (p : ℕ → ℝ)
    (hp0 : ∀ time, 0 ≤ p time) (hp1 : ∀ time, p time < 1)
    (time : ℕ) : ι → PMF Bool :=
  quittingSoloStationaryRoot (owner time)
    (quittingHazardCoin (p time) (hp0 time) (hp1 time).le)

/-- Singleton root at flattened microtime. -/
def quittingVariableSingletonMeshRoot
    (owner : ℕ → ι) (p : ℕ → ℝ) (length : ℕ → ℕ)
    (hp0 : ∀ time, 0 ≤ p time) (hp1 : ∀ time, p time < 1)
    (time : ℕ) : ι → PMF Bool :=
  let state := quittingVariableMeshState length time
  quittingSoloStationaryRoot (owner state.1)
    (quittingMeshHazardCoin (p state.1) (length state.1)
      (hp0 state.1) (hp1 state.1))

/-- Interpolated payoff at flattened microtime. -/
def quittingVariableSingletonMeshValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (p : ℕ → ℝ)
    (coarse : ℕ → Payoff ι) (length : ℕ → ℕ)
    (time : ℕ) : Payoff ι :=
  let state := quittingVariableMeshState length time
  quittingMeshPayoffInterpolant
    (quittingSoloReward reward (owner state.1)) (coarse state.1)
    (1 - quittingMeshHazard (p state.1) (length state.1)) state.2

@[simp] theorem quittingMeshPayoffInterpolant_zero
    (root start : Payoff ι) (a : ℝ) :
    quittingMeshPayoffInterpolant root start a 0 = start := by
  funext who
  simp [quittingMeshPayoffInterpolant, quittingMeshInterpolant]

@[simp] theorem quittingVariableSingletonMeshValue_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (p : ℕ → ℝ)
    (coarse : ℕ → Payoff ι) (length : ℕ → ℕ) :
    quittingVariableSingletonMeshValue reward owner p coarse length 0 =
      coarse 0 := by
  simp [quittingVariableSingletonMeshValue]

/-- Upper-bound companion to
`le_quittingMeshPayoffInterpolant_of_arcEndpoints`. -/
theorem quittingMeshPayoffInterpolant_le_of_arcEndpoints
    {p : ℝ} {m : ℕ} (hp0 : 0 ≤ p) (hp1 : p < 1) (hm : 0 < m)
    {root start next upper : Payoff ι}
    (harc : start = quittingSingletonArcPayoff p root next)
    (hupperStart : ∀ who, start who ≤ upper who)
    (hupperNext : ∀ who, next who ≤ upper who)
    (k : ℕ) (hk : k ≤ m) (who : ι) :
    quittingMeshPayoffInterpolant root start
        (1 - quittingMeshHazard p m) k who ≤ upper who := by
  let q := 1 - quittingMeshHazard p m
  have hqpos : 0 < q := by
    dsimp only [q]
    rw [one_sub_quittingMeshHazard]
    exact Real.rpow_pos_of_pos (sub_pos.mpr hp1) _
  have hqle : q ≤ 1 := by
    dsimp only [q]
    have hhazard := quittingMeshHazard_nonneg m hp0 hp1.le
    linarith
  have hqpow : q ^ m = 1 - p := by
    dsimp only [q]
    exact one_sub_quittingMeshHazard_pow hp1.le hm
  have harcWho : start who =
      p * root who + (1 - p) * next who := by
    simpa [quittingSingletonArcPayoff] using congrFun harc who
  have hstart : start who =
      root who + q ^ m * (next who - root who) := by
    rw [hqpow, harcWho]
    ring
  have hform := quittingMeshInterpolant_eq_pow_sub
    hqpos.ne' hk hstart
  rw [quittingMeshPayoffInterpolant_apply, hform]
  have hpowerLower : q ^ m ≤ q ^ (m - k) :=
    pow_le_pow_of_le_one hqpos.le hqle (Nat.sub_le m k)
  have hpowerUpper : q ^ (m - k) ≤ 1 :=
    pow_le_one₀ hqpos.le hqle
  by_cases hdirection : 0 ≤ next who - root who
  · have hscaled := mul_le_mul_of_nonneg_right hpowerUpper hdirection
    calc
      root who + q ^ (m - k) * (next who - root who) ≤
          root who + 1 * (next who - root who) :=
        add_le_add (le_refl _) hscaled
      _ = next who := by ring
      _ ≤ upper who := hupperNext who
  · have hscaled := mul_le_mul_of_nonpos_right
      hpowerLower (le_of_not_ge hdirection)
    calc
      root who + q ^ (m - k) * (next who - root who) ≤
          root who + q ^ m * (next who - root who) :=
        add_le_add (le_refl _) hscaled
      _ = start who := hstart.symm
      _ ≤ upper who := hupperStart who

/-! ## Closing one variable block -/

/-- The formal next interpolant is the actual payoff at the next flattened
time.  At the last offset this is exactly the next coarse value. -/
theorem quittingVariableSingletonMeshValue_succ_of_state
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (p : ℕ → ℝ)
    (coarse : ℕ → Payoff ι) (length : ℕ → ℕ)
    (hlength : ∀ block, 0 < length block)
    (hp1 : ∀ block, p block < 1)
    (harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (p block)
        (quittingSoloReward reward (owner block)) (coarse (block + 1)))
    {time block offset : ℕ}
    (hstate : quittingVariableMeshState length time = (block, offset)) :
    quittingMeshPayoffInterpolant
        (quittingSoloReward reward (owner block)) (coarse block)
        (1 - quittingMeshHazard (p block) (length block)) (offset + 1) =
      quittingVariableSingletonMeshValue reward owner p coarse length
        (time + 1) := by
  have hoffset : offset < length block := by
    have hvalid := quittingVariableMeshState_offset_lt length hlength time
    simpa only [hstate, Prod.snd, Prod.fst] using hvalid
  by_cases hinside : offset + 1 < length block
  · have hnextState :
        quittingVariableMeshState length (time + 1) =
          (block, offset + 1) := by
      rw [quittingVariableMeshState_succ, hstate]
      simp only [Prod.snd, Prod.fst]
      rw [if_pos hinside]
    simp [quittingVariableSingletonMeshValue, hnextState]
  · have hclose : offset + 1 = length block := by omega
    have hnextState :
        quittingVariableMeshState length (time + 1) =
          (block + 1, 0) := by
      rw [quittingVariableMeshState_succ, hstate]
      simp only [Prod.snd, Prod.fst]
      rw [if_neg hinside]
    calc
      quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner block)) (coarse block)
          (1 - quittingMeshHazard (p block) (length block)) (offset + 1) =
        coarse (block + 1) := by
          rw [hclose]
          exact quittingMeshPayoffInterpolant_at_length_eq_next
            (hp1 block) (hlength block) (harc block)
      _ = quittingVariableSingletonMeshValue reward owner p coarse length
          (time + 1) := by
        simp [quittingVariableSingletonMeshValue, hnextState]

/-! ## Local certificate and boundedness -/

/-- Every variable-mesh microstage has exact policy evaluation, exact
prescribed Continue, and quit-only error `D * h_t`. -/
theorem quittingVariableSingletonMesh_phase_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (p : ℕ → ℝ)
    (coarse : ℕ → Payoff ι) (length : ℕ → ℕ)
    (hlength : ∀ block, 0 < length block)
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    {D : ℝ} (hD : 0 ≤ D)
    (harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (p block)
        (quittingSoloReward reward (owner block)) (coarse (block + 1)))
    (hactive : ∀ block,
      coarse block (owner block) =
        quittingSoloReward reward (owner block) (owner block))
    (hcoarseSolo : ∀ block who,
      quittingSoloReward reward who who ≤ coarse block who)
    (hcollision : ∀ block other, other ≠ owner block →
      max (quittingSingletonCollisionReward reward (owner block) other -
        quittingSoloReward reward other other) 0 ≤ D)
    (time : ℕ) :
    quittingVariableSingletonMeshValue reward owner p coarse length time =
        quittingRootSuccessorPayoff reward
          (quittingVariableSingletonMeshValue reward owner p coarse length
            (time + 1))
          (quittingVariableSingletonMeshRoot owner p length hp0 hp1 time) ∧
      (∀ who,
        quittingStationaryFixedOpponentsContinueReward reward
              (quittingVariableSingletonMeshRoot owner p length hp0 hp1 time)
              who +
            quittingStationaryFixedOpponentsContinueMass
                (quittingVariableSingletonMeshRoot owner p length hp0 hp1 time)
                who *
              quittingVariableSingletonMeshValue reward owner p coarse length
                (time + 1) who =
          quittingVariableSingletonMeshValue reward owner p coarse length
            time who) ∧
      ∀ who,
        quittingStationaryFixedOpponentsQuitValue reward
            (quittingVariableSingletonMeshRoot owner p length hp0 hp1 time)
            who ≤
          quittingVariableSingletonMeshValue reward owner p coarse length
              time who +
            D * quittingMeshHazard
              (p (quittingVariableMeshState length time).1)
              (length (quittingVariableMeshState length time).1) := by
  generalize hstate : quittingVariableMeshState length time = state
  rcases state with ⟨block, offset⟩
  have hoffset : offset < length block := by
    have hvalid := quittingVariableMeshState_offset_lt length hlength time
    simpa only [hstate, Prod.snd, Prod.fst] using hvalid
  have hsoloLocal : ∀ who,
      quittingSoloReward reward who who ≤
        quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner block)) (coarse block)
          (1 - quittingMeshHazard (p block) (length block)) offset who := by
    intro who
    exact le_quittingMeshPayoffInterpolant_of_arcEndpoints
      (hp0 block) (hp1 block) (hlength block) (harc block)
      (hcoarseSolo block) (hcoarseSolo (block + 1))
      offset hoffset.le who
  have hcertificate :=
    singletonMeshStationaryRoot_interpolant_certificate
      reward (owner block) (length block) (hp0 block) (hp1 block)
      (quittingSoloReward reward (owner block)) (coarse block) offset
      hD rfl (hactive block) hsoloLocal (hcollision block)
  have hnext := quittingVariableSingletonMeshValue_succ_of_state
    reward owner p coarse length hlength hp1 harc hstate
  rw [hnext] at hcertificate
  simpa [quittingVariableSingletonMeshValue,
    quittingVariableSingletonMeshRoot, hstate] using hcertificate

/-- Absolute coarse endpoint bounds are inherited by every variable-mesh
microvalue. -/
theorem abs_quittingVariableSingletonMeshValue_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (p : ℕ → ℝ)
    (coarse : ℕ → Payoff ι) (length : ℕ → ℕ)
    (hlength : ∀ block, 0 < length block)
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (p block)
        (quittingSoloReward reward (owner block)) (coarse (block + 1)))
    {bound : ℝ}
    (hcoarseBound : ∀ block who, |coarse block who| ≤ bound)
    (time : ℕ) (who : ι) :
    |quittingVariableSingletonMeshValue reward owner p coarse length time who| ≤
      bound := by
  generalize hstate : quittingVariableMeshState length time = state
  rcases state with ⟨block, offset⟩
  have hoffset : offset < length block := by
    have hvalid := quittingVariableMeshState_offset_lt length hlength time
    simpa only [hstate, Prod.snd, Prod.fst] using hvalid
  have hlower := le_quittingMeshPayoffInterpolant_of_arcEndpoints
    (hp0 block) (hp1 block) (hlength block) (harc block)
    (fun player => (abs_le.mp (hcoarseBound block player)).1)
    (fun player => (abs_le.mp (hcoarseBound (block + 1) player)).1)
    offset hoffset.le who
  have hupper := quittingMeshPayoffInterpolant_le_of_arcEndpoints
    (hp0 block) (hp1 block) (hlength block) (harc block)
    (fun player => (abs_le.mp (hcoarseBound block player)).2)
    (fun player => (abs_le.mp (hcoarseBound (block + 1) player)).2)
    offset hoffset.le who
  rw [abs_le]
  constructor
  · simpa [quittingVariableSingletonMeshValue, hstate] using hlower
  · simpa [quittingVariableSingletonMeshValue, hstate] using hupper

/-! ## Exact preservation of coarse opponent survival -/

/-- Fixed-opponent continuation at one microstage. -/
theorem quittingVariableSingletonMeshRoot_continueMass_of_state
    (owner : ℕ → ι) (p : ℕ → ℝ) (length : ℕ → ℕ)
    (hp0 : ∀ time, 0 ≤ p time) (hp1 : ∀ time, p time < 1)
    {time block offset : ℕ}
    (hstate : quittingVariableMeshState length time = (block, offset))
    (who : ι) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingVariableSingletonMeshRoot owner p length hp0 hp1 time) who =
      if who = owner block then 1
      else 1 - quittingMeshHazard (p block) (length block) := by
  by_cases howner : who = owner block
  · subst who
    simp [quittingVariableSingletonMeshRoot, hstate]
  · rw [if_neg howner]
    simp only [quittingVariableSingletonMeshRoot, hstate,
      Prod.fst, Prod.snd]
    rw [quittingStationaryFixedOpponentsContinueMass_solo_other howner]
    exact quittingMeshHazardCoin_false_toReal
      (p block) (length block) (hp0 block) (hp1 block)

/-- Fixed-opponent continuation at one unsubdivided coarse root. -/
theorem quittingVariableSingletonCoarseRoot_continueMass
    (owner : ℕ → ι) (p : ℕ → ℝ)
    (hp0 : ∀ time, 0 ≤ p time) (hp1 : ∀ time, p time < 1)
    (block : ℕ) (who : ι) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingVariableSingletonCoarseRoot owner p hp0 hp1 block) who =
      if who = owner block then 1 else 1 - p block := by
  by_cases howner : who = owner block
  · subst who
    simp [quittingVariableSingletonCoarseRoot]
  · rw [if_neg howner]
    unfold quittingVariableSingletonCoarseRoot
    rw [quittingStationaryFixedOpponentsContinueMass_solo_other howner]
    exact quittingHazardCoin_false_toReal
      (p block) (hp0 block) (hp1 block).le

/-- The microfactors in one variable block multiply to its original coarse
opponent-continuation factor. -/
theorem prod_quittingVariableSingletonMeshRoot_continueMass_block
    (owner : ℕ → ι) (p : ℕ → ℝ) (length : ℕ → ℕ)
    (hlength : ∀ block, 0 < length block)
    (hp0 : ∀ time, 0 ≤ p time) (hp1 : ∀ time, p time < 1)
    (block : ℕ) (who : ι) :
    (∏ offset ∈ Finset.range (length block),
      quittingStationaryFixedOpponentsContinueMass
        (quittingVariableSingletonMeshRoot owner p length hp0 hp1
          (quittingVariableMeshBoundary length block + offset)) who) =
      if who = owner block then 1 else 1 - p block := by
  calc
    (∏ offset ∈ Finset.range (length block),
      quittingStationaryFixedOpponentsContinueMass
        (quittingVariableSingletonMeshRoot owner p length hp0 hp1
          (quittingVariableMeshBoundary length block + offset)) who) =
        ∏ _offset ∈ Finset.range (length block),
          if who = owner block then 1
          else 1 - quittingMeshHazard (p block) (length block) := by
      apply Finset.prod_congr rfl
      intro offset hoffset
      exact quittingVariableSingletonMeshRoot_continueMass_of_state
        owner p length hp0 hp1
        (quittingVariableMeshState_boundary_add length hlength block offset
          (Finset.mem_range.mp hoffset)) who
    _ = if who = owner block then 1 else 1 - p block := by
      by_cases howner : who = owner block
      · simp [howner]
      · simpa [howner] using
          one_sub_quittingMeshHazard_pow
            (p := p block) (m := length block)
            (hp1 block).le (hlength block)

/-- Initial micro-survival at every coarse boundary equals initial survival of
the unsubdivided singleton path. -/
theorem quittingVariableSingletonMesh_survival_boundary_eq_coarse
    (owner : ℕ → ι) (p : ℕ → ℝ) (length : ℕ → ℕ)
    (hlength : ∀ block, 0 < length block)
    (hp0 : ∀ time, 0 ≤ p time) (hp1 : ∀ time, p time < 1)
    (who : ι) :
    ∀ block,
      quittingOpponentSurvivalWeight
          (quittingVariableSingletonMeshRoot owner p length hp0 hp1)
          who 0 (quittingVariableMeshBoundary length block) =
        quittingOpponentSurvivalWeight
          (quittingVariableSingletonCoarseRoot owner p hp0 hp1)
          who 0 block := by
  intro block
  induction block with
  | zero => simp [quittingOpponentSurvivalWeight]
  | succ block ih =>
      have hmicroBlock :
          quittingOpponentSurvivalWeight
              (quittingVariableSingletonMeshRoot owner p length hp0 hp1)
              who (quittingVariableMeshBoundary length block)
              (length block) =
            if who = owner block then 1 else 1 - p block := by
        simpa [quittingOpponentSurvivalWeight] using
          prod_quittingVariableSingletonMeshRoot_continueMass_block
            owner p length hlength hp0 hp1 block who
      have hcoarseFactor := quittingVariableSingletonCoarseRoot_continueMass
        owner p hp0 hp1 block who
      calc
        quittingOpponentSurvivalWeight
            (quittingVariableSingletonMeshRoot owner p length hp0 hp1)
            who 0 (quittingVariableMeshBoundary length (block + 1)) =
          quittingOpponentSurvivalWeight
              (quittingVariableSingletonMeshRoot owner p length hp0 hp1)
              who 0 (quittingVariableMeshBoundary length block) *
            quittingOpponentSurvivalWeight
              (quittingVariableSingletonMeshRoot owner p length hp0 hp1)
              who (quittingVariableMeshBoundary length block)
                (length block) := by
          rw [quittingVariableMeshBoundary_succ,
            quittingOpponentSurvivalWeight_add]
          simp
        _ = quittingOpponentSurvivalWeight
              (quittingVariableSingletonCoarseRoot owner p hp0 hp1)
              who 0 block *
            quittingStationaryFixedOpponentsContinueMass
              (quittingVariableSingletonCoarseRoot owner p hp0 hp1 block) who := by
          rw [ih, hmicroBlock, hcoarseFactor]
        _ = quittingOpponentSurvivalWeight
              (quittingVariableSingletonCoarseRoot owner p hp0 hp1)
              who 0 (block + 1) := by
          symm
          simpa only [Nat.zero_add] using
            quittingOpponentSurvivalWeight_succ
              (quittingVariableSingletonCoarseRoot owner p hp0 hp1)
              who 0 block

/-- Exact boundary preservation lifts convergence of the coarse initial
opponent-survival clock to the flattened microtime clock. -/
theorem tendsto_zero_quittingVariableSingletonMesh_survival
    (owner : ℕ → ι) (p : ℕ → ℝ) (length : ℕ → ℕ)
    (hlength : ∀ block, 0 < length block)
    (hp0 : ∀ time, 0 ≤ p time) (hp1 : ∀ time, p time < 1)
    (who : ι)
    (hcoarse : Tendsto
      (quittingOpponentSurvivalWeight
        (quittingVariableSingletonCoarseRoot owner p hp0 hp1) who 0)
      atTop (nhds 0)) :
    Tendsto
      (quittingOpponentSurvivalWeight
        (quittingVariableSingletonMeshRoot owner p length hp0 hp1) who 0)
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop] at hcoarse ⊢
  intro epsilon hepsilon
  obtain ⟨block, hblock⟩ := hcoarse epsilon hepsilon
  refine ⟨quittingVariableMeshBoundary length block, ?_⟩
  intro fuel hfuel
  have hmono := antitone_quittingOpponentSurvivalWeight
    (quittingVariableSingletonMeshRoot owner p length hp0 hp1) who 0 hfuel
  have hclose := hblock block le_rfl
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (quittingOpponentSurvivalWeight_nonneg
      (quittingVariableSingletonCoarseRoot owner p hp0 hp1) who 0 block)]
      at hclose
  rw [Real.dist_eq, sub_zero,
    abs_of_nonneg (quittingOpponentSurvivalWeight_nonneg
      (quittingVariableSingletonMeshRoot owner p length hp0 hp1) who 0 fuel)]
  apply hmono.trans_lt
  rw [quittingVariableSingletonMesh_survival_boundary_eq_coarse
    owner p length hlength hp0 hp1 who block]
  exact hclose

/-! ## Adaptive nonperiodic terminal compiler -/

/-- **Adaptive variable-mesh compiler.**  Every coarse arc receives enough
microstages to make its hazard smaller than `delta`.  Exact block products
preserve coarse survival, so the resulting nonperiodic profile is terminal
`D * delta`-Nash and delivers the first coarse value exactly. -/
theorem adaptiveVariableSingletonMesh_isTerminalNash_and_delivers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ℕ → ι) (p : ℕ → ℝ) (coarse : ℕ → Payoff ι)
    {delta D bound : ℝ}
    (hdelta : 0 < delta) (hD : 0 ≤ D) (hbound : 0 ≤ bound)
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (hcoarseBound : ∀ block who, |coarse block who| ≤ bound)
    (harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (p block)
        (quittingSoloReward reward (owner block)) (coarse (block + 1)))
    (hactive : ∀ block,
      coarse block (owner block) =
        quittingSoloReward reward (owner block) (owner block))
    (hcoarseSolo : ∀ block who,
      quittingSoloReward reward who who ≤ coarse block who)
    (hcollision : ∀ block other, other ≠ owner block →
      max (quittingSingletonCollisionReward reward (owner block) other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hcoarseSurvival : ∀ who,
      Tendsto (quittingOpponentSurvivalWeight
        (quittingVariableSingletonCoarseRoot owner p hp0 hp1) who 0)
        atTop (nhds 0)) :
    let length := fun block => quittingAdaptiveMeshLength (p block) delta
    let roots := quittingVariableSingletonMeshRoot owner p length hp0 hp1
    let value := quittingVariableSingletonMeshValue
      reward owner p coarse length
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (D * delta)
        (quittingInfinitePathProfile reward roots) ∧
      quittingTerminalPayoff reward
          (quittingInfinitePathProfile reward roots) = coarse 0 := by
  dsimp only
  let length : ℕ → ℕ := fun block =>
    quittingAdaptiveMeshLength (p block) delta
  let roots := quittingVariableSingletonMeshRoot owner p length hp0 hp1
  let value := quittingVariableSingletonMeshValue
    reward owner p coarse length
  have hlength : ∀ block, 0 < length block := by
    intro block
    exact quittingAdaptiveMeshLength_pos (hp0 block) (hp1 block) hdelta
  have hhazard : ∀ block,
      quittingMeshHazard (p block) (length block) < delta := by
    intro block
    exact quittingMeshHazard_adaptive_lt
      (hp0 block) (hp1 block) hdelta
  have hcertificate : ∀ time,
      value time = quittingRootSuccessorPayoff reward
          (value (time + 1)) (roots time) ∧
        (∀ who,
          quittingStationaryFixedOpponentsContinueReward reward
                (roots time) who +
              quittingStationaryFixedOpponentsContinueMass
                  (roots time) who * value (time + 1) who =
            value time who) ∧
        ∀ who,
          quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
            value time who + D * quittingMeshHazard
              (p (quittingVariableMeshState length time).1)
              (length (quittingVariableMeshState length time).1) := by
    intro time
    exact quittingVariableSingletonMesh_phase_certificate
      reward owner p coarse length hlength hp0 hp1 hD harc hactive
        hcoarseSolo hcollision time
  have hpolicy := fun time => (hcertificate time).1
  have hcontinue := fun time => (hcertificate time).2.1
  have hquit : ∀ time who,
      quittingStationaryFixedOpponentsQuitValue reward (roots time) who ≤
        value time who + D * delta := by
    intro time who
    have hlocal := (hcertificate time).2.2 who
    have hscaled := mul_le_mul_of_nonneg_left
      (hhazard (quittingVariableMeshState length time).1).le hD
    exact hlocal.trans (add_le_add (le_refl _) hscaled)
  have hvalueBound : ∀ time who, |value time who| ≤ bound := by
    intro time who
    exact abs_quittingVariableSingletonMeshValue_le
      reward owner p coarse length hlength hp0 hp1 harc hcoarseBound time who
  have hsurvival : ∀ who,
      Tendsto (quittingOpponentSurvivalWeight roots who 0)
        atTop (nhds 0) := by
    intro who
    exact tendsto_zero_quittingVariableSingletonMesh_survival
      owner p length hlength hp0 hp1 who (hcoarseSurvival who)
  obtain ⟨hnash, hdelivery⟩ :=
    infinitePath_isεAsymptoticNash_and_delivers_of_quitError_exactContinue
      reward roots value (mul_nonneg hD hdelta.le) hbound hreward
        hvalueBound hpolicy hquit hcontinue hsurvival
  constructor
  · simpa only [roots] using hnash
  · simpa [roots, value] using hdelivery

end GameTheory
