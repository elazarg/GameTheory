/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Terminal.TargetTail.TerminalUniformization

/-!
# Cyclic assembly of subdivided singleton-flow arcs

This file assembles the one-microstage stationary-root certificate over the
lexicographically indexed phase space `Fin (L * m)`.  The key bookkeeping fact
is that `finRotate (L*m)` increments the micro-offset inside a block and sends
the final offset to offset zero of the next coarse block.
-/

noncomputable section

namespace GameTheory

open StochasticGame Filter Math.Probability Math.PMFProduct

variable {L m : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Constructor for a block/offset phase in the canonical `L * m` ordering. -/
def quittingSingletonMeshPhase
    (block : Fin L) (offset : Fin m) : Fin (L * m) :=
  finProdFinEquiv (block, offset)

/-- Offset-zero phase of a selected coarse block. -/
def quittingSingletonMeshInitialPhase
    (block : Fin L) (m : ℕ) (hm : 0 < m) : Fin (L * m) :=
  quittingSingletonMeshPhase block ⟨0, hm⟩

@[simp] theorem quittingSingletonMeshBlock_phase
    (block : Fin L) (offset : Fin m) :
    quittingSingletonMeshBlock
        (quittingSingletonMeshPhase block offset) = block := by
  simp [quittingSingletonMeshBlock, quittingSingletonMeshPhase]

@[simp] theorem quittingSingletonMeshOffset_phase
    (block : Fin L) (offset : Fin m) :
    quittingSingletonMeshOffset
        (quittingSingletonMeshPhase block offset) = offset := by
  simp [quittingSingletonMeshOffset, quittingSingletonMeshPhase]

theorem quittingSingletonMeshPhase_block_offset
    (phase : Fin (L * m)) :
    quittingSingletonMeshPhase
        (quittingSingletonMeshBlock phase)
        (quittingSingletonMeshOffset phase) = phase := by
  exact Equiv.apply_symm_apply finProdFinEquiv phase

/-- Numeric form of `finRotate`: increment modulo the cardinality. -/
theorem coe_finRotate_eq_succ_mod {n : ℕ} (phase : Fin n) :
    (finRotate n phase : ℕ) = (phase.val + 1) % n := by
  letI : NeZero n := phase.neZero
  rw [finRotate_apply, Fin.val_add]
  have hone : ((1 : Fin n) : ℕ) = 1 % n := Fin.val_natCast 1 n
  rw [hone]
  calc
    (phase.val + 1 % n) % n =
        (phase.val % n + 1 % n) % n := by
      rw [Nat.mod_eq_of_lt phase.isLt]
    _ = (phase.val + 1) % n := (Nat.add_mod phase.val 1 n).symm

/-- Rotation increments a nonfinal micro-offset without changing its block. -/
theorem finRotate_quittingSingletonMeshPhase_of_offset_succ_lt
    (block : Fin L) (offset : Fin m)
    (hoffset : offset.val + 1 < m) :
    finRotate (L * m) (quittingSingletonMeshPhase block offset) =
      quittingSingletonMeshPhase block
        ⟨offset.val + 1, hoffset⟩ := by
  apply Fin.eq_of_val_eq
  rw [coe_finRotate_eq_succ_mod]
  simp only [finProdFinEquiv_apply_val,
    quittingSingletonMeshPhase]
  have htotal : offset.val + m * block.val + 1 < L * m := by
    have hblock : block.val + 1 ≤ L := block.isLt
    have hmul : m * (block.val + 1) ≤ m * L :=
      Nat.mul_le_mul_left m hblock
    calc
      offset.val + m * block.val + 1 < m + m * block.val := by
        omega
      _ = m * (block.val + 1) := by ring
      _ ≤ m * L := hmul
      _ = L * m := by ring
  rw [Nat.mod_eq_of_lt htotal]
  omega

/-- Rotation sends the final offset of a block to offset zero of the next
coarse block, including wraparound at the last coarse block. -/
theorem finRotate_quittingSingletonMeshPhase_of_offset_succ_eq
    (block : Fin L) (offset : Fin m) (hm : 0 < m)
    (hoffset : offset.val + 1 = m) :
    finRotate (L * m) (quittingSingletonMeshPhase block offset) =
      quittingSingletonMeshPhase (finRotate L block) ⟨0, hm⟩ := by
  apply Fin.eq_of_val_eq
  rw [coe_finRotate_eq_succ_mod
      (quittingSingletonMeshPhase block offset)]
  simp only [finProdFinEquiv_apply_val,
    quittingSingletonMeshPhase, zero_add]
  rw [coe_finRotate_eq_succ_mod block]
  have hnum : offset.val + m * block.val + 1 =
      (block.val + 1) * m := by
    calc
      offset.val + m * block.val + 1 =
          (offset.val + 1) + m * block.val := by omega
      _ = m + m * block.val := by rw [hoffset]
      _ = (block.val + 1) * m := by ring
  rw [hnum, Nat.mul_mod_mul_right]
  ring

/-! ## Concrete arc-cycle data -/

/-- Stationary singleton root prescribed at a subdivided phase. -/
def quittingSingletonArcCycleRoot
    (owner : Fin L → ι) (p : Fin L → ℝ) (m : ℕ)
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (phase : Fin (L * m)) : ι → PMF Bool :=
  let block := quittingSingletonMeshBlock phase
  quittingSoloStationaryRoot (owner block)
    (quittingMeshHazardCoin (p block) m (hp0 block) (hp1 block))

/-- Interpolated payoff attached to a subdivided phase. -/
def quittingSingletonArcCycleValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : Fin L → ι) (p : Fin L → ℝ)
    (coarse : Fin L → Payoff ι) (m : ℕ)
    (phase : Fin (L * m)) : Payoff ι :=
  let block := quittingSingletonMeshBlock phase
  quittingMeshPayoffInterpolant
    (quittingSoloReward reward (owner block)) (coarse block)
    (1 - quittingMeshHazard (p block) m)
    (quittingSingletonMeshOffset phase).val

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem quittingSingletonArcCycleValue_initialPhase
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : Fin L → ι) (p : Fin L → ℝ)
    (coarse : Fin L → Payoff ι) (block : Fin L)
    (m : ℕ) (hm : 0 < m) :
    quittingSingletonArcCycleValue reward owner p coarse m
        (quittingSingletonMeshInitialPhase block m hm) = coarse block := by
  funext who
  simp [quittingSingletonArcCycleValue,
    quittingSingletonMeshInitialPhase,
    quittingMeshInterpolant]

omit [Fintype ι] [DecidableEq ι] in
/-- The value at the rotated phase is exactly the next interpolant used by
the local microstage certificate.  At a block boundary this is the coarse arc
closure theorem. -/
theorem quittingSingletonArcCycleValue_rotate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : Fin L → ι) (p : Fin L → ℝ)
    (coarse : Fin L → Payoff ι) (m : ℕ) (hm : 0 < m)
    (hp1 : ∀ block, p block < 1)
    (harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (p block)
        (quittingSoloReward reward (owner block))
        (coarse (finRotate L block)))
    (phase : Fin (L * m)) :
    quittingSingletonArcCycleValue reward owner p coarse m
        (finRotate (L * m) phase) =
      quittingMeshPayoffInterpolant
        (quittingSoloReward reward
          (owner (quittingSingletonMeshBlock phase)))
        (coarse (quittingSingletonMeshBlock phase))
        (1 - quittingMeshHazard
          (p (quittingSingletonMeshBlock phase)) m)
        ((quittingSingletonMeshOffset phase).val + 1) := by
  let block := quittingSingletonMeshBlock phase
  let offset := quittingSingletonMeshOffset phase
  have hphase : quittingSingletonMeshPhase block offset = phase := by
    exact quittingSingletonMeshPhase_block_offset phase
  rw [← hphase]
  simp only [quittingSingletonMeshBlock_phase,
    quittingSingletonMeshOffset_phase]
  have hoffsetLe : offset.val + 1 ≤ m := offset.isLt
  rcases hoffsetLe.lt_or_eq with hoffset | hoffset
  · rw [finRotate_quittingSingletonMeshPhase_of_offset_succ_lt
        block offset hoffset]
    simp [quittingSingletonArcCycleValue]
  · rw [finRotate_quittingSingletonMeshPhase_of_offset_succ_eq
        block offset hm hoffset]
    simp only [quittingSingletonArcCycleValue,
      quittingSingletonMeshBlock_phase,
      quittingSingletonMeshOffset_phase]
    rw [hoffset]
    have hzero :
        quittingMeshPayoffInterpolant
            (quittingSoloReward reward
              (owner (finRotate L block)))
            (coarse (finRotate L block))
            (1 - quittingMeshHazard
              (p (finRotate L block)) m) 0 =
          coarse (finRotate L block) := by
      funext who
      simp [quittingMeshPayoffInterpolant, quittingMeshInterpolant]
    rw [hzero]
    exact (quittingMeshPayoffInterpolant_at_length_eq_next
      (hp1 block) hm (harc block)).symm

omit [Fintype ι] [DecidableEq ι] in
/-- Singleton lower bounds need only be checked at the finitely many coarse
vertices; the arc interpolants preserve them at every subdivision scale and
microphase. -/
theorem quittingSoloReward_le_quittingSingletonArcCycleValue_of_coarse
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : Fin L → ι) (p : Fin L → ℝ)
    (coarse : Fin L → Payoff ι) (m : ℕ) (hm : 0 < m)
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (p block)
        (quittingSoloReward reward (owner block))
        (coarse (finRotate L block)))
    (hcoarseSolo : ∀ block who,
      quittingSoloReward reward who who ≤ coarse block who)
    (phase : Fin (L * m)) (who : ι) :
    quittingSoloReward reward who who ≤
      quittingSingletonArcCycleValue reward owner p coarse m phase who := by
  let block := quittingSingletonMeshBlock phase
  let offset := quittingSingletonMeshOffset phase
  exact le_quittingMeshPayoffInterpolant_of_arcEndpoints
    (hp0 block) (hp1 block) hm (harc block)
    (hcoarseSolo block)
    (hcoarseSolo (finRotate L block))
    offset.val offset.isLt.le who

/-- Each phase of the assembled arc cycle satisfies exact prescribed policy
evaluation, exact prescribed-Continue transport, and the local `D * h` Quit
bound required by the cyclic supersolution compiler. -/
theorem quittingSingletonArcCycle_phase_certificate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : Fin L → ι) (p : Fin L → ℝ)
    (coarse : Fin L → Payoff ι) (m : ℕ) (hm : 0 < m)
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (p block)
        (quittingSoloReward reward (owner block))
        (coarse (finRotate L block)))
    {D : ℝ} (hD : 0 ≤ D)
    (hactive : ∀ block,
      coarse block (owner block) =
        quittingSoloReward reward (owner block) (owner block))
    (hcoarseSolo : ∀ block who,
      quittingSoloReward reward who who ≤ coarse block who)
    (hcollision : ∀ block other, other ≠ owner block →
      max (quittingSingletonCollisionReward
          reward (owner block) other -
        quittingSoloReward reward other other) 0 ≤ D)
    (phase : Fin (L * m)) :
    quittingSingletonArcCycleValue reward owner p coarse m phase =
        quittingRootSuccessorPayoff reward
          (quittingSingletonArcCycleValue reward owner p coarse m
            (finRotate (L * m) phase))
          (quittingSingletonArcCycleRoot owner p m hp0 hp1 phase) ∧
      (∀ who,
        quittingStationaryFixedOpponentsContinueReward reward
              (quittingSingletonArcCycleRoot owner p m hp0 hp1 phase) who +
            quittingStationaryFixedOpponentsContinueMass
                (quittingSingletonArcCycleRoot owner p m hp0 hp1 phase) who *
              quittingSingletonArcCycleValue reward owner p coarse m
                (finRotate (L * m) phase) who =
          quittingSingletonArcCycleValue reward owner p coarse m phase who) ∧
      ∀ who,
        quittingStationaryFixedOpponentsQuitValue reward
            (quittingSingletonArcCycleRoot owner p m hp0 hp1 phase) who ≤
          quittingSingletonArcCycleValue reward owner p coarse m phase who +
            D * quittingMeshHazard
              (p (quittingSingletonMeshBlock phase)) m := by
  let block := quittingSingletonMeshBlock phase
  let offset := quittingSingletonMeshOffset phase
  have hnext := quittingSingletonArcCycleValue_rotate
    reward owner p coarse m hm hp1 harc phase
  have hsoloLocal : ∀ who,
      quittingSoloReward reward who who ≤
        quittingMeshPayoffInterpolant
          (quittingSoloReward reward (owner block)) (coarse block)
          (1 - quittingMeshHazard (p block) m) offset.val who := by
    intro who
    have hphaseSolo :=
      quittingSoloReward_le_quittingSingletonArcCycleValue_of_coarse
        reward owner p coarse m hm hp0 hp1 harc hcoarseSolo phase who
    simpa only [quittingSingletonArcCycleValue, block, offset] using
      hphaseSolo
  have hcertificate :=
    singletonMeshStationaryRoot_interpolant_certificate
      reward (owner block) m (hp0 block) (hp1 block)
      (quittingSoloReward reward (owner block)) (coarse block) offset.val
      hD rfl (hactive block) hsoloLocal (hcollision block)
  dsimp only at hcertificate
  rw [← hnext] at hcertificate
  simpa only [quittingSingletonArcCycleValue,
    quittingSingletonArcCycleRoot, block, offset] using hcertificate

/-! ## Opponent-cycle product -/

/-- Fixed-opponent continuation mass at a concrete singleton microphase. -/
theorem quittingSingletonArcCycleRoot_continueMass_phase
    (owner : Fin L → ι) (p : Fin L → ℝ) (m : ℕ)
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (block : Fin L) (offset : Fin m) (who : ι) :
    quittingStationaryFixedOpponentsContinueMass
        (quittingSingletonArcCycleRoot owner p m hp0 hp1
          (quittingSingletonMeshPhase block offset)) who =
      if who = owner block then 1
      else 1 - quittingMeshHazard (p block) m := by
  by_cases howner : who = owner block
  · subst who
    simp [quittingSingletonArcCycleRoot]
  · rw [if_neg howner]
    simp only [quittingSingletonArcCycleRoot,
      quittingSingletonMeshBlock_phase]
    rw [quittingStationaryFixedOpponentsContinueMass_solo_other
      howner]
    exact quittingMeshHazardCoin_false_toReal
      (p block) m (hp0 block) (hp1 block)

/-- The `m` microstages in one coarse block contribute exactly the original
coarse opponent-continuation factor. -/
theorem prod_quittingSingletonArcCycleRoot_continueMass_block
    (owner : Fin L → ι) (p : Fin L → ℝ) (m : ℕ) (hm : 0 < m)
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (block : Fin L) (who : ι) :
    (∏ offset : Fin m,
      quittingStationaryFixedOpponentsContinueMass
        (quittingSingletonArcCycleRoot owner p m hp0 hp1
          (quittingSingletonMeshPhase block offset)) who) =
      if who = owner block then 1 else 1 - p block := by
  simp_rw [quittingSingletonArcCycleRoot_continueMass_phase]
  by_cases howner : who = owner block
  · simp [howner]
  · rw [if_neg howner, if_neg howner, Fin.prod_const]
    exact one_sub_quittingMeshHazard_pow (hp1 block).le hm

/-- The complete opponent-cycle continuation product is independent of the
subdivision scale: each coarse block contributes `1` to its owner and `1-p`
to every other player. -/
theorem prod_quittingSingletonArcCycleRoot_continueMass
    (owner : Fin L → ι) (p : Fin L → ℝ) (m : ℕ) (hm : 0 < m)
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (who : ι) :
    (∏ phase : Fin (L * m),
      quittingStationaryFixedOpponentsContinueMass
        (quittingSingletonArcCycleRoot owner p m hp0 hp1 phase) who) =
      ∏ block : Fin L,
        if who = owner block then 1 else 1 - p block := by
  let factor := fun phase : Fin (L * m) ↦
    quittingStationaryFixedOpponentsContinueMass
      (quittingSingletonArcCycleRoot owner p m hp0 hp1 phase) who
  rw [← finProdFinEquiv.prod_comp factor, Fintype.prod_prod_type]
  apply Fintype.prod_congr
  intro block
  exact prod_quittingSingletonArcCycleRoot_continueMass_block
    owner p m hm hp0 hp1 block who

/-! ## Fixed-m terminal compilation -/

/-- For one fixed subdivision count `m`, the concrete arc cycle is a terminal
`D * aStar / m`-Nash profile and its terminal payoff is exactly the selected
coarse value.  This is deliberately separate from the horizon-indexed
`m = ceil (sqrt N)` construction below. -/
theorem singletonArcCycle_isTerminalNash_and_hasValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : Fin L → ι) (p : Fin L → ℝ)
    (coarse : Fin L → Payoff ι) (initial : Fin L)
    (m : ℕ) (hm : 0 < m) {aStar D : ℝ}
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (ha : ∀ block, quittingMeshIntensity (p block) ≤ aStar)
    (hD : 0 ≤ D)
    (harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (p block)
        (quittingSoloReward reward (owner block))
        (coarse (finRotate L block)))
    (hactive : ∀ block,
      coarse block (owner block) =
        quittingSoloReward reward (owner block) (owner block))
    (hcoarseSolo : ∀ block who,
      quittingSoloReward reward who who ≤ coarse block who)
    (hcollision : ∀ block other, other ≠ owner block →
      max (quittingSingletonCollisionReward
          reward (owner block) other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hcoarseContracts : ∀ who,
      (∏ block : Fin L,
        if who = owner block then 1 else 1 - p block) < 1) :
    (quittingGame reward).IsεAsymptoticNash
        (quittingTerminalPayoff reward) (D * aStar / (m : ℝ))
        (quittingCyclicBehaviorProfile reward
          (quittingSingletonArcCycleRoot owner p m hp0 hp1)
          (quittingSingletonMeshInitialPhase initial m hm)) ∧
      quittingTerminalPayoff reward
          (quittingCyclicBehaviorProfile reward
            (quittingSingletonArcCycleRoot owner p m hp0 hp1)
            (quittingSingletonMeshInitialPhase initial m hm)) =
        coarse initial := by
  let cycle := quittingSingletonArcCycleRoot owner p m hp0 hp1
  let value := quittingSingletonArcCycleValue reward owner p coarse m
  let phase := quittingSingletonMeshInitialPhase initial m hm
  let terminalError := D * aStar / (m : ℝ)
  have haStar : 0 ≤ aStar :=
    (quittingMeshIntensity_nonneg (hp0 initial) (hp1 initial).le).trans
      (ha initial)
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hterminalError0 : 0 ≤ terminalError :=
    div_nonneg (mul_nonneg hD haStar) hmReal.le
  have hphaseCertificate : ∀ cyclePhase,
      value cyclePhase = quittingRootSuccessorPayoff reward
          (value (finRotate (L * m) cyclePhase)) (cycle cyclePhase) ∧
        (∀ who,
          quittingStationaryFixedOpponentsContinueReward reward
                (cycle cyclePhase) who +
              quittingStationaryFixedOpponentsContinueMass
                  (cycle cyclePhase) who *
                value (finRotate (L * m) cyclePhase) who =
            value cyclePhase who) ∧
        ∀ who,
          quittingStationaryFixedOpponentsQuitValue reward
              (cycle cyclePhase) who ≤
            value cyclePhase who + D * quittingMeshHazard
              (p (quittingSingletonMeshBlock cyclePhase)) m := by
    intro cyclePhase
    exact quittingSingletonArcCycle_phase_certificate
      reward owner p coarse m hm hp0 hp1 harc hD hactive hcoarseSolo
      hcollision cyclePhase
  have hpolicy := fun cyclePhase ↦ (hphaseCertificate cyclePhase).1
  have hcontinue := fun cyclePhase ↦
    (hphaseCertificate cyclePhase).2.1
  have hquitLocal := fun cyclePhase ↦
    (hphaseCertificate cyclePhase).2.2
  have hquit : ∀ cyclePhase who,
      quittingStationaryFixedOpponentsQuitValue reward
          (cycle cyclePhase) who ≤
        value cyclePhase who + terminalError := by
    intro cyclePhase who
    have hhazard := quittingMeshHazard_le_intensityBound_div
      (m := m) p hp1 ha (quittingSingletonMeshBlock cyclePhase)
    have hscaled := mul_le_mul_of_nonneg_left hhazard hD
    calc
      quittingStationaryFixedOpponentsQuitValue reward
            (cycle cyclePhase) who ≤
          value cyclePhase who + D * quittingMeshHazard
            (p (quittingSingletonMeshBlock cyclePhase)) m :=
        hquitLocal cyclePhase who
      _ ≤ value cyclePhase who + D * (aStar / (m : ℝ)) :=
        add_le_add (le_refl _) hscaled
      _ = value cyclePhase who + terminalError := by
        dsimp only [terminalError]
        ring
  have hcontracts : ∀ who,
      (∏ cyclePhase : Fin (L * m),
        quittingStationaryFixedOpponentsContinueMass
          (cycle cyclePhase) who) < 1 := by
    intro who
    dsimp only [cycle]
    rw [prod_quittingSingletonArcCycleRoot_continueMass
      owner p m hm hp0 hp1 who]
    exact hcoarseContracts who
  have hterminalNash : (quittingGame reward).IsεAsymptoticNash
      (quittingTerminalPayoff reward) terminalError
      (quittingCyclicBehaviorProfile reward cycle phase) :=
    isεAsymptoticNash_quittingCyclicBehaviorProfile_of_quitError_exactContinue
      reward cycle value phase hterminalError0
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
      hpolicy hquit hcontinue hcontracts
  constructor
  · simpa only [cycle, phase, terminalError] using hterminalNash
  · have hcyclicValue :=
      eq_quittingCyclicTerminalValue_of_rootSuccessorPayoff
        reward cycle value hpolicy hcontracts
    change quittingTerminalPayoff reward
        (quittingCyclicBehaviorProfile reward cycle phase) = coarse initial
    rw [quittingTerminalPayoff_cyclicBehaviorProfile, ← hcyclicValue]
    exact quittingSingletonArcCycleValue_initialPhase
      reward owner p coarse initial m hm

/-- If one coarse singleton-flow cycle admits the concrete subdivision
certificate at every positive mesh scale, then its selected coarse value is
itself a uniform-equilibrium payoff.

For each requested accuracy this proof chooses one sufficiently large, but
then fixed, `m`.  Terminal exploitability is `D * aStar / m`; terminal payoff
is exactly `coarse initial`; the finite quitting-game terminal-to-uniform
theorem supplies one profile valid at every sufficiently long horizon.  This
quantifier pattern is distinct from the horizon-indexed square-root family. -/
theorem singletonArcCycle_isUniformEquilibriumPayoff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : Fin L → ι) (p : Fin L → ℝ)
    (coarse : Fin L → Payoff ι) (initial : Fin L)
    {aStar D : ℝ}
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (ha : ∀ block, quittingMeshIntensity (p block) ≤ aStar)
    (hD : 0 ≤ D)
    (harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (p block)
        (quittingSoloReward reward (owner block))
        (coarse (finRotate L block)))
    (hactive : ∀ block,
      coarse block (owner block) =
        quittingSoloReward reward (owner block) (owner block))
    (hcoarseSolo : ∀ block who,
      quittingSoloReward reward who who ≤ coarse block who)
    (hcollision : ∀ block other, other ≠ owner block →
      max (quittingSingletonCollisionReward
          reward (owner block) other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hcoarseContracts : ∀ who,
      (∏ block : Fin L,
        if who = owner block then 1 else 1 - p block) < 1) :
    (quittingGame reward).IsUniformEquilibriumPayoff none
      (coarse initial) := by
  intro ε hε
  have haStar : 0 ≤ aStar :=
    (quittingMeshIntensity_nonneg (hp0 initial) (hp1 initial).le).trans
      (ha initial)
  have hA : 0 ≤ D * aStar := mul_nonneg hD haStar
  obtain ⟨m, hmLarge⟩ := exists_nat_gt (2 * (D * aStar) / ε)
  have hmReal : 0 < (m : ℝ) := by
    have hthreshold0 : 0 ≤ 2 * (D * aStar) / ε :=
      div_nonneg (mul_nonneg (by norm_num) hA) hε.le
    exact lt_of_le_of_lt hthreshold0 hmLarge
  have hm : 0 < m := by exact_mod_cast hmReal
  have hhalf : 0 < ε / 2 := by linarith
  have hterminalError : D * aStar / (m : ℝ) < ε / 2 := by
    have hscaled : 2 * (D * aStar) < (m : ℝ) * ε := by
      exact (div_lt_iff₀ hε).mp hmLarge
    rw [div_lt_iff₀ hmReal]
    nlinarith
  let cycle := quittingSingletonArcCycleRoot owner p m hp0 hp1
  let phase := quittingSingletonMeshInitialPhase initial m hm
  let profile := quittingCyclicBehaviorProfile reward cycle phase
  obtain ⟨hterminalNash, hterminalValue⟩ :=
    singletonArcCycle_isTerminalNash_and_hasValue
      reward owner p coarse initial m hm hp0 hp1 ha hD harc hactive
      hcoarseSolo hcollision hcoarseContracts
  have huniform : (quittingGame reward).IsUniformεEquilibrium
      none (ε / 2) profile := by
    exact quittingGame_isUniformεEquilibrium_of_terminalNash_finite
      reward profile hterminalError hterminalNash
  obtain ⟨nashThreshold, hnash⟩ := huniform
  have heventuallyDelivery : ∀ᶠ horizon : ℕ in atTop, ∀ who,
      |(quittingGame reward).finiteAveragePayoff none horizon profile who -
        coarse initial who| < ε := by
    apply Filter.eventually_all.mpr
    intro who
    have htendsto : Tendsto
        (fun horizon ↦
          (quittingGame reward).finiteAveragePayoff none horizon profile who)
        atTop (nhds (coarse initial who)) := by
      rw [← congrFun hterminalValue who]
      exact tendsto_finiteAveragePayoff_quittingGame reward profile who
    have hball := htendsto.eventually
      (Metric.ball_mem_nhds (coarse initial who) hε)
    filter_upwards [hball] with horizon hhorizon
    simpa only [Metric.mem_ball, Real.dist_eq] using hhorizon
  obtain ⟨deliveryThreshold, hdelivery⟩ :=
    Filter.eventually_atTop.1 heventuallyDelivery
  refine ⟨profile, max nashThreshold deliveryThreshold,
    fun horizon hhorizon ↦ ?_⟩
  constructor
  · exact (hnash horizon
      (le_trans (Nat.le_max_left _ _) hhorizon)).mono (by linarith)
  · intro who
    exact (hdelivery horizon
      (le_trans (Nat.le_max_right _ _) hhorizon) who).le

/-! ## Canonical horizon compilation from coarse arcs -/

/-- A coarse singleton-flow cycle compiles directly to the canonical
`ceil (sqrt N)` horizon profile.

Unlike `singletonFlowSqrtMesh_isHorizonNash_and_delivers_of_product_le`, the
cycle, phase values, and initial target in this theorem are not opaque inputs:
they are the stationary singleton roots and rpow interpolants constructed
above from `owner`, `p`, `coarse`, and the coarse arc equations. -/
theorem singletonArcCycle_isHorizonNash_and_delivers
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : Fin L → ι) (p : Fin L → ℝ)
    (coarse : Fin L → Payoff ι) (initial : Fin L)
    {N : ℕ} {aStar D rhoBar bound : ℝ}
    (hp0 : ∀ block, 0 ≤ p block) (hp1 : ∀ block, p block < 1)
    (ha : ∀ block, quittingMeshIntensity (p block) ≤ aStar)
    (hD : 0 ≤ D) (hrho : rhoBar < 1) (hbound : 0 ≤ bound)
    (hN : 1 ≤ (N : ℝ))
    (hreward : ∀ terminal who, |reward terminal who| ≤ bound)
    (harc : ∀ block,
      coarse block = quittingSingletonArcPayoff (p block)
        (quittingSoloReward reward (owner block))
        (coarse (finRotate L block)))
    (hactive : ∀ block,
      coarse block (owner block) =
        quittingSoloReward reward (owner block) (owner block))
    (hcoarseSolo : ∀ block who,
      quittingSoloReward reward who who ≤ coarse block who)
    (hcollision : ∀ block other, other ≠ owner block →
      max (quittingSingletonCollisionReward
          reward (owner block) other -
        quittingSoloReward reward other other) 0 ≤ D)
    (hcoarseProd : ∀ who,
      (∏ block : Fin L,
        if who = owner block then 1 else 1 - p block) ≤ rhoBar) :
    (quittingGame reward).IsεHorizonNash none N
        ((D * aStar +
            4 * bound * ((L : ℝ) / (1 - rhoBar))) /
          Real.sqrt (N : ℝ))
        (quittingCyclicBehaviorProfile reward
          (quittingSingletonArcCycleRoot owner p
            (quittingSqrtMeshScale N) hp0 hp1)
          (quittingSingletonMeshInitialPhase initial
            (quittingSqrtMeshScale N)
            (quittingSqrtMeshScale_spec hN).1)) ∧
      ∀ who,
        |(quittingGame reward).finiteAveragePayoff none N
            (quittingCyclicBehaviorProfile reward
              (quittingSingletonArcCycleRoot owner p
                (quittingSqrtMeshScale N) hp0 hp1)
              (quittingSingletonMeshInitialPhase initial
                (quittingSqrtMeshScale N)
                (quittingSqrtMeshScale_spec hN).1)) who -
            coarse initial who| ≤
          (2 * bound * ((L : ℝ) / (1 - rhoBar))) /
            Real.sqrt (N : ℝ) := by
  have hm := (quittingSqrtMeshScale_spec hN).1
  have hphaseCertificate : ∀ phase,
      quittingSingletonArcCycleValue reward owner p coarse
            (quittingSqrtMeshScale N) phase =
          quittingRootSuccessorPayoff reward
            (quittingSingletonArcCycleValue reward owner p coarse
              (quittingSqrtMeshScale N)
              (finRotate (L * quittingSqrtMeshScale N) phase))
            (quittingSingletonArcCycleRoot owner p
              (quittingSqrtMeshScale N) hp0 hp1 phase) ∧
        (∀ who,
          quittingStationaryFixedOpponentsContinueReward reward
                (quittingSingletonArcCycleRoot owner p
                  (quittingSqrtMeshScale N) hp0 hp1 phase) who +
              quittingStationaryFixedOpponentsContinueMass
                  (quittingSingletonArcCycleRoot owner p
                    (quittingSqrtMeshScale N) hp0 hp1 phase) who *
                quittingSingletonArcCycleValue reward owner p coarse
                  (quittingSqrtMeshScale N)
                  (finRotate (L * quittingSqrtMeshScale N) phase) who =
            quittingSingletonArcCycleValue reward owner p coarse
              (quittingSqrtMeshScale N) phase who) ∧
        ∀ who,
          quittingStationaryFixedOpponentsQuitValue reward
              (quittingSingletonArcCycleRoot owner p
                (quittingSqrtMeshScale N) hp0 hp1 phase) who ≤
            quittingSingletonArcCycleValue reward owner p coarse
                (quittingSqrtMeshScale N) phase who +
              D * quittingMeshHazard
                (p (quittingSingletonMeshBlock phase))
                (quittingSqrtMeshScale N) := by
    intro phase
    exact quittingSingletonArcCycle_phase_certificate
      reward owner p coarse (quittingSqrtMeshScale N) hm hp0 hp1 harc
      hD hactive hcoarseSolo hcollision phase
  have hpolicy := fun phase ↦ (hphaseCertificate phase).1
  have hcontinue := fun phase ↦ (hphaseCertificate phase).2.1
  have hquit := fun phase ↦ (hphaseCertificate phase).2.2
  have hprod : ∀ who,
      (∏ phase : Fin (L * quittingSqrtMeshScale N),
        quittingStationaryFixedOpponentsContinueMass
          (quittingSingletonArcCycleRoot owner p
            (quittingSqrtMeshScale N) hp0 hp1 phase) who) ≤ rhoBar := by
    intro who
    rw [prod_quittingSingletonArcCycleRoot_continueMass
      owner p (quittingSqrtMeshScale N) hm hp0 hp1 who]
    exact hcoarseProd who
  have hvaluePhase :
      quittingSingletonArcCycleValue reward owner p coarse
          (quittingSqrtMeshScale N)
          (quittingSingletonMeshInitialPhase initial
            (quittingSqrtMeshScale N) hm) = coarse initial :=
    quittingSingletonArcCycleValue_initialPhase
      reward owner p coarse initial (quittingSqrtMeshScale N) hm
  exact singletonFlowSqrtMesh_isHorizonNash_and_delivers_of_product_le
    reward p
    (quittingSingletonArcCycleRoot owner p
      (quittingSqrtMeshScale N) hp0 hp1)
    (quittingSingletonArcCycleValue reward owner p coarse
      (quittingSqrtMeshScale N))
    (quittingSingletonMeshInitialPhase initial
      (quittingSqrtMeshScale N) hm)
    (coarse initial) hp0 hp1 ha hD hrho hbound hN hreward
    hpolicy hcontinue hquit hprod hvaluePhase

end GameTheory
