/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonBlockApproximation
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonCapDebtLasso
import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.CyclicLabelAdapter
import UniformEquilibrium.Quitting.Classification.LCP.HomogeneousProducer

/-!
# Carrier bridge for diffuse singleton blocks

This file records the topological part of the three-core singleton-block
bridge. Repeating a literal positive-hazard singleton root gives an actual
finite prefix, hence preserves the terminal-semantic carrier.  Its prescribed
coordinate and cap clearance obey explicit scalar recurrences.  Therefore any
pointwise limit of such finite blocks is again a carrier point.

No root Nash hypothesis is used.
-/

noncomputable section

namespace GameTheory
namespace IdealSingletonCarrierBridge

open Filter Math.Probability Math.PMFProduct
open QuittingSureSetOwnerRepair QuittingLCPClassification
open IdealSingletonBlockApproximation
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Repeat one literal singleton-prefix map a finite number of times. -/
def repeatedSingletonPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (steps : ℕ) (pair : QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  (quittingTerminalSemanticPrefix reward
    (singletonHazardRoot owner p hp0 hp1))^[steps] pair

@[simp] theorem repeatedSingletonPrefix_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (pair : QuittingTerminalSemanticPair ι) :
    repeatedSingletonPrefix reward owner p hp0 hp1 0 pair = pair := rfl

@[simp] theorem repeatedSingletonPrefix_succ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (steps : ℕ) (pair : QuittingTerminalSemanticPair ι) :
    repeatedSingletonPrefix reward owner p hp0 hp1 (steps + 1) pair =
      quittingTerminalSemanticPrefix reward
        (singletonHazardRoot owner p hp0 hp1)
        (repeatedSingletonPrefix reward owner p hp0 hp1 steps pair) := by
  simp [repeatedSingletonPrefix, Function.iterate_succ_apply']

/-- Every finite singleton microblock preserves the actual compact carrier. -/
theorem repeatedSingletonPrefix_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (steps : ℕ) (pair : QuittingTerminalSemanticPair ι)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ S player, |reward S player| ≤ B)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    repeatedSingletonPrefix reward owner p hp0 hp1 steps pair ∈
      quittingTerminalSemanticCarrier reward := by
  induction steps with
  | zero => simpa
  | succ steps ih =>
      rw [show steps + 1 = Nat.succ steps by omega,
        Nat.succ_eq_add_one, repeatedSingletonPrefix_succ]
      exact quittingTerminalSemanticPrefix_mem_carrier reward _ _
        hB hreward ih

/-- A singleton step mixes every prescribed coordinate toward the payoff of
the owner's singleton terminal. -/
theorem prescribed_prefix_singletonHazardRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner who : ι)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (quittingTerminalSemanticPrefix reward
        (singletonHazardRoot owner p hp0 hp1) pair).1 who =
      (1 - p) * pair.1 who + p *
        reward (quittingProjectiveSingletonTerminal owner) who := by
  change quittingRootSuccessorPayoff reward pair.1
      (singletonHazardRoot owner p hp0 hp1) who = _
  unfold quittingRootSuccessorPayoff singletonHazardRoot
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add]
  rw [quittingRootAbsorbingContribution_sureSetOwnerRoot reward
    (T := ∅) (owner := owner) (by simp) p hp0 hp1 who]
  rw [stationaryContinueMass_sureSetOwnerRoot_empty]
  simp [quittingSureSetOwnerValue, quittingProjectiveSingletonTerminal]
  ring

/-- Closed form of the prescribed coordinate after a finite singleton
microblock. -/
theorem prescribed_repeatedSingletonPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner who : ι)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (steps : ℕ) :
    (repeatedSingletonPrefix reward owner p hp0 hp1 steps pair).1 who =
      (1 - p) ^ steps * pair.1 who +
        (1 - (1 - p) ^ steps) *
          reward (quittingProjectiveSingletonTerminal owner) who := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [repeatedSingletonPrefix_succ,
        prescribed_prefix_singletonHazardRoot, ih, pow_succ]
      ring

/-- Exact nonowner cap recurrence through a finite singleton microblock. -/
theorem capClearance_repeatedSingletonPrefix_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) {owner who : ι}
    (hne : who ≠ owner) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (steps : ℕ) :
    capClearance reward
        (repeatedSingletonPrefix reward owner p hp0 hp1 steps pair).2 who =
      scalarClearanceIter (1 - p) (pairSurplus reward who owner)
        (normalizedSoloMatrix reward who owner)
        (capClearance reward pair.2 who) steps := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [repeatedSingletonPrefix_succ,
        capClearance_prefix_singletonHazardRoot_other reward _ hne,
        scalarClearanceIter_succ, ih]
      unfold scalarClearanceStep
      congr 1 <;> ring

/-- If the owner starts above its own singleton payoff, its cap clearance is
fixed throughout the finite singleton microblock. -/
theorem capClearance_repeatedSingletonPrefix_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hclearance : 0 ≤ capClearance reward pair.2 owner)
    (steps : ℕ) :
    capClearance reward
        (repeatedSingletonPrefix reward owner p hp0 hp1 steps pair).2 owner =
      capClearance reward pair.2 owner := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [repeatedSingletonPrefix_succ]
      calc
        capClearance reward
            (quittingTerminalSemanticPrefix reward
              (singletonHazardRoot owner p hp0 hp1)
              (repeatedSingletonPrefix reward owner p hp0 hp1 steps pair)).2
              owner =
            capClearance reward
              (repeatedSingletonPrefix reward owner p hp0 hp1 steps pair).2
              owner :=
          capClearance_prefix_singletonHazardRoot_owner reward _ owner p hp0 hp1
            (by rw [ih]; exact hclearance)
        _ = capClearance reward pair.2 owner := ih

/-- Closedness is the only topological input needed to turn a convergent
family of finite singleton blocks into a carrier transition. -/
theorem mem_carrier_of_tendsto_repeatedSingletonPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair limit : QuittingTerminalSemanticPair ι)
    (owner : ι) (p : ℕ → ℝ)
    (hp0 : ∀ n, 0 ≤ p n) (hp1 : ∀ n, p n ≤ 1)
    (steps : ℕ → ℕ)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ S player, |reward S player| ≤ B)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward)
    (hlimit : Tendsto (fun n =>
      repeatedSingletonPrefix reward owner (p n) (hp0 n) (hp1 n)
        (steps n) pair) atTop (𝓝 limit)) :
    limit ∈ quittingTerminalSemanticCarrier reward := by
  apply isClosed_closure.mem_of_tendsto hlimit
  exact Filter.Eventually.of_forall fun n =>
    repeatedSingletonPrefix_mem_carrier reward owner (p n)
      (hp0 n) (hp1 n) (steps n) pair hB hreward hpair

/-! ## The actual diffuse mesh and its ideal limit -/

/-- The semantic pair predicted by the ideal singleton cap/debt operator. -/
def idealSingletonSemanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (α : ℝ) (pair : QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  (fun who =>
      α * pair.1 who + (1 - α) *
        reward (quittingProjectiveSingletonTerminal owner) who,
    fun who =>
      ownSingleton reward who +
        idealSingletonClearance (normalizedSoloMatrix reward) owner α
          (capClearance reward pair.2) who)

/-- The `n`th genuine finite approximation to an ideal singleton block.  It
uses `n+1` positive-hazard microstages whose total Continue mass is exactly
`α`. -/
def diffuseSingletonPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (n : ℕ) (pair : QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  let p := quittingMeshHazard (1 - α) (n + 1)
  repeatedSingletonPrefix reward owner p
    (quittingMeshHazard_nonneg (n + 1) (sub_nonneg.mpr hα1)
      (by linarith : 1 - α ≤ 1))
    (quittingMeshHazard_le_one (n + 1) (by linarith : 1 - α ≤ 1))
    (n + 1) pair

/-- Prescribed payoffs of every diffuse approximant already equal their
ideal-block value exactly; no limiting argument is needed for this half. -/
theorem prescribed_diffuseSingletonPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner who : ι)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) (n : ℕ) :
    (diffuseSingletonPrefix reward owner α hα0 hα1 n pair).1 who =
      (idealSingletonSemanticPair reward owner α pair).1 who := by
  unfold diffuseSingletonPrefix idealSingletonSemanticPair
  dsimp only
  rw [prescribed_repeatedSingletonPrefix]
  rw [one_sub_quittingMeshHazard_pow
    (p := 1 - α) (m := n + 1) (by linarith) (Nat.succ_pos n)]
  ring

/-- The cap vector of the genuine positive-hazard microblocks converges
coordinatewise to the ideal reflected singleton update. -/
theorem tendsto_diffuseSingletonPrefix_cap
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hclearance : ∀ who, 0 ≤ capClearance reward pair.2 who) :
    Tendsto (fun n =>
        (diffuseSingletonPrefix reward owner α hα0 hα1 n pair).2)
      atTop (𝓝 (idealSingletonSemanticPair reward owner α pair).2) := by
  apply tendsto_pi_nhds.2
  intro who
  have hp0 : 0 ≤ 1 - α := sub_nonneg.mpr hα1
  have hp1 : 1 - α ≤ 1 := by linarith
  by_cases hwho : who = owner
  · subst who
    have hclear : Tendsto (fun n =>
        capClearance reward
          (diffuseSingletonPrefix reward owner α hα0 hα1 n pair).2 owner)
        atTop (𝓝 (capClearance reward pair.2 owner)) := by
      apply tendsto_const_nhds.congr'
      exact Eventually.of_forall fun n => by
        unfold diffuseSingletonPrefix
        dsimp only
        exact capClearance_repeatedSingletonPrefix_owner reward pair owner _ _ _
          (hclearance owner) (n + 1) |>.symm
    have hadd := hclear.add_const (ownSingleton reward owner)
    simpa [capClearance, idealSingletonSemanticPair,
      idealSingletonClearance] using hadd
  · have hscalar := scalarClearanceIter_mesh_tendsto_ideal
        (α := α) (A := pairSurplus reward who owner)
        (M := normalizedSoloMatrix reward who owner)
        (t := capClearance reward pair.2 who) hα0 hα1 (hclearance who)
    have hclear : Tendsto (fun n =>
        capClearance reward
          (diffuseSingletonPrefix reward owner α hα0 hα1 n pair).2 who)
        atTop (𝓝 (max 0
          (α * capClearance reward pair.2 who +
            (1 - α) * normalizedSoloMatrix reward who owner))) := by
      apply hscalar.congr'
      exact Eventually.of_forall fun n => by
        unfold diffuseSingletonPrefix
        dsimp only
        exact capClearance_repeatedSingletonPrefix_other reward pair hwho _ _ _
          (n + 1) |>.symm
    have hadd := hclear.add_const (ownSingleton reward who)
    simpa [capClearance, idealSingletonSemanticPair,
      idealSingletonClearance, hwho, add_comm] using hadd

/-- Each ideal singleton semantic operator is the limit of explicit finite
positive-hazard prefix blocks on the actual semantic pair. -/
theorem tendsto_diffuseSingletonPrefix
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hclearance : ∀ who, 0 ≤ capClearance reward pair.2 who) :
    Tendsto (fun n => diffuseSingletonPrefix reward owner α hα0 hα1 n pair)
      atTop (𝓝 (idealSingletonSemanticPair reward owner α pair)) := by
  apply Filter.Tendsto.prodMk_nhds
  · apply tendsto_pi_nhds.2
    intro who
    apply tendsto_const_nhds.congr'
    exact Eventually.of_forall fun n =>
      (prescribed_diffuseSingletonPrefix reward pair owner who α hα0 hα1 n).symm
  · exact tendsto_diffuseSingletonPrefix_cap reward pair owner α hα0 hα1
      hclearance

/-- Therefore the ideal singleton operator itself preserves the compact
attainable terminal-semantic carrier. -/
theorem idealSingletonSemanticPair_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hclearance : ∀ who, 0 ≤ capClearance reward pair.2 who)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ S player, |reward S player| ≤ B)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    idealSingletonSemanticPair reward owner α pair ∈
      quittingTerminalSemanticCarrier reward := by
  apply isClosed_closure.mem_of_tendsto
    (tendsto_diffuseSingletonPrefix reward pair owner α hα0 hα1 hclearance)
  exact Eventually.of_forall fun n => by
    unfold diffuseSingletonPrefix
    dsimp only
    exact repeatedSingletonPrefix_mem_carrier reward owner _ _ _ (n + 1)
      pair hB hreward hpair

/-! ## Exact limiting debt accounting -/

theorem idealSingletonSemanticPair_debt_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) (α : ℝ) :
    quittingTerminalSemanticDebt
        (idealSingletonSemanticPair reward owner α pair) owner =
      α * quittingTerminalSemanticDebt pair owner +
        (1 - α) * capClearance reward pair.2 owner := by
  simp [quittingTerminalSemanticDebt, idealSingletonSemanticPair,
    idealSingletonClearance, capClearance, ownSingleton]
  ring

theorem idealSingletonSemanticPair_debt_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) {owner who : ι}
    (hne : who ≠ owner) (α : ℝ) :
    quittingTerminalSemanticDebt
        (idealSingletonSemanticPair reward owner α pair) who =
      α * quittingTerminalSemanticDebt pair who +
        max 0 (-(α * capClearance reward pair.2 who +
          (1 - α) * normalizedSoloMatrix reward who owner)) := by
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  unfold quittingTerminalSemanticDebt idealSingletonSemanticPair
    idealSingletonClearance capClearance ownSingleton
    quittingProjectiveLCPMatrix
  dsimp only
  rw [if_neg hne]
  rw [normalizedSoloMatrix_eq_projectiveLCPMatrix]
  unfold quittingProjectiveLCPMatrix
  by_cases hy : 0 ≤
      α * (pair.2 who -
          reward (quittingProjectiveSingletonTerminal who) who) +
        (1 - α) *
          (reward (quittingProjectiveSingletonTerminal owner) who -
            reward (quittingProjectiveSingletonTerminal who) who)
  · rw [max_eq_right hy, max_eq_left (neg_nonpos.mpr hy)]
    ring
  · have hy' :
        α * (pair.2 who -
            reward (quittingProjectiveSingletonTerminal who) who) +
          (1 - α) *
            (reward (quittingProjectiveSingletonTerminal owner) who -
              reward (quittingProjectiveSingletonTerminal who) who) ≤ 0 :=
      le_of_not_ge hy
    rw [max_eq_left hy', max_eq_right (neg_nonneg.mpr hy')]
    ring

/-- Formula (9): the total debt of the ideal semantic limit is exactly the
autonomous ideal singleton debt operator. -/
theorem idealSingletonSemanticPair_debtSum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) (α : ℝ) :
    quittingTerminalSemanticDebtSum
        (idealSingletonSemanticPair reward owner α pair) =
      idealSingletonDebt (normalizedSoloMatrix reward) owner α
        (capClearance reward pair.2)
        (quittingTerminalSemanticDebtSum pair) := by
  unfold quittingTerminalSemanticDebtSum idealSingletonDebt
  rw [Finset.mul_sum]
  rw [← Finset.add_sum_erase Finset.univ
    (fun who => quittingTerminalSemanticDebt
      (idealSingletonSemanticPair reward owner α pair) who)
    (Finset.mem_univ owner)]
  rw [idealSingletonSemanticPair_debt_owner]
  have hsumOther :
      (∑ who ∈ Finset.univ.erase owner,
        quittingTerminalSemanticDebt
          (idealSingletonSemanticPair reward owner α pair) who) =
        ∑ who ∈ Finset.univ.erase owner,
          (α * quittingTerminalSemanticDebt pair who +
            max 0 (-(α * capClearance reward pair.2 who +
              (1 - α) * normalizedSoloMatrix reward who owner))) := by
    apply Finset.sum_congr rfl
    intro who hwho
    exact idealSingletonSemanticPair_debt_other reward pair
      (Finset.ne_of_mem_erase hwho) α
  rw [hsumOther, Finset.sum_add_distrib]
  rw [← Finset.add_sum_erase Finset.univ
    (fun who => α * quittingTerminalSemanticDebt pair who)
    (Finset.mem_univ owner)]
  ring

/-! ## Finite concatenation and lasso iteration -/

theorem capClearance_idealSingletonSemanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) (α : ℝ) :
    capClearance reward
        (idealSingletonSemanticPair reward owner α pair).2 =
      idealSingletonClearance (normalizedSoloMatrix reward) owner α
        (capClearance reward pair.2) := by
  funext who
  simp [capClearance, idealSingletonSemanticPair]

theorem capClearance_idealSingletonSemanticPair_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι) (owner : ι) (α : ℝ)
    (hclearance : ∀ who, 0 ≤ capClearance reward pair.2 who) :
    ∀ who, 0 ≤ capClearance reward
      (idealSingletonSemanticPair reward owner α pair).2 who := by
  intro who
  rw [capClearance_idealSingletonSemanticPair]
  by_cases hwho : who = owner
  · subst who
    simpa [idealSingletonClearance] using hclearance owner
  · simp [idealSingletonClearance, hwho]

/-- The cap-clearance action of three successive ideal singleton blocks. -/
def threeIdealSingletonClearance
    (M : ι → ι → ℝ)
    (owner₁ owner₂ owner₃ : ι) (α₁ α₂ α₃ : ℝ)
    (t : ι → ℝ) : ι → ℝ :=
  idealSingletonClearance M owner₃ α₃
    (idealSingletonClearance M owner₂ α₂
      (idealSingletonClearance M owner₁ α₁ t))

/-- The corresponding three-block semantic lasso map. -/
def threeIdealSingletonLasso
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner₁ owner₂ owner₃ : ι) (α₁ α₂ α₃ : ℝ)
    (pair : QuittingTerminalSemanticPair ι) :
    QuittingTerminalSemanticPair ι :=
  idealSingletonSemanticPair reward owner₃ α₃
    (idealSingletonSemanticPair reward owner₂ α₂
      (idealSingletonSemanticPair reward owner₁ α₁ pair))

theorem capClearance_threeIdealSingletonLasso
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (owner₁ owner₂ owner₃ : ι) (α₁ α₂ α₃ : ℝ) :
    capClearance reward
        (threeIdealSingletonLasso reward owner₁ owner₂ owner₃
          α₁ α₂ α₃ pair).2 =
      threeIdealSingletonClearance (normalizedSoloMatrix reward)
        owner₁ owner₂ owner₃ α₁ α₂ α₃ (capClearance reward pair.2) := by
  unfold threeIdealSingletonLasso threeIdealSingletonClearance
  rw [capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair]

/-- Three ideal singleton blocks may be concatenated inside the carrier. -/
theorem threeIdealSingletonLasso_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (owner₁ owner₂ owner₃ : ι) (α₁ α₂ α₃ : ℝ)
    (hα₁0 : 0 < α₁) (hα₁1 : α₁ ≤ 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ ≤ 1)
    (hα₃0 : 0 < α₃) (hα₃1 : α₃ ≤ 1)
    (hclearance : ∀ who, 0 ≤ capClearance reward pair.2 who)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ S player, |reward S player| ≤ B)
    (hpair : pair ∈ quittingTerminalSemanticCarrier reward) :
    threeIdealSingletonLasso reward owner₁ owner₂ owner₃ α₁ α₂ α₃ pair ∈
      quittingTerminalSemanticCarrier reward := by
  let pair₁ := idealSingletonSemanticPair reward owner₁ α₁ pair
  let pair₂ := idealSingletonSemanticPair reward owner₂ α₂ pair₁
  have hpair₁ : pair₁ ∈ quittingTerminalSemanticCarrier reward :=
    idealSingletonSemanticPair_mem_carrier reward pair owner₁ α₁ hα₁0 hα₁1
      hclearance hB hreward hpair
  have hclearance₁ : ∀ who, 0 ≤ capClearance reward pair₁.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward pair owner₁ α₁
      hclearance
  have hpair₂ : pair₂ ∈ quittingTerminalSemanticCarrier reward :=
    idealSingletonSemanticPair_mem_carrier reward pair₁ owner₂ α₂ hα₂0 hα₂1
      hclearance₁ hB hreward hpair₁
  have hclearance₂ : ∀ who, 0 ≤ capClearance reward pair₂.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward pair₁ owner₂ α₂
      hclearance₁
  exact idealSingletonSemanticPair_mem_carrier reward pair₂ owner₃ α₃
    hα₃0 hα₃1 hclearance₂ hB hreward hpair₂

/-- If all three ideal phases have zero additive cost at the displayed cap
orbit, one lasso turn multiplies total debt by the product of the three
survival factors. -/
theorem threeIdealSingletonLasso_debtSum_eq_mul
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (pair : QuittingTerminalSemanticPair ι)
    (owner₁ owner₂ owner₃ : ι) (α₁ α₂ α₃ : ℝ)
    (t : ι → ℝ)
    (ht : capClearance reward pair.2 = t)
    (hcost₁ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₁ α₁ t D = α₁ * D)
    (hcost₂ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₂ α₂ (idealSingletonClearance (normalizedSoloMatrix reward)
        owner₁ α₁ t) D = α₂ * D)
    (hcost₃ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₃ α₃ (idealSingletonClearance (normalizedSoloMatrix reward)
        owner₂ α₂ (idealSingletonClearance (normalizedSoloMatrix reward)
          owner₁ α₁ t)) D = α₃ * D) :
    quittingTerminalSemanticDebtSum
        (threeIdealSingletonLasso reward owner₁ owner₂ owner₃
          α₁ α₂ α₃ pair) =
      (α₁ * α₂ * α₃) * quittingTerminalSemanticDebtSum pair := by
  unfold threeIdealSingletonLasso
  rw [idealSingletonSemanticPair_debtSum]
  rw [capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair, ht, hcost₃]
  rw [idealSingletonSemanticPair_debtSum]
  rw [capClearance_idealSingletonSemanticPair, ht, hcost₂]
  rw [idealSingletonSemanticPair_debtSum, ht, hcost₁]
  ring

/-- Iterate the three-block ideal semantic lasso. -/
def threeIdealSingletonLassoOrbit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner₁ owner₂ owner₃ : ι) (α₁ α₂ α₃ : ℝ)
    (start : QuittingTerminalSemanticPair ι) (n : ℕ) :
    QuittingTerminalSemanticPair ι :=
  (threeIdealSingletonLasso reward owner₁ owner₂ owner₃ α₁ α₂ α₃)^[n] start

/-- A cap-returning zero-cost three-block lasso produces actual carrier
points with exact geometrically decaying total debt. -/
theorem threeIdealSingletonLassoOrbit_mem_and_debt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (start : QuittingTerminalSemanticPair ι)
    (owner₁ owner₂ owner₃ : ι) (α₁ α₂ α₃ : ℝ)
    (hα₁0 : 0 < α₁) (hα₁1 : α₁ ≤ 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ ≤ 1)
    (hα₃0 : 0 < α₃) (hα₃1 : α₃ ≤ 1)
    (t : ι → ℝ) (ht0 : ∀ who, 0 ≤ t who)
    (hstartCap : capClearance reward start.2 = t)
    (hreturn : threeIdealSingletonClearance (normalizedSoloMatrix reward)
      owner₁ owner₂ owner₃ α₁ α₂ α₃ t = t)
    (hcost₁ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₁ α₁ t D = α₁ * D)
    (hcost₂ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₂ α₂ (idealSingletonClearance (normalizedSoloMatrix reward)
        owner₁ α₁ t) D = α₂ * D)
    (hcost₃ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₃ α₃ (idealSingletonClearance (normalizedSoloMatrix reward)
        owner₂ α₂ (idealSingletonClearance (normalizedSoloMatrix reward)
          owner₁ α₁ t)) D = α₃ * D)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ S player, |reward S player| ≤ B)
    (hstart : start ∈ quittingTerminalSemanticCarrier reward) :
    ∀ n,
      threeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
          α₁ α₂ α₃ start n ∈ quittingTerminalSemanticCarrier reward ∧
      capClearance reward
          (threeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
            α₁ α₂ α₃ start n).2 = t ∧
      quittingTerminalSemanticDebtSum
          (threeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
            α₁ α₂ α₃ start n) =
        (α₁ * α₂ * α₃) ^ n * quittingTerminalSemanticDebtSum start := by
  intro n
  induction n with
  | zero =>
      constructor
      · simpa [threeIdealSingletonLassoOrbit] using hstart
      constructor
      · simpa [threeIdealSingletonLassoOrbit] using hstartCap
      · simp [threeIdealSingletonLassoOrbit]
  | succ n ih =>
      have hclear : ∀ who, 0 ≤ capClearance reward
          (threeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
            α₁ α₂ α₃ start n).2 who := by
        rw [ih.2.1]
        exact ht0
      have hmem := threeIdealSingletonLasso_mem_carrier reward
        (threeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
          α₁ α₂ α₃ start n) owner₁ owner₂ owner₃ α₁ α₂ α₃
        hα₁0 hα₁1 hα₂0 hα₂1 hα₃0 hα₃1 hclear hB hreward ih.1
      have hcap : capClearance reward
          (threeIdealSingletonLasso reward owner₁ owner₂ owner₃ α₁ α₂ α₃
            (threeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
              α₁ α₂ α₃ start n)).2 = t := by
        rw [capClearance_threeIdealSingletonLasso, ih.2.1, hreturn]
      have hdebt := threeIdealSingletonLasso_debtSum_eq_mul reward
        (threeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
          α₁ α₂ α₃ start n) owner₁ owner₂ owner₃ α₁ α₂ α₃ t ih.2.1
        hcost₁ hcost₂ hcost₃
      rw [ih.2.2] at hdebt
      simp only [threeIdealSingletonLassoOrbit,
        Function.iterate_succ_apply']
      refine ⟨hmem, hcap, ?_⟩
      calc
        _ = (α₁ * α₂ * α₃) *
              ((α₁ * α₂ * α₃) ^ n *
                quittingTerminalSemanticDebtSum start) := by
            simpa [threeIdealSingletonLassoOrbit] using hdebt
        _ = (α₁ * α₂ * α₃) ^ (n + 1) *
              quittingTerminalSemanticDebtSum start := by
            rw [pow_succ]
            ring

/-- Consequently, every contracting ideal three-block lasso gives a sequence
of genuine carrier points whose total semantic debt tends to zero. -/
theorem threeIdealSingletonLassoOrbit_debt_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (start : QuittingTerminalSemanticPair ι)
    (owner₁ owner₂ owner₃ : ι) (α₁ α₂ α₃ : ℝ)
    (hα₁0 : 0 < α₁) (hα₁1 : α₁ ≤ 1)
    (hα₂0 : 0 < α₂) (hα₂1 : α₂ ≤ 1)
    (hα₃0 : 0 < α₃) (hα₃1 : α₃ ≤ 1)
    (hcontract : α₁ * α₂ * α₃ < 1)
    (t : ι → ℝ) (ht0 : ∀ who, 0 ≤ t who)
    (hstartCap : capClearance reward start.2 = t)
    (hreturn : threeIdealSingletonClearance (normalizedSoloMatrix reward)
      owner₁ owner₂ owner₃ α₁ α₂ α₃ t = t)
    (hcost₁ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₁ α₁ t D = α₁ * D)
    (hcost₂ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₂ α₂ (idealSingletonClearance (normalizedSoloMatrix reward)
        owner₁ α₁ t) D = α₂ * D)
    (hcost₃ : ∀ D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₃ α₃ (idealSingletonClearance (normalizedSoloMatrix reward)
        owner₂ α₂ (idealSingletonClearance (normalizedSoloMatrix reward)
          owner₁ α₁ t)) D = α₃ * D)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ S player, |reward S player| ≤ B)
    (hstart : start ∈ quittingTerminalSemanticCarrier reward) :
    Tendsto (fun n => quittingTerminalSemanticDebtSum
        (threeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
          α₁ α₂ α₃ start n)) atTop (𝓝 0) := by
  have horbit := threeIdealSingletonLassoOrbit_mem_and_debt reward start
    owner₁ owner₂ owner₃ α₁ α₂ α₃ hα₁0 hα₁1 hα₂0 hα₂1 hα₃0 hα₃1
    t ht0 hstartCap hreturn hcost₁ hcost₂ hcost₃ hB hreward hstart
  have hfactor0 : 0 ≤ α₁ * α₂ * α₃ := by positivity
  have hpow : Tendsto (fun n : ℕ => (α₁ * α₂ * α₃) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hfactor0 hcontract
  simpa using
    (hpow.mul_const (quittingTerminalSemanticDebtSum start)).congr'
      (Eventually.of_forall fun n => (horbit n).2.2.symm)

/-! ## Varying-rate lasso orbits -/

/-- Iterate a three-block lasso whose survival factors may depend on the
current turn. -/
def varyingThreeIdealSingletonLassoOrbit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner₁ owner₂ owner₃ : ι)
    (α₁ α₂ α₃ : ℕ → ℝ)
    (start : QuittingTerminalSemanticPair ι) :
    ℕ → QuittingTerminalSemanticPair ι
  | 0 => start
  | n + 1 => threeIdealSingletonLasso reward owner₁ owner₂ owner₃
      (α₁ n) (α₂ n) (α₃ n)
      (varyingThreeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
        α₁ α₂ α₃ start n)

/-- Abstract varying-rate compiler.  If the displayed cap orbit is exact,
each phase is zero-cost, and every turn contracts by at most `q < 1`, then
the recursively concatenated ideal blocks remain in the actual carrier and
their total debt tends to zero. -/
theorem varyingThreeIdealSingletonLassoOrbit_mem_and_debt_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (start : QuittingTerminalSemanticPair ι)
    (owner₁ owner₂ owner₃ : ι)
    (α₁ α₂ α₃ : ℕ → ℝ) (t : ℕ → ι → ℝ)
    (hα₁0 : ∀ n, 0 < α₁ n) (hα₁1 : ∀ n, α₁ n ≤ 1)
    (hα₂0 : ∀ n, 0 < α₂ n) (hα₂1 : ∀ n, α₂ n ≤ 1)
    (hα₃0 : ∀ n, 0 < α₃ n) (hα₃1 : ∀ n, α₃ n ≤ 1)
    (ht0 : ∀ n who, 0 ≤ t n who)
    (hstartCap : capClearance reward start.2 = t 0)
    (hcapStep : ∀ n,
      threeIdealSingletonClearance (normalizedSoloMatrix reward)
        owner₁ owner₂ owner₃ (α₁ n) (α₂ n) (α₃ n) (t n) = t (n + 1))
    (hcost₁ : ∀ n D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₁ (α₁ n) (t n) D = α₁ n * D)
    (hcost₂ : ∀ n D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₂ (α₂ n) (idealSingletonClearance (normalizedSoloMatrix reward)
        owner₁ (α₁ n) (t n)) D = α₂ n * D)
    (hcost₃ : ∀ n D, idealSingletonDebt (normalizedSoloMatrix reward)
      owner₃ (α₃ n) (idealSingletonClearance (normalizedSoloMatrix reward)
        owner₂ (α₂ n) (idealSingletonClearance
          (normalizedSoloMatrix reward) owner₁ (α₁ n) (t n))) D = α₃ n * D)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : ∀ n, α₁ n * α₂ n * α₃ n ≤ q)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ S player, |reward S player| ≤ B)
    (hstart : start ∈ quittingTerminalSemanticCarrier reward) :
    (∀ n,
      varyingThreeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
          α₁ α₂ α₃ start n ∈ quittingTerminalSemanticCarrier reward ∧
      capClearance reward
          (varyingThreeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
            α₁ α₂ α₃ start n).2 = t n ∧
      quittingTerminalSemanticDebtSum
          (varyingThreeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
            α₁ α₂ α₃ start n) ≤
        q ^ n * quittingTerminalSemanticDebtSum start) ∧
    Tendsto (fun n => quittingTerminalSemanticDebtSum
        (varyingThreeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
          α₁ α₂ α₃ start n)) atTop (𝓝 0) := by
  have horbit : ∀ n,
      varyingThreeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
          α₁ α₂ α₃ start n ∈ quittingTerminalSemanticCarrier reward ∧
      capClearance reward
          (varyingThreeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
            α₁ α₂ α₃ start n).2 = t n ∧
      quittingTerminalSemanticDebtSum
          (varyingThreeIdealSingletonLassoOrbit reward owner₁ owner₂ owner₃
            α₁ α₂ α₃ start n) ≤
        q ^ n * quittingTerminalSemanticDebtSum start := by
    intro n
    induction n with
    | zero =>
        constructor
        · simpa [varyingThreeIdealSingletonLassoOrbit] using hstart
        constructor
        · simpa [varyingThreeIdealSingletonLassoOrbit] using hstartCap
        · simp [varyingThreeIdealSingletonLassoOrbit]
    | succ n ih =>
        let current := varyingThreeIdealSingletonLassoOrbit reward
          owner₁ owner₂ owner₃ α₁ α₂ α₃ start n
        have hclear : ∀ who, 0 ≤ capClearance reward current.2 who := by
          rw [ih.2.1]
          exact ht0 n
        have hmem := threeIdealSingletonLasso_mem_carrier reward current
          owner₁ owner₂ owner₃ (α₁ n) (α₂ n) (α₃ n)
          (hα₁0 n) (hα₁1 n) (hα₂0 n) (hα₂1 n) (hα₃0 n) (hα₃1 n)
          hclear hB hreward ih.1
        have hcap : capClearance reward
            (threeIdealSingletonLasso reward owner₁ owner₂ owner₃
              (α₁ n) (α₂ n) (α₃ n) current).2 = t (n + 1) := by
          rw [capClearance_threeIdealSingletonLasso, ih.2.1, hcapStep n]
        have hdebt := threeIdealSingletonLasso_debtSum_eq_mul reward current
          owner₁ owner₂ owner₃ (α₁ n) (α₂ n) (α₃ n) (t n) ih.2.1
          (hcost₁ n) (hcost₂ n) (hcost₃ n)
        have hcurrentNonneg : 0 ≤ quittingTerminalSemanticDebtSum current := by
          unfold quittingTerminalSemanticDebtSum
          exact Finset.sum_nonneg fun who _ =>
            quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hB
              hreward ih.1 who
        have hfactorNonneg : 0 ≤ α₁ n * α₂ n * α₃ n :=
          mul_nonneg (mul_nonneg (hα₁0 n).le (hα₂0 n).le) (hα₃0 n).le
        have hscaledFactor :
            (α₁ n * α₂ n * α₃ n) *
                quittingTerminalSemanticDebtSum current ≤
              q * quittingTerminalSemanticDebtSum current :=
          mul_le_mul_of_nonneg_right (hcontract n) hcurrentNonneg
        have hscaledDebt : q * quittingTerminalSemanticDebtSum current ≤
            q * (q ^ n * quittingTerminalSemanticDebtSum start) :=
          mul_le_mul_of_nonneg_left ih.2.2 hq0
        have hbound : quittingTerminalSemanticDebtSum
            (threeIdealSingletonLasso reward owner₁ owner₂ owner₃
              (α₁ n) (α₂ n) (α₃ n) current) ≤
            q ^ (n + 1) * quittingTerminalSemanticDebtSum start := by
          rw [hdebt]
          calc
            _ ≤ q * quittingTerminalSemanticDebtSum current := hscaledFactor
            _ ≤ q * (q ^ n * quittingTerminalSemanticDebtSum start) := hscaledDebt
            _ = q ^ (n + 1) * quittingTerminalSemanticDebtSum start := by
              rw [pow_succ]
              ring
        simpa [varyingThreeIdealSingletonLassoOrbit, current] using
          And.intro hmem (And.intro hcap hbound)
  refine ⟨horbit, ?_⟩
  have hupper : Tendsto
      (fun n : ℕ => q ^ n * quittingTerminalSemanticDebtSum start)
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const
      (quittingTerminalSemanticDebtSum start)
  apply squeeze_zero
  · intro n
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun who _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier reward hB
        hreward (horbit n).1 who
  · intro n
    exact (horbit n).2.2
  · exact hupper

/-! ## The varying-height directed three-core cycle -/

namespace Question193ThreeCoreCarrier

open Question193ThreeCore
open QuittingLCPClassification.ThreeByThreeZeroDiagonalQ

abbrev Player := Fin 3

/-- Heights generated by the rational three-core return map. -/
def heightOrbit (a b c d e f H₀ : ℝ) : ℕ → ℝ
  | 0 => H₀
  | n + 1 => heightReturn a b c d e f (heightOrbit a b c d e f H₀ n)

/-- Semantic orbit obtained by applying the three zero-cost blocks at their
current height-dependent rates. -/
def semanticOrbit
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (a b c d e f H₀ : ℝ) (start : QuittingTerminalSemanticPair Player) :
    ℕ → QuittingTerminalSemanticPair Player :=
  varyingThreeIdealSingletonLassoOrbit reward 0 2 1
    (fun n => firstRatio e (heightOrbit a b c d e f H₀ n))
    (fun n => secondRatio d
      (secondHeight c e (heightOrbit a b c d e f H₀ n)))
    (fun n => thirdRatio a
      (firstHeight b d
        (secondHeight c e (heightOrbit a b c d e f H₀ n))))
    start

theorem heightOrbit_pos
    {a b c d e f H₀ : ℝ}
    (hH₀ : 0 < H₀) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) :
    ∀ n, 0 < heightOrbit a b c d e f H₀ n := by
  intro n
  induction n with
  | zero => exact hH₀
  | succ n ih =>
      exact heightReturn_pos ih ha hb hc hd he hf

theorem min_height_le_heightOrbit
    {a b c d e f H₀ : ℝ}
    (hH₀ : 0 < H₀) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e)
    (hdet : a * d * e < b * c * f) :
    ∀ n, min H₀ (fixedHeight a b c d e f) ≤
      heightOrbit a b c d e f H₀ n := by
  intro n
  induction n with
  | zero => exact min_le_left _ _
  | succ n ih =>
      exact min_height_fixed_le_heightReturn hH₀ ih ha hb hc hd he hdet

private theorem ratio_pos_le_one
    {H x : ℝ} (hH : 0 < H) (hx : 0 < x) :
    0 < x / (H + x) ∧ x / (H + x) ≤ 1 := by
  constructor
  · exact div_pos hx (add_pos hH hx)
  · exact (div_le_one (add_pos hH hx)).2 (by linarith)

/-- Load-bearing three-core bridge: the varying-height ideal cycle is a
sequence of points of the actual terminal-semantic carrier and its total debt
tends to zero.  The ideal steps are justified by the explicit positive-hazard
finite meshes above, not postulated as abstract transitions. -/
theorem directedCycle_semanticOrbit_mem_and_debt_tendsto_zero
    (reward : {S : Finset Player // S.Nonempty} → Payoff Player)
    (start : QuittingTerminalSemanticPair Player)
    {a b c d e f H₀ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f) (hH₀ : 0 < H₀)
    (hdet : a * d * e < b * c * f)
    (hmatrix : normalizedSoloMatrix reward =
      directedCycleMatrix a b c d e f)
    (hstartCap : capClearance reward start.2 = axisTwo H₀)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ S player, |reward S player| ≤ B)
    (hstart : start ∈ quittingTerminalSemanticCarrier reward) :
    (∀ n, semanticOrbit reward a b c d e f H₀ start n ∈
      quittingTerminalSemanticCarrier reward) ∧
    Tendsto (fun n => quittingTerminalSemanticDebtSum
        (semanticOrbit reward a b c d e f H₀ start n)) atTop (𝓝 0) := by
  let H : ℕ → ℝ := heightOrbit a b c d e f H₀
  let H₂ : ℕ → ℝ := fun n => secondHeight c e (H n)
  let H₁ : ℕ → ℝ := fun n => firstHeight b d (H₂ n)
  let α₁ : ℕ → ℝ := fun n => firstRatio e (H n)
  let α₂ : ℕ → ℝ := fun n => secondRatio d (H₂ n)
  let α₃ : ℕ → ℝ := fun n => thirdRatio a (H₁ n)
  let t : ℕ → Player → ℝ := fun n => axisTwo (H n)
  let lower : ℝ := min H₀ (fixedHeight a b c d e f)
  let q : ℝ := e / (lower + e)
  have hH : ∀ n, 0 < H n := by
    intro n
    exact heightOrbit_pos hH₀ ha hb hc hd he hf n
  have hH₂ : ∀ n, 0 < H₂ n := by
    intro n
    unfold H₂ secondHeight
    exact div_pos (mul_pos hc (hH n)) (add_pos (hH n) he)
  have hH₁ : ∀ n, 0 < H₁ n := by
    intro n
    unfold H₁ firstHeight
    exact div_pos (mul_pos hb (hH₂ n)) (add_pos (hH₂ n) hd)
  have hα₁ : ∀ n, 0 < α₁ n ∧ α₁ n ≤ 1 := fun n =>
    ratio_pos_le_one (hH n) he
  have hα₂ : ∀ n, 0 < α₂ n ∧ α₂ n ≤ 1 := fun n =>
    ratio_pos_le_one (hH₂ n) hd
  have hα₃ : ∀ n, 0 < α₃ n ∧ α₃ n ≤ 1 := fun n =>
    ratio_pos_le_one (hH₁ n) ha
  have ht0 : ∀ n who, 0 ≤ t n who := by
    intro n who
    fin_cases who <;> simp [t, axisTwo, (hH n).le]
  have hcapStep : ∀ n,
      threeIdealSingletonClearance (normalizedSoloMatrix reward)
        0 2 1 (α₁ n) (α₂ n) (α₃ n) (t n) = t (n + 1) := by
    intro n
    unfold threeIdealSingletonClearance
    rw [hmatrix]
    rw [show t n = axisTwo (H n) by rfl]
    rw [show α₁ n = firstRatio e (H n) by rfl,
      first_block (hH n) he hc]
    rw [show α₂ n = secondRatio d (H₂ n) by rfl,
      show H₂ n = secondHeight c e (H n) by rfl,
      second_block (hH₂ n) hd hb]
    rw [show α₃ n = thirdRatio a (H₁ n) by rfl,
      show H₁ n = firstHeight b d (H₂ n) by rfl,
      third_block (hH₁ n) ha hf]
    rw [three_block_height_eq_return (hH n) ha hb hc hd he]
    rfl
  have hcost₁ : ∀ n D, idealSingletonDebt (normalizedSoloMatrix reward)
      0 (α₁ n) (t n) D = α₁ n * D := by
    intro n D
    rw [hmatrix]
    exact first_block_zeroCost (hH n) he hc
  have hcost₂ : ∀ n D, idealSingletonDebt (normalizedSoloMatrix reward)
      2 (α₂ n) (idealSingletonClearance (normalizedSoloMatrix reward)
        0 (α₁ n) (t n)) D = α₂ n * D := by
    intro n D
    rw [hmatrix]
    rw [show t n = axisTwo (H n) by rfl,
      show α₁ n = firstRatio e (H n) by rfl,
      first_block (hH n) he hc]
    exact second_block_zeroCost (hH₂ n) hd hb
  have hcost₃ : ∀ n D, idealSingletonDebt (normalizedSoloMatrix reward)
      1 (α₃ n) (idealSingletonClearance (normalizedSoloMatrix reward)
        2 (α₂ n) (idealSingletonClearance
          (normalizedSoloMatrix reward) 0 (α₁ n) (t n))) D = α₃ n * D := by
    intro n D
    rw [hmatrix]
    rw [show t n = axisTwo (H n) by rfl,
      show α₁ n = firstRatio e (H n) by rfl,
      first_block (hH n) he hc]
    rw [show α₂ n = secondRatio d (H₂ n) by rfl,
      show H₂ n = secondHeight c e (H n) by rfl,
      second_block (hH₂ n) hd hb]
    exact third_block_zeroCost (hH₁ n) ha hf
  have hlower : 0 < lower := by
    exact lt_min hH₀ (fixedHeight_pos ha hb hc hd hdet)
  have hq := fixed_height_contraction_nonneg_lt_one he hlower
  have hheightLower : ∀ n, lower ≤ H n := by
    intro n
    exact min_height_le_heightOrbit hH₀ ha hb hc hd he hdet n
  have hcontract : ∀ n, α₁ n * α₂ n * α₃ n ≤ q := by
    intro n
    exact three_ratio_product_le_fixed_contraction (hH n) ha hb hc hd he
      hlower (hheightLower n)
  have hcompiled := varyingThreeIdealSingletonLassoOrbit_mem_and_debt_tendsto_zero
    reward start 0 2 1 α₁ α₂ α₃ t
    (fun n => (hα₁ n).1) (fun n => (hα₁ n).2)
    (fun n => (hα₂ n).1) (fun n => (hα₂ n).2)
    (fun n => (hα₃ n).1) (fun n => (hα₃ n).2)
    ht0 (by simpa [t, H, heightOrbit] using hstartCap)
    hcapStep hcost₁ hcost₂ hcost₃
    q hq.1 hq.2 hcontract hB hreward hstart
  constructor
  · intro n
    simpa [semanticOrbit, α₁, α₂, α₃, H, H₂, H₁] using
      (hcompiled.1 n).1
  · simpa [semanticOrbit, α₁, α₂, α₃, H, H₂, H₁] using hcompiled.2

end Question193ThreeCoreCarrier

/-! ## Lifting the three-cycle through a three-element corrected core -/

namespace Question193ThreeCoreLift

open Question193ThreeCore
open QuittingLCPClassification
open QuittingLCPClassification.ThreeByThreeZeroDiagonalQ
open Math.LinearProgramming

abbrev CorePlayer := Fin 3

/-- The ambient player carrying a given labeled core coordinate. -/
def coreOwner {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : ι → ι → ℝ} (label : normalCore M ≃ CorePlayer)
    (who : CorePlayer) : ι :=
  (label.symm who).1

/-- Restrict an ambient vector to labeled core coordinates. -/
def coreRestriction {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : ι → ι → ℝ} (label : normalCore M ≃ CorePlayer)
    (t : ι → ℝ) : CorePlayer → ℝ :=
  fun who => t (coreOwner label who)

theorem coreOwner_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : ι → ι → ℝ} (label : normalCore M ≃ CorePlayer)
    (who : CorePlayer) : coreOwner label who ∈ normalCore M :=
  (label.symm who).property

theorem coreOwner_injective {ι : Type} [Fintype ι] [DecidableEq ι]
    {M : ι → ι → ℝ} (label : normalCore M ≃ CorePlayer) :
    Function.Injective (coreOwner label) := by
  intro i j hij
  apply label.symm.injective
  exact Subtype.ext hij

/-- Restriction commutes with an ideal singleton update when the labeled
principal matrix is the displayed directed-cycle matrix. -/
theorem coreRestriction_idealSingletonClearance
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (label : normalCore M ≃ CorePlayer)
    (a b c d e f : ℝ)
    (hmatrix : reindexMatrix label (normalPlayerMatrix M) =
      directedCycleMatrix a b c d e f)
    (owner : CorePlayer) (α : ℝ) (t : ι → ℝ) :
    coreRestriction label
        (idealSingletonClearance M (coreOwner label owner) α t) =
      idealSingletonClearance (directedCycleMatrix a b c d e f)
        owner α (coreRestriction label t) := by
  funext who
  have hentry : M (coreOwner label who) (coreOwner label owner) =
      directedCycleMatrix a b c d e f who owner := by
    have := congrFun (congrFun hmatrix who) owner
    simpa [reindexMatrix, normalPlayerMatrix, principalMatrix, coreOwner] using this
  by_cases hwho : who = owner
  · subst who
    simp [coreRestriction, idealSingletonClearance]
  · have hambient : coreOwner label who ≠ coreOwner label owner :=
      fun h => hwho (coreOwner_injective label h)
    simp [coreRestriction, idealSingletonClearance, hwho, hambient, hentry]

/-- Zero additive debt on a finite core implies every individual nonowner
affine update on that core is nonnegative. -/
theorem affine_nonneg_of_idealSingletonDebt_eq_mul
    {κ : Type} [Fintype κ] [DecidableEq κ]
    (M : κ → κ → ℝ) (owner : κ) (α : ℝ) (t : κ → ℝ)
    (howner : t owner = 0)
    (hzero : ∀ D, idealSingletonDebt M owner α t D = α * D) :
    ∀ who, who ≠ owner → 0 ≤ α * t who + (1 - α) * M who owner := by
  intro who hwho
  have hsum : (∑ player ∈ Finset.univ.erase owner,
      max 0 (-(α * t player + (1 - α) * M player owner))) = 0 := by
    have := hzero 0
    unfold idealSingletonDebt at this
    rw [howner] at this
    simpa using this
  have hall := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => le_max_left 0 _)).1 hsum
  have hterm := hall who (by simp [hwho])
  have hle : -(α * t who + (1 - α) * M who owner) ≤ 0 := by
    calc
      _ ≤ max 0 (-(α * t who + (1 - α) * M who owner)) :=
        le_max_right _ _
      _ = 0 := hterm
  linarith

/-- A zero-cost singleton phase on the labeled core lifts to the ambient
player set provided every outside-core affine update is nonnegative. -/
theorem idealSingletonDebt_eq_mul_of_core_zeroCost
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (label : normalCore M ≃ CorePlayer)
    (a b c d e f : ℝ)
    (hmatrix : reindexMatrix label (normalPlayerMatrix M) =
      directedCycleMatrix a b c d e f)
    (owner : CorePlayer) (α : ℝ) (t : ι → ℝ) (coreT : CorePlayer → ℝ)
    (ht : coreRestriction label t = coreT)
    (howner : coreT owner = 0)
    (hcore : ∀ D, idealSingletonDebt (directedCycleMatrix a b c d e f)
      owner α coreT D = α * D)
    (houtside : ∀ who, who ∉ normalCore M →
      0 ≤ α * t who + (1 - α) * M who (coreOwner label owner)) :
    ∀ D, idealSingletonDebt M (coreOwner label owner) α t D = α * D := by
  intro D
  apply idealSingletonDebt_eq_mul_of_zeroCost
  · have := congrFun ht owner
    simpa [coreRestriction, howner] using this
  · intro who hwho
    by_cases hmem : who ∈ normalCore M
    · let coreWho : normalCore M := ⟨who, hmem⟩
      let k : CorePlayer := label coreWho
      have hkOwner : k ≠ owner := by
        intro hk
        apply hwho
        have : coreWho = label.symm owner := by
          apply label.injective
          simpa [k] using hk
        exact congrArg Subtype.val this
      have hnonneg := affine_nonneg_of_idealSingletonDebt_eq_mul
        (directedCycleMatrix a b c d e f) owner α coreT howner hcore
        k hkOwner
      have hwhoEq : coreOwner label k = who := by
        simp [coreOwner, k, coreWho]
      have htWho : t who = coreT k := by
        rw [← hwhoEq]
        exact congrFun ht k
      have hentry : M who (coreOwner label owner) =
          directedCycleMatrix a b c d e f k owner := by
        have hm := congrFun (congrFun hmatrix k) owner
        simpa [reindexMatrix, normalPlayerMatrix, principalMatrix,
          coreOwner, k, coreWho] using hm
      simpa [htWho, hentry] using hnonneg
    · exact houtside who hmem

/-- Ambient cap orbit: core coordinates perform the directed cycle, while
outside coordinates are carried along by the same three ideal blocks. -/
def ambientClearanceOrbit
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (label : normalCore M ≃ CorePlayer)
    (a b c d e f H₀ : ℝ) (t₀ : ι → ℝ) : ℕ → ι → ℝ
  | 0 => t₀
  | n + 1 =>
      let H := Question193ThreeCoreCarrier.heightOrbit a b c d e f H₀ n
      threeIdealSingletonClearance M
        (coreOwner label 0) (coreOwner label 2) (coreOwner label 1)
        (firstRatio e H)
        (secondRatio d (secondHeight c e H))
        (thirdRatio a (firstHeight b d (secondHeight c e H)))
        (ambientClearanceOrbit M label a b c d e f H₀ t₀ n)

theorem ambientClearanceOrbit_nonneg
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (label : normalCore M ≃ CorePlayer)
    (a b c d e f H₀ : ℝ) (t₀ : ι → ℝ)
    (ht₀ : ∀ who, 0 ≤ t₀ who) :
    ∀ n who, 0 ≤ ambientClearanceOrbit M label a b c d e f H₀ t₀ n who := by
  intro n
  induction n with
  | zero => exact ht₀
  | succ n ih =>
      unfold ambientClearanceOrbit threeIdealSingletonClearance
      have hone : ∀ who, 0 ≤ idealSingletonClearance M
          (coreOwner label 0)
          (firstRatio e
            (Question193ThreeCoreCarrier.heightOrbit a b c d e f H₀ n))
          (ambientClearanceOrbit M label a b c d e f H₀ t₀ n) who := by
        intro who
        by_cases hwho : who = coreOwner label 0
        · simpa [idealSingletonClearance, hwho] using ih who
        · simp [idealSingletonClearance, hwho]
      have htwo : ∀ who, 0 ≤ idealSingletonClearance M
          (coreOwner label 2)
          (secondRatio d (secondHeight c e
            (Question193ThreeCoreCarrier.heightOrbit a b c d e f H₀ n)))
          (idealSingletonClearance M (coreOwner label 0)
            (firstRatio e
              (Question193ThreeCoreCarrier.heightOrbit a b c d e f H₀ n))
            (ambientClearanceOrbit M label a b c d e f H₀ t₀ n)) who := by
        intro who
        by_cases hwho : who = coreOwner label 2
        · simpa [idealSingletonClearance, hwho] using hone who
        · simp [idealSingletonClearance, hwho]
      intro who
      by_cases hwho : who = coreOwner label 1
      · simpa [idealSingletonClearance, hwho] using htwo who
      · simp [idealSingletonClearance, hwho]

theorem coreRestriction_ambientClearanceOrbit
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (label : normalCore M ≃ CorePlayer)
    {a b c d e f H₀ : ℝ}
    (hH₀ : 0 < H₀) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hmatrix : reindexMatrix label (normalPlayerMatrix M) =
      directedCycleMatrix a b c d e f)
    (t₀ : ι → ℝ) (ht₀ : coreRestriction label t₀ = axisTwo H₀) :
    ∀ n, coreRestriction label
        (ambientClearanceOrbit M label a b c d e f H₀ t₀ n) =
      axisTwo (Question193ThreeCoreCarrier.heightOrbit a b c d e f H₀ n) := by
  intro n
  induction n with
  | zero => exact ht₀
  | succ n ih =>
      let H := Question193ThreeCoreCarrier.heightOrbit a b c d e f H₀ n
      have hH : 0 < H :=
        Question193ThreeCoreCarrier.heightOrbit_pos hH₀ ha hb hc hd he hf n
      unfold ambientClearanceOrbit threeIdealSingletonClearance
      rw [coreRestriction_idealSingletonClearance M label a b c d e f hmatrix]
      rw [coreRestriction_idealSingletonClearance M label a b c d e f hmatrix]
      rw [coreRestriction_idealSingletonClearance M label a b c d e f hmatrix]
      rw [ih, first_block hH he hc]
      have hH₂ : 0 < secondHeight c e H := by
        unfold secondHeight
        exact div_pos (mul_pos hc hH) (add_pos hH he)
      rw [second_block hH₂ hd hb]
      have hH₁ : 0 < firstHeight b d (secondHeight c e H) := by
        unfold firstHeight
        exact div_pos (mul_pos hb hH₂) (add_pos hH₂ hd)
      rw [third_block hH₁ ha hf,
        three_block_height_eq_return hH ha hb hc hd he]
      rfl

/-- For a genuine corrected core, outside rows automatically satisfy every
nonnegative affine condition used by a core singleton clock. -/
theorem outside_core_affine_nonneg
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (M : ι → ι → ℝ) (label : normalCore M ≃ CorePlayer)
    (t : ι → ℝ) (ht : ∀ who, 0 ≤ t who)
    (owner : CorePlayer) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∀ who, who ∉ normalCore M →
      0 ≤ α * t who + (1 - α) * M who (coreOwner label owner) := by
  intro who hwho
  exact add_nonneg (mul_nonneg hα0 (ht who))
    (mul_nonneg (sub_nonneg.mpr hα1)
      (normalCore_entry_pos_of_notMem M hwho (coreOwner_mem label owner)).le)

end Question193ThreeCoreLift

end IdealSingletonCarrierBridge
end GameTheory
