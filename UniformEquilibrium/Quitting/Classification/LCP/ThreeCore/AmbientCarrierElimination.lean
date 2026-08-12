/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Classification.LCP.ThreeCore.IdealSingletonZeroRetentionCarrier
import UniformEquilibrium.Quitting.Classification.LCP.CounterexampleNecessary
import UniformEquilibrium.Quitting.Classification.LCP.StandardQSideExample
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEqualityStratum

/-!
# Elimination of a three-element corrected core on the semantic carrier

This composes the cyclic labeling of a three-coordinate standard-Q core, the
zero-retention carrier reset, and the varying-height directed-cycle lasso.
The carrier construction eliminates the entire three-element corrected-core
counterexample branch.
-/

noncomputable section

namespace GameTheory
namespace ThreeCoreAmbientCarrierElimination

open Filter Finset
open IdealSingletonBlockApproximation IdealSingletonCarrierBridge
open IdealSingletonCarrierBridge.Question193ThreeCoreLift
open Question193ThreeCore
open QuittingLCPClassification
open QuittingLCPClassification.ThreeByThreeZeroDiagonalQ
open Math.LinearProgramming
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Explicit terminal semantic pair of the perpetual-Continue suffix. -/
private def threeCoreNeverBoundarySemanticPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    QuittingTerminalSemanticPair ι :=
  (fun _ => 0,
    fun who => max 0 (reward (quittingSingletonTerminal who) who))

/-- The perpetual-Continue root word realizes the explicit boundary pair. -/
private theorem quittingTerminalSemanticPair_never_eq_threeCoreBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B) :
    quittingTerminalSemanticPair reward
        (quittingRootSequenceProfile reward
          (quittingElementaryCapRoots
            (.never : QuittingElementaryTailCap ι)) 0) =
      threeCoreNeverBoundarySemanticPair reward := by
  apply Prod.ext
  · funext who
    exact quittingRootSequenceTerminalValue_elementaryCap_never reward who
  · funext who
    exact quittingRootSequenceBestResponseValue_elementaryCap_never
      reward who hB hreward

/-- Three zero-retention singleton resets erase an arbitrary directed-core
clearance vector and leave the positive coordinate-two axis. -/
theorem directedCycle_three_zero_reset
    {a b c d e f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (t : Fin 3 → ℝ) :
    idealSingletonClearance (directedCycleMatrix a b c d e f) 1 0
        (idealSingletonClearance (directedCycleMatrix a b c d e f) 2 0
          (idealSingletonClearance (directedCycleMatrix a b c d e f) 0 0 t)) =
      axisTwo f := by
  funext who
  fin_cases who <;>
    simp [idealSingletonClearance, directedCycleMatrix, axisTwo,
      ha.le, hb.le, hc.le, hd.le, he.le, hf.le]

omit [Fintype ι] [DecidableEq ι] in
/-- The explicit Never semantic boundary has nonnegative cap clearance. -/
theorem never_capClearance_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∀ who, 0 ≤ capClearance reward
      (threeCoreNeverBoundarySemanticPair reward).2 who := by
  intro who
  have hterminal : quittingSingletonTerminal who =
      quittingProjectiveSingletonTerminal who := by
    apply Subtype.ext
    rfl
  rw [capClearance]
  simp only [threeCoreNeverBoundarySemanticPair, hterminal]
  exact sub_nonneg.mpr (le_max_right _ _)

/-- The explicit Never boundary is an actual semantic-carrier point. -/
theorem never_mem_carrier
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B) :
    threeCoreNeverBoundarySemanticPair reward ∈
      quittingTerminalSemanticCarrier reward := by
  apply subset_closure
  refine ⟨quittingRootSequenceProfile reward
    (quittingElementaryCapRoots (.never : QuittingElementaryTailCap ι)) 0, ?_⟩
  exact quittingTerminalSemanticPair_never_eq_threeCoreBoundary
    reward hB hreward

/-- Reset the Never boundary along the labeled owners `0,2,1`. -/
def resetPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (label : normalCore (normalizedSoloMatrix reward) ≃ Fin 3) :
    QuittingTerminalSemanticPair ι :=
  idealSingletonSemanticPair reward (coreOwner label 1) 0
    (idealSingletonSemanticPair reward (coreOwner label 2) 0
      (idealSingletonSemanticPair reward (coreOwner label 0) 0
        (threeCoreNeverBoundarySemanticPair reward)))

/-- The three-reset start belongs to the carrier and has nonnegative ambient
clearance. -/
theorem resetPair_mem_and_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (label : normalCore (normalizedSoloMatrix reward) ≃ Fin 3)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B) :
    resetPair reward label ∈ quittingTerminalSemanticCarrier reward ∧
      ∀ who, 0 ≤ capClearance reward (resetPair reward label).2 who := by
  let never := threeCoreNeverBoundarySemanticPair reward
  let first := idealSingletonSemanticPair reward (coreOwner label 0) 0 never
  let second := idealSingletonSemanticPair reward (coreOwner label 2) 0 first
  have hneverClear : ∀ who, 0 ≤ capClearance reward never.2 who :=
    never_capClearance_nonneg reward
  have hneverMem : never ∈ quittingTerminalSemanticCarrier reward :=
    never_mem_carrier reward hB hreward
  have hfirstMem : first ∈ quittingTerminalSemanticCarrier reward :=
    idealSingletonSemanticPair_zero_mem_carrier reward never
      (coreOwner label 0) hneverClear hB hreward hneverMem
  have hfirstClear : ∀ who, 0 ≤ capClearance reward first.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward never
      (coreOwner label 0) 0 hneverClear
  have hsecondMem : second ∈ quittingTerminalSemanticCarrier reward :=
    idealSingletonSemanticPair_zero_mem_carrier reward first
      (coreOwner label 2) hfirstClear hB hreward hfirstMem
  have hsecondClear : ∀ who, 0 ≤ capClearance reward second.2 who :=
    capClearance_idealSingletonSemanticPair_nonneg reward first
      (coreOwner label 2) 0 hfirstClear
  have hthirdMem := idealSingletonSemanticPair_zero_mem_carrier reward second
    (coreOwner label 1) hsecondClear hB hreward hsecondMem
  have hthirdClear := capClearance_idealSingletonSemanticPair_nonneg reward second
    (coreOwner label 1) 0 hsecondClear
  simpa [resetPair, never, first, second] using And.intro hthirdMem hthirdClear

/-- Under a directed-cycle labeling, the reset start has exactly the required
positive coordinate-two core clearance. -/
theorem coreRestriction_resetPair
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (label : normalCore (normalizedSoloMatrix reward) ≃ Fin 3)
    {a b c d e f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hmatrix : reindexMatrix label
        (normalPlayerMatrix (normalizedSoloMatrix reward)) =
      directedCycleMatrix a b c d e f) :
    coreRestriction label (capClearance reward (resetPair reward label).2) =
      axisTwo f := by
  unfold resetPair
  rw [capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair,
    capClearance_idealSingletonSemanticPair]
  rw [coreRestriction_idealSingletonClearance
      (normalizedSoloMatrix reward) label a b c d e f hmatrix,
    coreRestriction_idealSingletonClearance
      (normalizedSoloMatrix reward) label a b c d e f hmatrix,
    coreRestriction_idealSingletonClearance
      (normalizedSoloMatrix reward) label a b c d e f hmatrix]
  exact directedCycle_three_zero_reset ha hb hc hd he hf _

private theorem ratio_pos_le_one
    {H x : ℝ} (hH : 0 < H) (hx : 0 < x) :
    0 < x / (H + x) ∧ x / (H + x) ≤ 1 := by
  exact ⟨div_pos hx (add_pos hH hx),
    (div_le_one (add_pos hH hx)).2 (by linarith)⟩

/-- The ambient semantic orbit obtained by running the labeled directed-core
clock after the three-reset start. -/
def ambientSemanticOrbit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (label : normalCore (normalizedSoloMatrix reward) ≃ Fin 3)
    (a b c d e f : ℝ) : ℕ → QuittingTerminalSemanticPair ι :=
  varyingThreeIdealSingletonLassoOrbit reward
    (coreOwner label 0) (coreOwner label 2) (coreOwner label 1)
    (fun n => firstRatio e
      (IdealSingletonCarrierBridge.Question193ThreeCoreCarrier.heightOrbit
        a b c d e f f n))
    (fun n => secondRatio d (secondHeight c e
      (IdealSingletonCarrierBridge.Question193ThreeCoreCarrier.heightOrbit
        a b c d e f f n)))
    (fun n => thirdRatio a (firstHeight b d (secondHeight c e
      (IdealSingletonCarrierBridge.Question193ThreeCoreCarrier.heightOrbit
        a b c d e f f n))))
    (resetPair reward label)

/-- A labeled positive directed core gives an ambient sequence of actual
semantic-carrier points whose total debt tends to zero. -/
theorem labeled_directedCycle_ambientOrbit_mem_and_debt_tendsto_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (label : normalCore (normalizedSoloMatrix reward) ≃ Fin 3)
    {a b c d e f : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (he : 0 < e) (hf : 0 < f)
    (hdet : a * d * e < b * c * f)
    (hmatrix : reindexMatrix label
        (normalPlayerMatrix (normalizedSoloMatrix reward)) =
      directedCycleMatrix a b c d e f)
    {B : ℝ} (hB : 0 ≤ B)
    (hreward : ∀ terminal player, |reward terminal player| ≤ B) :
    (∀ n, ambientSemanticOrbit reward label a b c d e f n ∈
      quittingTerminalSemanticCarrier reward) ∧
    Tendsto (fun n => quittingTerminalSemanticDebtSum
        (ambientSemanticOrbit reward label a b c d e f n))
      atTop (nhds 0) := by
  let M := normalizedSoloMatrix reward
  let start := resetPair reward label
  let H : ℕ → ℝ :=
    IdealSingletonCarrierBridge.Question193ThreeCoreCarrier.heightOrbit
      a b c d e f f
  let H₂ : ℕ → ℝ := fun n => secondHeight c e (H n)
  let H₁ : ℕ → ℝ := fun n => firstHeight b d (H₂ n)
  let α₁ : ℕ → ℝ := fun n => firstRatio e (H n)
  let α₂ : ℕ → ℝ := fun n => secondRatio d (H₂ n)
  let α₃ : ℕ → ℝ := fun n => thirdRatio a (H₁ n)
  let t : ℕ → ι → ℝ :=
    ambientClearanceOrbit M label a b c d e f f
      (capClearance reward start.2)
  let lower : ℝ := min f (fixedHeight a b c d e f)
  let q : ℝ := e / (lower + e)
  have hH : ∀ n, 0 < H n := by
    intro n
    exact IdealSingletonCarrierBridge.Question193ThreeCoreCarrier.heightOrbit_pos
      hf ha hb hc hd he hf n
  have hH₂ : ∀ n, 0 < H₂ n := by
    intro n
    exact div_pos (mul_pos hc (hH n)) (add_pos (hH n) he)
  have hH₁ : ∀ n, 0 < H₁ n := by
    intro n
    exact div_pos (mul_pos hb (hH₂ n)) (add_pos (hH₂ n) hd)
  have hα₁ : ∀ n, 0 < α₁ n ∧ α₁ n ≤ 1 := fun n =>
    ratio_pos_le_one (hH n) he
  have hα₂ : ∀ n, 0 < α₂ n ∧ α₂ n ≤ 1 := fun n =>
    ratio_pos_le_one (hH₂ n) hd
  have hα₃ : ∀ n, 0 < α₃ n ∧ α₃ n ≤ 1 := fun n =>
    ratio_pos_le_one (hH₁ n) ha
  have hstart := resetPair_mem_and_nonneg reward label hB hreward
  have ht0 : ∀ n who, 0 ≤ t n who := by
    exact ambientClearanceOrbit_nonneg M label a b c d e f f
      (capClearance reward start.2) hstart.2
  have hstartCore : coreRestriction label
      (capClearance reward start.2) = axisTwo f := by
    exact coreRestriction_resetPair reward label ha hb hc hd he hf hmatrix
  have hcoreOrbit : ∀ n, coreRestriction label (t n) = axisTwo (H n) := by
    exact coreRestriction_ambientClearanceOrbit M label hf ha hb hc hd he hf
      hmatrix (capClearance reward start.2) hstartCore
  have hcapStep : ∀ n,
      threeIdealSingletonClearance M
        (coreOwner label 0) (coreOwner label 2) (coreOwner label 1)
        (α₁ n) (α₂ n) (α₃ n) (t n) = t (n + 1) := by
    intro n
    rfl
  have hcost₁ : ∀ n D, idealSingletonDebt M
      (coreOwner label 0) (α₁ n) (t n) D = α₁ n * D := by
    intro n
    apply idealSingletonDebt_eq_mul_of_core_zeroCost M label a b c d e f
      hmatrix 0 (α₁ n) (t n) (axisTwo (H n)) (hcoreOrbit n)
    · simp [axisTwo]
    · intro D
      exact first_block_zeroCost (hH n) he hc
    · exact outside_core_affine_nonneg M label (t n) (ht0 n) 0 (α₁ n)
        (hα₁ n).1.le (hα₁ n).2
  have hcost₂ : ∀ n D, idealSingletonDebt M
      (coreOwner label 2) (α₂ n)
        (idealSingletonClearance M (coreOwner label 0) (α₁ n) (t n)) D =
      α₂ n * D := by
    intro n
    let t₁ := idealSingletonClearance M (coreOwner label 0) (α₁ n) (t n)
    have ht₁ : coreRestriction label t₁ = axisOne (H₂ n) := by
      dsimp [t₁]
      rw [coreRestriction_idealSingletonClearance M label a b c d e f hmatrix,
        hcoreOrbit n]
      exact first_block (hH n) he hc
    have ht₁nonneg : ∀ who, 0 ≤ t₁ who := by
      intro who
      by_cases hwho : who = coreOwner label 0
      · simpa [t₁, idealSingletonClearance, hwho] using ht0 n who
      · simp [t₁, idealSingletonClearance, hwho]
    apply idealSingletonDebt_eq_mul_of_core_zeroCost M label a b c d e f
      hmatrix 2 (α₂ n) t₁ (axisOne (H₂ n)) ht₁
    · simp [axisOne]
    · intro D
      exact second_block_zeroCost (hH₂ n) hd hb
    · exact outside_core_affine_nonneg M label t₁ ht₁nonneg 2 (α₂ n)
        (hα₂ n).1.le (hα₂ n).2
  have hcost₃ : ∀ n D, idealSingletonDebt M
      (coreOwner label 1) (α₃ n)
        (idealSingletonClearance M (coreOwner label 2) (α₂ n)
          (idealSingletonClearance M (coreOwner label 0) (α₁ n) (t n))) D =
      α₃ n * D := by
    intro n
    let t₁ := idealSingletonClearance M (coreOwner label 0) (α₁ n) (t n)
    let t₂ := idealSingletonClearance M (coreOwner label 2) (α₂ n) t₁
    have ht₁ : coreRestriction label t₁ = axisOne (H₂ n) := by
      dsimp [t₁]
      rw [coreRestriction_idealSingletonClearance M label a b c d e f hmatrix,
        hcoreOrbit n]
      exact first_block (hH n) he hc
    have ht₂ : coreRestriction label t₂ = axisZero (H₁ n) := by
      dsimp [t₂]
      rw [coreRestriction_idealSingletonClearance M label a b c d e f hmatrix,
        ht₁]
      exact second_block (hH₂ n) hd hb
    have ht₁nonneg : ∀ who, 0 ≤ t₁ who := by
      intro who
      by_cases hwho : who = coreOwner label 0
      · simpa [t₁, idealSingletonClearance, hwho] using ht0 n who
      · simp [t₁, idealSingletonClearance, hwho]
    have ht₂nonneg : ∀ who, 0 ≤ t₂ who := by
      intro who
      by_cases hwho : who = coreOwner label 2
      · simpa [t₂, idealSingletonClearance, hwho] using ht₁nonneg who
      · simp [t₂, idealSingletonClearance, hwho]
    apply idealSingletonDebt_eq_mul_of_core_zeroCost M label a b c d e f
      hmatrix 1 (α₃ n) t₂ (axisZero (H₁ n)) ht₂
    · simp [axisZero]
    · intro D
      exact third_block_zeroCost (hH₁ n) ha hf
    · exact outside_core_affine_nonneg M label t₂ ht₂nonneg 1 (α₃ n)
        (hα₃ n).1.le (hα₃ n).2
  have hlower : 0 < lower := by
    exact lt_min hf (fixedHeight_pos ha hb hc hd hdet)
  have hq := fixed_height_contraction_nonneg_lt_one he hlower
  have hheightLower : ∀ n, lower ≤ H n := by
    intro n
    exact IdealSingletonCarrierBridge.Question193ThreeCoreCarrier.min_height_le_heightOrbit
      hf ha hb hc hd he hdet n
  have hcontract : ∀ n, α₁ n * α₂ n * α₃ n ≤ q := by
    intro n
    exact three_ratio_product_le_fixed_contraction (hH n) ha hb hc hd he
      hlower (hheightLower n)
  have hcompiled := varyingThreeIdealSingletonLassoOrbit_mem_and_debt_tendsto_zero
    reward start (coreOwner label 0) (coreOwner label 2) (coreOwner label 1)
    α₁ α₂ α₃ t
    (fun n => (hα₁ n).1) (fun n => (hα₁ n).2)
    (fun n => (hα₂ n).1) (fun n => (hα₂ n).2)
    (fun n => (hα₃ n).1) (fun n => (hα₃ n).2)
    ht0 (by rfl) hcapStep hcost₁ hcost₂ hcost₃
    q hq.1 hq.2 hcontract hB hreward hstart.1
  constructor
  · intro n
    simpa [ambientSemanticOrbit, start, α₁, α₂, α₃, H, H₂, H₁] using
      (hcompiled.1 n).1
  · simpa [ambientSemanticOrbit, start, α₁, α₂, α₃, H, H₂, H₁] using
      hcompiled.2

/-- Coordinate-free three-core elimination.  Standard-Q and failure of the
homogeneous simplex problem label the corrected core as a positive directed
cycle; the reset-and-lasso construction then supplies carrier points with
total debt tending to zero. -/
theorem exists_carrier_sequence_debt_tendsto_zero_of_three_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcard : Fintype.card (normalCore (normalizedSoloMatrix reward)) = 3)
    (hQ : IsStandardQMatrix
      (normalPlayerMatrix (normalizedSoloMatrix reward)))
    (hhom : ¬HasHomogeneousSimplexSolution
      (normalPlayerMatrix (normalizedSoloMatrix reward))) :
    ∃ pairs : ℕ → QuittingTerminalSemanticPair ι,
      (∀ n, pairs n ∈ quittingTerminalSemanticCarrier reward) ∧
      Tendsto (fun n => quittingTerminalSemanticDebtSum (pairs n))
        atTop (nhds 0) := by
  have hdiag : ∀ i,
      normalPlayerMatrix (normalizedSoloMatrix reward) i i = 0 := by
    intro i
    simp [normalPlayerMatrix, principalMatrix, normalizedSoloMatrix_diagonal]
  obtain ⟨label, a, b, c, d, e, f,
      ha, hb, hc, hd, he, hf, hgap, hmatrix⟩ :=
    ThreeCoreCyclicLabelAdapter.exists_directedCycle_labeling
      (normalPlayerMatrix (normalizedSoloMatrix reward)) hcard hdiag hQ hhom
  have hdet : a * d * e < b * c * f := by
    simpa [cycleGap] using hgap
  refine ⟨ambientSemanticOrbit reward label a b c d e f, ?_⟩
  exact labeled_directedCycle_ambientOrbit_mem_and_debt_tendsto_zero
    reward label ha hb hc hd he hf hdet hmatrix
    (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward)

/-- In particular, a three-element corrected core on the standard-Q,
nonhomogeneous branch cannot support a positive total-debt floor on the
attainable terminal-semantic carrier. -/
theorem no_positive_carrier_debt_floor_of_three_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcard : Fintype.card (normalCore (normalizedSoloMatrix reward)) = 3)
    (hQ : IsStandardQMatrix
      (normalPlayerMatrix (normalizedSoloMatrix reward)))
    (hhom : ¬HasHomogeneousSimplexSolution
      (normalPlayerMatrix (normalizedSoloMatrix reward))) :
    ¬∃ δ : ℝ, 0 < δ ∧
      ∀ pair ∈ quittingTerminalSemanticCarrier reward,
        δ ≤ quittingTerminalSemanticDebtSum pair := by
  obtain ⟨pairs, hpairs, htendsto⟩ :=
    exists_carrier_sequence_debt_tendsto_zero_of_three_core
      reward hcard hQ hhom
  rintro ⟨δ, hδ, hfloor⟩
  have heventually : ∀ᶠ n in atTop,
      quittingTerminalSemanticDebtSum (pairs n) < δ :=
    (tendsto_order.1 htendsto).2 δ hδ
  obtain ⟨n, hn⟩ := eventually_atTop.1 heventually
  have hle := hfloor (pairs n) (hpairs n)
  linarith [hn n (le_refl n)]

/-- Four-player specialization of the three-core debt-floor exclusion. -/
theorem fourPlayer_no_positive_carrier_debt_floor_of_three_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (_hplayers : Fintype.card ι = 4)
    (hcard : Fintype.card (normalCore (normalizedSoloMatrix reward)) = 3)
    (hQ : IsStandardQMatrix
      (normalPlayerMatrix (normalizedSoloMatrix reward)))
    (hhom : ¬HasHomogeneousSimplexSolution
      (normalPlayerMatrix (normalizedSoloMatrix reward))) :
    ¬∃ δ : ℝ, 0 < δ ∧
      ∀ pair ∈ quittingTerminalSemanticCarrier reward,
        δ ≤ quittingTerminalSemanticDebtSum pair :=
  no_positive_carrier_debt_floor_of_three_core reward hcard hQ hhom

/-- A standard-Q, nonhomogeneous three-core branch cannot contain a positive
global minimum of total terminal-semantic debt. -/
theorem not_exists_positive_minimum_of_three_core
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcard : Fintype.card (normalCore (normalizedSoloMatrix reward)) = 3)
    (hQ : IsStandardQMatrix
      (normalPlayerMatrix (normalizedSoloMatrix reward)))
    (hhom : ¬HasHomogeneousSimplexSolution
      (normalPlayerMatrix (normalizedSoloMatrix reward))) :
    ¬∃ minimum : QuittingTerminalSemanticPair ι,
      minimum ∈ quittingTerminalSemanticCarrier reward ∧
      (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum minimum ≤
          quittingTerminalSemanticDebtSum candidate) ∧
      0 < quittingTerminalSemanticDebtSum minimum := by
  rintro ⟨minimum, hminimumMem, hminimum, hminimumPos⟩
  exact no_positive_carrier_debt_floor_of_three_core reward hcard hQ hhom
    ⟨quittingTerminalSemanticDebtSum minimum, hminimumPos, hminimum⟩

/-- The three-element corrected-core counterexample branch is empty: every
finite quitting game whose corrected normal core has cardinality three has an
ordinary uniform-equilibrium payoff.  Standard-Q and nonhomogeneity are not
extra assumptions here; the existing counterexample-facing LCP gate supplies
them under the contrary hypothesis. -/
theorem exists_uniformEquilibriumPayoff_of_normalCore_card_three
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hcard : Fintype.card (normalCore (normalizedSoloMatrix reward)) = 3) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff := by
  by_contra hno
  have hstandard :=
    standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff reward hno
  obtain ⟨minimum, _root, hminimumMem, _hnash, hminimum,
      ⟨who, hwho⟩, _hface⟩ :=
    exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff
      reward (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward) hno
  have hsumPos : 0 < quittingTerminalSemanticDebtSum minimum := by
    have hwhoLe : quittingTerminalSemanticDebt minimum who ≤
        quittingTerminalSemanticDebtSum minimum := by
      unfold quittingTerminalSemanticDebtSum
      exact Finset.single_le_sum
        (fun other _ => quittingTerminalSemanticDebt_nonneg_of_mem_carrier
          reward (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward) hminimumMem other)
        (Finset.mem_univ who)
    exact hwho.trans_le hwhoLe
  exact not_exists_positive_minimum_of_three_core reward hcard
    hstandard.normal_standardQ hstandard.no_homogeneous
    ⟨minimum, hminimumMem, hminimum, hsumPos⟩

/-- Four-player spelling of the eliminated three-core branch. -/
theorem fourPlayer_exists_uniformEquilibriumPayoff_of_normalCore_card_three
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (_hplayers : Fintype.card ι = 4)
    (hcard : Fintype.card (normalCore (normalizedSoloMatrix reward)) = 3) :
    ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff :=
  exists_uniformEquilibriumPayoff_of_normalCore_card_three reward hcard

/-- Every four-player counterexample has the full corrected normal core. -/
theorem normalCore_eq_univ_of_fourPlayer_not_exists_uniformEquilibriumPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hplayers : Fintype.card ι = 4)
    (hnot : ¬∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    normalCore (normalizedSoloMatrix reward) = Finset.univ := by
  have hstandard :=
    standardQMatrixSide_of_not_exists_uniformEquilibriumPayoff reward hnot
  have hcards := StandardQSideExample.standardQSide_core_card_eq_three_or_four
    (normalizedSoloMatrix reward)
    (normalizedSoloMatrix_diagonal reward) hplayers hstandard.normal_nonempty
    hstandard.normal_standardQ
  rcases hcards with hthree | hfour
  · exact False.elim
      (hnot (exists_uniformEquilibriumPayoff_of_normalCore_card_three
        reward (by simpa using hthree)))
  · apply Finset.eq_univ_of_card
    simpa [hplayers] using hfour

end ThreeCoreAmbientCarrierElimination
end GameTheory
