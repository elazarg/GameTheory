/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.EssentialAPS.OpponentMass
import UniformEquilibrium.Quitting.Cycles.BlockSurvival
import UniformEquilibrium.Quitting.Stationary.SingletonStationaryRoot

/-!
# Opponent contraction from essential-APS mass

For nonnegative stage hazards `q_t ≤ 1`,

`(∏ (1 - q_t)) * (1 + ∑ q_t) ≤ 1`.

Consequently opponent mass at least `eta > 0` in a block forces opponent
survival at most `1 / (1 + eta) < 1`.  Specializing the factors to singleton
roots turns the deterministic APS opponent-mass estimate into exactly the
`IsQuittingOpponentBlockContraction` hypothesis consumed by the nonperiodic
quitting-path compiler.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The amount of absorption mass at one stage contributed by an opponent of
`who`. -/
def quittingEssentialAPSOpponentStageMass
    (owner : ℕ → ι) (mass : ℕ → ℝ) (who : ι) (time : ℕ) : ℝ :=
  if owner time = who then 0 else mass time

/-- Singleton product roots implementing an APS mass path. -/
def quittingEssentialAPSSingletonRoots
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1) :
    ℕ → ι → PMF Bool :=
  fun time ↦ quittingSoloStationaryRoot (owner time)
    (quittingHazardCoin (mass time) (hmass0 time) (hmass1 time))

omit [Fintype ι] in
/-- Opponent stage mass inherits nonnegativity. -/
theorem quittingEssentialAPSOpponentStageMass_nonneg
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (who : ι) (time : ℕ) :
    0 ≤ quittingEssentialAPSOpponentStageMass owner mass who time := by
  unfold quittingEssentialAPSOpponentStageMass
  split <;> simp_all

omit [Fintype ι] in
/-- Opponent stage mass is at most one. -/
theorem quittingEssentialAPSOpponentStageMass_le_one
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass1 : ∀ time, mass time ≤ 1)
    (who : ι) (time : ℕ) :
    quittingEssentialAPSOpponentStageMass owner mass who time ≤ 1 := by
  unfold quittingEssentialAPSOpponentStageMass
  split <;> simp_all

omit [Fintype ι] in
/-- The window sum of stagewise opponent mass is the previously defined
opponent window mass. -/
theorem sum_quittingEssentialAPSOpponentStageMass
    (owner : ℕ → ι) (mass : ℕ → ℝ) (who : ι)
    (start fuel : ℕ) :
    (∑ offset ∈ Finset.range fuel,
        quittingEssentialAPSOpponentStageMass owner mass who
          (start + offset)) =
      quittingEssentialAPSOpponentWindowMass owner mass who start fuel := by
  rfl

/-- Against a singleton root, the deleted-player continue mass is one minus
that player's opponent stage mass. -/
theorem quittingFixedOpponentsContinueMass_singletonRoots
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    (who : ι) (time : ℕ) :
    quittingFixedOpponentsContinueMass
        (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
        who time =
      1 - quittingEssentialAPSOpponentStageMass owner mass who time := by
  unfold quittingEssentialAPSSingletonRoots
  unfold quittingFixedOpponentsContinueMass
  by_cases howner : owner time = who
  · subst who
    simp [quittingEssentialAPSOpponentStageMass]
  · have hne : who ≠ owner time := Ne.symm howner
    rw [update_quittingSoloStationaryRoot_other hne,
      quittingStationaryContinueMass_solo]
    simp [quittingEssentialAPSOpponentStageMass, howner]

/-- Finite opponent survival of singleton roots is the product of one minus
the APS opponent stage masses. -/
theorem quittingOpponentSurvivalWeight_singletonRoots_eq
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    (who : ι) (start fuel : ℕ) :
    quittingOpponentSurvivalWeight
        (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
        who start fuel =
      ∏ offset ∈ Finset.range fuel,
        (1 - quittingEssentialAPSOpponentStageMass owner mass who
          (start + offset)) := by
  unfold quittingOpponentSurvivalWeight
  apply Finset.prod_congr rfl
  intro offset _
  exact quittingFixedOpponentsContinueMass_singletonRoots
    owner mass hmass0 hmass1 who (start + offset)

/-- Product-versus-sum estimate for hazards in `[0,1]`. -/
theorem prod_one_sub_mul_one_add_sum_le_one
    (hazard : ℕ → ℝ)
    (hhazard0 : ∀ time, 0 ≤ hazard time)
    (hhazard1 : ∀ time, hazard time ≤ 1) :
    ∀ start fuel,
      (∏ offset ∈ Finset.range fuel,
          (1 - hazard (start + offset))) *
          (1 + ∑ offset ∈ Finset.range fuel,
            hazard (start + offset)) ≤ 1 := by
  intro start fuel
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      let product : ℝ :=
        ∏ offset ∈ Finset.range fuel, (1 - hazard (start + offset))
      let total : ℝ :=
        ∑ offset ∈ Finset.range fuel, hazard (start + offset)
      let last : ℝ := hazard (start + fuel)
      have hproduct0 : 0 ≤ product := by
        dsimp only [product]
        apply Finset.prod_nonneg
        intro offset _
        exact sub_nonneg.mpr (hhazard1 (start + offset))
      have htotal0 : 0 ≤ total := by
        dsimp only [total]
        exact Finset.sum_nonneg fun offset _ ↦ hhazard0 (start + offset)
      have hlast0 : 0 ≤ last := hhazard0 (start + fuel)
      have hfactor :
          (1 - last) * (1 + total + last) ≤ 1 + total := by
        nlinarith [mul_nonneg hlast0 htotal0, sq_nonneg last]
      have hscaled := mul_le_mul_of_nonneg_left hfactor hproduct0
      calc
        product * (1 - last) * (1 + (total + last)) =
            product * ((1 - last) * (1 + total + last)) := by ring
        _ ≤ product * (1 + total) := hscaled
        _ ≤ 1 := by
          simpa only [product, total] using ih

/-- A lower bound on cumulative hazard gives a strict explicit product bound. -/
theorem prod_one_sub_le_one_div_one_add_of_le_sum
    (hazard : ℕ → ℝ)
    (hhazard0 : ∀ time, 0 ≤ hazard time)
    (hhazard1 : ∀ time, hazard time ≤ 1)
    {eta : ℝ} (heta0 : 0 ≤ eta)
    (start fuel : ℕ)
    (heta : eta ≤ ∑ offset ∈ Finset.range fuel,
      hazard (start + offset)) :
    (∏ offset ∈ Finset.range fuel,
        (1 - hazard (start + offset))) ≤ 1 / (1 + eta) := by
  let product : ℝ :=
    ∏ offset ∈ Finset.range fuel, (1 - hazard (start + offset))
  let total : ℝ :=
    ∑ offset ∈ Finset.range fuel, hazard (start + offset)
  have hproduct0 : 0 ≤ product := by
    dsimp only [product]
    apply Finset.prod_nonneg
    intro offset _
    exact sub_nonneg.mpr (hhazard1 (start + offset))
  have hdenom : 0 < 1 + eta := by linarith
  have hsum := prod_one_sub_mul_one_add_sum_le_one
    hazard hhazard0 hhazard1 start fuel
  have hscaled : product * (1 + eta) ≤ product * (1 + total) := by
    exact mul_le_mul_of_nonneg_left (by linarith) hproduct0
  apply (le_div_iff₀ hdenom).2
  calc
    product * (1 + eta) ≤ product * (1 + total) := hscaled
    _ ≤ 1 := by simpa only [product, total] using hsum

/-- An APS opponent-mass floor gives the corresponding singleton-root
opponent-survival bound. -/
theorem quittingOpponentSurvivalWeight_singletonRoots_le
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    {eta : ℝ} (heta0 : 0 ≤ eta)
    (who : ι) (start fuel : ℕ)
    (heta : eta ≤
      quittingEssentialAPSOpponentWindowMass owner mass who start fuel) :
    quittingOpponentSurvivalWeight
        (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
        who start fuel ≤ 1 / (1 + eta) := by
  rw [quittingOpponentSurvivalWeight_singletonRoots_eq]
  apply prod_one_sub_le_one_div_one_add_of_le_sum
    (quittingEssentialAPSOpponentStageMass owner mass who)
    (quittingEssentialAPSOpponentStageMass_nonneg owner mass hmass0 who)
    (quittingEssentialAPSOpponentStageMass_le_one owner mass hmass1 who)
    heta0 start fuel
  simpa only [sum_quittingEssentialAPSOpponentStageMass] using heta

/-- A uniform opponent-mass floor on aligned blocks is exactly a block
contraction certificate for the implemented singleton roots. -/
theorem isQuittingOpponentBlockContraction_singletonRoots_of_opponentMass
    (owner : ℕ → ι) (mass : ℕ → ℝ)
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    {K : ℕ} {eta : ℝ} (heta0 : 0 ≤ eta)
    (hopponent : ∀ block who,
      eta ≤ quittingEssentialAPSOpponentWindowMass owner mass who
        (block * K) K) :
    IsQuittingOpponentBlockContraction
      (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
      K (1 / (1 + eta)) := by
  intro block who
  exact quittingOpponentSurvivalWeight_singletonRoots_le
    owner mass hmass0 hmass1 heta0 who (block * K) K
      (hopponent block who)

/-- The contraction rate supplied by a positive opponent-mass floor is
nonnegative and strictly below one. -/
theorem one_div_one_add_opponentMass_mem_Ico {eta : ℝ} (heta : 0 < eta) :
    1 / (1 + eta) ∈ Set.Ico (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg zero_le_one (by linarith)
  · apply (div_lt_iff₀ (by linarith : 0 < 1 + eta)).2
    linarith

/-- **Total APS mass forces playerwise block contraction.**  If every window
of length `window` carries total mass at least `nu`, then any sufficiently
long concatenation of those windows has a positive opponent-mass floor for
every player. -/
theorem
    isQuittingOpponentBlockContraction_singletonRoots_of_windowMass
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (successor : ι → ι) (owner : ℕ → ι)
    (mass : ℕ → ℝ) (value : ℕ → Payoff ι)
    {gap bound nu : ℝ} {window blocks : ℕ}
    (hgapPos : 0 < gap) (hbound : 0 ≤ bound) (_hnu : 0 < nu)
    (hwindow : ∀ start,
      nu ≤ quittingEssentialAPSWindowMass mass start window)
    (hwindowPos : 0 < window) (hblocksPos : 0 < blocks)
    (hlarge : 2 * bound < gap * ((blocks : ℝ) * nu))
    (hmass0 : ∀ time, 0 ≤ mass time)
    (hmass1 : ∀ time, mass time ≤ 1)
    (harc : ∀ time,
      value time = quittingSingletonArcPayoff (mass time)
        (quittingSoloReward reward (owner time)) (value (time + 1)))
    (hactive : ∀ time,
      value time (owner time) =
        quittingSoloReward reward (owner time) (owner time))
    (hownerNext : ∀ time,
      owner (time + 1) = successor (owner time))
    (hgap : ∀ player,
      gap ≤ quittingSoloReward reward player (successor player) -
        quittingSoloReward reward (successor player) (successor player))
    (hrootBound : ∀ time who,
      |quittingSoloReward reward (owner time) who| ≤ bound)
    (hvalueBound : ∀ time who, |value time who| ≤ bound) :
    let K := blocks * window
    let eta :=
      (gap * ((blocks : ℝ) * nu) - 2 * bound) / (gap + 2 * bound)
    let rho := 1 / (1 + eta)
    0 < K ∧ 0 < eta ∧ 0 ≤ rho ∧ rho < 1 ∧
      IsQuittingOpponentBlockContraction
        (quittingEssentialAPSSingletonRoots owner mass hmass0 hmass1)
        K rho := by
  dsimp only
  let eta : ℝ :=
    (gap * ((blocks : ℝ) * nu) - 2 * bound) / (gap + 2 * bound)
  have hdenom : 0 < gap + 2 * bound := by positivity
  have heta : 0 < eta := by
    dsimp only [eta]
    exact div_pos (sub_pos.mpr hlarge) hdenom
  have hK : 0 < blocks * window := Nat.mul_pos hblocksPos hwindowPos
  have hopponent : ∀ block who,
      eta ≤ quittingEssentialAPSOpponentWindowMass owner mass who
        (block * (blocks * window)) (blocks * window) := by
    intro block who
    apply div_le_quittingEssentialAPSOpponentWindowMass_of_windowMass_le
      reward successor owner mass value hgapPos hbound hmass0 harc hactive
        hownerNext hgap hrootBound hvalueBound
    exact mul_le_quittingEssentialAPSWindowMass_mul mass hwindow blocks
      (block * (blocks * window))
  have hrho := one_div_one_add_opponentMass_mem_Ico heta
  refine ⟨hK, heta, hrho.1, hrho.2, ?_⟩
  exact isQuittingOpponentBlockContraction_singletonRoots_of_opponentMass
    owner mass hmass0 hmass1 heta.le hopponent

end GameTheory
