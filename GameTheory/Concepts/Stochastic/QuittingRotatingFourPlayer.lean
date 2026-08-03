/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSingletonArcCycle

/-!
# The normalized rotating four-player quitting family

This file instantiates the singleton-arc compiler for the rotating family in
Question 121.  The algebraic parameterization

`kappa = (2 - v) * (1 - v)`, `u = 2 * v - v ^ 2`, with `0 < v < 1`,

makes all four coarse Bellman identities polynomial.  The active-owner order
is `0, 3, 2, 1`, and the four coarse vertices are rotations of
`(1, 1, 1 + u, 1 + v)`.  Consequently the construction supplies both a fixed
uniform-equilibrium payoff and an explicit horizon-indexed square-root rate.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace RotatingFourPlayerQuitting

open StochasticGame Math.Probability Math.PMFProduct

/-- The four cyclic players. -/
abbrev Player := Fin 4

/-- A nonempty terminal quitter set. -/
abbrev Terminal := {S : Finset Player // S.Nonempty}

/-- The normalized cost parameter selected by the geometric shape `v`. -/
def kappa (v : ℝ) : ℝ := (2 - v) * (1 - v)

/-- The second coordinate of the rotating shape. -/
def u (v : ℝ) : ℝ := 2 * v - v ^ 2

theorem kappa_pos {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    0 < kappa v := by
  unfold kappa
  exact mul_pos (by linarith) (by linarith)

theorem kappa_lt_two {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    kappa v < 2 := by
  unfold kappa
  nlinarith

theorem u_pos {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    0 < u v := by
  unfold u
  nlinarith

theorem u_eq_one_sub_sq (v : ℝ) :
    u v = 1 - (1 - v) ^ 2 := by
  unfold u
  ring

/-- The exact normalized terminal table from (24)--(26) of Question 121.
The impossible all-false branch is assigned zero to make the match total. -/
def terminalReward (cost : ℝ) (S : Terminal) : Payoff Player :=
  match decide (0 ∈ S.1), decide (1 ∈ S.1),
      decide (2 ∈ S.1), decide (3 ∈ S.1) with
  | true, false, false, false => ![1, 1 - cost, 2, 2]
  | false, true, false, false => ![2, 1, 1 - cost, 2]
  | false, false, true, false => ![2, 2, 1, 1 - cost]
  | false, false, false, true => ![1 - cost, 2, 2, 1]
  | true, true, false, false => ![-1, 3 - cost, 2 - cost, 3]
  | true, false, true, false => ![-1, 2 - cost, -1, 2 - cost]
  | true, false, false, true => ![3 - cost, 2 - cost, 3, -1]
  | false, true, true, false => ![3, -1, 3 - cost, 2 - cost]
  | false, true, false, true => ![2 - cost, -1, 2 - cost, -1]
  | false, false, true, true => ![2 - cost, 3, -1, 3 - cost]
  | true, true, true, false => ![-4, -cost, -cost, 3 - cost]
  | true, true, false, true => ![-cost, -cost, 3 - cost, -4]
  | true, false, true, true => ![-cost, 3 - cost, -4, -cost]
  | false, true, true, true => ![3 - cost, -4, -cost, -cost]
  | true, true, true, true =>
      ![-3 - cost, -3 - cost, -3 - cost, -3 - cost]
  | false, false, false, false => ![0, 0, 0, 0]

/-- Coarse-block owners, in the rotating order `0, 3, 2, 1`. -/
def owner : Fin 4 → Player := ![0, 3, 2, 1]

/-- Every coarse arc has total hazard `v`. -/
def arcHazard (v : ℝ) : Fin 4 → ℝ := fun _ ↦ v

/-- The four cyclic coarse vertices.  Block zero is the designated target. -/
def coarse (v : ℝ) : Fin 4 → Payoff Player :=
  ![
    ![1, 1, 1 + u v, 1 + v],
    ![1, 1 + u v, 1 + v, 1],
    ![1 + u v, 1 + v, 1, 1],
    ![1 + v, 1, 1, 1 + u v]
  ]

/-- The designated phase-start vector. -/
def target (v : ℝ) : Payoff Player := ![1, 1, 1 + u v, 1 + v]

@[simp] theorem coarse_zero (v : ℝ) : coarse v 0 = target v := by
  rfl

/-- A singleton quit by `j` has the relative reward vector
`(1, 1-kappa, 2, 2)`. -/
theorem soloReward_self (v : ℝ) (j : Player) :
    quittingSoloReward (terminalReward (kappa v)) j j = 1 := by
  fin_cases j <;> simp [quittingSoloReward, terminalReward]

/-- The four coarse vertices satisfy the exact singleton-flow Bellman arcs. -/
theorem coarse_arc (v : ℝ) : ∀ block,
    coarse v block =
      quittingSingletonArcPayoff (arcHazard v block)
        (quittingSoloReward (terminalReward (kappa v)) (owner block))
        (coarse v (finRotate 4 block)) := by
  intro block
  funext who
  fin_cases block <;> fin_cases who <;>
    simp [coarse, owner, arcHazard, quittingSingletonArcPayoff,
      quittingSoloReward, terminalReward, kappa, u, finRotate_apply] <;>
    ring

/-- The active coordinate is exactly its singleton reward at every vertex. -/
theorem coarse_active (v : ℝ) : ∀ block,
    coarse v block (owner block) =
      quittingSoloReward (terminalReward (kappa v))
        (owner block) (owner block) := by
  intro block
  fin_cases block <;>
    simp [coarse, owner, quittingSoloReward, terminalReward]

/-- Every singleton own payoff is below every coarse vertex. -/
theorem soloReward_le_coarse {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    ∀ block who,
      quittingSoloReward (terminalReward (kappa v)) who who ≤
        coarse v block who := by
  have hu0 : 0 ≤ u v := (u_pos hv0 hv1).le
  intro block who
  fin_cases block <;> fin_cases who <;>
    simp [coarse, quittingSoloReward, terminalReward] <;>
    linarith

set_option linter.flexible false in
/-- The only positive pair-collision surplus is `2-kappa`. -/
theorem collision_surplus_le {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    ∀ block other, other ≠ owner block →
      max
          (quittingSingletonCollisionReward
              (terminalReward (kappa v)) (owner block) other -
            quittingSoloReward (terminalReward (kappa v)) other other)
          0 ≤
        2 - kappa v := by
  have hk2 : kappa v < 2 := kappa_lt_two hv0 hv1
  have hkD : 0 ≤ 2 - kappa v := by linarith
  intro block other hne
  fin_cases block <;> fin_cases other <;>
    simp [owner, quittingSingletonCollisionReward, quittingSoloReward,
      terminalReward] at hne ⊢
  all_goals first | constructor <;> linarith | linarith

/-- Each player sees exactly three of the four coarse hazards as opponent
hazards. -/
theorem opponentProduct (v : ℝ) (who : Player) :
    (∏ block : Fin 4,
      if who = owner block then 1 else 1 - arcHazard v block) =
        (1 - v) ^ 3 := by
  fin_cases who <;>
    simp [owner, arcHazard, Fin.prod_univ_succ] <;>
    ring

theorem opponentProduct_lt_one {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1)
    (who : Player) :
    (∏ block : Fin 4,
      if who = owner block then 1 else 1 - arcHazard v block) < 1 := by
  rw [opponentProduct]
  exact pow_lt_one₀ (by linarith) (by linarith) (by norm_num)

set_option linter.flexible false in
/-- Every normalized terminal reward has absolute value at most five. -/
theorem abs_terminalReward_le_five {cost : ℝ}
    (hcost0 : 0 < cost) (hcost2 : cost < 2)
    (terminal : Terminal) (who : Player) :
    |terminalReward cost terminal who| ≤ 5 := by
  rcases terminal with ⟨S, hS⟩
  by_cases h0 : 0 ∈ S
  <;> by_cases h1 : 1 ∈ S
  <;> by_cases h2 : 2 ∈ S
  <;> by_cases h3 : 3 ∈ S
  <;> fin_cases who
  <;> simp [terminalReward, h0, h1, h2, h3, abs_le]
  all_goals first | constructor <;> linarith | linarith

/-! ## Concrete compiler outputs -/

/-- The fixed target selected by the rotating coarse cycle is a uniform
equilibrium payoff.  The proof chooses one sufficiently fine, then fixed,
four-block mesh for each requested accuracy. -/
theorem target_isUniformEquilibriumPayoff {v : ℝ}
    (hv0 : 0 < v) (hv1 : v < 1) :
    (quittingGame (terminalReward (kappa v))).IsUniformEquilibriumPayoff
      none (target v) := by
  have hp0 : ∀ block, 0 ≤ arcHazard v block := fun _ ↦ hv0.le
  have hp1 : ∀ block, arcHazard v block < 1 := fun _ ↦ hv1
  have ha : ∀ block,
      quittingMeshIntensity (arcHazard v block) ≤
        quittingMeshIntensity v := fun _ ↦ le_rfl
  have hD : 0 ≤ 2 - kappa v := by
    linarith [kappa_lt_two hv0 hv1]
  have hcontracts : ∀ who,
      (∏ block : Fin 4,
        if who = owner block then 1 else 1 - arcHazard v block) < 1 :=
    opponentProduct_lt_one hv0 hv1
  have h := singletonArcCycle_isUniformEquilibriumPayoff
    (terminalReward (kappa v)) owner (arcHazard v) (coarse v) 0
    (aStar := quittingMeshIntensity v) (D := 2 - kappa v)
    hp0 hp1 ha hD (coarse_arc v) (coarse_active v)
    (soloReward_le_coarse hv0 hv1) (collision_surplus_le hv0 hv1)
    hcontracts
  simpa only [coarse_zero] using h

/-- The canonical horizon-indexed `ceil (sqrt N)` rotating mesh. -/
def sqrtMeshProfile (v : ℝ) (hv0 : 0 ≤ v) (hv1 : v < 1)
    (N : ℕ) (hN : 1 ≤ (N : ℝ)) :
    (quittingGame (terminalReward (kappa v))).BehaviorProfile :=
  quittingCyclicBehaviorProfile (terminalReward (kappa v))
    (quittingSingletonArcCycleRoot owner (arcHazard v)
      (quittingSqrtMeshScale N) (fun _ ↦ hv0) (fun _ ↦ hv1))
    (quittingSingletonMeshInitialPhase 0 (quittingSqrtMeshScale N)
      (quittingSqrtMeshScale_spec hN).1)

/-- Explicit coefficient in the horizon Nash error. -/
def horizonNashConstant (v : ℝ) : ℝ :=
  (2 - kappa v) * quittingMeshIntensity v +
    4 * 5 * ((4 : ℝ) / (1 - (1 - v) ^ 3))

/-- Explicit coefficient in delivery to the designated coarse vertex. -/
def horizonDeliveryConstant (v : ℝ) : ℝ :=
  2 * 5 * ((4 : ℝ) / (1 - (1 - v) ^ 3))

theorem horizonNashConstant_eq (v : ℝ) :
    horizonNashConstant v =
      (2 - kappa v) * (-Real.log (1 - v)) +
        80 / (1 - (1 - v) ^ 3) := by
  unfold horizonNashConstant quittingMeshIntensity
  ring

theorem horizonDeliveryConstant_eq (v : ℝ) :
    horizonDeliveryConstant v = 40 / (1 - (1 - v) ^ 3) := by
  unfold horizonDeliveryConstant
  ring

/-- The normalized rotating family has a completely explicit
`O(N⁻¹⁄²)` horizon Nash profile and delivers the same fixed target.

The one-cycle opponent continuation product is exactly `(1-v)^3`; the local
quit error coefficient is exactly `2-kappa`, and every terminal reward is
bounded by five. -/
theorem sqrtMeshProfile_isHorizonNash_and_delivers {v : ℝ}
    (hv0 : 0 < v) (hv1 : v < 1) {N : ℕ} (hN : 1 ≤ (N : ℝ)) :
    (quittingGame (terminalReward (kappa v))).IsεHorizonNash none N
        (horizonNashConstant v / Real.sqrt (N : ℝ))
        (sqrtMeshProfile v hv0.le hv1 N hN) ∧
      ∀ who,
        |(quittingGame (terminalReward (kappa v))).finiteAveragePayoff
              none N (sqrtMeshProfile v hv0.le hv1 N hN) who -
            target v who| ≤
          horizonDeliveryConstant v / Real.sqrt (N : ℝ) := by
  have hp0 : ∀ block, 0 ≤ arcHazard v block := fun _ ↦ hv0.le
  have hp1 : ∀ block, arcHazard v block < 1 := fun _ ↦ hv1
  have ha : ∀ block,
      quittingMeshIntensity (arcHazard v block) ≤
        quittingMeshIntensity v := fun _ ↦ le_rfl
  have hD : 0 ≤ 2 - kappa v := by
    linarith [kappa_lt_two hv0 hv1]
  have hrho : (1 - v) ^ 3 < 1 :=
    pow_lt_one₀ (by linarith) (by linarith) (by norm_num)
  have hreward : ∀ terminal who,
      |terminalReward (kappa v) terminal who| ≤ 5 :=
    abs_terminalReward_le_five (kappa_pos hv0 hv1)
      (kappa_lt_two hv0 hv1)
  have hprod : ∀ who,
      (∏ block : Fin 4,
        if who = owner block then 1 else 1 - arcHazard v block) ≤
          (1 - v) ^ 3 := by
    intro who
    rw [opponentProduct]
  have h := singletonArcCycle_isHorizonNash_and_delivers
    (terminalReward (kappa v)) owner (arcHazard v) (coarse v) 0
    (N := N) (aStar := quittingMeshIntensity v) (D := 2 - kappa v)
    (rhoBar := (1 - v) ^ 3) (bound := 5)
    hp0 hp1 ha hD hrho (by norm_num) hN hreward
    (coarse_arc v) (coarse_active v) (soloReward_le_coarse hv0 hv1)
    (collision_surplus_le hv0 hv1) hprod
  simpa [sqrtMeshProfile, horizonNashConstant,
    horizonDeliveryConstant] using h

/-! ## Selection from the normalized cost parameter -/

/-- The exact rotating shape selected by a normalized cost `cost`. -/
def selectedV (cost : ℝ) : ℝ :=
  (3 - Real.sqrt (1 + 4 * cost)) / 2

theorem selectedV_mem_Ioo {cost : ℝ}
    (hcost0 : 0 < cost) (hcost2 : cost < 2) :
    selectedV cost ∈ Set.Ioo (0 : ℝ) 1 := by
  have hradicand : 0 ≤ 1 + 4 * cost := by linarith
  have hsquare : (Real.sqrt (1 + 4 * cost)) ^ 2 = 1 + 4 * cost := by
    exact Real.sq_sqrt hradicand
  have hsqrt0 : 0 ≤ Real.sqrt (1 + 4 * cost) := Real.sqrt_nonneg _
  have hsqrtLower : 1 < Real.sqrt (1 + 4 * cost) := by
    nlinarith
  have hsqrtUpper : Real.sqrt (1 + 4 * cost) < 3 := by
    nlinarith
  constructor <;> unfold selectedV <;> linarith

/-- The selected shape solves the exact algebraic root identity
`cost = (2-v)(1-v)`. -/
theorem kappa_selectedV {cost : ℝ} (hcost0 : 0 < cost) :
    kappa (selectedV cost) = cost := by
  have hradicand : 0 ≤ 1 + 4 * cost := by linarith
  have hsquare : (Real.sqrt (1 + 4 * cost)) ^ 2 = 1 + 4 * cost :=
    Real.sq_sqrt hradicand
  unfold kappa selectedV
  nlinarith

/-- Every normalized member `0 < cost < 2` therefore has the fixed
uniform-equilibrium payoff selected by its exact square-root shape. -/
theorem selectedTarget_isUniformEquilibriumPayoff {cost : ℝ}
    (hcost0 : 0 < cost) (hcost2 : cost < 2) :
    (quittingGame (terminalReward cost)).IsUniformEquilibriumPayoff none
      (target (selectedV cost)) := by
  have hv := selectedV_mem_Ioo hcost0 hcost2
  have h := target_isUniformEquilibriumPayoff hv.1 hv.2
  rw [kappa_selectedV hcost0] at h
  exact h

/-- For every normalized cost `0 < cost < 2` and every positive horizon,
the canonical square-root mesh gives a horizon Nash profile with the explicit
coefficient from `horizonNashConstant`, while delivering the fixed selected
target with coefficient `horizonDeliveryConstant`. -/
theorem exists_selectedHorizonProfile {cost : ℝ}
    (hcost0 : 0 < cost) (hcost2 : cost < 2)
    {N : ℕ} (hN : 1 ≤ (N : ℝ)) :
    ∃ profile : (quittingGame (terminalReward cost)).BehaviorProfile,
      (quittingGame (terminalReward cost)).IsεHorizonNash none N
          (horizonNashConstant (selectedV cost) / Real.sqrt (N : ℝ))
          profile ∧
        ∀ who,
          |(quittingGame (terminalReward cost)).finiteAveragePayoff
                none N profile who - target (selectedV cost) who| ≤
            horizonDeliveryConstant (selectedV cost) /
              Real.sqrt (N : ℝ) := by
  have hv := selectedV_mem_Ioo hcost0 hcost2
  have h := sqrtMeshProfile_isHorizonNash_and_delivers hv.1 hv.2 hN
  rw [kappa_selectedV hcost0] at h
  exact ⟨_, h⟩

end RotatingFourPlayerQuitting
end GameTheory
