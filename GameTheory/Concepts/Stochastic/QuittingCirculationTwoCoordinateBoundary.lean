/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.SingletonFaceCirculation
import GameTheory.Concepts.Stochastic.QuittingTwoPlayerExistence
import GameTheory.Concepts.Stochastic.QuittingTwoPlayerPairRepair

/-!
# The circulation certificate class, measured at two coordinates

The face-circulation certificate (`FaceCirculationCertificate`, in
`SingletonFaceCirculation.lean`) is the program's newest existence engine.
This file asks whether it is real at `n = 2`, where the two-player capstone
(`QuittingTwoPlayerExistence.lean`) already closes the whole conjecture by a
four-way case split, or whether circulation is strictly a high-`n` device.

## The two-coordinate reduction

At `ι = Bool` an `L = 1` certificate collapses completely: `ZMod 1` is a
subsingleton, so `vertex`, `mixWeight`, `ratio` are each a single value
`z, λ, α`, and the `step` equation `z = α z + (1 - α) u` (with `u` the mixed
target `mixTarget r λ`) forces `z = u` since `α < 1`. What survives is
exactly

* `λ : Bool → ℝ` a distribution on the two players (`CirculationL1Feasible`);
* `u = λ_false · r{false} + λ_true · r{true}`, the mix of the two solo rows;
* `u ≥ floor` at both coordinates;
* pinning: `λ_j > 0 ⟹ u_j = r{j}_j` (`d_j`, `j`'s own solo value).

`faceCirculationCertificate_one_bool_iff` proves this reduction directly from
the real structure. `circulationL1Feasible_bool_iff` then closes
`CirculationL1Feasible` into the two-coordinate disjunction, mirroring
`Math.LinearProgramming.SingletonLCP`'s `singletonLCPFeasible_bool_iff`: a
pure witness at `false`, a pure witness at `true`, or a mixed witness. Unlike
the LCP case, the mixed disjunct is *not* a genuine third case here: solving
its two pinning equations forces `r{false} = r{true}` outright, at which
point it is subsumed by either pure disjunct. So the closed form is a clean
two-way split, `(∀ j, floor j ≤ r{false} j) ∨ (∀ j, floor j ≤ r{true} j)`.

## The floor and the min-max parameter

`floor j = max (d_j) (χ_j)` with `χ` the (unformalized) min-max level,
constrained only by `χ_j ≤ max 0 (d_j)` (`ValidFloorFor`,
`validFloorFor_iff_exists_chi`). This pins the *achievable range* of `floor`
to the interval `[d_j, max 0 (d_j)]`, independent of `χ`'s real value. Asking
whether *some* admissible `χ` gives a certificate (`CirculationTwoExists`)
therefore reduces to the *easiest* floor, `floor = d` — always achievable,
since `χ_j := d_j` satisfies the bound trivially — giving the headline
closed form (`circulationTwoExists_iff`):

  `CirculationTwoExists v0 v1 ↔ v1 true ≤ v0 true ∨ v0 false ≤ v1 false`.

Reading `v0 = r{false}`, `v1 = r{true}`: the class holds exactly when one
player's own solo value is dominated by the *other* player's cross payoff.

## The verdict

None of the two-player capstone's four branches implies this disjunction.
Each admits an explicit weight, built from `sampleReward`, satisfying the
branch's own hypotheses — and, for the two branches checked against the
headline theorems directly, actually producing a uniform-equilibrium payoff
via that branch — while failing `circulationTwoExists_iff` at both
disjuncts (`pairRepair_exists_outside_circulationTwoExists`,
`soloRate_exists_outside_circulationTwoExists`,
`jointExit_exists_outside_circulationTwoExists`,
`zeroSolo_exists_outside_circulationTwoExists`).

The pair-repair branch, flagged as the one needing genuinely approximate
equilibria, is confirmed **outside** the circulation class: its two defining
inequalities (`howner`, `hblocker`) pull in exactly the wrong direction for
the pure-witness case they most resemble (`hblocker` gives
`v0 true ≤ v1 true`, the reverse of what `circulationTwoExists_iff`'s second
disjunct needs), so satisfying them generically breaks both disjuncts at
once. But the same construction breaks all three *other* branches too. The
verdict is not "circulation misses one branch" but the stronger fact that
**the `L = 1` circulation floor is a strictly stronger rationality demand
than two-player Nash rationality**: it asks a player's equilibrium payoff to
dominate its own solo value at every coordinate, which no branch of the
capstone guarantees (each branch's mechanism can legitimately hand a player
less than its own solo value, compensated by an unattractive alternative).
Circulation, at `L = 1`, is confirmed a genuinely high-`n` device: at
`n = 2` it is neither implied by nor implies the class the capstone closed.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open QuittingTwoPlayerExistence QuittingTwoPlayerPairRepair

namespace QuittingCirculationTwoCoordinateBoundary

/-! ## The `L = 1` two-coordinate certificate, as a pure `λ`-mixing `Prop` -/

/-- **The `L = 1`, two-coordinate circulation certificate**, as a bare
existence statement: some distribution `λ` on `Bool` whose mix of the two
solo rows `v0 = r{false}`, `v1 = r{true}` dominates `floor` everywhere and
pins every coordinate its own player has positive weight on. This is exactly
what an `L = 1` `FaceCirculationCertificate` reduces to at `ι = Bool`
(`faceCirculationCertificate_one_bool_iff`), short of the weight-level
`solo_le_floor` axiom, which is orthogonal to the choice of `λ`. -/
def CirculationL1Feasible (v0 v1 floor : Bool → ℝ) : Prop :=
  ∃ lam : Bool → ℝ, 0 ≤ lam false ∧ 0 ≤ lam true ∧ lam false + lam true = 1 ∧
    (∀ j, floor j ≤ lam false * v0 j + lam true * v1 j) ∧
    (0 < lam false → lam false * v0 false + lam true * v1 false = v0 false) ∧
    (0 < lam true → lam false * v0 true + lam true * v1 true = v1 true)

/-! ## Reduction from the real certificate structure -/

/-- Every element of `ZMod 1` is `0`: the phase index is a subsingleton. -/
private theorem zmod_one_eq_zero (l : ZMod 1) : l = 0 := Subsingleton.elim l 0

/-- `mixTarget` at `ι = Bool`, expanded into its two summands in a fixed
order. Routing every use of `mixTarget` through this lemma avoids fighting
`Fintype.sum_bool`'s own summand order by hand. -/
private theorem mixTarget_bool_eq (r : Finset Bool → Bool → ℝ) (lam : Bool → ℝ) (j : Bool) :
    mixTarget r lam j = lam false * r {false} j + lam true * r {true} j := by
  simp only [mixTarget, Fintype.sum_bool]
  ring

/-- **The `L = 1` reduction, faithfully derived.** An `L = 1`
`FaceCirculationCertificate` for `r` and `floor` exists iff `solo_le_floor`
holds and the two-coordinate mixing problem `CirculationL1Feasible` is
feasible for the solo rows `r{false}, r{true}`. The forward direction
solves `step`'s single equation for `vertex 0 = mixTarget r (mixWeight 0)`
(using `ratio_lt_one` to cancel `1 - ratio 0 ≠ 0`) and reads pinning off
`vertex_pinned`; the reverse direction builds the constant witness
`vertex := mixTarget r λ`, `mixWeight := λ`, `ratio := 1 / 2`. -/
theorem faceCirculationCertificate_one_bool_iff (r : Finset Bool → Bool → ℝ)
    (floor : Bool → ℝ) :
    Nonempty (FaceCirculationCertificate r floor 1) ↔
      (∀ j, r {j} j ≤ floor j) ∧ CirculationL1Feasible (r {false}) (r {true}) floor := by
  constructor
  · rintro ⟨C⟩
    have heq : ∀ j, C.vertex 0 j = mixTarget r (C.mixWeight 0) j := by
      intro j
      have hstep := C.step 0 j
      rw [show (0 : ZMod 1) + 1 = 0 from zmod_one_eq_zero _] at hstep
      have hne : (1 : ℝ) - C.ratio 0 ≠ 0 := by
        have := C.ratio_lt_one 0; linarith
      have hfactor : (1 - C.ratio 0) * C.vertex 0 j =
          (1 - C.ratio 0) * mixTarget r (C.mixWeight 0) j := by linear_combination hstep
      exact mul_left_cancel₀ hne hfactor
    refine ⟨C.solo_le_floor, C.mixWeight 0, C.mixWeight_nonneg 0 false,
      C.mixWeight_nonneg 0 true, ?_, ?_, ?_, ?_⟩
    · have h2 := C.mixWeight_sum 0
      rw [Fintype.sum_bool] at h2
      linarith
    · intro j
      have hge := C.vertex_ge_floor 0 j
      rw [heq j, mixTarget_bool_eq] at hge
      exact hge
    · intro hpos
      have h1 := C.vertex_pinned 0 false hpos
      rw [heq false, mixTarget_bool_eq] at h1
      exact h1
    · intro hpos
      have h1 := C.vertex_pinned 0 true hpos
      rw [heq true, mixTarget_bool_eq] at h1
      exact h1
  · rintro ⟨hfloor, lam, hlam0, hlam1, hsum, hge, hpin0, hpin1⟩
    refine ⟨{
      vertex := fun _ j => lam false * r {false} j + lam true * r {true} j
      mixWeight := fun _ => lam
      ratio := fun _ => 1 / 2
      mixWeight_nonneg := fun _ j => match j with
        | false => hlam0
        | true => hlam1
      mixWeight_sum := fun _ => by rw [Fintype.sum_bool]; linarith
      ratio_pos := fun _ => by norm_num
      ratio_lt_one := fun _ => by norm_num
      step := fun _ j => by
        show lam false * r {false} j + lam true * r {true} j =
          (1 / 2) * (lam false * r {false} j + lam true * r {true} j) +
            (1 - 1 / 2) * mixTarget r lam j
        rw [mixTarget_bool_eq]; ring
      vertex_ge_floor := fun _ j => hge j
      vertex_pinned := fun _ j hj => match j, hj with
        | false, hj => hpin0 hj
        | true, hj => hpin1 hj
      target_pinned := fun _ j hj => by
        rw [mixTarget_bool_eq]
        match j, hj with
        | false, hj => exact hpin0 hj
        | true, hj => exact hpin1 hj
      solo_le_floor := hfloor }⟩

/-! ## The two-coordinate closed form -/

/-- **The two-coordinate characterization.** `CirculationL1Feasible` is a
two-way disjunction: a pure witness at `false` (`floor ≤ v0` everywhere,
pinning at `false` being automatic since `v0 false = v0 false`) or a pure
witness at `true` (symmetric). A mixed witness `0 < λ_false, λ_true`
forces, from the two pinning equations, `v1 false = v0 false` and
`v0 true = v1 true` — i.e. `v0 = v1` outright — at which point it already
lies in the `false`-pure disjunct. So the mixed case adds nothing beyond
the pure disjuncts, unlike the singleton-LCP two-coordinate case, whose
mixed disjunct is a genuine third alternative. -/
theorem circulationL1Feasible_bool_iff (v0 v1 floor : Bool → ℝ) :
    CirculationL1Feasible v0 v1 floor ↔
      (∀ j, floor j ≤ v0 j) ∨ (∀ j, floor j ≤ v1 j) := by
  constructor
  · rintro ⟨lam, hlam0, hlam1, hsum, hge, hpin0, hpin1⟩
    by_cases hq : lam true = 0
    · left
      have hp1 : lam false = 1 := by linarith
      intro j
      have := hge j
      rw [hp1, hq] at this
      linarith
    · have hqpos : 0 < lam true := lt_of_le_of_ne hlam1 (Ne.symm hq)
      by_cases hp : lam false = 0
      · right
        have hq1 : lam true = 1 := by linarith
        intro j
        have := hge j
        rw [hp, hq1] at this
        linarith
      · have hppos : 0 < lam false := lt_of_le_of_ne hlam0 (Ne.symm hp)
        have heq0 := hpin0 hppos
        have heq1 := hpin1 hqpos
        have hv10 : v1 false = v0 false := by
          have h1 : lam true * v1 false = lam true * v0 false := by
            linear_combination heq0 - v0 false * hsum
          exact mul_left_cancel₀ (ne_of_gt hqpos) h1
        have hv01 : v0 true = v1 true := by
          have h1 : lam false * v0 true = lam false * v1 true := by
            linear_combination heq1 - v1 true * hsum
          exact mul_left_cancel₀ (ne_of_gt hppos) h1
        left
        intro j
        cases j
        · have hthis := hge false
          rw [hv10] at hthis
          have hone : lam false * v0 false + lam true * v0 false = v0 false := by
            linear_combination v0 false * hsum
          linarith [hthis, hone]
        · have hthis := hge true
          rw [hv01] at hthis
          have hone : lam false * v1 true + lam true * v1 true = v1 true := by
            linear_combination v1 true * hsum
          linarith [hthis, hone]
  · rintro (h | h)
    · refine ⟨fun j => if j then 0 else 1, by norm_num, by norm_num, by norm_num,
        fun j => by cases j <;> simpa using h _,
        fun _ => by norm_num,
        fun hc => ?_⟩
      norm_num at hc
    · refine ⟨fun j => if j then 1 else 0, by norm_num, by norm_num, by norm_num,
        fun j => by cases j <;> simpa using h _,
        fun hc => ?_,
        fun _ => by norm_num⟩
      norm_num at hc

/-! ## The floor's achievable range -/

/-- **Validity of a floor** for the two solo rows `v0, v1`, spelled directly
as the achievable range `d_j ≤ floor j ≤ max 0 (d_j)` at each coordinate,
with `d_false = v0 false`, `d_true = v1 true`. Equivalent to the min-max
formulation (`validFloorFor_iff_exists_chi`). -/
def ValidFloorFor (v0 v1 floor : Bool → ℝ) : Prop :=
  (v0 false ≤ floor false ∧ floor false ≤ max 0 (v0 false)) ∧
    (v1 true ≤ floor true ∧ floor true ≤ max 0 (v1 true))

/-- **The min-max formulation.** `floor` is valid iff it is `max (d, χ)` for
some `χ ≤ max 0 d` at both coordinates — the reading `floor_i = max{d_i,χ_i}`
quoted from `SingletonFaceCirculation.lean`'s scope note, with `χ` the
abstract min-max parameter. -/
theorem validFloorFor_iff_exists_chi (v0 v1 floor : Bool → ℝ) :
    ValidFloorFor v0 v1 floor ↔
      ∃ chi : Bool → ℝ, chi false ≤ max 0 (v0 false) ∧ chi true ≤ max 0 (v1 true) ∧
        floor false = max (v0 false) (chi false) ∧ floor true = max (v1 true) (chi true) := by
  constructor
  · rintro ⟨⟨hlo0, hhi0⟩, ⟨hlo1, hhi1⟩⟩
    exact ⟨floor, hhi0, hhi1, (max_eq_right hlo0).symm, (max_eq_right hlo1).symm⟩
  · rintro ⟨chi, hchi0, hchi1, hf0, hf1⟩
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · rw [hf0]; exact le_max_left _ _
    · rw [hf0]; exact max_le (le_max_right _ _) hchi0
    · rw [hf1]; exact le_max_left _ _
    · rw [hf1]; exact max_le (le_max_right _ _) hchi1

/-! ## The headline two-coordinate class -/

/-- **The two-coordinate circulation class.** `v0, v1` admit an `L = 1`
circulation certificate for *some* admissible floor. -/
def CirculationTwoExists (v0 v1 : Bool → ℝ) : Prop :=
  ∃ floor, ValidFloorFor v0 v1 floor ∧ CirculationL1Feasible v0 v1 floor

/-- **The headline closed form.** Since the achievable floor range bottoms
out at `d` (always achievable, taking `χ := d`), existence for *some*
admissible floor is exactly existence at the tightest one, `floor := d`.
Combined with `circulationL1Feasible_bool_iff` at that floor, the class is a
clean two-way disjunction on the four numbers `v0 false, v0 true, v1 false,
v1 true`: one player's own solo value is dominated by the *other* player's
cross payoff. -/
theorem circulationTwoExists_iff (v0 v1 : Bool → ℝ) :
    CirculationTwoExists v0 v1 ↔ v1 true ≤ v0 true ∨ v0 false ≤ v1 false := by
  constructor
  · rintro ⟨floor, ⟨⟨hlo0, _⟩, ⟨hlo1, _⟩⟩, hfeas⟩
    rcases (circulationL1Feasible_bool_iff v0 v1 floor).mp hfeas with h | h
    · exact Or.inl (le_trans hlo1 (h true))
    · exact Or.inr (le_trans hlo0 (h false))
  · intro h
    refine ⟨fun j => if j then v1 true else v0 false, ⟨⟨le_refl _, le_max_right _ _⟩,
      ⟨le_refl _, le_max_right _ _⟩⟩, ?_⟩
    rw [circulationL1Feasible_bool_iff]
    rcases h with h | h
    · left; intro j; cases j
      · simp
      · simpa using h
    · right; intro j; cases j
      · simpa using h
      · simp

/-! ## A concrete family of two-player weights

`sampleReward v0 v1 c` is the reward with solo rows `v0 = r{false}`,
`v1 = r{true}` and a single shared value `c` for the joint coalition; it is
the vehicle for every branch counterexample below. -/

/-- The reward with solo rows `v0, v1` and joint-coalition row `c`. -/
def sampleReward (v0 v1 c : Bool → ℝ) : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun S => if S.1 = {false} then v0 else if S.1 = {true} then v1 else c

@[simp] theorem quittingSoloReward_sampleReward_false (v0 v1 c : Bool → ℝ) :
    quittingSoloReward (sampleReward v0 v1 c) false = v0 := by
  simp [quittingSoloReward, sampleReward]

@[simp] theorem quittingSoloReward_sampleReward_true (v0 v1 c : Bool → ℝ) :
    quittingSoloReward (sampleReward v0 v1 c) true = v1 := by
  have hne : ({true} : Finset Bool) ≠ {false} := by decide
  simp [quittingSoloReward, sampleReward, hne]

theorem quittingSingletonCollisionReward_sampleReward (v0 v1 c : Bool → ℝ)
    (owner other : Bool) (hne : other ≠ owner) :
    quittingSingletonCollisionReward (sampleReward v0 v1 c) owner other = c other := by
  have h1 : ({owner, other} : Finset Bool) ≠ {false} := by
    revert hne; cases owner <;> cases other <;> decide
  have h2 : ({owner, other} : Finset Bool) ≠ {true} := by
    revert hne; cases owner <;> cases other <;> decide
  unfold quittingSingletonCollisionReward
  simp [sampleReward, h1, h2]

/-! ## The pair-repair branch: outside the circulation class -/

/-- The pair-repair weight witnessing the boundary: owner's solo value `1`,
blocker's solo value `5`, cross payoffs both `0`, collision-at-owner `-1`. -/
private noncomputable def pairRepairWitness : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  sampleReward (fun j => if j then 0 else 1) (fun j => if j then 5 else 0)
    (fun j => if j then 0 else -1)

/-- **The pair-repair branch, outside the circulation class.**
`pairRepairWitness` satisfies both of `exists_uniformEquilibriumPayoff_of_bool_pairRepair`'s
hypotheses at `owner = false` — so it has a uniform-equilibrium payoff via
pair repair — yet fails `circulationTwoExists_iff` at both disjuncts: the
theorem's own `hblocker` (`v0 true ≤ v1 true`, here `0 ≤ 5`) is consistent
with, not the reverse of, what the first disjunct would need
(`v1 true ≤ v0 true`), and the second disjunct (`v0 false ≤ v1 false`,
`1 ≤ 0`) fails outright. -/
theorem pairRepair_exists_outside_circulationTwoExists :
    (∃ payoff : Payoff Bool,
      (quittingGame pairRepairWitness).IsUniformEquilibriumPayoff none payoff) ∧
    ¬ CirculationTwoExists (quittingSoloReward pairRepairWitness false)
        (quittingSoloReward pairRepairWitness true) := by
  have howner : quittingSingletonCollisionReward pairRepairWitness true false ≤
      quittingSoloReward pairRepairWitness true false := by
    unfold pairRepairWitness
    rw [quittingSingletonCollisionReward_sampleReward _ _ _ true false (by decide)]
    simp
  have hblocker : quittingSoloReward pairRepairWitness false true ≤
      quittingSoloReward pairRepairWitness true true := by
    simp [pairRepairWitness]
  refine ⟨exists_uniformEquilibriumPayoff_of_bool_pairRepair pairRepairWitness false
      howner hblocker, ?_⟩
  simp only [pairRepairWitness, quittingSoloReward_sampleReward_false,
    quittingSoloReward_sampleReward_true]
  rw [circulationTwoExists_iff]
  norm_num

/-! ## The other three branches, likewise outside -/

/-- The solo-quitter weight: owner's solo value `2`, blocker's solo value
`1`, cross payoff `0`, collision-at-blocker `-10` (making the rate `p = 1`
keep the blocker out). -/
private noncomputable def soloRateWitness : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  sampleReward (fun j => if j then 0 else 2) (fun j => if j then 1 else 0)
    (fun j => if j then -10 else 0)

/-- **The solo-quitter branch, outside the circulation class.** At
`owner = false`, `p = 1` witnesses the rate hypothesis of
`quittingGame_isUniformEquilibriumPayoff_soloRate`, so `soloRateWitness` has
a uniform-equilibrium payoff (the owner's own solo row) — yet fails
`circulationTwoExists_iff`. The rate mechanism can certify a *deviating*
blocker is deterred by an unattractive collision term, without the
blocker's assigned payoff ever reaching its own solo value; that gap is
exactly what the circulation floor forbids. -/
theorem soloRate_exists_outside_circulationTwoExists :
    (∃ payoff : Payoff Bool,
      (quittingGame soloRateWitness).IsUniformEquilibriumPayoff none payoff) ∧
    ¬ CirculationTwoExists (quittingSoloReward soloRateWitness false)
        (quittingSoloReward soloRateWitness true) := by
  have hsolo : 0 ≤ quittingSoloReward soloRateWitness false false := by
    simp [soloRateWitness]
  have hrate : (1 - (1:ℝ)) * quittingSoloReward soloRateWitness true true +
      1 * quittingSingletonCollisionReward soloRateWitness false true ≤
      quittingSoloReward soloRateWitness false true := by
    unfold soloRateWitness
    rw [quittingSingletonCollisionReward_sampleReward _ _ _ false true (by decide)]
    simp
  refine ⟨⟨_, quittingGame_isUniformEquilibriumPayoff_soloRate soloRateWitness false
      hsolo one_pos le_rfl hrate⟩, ?_⟩
  simp only [soloRateWitness, quittingSoloReward_sampleReward_false,
    quittingSoloReward_sampleReward_true]
  rw [circulationTwoExists_iff]
  norm_num

/-- The joint-exit weight: owner's solo value `1`, blocker's solo value `1`,
cross payoffs both `-5`, collision both `10`. -/
private noncomputable def jointExitWitness : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  sampleReward (fun j => if j then -5 else 1) (fun j => if j then 1 else -5)
    (fun _ => 10)

/-- **The joint-exit branch, outside the circulation class.**
`jointExitWitness` satisfies `quittingGame_isUniformEquilibriumPayoff_jointExit`'s
two hypotheses at `owner = false` (neither player prefers the other's solo
exit to the joint exit, since the collision value `10` dominates both cross
payoffs `-5`), giving a uniform-equilibrium payoff — the joint-coalition row,
which is not even of the mixed-solo-row form `CirculationL1Feasible`
targets. It also fails `circulationTwoExists_iff` outright. -/
theorem jointExit_exists_outside_circulationTwoExists :
    (∃ payoff : Payoff Bool,
      (quittingGame jointExitWitness).IsUniformEquilibriumPayoff none payoff) ∧
    ¬ CirculationTwoExists (quittingSoloReward jointExitWitness false)
        (quittingSoloReward jointExitWitness true) := by
  have howner : quittingSoloReward jointExitWitness true false ≤
      quittingSingletonCollisionReward jointExitWitness true false := by
    unfold jointExitWitness
    rw [quittingSingletonCollisionReward_sampleReward _ _ _ true false (by decide)]
    norm_num
  have hblocker : quittingSoloReward jointExitWitness false true ≤
      quittingSingletonCollisionReward jointExitWitness false true := by
    unfold jointExitWitness
    rw [quittingSingletonCollisionReward_sampleReward _ _ _ false true (by decide)]
    norm_num
  refine ⟨⟨_, quittingGame_isUniformEquilibriumPayoff_jointExit jointExitWitness false
      howner hblocker⟩, ?_⟩
  simp only [jointExitWitness, quittingSoloReward_sampleReward_false,
    quittingSoloReward_sampleReward_true]
  rw [circulationTwoExists_iff]
  norm_num

/-- The zero-solo weight: both solo values `0`, both cross payoffs `-5`. -/
private noncomputable def zeroSoloWitness : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  sampleReward (fun j => if j then -5 else 0) (fun j => if j then 0 else -5) (fun _ => 0)

/-- **The zero-solo branch, outside the circulation class.**
`zeroSoloWitness` is zero-solo (`IsQuittingZeroSolo`), giving the all-continue
equilibrium payoff `0` — not of the mixed-solo-row form either — and it also
fails `circulationTwoExists_iff` outright. -/
theorem zeroSolo_exists_outside_circulationTwoExists :
    (∃ payoff : Payoff Bool,
      (quittingGame zeroSoloWitness).IsUniformEquilibriumPayoff none payoff) ∧
    ¬ CirculationTwoExists (quittingSoloReward zeroSoloWitness false)
        (quittingSoloReward zeroSoloWitness true) := by
  have hzero : IsQuittingZeroSolo zeroSoloWitness := by
    intro who
    cases who <;> simp [zeroSoloWitness, quittingSingletonTerminal, sampleReward]
  refine ⟨exists_uniformEquilibriumPayoff_of_zeroSolo zeroSoloWitness hzero, ?_⟩
  simp only [zeroSoloWitness, quittingSoloReward_sampleReward_false,
    quittingSoloReward_sampleReward_true]
  rw [circulationTwoExists_iff]
  norm_num

end QuittingCirculationTwoCoordinateBoundary

end GameTheory
