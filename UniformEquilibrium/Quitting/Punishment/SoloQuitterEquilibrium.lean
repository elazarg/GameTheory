/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Punishment.OwnerSoloCertification
import UniformEquilibrium.Quitting.Boundary.Repair.BoundedSurgeryDescentCounterexample
import UniformEquilibrium.Quitting.Debt.Dynamic.PositiveDebtPlateauTable

/-!
# The solo-quitter row is an absorbing stationary equilibrium row

Fix a coordinate `owner` and let `y` be the stationary row at which `owner`
quits with probability `p` and every other coordinate continues surely --
the repository's `quittingSoloStationaryRoot owner hazard`.  Pair it with the
value vector

`z = quittingSoloReward reward owner`, that is `z who = r_who({owner})`,

so that `z owner = r_owner({owner})` and `z other = r_other({owner})`.

This file proves the four row-level facts about that pair:

* `quittingRootSuccessorPayoff_soloStationaryRoot_self` -- `y` run against
  `z` reproduces `z` exactly, at *every* `p ∈ [0,1]`;
* `quittingRootEndpointDifference_soloStationaryRoot_owner` -- the owner is
  exactly indifferent, at every `p`;
* `isεQuittingRootEndpointNash_soloStationaryRoot` -- every other coordinate
  weakly prefers continuing exactly when
  `(1-p) * r_other({other}) + p * r_other({owner, other}) ≤ r_other({owner})`,
  so the pair is an exact (`ε = 0`) endpoint-Nash root;
* `quittingStationaryContinueMass_soloStationaryRoot_lt_one` -- the row
  absorbs, its all-continue mass being `1 - p < 1`, and this is the *only*
  place `p > 0` is used.

## Relation to the existing owner-solo certification

`isεAsymptoticNash_soloStationary_exact` in
`QuittingOwnerSoloCertification.lean` already proves, from the *same* scalar
criterion, the strictly stronger behavioral statement that the stationary
*profile* built from this row is an exact terminal Nash equilibrium of the
quitting game -- but it needs the extra hypothesis
`0 ≤ quittingSoloReward reward owner owner`, because in the behavioral game
the owner may deviate to never quitting and collect `0`.  The row-level
certificates below do not see that deviation (the continuation is pinned to
`z`), so they hold without any sign hypothesis on `r_owner({owner})`.  They
are the certificates the Nash--Bellman chain machinery consumes, and the
form in which the two landed plateau tables state their equilibrium rows.

## Why absorption must be stated separately

The all-continue row satisfies `F_y(z) = z` for *every* `z`
(`quittingRootSuccessorPayoff_allContinueRoot_eq`) and is endpoint-Nash
against every tail dominating the singleton rewards.  A "reproduces its own
value and is endpoint-Nash" certificate is therefore vacuous on its own: it
is satisfied by the row that never absorbs, whose declared value is pure
fiction.  `quittingStationaryContinueMass_soloStationaryRoot_lt_one` is the
non-degeneracy guard that rules this out, and it is exactly where the
hypothesis `0 < p` enters.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Marginals of a solo-quitter row -/

/-- The owner's and the complementary mass of a Boolean hazard sum to one. -/
theorem quittingSoloHazardMass_add (hazard : PMF Bool) :
    (hazard false).toReal + (hazard true).toReal = 1 := by
  simpa [Fintype.sum_bool, add_comm] using pmf_toReal_sum_one hazard

omit [Fintype ι] in
/-- The owner's marginal at its own solo row is the supplied hazard. -/
@[simp] theorem quittingSoloStationaryRoot_apply_owner
    (owner : ι) (hazard : PMF Bool) :
    quittingSoloStationaryRoot owner hazard owner = hazard := by
  simp [quittingSoloStationaryRoot]

omit [Fintype ι] in
/-- Every coordinate other than the owner continues surely at a solo row. -/
theorem quittingSoloStationaryRoot_apply_other
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool) :
    quittingSoloStationaryRoot owner hazard other = PMF.pure false := by
  simp [quittingSoloStationaryRoot, hne]

omit [Fintype ι] in
/-- A row at which every coordinate other than `owner` continues surely *is*
the solo stationary row carrying the owner's own marginal.  This is the
recognizer used to specialize the certificates below to concrete tables. -/
theorem eq_quittingSoloStationaryRoot_of_others_continue
    {root : ι → PMF Bool} {owner : ι}
    (hother : ∀ other, other ≠ owner → root other = PMF.pure false) :
    root = quittingSoloStationaryRoot owner (root owner) := by
  funext player
  by_cases hp : player = owner
  · subst player
    simp [quittingSoloStationaryRoot]
  · rw [hother player hp]
    simp [quittingSoloStationaryRoot, hp]

/-! ## Exact endpoint formulas at a solo-quitter row -/

/-- The owner's pure-Quit endpoint at its own solo row is its singleton
reward, whatever the declared continuation. -/
theorem quittingRootQuitPayoff_soloStationaryRoot_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) (tail : Payoff ι) :
    quittingRootQuitPayoff reward tail
        (quittingSoloStationaryRoot owner hazard) owner =
      quittingSoloReward reward owner owner := by
  have h := congrFun
    (quittingRootSuccessorPayoff_solo reward owner (PMF.pure true) tail) owner
  unfold quittingRootQuitPayoff
  rw [update_quittingSoloStationaryRoot_owner]
  simpa [quittingRootSuccessorPayoff] using h

/-- The owner's pure-Continue endpoint at its own solo row is the declared
continuation, because no opponent can absorb. -/
theorem quittingRootContinuePayoff_soloStationaryRoot_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) (tail : Payoff ι) :
    quittingRootContinuePayoff reward tail
        (quittingSoloStationaryRoot owner hazard) owner = tail owner := by
  have h := congrFun
    (quittingRootSuccessorPayoff_solo reward owner (PMF.pure false) tail) owner
  unfold quittingRootContinuePayoff
  rw [update_quittingSoloStationaryRoot_owner]
  simpa [quittingRootSuccessorPayoff] using h

/-- An inactive coordinate's pure-Quit endpoint at a solo row mixes quitting
alone with colliding with the owner, and does not depend on the declared
continuation. -/
theorem quittingRootQuitPayoff_soloStationaryRoot_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool)
    (tail : Payoff ι) :
    quittingRootQuitPayoff reward tail
        (quittingSoloStationaryRoot owner hazard) other =
      (hazard false).toReal * quittingSoloReward reward other other +
        (hazard true).toReal *
          quittingSingletonCollisionReward reward owner other := by
  have h := quittingRootQuitPayoff_eq_fixedOpponentsQuitValue reward
    (fun _ => quittingSoloStationaryRoot owner hazard) other tail 0
  rw [h]
  exact quittingStationaryFixedOpponentsQuitValue_solo_other_eq_mix
    reward hne hazard

/-- An inactive coordinate's pure-Continue endpoint at a solo row is the
row's own successor value there: the coordinate already continues surely. -/
theorem quittingRootContinuePayoff_soloStationaryRoot_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool)
    (tail : Payoff ι) :
    quittingRootContinuePayoff reward tail
        (quittingSoloStationaryRoot owner hazard) other =
      (hazard true).toReal * quittingSoloReward reward owner other +
        (hazard false).toReal * tail other := by
  have h := congrFun
    (quittingRootSuccessorPayoff_solo reward owner hazard tail) other
  unfold quittingRootContinuePayoff
  rw [update_quittingSoloStationaryRoot_other hne]
  simpa [quittingRootSuccessorPayoff] using h

/-! ## The value recursion -/

/-- **The solo-quitter row reproduces its own value.**  Running the one-stage
value map at the solo row against the continuation
`z = quittingSoloReward reward owner` returns `z` exactly.

Note this holds at *every* hazard, including the zero hazard: it is the
all-continue row's degenerate fixed point that makes this identity alone
worthless as a certificate.  Positivity of the hazard is what makes `z` the
*unique* fixed point, and it is supplied separately by
`quittingStationaryContinueMass_soloStationaryRoot_lt_one`. -/
theorem quittingRootSuccessorPayoff_soloStationaryRoot_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) :
    quittingRootSuccessorPayoff reward (quittingSoloReward reward owner)
        (quittingSoloStationaryRoot owner hazard) =
      quittingSoloReward reward owner := by
  rw [quittingRootSuccessorPayoff_solo]
  funext who
  have hsum := quittingSoloHazardMass_add hazard
  have hfalse : (hazard false).toReal = 1 - (hazard true).toReal := by linarith
  rw [hfalse]
  ring

/-! ## The endpoint differences -/

/-- **The owner is exactly indifferent.**  Against its own solo value the
owner's pure-Quit and pure-Continue endpoints coincide, at every hazard. -/
theorem quittingRootEndpointDifference_soloStationaryRoot_owner
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) :
    quittingRootEndpointDifference reward (quittingSoloReward reward owner)
        (quittingSoloStationaryRoot owner hazard) owner = 0 := by
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_soloStationaryRoot_owner,
    quittingRootContinuePayoff_soloStationaryRoot_owner]
  exact sub_self _

/-- An inactive coordinate's endpoint difference against the owner's solo
value is exactly the joining surplus tested by the criterion. -/
theorem quittingRootEndpointDifference_soloStationaryRoot_other
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner other : ι} (hne : other ≠ owner) (hazard : PMF Bool) :
    quittingRootEndpointDifference reward (quittingSoloReward reward owner)
        (quittingSoloStationaryRoot owner hazard) other =
      ((hazard false).toReal * quittingSoloReward reward other other +
          (hazard true).toReal *
            quittingSingletonCollisionReward reward owner other) -
        quittingSoloReward reward owner other := by
  have hsum := quittingSoloHazardMass_add hazard
  rw [quittingRootEndpointDifference,
    quittingRootQuitPayoff_soloStationaryRoot_other reward hne,
    quittingRootContinuePayoff_soloStationaryRoot_other reward hne]
  have hfalse : (hazard false).toReal = 1 - (hazard true).toReal := by linarith
  rw [hfalse]
  ring

/-! ## The joining criterion -/

/-- **The joining criterion at rate `p`.**  No opponent of `owner` strictly
prefers to join the exit: quitting -- alone with probability `1 - p`, or
together with `owner` with probability `p` -- is no better than letting
`owner` quit alone. -/
def QuittingSoloQuitterCriterion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) : Prop :=
  ∀ other, other ≠ owner →
    (1 - p) * quittingSoloReward reward other other +
      p * quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other

omit [Fintype ι] in
/-- The criterion is precisely the failure of the joining obstruction of
`QuittingOwnerSoloCertification.lean`. -/
theorem quittingSoloQuitterCriterion_iff_not_joiningObstruction
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) :
    QuittingSoloQuitterCriterion reward owner p ↔
      ¬ QuittingSoloJoiningObstruction reward owner p := by
  unfold QuittingSoloQuitterCriterion QuittingSoloJoiningObstruction
  constructor
  · rintro h ⟨other, hother, hlt⟩
    exact absurd (h other hother) (not_le.mpr hlt)
  · intro h other hother
    by_contra hcontra
    exact h ⟨other, hother, not_le.mp hcontra⟩

omit [Fintype ι] in
/-- **The criterion is one-dimensional and affine in `p`.**  Opponent by
opponent it reads `p * (collision - solo) ≤ ownerSolo - solo`, a half-line
in `p`. -/
theorem quittingSoloQuitterCriterion_iff_affine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (p : ℝ) :
    QuittingSoloQuitterCriterion reward owner p ↔
      ∀ other, other ≠ owner →
        p * (quittingSingletonCollisionReward reward owner other -
            quittingSoloReward reward other other) ≤
          quittingSoloReward reward owner other -
            quittingSoloReward reward other other := by
  constructor
  · intro h other hother
    have hlocal := h other hother
    nlinarith [hlocal]
  · intro h other hother
    have hlocal := h other hother
    nlinarith [hlocal]

omit [Fintype ι] in
/-- Consequently the feasible rate set is an interval: it is an intersection
of half-lines, hence convex.  Feasibility on `(0,1]` is therefore the
question of whether finitely many intervals meet `(0,1]`. -/
theorem convex_quittingSoloQuitterCriterion
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    Convex ℝ {p : ℝ | QuittingSoloQuitterCriterion reward owner p} := by
  intro first hfirst second hsecond a b ha hb hab
  simp only [Set.mem_setOf_eq, QuittingSoloQuitterCriterion,
    smul_eq_mul] at hfirst hsecond ⊢
  intro other hother
  have h1 := hfirst other hother
  have h2 := hsecond other hother
  have hb' : b = 1 - a := by linarith
  have hsplit :
      (1 - (a * first + b * second)) * quittingSoloReward reward other other +
          (a * first + b * second) *
            quittingSingletonCollisionReward reward owner other =
        a * ((1 - first) * quittingSoloReward reward other other +
            first * quittingSingletonCollisionReward reward owner other) +
          b * ((1 - second) * quittingSoloReward reward other other +
            second * quittingSingletonCollisionReward reward owner other) := by
    rw [hb']
    ring
  have htotal :
      a * quittingSoloReward reward owner other +
          b * quittingSoloReward reward owner other =
        quittingSoloReward reward owner other := by
    rw [hb']
    ring
  rw [hsplit]
  linarith [mul_le_mul_of_nonneg_left h1 ha,
    mul_le_mul_of_nonneg_left h2 hb, htotal]

/-! ## The equilibrium row -/

/-- **Solo-quitter endpoint-Nash certificate.**  If no opponent strictly
prefers joining, the solo row of `owner` is an exact (`ε = 0`) endpoint-Nash
root against the value vector `quittingSoloReward reward owner`.

The owner's half is unconditional (it is exactly indifferent); the criterion
is used only at the inactive coordinates.  No sign hypothesis on
`r_owner({owner})` and no positivity of the hazard are needed here -- see the
module docstring for why absorption is nevertheless indispensable. -/
theorem isεQuittingRootEndpointNash_soloStationaryRoot
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (hinactive : ∀ other, other ≠ owner →
      (hazard false).toReal * quittingSoloReward reward other other +
        (hazard true).toReal *
          quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other) :
    IsεQuittingRootEndpointNash reward (quittingSoloReward reward owner) 0
      (quittingSoloStationaryRoot owner hazard) := by
  intro who
  by_cases hwho : who = owner
  · subst who
    rw [quittingRootEndpointDifference_soloStationaryRoot_owner]
    constructor
    · simp
    · simp
  · have hlocal := hinactive who hwho
    have hcontinueMass :
        (quittingSoloStationaryRoot owner hazard who false).toReal = 1 := by
      rw [quittingSoloStationaryRoot_apply_other hwho]
      simp
    have hquitMass :
        (quittingSoloStationaryRoot owner hazard who true).toReal = 0 := by
      rw [quittingSoloStationaryRoot_apply_other hwho]
      simp
    rw [quittingRootEndpointDifference_soloStationaryRoot_other reward hwho]
    refine ⟨?_, ?_⟩
    · rw [hcontinueMass, one_mul]
      linarith
    · rw [hquitMass, zero_mul]
      norm_num

/-- **The criterion is exactly right.**  At the solo row, exact endpoint Nash
against the owner's own solo value is *equivalent* to the inactive
inequality at every opponent: the hypothesis of
`isεQuittingRootEndpointNash_soloStationaryRoot` can be neither weakened nor
strengthened. -/
theorem isεQuittingRootEndpointNash_soloStationaryRoot_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool) :
    IsεQuittingRootEndpointNash reward (quittingSoloReward reward owner) 0
        (quittingSoloStationaryRoot owner hazard) ↔
      ∀ other, other ≠ owner →
        (hazard false).toReal * quittingSoloReward reward other other +
          (hazard true).toReal *
            quittingSingletonCollisionReward reward owner other ≤
          quittingSoloReward reward owner other := by
  refine ⟨fun hnash other hother ↦ ?_,
    isεQuittingRootEndpointNash_soloStationaryRoot reward owner hazard⟩
  have hcontinueMass :
      (quittingSoloStationaryRoot owner hazard other false).toReal = 1 := by
    rw [quittingSoloStationaryRoot_apply_other hother]
    simp
  have hendpoint := (hnash other).1
  rw [quittingRootEndpointDifference_soloStationaryRoot_other reward hother,
    hcontinueMass, one_mul] at hendpoint
  linarith

/-- **Absorption at the solo-quitter row.**  The all-continue mass is
`1 - p < 1` exactly when the owner's rate `p` is positive.

This lemma is not decoration.  The all-continue row reproduces *every* value
vector and is endpoint-Nash against every tail dominating the singleton
rewards, so "reproduces its own value and is endpoint-Nash" certifies
nothing by itself; the declared value only becomes a genuine expected
terminal payoff once play is absorbed with probability one. -/
theorem quittingStationaryContinueMass_soloStationaryRoot_lt_one
    (owner : ι) (hazard : PMF Bool) (hpositive : 0 < (hazard true).toReal) :
    quittingStationaryContinueMass
      (quittingSoloStationaryRoot owner hazard) < 1 := by
  have hsum := quittingSoloHazardMass_add hazard
  rw [quittingStationaryContinueMass_solo]
  linarith

/-- The solo row's one-stage absorption probability is the owner's rate. -/
@[simp] theorem quittingRootAbsorptionMass_soloStationaryRoot
    (owner : ι) (hazard : PMF Bool) :
    quittingRootAbsorptionMass (quittingSoloStationaryRoot owner hazard) =
      (hazard true).toReal := by
  have hsum := quittingSoloHazardMass_add hazard
  unfold quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_solo]
  linarith

/-- **The solo-quitter row is an absorbing stationary equilibrium row.**
If the owner's rate is positive and no opponent strictly prefers joining,
then the solo row together with the value vector
`z = quittingSoloReward reward owner` is an exact root successor
certificate -- `z` is the row's own successor value and the row is exact
endpoint-Nash against it -- the owner is exactly indifferent, the row
absorbs at rate `(hazard true).toReal`, and the all-continue mass is
strictly below one. -/
theorem soloStationaryRoot_isAbsorbingEquilibriumRow
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) (hazard : PMF Bool)
    (hpositive : 0 < (hazard true).toReal)
    (hinactive : ∀ other, other ≠ owner →
      (hazard false).toReal * quittingSoloReward reward other other +
        (hazard true).toReal *
          quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other) :
    IsεQuittingRootSuccessorCertificate reward 0
        (quittingSoloStationaryRoot owner hazard)
        (quittingSoloReward reward owner)
        (quittingSoloReward reward owner) ∧
      quittingRootEndpointDifference reward
          (quittingSoloReward reward owner)
          (quittingSoloStationaryRoot owner hazard) owner = 0 ∧
      quittingRootAbsorptionMass (quittingSoloStationaryRoot owner hazard) =
        (hazard true).toReal ∧
      quittingStationaryContinueMass
        (quittingSoloStationaryRoot owner hazard) < 1 := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact (quittingRootSuccessorPayoff_soloStationaryRoot_self
      reward owner hazard).symm
  · exact isεQuittingRootEndpointNash_soloStationaryRoot
      reward owner hazard hinactive
  · exact quittingRootEndpointDifference_soloStationaryRoot_owner
      reward owner hazard
  · exact quittingRootAbsorptionMass_soloStationaryRoot owner hazard
  · exact quittingStationaryContinueMass_soloStationaryRoot_lt_one
      owner hazard hpositive

/-- **Rate form.**  Every rate `p ∈ (0,1]` satisfying the joining criterion
produces an absorbing solo-quitter equilibrium row whose all-continue mass
is exactly `1 - p`. -/
theorem soloStationaryRoot_isAbsorbingEquilibriumRow_of_rate
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hcriterion : QuittingSoloQuitterCriterion reward owner p) :
    IsεQuittingRootSuccessorCertificate reward 0
        (quittingSoloStationaryRoot owner
          (quittingHazardCoin p hp0.le hp1))
        (quittingSoloReward reward owner)
        (quittingSoloReward reward owner) ∧
      quittingRootEndpointDifference reward
          (quittingSoloReward reward owner)
          (quittingSoloStationaryRoot owner
            (quittingHazardCoin p hp0.le hp1)) owner = 0 ∧
      quittingRootAbsorptionMass (quittingSoloStationaryRoot owner
          (quittingHazardCoin p hp0.le hp1)) = p ∧
      quittingStationaryContinueMass (quittingSoloStationaryRoot owner
          (quittingHazardCoin p hp0.le hp1)) = 1 - p ∧
      quittingStationaryContinueMass (quittingSoloStationaryRoot owner
          (quittingHazardCoin p hp0.le hp1)) < 1 := by
  have hpositive : 0 < (quittingHazardCoin p hp0.le hp1 true).toReal := by
    rw [quittingHazardCoin_true_toReal]
    exact hp0
  have hinactive : ∀ other, other ≠ owner →
      (quittingHazardCoin p hp0.le hp1 false).toReal *
          quittingSoloReward reward other other +
        (quittingHazardCoin p hp0.le hp1 true).toReal *
          quittingSingletonCollisionReward reward owner other ≤
        quittingSoloReward reward owner other := by
    intro other hother
    rw [quittingHazardCoin_true_toReal, quittingHazardCoin_false_toReal]
    exact hcriterion other hother
  obtain ⟨hcertificate, howner, habsorb, hmass⟩ :=
    soloStationaryRoot_isAbsorbingEquilibriumRow reward owner _
      hpositive hinactive
  refine ⟨hcertificate, howner, ?_, ?_, hmass⟩
  · rw [habsorb, quittingHazardCoin_true_toReal]
  · rw [quittingStationaryContinueMass_solo, quittingHazardCoin_false_toReal]

omit [Fintype ι] in
/-- Restated with the feasibility question in front: either some rate in
`(0,1]` certifies the owner's solo row, or every rate has a strict joining
obstruction.  The feasible side is exactly the hypothesis of
`soloStationaryRoot_isAbsorbingEquilibriumRow_of_rate`. -/
theorem exists_soloQuitterRate_or_universalJoining
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (owner : ι) :
    (∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧
        QuittingSoloQuitterCriterion reward owner p) ∨
      ∀ p : ℝ, 0 < p → p ≤ 1 →
        QuittingSoloJoiningObstruction reward owner p :=
  soloCertification_or_universalJoining reward owner

/-! ## Faithfulness: the bounded-surgery plateau table -/

section BoundedSurgeryTable

open QuittingBoundedSurgeryDescentCounterexample

/-- Player one's solo value vector in the bounded-surgery table is `(a, 0)`,
the very continuation that table's stationary row is stated against. -/
theorem boundedSurgery_quittingSoloReward (a : ℝ) :
    quittingSoloReward (reward a) false =
      fun who => if who then (0 : ℝ) else a := by
  funext who
  cases who <;> simp [quittingSoloReward, reward]

/-- The bounded-surgery table's stationary row is player one's solo row. -/
theorem boundedSurgery_stationaryRoot_eq (a : ℝ) :
    stationaryRoot a =
      quittingSoloStationaryRoot false (stationaryRoot a false) := by
  refine eq_quittingSoloStationaryRoot_of_others_continue ?_
  intro other hother
  cases other
  · exact absurd rfl hother
  · rfl

/-- The bounded-surgery table satisfies the joining criterion at `p = 1/2`,
with equality: `1/2` is exactly the right endpoint of the feasible
interval. -/
theorem boundedSurgery_inactive (a : ℝ) :
    ∀ other, other ≠ false →
      (stationaryRoot a false false).toReal *
          quittingSoloReward (reward a) other other +
        (stationaryRoot a false true).toReal *
          quittingSingletonCollisionReward (reward a) false other ≤
        quittingSoloReward (reward a) false other := by
  intro other hother
  cases other
  · exact absurd rfl hother
  · rw [stationaryRoot_false_true, stationaryRoot_false_false]
    norm_num [quittingSoloReward, quittingSingletonCollisionReward, reward]

/-- **Faithfulness test.**  The general certificate reproduces the landed
`QuittingBoundedSurgeryDescentCounterexample.stationaryRoot_isEndpointNash`
verbatim. -/
theorem boundedSurgery_stationaryRoot_isEndpointNash (a : ℝ) :
    IsεQuittingRootEndpointNash (reward a)
      (fun who => if who then (0 : ℝ) else a) 0 (stationaryRoot a) := by
  rw [← boundedSurgery_quittingSoloReward a, boundedSurgery_stationaryRoot_eq a]
  exact isεQuittingRootEndpointNash_soloStationaryRoot (reward a) false _
    (boundedSurgery_inactive a)

/-- **Faithfulness test.**  The general fixed-point law reproduces the landed
`QuittingBoundedSurgeryDescentCounterexample.stationaryRoot_successor_eq`. -/
theorem boundedSurgery_stationaryRoot_successor_eq (a : ℝ) :
    quittingRootSuccessorPayoff (reward a)
        (fun who => if who then (0 : ℝ) else a) (stationaryRoot a) =
      fun who => if who then (0 : ℝ) else a := by
  rw [← boundedSurgery_quittingSoloReward a, boundedSurgery_stationaryRoot_eq a]
  exact quittingRootSuccessorPayoff_soloStationaryRoot_self (reward a) false _

/-- The bounded-surgery stationary row absorbs at rate `1/2`, so its declared
value `(a, 0)` is a genuine expected terminal payoff and not the vacuous
all-continue fixed point. -/
theorem boundedSurgery_stationaryRoot_absorptionMass (a : ℝ) :
    quittingRootAbsorptionMass (stationaryRoot a) = 1 / 2 := by
  rw [boundedSurgery_stationaryRoot_eq a,
    quittingRootAbsorptionMass_soloStationaryRoot,
    stationaryRoot_false_true]

/-- The reproduced statement is literally the landed one: this `rfl`
type-checks only because the two theorems have definitionally equal
statements. -/
example (a : ℝ) :
    boundedSurgery_stationaryRoot_isEndpointNash a =
      QuittingBoundedSurgeryDescentCounterexample.stationaryRoot_isEndpointNash
        a := rfl

end BoundedSurgeryTable

/-! ## Faithfulness: the `1/8` positive-debt plateau table -/

section PlateauTable

open QuittingPositiveDebtPlateauTable

/-- Player one's solo value vector in the `1/8` plateau table is `(1/4, 0)`,
which is exactly that table's `stationaryValue`. -/
theorem plateau_quittingSoloReward :
    quittingSoloReward reward false = stationaryValue := by
  funext who
  cases who <;> simp [quittingSoloReward, reward, stationaryValue]

/-- The `1/8` plateau table's stationary row is player one's solo row. -/
theorem plateau_stationaryRoot_eq :
    stationaryRoot = quittingSoloStationaryRoot false (stationaryRoot false) := by
  refine eq_quittingSoloStationaryRoot_of_others_continue ?_
  intro other hother
  cases other
  · exact absurd rfl hother
  · rfl

/-- The `1/8` plateau table satisfies the joining criterion at `p = 1/2`,
again with equality at the right endpoint of the feasible interval. -/
theorem plateau_inactive :
    ∀ other, other ≠ false →
      (stationaryRoot false false).toReal *
          quittingSoloReward reward other other +
        (stationaryRoot false true).toReal *
          quittingSingletonCollisionReward reward false other ≤
        quittingSoloReward reward false other := by
  intro other hother
  cases other
  · exact absurd rfl hother
  · rw [stationaryRoot_false_true, stationaryRoot_false_false]
    norm_num [quittingSoloReward, quittingSingletonCollisionReward, reward]

/-- **Faithfulness test.**  The general certificate reproduces the landed
`QuittingPositiveDebtPlateauTable.stationaryRoot_isEndpointNash` verbatim. -/
theorem plateau_stationaryRoot_isEndpointNash :
    IsεQuittingRootEndpointNash reward stationaryValue 0 stationaryRoot := by
  rw [← plateau_quittingSoloReward, plateau_stationaryRoot_eq]
  exact isεQuittingRootEndpointNash_soloStationaryRoot reward false _
    plateau_inactive

/-- **Faithfulness test.**  The general fixed-point law reproduces the landed
`QuittingPositiveDebtPlateauTable.stationaryRoot_successor_eq`. -/
theorem plateau_stationaryRoot_successor_eq :
    quittingRootSuccessorPayoff reward stationaryValue stationaryRoot =
      stationaryValue := by
  rw [← plateau_quittingSoloReward, plateau_stationaryRoot_eq]
  exact quittingRootSuccessorPayoff_soloStationaryRoot_self reward false _

/-- **Faithfulness test.**  The general absorption law reproduces the landed
`QuittingPositiveDebtPlateauTable.stationaryRoot_absorptionMass`. -/
theorem plateau_stationaryRoot_absorptionMass :
    quittingRootAbsorptionMass stationaryRoot = 1 / 2 := by
  rw [plateau_stationaryRoot_eq, quittingRootAbsorptionMass_soloStationaryRoot,
    stationaryRoot_false_true]

/-- The reproduced statements are literally the landed ones: these `rfl`s
type-check only because the corresponding theorems have definitionally equal
statements. -/
example :
    plateau_stationaryRoot_isEndpointNash =
      QuittingPositiveDebtPlateauTable.stationaryRoot_isEndpointNash := rfl

/-- Same check for the successor law. -/
example :
    plateau_stationaryRoot_successor_eq =
      QuittingPositiveDebtPlateauTable.stationaryRoot_successor_eq := rfl

/-- Same check for the absorption mass. -/
example :
    plateau_stationaryRoot_absorptionMass =
      QuittingPositiveDebtPlateauTable.stationaryRoot_absorptionMass := rfl

end PlateauTable

end GameTheory
