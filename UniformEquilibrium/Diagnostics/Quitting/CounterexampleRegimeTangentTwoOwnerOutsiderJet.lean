/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerEdgeGateCollapse

/-!
# The exact quadratic outsider jet on a two-owner packet ray

Once the auxiliary floor and box gates are separated from exact-edge
existence, the only local obstruction left on a compatible two-owner packet
is a singleton-tight inactive owner.  That obstruction is not an arbitrary
nonlinear condition.  Along a literal two-owner hazard ray, the inactive
owner's forced-Quit payoff samples only four coalitions: its singleton, the
two pairs obtained by joining either owner, and the triple obtained by joining
both.  Consequently the outsider regression is exactly quadratic in the ray
scale.

This file exposes the constant, linear, and quadratic coefficients.  At a
tight singleton row the constant vanishes, so the eventual sign is decided
lexicographically by the linear coefficient and then the quadratic
coefficient.  A positive jet is the finite support-entry pivot which remains
after exact-edge gate collapse.
-/

noncomputable section

namespace GameTheory

open Finset Filter Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- The terminal coalition in which an inactive receiver and both declared
owners quit. -/
def quittingTripleJoinTerminal (who first second : ι) :
    {S : Finset ι // S.Nonempty} :=
  ⟨{who, first, second}, by simp⟩

/-- For an owner outside the declared pair, forcing Quit against a two-owner
hazard row samples exactly the singleton, two pair, and one triple rewards. -/
theorem sigmaValue_twoOwner_outside
    (first second who : ι) (firstHazard secondHazard : ℝ)
    (hne : first ≠ second)
    (hwhoFirst : who ≠ first) (hwhoSecond : who ≠ second) :
    sigmaValue (weightOfReward reward)
        (quittingTwoOwnerHazard first second firstHazard secondHazard) who =
      (1 - firstHazard) * (1 - secondHazard) *
          reward (quittingSingletonTerminal who) who +
        firstHazard * (1 - secondHazard) *
          reward (quittingPairJoinTerminal who first) who +
        (1 - firstHazard) * secondHazard *
          reward (quittingPairJoinTerminal who second) who +
        firstHazard * secondHazard *
          reward (quittingTripleJoinTerminal who first second) who := by
  let opponents := Finset.univ.erase who
  let support : Finset ι := {first, second}
  let x := quittingTwoOwnerHazard first second firstHazard secondHazard
  let term : Finset ι → ℝ := fun J =>
    (∏ owner ∈ J, x owner) *
      (∏ owner ∈ opponents \ J, (1 - x owner)) *
        weightOfReward reward (insert who J) who
  have hsupportSubset : support ⊆ opponents := by
    intro owner howner
    simp only [support, Finset.mem_insert, Finset.mem_singleton] at howner
    rcases howner with rfl | rfl
    · simp [opponents, hwhoFirst.symm]
    · simp [opponents, hwhoSecond.symm]
  have hdiffFirst : support \ {first} = {second} := by
    ext owner
    simp only [support, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨howner, hnotFirst⟩
      exact howner.resolve_left hnotFirst
    · intro hsecond
      refine ⟨Or.inr hsecond, ?_⟩
      intro hfirst
      exact hne (hfirst.symm.trans hsecond)
  have hdiffSecond : support \ {second} = {first} := by
    ext owner
    simp only [support, Finset.mem_sdiff, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨howner, hnotSecond⟩
      exact howner.resolve_right hnotSecond
    · intro hfirst
      refine ⟨Or.inl hfirst, ?_⟩
      intro hsecond
      exact hne (hfirst.symm.trans hsecond)
  have hsplit (J : Finset ι) (hJ : J ⊆ support) :
      opponents \ J = (support \ J) ∪ (opponents \ support) := by
    ext owner
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · intro howner
      by_cases hsupport : owner ∈ support
      · exact Or.inl ⟨hsupport, howner.2⟩
      · exact Or.inr ⟨howner.1, hsupport⟩
    · rintro (howner | howner)
      · exact ⟨hsupportSubset howner.1, howner.2⟩
      · refine ⟨howner.1, ?_⟩
        intro hownerJ
        exact howner.2 (hJ hownerJ)
  have hdisjoint (J : Finset ι) :
      Disjoint (support \ J) (opponents \ support) := by
    exact Finset.disjoint_left.mpr fun owner hleft hright =>
      (Finset.mem_sdiff.mp hright).2 (Finset.mem_sdiff.mp hleft).1
  have hprodOutside :
      (∏ owner ∈ opponents \ support, (1 - x owner)) = 1 := by
    apply Finset.prod_eq_one
    intro owner howner
    have hownerOutside := (Finset.mem_sdiff.mp howner).2
    have hownerFirst : owner ≠ first := by
      intro heq
      subst owner
      exact hownerOutside (by simp [support])
    have hownerSecond : owner ≠ second := by
      intro heq
      subst owner
      exact hownerOutside (by simp [support])
    have hxzero := quittingTwoOwnerHazard_eq_zero_of_ne first second owner
      firstHazard secondHazard hownerFirst hownerSecond
    change x owner = 0 at hxzero
    rw [hxzero]
    ring
  have hsurvival (J : Finset ι) (hJ : J ⊆ support) :
      (∏ owner ∈ opponents \ J, (1 - x owner)) =
        ∏ owner ∈ support \ J, (1 - x owner) := by
    rw [hsplit J hJ, Finset.prod_union (hdisjoint J), hprodOutside, mul_one]
  have hsum :
      (∑ J ∈ opponents.powerset, term J) =
        ∑ J ∈ support.powerset, term J := by
    symm
    apply Finset.sum_subset
    · intro J hJ
      rw [Finset.mem_powerset] at hJ ⊢
      exact hJ.trans hsupportSubset
    · intro J hJ hJnot
      have hsubsetOpponents := Finset.mem_powerset.mp hJ
      have hnotsubset : ¬ J ⊆ support := by
        intro hsubset
        exact hJnot (Finset.mem_powerset.mpr hsubset)
      obtain ⟨owner, hownerJ, hownerOutside⟩ :=
        Finset.not_subset.mp hnotsubset
      have hownerFirst : owner ≠ first := by
        intro heq
        subst owner
        exact hownerOutside (by simp [support])
      have hownerSecond : owner ≠ second := by
        intro heq
        subst owner
        exact hownerOutside (by simp [support])
      have hxzero := quittingTwoOwnerHazard_eq_zero_of_ne first second owner
        firstHazard secondHazard hownerFirst hownerSecond
      change x owner = 0 at hxzero
      have hprod : (∏ owner ∈ J, x owner) = 0 :=
        Finset.prod_eq_zero hownerJ hxzero
      simp [term, hprod]
  unfold sigmaValue
  change (∑ J ∈ opponents.powerset, term J) = _
  rw [hsum]
  change (∑ J ∈ ({first, second} : Finset ι).powerset, term J) = _
  rw [sum_powerset_pair first second hne term]
  simp only [term]
  rw [hsurvival ∅ (by simp),
    hsurvival {second} (by simp [support]),
    hsurvival {first} (by simp [support]),
    hsurvival {first, second} (by simp [support])]
  rw [hdiffFirst, hdiffSecond]
  simp [support, x, quittingTwoOwnerHazard, quittingTwoOwnerLeadingVariation,
    hne, hne.symm, weightOfReward,
    quittingSingletonTerminal, quittingPairJoinTerminal,
    quittingTripleJoinTerminal]
  ring

namespace QuittingChargeTangentPacket

/-- Linear coefficient of a tight outsider's gain along the packet's exact
two-owner ray. -/
def twoOwnerOutsiderLinearCoefficient
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) : ℝ :=
  packet.mass first *
      (reward (quittingPairJoinTerminal who first) who -
        reward (quittingSingletonTerminal who) who) +
    packet.mass second *
      (reward (quittingPairJoinTerminal who second) who -
        reward (quittingSingletonTerminal who) who)

/-- Quadratic coefficient of a tight outsider's gain along the packet's exact
two-owner ray.  It is the mixed second difference of the receiver's coalition
payoff, scaled by the two owner masses. -/
def twoOwnerOutsiderQuadraticCoefficient
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) : ℝ :=
  packet.mass first * packet.mass second *
    (reward (quittingTripleJoinTerminal who first second) who -
      reward (quittingPairJoinTerminal who first) who -
      reward (quittingPairJoinTerminal who second) who +
      reward (quittingSingletonTerminal who) who)

/-- Exact constant--linear--quadratic expansion of the outsider regression. -/
theorem twoOwnerOutsiderGainRegression_eq_polynomial
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) (t : ℝ)
    (hne : first ≠ second)
    (hwhoFirst : who ≠ first) (hwhoSecond : who ≠ second) :
    packet.twoOwnerOutsiderGainRegression first second t who =
      reward (quittingSingletonTerminal who) who - packet.boundary who +
        t * packet.twoOwnerOutsiderLinearCoefficient first second who +
        t ^ 2 * packet.twoOwnerOutsiderQuadraticCoefficient first second who := by
  unfold twoOwnerOutsiderGainRegression twoOwnerHazardAt
    twoOwnerOutsiderLinearCoefficient twoOwnerOutsiderQuadraticCoefficient
  rw [sigmaValue_twoOwner_outside first second who
    (t * packet.mass first) (t * packet.mass second)
    hne hwhoFirst hwhoSecond]
  ring

/-- At a singleton-tight inactive row the outsider regression has no constant
term and is the scale times its affine first jet. -/
theorem twoOwnerOutsiderGainRegression_eq_t_mul_jet_of_tight
    (packet : QuittingChargeTangentPacket reward)
    (first second who : ι) (t : ℝ)
    (hne : first ≠ second)
    (hwhoFirst : who ≠ first) (hwhoSecond : who ≠ second)
    (htight : reward (quittingSingletonTerminal who) who =
      packet.boundary who) :
    packet.twoOwnerOutsiderGainRegression first second t who =
      t * (packet.twoOwnerOutsiderLinearCoefficient first second who +
        t * packet.twoOwnerOutsiderQuadraticCoefficient first second who) := by
  rw [packet.twoOwnerOutsiderGainRegression_eq_polynomial
    first second who t hne hwhoFirst hwhoSecond, htight]
  ring

end QuittingChargeTangentPacket

end GameTheory
