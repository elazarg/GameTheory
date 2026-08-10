/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTerminalFundingSupportNecessity
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerSupport

/-!
# A two-owner compatible packet cannot fund the zero terminal target

An interior zero-target lift at an owner with positive singleton payoff must
contain a supported simultaneous-quitting action at which that owner is paid
strictly negatively.  If every active root coordinate lies in a declared
pair, that action is exactly the pair collision.

The tangent compatibility equation on a literal two-owner packet forces the
same pair collision payoff to equal the owner's positive singleton payoff.
Consequently the terminal repair cannot stop on that compatible two-owner
stratum: its physical root support must contain a third owner.  This is a
support-enlargement obstruction, not a construction of the required
three-owner root.  In particular it does not supply the remaining outsider,
floor, or box inequalities.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open QuittingSureSetOwnerRepair

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

private theorem action_eq_false_of_forcedQuitSupport_of_hazard_zero
    (root : ι → PMF Bool) (owner other : ι) (action : ι → Bool)
    (hne : other ≠ owner)
    (haction : action ∈
      (pmfPi (Function.update root owner (PMF.pure true))).support)
    (hzero : hazardOfRoot root other = 0) :
    action other = false := by
  have hpure : root other = PMF.pure false :=
    pmf_eq_pure_false_of_apply_true_toReal_eq_zero (root other) hzero
  have hcoordinate : action other ∈
      (pushforward
        (pmfPi (Function.update root owner (PMF.pure true)))
        (fun joint => joint other)).support := by
    rw [pushforward, PMF.mem_support_map_iff]
    exact ⟨action, haction, rfl⟩
  rw [pmfPi_push_coord] at hcoordinate
  rw [Function.update_of_ne hne, hpure] at hcoordinate
  simpa using hcoordinate

/-- **Pair support is insufficient for positive terminal funding.**  If a
physical zero-target lift mixes an owner with positive singleton payoff and
the owner's pair-join effect with `other` vanishes, then the lift support
contains a third coordinate outside that pair.

Thus an exact compatible two-owner tangent root cannot also be the required
zero-target incoming root for a positively funded owner. -/
theorem exists_support_outside_pair_of_pairJoin_zero_positiveSingleton_zeroTargetLift
    (floor : Payoff ι) (upper : ℝ)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward 0 floor upper
      root support continuation)
    (owner other : ι) (hne : owner ≠ other)
    (howner : owner ∈ support)
    (hpositive : 0 < reward (quittingSingletonTerminal owner) owner)
    (hjoin : quittingActiveMixingPairJoinEffect reward owner other = 0) :
    ∃ third, third ∈ support ∧ third ≠ owner ∧ third ≠ other := by
  by_contra hthird
  have hsubset : ∀ third, third ∈ support →
      third = owner ∨ third = other := by
    intro third hthirdSupport
    by_contra hpair
    push Not at hpair
    exact hthird ⟨third, hthirdSupport, hpair.1, hpair.2⟩
  rcases exists_negativeCollision_of_positiveSingleton_zeroTargetLift
      (reward := reward) floor upper root support hsupport continuation hlift
        owner howner hpositive with
    ⟨action, hactionMass, hactionOwner, hopponent, hnegative⟩
  have hactionSupport : action ∈
      (pmfPi (Function.update root owner (PMF.pure true))).support := by
    simpa [PMF.mem_support_iff] using hactionMass
  rcases hopponent with ⟨quitter, hquitterOwner, hquitterTrue⟩
  have hquitterSupport : quitter ∈ support := by
    by_contra hquitterOutside
    have hfalse := action_eq_false_of_forcedQuitSupport_of_hazard_zero
      root owner quitter action hquitterOwner hactionSupport
        (hsupport.2 quitter hquitterOutside)
    rw [hfalse] at hquitterTrue
    contradiction
  have hquitterOther : quitter = other :=
    (hsubset quitter hquitterSupport).resolve_left hquitterOwner
  have hactionOther : action other = true := by
    simpa [hquitterOther] using hquitterTrue
  have hquitters : quittingQuitters action = {owner, other} := by
    apply Finset.ext
    intro who
    by_cases hwhoOwner : who = owner
    · subst who
      simp [quittingQuitters, hactionOwner]
    by_cases hwhoOther : who = other
    · subst who
      simp [quittingQuitters, hactionOther]
    have hwhoOutside : who ∉ support := by
      intro hwhoSupport
      rcases hsubset who hwhoSupport with rfl | rfl
      · exact hwhoOwner rfl
      · exact hwhoOther rfl
    have hactionFalse := action_eq_false_of_forcedQuitSupport_of_hazard_zero
      root owner who action hwhoOwner hactionSupport
        (hsupport.2 who hwhoOutside)
    simp [quittingQuitters, hactionFalse, hwhoOwner, hwhoOther]
  have hpairNegative :
      reward (quittingPairJoinTerminal owner other) owner < 0 := by
    rw [hquitters, quittingSetReward_of_nonempty reward
      (Finset.insert_nonempty owner {other})] at hnegative
    simpa [quittingPairJoinTerminal] using hnegative
  unfold quittingActiveMixingPairJoinEffect at hjoin
  linarith

namespace QuittingChargeTangentPacket

/-- **Compatible packet support must enlarge at the zero target.**  If
`first, second` are the entire positive-mass support of a compatible tangent
packet, then any physical zero-target lift funding `first` positively has an
active third owner outside the packet pair.

The theorem deliberately does not identify that third owner or solve its
three-owner product-root equations. -/
theorem exists_third_rootSupport_of_compatible_twoOwnerPacket_zeroTargetLift
    (packet : QuittingChargeTangentPacket reward)
    (floor : Payoff ι) (upper : ℝ)
    (root : ι → PMF Bool) (support : Finset ι)
    (hsupport : IsQuittingRootInteriorOnSupport root support)
    (continuation : Payoff ι)
    (hlift : IsQuittingFrozenRootContinuationLift reward 0 floor upper
      root support continuation)
    (first second : ι) (hne : first ≠ second)
    (hrootFirst : first ∈ support)
    (hpositive : 0 < reward (quittingSingletonTerminal first) first)
    (hfirst : 0 < packet.mass first)
    (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst :
      quittingActivePairCompatibilityResidual packet first = 0) :
    ∃ third, third ∈ support ∧ third ≠ first ∧ third ≠ second := by
  have hjoin :=
    packet.pairJoinEffect_eq_zero_of_twoOwnerSupport_compatible_first
      first second hne hfirst hsecond houtside hcompatFirst
  exact
    exists_support_outside_pair_of_pairJoin_zero_positiveSingleton_zeroTargetLift
      floor upper root support hsupport continuation hlift first second hne
        hrootFirst hpositive hjoin

/-- The exact nonexistence form on the literal packet pair.  Compatible
two-owner tangent roots may integrate at their pinned packet boundary, but
they cannot be reused as positive-owner lifts at the zero target. -/
theorem not_exists_zeroTargetLift_on_compatible_twoOwnerPacketSupport
    (packet : QuittingChargeTangentPacket reward)
    (floor : Payoff ι) (upper : ℝ) (root : ι → PMF Bool)
    (first second : ι) (hne : first ≠ second)
    (hsupport : IsQuittingRootInteriorOnSupport root {first, second})
    (hpositive : 0 < reward (quittingSingletonTerminal first) first)
    (hfirst : 0 < packet.mass first)
    (hsecond : 0 < packet.mass second)
    (houtside : ∀ owner, owner ≠ first → owner ≠ second →
      packet.mass owner = 0)
    (hcompatFirst :
      quittingActivePairCompatibilityResidual packet first = 0) :
    ¬ ∃ continuation, IsQuittingFrozenRootContinuationLift
      reward 0 floor upper root {first, second} continuation := by
  rintro ⟨continuation, hlift⟩
  rcases packet.exists_third_rootSupport_of_compatible_twoOwnerPacket_zeroTargetLift
      floor upper root {first, second} hsupport continuation hlift first second
        hne (by simp) hpositive hfirst hsecond houtside hcompatFirst with
    ⟨third, hthird, hthirdFirst, hthirdSecond⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hthird
  exact hthird.elim hthirdFirst hthirdSecond

end QuittingChargeTangentPacket

end GameTheory
