/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PrescribedEndpointTargetTransportBoundaryNoGo
import GameTheory.Concepts.Stochastic.PrescribedEndpointTransportChildAlternative

/-!
# Moving endpoint transport is not controlled by the endpoint kernel

The analytic prescribed-transport example has non-sublinear target
transport along the universal calendar.  Nevertheless, its kernel at the
analytic endpoint is the identity kernel.  From the low entry state, the
high state is then unreachable, and the entry-restricted endpoint family
has no positive charged circulation.

At every positive parameter, however, the low-to-high edge is present and
the high self-loop carries a positive charged circulation.  Thus the
obstruction is a singular support change: a vanishing edge is traversed
with non-summable cumulative hazard.  Any moving-kernel theorem must retain
the punctured support and the calendar rate; it cannot freeze only the
endpoint kernel.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace MovingEndpointTransportEndpointKernelBoundary

open Filter Math Math.PMFProduct Math.Probability Set
open AnalyticBellmanGerm.FiniteBiasSeed
open PrescribedEndpointTargetTransportBoundaryNoGo

abbrev State := Bool

/-- The endpoint target of the player whose prescribed payoff drifts. -/
def target (state : State) : ℝ :=
  if state then 1 else 0

/-- The endpoint kernel: both states are absorbing. -/
def endpointKernel (state : State) : PMF State :=
  PMF.pure state

/-- Each state indexes the transition sourced at that state. -/
def source (state : State) : State :=
  state

/-- The positive-parameter kernel: low leaks to high with probability
`p`, while high remains absorbing. -/
def puncturedKernel
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (state : State) : PMF State :=
  if state then PMF.pure true
  else PrescribedEndpointTargetTransportNoGo.coin p hp0 hp1

/-- The actual state kernel induced by the explicit analytic Bellman
profile at parameter `p`. -/
def inducedKernel
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (state : State) : PMF State :=
  (pmfPi
    (PrescribedEndpointTargetTransportNoGo.profile
      p hp0 hp1 state)).bind
    (PrescribedEndpointTargetTransportNoGo.game.transition state)

private theorem expect_pmfPi_bool
    (m : PrescribedEndpointTargetTransportNoGo.Player → PMF Bool)
    (f :
      (PrescribedEndpointTargetTransportNoGo.Player → Bool) → ℝ) :
    expect (pmfPi m) f =
      expect (m false) (fun owner =>
        expect (m true) (fun other =>
          f (fun player => if player then other else owner))) := by
  classical
  have hfalse : Function.update m false (m false) = m :=
    Function.update_eq_self false m
  rw [← hfalse, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (m false))
  funext owner
  have htrue :
      Function.update (Function.update m false (PMF.pure owner))
          true (m true) =
        Function.update m false (PMF.pure owner) := by
    funext player
    cases player <;> simp
  rw [← htrue, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (m true))
  funext other
  have hpure :
      Function.update
          (Function.update m false (PMF.pure owner))
          true (PMF.pure other) =
        fun player =>
          PMF.pure (if player then other else owner) := by
    funext player
    cases player <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

/-- The explicit Bellman profile induces exactly the punctured leak kernel.
At `p = 0`, this specializes to the endpoint identity kernel. -/
theorem inducedKernel_eq_puncturedKernel
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (state : State) :
    inducedKernel p hp0 hp1 state =
      puncturedKernel p hp0 hp1 state := by
  apply Math.ProbabilityMassFunction.toVector_injective
  funext destination
  unfold Math.ProbabilityMassFunction.toVector inducedKernel
  rw [← expect_pi_single, expect_bind, expect_pmfPi_bool]
  cases state <;> cases destination
  all_goals
    simp [PrescribedEndpointTargetTransportNoGo.profile,
      PrescribedEndpointTargetTransportNoGo.game,
      PrescribedEndpointTargetTransportNoGo.otherAction,
      puncturedKernel,
      PrescribedEndpointTargetTransportNoGo.expect_coin,
      PrescribedEndpointTargetTransportNoGo.coin_true_toReal,
      PrescribedEndpointTargetTransportNoGo.coin_false_toReal]

/-- The analytic endpoint of the induced Bellman kernels is the identity
kernel used below. -/
theorem inducedKernel_zero_eq_endpointKernel
    (state : State) :
    inducedKernel 0 le_rfl zero_le_one state =
      endpointKernel state := by
  rw [inducedKernel_eq_puncturedKernel]
  apply Math.ProbabilityMassFunction.toVector_injective
  funext destination
  unfold Math.ProbabilityMassFunction.toVector
  cases state <;> cases destination <;>
    simp [puncturedKernel, endpointKernel,
      PrescribedEndpointTargetTransportNoGo.coin_true_toReal,
      PrescribedEndpointTargetTransportNoGo.coin_false_toReal]

/-- The forward displacement from the low entry state is the indicator of
the high state. -/
@[simp]
theorem signedCharge_forward (state : State) :
    FrozenEndpointTransport.signedCharge target false true state =
      target state := by
  simp [FrozenEndpointTransport.signedCharge,
    MovingEndpointOccupationEvidence.orientedDisplacement, target]

/-- At the endpoint, available support steps are self-loops. -/
theorem endpoint_availableSupportStep_eq
    {current next : State}
    (step :
      AvailableSupportStep endpointKernel source current next) :
    current = next := by
  obtain ⟨index, index_source, transition_pos⟩ := step
  have next_eq : next = index := by
    simpa [endpointKernel] using transition_pos
  exact index_source.symm.trans next_eq.symm

/-- Endpoint reachability is equality. -/
theorem endpoint_eq_of_availableReachable
    {current next : State}
    (reachable :
      AvailableReachable endpointKernel source current next) :
    current = next := by
  induction reachable using Relation.ReflTransGen.head_induction_on with
  | refl =>
      rfl
  | head step _ inductionHypothesis =>
      exact
        (endpoint_availableSupportStep_eq step).trans
          inductionHypothesis

/-- Every endpoint operational index reachable from the low entry is the
low self-loop. -/
theorem endpoint_reachableIndex_eq_false
    (index :
      ReachableOccupationIndex endpointKernel source false) :
    index.1 = false := by
  have reachable :=
    index.source_reachable endpointKernel source false
  simpa [source] using
    endpoint_eq_of_availableReachable reachable

/-- The entry-restricted endpoint family has no forward positive charged
circulation. -/
theorem no_endpoint_positiveChargedCirculation :
    ∀ forward : Bool,
    ¬HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (fun index :
            ReachableOccupationIndex endpointKernel source false =>
          endpointKernel index.1)
        (fun index :
            ReachableOccupationIndex endpointKernel source false =>
          source index.1))
      (fun index :
          ReachableOccupationIndex endpointKernel source false =>
        FrozenEndpointTransport.signedCharge
          target false forward index.1) := by
  intro forward
  rintro ⟨mass, -, -, charge_eq_one⟩
  have charge_eq_zero :
      (∑ index :
          ReachableOccupationIndex endpointKernel source false,
        mass index *
          FrozenEndpointTransport.signedCharge
            target false forward index.1) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    rw [endpoint_reachableIndex_eq_false index]
    simp [FrozenEndpointTransport.signedCharge,
      MovingEndpointOccupationEvidence.orientedDisplacement, target]
  rw [charge_eq_zero] at charge_eq_one
  norm_num at charge_eq_one

/-- The same endpoint failure expressed using the entry-aware circulation
structure. -/
theorem no_endpoint_entryReachablePositiveChargedCirculation :
    ∀ forward : Bool,
    ¬Nonempty
      (EntryReachablePositiveChargedCirculation
        endpointKernel source
        (FrozenEndpointTransport.signedCharge target false forward)
        false) := by
  intro forward
  rintro ⟨circulation⟩
  apply no_endpoint_positiveChargedCirculation forward
  exact ⟨
    circulation.mass,
    circulation.mass_nonneg,
    circulation.balance,
    circulation.charge_eq_one
  ⟩

/-- The endpoint kernel stays forever at its initial state. -/
@[simp]
theorem endpoint_iter_eq_pure
    (stage : ℕ) (state : State) :
    Math.PMFIter.iter endpointKernel stage state =
      PMF.pure state := by
  induction stage with
  | zero =>
      rfl
  | succ stage inductionHypothesis =>
      rw [Math.PMFIter.iter_succ', inductionHypothesis,
        PMF.pure_bind]
      rfl

/-- Frozen endpoint transport is identically zero. -/
@[simp]
theorem endpoint_cumulativeTransport_eq_zero
    (horizon : ℕ) :
    FrozenEndpointTransport.cumulativeTransport
      endpointKernel target false horizon = 0 := by
  unfold FrozenEndpointTransport.cumulativeTransport
  apply Finset.sum_eq_zero
  intro stage _
  rw [endpoint_iter_eq_pure, expect_pure]
  norm_num [target]

/-- Hence the endpoint kernel itself has a sublinear transport account. -/
theorem endpoint_cumulativeTransport_sublinear :
    IsAsymptoticallySublinear fun horizon =>
      |FrozenEndpointTransport.cumulativeTransport
        endpointKernel target false horizon| := by
  simpa using IsAsymptoticallySublinear.const 0

/-- The endpoint frozen-kernel alternative is in its bounded-account
branch.  This account does not control the moving punctured kernels. -/
theorem endpoint_twoSidedPotentialData :
    Nonempty
      (FrozenEndpointTransport.TwoSidedPotentialData
        endpointKernel target false) := by
  obtain ⟨alternative⟩ :=
    FrozenEndpointTransport.exists_alternative
      endpointKernel target false
  cases alternative with
  | chargedClass data =>
      exact False.elim
        (no_endpoint_entryReachablePositiveChargedCirculation
          data.forward
          ⟨data.circulation⟩)
  | boundedAccount data =>
      exact ⟨data⟩

/-- At every positive parameter, the vanishing low-to-high edge makes the
high state support-reachable from the low entry. -/
theorem punctured_true_reachable
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    AvailableReachable
      (puncturedKernel p hp.le hp1) source false true := by
  apply Relation.ReflTransGen.single
  refine ⟨false, rfl, ?_⟩
  simp only [puncturedKernel, Bool.false_eq_true, ↓reduceIte]
  intro transition_zero
  apply hp.ne'
  calc
    p =
        (PrescribedEndpointTargetTransportNoGo.coin
          p hp.le hp1 true).toReal := by
      rw [
        PrescribedEndpointTargetTransportNoGo.coin_true_toReal]
    _ = 0 := by
      rw [transition_zero]
      rfl

/-- The positive-parameter kernel has a normalized charged circulation
supported on the high self-loop, and that support is reachable through the
vanishing edge. -/
theorem punctured_positiveChargedCirculation
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1) :
    HasNormalizedPositiveChargedCirculation
      (actualOccupationColumn
        (fun index :
            ReachableOccupationIndex
              (puncturedKernel p hp.le hp1) source false =>
          puncturedKernel p hp.le hp1 index.1)
        (fun index :
            ReachableOccupationIndex
              (puncturedKernel p hp.le hp1) source false =>
          source index.1))
      (fun index :
          ReachableOccupationIndex
            (puncturedKernel p hp.le hp1) source false =>
        FrozenEndpointTransport.signedCharge
          target false true index.1) := by
  apply restrict_positiveChargedCirculation_of_mass_support
    (puncturedKernel p hp.le hp1) source
    (FrozenEndpointTransport.signedCharge target false true)
    false
    (fun state => if state then 1 else 0)
  · intro state
    cases state <;> norm_num
  · intro destination
    cases destination <;>
      norm_num [actualOccupationColumn, puncturedKernel, source]
  · norm_num [FrozenEndpointTransport.signedCharge,
      MovingEndpointOccupationEvidence.orientedDisplacement, target]
  · intro state mass_pos
    cases state
    · exact Relation.ReflTransGen.refl
    · exact punctured_true_reachable p hp hp1

/-- The concrete analytic calendar has non-sublinear transport even though
the entry-restricted endpoint kernel has no positive charged circulation
and its frozen transport is identically zero. -/
theorem moving_transport_not_detected_by_endpoint_kernel :
    (¬HasSublinearPrescribedCalendarEndpointTargetTransport
        PrescribedEndpointTargetTransportNoGo.germ
        false 0 unshiftedValid) ∧
      (¬Nonempty
        (EntryReachablePositiveChargedCirculation
          endpointKernel source
          (FrozenEndpointTransport.signedCharge target false true)
          false)) ∧
      IsAsymptoticallySublinear (fun horizon =>
        |FrozenEndpointTransport.cumulativeTransport
          endpointKernel target false horizon|) := by
  exact ⟨
    not_hasSublinearPrescribedCalendarEndpointTargetTransport,
    no_endpoint_entryReachablePositiveChargedCirculation true,
    endpoint_cumulativeTransport_sublinear
  ⟩

/-- In particular, existence of bounded potentials for the endpoint kernel
does not imply a moving-calendar transport account. -/
theorem moving_transport_failure_with_endpoint_boundedAccount :
    (¬HasSublinearPrescribedCalendarEndpointTargetTransport
        PrescribedEndpointTargetTransportNoGo.germ
        false 0 unshiftedValid) ∧
      Nonempty
        (FrozenEndpointTransport.TwoSidedPotentialData
          endpointKernel target false) :=
  ⟨not_hasSublinearPrescribedCalendarEndpointTargetTransport,
    endpoint_twoSidedPotentialData⟩

end MovingEndpointTransportEndpointKernelBoundary
end StochasticGame
end GameTheory
