/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.MovingEndpointOccupationEvidence
import Math.PMFIter
import Math.Probability.ChargedClassSupportRank
import Math.Probability.IntegratedResponseLedger

/-!
# Frozen endpoint transport: charged class or bounded account

For one fixed finite Markov kernel and one scalar endpoint target, there is
an exact entry-aware alternative:

* an entry-reachable stationary occupation has strictly positive target
  displacement in one orientation, and hence has a positive communicating
  class; or
* bounded potentials dominate both orientations of the displacement.

The second branch bounds the absolute cumulative expected displacement by
one constant, so it is asymptotically sublinear.  Consequently failure of
sublinearity for the frozen kernel forces the charged-class branch.

The selected class comes with the existing proper-support/full-support
dichotomy.  The full-support case is intentionally not called a recursive
child.  This theorem also makes no claim that a class of a frozen kernel is
a legal continuation class for a time-inhomogeneous analytic calendar.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability
namespace FrozenEndpointTransport

open Filter Math Math.Probability Set

variable {State : Type*} [Fintype State] [DecidableEq State]

/-- Endpoint displacement, with `true` denoting the forward orientation
and `false` its negative.  This is exactly the oriented displacement of
`MovingEndpointOccupationEvidence`, kept under its own frozen-kernel name. -/
abbrev signedCharge
    (target : State → ℝ) (entry : State)
    (forward : Bool) (state : State) : ℝ :=
  MovingEndpointOccupationEvidence.orientedDisplacement
    target entry forward state

/-- A fixed kernel as a source-indexed operational transition family. -/
def indexedKernel (kernel : State → PMF State) (state : State) :
    PMF State :=
  kernel state

/-- Every operational index is sourced at the state carrying the same
index. -/
def indexedSource (state : State) : State :=
  state

/-- The cumulative expected endpoint displacement under a fixed kernel. -/
def cumulativeTransport
    (kernel : State → PMF State)
    (target : State → ℝ) (entry : State)
    (horizon : ℕ) : ℝ :=
  ∑ stage ∈ Finset.range horizon,
    expect (Math.PMFIter.iter kernel stage entry)
      (fun state => target state - target entry)

omit [Fintype State] [DecidableEq State] in
private theorem pmfReachable_to_availableReachable
    (kernel : State → PMF State) {entry state : State}
    (reachable : PMFReachable kernel entry state) :
    AvailableReachable
      (indexedKernel kernel) indexedSource entry state := by
  induction reachable with
  | refl =>
      exact Relation.ReflTransGen.refl
  | @tail middle destination hprefix step inductionHypothesis =>
      exact Relation.ReflTransGen.tail
        inductionHypothesis ⟨middle, rfl, step⟩

omit [DecidableEq State] in
private theorem mem_reachableOccupationIndices_of_pmfReachable
    (kernel : State → PMF State) {entry state : State}
    (reachable : PMFReachable kernel entry state) :
    state ∈
      reachableOccupationIndices
        (indexedKernel kernel) indexedSource entry := by
  classical
  unfold reachableOccupationIndices
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact pmfReachable_to_availableReachable kernel reachable

omit [Fintype State] [DecidableEq State] in
private theorem pmfReachable_of_mem_iter_support
    (kernel : State → PMF State) (entry : State)
    {stage : ℕ} {state : State}
    (state_mem :
      state ∈ (Math.PMFIter.iter kernel stage entry).support) :
    PMFReachable kernel entry state := by
  induction stage generalizing state with
  | zero =>
      have state_eq : state = entry := by
        simpa [Math.PMFIter.iter_zero] using state_mem
      subst state
      exact Relation.ReflTransGen.refl
  | succ stage inductionHypothesis =>
      rw [Math.PMFIter.iter_succ',
        PMF.mem_support_bind_iff] at state_mem
      obtain ⟨previous, previous_mem, step⟩ := state_mem
      exact (inductionHypothesis previous_mem).tail step

/-- A positive signed stationary occupation and one of its positive
communicating classes. -/
structure ChargedClassData
    (kernel : State → PMF State)
    (target : State → ℝ) (entry : State) where
  forward : Bool
  circulation :
    EntryReachablePositiveChargedCirculation
      (indexedKernel kernel) indexedSource
      (signedCharge target entry forward) entry
  positiveClass : circulation.PositiveCommunicatingClass
  supportAlternative :
    positiveClass.HasProperSupportRankDescent ∨
      positiveClass.IsFullActiveSupportClass

/-- Two bounded potentials dominate the forward and reverse endpoint
displacements on every source reachable from the entry. -/
structure TwoSidedPotentialData
    (kernel : State → PMF State)
    (target : State → ℝ) (entry : State) where
  forward :
    EntryReachableBoundedChargePotential
      (indexedKernel kernel) indexedSource
      (signedCharge target entry true) entry
  reverse :
    EntryReachableBoundedChargePotential
      (indexedKernel kernel) indexedSource
      (signedCharge target entry false) entry

/-- The exhaustive frozen-kernel endpoint-transport alternatives. -/
inductive Alternative
    (kernel : State → PMF State)
    (target : State → ℝ) (entry : State)
  | chargedClass (data : ChargedClassData kernel target entry)
  | boundedAccount (data : TwoSidedPotentialData kernel target entry)

omit [DecidableEq State] in
private theorem expected_signedCharge_le_scaledDrift
    (kernel : State → PMF State)
    (target : State → ℝ) (entry : State)
    (forward : Bool)
    (potential :
      EntryReachableBoundedChargePotential
        (indexedKernel kernel) indexedSource
        (signedCharge target entry forward) entry)
    (stage : ℕ) :
    expect (Math.PMFIter.iter kernel stage entry)
        (signedCharge target entry forward) ≤
      potential.scale *
        (expect (Math.PMFIter.iter kernel (stage + 1) entry)
            potential.potential -
          expect (Math.PMFIter.iter kernel stage entry)
            potential.potential) := by
  let law := Math.PMFIter.iter kernel stage entry
  let drift : State → ℝ := fun state =>
    expect (kernel state) potential.potential -
      potential.potential state
  have charge_le_scaled_drift
      (state : State) (state_mem : state ∈ law.support) :
      signedCharge target entry forward state ≤
        potential.scale * drift state := by
    have reachable :
        PMFReachable kernel entry state :=
      pmfReachable_of_mem_iter_support
        kernel entry state_mem
    let index :
        ReachableOccupationIndex
          (indexedKernel kernel) indexedSource entry :=
      ⟨state,
        mem_reachableOccupationIndices_of_pmfReachable
          kernel reachable⟩
    have bound := potential.charge_le_discrepancy index
    have scaled :=
      (div_le_iff₀ potential.scale_pos).mp bound
    simpa [index, indexedKernel, indexedSource, drift,
      mul_comm] using scaled
  classical
  calc
    expect law (signedCharge target entry forward) =
        expect law
          (fun state =>
            if state ∈ law.support then
              signedCharge target entry forward state
            else
              potential.scale * drift state) := by
      apply ProbabilityMassFunction.expect_congr_on_support
      intro state state_mem
      simp [state_mem]
    _ ≤ expect law (fun state =>
          potential.scale * drift state) := by
      apply expect_mono
      intro state
      by_cases state_mem : state ∈ law.support
      · simpa [state_mem] using
          charge_le_scaled_drift state state_mem
      · simp [state_mem]
    _ =
        potential.scale *
          (expect (Math.PMFIter.iter kernel (stage + 1) entry)
              potential.potential -
            expect law potential.potential) := by
      rw [expect_const_mul, expect_sub,
        Math.PMFIter.iter_succ', expect_bind]

omit [DecidableEq State] in
private theorem cumulative_signedCharge_le_scale
    (kernel : State → PMF State)
    (target : State → ℝ) (entry : State)
    (forward : Bool)
    (potential :
      EntryReachableBoundedChargePotential
        (indexedKernel kernel) indexedSource
        (signedCharge target entry forward) entry)
    (horizon : ℕ) :
    (∑ stage ∈ Finset.range horizon,
      expect (Math.PMFIter.iter kernel stage entry)
        (signedCharge target entry forward)) ≤
      potential.scale := by
  have telescope :
      ∀ horizon : ℕ,
        (∑ stage ∈ Finset.range horizon,
          expect (Math.PMFIter.iter kernel stage entry)
            (signedCharge target entry forward)) ≤
          potential.scale *
            (expect (Math.PMFIter.iter kernel horizon entry)
                potential.potential -
              potential.potential entry) := by
    intro horizon
    induction horizon with
    | zero =>
        simp
    | succ horizon inductionHypothesis =>
        rw [Finset.sum_range_succ]
        calc
          _ ≤
              potential.scale *
                  (expect (Math.PMFIter.iter kernel horizon entry)
                      potential.potential -
                    potential.potential entry) +
                potential.scale *
                  (expect
                      (Math.PMFIter.iter kernel (horizon + 1) entry)
                      potential.potential -
                    expect (Math.PMFIter.iter kernel horizon entry)
                      potential.potential) := by
            gcongr
            exact
              expected_signedCharge_le_scaledDrift
                kernel target entry forward potential horizon
          _ =
              potential.scale *
                (expect
                    (Math.PMFIter.iter kernel (horizon + 1) entry)
                    potential.potential -
                  potential.potential entry) := by
            ring
  have final_le_one :
      expect (Math.PMFIter.iter kernel horizon entry)
          potential.potential ≤ 1 := by
    calc
      expect (Math.PMFIter.iter kernel horizon entry)
          potential.potential ≤
          expect (Math.PMFIter.iter kernel horizon entry)
            (fun _ => 1) := by
        apply expect_mono
        intro state
        exact (potential.bounded state).2
      _ = 1 := expect_const _ _
  have entry_nonneg : 0 ≤ potential.potential entry :=
    (potential.bounded entry).1
  calc
    _ ≤
        potential.scale *
          (expect (Math.PMFIter.iter kernel horizon entry)
              potential.potential -
            potential.potential entry) :=
      telescope horizon
    _ ≤ potential.scale := by
      nlinarith [potential.scale_pos]

namespace TwoSidedPotentialData

variable
    {kernel : State → PMF State}
    {target : State → ℝ} {entry : State}

omit [DecidableEq State] in
/-- The two potential scales uniformly bound absolute frozen transport. -/
theorem abs_cumulativeTransport_le
    (data : TwoSidedPotentialData kernel target entry)
    (horizon : ℕ) :
    |cumulativeTransport kernel target entry horizon| ≤
      data.forward.scale + data.reverse.scale := by
  have upper :
      cumulativeTransport kernel target entry horizon ≤
        data.forward.scale := by
    have h :=
      cumulative_signedCharge_le_scale
        kernel target entry true data.forward horizon
    change
      (∑ stage ∈ Finset.range horizon,
        expect (Math.PMFIter.iter kernel stage entry)
          (fun state => target state - target entry)) ≤
        data.forward.scale at h
    exact h
  have lower :
      -cumulativeTransport kernel target entry horizon ≤
        data.reverse.scale := by
    have reverse :=
      cumulative_signedCharge_le_scale
        kernel target entry false data.reverse horizon
    change
      (∑ stage ∈ Finset.range horizon,
        expect (Math.PMFIter.iter kernel stage entry)
          (fun state => target entry - target state)) ≤
        data.reverse.scale at reverse
    calc
      -cumulativeTransport kernel target entry horizon =
          ∑ stage ∈ Finset.range horizon,
            expect (Math.PMFIter.iter kernel stage entry)
              (fun state => target entry - target state) := by
        unfold cumulativeTransport
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro stage _
        rw [expect_sub, expect_sub, expect_const]
        ring
      _ ≤ data.reverse.scale := reverse
  rw [abs_le]
  constructor
  · linarith [data.forward.scale_pos, data.reverse.scale_pos]
  · linarith [data.forward.scale_pos, data.reverse.scale_pos]

omit [DecidableEq State] in
/-- In particular, the absolute frozen transport is sublinear. -/
theorem abs_cumulativeTransport_sublinear
    (data : TwoSidedPotentialData kernel target entry) :
    IsAsymptoticallySublinear fun horizon =>
      |cumulativeTransport kernel target entry horizon| := by
  apply IsAsymptoticallySublinear.of_nonneg_le
  · exact fun _ => abs_nonneg _
  · exact data.abs_cumulativeTransport_le
  · exact IsAsymptoticallySublinear.const
      (data.forward.scale + data.reverse.scale)

end TwoSidedPotentialData

/-- Every frozen finite kernel has the exact charged-class/bounded-account
alternative. -/
theorem exists_alternative
    (kernel : State → PMF State)
    (target : State → ℝ) (entry : State) :
    Nonempty (Alternative kernel target entry) := by
  rcases
      entryReachablePositiveChargedCirculation_or_boundedPotential
        (indexedKernel kernel) indexedSource
        (signedCharge target entry true) entry with
    forwardCirculation | forwardPotential
  · obtain ⟨circulation⟩ := forwardCirculation
    obtain ⟨positiveClass⟩ :=
      circulation.exists_positiveCommunicatingClass
    exact ⟨.chargedClass {
      forward := true
      circulation := circulation
      positiveClass := positiveClass
      supportAlternative :=
        positiveClass.properSupportRankDescent_or_fullActiveSupport
          circulation
    }⟩
  · rcases
      entryReachablePositiveChargedCirculation_or_boundedPotential
        (indexedKernel kernel) indexedSource
        (signedCharge target entry false) entry with
      reverseCirculation | reversePotential
    · obtain ⟨circulation⟩ := reverseCirculation
      obtain ⟨positiveClass⟩ :=
        circulation.exists_positiveCommunicatingClass
      exact ⟨.chargedClass {
        forward := false
        circulation := circulation
        positiveClass := positiveClass
        supportAlternative :=
          positiveClass.properSupportRankDescent_or_fullActiveSupport
            circulation
      }⟩
    · exact ⟨.boundedAccount {
        forward := forwardPotential.some
        reverse := reversePotential.some
      }⟩

/-- Failure of sublinear absolute transport for a fixed kernel forces an
entry-reachable charged communicating class. -/
theorem exists_chargedClassData_of_not_sublinear
    (kernel : State → PMF State)
    (target : State → ℝ) (entry : State)
    (failure :
      ¬IsAsymptoticallySublinear fun horizon =>
        |cumulativeTransport kernel target entry horizon|) :
    Nonempty (ChargedClassData kernel target entry) := by
  obtain ⟨alternative⟩ :=
    exists_alternative kernel target entry
  cases alternative with
  | chargedClass data =>
      exact ⟨data⟩
  | boundedAccount data =>
      exact False.elim
        (failure data.abs_cumulativeTransport_sublinear)

/-! ## Why the class need not be proper -/

namespace TwoCycleBoundary

/-- The deterministic two-cycle is irreducible on both states. -/
def kernel (state : Bool) : PMF Bool :=
  PMF.pure (!state)

def target (state : Bool) : ℝ :=
  if state then 1 else 0

def stateAt : ℕ → Bool
  | 0 => false
  | stage + 1 => !(stateAt stage)

@[simp]
theorem stateAt_two_mul (n : ℕ) :
    stateAt (2 * n) = false := by
  induction n with
  | zero =>
      rfl
  | succ n inductionHypothesis =>
      rw [Nat.mul_succ]
      simp only [stateAt, inductionHypothesis, Bool.not_false,
        Bool.not_true]

@[simp]
theorem stateAt_two_mul_add_one (n : ℕ) :
    stateAt (2 * n + 1) = true := by
  simp [stateAt]

theorem iter_eq_pure_stateAt (stage : ℕ) :
    Math.PMFIter.iter kernel stage false =
      PMF.pure (stateAt stage) := by
  induction stage with
  | zero =>
      rfl
  | succ stage inductionHypothesis =>
      rw [Math.PMFIter.iter_succ',
        inductionHypothesis, PMF.pure_bind]
      rfl

theorem expected_displacement_even (n : ℕ) :
    expect (Math.PMFIter.iter kernel (2 * n) false)
        (fun state => target state - target false) = 0 := by
  rw [iter_eq_pure_stateAt, expect_pure]
  simp [target]

theorem expected_displacement_odd (n : ℕ) :
    expect (Math.PMFIter.iter kernel (2 * n + 1) false)
        (fun state => target state - target false) = 1 := by
  rw [iter_eq_pure_stateAt, expect_pure]
  simp [target]

/-- Every pair of stages contributes exactly one unit of transport. -/
theorem cumulativeTransport_two_mul (n : ℕ) :
    cumulativeTransport kernel target false (2 * n) = n := by
  induction n with
  | zero =>
      simp [cumulativeTransport]
  | succ n inductionHypothesis =>
      rw [Nat.mul_succ, show 2 * n + 2 = (2 * n + 1) + 1 by omega]
      unfold cumulativeTransport at inductionHypothesis ⊢
      rw [Finset.sum_range_succ, Finset.sum_range_succ,
        inductionHypothesis, expected_displacement_even,
        expected_displacement_odd]
      norm_num

/-- Thus frozen endpoint transport can fail sublinearity even though the
only recurrent class is the full two-state space. -/
theorem cumulativeTransport_not_sublinear :
    ¬IsAsymptoticallySublinear fun horizon =>
      |cumulativeTransport kernel target false horizon| := by
  intro sublinear
  have even_tendsto_zero :
      Tendsto
        (fun n : ℕ =>
          ((2 * n : ℕ) : ℝ)⁻¹ *
            |cumulativeTransport kernel target false (2 * n)|)
        atTop (nhds 0) := by
    apply (isAsymptoticallySublinear_iff_tendsto.mp sublinear).comp
    apply tendsto_atTop.2
    intro lower
    filter_upwards [eventually_ge_atTop lower] with n hn
    omega
  have eventually_half :
      ∀ᶠ n : ℕ in atTop,
        ((2 * n : ℕ) : ℝ)⁻¹ *
            |cumulativeTransport kernel target false (2 * n)| =
          (1 / 2 : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [cumulativeTransport_two_mul, abs_of_nonneg (by positivity)]
    push_cast
    field_simp
  have even_tendsto_half :
      Tendsto
        (fun n : ℕ =>
          ((2 * n : ℕ) : ℝ)⁻¹ *
            |cumulativeTransport kernel target false (2 * n)|)
        atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds.congr'
      (eventually_half.mono fun _ equality => equality.symm)
  have false_eq :
      (0 : ℝ) = 1 / 2 :=
    tendsto_nhds_unique even_tendsto_zero even_tendsto_half
  norm_num at false_eq

theorem closed_states_eq_univ
    (states : Finset Bool) (states_nonempty : states.Nonempty)
    (closed : IsPMFClosed kernel states) :
    states = Finset.univ := by
  obtain ⟨state, state_mem⟩ := states_nonempty
  have other_mem : (!state) ∈ states := by
    apply closed state_mem
    simp [PMFSupportStep, kernel]
  apply Finset.eq_univ_of_forall
  intro candidate
  cases state <;> cases candidate <;>
    simp_all

/-- In particular there is no nonempty proper closed child.  Failure of
transport therefore cannot imply proper-state-support descent, even for a
fixed kernel. -/
theorem no_nonempty_proper_closed_class :
    ¬∃ states : Finset Bool,
      states.Nonempty ∧
        IsPMFClosed kernel states ∧
        states ⊂ Finset.univ := by
  rintro ⟨states, states_nonempty, closed, proper⟩
  exact proper.ne (closed_states_eq_univ states states_nonempty closed)

end TwoCycleBoundary

end FrozenEndpointTransport
end Probability
end Math
