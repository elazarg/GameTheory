/-
# Self-generating payoff sets under public monitoring

An Abreu--Pearce--Stacchetti self-generating set selects a current stage profile
and a public continuation promise at every promised payoff. This module turns
those selections into a pure public strategy, proves by a discounted
contraction that the strategy realizes its current promise, and uses the
canonical one-shot-deviation principle to obtain perfect public equilibrium.
It does not formalize the paper's constrained-efficiency or bang-bang results.
-/

import GameTheory.Repeated.MonitoringDecomposition
import GameTheory.Repeated.MonitoringOneShot

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo uy

variable {ι : Type uι}

namespace UtilityGame.PublicMonitoring

variable {G : UtilityGame.{uι, us, uo} ι}

/-- Coordinatewise boundedness of a payoff set. -/
def IsBoundedPayoffSet (payoffs : Set (ι → ℝ)) : Prop :=
  ∀ who, ∃ bound : ℝ, ∀ payoff ∈ payoffs, |payoff who| ≤ bound

/-- Payoff vectors delivered by perfect public equilibria. -/
def perfectPublicEquilibriumPayoffs
    (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ)
    (hstage : ∀ profile : M.MonitoredProfile, ∀ who t,
      M.MonitoredStageIntegrable profile t who)
    (hsum : ∀ profile : M.MonitoredProfile, ∀ who,
      Summable fun t : ℕ => discount ^ t *
        M.monitoredStagePayoff profile t who (hstage profile who t)) :
    Set (ι → ℝ) :=
  {payoff | ∃ profile : M.MonitoredProfile,
    M.IsPerfectPublicEquilibrium discount hstage hsum profile ∧
      ∀ who, M.discountedPayoff discount profile who
        (hstage profile who) (hsum profile who) = payoff who}

/-- Continuation payoff delivered after each possible next public signal. -/
def continuationPayoffAssignment
    (M : G.PublicMonitoring) (discount : ℝ)
    (hstage : ∀ profile : M.MonitoredProfile, ∀ who t,
      M.MonitoredStageIntegrable profile t who)
    (hsum : ∀ profile : M.MonitoredProfile, ∀ who,
      Summable fun t : ℕ => discount ^ t *
        M.monitoredStagePayoff profile t who (hstage profile who t))
    (profile : M.MonitoredProfile) : M.ContinuationAssignment :=
  fun signal who =>
    M.discountedPayoff discount (M.afterSignal profile signal) who
      (hstage _ who) (hsum _ who)

/-- Bounded stage payoffs bound the complete PPE payoff set coordinatewise. -/
theorem isBoundedPayoffSet_perfectPublicEquilibriumPayoffs_of_bounded
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ profile : Profile G.form.sig,
        |G.stagePayoff profile who (hG who profile)| ≤ bound) :
    IsBoundedPayoffSet (M.perfectPublicEquilibriumPayoffs discount
      (M.discountedStageIntegrableOfBounded hG hbound)
      (M.discountedSummableOfBounded
        hdiscount0 hdiscount1 hG hbound)) := by
  intro who
  obtain ⟨bound, hwho⟩ := hbound who
  refine ⟨bound, ?_⟩
  rintro payoff ⟨profile, _hequilibrium, hpayoff⟩
  rw [← hpayoff who]
  exact M.abs_discountedPayoffOfBounded_le
    hdiscount0 hdiscount1 hG profile who hwho

namespace SelfGenerating

variable {M : G.PublicMonitoring} [DecidableEq ι]
variable {discount : ℝ} {payoffs : Set (ι → ℝ)}

/-- Current stage profile selected from the decomposition of a promise. -/
noncomputable def action
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs) :
    Profile G.form.sig :=
  (hself promise.2).choose

/-- Public continuation assignment selected from the decomposition of a
promise. -/
noncomputable def continuation
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs) :
    M.ContinuationAssignment :=
  (hself promise.2).choose_spec.choose

theorem continuation_mem
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs)
    (signal : M.Signal) :
    hself.continuation promise signal ∈ payoffs :=
  (hself promise.2).choose_spec.choose_spec.1 signal

theorem promiseKeeping
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs) :
    M.IsPromiseKeeping discount promise.1 (hself.action promise)
      (hself.continuation promise) :=
  (hself promise.2).choose_spec.choose_spec.2.1

theorem enforceable
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs) :
    M.IsEnforceable discount (hself.action promise)
      (hself.continuation promise) :=
  (hself promise.2).choose_spec.choose_spec.2.2

/-- Promise state selected after one public signal. -/
noncomputable def nextState
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs)
    (signal : M.Signal) : payoffs :=
  ⟨hself.continuation promise signal,
    hself.continuation_mem promise signal⟩

@[simp]
theorem nextState_val
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs)
    (signal : M.Signal) :
    (hself.nextState promise signal).1 =
      hself.continuation promise signal :=
  rfl

/-- Promise state reached after a chronological list of public signals. -/
noncomputable def stateAfterSignals
    (hself : M.SelfGenerating discount payoffs) :
    payoffs → List M.Signal → payoffs
  | promise, [] => promise
  | promise, signal :: signals =>
      hself.stateAfterSignals (hself.nextState promise signal) signals

@[simp]
theorem stateAfterSignals_nil
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs) :
    hself.stateAfterSignals promise [] = promise :=
  rfl

@[simp]
theorem stateAfterSignals_cons
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs)
    (signal : M.Signal) (signals : List M.Signal) :
    hself.stateAfterSignals promise (signal :: signals) =
      hself.stateAfterSignals (hself.nextState promise signal) signals :=
  rfl

/-- Public strategy generated by repeatedly decomposing the current promised
payoff. -/
noncomputable def generatedProfile
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs) :
    M.MonitoredProfile :=
  fun who _ history =>
    hself.action
      (hself.stateAfterSignals promise (List.ofFn history)) who

@[simp]
theorem generatedProfile_zero
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs)
    (who : ι) (history : M.SignalHistory 0) :
    hself.generatedProfile promise who 0 history =
      hself.action promise who := by
  simp [generatedProfile]

/-- The generated strategy continues from the selected next promise state. -/
theorem afterSignal_generatedProfile
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs)
    (signal : M.Signal) :
    M.afterSignal (hself.generatedProfile promise) signal =
      hself.generatedProfile (hself.nextState promise signal) := by
  funext who n history
  simp [afterSignal, generatedProfile, List.ofFn_succ]

/-- Iterated continuation follows the corresponding promise-state
transition. -/
theorem afterSignals_generatedProfile
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs)
    (signals : List M.Signal) :
    M.afterSignals (hself.generatedProfile promise) signals =
      hself.generatedProfile
        (hself.stateAfterSignals promise signals) := by
  induction signals generalizing promise with
  | nil => rfl
  | cons signal signals ih =>
      rw [M.afterSignals_cons, hself.afterSignal_generatedProfile, ih]
      rfl

/-- Continuation after any public history is generated from the promise state
reached along that history. -/
theorem after_generatedProfile
    (hself : M.SelfGenerating discount payoffs) (promise : payoffs)
    {t : ℕ} (history : M.SignalHistory t) :
    M.after (hself.generatedProfile promise) history =
      hself.generatedProfile
        (hself.stateAfterSignals promise (List.ofFn history)) :=
  hself.afterSignals_generatedProfile promise (List.ofFn history)

/-- A generated strategy realizes its promised payoff.  After `steps`
Bellman substitutions, the remaining error is bounded by a geometric factor;
bounded stage payoffs and bounded promise states close the limit. -/
theorem generatedProfile_realizesPromise_of_bounds
    (hself : M.SelfGenerating discount payoffs)
    {who : ι} {stageBound promiseBound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hstage : ∀ profile : Profile G.form.sig,
      |G.stagePayoff profile who (hG who profile)| ≤ stageBound)
    (hpromise : ∀ payoff ∈ payoffs,
      |payoff who| ≤ promiseBound)
    (promise : payoffs) :
    M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
      (hself.generatedProfile promise) who hstage =
      promise.1 who := by
  let V (state : payoffs) : ℝ :=
    M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
      (hself.generatedProfile state) who hstage
  have hstageNonneg : 0 ≤ stageBound :=
    le_trans (abs_nonneg _) (hstage (hself.action promise))
  have hpromiseNonneg : 0 ≤ promiseBound :=
    le_trans (abs_nonneg _) (hpromise promise.1 promise.2)
  have herror : ∀ steps (state : payoffs),
      |V state - state.1 who| ≤
        discount ^ steps * (stageBound + promiseBound) := by
    intro steps
    induction steps with
    | zero =>
        intro state
        rw [pow_zero, one_mul]
        calc
          |V state - state.1 who| ≤
              |V state| + |state.1 who| :=
            abs_sub _ _
          _ ≤ stageBound + promiseBound := by
            exact add_le_add
              (M.abs_discountedPayoffOfBounded_le
                hdiscount0 hdiscount1 hG
                (hself.generatedProfile state) who hstage)
              (hpromise state.1 state.2)
    | succ steps ih =>
        intro state
        let errorBound : ℝ :=
          discount ^ steps * (stageBound + promiseBound)
        let realized : payoffs → ℝ := V
        let promised : payoffs → ℝ := fun next => next.1 who
        let law := M.signalLaw (hself.action state)
        have hpointUpper (signal : M.Signal) :
            realized (hself.nextState state signal) ≤
              promised (hself.nextState state signal) + errorBound := by
          have habs := abs_le.mp (ih (hself.nextState state signal))
          dsimp only [realized, promised, errorBound]
          linarith
        have hpointLower (signal : M.Signal) :
            promised (hself.nextState state signal) ≤
              realized (hself.nextState state signal) + errorBound := by
          have habs := abs_le.mp (ih (hself.nextState state signal))
          dsimp only [realized, promised, errorBound]
          linarith
        have hreal : PayoffIntegrable law
            (fun signal => realized (hself.nextState state signal)) :=
          payoffIntegrable_of_bounded law _ (fun signal =>
            M.abs_discountedPayoffOfBounded_le hdiscount0 hdiscount1
              hG (hself.generatedProfile (hself.nextState state signal))
              who hstage)
        have hprom : PayoffIntegrable law
            (fun signal => promised (hself.nextState state signal)) :=
          payoffIntegrable_of_bounded law _
            (fun signal => hpromise
              (hself.nextState state signal).1
              (hself.nextState state signal).2)
        have hconstant : PayoffIntegrable law
            (fun _ : M.Signal => errorBound) :=
          payoffIntegrable_constant law errorBound
        have hexpectUpper :
            expect law (fun signal =>
                realized (hself.nextState state signal)) hreal ≤
              expect law (fun signal =>
                promised (hself.nextState state signal)) hprom +
                errorBound := by
          calc
            expect law (fun signal =>
                realized (hself.nextState state signal)) hreal ≤
                expect law (fun signal =>
                  promised (hself.nextState state signal) + errorBound)
                  (payoffIntegrable_add hprom hconstant) :=
              expect_mono (fun signal _ => hpointUpper signal)
                hreal (payoffIntegrable_add hprom hconstant)
            _ = expect law
                  (fun signal => promised (hself.nextState state signal))
                  hprom + expect law (fun _ => errorBound) hconstant :=
              expect_add hprom hconstant
            _ = _ := by rw [expect_constant law errorBound hconstant]
        have hexpectLower :
            expect law (fun signal =>
                promised (hself.nextState state signal)) hprom ≤
              expect law (fun signal =>
                realized (hself.nextState state signal)) hreal +
                errorBound := by
          calc
            expect law (fun signal =>
                promised (hself.nextState state signal)) hprom ≤
                expect law (fun signal =>
                  realized (hself.nextState state signal) + errorBound)
                  (payoffIntegrable_add hreal hconstant) :=
              expect_mono (fun signal _ => hpointLower signal)
                hprom (payoffIntegrable_add hreal hconstant)
            _ = expect law
                  (fun signal => realized (hself.nextState state signal))
                  hreal + expect law (fun _ => errorBound) hconstant :=
              expect_add hreal hconstant
            _ = _ := by rw [expect_constant law errorBound hconstant]
        have hbell := M.discountedPayoff_eq_head_add_expected
          hdiscount0 hdiscount1 hG
          (hself.generatedProfile state) who hstage
        simp only [hself.generatedProfile_zero,
          hself.afterSignal_generatedProfile] at hbell
        have hbellRealized :
            realized state =
              (1 - discount) *
                  G.stagePayoff (hself.action state) who
                    (hG who (hself.action state)) +
                discount * expect law (fun signal =>
                  realized (hself.nextState state signal)) hreal := by
          simpa only [realized, V, law] using hbell
        have hkeep :
            (1 - discount) * G.stagePayoff
                (hself.action state) who (hG who (hself.action state)) +
                discount * expect law (fun signal =>
                  promised (hself.nextState state signal)) hprom =
              promised state := by
          obtain ⟨hbase, hsignal, hcoordinate⟩ :=
            hself.promiseKeeping state who
          simpa only [decomposedPayoff, law, promised, nextState_val]
            using hcoordinate
        have hupper :
            realized state ≤ promised state + discount * errorBound := by
          calc
            realized state =
                (1 - discount) * G.stagePayoff
                    (hself.action state) who (hG who _) +
                  discount * expect law (fun signal =>
                    realized (hself.nextState state signal)) hreal :=
              hbellRealized
            _ ≤ (1 - discount) * G.stagePayoff
                    (hself.action state) who (hG who _) +
                  discount *
                    (expect law (fun signal =>
                      promised (hself.nextState state signal)) hprom +
                        errorBound) := by
              exact add_le_add_right
                (mul_le_mul_of_nonneg_left hexpectUpper hdiscount0) _
            _ = promised state + discount * errorBound := by
              rw [← hkeep]
              ring
        have hlower :
            promised state ≤ realized state + discount * errorBound := by
          calc
            promised state =
                (1 - discount) * G.stagePayoff
                    (hself.action state) who (hG who _) +
                  discount * expect law (fun signal =>
                    promised (hself.nextState state signal)) hprom :=
              hkeep.symm
            _ ≤ (1 - discount) * G.stagePayoff
                    (hself.action state) who (hG who _) +
                  discount *
                    (expect law (fun signal =>
                      realized (hself.nextState state signal)) hreal +
                        errorBound) := by
              exact add_le_add_right
                (mul_le_mul_of_nonneg_left hexpectLower hdiscount0) _
            _ = realized state + discount * errorBound := by
              rw [hbellRealized]
              ring
        have hnextError :
            discount * errorBound =
              discount ^ (steps + 1) *
                (stageBound + promiseBound) := by
          simp only [errorBound, pow_succ]
          ring
        rw [← hnextError]
        apply abs_le.mpr
        constructor <;>
          dsimp only [realized, promised] at hupper hlower ⊢ <;>
          linarith
  have hlimit : Filter.Tendsto
      (fun steps => discount ^ steps * (stageBound + promiseBound))
      Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        hdiscount0 hdiscount1).mul_const
          (stageBound + promiseBound)
  have hzero :
      |V promise - promise.1 who| ≤ 0 :=
    ge_of_tendsto' hlimit (fun steps => herror steps promise)
  have hequal :
      V promise - promise.1 who = 0 :=
    abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _))
  exact sub_eq_zero.mp hequal

/-- Coordinatewise bounded payoff sets and bounded stage payoffs suffice for
promise realization. -/
theorem generatedProfile_realizesPromise
    (hself : M.SelfGenerating discount payoffs)
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ profile : Profile G.form.sig,
        |G.stagePayoff profile who (hG who profile)| ≤ bound)
    (hpayoffs : IsBoundedPayoffSet payoffs)
    (promise : payoffs) (who : ι) :
    M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
      (hself.generatedProfile promise) who (hbound who).choose_spec =
      promise.1 who := by
  obtain ⟨stageBound, hstageBound⟩ := hbound who
  obtain ⟨promiseBound, hpromiseBound⟩ := hpayoffs who
  exact hself.generatedProfile_realizesPromise_of_bounds
    hdiscount0 hdiscount1 hG hstageBound hpromiseBound promise

/-- The actual payoff from a generated strategy's one-shot deviation equals
the selected decomposed deviation payoff. -/
theorem discountedPayoff_oneShotDeviation_eq_decomposedDeviationPayoff
    (hself : M.SelfGenerating discount payoffs)
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ profile : Profile G.form.sig,
        |G.stagePayoff profile who (hG who profile)| ≤ bound)
    (hpayoffs : IsBoundedPayoffSet payoffs)
    (promise : payoffs) (who : ι)
    (action : G.form.sig.Strategy who)
    (hdeviationStage : UtilityIntegrable G.utility who
      (G.form.play (Profile.update (hself.action promise) who action)))
    (hdeviationSignal : PayoffIntegrable
      (M.signalLaw (Profile.update (hself.action promise) who action))
      (fun signal => hself.continuation promise signal who)) :
    M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
        (Profile.update (sig := M.monitoredSignature)
          (hself.generatedProfile promise) who
          (M.oneShotDeviation (hself.generatedProfile promise)
            who action)) who (hbound who).choose_spec =
      M.decomposedDeviationPayoff discount
        (hself.action promise) (hself.continuation promise)
        who action hdeviationStage hdeviationSignal := by
  obtain ⟨bound, hwho⟩ := hbound who
  let deviating : M.MonitoredProfile :=
    Profile.update (sig := M.monitoredSignature)
      (hself.generatedProfile promise) who
      (M.oneShotDeviation (hself.generatedProfile promise) who action)
  have hroot := M.currentProfile_update_oneShotDeviation
    (hself.generatedProfile promise) who action
  simp only [hself.generatedProfile_zero] at hroot
  have hbell := M.discountedPayoff_eq_head_add_expected
    hdiscount0 hdiscount1 hG deviating who hwho
  have hcontinuation (signal : M.Signal) :
      M.afterSignal deviating signal =
        hself.generatedProfile (hself.nextState promise signal) := by
    dsimp only [deviating]
    rw [M.afterSignal_update_oneShotDeviation,
      hself.afterSignal_generatedProfile]
  have hpoint (signal : M.Signal) :
      M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
          (M.afterSignal deviating signal) who hwho =
        hself.continuation promise signal who := by
    rw [hcontinuation]
    exact hself.generatedProfile_realizesPromise
      hdiscount0 hdiscount1 hG hbound hpayoffs
      (hself.nextState promise signal) who
  have hlaw :
      M.signalLaw (fun i => deviating i 0 (fun k => k.elim0)) =
        M.signalLaw (Profile.update (hself.action promise) who action) :=
    congrArg M.signalLaw hroot
  have hsignalRealized :=
    M.discountedAfterSignal_integrable_of_expected_bound
      hdiscount0 hdiscount1 hG deviating who hwho
  have hsignalUpdated := payoffIntegrable_congr_law
    hlaw hsignalRealized
  have hexpect := expect_congr_on_support
    (μ := M.signalLaw (Profile.update (hself.action promise) who action))
    (fun signal _ => hpoint signal)
    hsignalUpdated hdeviationSignal
  calc
    M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
        deviating who hwho =
      (1 - discount) * G.stagePayoff
          (fun i => deviating i 0 (fun k => k.elim0))
          who (hG who _) +
        discount * expect
          (M.signalLaw
            (fun i => deviating i 0 (fun k => k.elim0)))
          (fun signal => M.discountedPayoffOfBounded
            hdiscount0 hdiscount1 hG
            (M.afterSignal deviating signal) who hwho)
          hsignalRealized := hbell
    _ = (1 - discount) * G.stagePayoff
          (Profile.update (hself.action promise) who action)
          who (hG who _) +
        discount * expect
          (M.signalLaw
            (Profile.update (hself.action promise) who action))
          (fun signal => M.discountedPayoffOfBounded
            hdiscount0 hdiscount1 hG
            (M.afterSignal deviating signal) who hwho)
          hsignalUpdated := by
      have hstageEq := congrArg
        (fun stage : Profile G.form.sig =>
          G.stagePayoff stage who (hG who stage)) hroot
      rw [hstageEq]
      exact congrArg (fun value : ℝ =>
        (1 - discount) * G.stagePayoff
          (Profile.update (hself.action promise) who action)
          who (hG who _) + discount * value)
        (expect_congr_law hlaw _ hsignalRealized hsignalUpdated)
    _ = (1 - discount) * G.stagePayoff
          (Profile.update (hself.action promise) who action)
          who (hG who _) +
        discount * expect
          (M.signalLaw
            (Profile.update (hself.action promise) who action))
          (fun signal => hself.continuation promise signal who)
          hdeviationSignal := by rw [hexpect]
    _ = M.decomposedDeviationPayoff discount
          (hself.action promise) (hself.continuation promise)
          who action hdeviationStage hdeviationSignal := rfl

/-- The generated strategy has no profitable current one-shot deviation. -/
theorem generatedProfile_hasNoProfitableOneShotDeviation
    (hself : M.SelfGenerating discount payoffs)
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ profile : Profile G.form.sig,
        |G.stagePayoff profile who (hG who profile)| ≤ bound)
    (hpayoffs : IsBoundedPayoffSet payoffs) (promise : payoffs) :
    M.HasNoProfitableOneShotDeviation discount
      (M.discountedStageIntegrableOfBounded hG hbound)
      (M.discountedSummableOfBounded hdiscount0 hdiscount1 hG hbound)
      (hself.generatedProfile promise) := by
  intro who action
  obtain ⟨hbaseStage, hbaseSignal, hdeviationStage,
    hdeviationSignal, henforce⟩ := hself.enforceable promise who action
  calc
    M.discountedUtility discount
        (M.discountedStageIntegrableOfBounded hG hbound)
        (M.discountedSummableOfBounded
          hdiscount0 hdiscount1 hG hbound)
        (Profile.update (sig := M.monitoredSignature)
          (hself.generatedProfile promise) who
          (M.oneShotDeviation (hself.generatedProfile promise)
            who action)) who =
        M.decomposedDeviationPayoff discount
          (hself.action promise) (hself.continuation promise)
          who action hdeviationStage hdeviationSignal :=
      hself.discountedPayoff_oneShotDeviation_eq_decomposedDeviationPayoff
        hdiscount0 hdiscount1 hG hbound hpayoffs promise who action
        hdeviationStage hdeviationSignal
    _ ≤ M.decomposedPayoff discount
          (hself.action promise) (hself.continuation promise)
          who hbaseStage hbaseSignal := henforce
    _ = promise.1 who := by
      obtain ⟨hstage, hsignal, hkeep⟩ := hself.promiseKeeping promise who
      exact hkeep
    _ = M.discountedUtility discount
          (M.discountedStageIntegrableOfBounded hG hbound)
          (M.discountedSummableOfBounded
            hdiscount0 hdiscount1 hG hbound)
          (hself.generatedProfile promise) who :=
      (hself.generatedProfile_realizesPromise hdiscount0 hdiscount1
        hG hbound hpayoffs promise who).symm

/-- One-shot optimality of the generated strategy holds after every public
history, including off-path histories. -/
theorem generatedProfile_hasNoProfitableOneShotDeviationAfterEveryHistory
    (hself : M.SelfGenerating discount payoffs)
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ profile : Profile G.form.sig,
        |G.stagePayoff profile who (hG who profile)| ≤ bound)
    (hpayoffs : IsBoundedPayoffSet payoffs) (promise : payoffs) :
    M.HasNoProfitableOneShotDeviationAfterEveryHistory discount
      (M.discountedStageIntegrableOfBounded hG hbound)
      (M.discountedSummableOfBounded hdiscount0 hdiscount1 hG hbound)
      (hself.generatedProfile promise) := by
  intro t history
  rw [hself.after_generatedProfile]
  exact hself.generatedProfile_hasNoProfitableOneShotDeviation
    hdiscount0 hdiscount1 hG hbound hpayoffs _

/-- The strategy generated by a bounded self-generating set is a perfect
public equilibrium. -/
theorem generatedProfile_isPerfectPublicEquilibrium
    (hself : M.SelfGenerating discount payoffs)
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ profile : Profile G.form.sig,
        |G.stagePayoff profile who (hG who profile)| ≤ bound)
    (hpayoffs : IsBoundedPayoffSet payoffs) (promise : payoffs) :
    M.IsPerfectPublicEquilibrium discount
      (M.discountedStageIntegrableOfBounded hG hbound)
      (M.discountedSummableOfBounded hdiscount0 hdiscount1 hG hbound)
      (hself.generatedProfile promise) :=
  (hself.generatedProfile_hasNoProfitableOneShotDeviationAfterEveryHistory
    hdiscount0 hdiscount1 hG hbound hpayoffs promise
      ).isPerfectPublicEquilibrium_of_bounded
        hdiscount0 hdiscount1 hG hbound

/-- Every payoff in a bounded self-generating set is delivered by a perfect
public equilibrium. -/
theorem selfGenerating_subset_perfectPublicEquilibriumPayoffs
    (M : G.PublicMonitoring)
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ profile : Profile G.form.sig,
        |G.stagePayoff profile who (hG who profile)| ≤ bound)
    {payoffs : Set (ι → ℝ)} (hpayoffs : IsBoundedPayoffSet payoffs)
    (hself : M.SelfGenerating discount payoffs) :
    payoffs ⊆ M.perfectPublicEquilibriumPayoffs discount
      (M.discountedStageIntegrableOfBounded hG hbound)
      (M.discountedSummableOfBounded
        hdiscount0 hdiscount1 hG hbound) := by
  intro payoff hpayoff
  let promise : payoffs := ⟨payoff, hpayoff⟩
  exact ⟨hself.generatedProfile promise,
    hself.generatedProfile_isPerfectPublicEquilibrium
      hdiscount0 hdiscount1 hG hbound hpayoffs promise,
    fun who => hself.generatedProfile_realizesPromise
      hdiscount0 hdiscount1 hG hbound hpayoffs promise who⟩

end SelfGenerating

/-- Under bounded stage payoffs, the complete PPE payoff set decomposes using
its own continuation payoffs. -/
theorem perfectPublicEquilibriumPayoffs_selfGenerating_of_bounded
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ profile : Profile G.form.sig,
        |G.stagePayoff profile who (hG who profile)| ≤ bound) :
    M.SelfGenerating discount
      (M.perfectPublicEquilibriumPayoffs discount
        (M.discountedStageIntegrableOfBounded hG hbound)
        (M.discountedSummableOfBounded
          hdiscount0 hdiscount1 hG hbound)) := by
  intro payoff hpayoff
  obtain ⟨profile, hequilibrium, hpayoff⟩ := hpayoff
  let current : Profile G.form.sig :=
    fun who => profile who 0 (fun index => index.elim0)
  let continuation : M.ContinuationAssignment :=
    M.continuationPayoffAssignment discount
      (M.discountedStageIntegrableOfBounded hG hbound)
      (M.discountedSummableOfBounded
        hdiscount0 hdiscount1 hG hbound) profile
  refine ⟨current, continuation, ?_, ?_, ?_⟩
  · intro signal
    exact ⟨M.afterSignal profile signal,
      IsPerfectPublicEquilibrium.afterSignal M discount
        (M.discountedStageIntegrableOfBounded hG hbound)
        (M.discountedSummableOfBounded
          hdiscount0 hdiscount1 hG hbound)
        hequilibrium signal,
      fun _ => rfl⟩
  · intro who
    obtain ⟨bound, hwho⟩ := hbound who
    have hbaseStage := hG who current
    have hbaseSignal : PayoffIntegrable (M.signalLaw current)
        (fun signal => continuation signal who) := by
      simpa only [current, continuation, continuationPayoffAssignment]
        using M.discountedAfterSignal_integrable_of_expected_bound
          hdiscount0 hdiscount1 hG profile who hwho
    refine ⟨hbaseStage, hbaseSignal, ?_⟩
    have hbell := M.discountedPayoff_eq_head_add_expected
      hdiscount0 hdiscount1 hG profile who hwho
    rw [← hpayoff who]
    simpa only [decomposedPayoff, current, continuation,
      continuationPayoffAssignment] using hbell.symm
  · intro who action
    obtain ⟨bound, hwho⟩ := hbound who
    let deviating : M.MonitoredProfile :=
      Profile.update (sig := M.monitoredSignature) profile who
        (M.oneShotDeviation profile who action)
    have hroot := M.currentProfile_update_oneShotDeviation
      profile who action
    have hcontinuation (signal : M.Signal) :
        M.afterSignal deviating signal = M.afterSignal profile signal := by
      simp [deviating]
    have hcontBound (signal : M.Signal) :
        |continuation signal who| ≤ bound := by
      simpa only [continuation, continuationPayoffAssignment] using
        M.abs_discountedPayoffOfBounded_le hdiscount0 hdiscount1
          hG (M.afterSignal profile signal) who hwho
    have hbaseStage := hG who current
    have hdeviationStage :=
      hG who (Profile.update current who action)
    have hbaseSignal : PayoffIntegrable (M.signalLaw current)
        (fun signal => continuation signal who) :=
      payoffIntegrable_of_bounded _ _ hcontBound
    have hdeviationSignal : PayoffIntegrable
        (M.signalLaw (Profile.update current who action))
        (fun signal => continuation signal who) :=
      payoffIntegrable_of_bounded _ _ hcontBound
    refine ⟨hbaseStage, hbaseSignal, hdeviationStage,
      hdeviationSignal, ?_⟩
    have hdeviatingBell := M.discountedPayoff_eq_head_add_expected
      hdiscount0 hdiscount1 hG deviating who hwho
    have hbaseBell := M.discountedPayoff_eq_head_add_expected
      hdiscount0 hdiscount1 hG profile who hwho
    have hlaw :
        M.signalLaw (fun i => deviating i 0 (fun k => k.elim0)) =
          M.signalLaw (Profile.update current who action) := by
      exact congrArg M.signalLaw hroot
    have hsignalRealized :=
      M.discountedAfterSignal_integrable_of_expected_bound
        hdiscount0 hdiscount1 hG deviating who hwho
    have hsignalUpdated := payoffIntegrable_congr_law
      hlaw hsignalRealized
    have hpoint (signal : M.Signal) :
        M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
            (M.afterSignal deviating signal) who hwho =
          continuation signal who := by
      rw [hcontinuation]
      rfl
    have hexpect := expect_congr_on_support
      (μ := M.signalLaw (Profile.update current who action))
      (fun signal _ => hpoint signal)
      hsignalUpdated hdeviationSignal
    have hstageEq := congrArg
      (fun stage : Profile G.form.sig =>
        G.stagePayoff stage who (hG who stage)) hroot
    have hdeviationValue :
        M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
            deviating who hwho =
          M.decomposedDeviationPayoff discount current continuation
            who action hdeviationStage hdeviationSignal := by
      calc
        _ = (1 - discount) * G.stagePayoff
              (fun i => deviating i 0 (fun k => k.elim0))
              who (hG who _) +
            discount * expect
              (M.signalLaw
                (fun i => deviating i 0 (fun k => k.elim0)))
              (fun signal => M.discountedPayoffOfBounded
                hdiscount0 hdiscount1 hG
                (M.afterSignal deviating signal) who hwho)
              hsignalRealized := hdeviatingBell
        _ = (1 - discount) * G.stagePayoff
              (Profile.update current who action) who (hG who _) +
            discount * expect
              (M.signalLaw (Profile.update current who action))
              (fun signal => continuation signal who)
              hdeviationSignal := by
          rw [hstageEq]
          exact congrArg (fun value : ℝ =>
            (1 - discount) * G.stagePayoff
              (Profile.update current who action) who (hG who _) +
              discount * value)
            ((expect_congr_law hlaw _ hsignalRealized hsignalUpdated).trans
              hexpect)
        _ = _ := rfl
    have hbaseValue :
        M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
            profile who hwho =
          M.decomposedPayoff discount current continuation
            who hbaseStage hbaseSignal := by
      simpa only [decomposedPayoff, current, continuation,
        continuationPayoffAssignment] using hbaseBell
    have hNoShot := IsDiscountedPublicNash.hasNoProfitableOneShotDeviation
      M discount
      (M.discountedStageIntegrableOfBounded hG hbound)
      (M.discountedSummableOfBounded
        hdiscount0 hdiscount1 hG hbound)
      (IsPerfectPublicEquilibrium.isDiscountedPublicNash
        M discount
        (M.discountedStageIntegrableOfBounded hG hbound)
        (M.discountedSummableOfBounded
          hdiscount0 hdiscount1 hG hbound)
        hequilibrium)
    calc
      M.decomposedDeviationPayoff discount current continuation
          who action hdeviationStage hdeviationSignal =
          M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
            deviating who hwho := hdeviationValue.symm
      _ ≤ M.discountedPayoffOfBounded hdiscount0 hdiscount1 hG
          profile who hwho := hNoShot who action
      _ = M.decomposedPayoff discount current continuation
          who hbaseStage hbaseSignal := hbaseValue

/-- The PPE payoff set is the greatest coordinatewise-bounded
self-generating set under bounded stage payoffs. -/
theorem perfectPublicEquilibriumPayoffs_greatest_bounded_selfGenerating
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (hG : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ profile : Profile G.form.sig,
        |G.stagePayoff profile who (hG who profile)| ≤ bound) :
    M.SelfGenerating discount
        (M.perfectPublicEquilibriumPayoffs discount
          (M.discountedStageIntegrableOfBounded hG hbound)
          (M.discountedSummableOfBounded
            hdiscount0 hdiscount1 hG hbound)) ∧
      ∀ payoffs : Set (ι → ℝ),
        IsBoundedPayoffSet payoffs →
          M.SelfGenerating discount payoffs →
            payoffs ⊆ M.perfectPublicEquilibriumPayoffs discount
              (M.discountedStageIntegrableOfBounded hG hbound)
              (M.discountedSummableOfBounded
                hdiscount0 hdiscount1 hG hbound) := by
  refine ⟨M.perfectPublicEquilibriumPayoffs_selfGenerating_of_bounded
    hdiscount0 hdiscount1 hG hbound, ?_⟩
  intro payoffs hbounded hself
  exact SelfGenerating.selfGenerating_subset_perfectPublicEquilibriumPayoffs
    M hdiscount0 hdiscount1 hG hbound hbounded hself

end UtilityGame.PublicMonitoring

end GameTheory
