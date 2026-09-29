/- Copyright (c) 2026 GameTheory contributors. All rights reserved. -/

import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.ExpectationBind

/-! # Choosing whether to stop after observing a state

The state may contain a committed action and observations learned afterwards.
`true` selects stopping; `false` selects feasible continuation. Both branches
may have further randomness. Comparisons use actual-law integrability.
-/

noncomputable section

namespace GameTheory.Math.Probability

variable {State Outcome : Type*}

private def decisionLaw (states : PMF State) (stop : State → PMF Bool) :
    PMF (State × Bool) :=
  states.bind fun state => (stop state).map (state, ·)

private def selectedKernel (quit proceed : State → PMF Outcome) :
    State × Bool → PMF Outcome :=
  fun decision => if decision.2 then quit decision.1 else proceed decision.1

private def proceedKernel (proceed : State → PMF Outcome) :
    State × Bool → PMF Outcome :=
  fun decision => proceed decision.1

private theorem selectedLaw_eq (states : PMF State) (stop : State → PMF Bool)
    (quit proceed : State → PMF Outcome) :
    (decisionLaw states stop).bind (selectedKernel quit proceed) =
      states.bind (fun state => (stop state).bind fun stops =>
        if stops then quit state else proceed state) := by
  simp only [decisionLaw, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    selectedKernel]

private theorem proceedLaw_eq (states : PMF State) (stop : State → PMF Bool)
    (proceed : State → PMF Outcome) :
    (decisionLaw states stop).bind (proceedKernel proceed) =
      states.bind proceed := by
  simp only [decisionLaw, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    proceedKernel, PMF.bind_const]

private theorem stopLaw_eq (states : PMF State) (stop : State → PMF Bool) :
    (decisionLaw states stop).map Prod.snd = states.bind stop := by
  simp only [decisionLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
  congr 1
  funext state
  exact PMF.map_id (stop state)

/-- Branchwise continuation superiority survives arbitrary informed,
randomized stopping. The only integrability premises concern the two actual
ex-ante laws; conditional branch guards are derived where decisions occur. -/
theorem selective_stopping_bound
    (states : PMF State) (stop : State → PMF Bool)
    (quit proceed : State → PMF Outcome) (utility : Outcome → ℝ) (margin : ℝ)
    (hselected : PayoffIntegrable
      (states.bind fun state => (stop state).bind fun stops =>
        if stops then quit state else proceed state) utility)
    (hproceed : PayoffIntegrable (states.bind proceed) utility)
    (hmargin : ∀ state ∈ states.support, true ∈ (stop state).support →
      PayoffIntegrable (quit state) utility → PayoffIntegrable (proceed state) utility →
      expect (quit state) utility + margin ≤ expect (proceed state) utility) :
    expect (states.bind fun state => (stop state).bind fun stops =>
      if stops then quit state else proceed state) utility +
      margin * ((states.bind stop).toOuterMeasure {true}).toReal ≤
    expect (states.bind proceed) utility := by
  classical
  let decisions := decisionLaw states stop
  let selected := selectedKernel quit proceed
  let continuing := proceedKernel proceed
  have hselectedLaw : decisions.bind selected =
      states.bind (fun state => (stop state).bind fun stops =>
        if stops then quit state else proceed state) :=
    selectedLaw_eq states stop quit proceed
  have hproceedLaw : decisions.bind continuing = states.bind proceed :=
    proceedLaw_eq states stop proceed
  have hs : PayoffIntegrable (decisions.bind selected) utility :=
    payoffIntegrable_congr_law hselectedLaw.symm hselected
  have hp : PayoffIntegrable (decisions.bind continuing) utility :=
    payoffIntegrable_congr_law hproceedLaw.symm hproceed
  let selectedValue : State × Bool → ℝ := fun d => expect (selected d) utility
  let proceedValue : State × Bool → ℝ := fun d => expect (continuing d) utility
  have hselectedValue : ∀ d ∈ decisions.support,
      selectedValue d = expect (selected d) utility := fun _ _ => rfl
  have hproceedValue : ∀ d ∈ decisions.support,
      proceedValue d = expect (continuing d) utility := fun _ _ => rfl
  have hsi : PayoffIntegrable decisions selectedValue :=
    payoffIntegrable_bind_conditionalValue_on_support
      decisions selected utility hs selectedValue hselectedValue
  have hpi : PayoffIntegrable decisions proceedValue :=
    payoffIntegrable_bind_conditionalValue_on_support
      decisions continuing utility hp proceedValue hproceedValue
  let event : Set (State × Bool) := {d | d.2 = true}
  have hbound : expect decisions selectedValue ≤
      expect decisions proceedValue -
        margin * (decisions.toOuterMeasure event).toReal := by
    have hgap := expect_le_add_event_gap decisions event
      proceedValue selectedValue (-margin) hpi hsi
      (by
        intro d hd hnot
        have hfalse : d.2 = false := by
          cases hd' : d.2 <;> simp [event, hd'] at hnot ⊢
        simp only [selectedValue, proceedValue,
          selected, continuing, selectedKernel, proceedKernel, hfalse]
        exact le_rfl)
      (by
        intro d hd hevent
        have htrue : d.2 = true := hevent
        have hsupport : d.1 ∈ states.support ∧ d.2 ∈ (stop d.1).support := by
          have hd' : d ∈
              (states.bind fun state => (stop state).map (state, ·)).support := hd
          rw [PMF.support_bind] at hd'
          obtain ⟨state, hs, hpair⟩ := Set.mem_iUnion₂.mp hd'
          rw [PMF.mem_support_map_iff] at hpair
          obtain ⟨stops, ht, hpair⟩ := hpair
          cases hpair
          exact ⟨hs, ht⟩
        have hstops : true ∈ (stop d.1).support := by
          simpa only [htrue] using hsupport.2
        have hquit : PayoffIntegrable (quit d.1) utility := by
          simpa [selected, selectedKernel, htrue] using
            payoffIntegrable_bind_conditional_on_support
              decisions selected utility hs d hd
        have hcontinue : PayoffIntegrable (proceed d.1) utility := by
          simpa [continuing, proceedKernel] using
            payoffIntegrable_bind_conditional_on_support
              decisions continuing utility hp d hd
        have hpoint := hmargin d.1 hsupport.1 hstops hquit hcontinue
        have hvalue : selectedValue d + margin ≤ proceedValue d := by
          simpa [selectedValue, proceedValue,
            selected, continuing, selectedKernel, proceedKernel, htrue]
            using hpoint
        linarith)
    simpa [sub_eq_add_neg, mul_neg] using hgap
  have hevent : (decisions.toOuterMeasure event).toReal =
      ((states.bind stop).toOuterMeasure {true}).toReal := by
    rw [← stopLaw_eq states stop, PMF.toOuterMeasure_map_apply]
    rfl
  have hstower := expect_bind_tower_on_support decisions selected utility hs
    selectedValue hselectedValue
  have hptower := expect_bind_tower_on_support decisions continuing utility hp
    proceedValue hproceedValue
  have hsexpect : expect (states.bind fun state => (stop state).bind fun stops =>
        if stops then quit state else proceed state) utility =
      expect decisions selectedValue := by
    exact (expect_congr_law hselectedLaw.symm utility).trans hstower
  have hpexpect : expect (states.bind proceed) utility =
      expect decisions proceedValue := by
    exact (expect_congr_law hproceedLaw.symm utility).trans hptower
  rw [hsexpect, hpexpect, ← hevent]
  linarith

/-- Weak continuation superiority removes informed stopping from an upper
bound on utility. -/
theorem selective_stopping_le
    (states : PMF State) (stop : State → PMF Bool)
    (quit proceed : State → PMF Outcome) (utility : Outcome → ℝ)
    (hselected : PayoffIntegrable
      (states.bind fun state => (stop state).bind fun stops =>
        if stops then quit state else proceed state) utility)
    (hproceed : PayoffIntegrable (states.bind proceed) utility)
    (hcontinue : ∀ state ∈ states.support, true ∈ (stop state).support →
      PayoffIntegrable (quit state) utility → PayoffIntegrable (proceed state) utility →
      expect (quit state) utility ≤ expect (proceed state) utility) :
    expect (states.bind fun state => (stop state).bind fun stops =>
      if stops then quit state else proceed state) utility ≤
    expect (states.bind proceed) utility := by
  simpa using selective_stopping_bound states stop quit proceed utility 0
    hselected hproceed (fun state hs ht hq hp => by
      simpa using hcontinue state hs ht hq hp)

/-- A positive margin makes any positive probability of stopping strictly
worse than feasible continuation. -/
theorem selective_stopping_lt
    (states : PMF State) (stop : State → PMF Bool)
    (quit proceed : State → PMF Outcome) (utility : Outcome → ℝ) (margin : ℝ)
    (hselected : PayoffIntegrable
      (states.bind fun state => (stop state).bind fun stops =>
        if stops then quit state else proceed state) utility)
    (hproceed : PayoffIntegrable (states.bind proceed) utility)
    (hmargin : ∀ state ∈ states.support, true ∈ (stop state).support →
      PayoffIntegrable (quit state) utility → PayoffIntegrable (proceed state) utility →
      expect (quit state) utility + margin ≤ expect (proceed state) utility)
    (hpositive : 0 < margin)
    (hstops : 0 < ((states.bind stop).toOuterMeasure {true}).toReal) :
    expect (states.bind fun state => (stop state).bind fun stops =>
      if stops then quit state else proceed state) utility <
    expect (states.bind proceed) utility := by
  have hbound := selective_stopping_bound states stop quit proceed utility margin
    hselected hproceed hmargin
  have hcost := mul_pos hpositive hstops
  linarith

/-- The event indicator for a deterministic stopping decision. -/
def stopIndicator (stopped : State → Bool) : State → ℝ :=
  fun state => if stopped state then 1 else 0

theorem stopIndicator_integrable (law : PMF State) (stopped : State → Bool) :
    PayoffIntegrable law (stopIndicator stopped) := by
  apply payoffIntegrable_of_bounded law _ (C := 1)
  intro state
  cases hstop : stopped state <;> norm_num [stopIndicator, hstop]

theorem expect_stopIndicator (law : PMF State) (stopped : State → Bool) :
    expect law (stopIndicator stopped) =
      ((law.map stopped).toOuterMeasure {true}).toReal := by
  classical
  let event : Set State := {state | stopped state = true}
  have hvalue : ∀ state ∈ law.support,
      stopIndicator stopped state =
        (@ite ℝ (state ∈ event) (Classical.propDecidable _) 1 0) := by
    intro state _
    cases hstop : stopped state <;> simp [stopIndicator, event, hstop]
  calc
    expect law (stopIndicator stopped) =
        expect law
          (fun state => @ite ℝ (state ∈ event) (Classical.propDecidable _) 1 0) :=
      expect_congr_on_support hvalue
    _ = (law.toOuterMeasure event).toReal := expect_indicator law event
    _ = ((law.map stopped).toOuterMeasure {true}).toReal := by
      rw [PMF.toOuterMeasure_map_apply]
      rfl

/-- Add a fixed charge exactly where stopping occurs. -/
def stoppingCharge (stopped : State → Bool)
    (target : State → ℝ) (margin : ℝ) : State → ℝ :=
  fun state => target state + margin * stopIndicator stopped state

theorem stoppingCharge_integrable (law : PMF State) (stopped : State → Bool)
    (target : State → ℝ) (margin : ℝ)
    (htarget : PayoffIntegrable law target) :
    PayoffIntegrable law (stoppingCharge stopped target margin) :=
  payoffIntegrable_add htarget
    (payoffIntegrable_const_mul (c := margin)
      (stopIndicator_integrable law stopped))

theorem expect_stoppingCharge (law : PMF State) (stopped : State → Bool)
    (target : State → ℝ) (margin : ℝ)
    (htarget : PayoffIntegrable law target) :
    expect law (stoppingCharge stopped target margin) =
    expect law target +
      margin * ((law.map stopped).toOuterMeasure {true}).toReal := by
  rw [show expect law (stoppingCharge stopped target margin) =
      expect law target +
        margin * expect law (stopIndicator stopped)
           by
    unfold stoppingCharge
    rw [expect_add htarget
      (payoffIntegrable_const_mul (c := margin)
        (stopIndicator_integrable law stopped))]
    rw [expect_const_mul (c := margin)]]
  rw [expect_stopIndicator]

/-- Fiberwise comparison of the charged target against the source gives the
global stopping bound. A null information fiber imposes no condition. -/
theorem stopping_information_fiber_bound {Information : Type*}
    (law : PMF State) (stopped : State → Bool)
    (information : State → Information)
    (sourceValue targetValue : State → ℝ) (margin : ℝ)
    (hsource : PayoffIntegrable law sourceValue)
    (htarget : PayoffIntegrable law targetValue)
    (hfiber : ∀ observed ∈ (law.map information).support,
      expect law ((information ⁻¹' {observed}).indicator
        (stoppingCharge stopped targetValue margin)) ≤
      expect law ((information ⁻¹' {observed}).indicator sourceValue)) :
    expect law targetValue +
      margin * ((law.map stopped).toOuterMeasure {true}).toReal ≤
    expect law sourceValue := by
  rw [← expect_stoppingCharge law stopped targetValue margin htarget]
  apply expect_le_of_fiber_expect_le law information sourceValue
    (stoppingCharge stopped targetValue margin) hsource
    (stoppingCharge_integrable law stopped targetValue margin htarget)
  intro observed hs
  classical
  let fiber : Set State := information ⁻¹' {observed}
  calc
    expect law (fun state => if state ∈ fiber then
        stoppingCharge stopped targetValue margin state else 0) =
      expect law (fiber.indicator (stoppingCharge stopped targetValue margin)) := by
        apply expect_congr_on_support
        intro state _
        by_cases hstate : state ∈ fiber <;> simp [Set.indicator, hstate]
    _ ≤ expect law (fiber.indicator sourceValue) := hfiber observed hs
    _ = expect law (fun state => if state ∈ fiber then sourceValue state else 0) := by
        apply expect_congr_on_support
        intro state _
        by_cases hstate : state ∈ fiber <;> simp [Set.indicator, hstate]

/-- Stopped fibers need only their local charged comparison when the target is
no better than the source outside stopping. Both global values are evaluated
under the actual state law, and null stopped fibers impose no condition. -/
theorem stopping_information_fiber_bound_of_stopped {Information : Type*}
    (law : PMF State) (stopped : State → Bool)
    (information : State → Information)
    (sourceValue targetValue : State → ℝ) (margin : ℝ)
    (hsource : PayoffIntegrable law sourceValue)
    (htarget : PayoffIntegrable law targetValue)
    (houtside : ∀ state ∈ law.support, stopped state = false →
      targetValue state ≤ sourceValue state)
    (hstopped : ∀ observed ∈ (law.map information).support,
      let stoppedFiber : Set State :=
        {state | information state = observed ∧ stopped state = true}
      expect law (stoppedFiber.indicator
        (stoppingCharge stopped targetValue margin)) ≤
      expect law (stoppedFiber.indicator sourceValue)) :
    expect law targetValue +
      margin * ((law.map stopped).toOuterMeasure {true}).toReal ≤
    expect law sourceValue := by
  classical
  apply stopping_information_fiber_bound law stopped information
    sourceValue targetValue margin hsource htarget
  intro observed hs
  let fiber : Set State := information ⁻¹' {observed}
  let stoppedFiber : Set State :=
    {state | information state = observed ∧ stopped state = true}
  let continuedFiber : Set State :=
    {state | information state = observed ∧ stopped state = false}
  have hsplit (f : State → ℝ) (hf : PayoffIntegrable law f) :
      expect law (fiber.indicator f) =
        expect law (stoppedFiber.indicator f) +
        expect law (continuedFiber.indicator f) := by
    have hpoint (state : State) :
        fiber.indicator f state =
          stoppedFiber.indicator f state +
            continuedFiber.indicator f state := by
      by_cases hinfo : information state = observed
      · cases hstop : stopped state <;>
          simp [fiber, stoppedFiber, continuedFiber, hinfo, hstop]
      · simp [fiber, stoppedFiber, continuedFiber, hinfo]
    calc
      expect law (fiber.indicator f) =
        expect law (fun state =>
          stoppedFiber.indicator f state + continuedFiber.indicator f state) := by
              exact expect_congr_on_support (fun state _ => hpoint state)
      _ = _ := expect_add (payoffIntegrable_indicator _ hf)
        (payoffIntegrable_indicator _ hf)
  have hcontinued :
      expect law (continuedFiber.indicator
        (stoppingCharge stopped targetValue margin)) ≤
      expect law (continuedFiber.indicator sourceValue) := by
    refine expect_mono (fun state hstate => ?_)
      (payoffIntegrable_indicator _
        (stoppingCharge_integrable law stopped targetValue margin htarget))
      (payoffIntegrable_indicator _ hsource)
    by_cases hc : state ∈ continuedFiber
    · have hfalse : stopped state = false := hc.2
      simp only [Set.indicator_of_mem hc, stoppingCharge,
        stopIndicator, hfalse, Bool.false_eq_true, ↓reduceIte,
        mul_zero, add_zero]
      exact houtside state hstate hfalse
    · simp [Set.indicator_of_notMem hc]
  rw [hsplit (stoppingCharge stopped targetValue margin)
      (stoppingCharge_integrable law stopped targetValue margin htarget),
    hsplit sourceValue hsource]
  exact add_le_add (hstopped observed hs) hcontinued

/-- The fully informed branch value: the better of the two branches. -/
def informedStoppingValue (quit proceed : State → PMF Outcome) (utility : Outcome → ℝ) :
    State → ℝ :=
  fun state => max (expect (quit state) utility) (expect (proceed state) utility)

/-- The best informed stopping policy takes the better branch at every
reached state. All policies in the comparison family have defined payoffs. -/
theorem selective_stopping_optimal
    (states : PMF State) (quit proceed : State → PMF Outcome)
    (utility : Outcome → ℝ)
    (hvalue : PayoffIntegrable states (informedStoppingValue quit proceed utility))
    (hall : ∀ stop : State → PMF Bool, PayoffIntegrable
      (states.bind fun state => (stop state).bind fun stops =>
        if stops then quit state else proceed state) utility) :
    ∃ stop : State → PMF Bool,
      expect (states.bind fun state => (stop state).bind fun stops =>
        if stops then quit state else proceed state) utility =
        expect states
          (informedStoppingValue quit proceed utility)
           ∧
      ∀ alternative : State → PMF Bool,
        expect (states.bind fun state => (alternative state).bind fun stops =>
          if stops then quit state else proceed state) utility ≤
        expect states
          (informedStoppingValue quit proceed utility) := by
  classical
  let branch : State → Bool → PMF Outcome :=
    fun state stops => if stops then quit state else proceed state
  let best : State → PMF Bool := fun state =>
    if hs : state ∈ states.support then
      PMF.pure (decide
        (expect (proceed state) utility ≤
          expect (quit state) utility))
    else PMF.pure false
  have hbest (state : State) (hs : state ∈ states.support) :
      expect ((best state).bind (branch state)) utility =
        informedStoppingValue quit proceed utility state := by
    by_cases h :
        expect (proceed state) utility ≤
          expect (quit state) utility
    · have hlaw : (best state).bind (branch state) = quit state := by
        simp only [best, dite_eq_left hs, PMF.pure_bind, branch]
        simp [h]
      calc
        _ = expect (quit state) utility :=
          expect_congr_law hlaw utility
        _ = _ := by simp [informedStoppingValue, max_eq_left h]
    · have hlaw : (best state).bind (branch state) = proceed state := by
        simp only [best, dite_eq_left hs, PMF.pure_bind, branch]
        simp [h]
      calc
        _ = expect (proceed state) utility :=
          expect_congr_law hlaw utility
        _ = _ := by
          simp [informedStoppingValue, max_eq_right (le_of_lt (lt_of_not_ge h))]
  refine ⟨best, ?_, ?_⟩
  · exact expect_bind_tower_on_support states
      (fun state => (best state).bind (branch state)) utility (hall best)
      (informedStoppingValue quit proceed utility)
      (fun state hs => (hbest state hs).symm)
  · intro alternative
    let kernel : State → PMF Outcome :=
      fun state => (alternative state).bind (branch state)
    have hbranch (state : State) (hs : state ∈ states.support) :
        expect (kernel state) utility ≤
          informedStoppingValue quit proceed utility state := by
      have hcond : PayoffIntegrable
          ((alternative state).bind (branch state)) utility :=
        payoffIntegrable_bind_conditional_on_support
          states kernel utility (hall alternative) state hs
      have hmax : ∀ stops ∈ (alternative state).support,
          expect (branch state stops) utility ≤
          informedStoppingValue quit proceed utility state := by
        intro stops hstops
        cases stops with
        | false =>
            have hlaw : branch state false = proceed state := rfl
            rw [expect_congr_law hlaw utility]
            simp [informedStoppingValue]
        | true =>
            have hlaw : branch state true = quit state := rfl
            rw [expect_congr_law hlaw utility]
            simp [informedStoppingValue]
      exact expect_bind_le_constant_on_support
        (alternative state) (branch state) utility _ hcond hmax
    calc
      _ = expect states (fun state => expect (kernel state) utility) :=
        expect_bind_tower states kernel utility (hall alternative)
      _ ≤ expect states (informedStoppingValue quit proceed utility) :=
        expect_mono hbranch
          (payoffIntegrable_bind_conditionalExpectation states kernel utility
            (hall alternative)) hvalue

/-- Uniform elimination of the stopping option is equivalent to continuation
dominance at every state where both branch payoffs are defined. -/
theorem selective_stopping_le_iff
    (quit proceed : State → PMF Outcome) (utility : Outcome → ℝ) :
    (∀ (states : PMF State) (stop : State → PMF Bool),
      PayoffIntegrable
        (states.bind fun state => (stop state).bind fun stops =>
          if stops then quit state else proceed state) utility →
      PayoffIntegrable (states.bind proceed) utility →
      expect (states.bind fun state => (stop state).bind fun stops =>
        if stops then quit state else proceed state) utility ≤
        expect (states.bind proceed) utility) ↔
    ∀ state, PayoffIntegrable (quit state) utility →
      PayoffIntegrable (proceed state) utility →
      expect (quit state) utility ≤ expect (proceed state) utility := by
  constructor
  · intro hall state hquit hproceed
    let states : PMF State := PMF.pure state
    let stop : State → PMF Bool := fun _ => PMF.pure true
    have hs : PayoffIntegrable
        (states.bind fun current => (stop current).bind fun stops =>
          if stops then quit current else proceed current) utility := by
      simpa [states, stop, PMF.pure_bind] using hquit
    have hp : PayoffIntegrable (states.bind proceed) utility := by
      simpa [states, PMF.pure_bind] using hproceed
    have h := hall states stop hs hp
    simpa [states, stop, PMF.pure_bind] using h
  · intro hall states stop hselected hproceed
    exact selective_stopping_le states stop quit proceed utility
      hselected hproceed
      (fun state _ _ hquit hp => hall state hquit hp)

end GameTheory.Math.Probability
