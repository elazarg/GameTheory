/-
# Recursive payoff decomposition under public monitoring

This is the decomposition surface used in Abreu, Pearce, and
Stacchetti, *Toward a Theory of Discounted Repeated Games with Imperfect
Monitoring*, Econometrica 58(5), 1990, 1041--1063. A current stage profile and
a signal-indexed continuation payoff assignment jointly promise a payoff
vector and deter unilateral current-stage deviations.

A promise is a real payoff vector, so promise keeping carries the actual
integration certificates of the current-stage and continuation expectations.
Deterrence instead compares extended-real decomposed payoffs: a deviation whose
current-stage or continuation expectation is infinite is still ranked, and only
a deviation whose payoff is genuinely undefined is left incomparable. No bound
or finite signal carrier is stored in the model.
-/

import GameTheory.Repeated.MonitoringDiscounted

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo uy

variable {ι : Type uι}

namespace UtilityGame.PublicMonitoring

variable {G : UtilityGame.{uι, us, uo} ι}

/-- A public continuation payoff vector assigned to every next-period public
signal. -/
abbrev ContinuationAssignment (M : G.PublicMonitoring) :=
  M.Signal → ι → ℝ

/-- Normalized discounted payoff promised by current play and a public
continuation assignment. -/
def decomposedPayoff (M : G.PublicMonitoring) (discount : ℝ)
    (profile : Profile G.form.sig) (continuation : M.ContinuationAssignment)
    (who : ι) : ℝ :=
  (1 - discount) * G.stagePayoff profile who +
    discount * expect (M.signalLaw profile)
      (fun signal => continuation signal who)

/-- Payoff to one player from a current unilateral deviation, retaining the
same signal-contingent continuation assignment. -/
def decomposedDeviationPayoff (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (profile : Profile G.form.sig)
    (continuation : M.ContinuationAssignment) (who : ι)
    (action : G.form.sig.Strategy who) : ℝ :=
  M.decomposedPayoff discount (Profile.update profile who action)
    continuation who

/-- The current stage profile and continuation assignment deliver the promised
payoff vector. -/
def IsPromiseKeeping (M : G.PublicMonitoring) (discount : ℝ)
    (promise : ι → ℝ) (profile : Profile G.form.sig)
    (continuation : M.ContinuationAssignment) : Prop :=
  ∀ who, UtilityIntegrable G.utility who (G.form.play profile) ∧
    PayoffIntegrable (M.signalLaw profile)
      (fun signal => continuation signal who) ∧
      M.decomposedPayoff discount profile continuation
        who = promise who

/-- The normalized discounted payoff promised by a profile and a continuation
assignment, in the extended reals: each of the current-stage and continuation
expectations may be infinite. -/
def extendedDecomposedPayoff (M : G.PublicMonitoring) (discount : ℝ)
    (profile : Profile G.form.sig) (continuation : M.ContinuationAssignment)
    (who : ι) : EReal :=
  ((1 - discount : ℝ) : EReal) *
      extendedExpectedUtility G.utility who (G.form.play profile) +
    (discount : EReal) *
      extendedExpect (M.signalLaw profile) (fun signal => continuation signal who)

/-- The decomposed payoff exists: both expectations exist and their weighted
terms are not opposite infinities. -/
def HasDecomposedPayoff (M : G.PublicMonitoring) (discount : ℝ)
    (profile : Profile G.form.sig) (continuation : M.ContinuationAssignment)
    (who : ι) : Prop :=
  UtilityHasExpectation G.utility who (G.form.play profile) ∧
    HasExpectation (M.signalLaw profile) (fun signal => continuation signal who) ∧
    HasDefinedSum
      (((1 - discount : ℝ) : EReal) *
        extendedExpectedUtility G.utility who (G.form.play profile))
      ((discount : EReal) *
        extendedExpect (M.signalLaw profile) (fun signal => continuation signal who))

/-- One unilateral current-stage action is deterred: both decomposed payoffs
exist and the deviation's is no larger. -/
def Deters (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (profile : Profile G.form.sig)
    (continuation : M.ContinuationAssignment) (who : ι)
    (action : G.form.sig.Strategy who) : Prop :=
  M.HasDecomposedPayoff discount profile continuation who ∧
    M.HasDecomposedPayoff discount (Profile.update profile who action) continuation who ∧
    M.extendedDecomposedPayoff discount (Profile.update profile who action)
        continuation who ≤
      M.extendedDecomposedPayoff discount profile continuation who

/-- Every unilateral current-stage action is deterred by the same public
continuation assignment. -/
def IsEnforceable (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (profile : Profile G.form.sig)
    (continuation : M.ContinuationAssignment) : Prop :=
  ∀ who action, M.Deters discount profile continuation who action

/-- With integrable expectations, the extended decomposed payoff is the real
one. -/
theorem extendedDecomposedPayoff_eq (M : G.PublicMonitoring) {discount : ℝ}
    {profile : Profile G.form.sig} {continuation : M.ContinuationAssignment} {who : ι}
    (hstage : UtilityIntegrable G.utility who (G.form.play profile))
    (hsignal : PayoffIntegrable (M.signalLaw profile)
      (fun signal => continuation signal who)) :
    M.extendedDecomposedPayoff discount profile continuation who =
      M.decomposedPayoff discount profile continuation who := by
  rw [extendedDecomposedPayoff, extendedExpectedUtility_eq hstage,
    extendedExpect_eq_expect hsignal, decomposedPayoff, stagePayoff]
  norm_cast

theorem hasDecomposedPayoff_of_integrable (M : G.PublicMonitoring) {discount : ℝ}
    {profile : Profile G.form.sig} {continuation : M.ContinuationAssignment} {who : ι}
    (hstage : UtilityIntegrable G.utility who (G.form.play profile))
    (hsignal : PayoffIntegrable (M.signalLaw profile)
      (fun signal => continuation signal who)) :
    M.HasDecomposedPayoff discount profile continuation who := by
  refine ⟨hasExpectation_of_payoffIntegrable hstage,
    hasExpectation_of_payoffIntegrable hsignal, ?_⟩
  rw [extendedExpect_eq_expect hsignal, ← EReal.coe_mul]
  exact hasDefinedSum_coe_right _ _

/-- With integrable expectations on both sides, deterrence is the real
comparison of decomposed payoffs. -/
theorem deters_iff_of_integrable (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} {profile : Profile G.form.sig}
    {continuation : M.ContinuationAssignment} {who : ι}
    {action : G.form.sig.Strategy who}
    (hstage : UtilityIntegrable G.utility who (G.form.play profile))
    (hsignal : PayoffIntegrable (M.signalLaw profile)
      (fun signal => continuation signal who))
    (hdeviationStage : UtilityIntegrable G.utility who
      (G.form.play (Profile.update profile who action)))
    (hdeviationSignal : PayoffIntegrable (M.signalLaw (Profile.update profile who action))
      (fun signal => continuation signal who)) :
    M.Deters discount profile continuation who action ↔
      M.decomposedDeviationPayoff discount profile continuation who action ≤
        M.decomposedPayoff discount profile continuation who := by
  rw [Deters, M.extendedDecomposedPayoff_eq hstage hsignal,
    M.extendedDecomposedPayoff_eq hdeviationStage hdeviationSignal, EReal.coe_le_coe_iff,
    decomposedDeviationPayoff]
  exact ⟨fun h => h.2.2, fun h => ⟨M.hasDecomposedPayoff_of_integrable hstage hsignal,
    M.hasDecomposedPayoff_of_integrable hdeviationStage hdeviationSignal, h⟩⟩

/-- A payoff decomposes on `payoffs` when it is promised and enforced by a
current profile and every signal-contingent continuation lies in `payoffs`. -/
def DecomposesOn (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (payoffs : Set (ι → ℝ)) (promise : ι → ℝ) : Prop :=
  ∃ (profile : Profile G.form.sig)
      (continuation : M.ContinuationAssignment),
    (∀ signal, continuation signal ∈ payoffs) ∧
      M.IsPromiseKeeping discount promise profile continuation ∧
      M.IsEnforceable discount profile continuation

/-- Payoffs decomposable using continuations in `payoffs`. -/
def decompositionOperator (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (payoffs : Set (ι → ℝ)) : Set (ι → ℝ) :=
  {promise | M.DecomposesOn discount payoffs promise}

/-- A set is self-generating when each of its promises decomposes using
continuations from that same set. -/
def SelfGenerating (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (payoffs : Set (ι → ℝ)) : Prop :=
  payoffs ⊆ M.decompositionOperator discount payoffs

@[simp]
theorem mem_decompositionOperator_iff
    (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (payoffs : Set (ι → ℝ)) (promise : ι → ℝ) :
    promise ∈ M.decompositionOperator discount payoffs ↔
      M.DecomposesOn discount payoffs promise :=
  Iff.rfl

/-- Allowing a larger continuation set can only enlarge the decomposition
operator. -/
theorem decompositionOperator_mono
    (M : G.PublicMonitoring) [DecidableEq ι] (discount : ℝ) :
    Monotone (M.decompositionOperator discount) := by
  intro first second hsubset promise
  rintro ⟨profile, continuation, hcontinuation, hpromise, henforce⟩
  exact ⟨profile, continuation, fun signal => hsubset (hcontinuation signal),
    hpromise, henforce⟩

@[simp]
theorem selfGenerating_empty
    (M : G.PublicMonitoring) [DecidableEq ι] (discount : ℝ) :
    M.SelfGenerating discount (∅ : Set (ι → ℝ)) := by
  intro promise hpromise
  exact False.elim hpromise

/-- Signal-independent continuation at one payoff vector. -/
def constantContinuation (M : G.PublicMonitoring) (payoff : ι → ℝ) :
    M.ContinuationAssignment :=
  fun _ => payoff

@[simp]
theorem constantContinuation_apply
    (M : G.PublicMonitoring) (payoff : ι → ℝ)
    (signal : M.Signal) :
    M.constantContinuation payoff signal = payoff :=
  rfl

/-- Constant continuation promises give the expected affine decomposition. -/
@[simp]
theorem decomposedPayoff_constant
    (M : G.PublicMonitoring) (discount : ℝ)
    (profile : Profile G.form.sig) (payoff : ι → ℝ) (who : ι) :
    M.decomposedPayoff discount profile (M.constantContinuation payoff)
        who =
      (1 - discount) * G.stagePayoff profile who +
        discount * payoff who := by
  simp only [decomposedPayoff, constantContinuation_apply]
  rw [expect_constant]

/-- Repeating the current stage-payoff vector as the continuation keeps that
promise for every discount factor. -/
theorem isPromiseKeeping_constant_stagePayoff
    (M : G.PublicMonitoring) (discount : ℝ)
    (profile : Profile G.form.sig)
    (hstage : ∀ who, UtilityIntegrable G.utility who (G.form.play profile)) :
    M.IsPromiseKeeping discount
      (fun who => G.stagePayoff profile who)
      profile (M.constantContinuation fun who =>
        G.stagePayoff profile who) := by
  intro who
  refine ⟨hstage who, payoffIntegrable_constant _ _, ?_⟩
  calc
    M.decomposedPayoff discount profile
        (M.constantContinuation fun who =>
          G.stagePayoff profile who) who =
      (1 - discount) * G.stagePayoff profile who +
        discount * G.stagePayoff profile who :=
      M.decomposedPayoff_constant discount profile _ who
    _ = G.stagePayoff profile who := by ring

/-- A constant continuation contributes a finite term, so the decomposed
payoff exists exactly when the current-stage expectation does. -/
theorem hasDecomposedPayoff_constant_iff (M : G.PublicMonitoring) (discount : ℝ)
    (profile : Profile G.form.sig) (payoff : ι → ℝ) (who : ι) :
    M.HasDecomposedPayoff discount profile (M.constantContinuation payoff) who ↔
      UtilityHasExpectation G.utility who (G.form.play profile) := by
  have hsignal : PayoffIntegrable (M.signalLaw profile)
      (fun signal => M.constantContinuation payoff signal who) :=
    payoffIntegrable_constant _ _
  refine ⟨fun h => h.1, fun h => ⟨h, hasExpectation_of_payoffIntegrable hsignal, ?_⟩⟩
  rw [extendedExpect_eq_expect hsignal, ← EReal.coe_mul]
  exact hasDefinedSum_coe_right _ _

theorem extendedDecomposedPayoff_constant (M : G.PublicMonitoring) (discount : ℝ)
    (profile : Profile G.form.sig) (payoff : ι → ℝ) (who : ι) :
    M.extendedDecomposedPayoff discount profile (M.constantContinuation payoff) who =
      ((1 - discount : ℝ) : EReal) *
          extendedExpectedUtility G.utility who (G.form.play profile) +
        ((discount * payoff who : ℝ) : EReal) := by
  rw [extendedDecomposedPayoff]
  simp only [constantContinuation_apply]
  rw [extendedExpect_constant, EReal.coe_mul]

/-- With a constant continuation and `discount < 1`, APS enforceability is
exactly ordinary stage-game Nash. -/
theorem isEnforceable_constant_iff_isNash
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount1 : discount < 1)
    (profile : Profile G.form.sig) (payoff : ι → ℝ) :
    M.IsEnforceable discount profile (M.constantContinuation payoff) ↔
      IsNash G.form (euPreference G.utility) profile := by
  rw [IsEnforceable, isNash_iff]
  refine forall_congr' fun who => forall_congr' fun action => ?_
  rw [Deters, euPreference_apply, hasDecomposedPayoff_constant_iff,
    hasDecomposedPayoff_constant_iff, extendedDecomposedPayoff_constant,
    extendedDecomposedPayoff_constant, coe_mul_add_coe_le_iff (by linarith)]

/-- A stage-Nash payoff with an integrable incumbent decomposes on its
singleton through stationary continuation promises. -/
theorem decomposesOn_singleton_stagePayoff_of_isNash
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount1 : discount < 1)
    {profile : Profile G.form.sig}
    (hnash : IsNash G.form (euPreference G.utility) profile)
    (hstage : ∀ who, UtilityIntegrable G.utility who (G.form.play profile)) :
    M.DecomposesOn discount
      ({fun who => G.stagePayoff profile who} : Set (ι → ℝ))
      (fun who => G.stagePayoff profile who) := by
  let payoff : ι → ℝ := fun who => G.stagePayoff profile who
  refine ⟨profile, M.constantContinuation payoff, ?_, ?_, ?_⟩
  · intro signal
    simp [payoff]
  · exact M.isPromiseKeeping_constant_stagePayoff discount profile hstage
  · exact (M.isEnforceable_constant_iff_isNash hdiscount1 profile payoff).2 hnash

/-- Every singleton stage-Nash payoff with an integrable incumbent is
self-generating. -/
theorem selfGenerating_singleton_stagePayoff_of_isNash
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount1 : discount < 1)
    {profile : Profile G.form.sig}
    (hnash : IsNash G.form (euPreference G.utility) profile)
    (hstage : ∀ who, UtilityIntegrable G.utility who (G.form.play profile)) :
    M.SelfGenerating discount
      ({fun who => G.stagePayoff profile who} : Set (ι → ℝ)) := by
  intro promise hpromise
  rw [Set.mem_singleton_iff] at hpromise
  subst promise
  exact M.decomposesOn_singleton_stagePayoff_of_isNash hdiscount1 hnash hstage

end UtilityGame.PublicMonitoring

end GameTheory
