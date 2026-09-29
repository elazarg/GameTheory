/-
# Recursive payoff decomposition under public monitoring

This is the decomposition surface used in Abreu, Pearce, and
Stacchetti, *Toward a Theory of Discounted Repeated Games with Imperfect
Monitoring*, Econometrica 58(5), 1990, 1041--1063. A current stage profile and
a signal-indexed continuation payoff assignment jointly promise a payoff
vector and deter unilateral current-stage deviations.

Current-stage and continuation expectations carry their actual integration
certificates. No bound or finite signal carrier is stored in the model.
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

/-- Every unilateral current-stage action is deterred by the same public
continuation assignment. -/
def IsEnforceable (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (profile : Profile G.form.sig)
    (continuation : M.ContinuationAssignment) : Prop :=
  ∀ who action,
    UtilityIntegrable G.utility who (G.form.play profile) ∧
    PayoffIntegrable (M.signalLaw profile)
      (fun signal => continuation signal who) ∧
    UtilityIntegrable G.utility who
      (G.form.play (Profile.update profile who action)) ∧
    PayoffIntegrable
      (M.signalLaw (Profile.update profile who action))
      (fun signal => continuation signal who) ∧
      M.decomposedDeviationPayoff discount profile continuation
          who action ≤
        M.decomposedPayoff discount profile continuation
          who

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

/-- With a constant continuation and `discount < 1`, APS enforceability is
exactly ordinary stage-game Nash with integrable unilateral deviations. -/
theorem isEnforceable_constant_iff_isNash
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount1 : discount < 1)
    (profile : Profile G.form.sig) (payoff : ι → ℝ) :
    M.IsEnforceable discount profile (M.constantContinuation payoff) ↔
      IsNash G.form (euPreference G.utility) profile ∧
        G.form.HasIntegrableDeviations G.utility profile := by
  rw [IsEnforceable, isNash_iff]
  constructor
  · intro henforce
    refine ⟨fun who action => ?_, fun who action => (henforce who action).2.2.1⟩
    obtain ⟨hbase, _hbaseSignal, hupdate, _hupdateSignal,
      hdeviation⟩ := henforce who action
    refine (euPreference_iff _ _ _ _ hbase hupdate).2 ?_
    have hdeviation' :
        (1 - discount) * G.stagePayoff
            (Profile.update profile who action) who +
          discount * payoff who ≤
        (1 - discount) * G.stagePayoff profile who +
          discount * payoff who := by
      calc
        _ = M.decomposedDeviationPayoff discount profile
            (M.constantContinuation payoff) who action :=
          (M.decomposedPayoff_constant discount
            (Profile.update profile who action) payoff who).symm
        _ ≤ M.decomposedPayoff discount profile
            (M.constantContinuation payoff) who := hdeviation
        _ = _ := M.decomposedPayoff_constant
          discount profile payoff who
    dsimp only [stagePayoff] at hdeviation'
    nlinarith
  · rintro ⟨hnash, hintegrable⟩ who action
    have hbase := hintegrable.base who
    have hupdate := hintegrable who action
    have hdeviation := (euPreference_iff _ _ _ _ hbase hupdate).1 (hnash who action)
    refine ⟨hbase, payoffIntegrable_constant _ _,
      hupdate, payoffIntegrable_constant _ _, ?_⟩
    calc
      M.decomposedDeviationPayoff discount profile
          (M.constantContinuation payoff) who action =
        (1 - discount) * G.stagePayoff
            (Profile.update profile who action) who +
          discount * payoff who :=
        M.decomposedPayoff_constant discount
          (Profile.update profile who action) payoff who
      _ ≤ (1 - discount) * G.stagePayoff profile who +
          discount * payoff who := by
        dsimp only [stagePayoff]
        nlinarith
      _ = M.decomposedPayoff discount profile
          (M.constantContinuation payoff) who :=
        (M.decomposedPayoff_constant
          discount profile payoff who).symm

/-- A stage-Nash payoff with integrable unilateral deviations decomposes on
its singleton through stationary continuation promises. -/
theorem decomposesOn_singleton_stagePayoff_of_isNash
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount1 : discount < 1)
    {profile : Profile G.form.sig}
    (hnash : IsNash G.form (euPreference G.utility) profile)
    (hintegrable : G.form.HasIntegrableDeviations G.utility profile) :
    M.DecomposesOn discount
      ({fun who => G.stagePayoff profile who} : Set (ι → ℝ))
      (fun who => G.stagePayoff profile who) := by
  have hstage : ∀ who,
      UtilityIntegrable G.utility who (G.form.play profile) := hintegrable.base
  let payoff : ι → ℝ := fun who => G.stagePayoff profile who
  refine ⟨profile, M.constantContinuation payoff, ?_, ?_, ?_⟩
  · intro signal
    simp [payoff]
  · exact M.isPromiseKeeping_constant_stagePayoff discount profile hstage
  · exact (M.isEnforceable_constant_iff_isNash
      hdiscount1 profile payoff).2 ⟨hnash, hintegrable⟩

/-- Every singleton stage-Nash payoff with integrable unilateral deviations is
self-generating. -/
theorem selfGenerating_singleton_stagePayoff_of_isNash
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount1 : discount < 1)
    {profile : Profile G.form.sig}
    (hnash : IsNash G.form (euPreference G.utility) profile)
    (hintegrable : G.form.HasIntegrableDeviations G.utility profile) :
    M.SelfGenerating discount
      ({fun who => G.stagePayoff profile who} : Set (ι → ℝ)) := by
  intro promise hpromise
  rw [Set.mem_singleton_iff] at hpromise
  subst promise
  exact M.decomposesOn_singleton_stagePayoff_of_isNash hdiscount1 hnash hintegrable

end UtilityGame.PublicMonitoring

end GameTheory
