/-
# Recursive payoff decomposition under public monitoring

This is the finite-support decomposition surface used in Abreu, Pearce, and
Stacchetti, *Toward a Theory of Discounted Repeated Games with Imperfect
Monitoring*, Econometrica 58(5), 1990, 1041--1063. A current stage profile and
a signal-indexed continuation payoff assignment jointly promise a payoff
vector and deter unilateral current-stage deviations.

The signal law is `FinDist`, so every displayed continuation expectation is a
finite-support expectation even when the signal carrier itself is infinite.
No extra boundedness field is stored in a decomposition certificate; bounds
enter only later, where infinite discounted payoff series require them.
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
    (profile : Profile G.form.sig) (continuation : M.ContinuationAssignment) :
    ι → ℝ :=
  fun who =>
    (1 - discount) * G.stagePayoff profile who +
      discount * (M.signalLaw profile).expect
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
  M.decomposedPayoff discount profile continuation = promise

/-- Every unilateral current-stage action is deterred by the same public
continuation assignment. -/
def IsEnforceable (M : G.PublicMonitoring) [DecidableEq ι]
    (discount : ℝ) (profile : Profile G.form.sig)
    (continuation : M.ContinuationAssignment) : Prop :=
  ∀ who action,
    M.decomposedDeviationPayoff discount profile continuation who action ≤
      M.decomposedPayoff discount profile continuation who

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
    M.decomposedPayoff discount profile (M.constantContinuation payoff) who =
      (1 - discount) * G.stagePayoff profile who +
        discount * payoff who := by
  simp [decomposedPayoff, constantContinuation]

/-- Repeating the current stage-payoff vector as the continuation keeps that
promise for every discount factor. -/
theorem isPromiseKeeping_constant_stagePayoff
    (M : G.PublicMonitoring) (discount : ℝ)
    (profile : Profile G.form.sig) :
    M.IsPromiseKeeping discount (fun who => G.stagePayoff profile who)
      profile (M.constantContinuation fun who => G.stagePayoff profile who) := by
  funext who
  simp
  ring

/-- With a constant continuation and `discount < 1`, APS enforceability is
exactly ordinary stage-game Nash. -/
theorem isEnforceable_constant_iff_isNash
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount1 : discount < 1)
    (profile : Profile G.form.sig) (payoff : ι → ℝ) :
    M.IsEnforceable discount profile (M.constantContinuation payoff) ↔
      IsNash G.form (euPreference G.utility) profile := by
  rw [IsEnforceable, isNash_iff]
  constructor
  · intro henforce who action
    have hdeviation := henforce who action
    simp only [decomposedDeviationPayoff,
      decomposedPayoff_constant] at hdeviation
    rw [euPreference_apply]
    have hbase : G.stagePayoff profile who =
        expectedUtility G.utility who (G.form.play profile) := rfl
    have hupdate : G.stagePayoff (Profile.update profile who action) who =
        expectedUtility G.utility who
          (G.form.play (Profile.update profile who action)) := rfl
    rw [hbase, hupdate] at hdeviation
    nlinarith
  · intro hnash who action
    have hdeviation := hnash who action
    rw [euPreference_apply] at hdeviation
    simp only [decomposedDeviationPayoff,
      decomposedPayoff_constant]
    have hbase : G.stagePayoff profile who =
        expectedUtility G.utility who (G.form.play profile) := rfl
    have hupdate : G.stagePayoff (Profile.update profile who action) who =
        expectedUtility G.utility who
          (G.form.play (Profile.update profile who action)) := rfl
    rw [hbase, hupdate]
    nlinarith

/-- A stage-Nash payoff decomposes on its singleton through stationary
continuation promises. -/
theorem decomposesOn_singleton_stagePayoff_of_isNash
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount1 : discount < 1)
    {profile : Profile G.form.sig}
    (hnash : IsNash G.form (euPreference G.utility) profile) :
    M.DecomposesOn discount
      ({fun who => G.stagePayoff profile who} : Set (ι → ℝ))
      (fun who => G.stagePayoff profile who) := by
  let payoff : ι → ℝ := fun who => G.stagePayoff profile who
  refine ⟨profile, M.constantContinuation payoff, ?_, ?_, ?_⟩
  · intro signal
    simp [payoff]
  · exact M.isPromiseKeeping_constant_stagePayoff discount profile
  · exact (M.isEnforceable_constant_iff_isNash
      hdiscount1 profile payoff).2 hnash

/-- Every singleton stage-Nash payoff is self-generating. -/
theorem selfGenerating_singleton_stagePayoff_of_isNash
    (M : G.PublicMonitoring) [DecidableEq ι]
    {discount : ℝ} (hdiscount1 : discount < 1)
    {profile : Profile G.form.sig}
    (hnash : IsNash G.form (euPreference G.utility) profile) :
    M.SelfGenerating discount
      ({fun who => G.stagePayoff profile who} : Set (ι → ℝ)) := by
  intro promise hpromise
  rw [Set.mem_singleton_iff] at hpromise
  subst promise
  exact M.decomposesOn_singleton_stagePayoff_of_isNash hdiscount1 hnash

end UtilityGame.PublicMonitoring

end GameTheory
