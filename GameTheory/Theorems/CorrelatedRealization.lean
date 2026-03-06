import GameTheory.Model.SemanticForm
import Math.ParameterizedChain

/-! # Correlated realization theorem

For **any** joint distribution `ν : PMF (PureProfile I)` (not necessarily a product),
there exists a **mediator** — a history-dependent correlated action recommendation —
producing the same outcome distribution.  No perfect-recall assumption is needed.

The mediator sees the full state trace and recommends correlated joint actions,
which the dynamics then converts to state transitions.  This separates the
strategic choice (actions) from the physical transition (dynamics).

Decentralizing the mediator into independent per-player behavioral strategies
requires perfect recall (classical Kuhn = correlated realization + decentralization).
-/

set_option autoImplicit false

namespace GameTheory

open Math.ProbabilityMassFunction Math.ParameterizedChain Execution Execution.Dynamics

variable {ι : Type} {M : LSM ι} {I : InfoModel M}

section

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

/-- The parameterized step function extracted from game dynamics:
maps a pure profile and a state trace to a next-state distribution. -/
noncomputable def pureStep (D : Dynamics I) (π : PureProfile I)
    (ss : List M.State) : PMF M.State :=
  D.stepDist (pureToBehavioral I π) ss

/-- `runDistPure` is definitionally equal to `pureRun` applied to `pureStep`. -/
theorem runDistPure_eq_pureRun (D : Dynamics I) (k : Nat) (π : PureProfile I) :
    D.runDistPure k π = pureRun (pureStep D) M.init k π := rfl

/-- Mediator construction: condition `ν` on the probability of reaching
the current state trace, then extract correlated joint actions. -/
noncomputable def mixedToMediator [Fintype (PureProfile I)]
    (ν : PMF (PureProfile I)) (D : Dynamics I)
    (n : Nat) (ss : List M.State) : PMF (JointAction M) :=
  (reweightPMF ν (fun π => pureRun (pureStep D) M.init n π ss)).bind
    (fun π => jointActionDist (pureToBehavioral I π) ss)

/-- The mediator's action recommendations composed with dynamics equal
the `condStep` from `ParameterizedChain` (monad associativity). -/
theorem mediator_step_eq_condStep [Fintype (PureProfile I)]
    (ν : PMF (PureProfile I)) (D : Dynamics I) (n : Nat) (ss : List M.State) :
    (mixedToMediator ν D n ss).bind
      (fun a => D.nextState a ((ss.getLast?).getD M.init)) =
      condStep ν (pureStep D) M.init n ss := by
  unfold mixedToMediator condStep pureStep stepDist
  rw [PMF.bind_bind]

variable [∀ i, Fintype (I.LocalTrace i)]

set_option linter.unusedFintypeInType false in
/-- **Correlated realization theorem**: for any joint distribution `ν` over
pure profiles, there exists a mediator `m` — producing correlated action
recommendations from the state trace at each step — such that the run under `m`
(with actions converted to state transitions by the dynamics) yields the same
outcome distribution as the `ν`-averaged pure runs.

No perfect recall is needed. -/
theorem correlated_realization (D : Dynamics I) (ν : PMF (PureProfile I)) (k : Nat) :
    ∃ m : Nat → List M.State → PMF (JointAction M),
      pushforward
        (seqRun (fun n ss =>
          (m n ss).bind (fun a => D.nextState a ((ss.getLast?).getD M.init)))
          M.init k)
        I.outcomeOfStates =
        ν.bind (fun π => D.evalPure k π) := by
  classical
  refine ⟨mixedToMediator ν D, ?_⟩
  have hstep : (fun n ss =>
      (mixedToMediator ν D n ss).bind
        (fun a => D.nextState a ((ss.getLast?).getD M.init))) =
      condStep ν (pureStep D) M.init := by
    funext n ss
    exact mediator_step_eq_condStep ν D n ss
  rw [hstep, condRun_eq_mixedRun, pushforward_bind]
  rfl

end

/-! ## Observation-level correlated realization

Under **per-step action recall** (the observation transition determines the
action), the state-trace mediator factors through observations, giving a
`BehavioralProfileCorr I` witness.

`PerStepActionRecall` is defined here temporarily; it is intended to move to
`SemanticForm.lean` alongside `ObsRecall` and `ActionRecall`. -/

/-- Per-step action recall: any two transitions with observation-equivalent
source and target states must use the same joint action.  This means the
observation transition uniquely determines the action taken. -/
def PerStepActionRecall (I : InfoModel M) : Prop :=
  ∀ (a a' : JointAction M) (s s' t t' : M.State),
    M.step a s t → M.step a' s' t' →
    (∀ i, I.obsEq i s s') → (∀ i, I.obsEq i t t') →
    a = a'

section ObsLevel

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

/-- `jointActionDist` depends on the state trace only through observations. -/
theorem jointActionDist_obs_invariant
    (σ : BehavioralProfile I) (ss₁ ss₂ : List M.State)
    (hobs : ∀ i, I.projectStates i ss₁ = I.projectStates i ss₂) :
    jointActionDist (I := I) σ ss₁ = jointActionDist (I := I) σ ss₂ := by
  unfold jointActionDist
  congr 1; funext i; rw [hobs]

/-- For pure profiles, `pureStep` is just `D.nextState` at the deterministic
joint action. (Because `jointActionDist` on a pure profile is a point mass.) -/
theorem pureStep_eq (D : Dynamics I) (π : PureProfile I) (ss : List M.State) :
    pureStep D π ss =
      D.nextState (fun i => π i (I.projectStates i ss)) ((ss.getLast?).getD M.init) := by
  unfold pureStep stepDist jointActionDist pureToBehavioral
  simp [Math.PMFProduct.pmfPi_pure, PMF.pure_bind]

/-- Under PSAR, if two profiles produce nonzero transition at the same state
trace and target, their step distributions are equal. -/
theorem pureStep_eq_of_nonzero_same
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    {π₁ π₂ : PureProfile I} {ss : List M.State} {t : M.State}
    (h₁ : pureStep D π₁ ss t ≠ 0) (h₂ : pureStep D π₂ ss t ≠ 0) :
    pureStep D π₁ ss = pureStep D π₂ ss := by
  simp only [pureStep_eq] at h₁ h₂ ⊢
  rw [hPSAR _ _ _ _ _ _
    (D.nextState_sound _ _ _ h₁) (D.nextState_sound _ _ _ h₂)
    (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)]

/-- Under `PerStepActionRecall`, if `pureStep` at obs-equivalent traces gives
nonzero probability to obs-equivalent next states, the actions are equal. -/
theorem pureStep_action_eq_of_psar
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    {π π' : PureProfile I} {ss ss' : List M.State} {t t' : M.State}
    (hobs : ∀ i, I.projectStates i ss = I.projectStates i ss')
    (hobst : ∀ i, I.obsEq i t t')
    (h1 : pureStep D π ss t ≠ 0) (h2 : pureStep D π' ss' t' ≠ 0) :
    (fun i => π i (I.projectStates i ss)) = (fun i => π' i (I.projectStates i ss')) := by
  rw [pureStep_eq] at h1 h2
  have hs1 := D.nextState_sound _ _ _ h1
  have hs2 := D.nextState_sound _ _ _ h2
  have hobss : ∀ i, I.obsEq i ((ss.getLast?).getD M.init) ((ss'.getLast?).getD M.init) := by
    intro i
    have hproj := hobs i
    unfold InfoModel.projectStates InfoModel.projectPublic InfoModel.projectPrivate at hproj
    have hpub : ss.map I.publicView = ss'.map I.publicView := (Prod.ext_iff.mp hproj).1
    have hpriv : ss.map (I.observe i) = ss'.map (I.observe i) := (Prod.ext_iff.mp hproj).2
    constructor
    · -- publicView
      have := congr_arg List.getLast? hpub
      simp only [List.getLast?_map] at this
      cases hss : ss.getLast? <;> cases hss' : ss'.getLast? <;>
        simp_all [Option.map]
    · -- observe i
      have := congr_arg List.getLast? hpriv
      simp only [List.getLast?_map] at this
      cases hss : ss.getLast? <;> cases hss' : ss'.getLast? <;>
        simp_all [Option.map]
  exact hPSAR _ _ _ _ _ _ hs1 hs2 hobss hobst

/-- Under PSAR, `pureStep` satisfies the cross-ratio for obs-equivalent
state traces and obs-equivalent targets. -/
theorem pureStep_cross_ratio
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    {π₁ π₂ : PureProfile I} {ss₁ ss₂ : List M.State} {t₁ t₂ : M.State}
    (hobs : ∀ i, I.projectStates i ss₁ = I.projectStates i ss₂)
    (hobst : ∀ i, I.obsEq i t₁ t₂) :
    pureStep D π₁ ss₁ t₁ * pureStep D π₂ ss₂ t₂ =
      pureStep D π₂ ss₁ t₁ * pureStep D π₁ ss₂ t₂ := by
  -- Actions are the same at obs-equivalent traces for any fixed profile
  have hact₁ : (fun i => π₁ i (I.projectStates i ss₁)) =
      (fun i => π₁ i (I.projectStates i ss₂)) := by funext i; rw [hobs]
  have hact₂ : (fun i => π₂ i (I.projectStates i ss₁)) =
      (fun i => π₂ i (I.projectStates i ss₂)) := by funext i; rw [hobs]
  simp only [pureStep_eq, ← hact₁, ← hact₂]
  -- Now: nextState(a, last ss₁)(t₁) * nextState(b, last ss₂)(t₂) = ...
  -- where a = act(π₁,ss₁), b = act(π₂,ss₁)
  by_cases hab :
      (fun i => π₁ i (I.projectStates i ss₁)) = (fun i => π₂ i (I.projectStates i ss₁))
  · rw [hab]
  · -- If a ≠ b, PSAR forces both products to be zero
    have hobss : ∀ i, I.obsEq i
        ((ss₁.getLast?).getD M.init) ((ss₂.getLast?).getD M.init) := by
      intro i
      have hproj := hobs i
      unfold InfoModel.projectStates InfoModel.projectPublic InfoModel.projectPrivate at hproj
      have hpub : ss₁.map I.publicView = ss₂.map I.publicView := (Prod.ext_iff.mp hproj).1
      have hpriv : ss₁.map (I.observe i) = ss₂.map (I.observe i) := (Prod.ext_iff.mp hproj).2
      constructor
      · have := congrArg List.getLast? hpub
        simp only [List.getLast?_map] at this
        cases hss : ss₁.getLast? <;> cases hss' : ss₂.getLast? <;>
          simp_all [Option.map, Option.getD]
      · have := congrArg List.getLast? hpriv
        simp only [List.getLast?_map] at this
        cases hss : ss₁.getLast? <;> cases hss' : ss₂.getLast? <;>
          simp_all [Option.map, Option.getD]
    have hL : D.nextState (fun i => π₁ i (I.projectStates i ss₁))
          ((ss₁.getLast?).getD M.init) t₁ *
        D.nextState (fun i => π₂ i (I.projectStates i ss₁))
          ((ss₂.getLast?).getD M.init) t₂ = 0 := by
      by_contra h
      rw [mul_eq_zero, not_or] at h
      exact hab (hPSAR _ _ _ _ _ _
        (D.nextState_sound _ _ _ h.1) (D.nextState_sound _ _ _ h.2) hobss hobst)
    have hR : D.nextState (fun i => π₂ i (I.projectStates i ss₁))
          ((ss₁.getLast?).getD M.init) t₁ *
        D.nextState (fun i => π₁ i (I.projectStates i ss₁))
          ((ss₂.getLast?).getD M.init) t₂ = 0 := by
      by_contra h
      rw [mul_eq_zero, not_or] at h
      exact hab (hPSAR _ _ _ _ _ _
        (D.nextState_sound _ _ _ h.1) (D.nextState_sound _ _ _ h.2) hobss hobst).symm
    rw [hL, hR]

variable [Fintype (PureProfile I)] [∀ i, Fintype (I.LocalTrace i)]

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
/-- Under PSAR, pureRun satisfies the pairwise cross-ratio for
obs-equivalent traces: the reach probability ratio is profile-independent.
Proof: by induction on k, using `pureStep_eq_of_nonzero_same` for the
same-state case and `pureStep_action_eq_of_psar` for cross-state. -/
theorem pureRun_pairwise_cross_of_psar
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    (k : Nat) (π₁ π₂ : PureProfile I) (ss₁ ss₂ : List M.State)
    (hobs : ∀ i, I.projectStates i ss₁ = I.projectStates i ss₂) :
    pureRun (pureStep D) M.init k π₁ ss₁ *
      pureRun (pureStep D) M.init k π₂ ss₂ =
    pureRun (pureStep D) M.init k π₂ ss₁ *
      pureRun (pureStep D) M.init k π₁ ss₂ := by
  induction k generalizing ss₁ ss₂ with
  | zero =>
    -- pureRun at 0 = PMF.pure [s₀], independent of π
    simp [pureRun]
  | succ n ih =>
    -- Decompose ss₁ and ss₂ as prefix ++ [last]
    rcases List.eq_nil_or_concat ss₁ with rfl | ⟨p₁, t₁, rfl⟩
    · -- ss₁ = []: pureRun at succ on [] is 0, both sides = 0
      simp only [show ∀ π, pureRun (pureStep D) M.init (n + 1) π ([] : List M.State) = 0 from
        fun π => pureRun_succ_nil (pureStep D) M.init n π, zero_mul]
    · rcases List.eq_nil_or_concat ss₂ with rfl | ⟨p₂, t₂, rfl⟩
      · -- ss₂ = []: similar
        simp only [show ∀ π, pureRun (pureStep D) M.init (n + 1) π ([] : List M.State) = 0 from
          fun π => pureRun_succ_nil (pureStep D) M.init n π, mul_zero]
      · -- Main case: ss₁ = p₁ ++ [t₁], ss₂ = p₂ ++ [t₂]
        simp only [List.concat_eq_append] at hobs ⊢
        simp only [pureRun_succ_append]
        -- Goal: R(n,π₁,p₁)*S(π₁,p₁,t₁) * (R(n,π₂,p₂)*S(π₂,p₂,t₂)) =
        --       R(n,π₂,p₁)*S(π₂,p₁,t₁) * (R(n,π₁,p₂)*S(π₁,p₂,t₂))
        -- Extract obs-equiv of prefixes and last elements
        have hobs_prefix : ∀ i, I.projectStates i p₁ = I.projectStates i p₂ := by
          intro i; have hi := hobs i
          simp only [InfoModel.projectStates, InfoModel.projectPublic,
            InfoModel.projectPrivate, List.map_append, List.map_cons, List.map_nil] at hi
          exact Prod.ext
            (Math.ParameterizedChain.append_singleton_inj (Prod.ext_iff.mp hi).1).1
            (Math.ParameterizedChain.append_singleton_inj (Prod.ext_iff.mp hi).2).1
        have hobs_last : ∀ i, I.obsEq i t₁ t₂ := by
          intro i; have hi := hobs i
          simp only [InfoModel.projectStates, InfoModel.projectPublic,
            InfoModel.projectPrivate, List.map_append, List.map_cons, List.map_nil] at hi
          exact ⟨(Math.ParameterizedChain.append_singleton_inj (Prod.ext_iff.mp hi).1).2,
                 (Math.ParameterizedChain.append_singleton_inj (Prod.ext_iff.mp hi).2).2⟩
        -- Use IH for prefixes and step cross-ratio for last elements
        have hIH := ih p₁ p₂ hobs_prefix
        have hStep := pureStep_cross_ratio hPSAR D hobs_prefix hobs_last
          (π₁ := π₁) (π₂ := π₂) (t₁ := t₁) (t₂ := t₂)
        -- Combine: (a₁*b₁)*(a₂*b₂) = (a₁*a₂)*(b₁*b₂)
        --        = (a₃*a₄)*(b₃*b₄) = (a₃*b₃)*(a₄*b₄) by rearrangement
        calc pureRun (pureStep D) M.init n π₁ p₁ * pureStep D π₁ p₁ t₁ *
              (pureRun (pureStep D) M.init n π₂ p₂ * pureStep D π₂ p₂ t₂)
            = (pureRun (pureStep D) M.init n π₁ p₁ *
                pureRun (pureStep D) M.init n π₂ p₂) *
              (pureStep D π₁ p₁ t₁ * pureStep D π₂ p₂ t₂) := by ring
          _ = (pureRun (pureStep D) M.init n π₂ p₁ *
                pureRun (pureStep D) M.init n π₁ p₂) *
              (pureStep D π₂ p₁ t₁ * pureStep D π₁ p₂ t₂) := by rw [hIH, hStep]
          _ = pureRun (pureStep D) M.init n π₂ p₁ * pureStep D π₂ p₁ t₁ *
              (pureRun (pureStep D) M.init n π₁ p₂ * pureStep D π₁ p₂ t₂) := by ring

set_option linter.unusedFintypeInType false in
/-- Under `PerStepActionRecall`, for obs-equivalent state traces, the
`reweightPMF` on reach probabilities gives the same distribution. -/
theorem reweightPMF_pureRun_obs_invariant
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    (ν : PMF (PureProfile I)) (n : Nat)
    (ss₁ ss₂ : List M.State)
    (hobs : ∀ i, I.projectStates i ss₁ = I.projectStates i ss₂)
    (hreach₁ : ∑ π : PureProfile I, ν π * pureRun (pureStep D) M.init n π ss₁ ≠ 0)
    (hreach₂ : ∑ π : PureProfile I, ν π * pureRun (pureStep D) M.init n π ss₂ ≠ 0) :
    reweightPMF ν (fun π => pureRun (pureStep D) M.init n π ss₁) =
    reweightPMF ν (fun π => pureRun (pureStep D) M.init n π ss₂) := by
  have hCtop₁ : ∑ π, ν π * pureRun (pureStep D) M.init n π ss₁ ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show (1 : ENNReal) ≠ ⊤ from ENNReal.one_ne_top)
    calc ∑ π, ν π * pureRun (pureStep D) M.init n π ss₁
        ≤ ∑ π, ν π := Finset.sum_le_sum fun π _ => by
          calc ν π * _ ≤ ν π * 1 := by gcongr; exact PMF.coe_le_one _ _
            _ = ν π := mul_one _
      _ = 1 := by have := PMF.tsum_coe ν; rwa [tsum_fintype] at this
  have hCtop₂ : ∑ π, ν π * pureRun (pureStep D) M.init n π ss₂ ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show (1 : ENNReal) ≠ ⊤ from ENNReal.one_ne_top)
    calc ∑ π, ν π * pureRun (pureStep D) M.init n π ss₂
        ≤ ∑ π, ν π := Finset.sum_le_sum fun π _ => by
          calc ν π * _ ≤ ν π * 1 := by gcongr; exact PMF.coe_le_one _ _
            _ = ν π := mul_one _
      _ = 1 := by have := PMF.tsum_coe ν; rwa [tsum_fintype] at this
  apply Math.ParameterizedChain.reweightPMF_eq_of_cross_mul ν _ _ hreach₁ hCtop₁ hreach₂ hCtop₂
  intro π
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro π' _
  have h := pureRun_pairwise_cross_of_psar hPSAR D n π π' ss₁ ss₂ hobs
  calc pureRun (pureStep D) M.init n π ss₁ * (ν π' * pureRun (pureStep D) M.init n π' ss₂)
      = ν π' * (pureRun (pureStep D) M.init n π ss₁ * pureRun (pureStep D) M.init n π' ss₂) :=
        by ac_rfl
    _ = ν π' * (pureRun (pureStep D) M.init n π' ss₁ * pureRun (pureStep D) M.init n π ss₂) :=
        by rw [h]
    _ = pureRun (pureStep D) M.init n π ss₂ * (ν π' * pureRun (pureStep D) M.init n π' ss₁) :=
        by ac_rfl

set_option linter.unusedFintypeInType false in
/-- Under `PerStepActionRecall`, the state-trace mediator at obs-equivalent
reachable traces produces the same action distribution. -/
theorem mixedToMediator_obs_invariant
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    (ν : PMF (PureProfile I)) (n : Nat)
    (ss₁ ss₂ : List M.State)
    (hobs : ∀ i, I.projectStates i ss₁ = I.projectStates i ss₂)
    (hreach₁ : ∑ π : PureProfile I, ν π * pureRun (pureStep D) M.init n π ss₁ ≠ 0)
    (hreach₂ : ∑ π : PureProfile I, ν π * pureRun (pureStep D) M.init n π ss₂ ≠ 0) :
    mixedToMediator ν D n ss₁ = mixedToMediator ν D n ss₂ := by
  unfold mixedToMediator
  rw [reweightPMF_pureRun_obs_invariant hPSAR D ν n ss₁ ss₂ hobs hreach₁ hreach₂]
  congr 1; funext π
  exact jointActionDist_obs_invariant (pureToBehavioral I π) ss₁ ss₂ hobs

end ObsLevel

section ObsCorrelatedRealization

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
variable [Fintype (PureProfile I)] [∀ i, Fintype (I.LocalTrace i)]

set_option linter.unusedSectionVars false in
/-- Obs-equivalent state traces have the same length (via publicView map). -/
theorem projectStates_eq_length (i : ι) {ss₁ ss₂ : List M.State}
    (h : I.projectStates i ss₁ = I.projectStates i ss₂) :
    ss₁.length = ss₂.length := by
  have := congr_arg (fun p => p.1.length) h
  simp only [InfoModel.projectStates, InfoModel.projectPublic, List.length_map] at this
  exact this

set_option linter.unusedSectionVars false in
set_option linter.unusedFintypeInType false in
open Classical in
/-- **Observation-level correlated realization**: under `PerStepActionRecall`,
a `BehavioralProfileCorr I` (observation-level mediator) produces the same
outcome distribution as any mixed strategy `ν`. -/
theorem obs_correlated_realization [Inhabited ι]
    (hPSAR : PerStepActionRecall I)
    (D : Dynamics I) (ν : PMF (PureProfile I)) (k : Nat) :
    ∃ σ : BehavioralProfileCorr I,
      pushforward
        (seqRun (fun _ ss => D.stepDistCorr σ ss) M.init k)
        I.outcomeOfStates =
        ν.bind (fun π => D.evalPure k π) := by
  -- Define obs-level mediator: pick a reachable representative state trace
  let σ : BehavioralProfileCorr I := fun v =>
    if h : ∃ ss : List M.State,
          (∀ i, I.projectStates i ss = v i) ∧
          ∑ π : PureProfile I, ν π * pureRun (pureStep D) M.init (ss.length - 1) π ss ≠ 0
    then mixedToMediator ν D (h.choose.length - 1) h.choose
    else PMF.pure (fun _ => none)
  refine ⟨σ, ?_⟩
  -- Suffices: seqRun under σ = seqRun under condStep
  suffices hsuff : seqRun (fun _ ss => D.stepDistCorr σ ss) M.init k =
      seqRun (condStep ν (pureStep D) M.init) M.init k by
    rw [hsuff, condRun_eq_mixedRun, pushforward_bind]
    rfl
  -- Key lemma: step functions agree on the support
  suffices hfn : ∀ (n : Nat) (ss : List M.State),
      (seqRun (condStep ν (pureStep D) M.init) M.init n) ss ≠ 0 →
      D.stepDistCorr σ ss = condStep ν (pureStep D) M.init n ss by
    -- Induction on k
    induction k with
    | zero => rfl
    | succ n ih =>
      change (seqRun (fun _ ss => D.stepDistCorr σ ss) M.init n).bind
            (fun ss => pushforward (D.stepDistCorr σ ss) (fun t => ss ++ [t])) =
          (seqRun (condStep ν (pureStep D) M.init) M.init n).bind
            (fun ss => pushforward (condStep ν (pureStep D) M.init n ss)
              (fun t => ss ++ [t]))
      rw [ih]
      ext y
      simp only [PMF.bind_apply]
      apply tsum_congr
      intro ss
      by_cases hss : (seqRun (condStep ν (pureStep D) M.init) M.init n) ss = 0
      · simp [hss]
      · rw [hfn n ss hss]
  -- Prove hfn
  intro n ss hss
  -- 1. ss is reachable at step n
  have hreach : ∑ π, ν π * pureRun (pureStep D) M.init n π ss ≠ 0 := by
    rwa [condRun_eq_mixedRun, PMF.bind_apply, tsum_fintype] at hss
  -- 2. ss.length = n + 1
  have hlen : ss.length = n + 1 := by
    obtain ⟨π, _, hπ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hreach
    exact pureRun_length (pureStep D) M.init n π ss (right_ne_zero_of_mul hπ)
  -- 3. σ(projectStates(ss)) = mixedToMediator ν D n ss
  have hσ : σ (fun i => I.projectStates i ss) = mixedToMediator ν D n ss := by
    -- The existential is satisfied by ss itself
    have hexist : ∃ ss' : List M.State,
        (∀ i, I.projectStates i ss' = I.projectStates i ss) ∧
        ∑ π, ν π * pureRun (pureStep D) M.init (ss'.length - 1) π ss' ≠ 0 :=
      ⟨ss, fun _ => rfl, by rwa [show ss.length - 1 = n from by omega]⟩
    change (if h : ∃ ss' : List M.State,
        (∀ i, I.projectStates i ss' = (fun i => I.projectStates i ss) i) ∧
        ∑ π, ν π * pureRun (pureStep D) M.init (ss'.length - 1) π ss' ≠ 0
      then mixedToMediator ν D (h.choose.length - 1) h.choose
      else PMF.pure (fun _ => none)) = _
    rw [dif_pos hexist]
    -- hexist.choose has same projections and is reachable
    set ss' := hexist.choose with hss'_def
    have hobs' := hexist.choose_spec.1
    have hreach' := hexist.choose_spec.2
    -- ss'.length = ss.length (from obs-equiv via publicView)
    have hlen' : ss'.length = ss.length :=
      projectStates_eq_length (default : ι) (hobs' default)
    -- ss'.length - 1 = n
    have hn' : ss'.length - 1 = n := by omega
    rw [hn']
    exact mixedToMediator_obs_invariant hPSAR D ν n ss' ss hobs'
      (by rwa [hn'] at hreach') hreach
  -- 4. stepDistCorr σ ss = condStep ... n ss
  calc D.stepDistCorr σ ss
      = (σ (fun i => I.projectStates i ss)).bind
          (fun a => D.nextState a ((ss.getLast?).getD M.init)) := rfl
    _ = (mixedToMediator ν D n ss).bind
          (fun a => D.nextState a ((ss.getLast?).getD M.init)) := by rw [hσ]
    _ = condStep ν (pureStep D) M.init n ss := mediator_step_eq_condStep ν D n ss

end ObsCorrelatedRealization

/-! ## Per-step player recall

`PerStepPlayerRecall` is the per-player version of `PerStepActionRecall`:
each player's action component is determined by their own observation
transition (not requiring other players' observations). -/

/-- Per-step player recall: each player's action is determined by
their own observation transition alone. -/
def PerStepPlayerRecall (I : InfoModel M) : Prop :=
  ∀ (i : ι) (a a' : JointAction M) (s s' t t' : M.State),
    M.step a s t → M.step a' s' t' →
    I.obsEq i s s' → I.obsEq i t t' →
    a i = a' i

/-- `PerStepPlayerRecall` implies `PerStepActionRecall`. -/
theorem PerStepPlayerRecall.toAction (h : PerStepPlayerRecall I) :
    PerStepActionRecall I :=
  fun a a' s s' t t' hs hs' hobs hobst =>
    funext fun i => h i a a' s s' t t' hs hs' (hobs i) (hobst i)

/-- Under `PerStepActionRecall`, at most one action can produce a nonzero
transition probability between any pair of states. -/
theorem action_unique_of_psar
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    {a a' : JointAction M} {s t : M.State}
    (ha : D.nextState a s t ≠ 0) (ha' : D.nextState a' s t ≠ 0) :
    a = a' :=
  hPSAR a a' s s t t (D.nextState_sound a s t ha) (D.nextState_sound a' s t ha')
    (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)

/-- Under `PerStepPlayerRecall`, player `i`'s action component is determined by
their own observation at source and target. -/
theorem action_component_unique_of_pspr
    (hPSPR : PerStepPlayerRecall I) (D : Dynamics I)
    (i : ι) {a a' : JointAction M} {s s' t t' : M.State}
    (ha : D.nextState a s t ≠ 0) (ha' : D.nextState a' s' t' ≠ 0)
    (hobs : I.obsEq i s s') (hobst : I.obsEq i t t') :
    a i = a' i :=
  hPSPR i a a' s s' t t' (D.nextState_sound a s t ha) (D.nextState_sound a' s' t' ha')
    hobs hobst

/-! ## Reach factoring under PSAR

Under `PerStepActionRecall`, the reach probability `pureRun(pureStep D, s₀, n, π, ss)`
depends on `π` only through whether `π` produces the uniquely forced action at each
step. This gives:

1. **Constancy**: nonzero reach probabilities are equal across all profiles
2. **Per-player factoring**: the nonzero condition factors as `∀ i, π_i consistent`
3. **Product preservation**: reweighting a product measure by reach gives a product -/

section ReachFactor

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

/-- Under PSAR, nonzero reach probabilities at the same trace are equal.
If two profiles both reach `ss` with nonzero probability, they must produce
the same action at every step, hence have the same reach probability. -/
theorem pureRun_const_of_psar
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    (n : Nat) {π π' : PureProfile I} {ss : List M.State}
    (h : pureRun (pureStep D) M.init n π ss ≠ 0)
    (h' : pureRun (pureStep D) M.init n π' ss ≠ 0) :
    pureRun (pureStep D) M.init n π ss =
      pureRun (pureStep D) M.init n π' ss := by
  induction n generalizing ss with
  | zero => simp [pureRun] at h h' ⊢
  | succ k ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h
    · simp only [List.concat_eq_append, pureRun_succ_append] at h h' ⊢
      have hp := left_ne_zero_of_mul h
      have hp' := left_ne_zero_of_mul h'
      have ht := right_ne_zero_of_mul h
      have ht' := right_ne_zero_of_mul h'
      rw [ih hp hp',
          pureStep_eq_of_nonzero_same hPSAR D ht ht']

/-- Under PSAR, at a reachable transition, `pureStep` is nonzero iff
the profile produces the same action as any fixed witness profile. -/
theorem pureStep_nonzero_iff_action_eq
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    {π₀ : PureProfile I} {ss : List M.State} {t : M.State}
    (h₀ : pureStep D π₀ ss t ≠ 0) (π : PureProfile I) :
    pureStep D π ss t ≠ 0 ↔
      (fun i => π i (I.projectStates i ss)) =
        (fun i => π₀ i (I.projectStates i ss)) := by
  constructor
  · intro hne
    rw [pureStep_eq] at hne h₀
    exact hPSAR _ _ _ _ _ _
      (D.nextState_sound _ _ _ hne) (D.nextState_sound _ _ _ h₀)
      (fun _ => ⟨rfl, rfl⟩) (fun _ => ⟨rfl, rfl⟩)
  · intro heq
    rwa [pureStep_eq, heq, ← pureStep_eq]

/-- Under PSAR, `pureRun` is nonzero iff the profile produces the same
action as the witness at every step (prefix). The condition is:
at each prefix `p ++ [t]` of `ss`, the profile agrees on the action at `p`. -/
theorem pureRun_nonzero_iff_action_eq
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    (n : Nat) {π₀ : PureProfile I} {ss : List M.State}
    (h₀ : pureRun (pureStep D) M.init n π₀ ss ≠ 0) (π : PureProfile I) :
    pureRun (pureStep D) M.init n π ss ≠ 0 ↔
      (pureRun (pureStep D) M.init n π ss =
        pureRun (pureStep D) M.init n π₀ ss) := by
  constructor
  · exact fun h => pureRun_const_of_psar hPSAR D n h h₀
  · intro heq; rw [heq]; exact h₀

/-- Under PSAR, `pureStep D π ss t` factors per-player: it is nonzero iff
each player `i` individually produces the forced action component. -/
theorem pureStep_nonzero_iff_forall_player
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    {π₀ : PureProfile I} {ss : List M.State} {t : M.State}
    (h₀ : pureStep D π₀ ss t ≠ 0) (π : PureProfile I) :
    pureStep D π ss t ≠ 0 ↔
      ∀ i, π i (I.projectStates i ss) = π₀ i (I.projectStates i ss) := by
  rw [pureStep_nonzero_iff_action_eq hPSAR D h₀]
  exact ⟨fun h i => congr_fun h i, funext⟩

/-- Under PSAR, `pureRun` factors into a trace-dependent constant times a
per-player consistency indicator. If `π` is consistent (nonzero reach),
the reach value equals the witness; otherwise it's zero. -/
theorem pureRun_eq_const_mul_indicator
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    (n : Nat) (π₀ : PureProfile I) (ss : List M.State)
    (h₀ : pureRun (pureStep D) M.init n π₀ ss ≠ 0)
    (π : PureProfile I) :
    pureRun (pureStep D) M.init n π ss =
      if pureRun (pureStep D) M.init n π ss ≠ 0
      then pureRun (pureStep D) M.init n π₀ ss
      else 0 := by
  split
  · exact pureRun_const_of_psar hPSAR D n ‹_› h₀
  · push_neg at *; exact le_antisymm (le_of_eq ‹_›) (zero_le _)

/-- Under PSAR, `pureRun` nonzero is equivalent to matching the witness action
at every prefix. Stated inductively: nonzero at `p ++ [t]` iff nonzero at `p`
and action matches at `p`. -/
theorem pureRun_succ_nonzero_iff
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    (m : Nat) {π₀ : PureProfile I} {p : List M.State} {t : M.State}
    (h₀ : pureRun (pureStep D) M.init (m + 1) π₀ (p ++ [t]) ≠ 0)
    (π : PureProfile I) :
    pureRun (pureStep D) M.init (m + 1) π (p ++ [t]) ≠ 0 ↔
      pureRun (pureStep D) M.init m π p ≠ 0 ∧
        ∀ i, π i (I.projectStates i p) = π₀ i (I.projectStates i p) := by
  simp only [pureRun_succ_append] at h₀ ⊢
  have hp₀ := left_ne_zero_of_mul h₀
  have ht₀ := right_ne_zero_of_mul h₀
  constructor
  · intro hne
    exact ⟨left_ne_zero_of_mul hne,
      (pureStep_nonzero_iff_forall_player hPSAR D ht₀ π).mp
        (right_ne_zero_of_mul hne)⟩
  · intro ⟨hp, hall⟩
    exact mul_ne_zero hp
      ((pureStep_nonzero_iff_forall_player hPSAR D ht₀ π).mpr hall)

/-- Under PSAR, `pureStep` is invariant under changing players who produce
the same action. If `π` and `π'` agree on the action at `ss` (all players
give the same action component), then `pureStep D π ss = pureStep D π' ss`. -/
theorem pureStep_eq_of_action_eq (D : Dynamics I)
    {π π' : PureProfile I} {ss : List M.State}
    (h : ∀ i, π i (I.projectStates i ss) = π' i (I.projectStates i ss)) :
    pureStep D π ss = pureStep D π' ss := by
  simp only [pureStep_eq, funext h]

open Classical in
/-- Under PSAR, reach factors per-player via `Function.update`:
`pureRun π ss ≠ 0` iff for each player `i`, swapping just player `i`'s
component from `π` into the witness `π₀` still gives nonzero reach.

This is the cleanest per-player factoring: each player's consistency
can be tested independently. -/
theorem pureRun_nonzero_iff_update
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    (n : Nat) {π₀ : PureProfile I} {ss : List M.State}
    (h₀ : pureRun (pureStep D) M.init n π₀ ss ≠ 0)
    (π : PureProfile I) :
    pureRun (pureStep D) M.init n π ss ≠ 0 ↔
      ∀ i, pureRun (pureStep D) M.init n
        (Function.update π₀ i (π i)) ss ≠ 0 := by
  induction n generalizing ss with
  | zero =>
    simp only [pureRun, ne_eq] at h₀ ⊢
    exact ⟨fun _ _ => h₀, fun _ => h₀⟩
  | succ m ih =>
    rcases List.eq_nil_or_concat ss with rfl | ⟨p, t, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h₀
    · simp only [List.concat_eq_append] at h₀ ⊢
      have hp₀ : pureRun (pureStep D) M.init m π₀ p ≠ 0 := by
        rw [pureRun_succ_append] at h₀; exact left_ne_zero_of_mul h₀
      rw [pureRun_succ_nonzero_iff hPSAR D m h₀]
      constructor
      · -- Forward: π consistent → each update consistent
        intro ⟨hp, hact⟩ i
        exact (pureRun_succ_nonzero_iff hPSAR D m h₀
          (Function.update π₀ i (π i))).mpr
          ⟨(ih hp₀).mp hp i, fun j => by
            by_cases hij : j = i
            · subst hij; simp [Function.update_self, hact]
            · simp [Function.update_of_ne hij]⟩
      · -- Backward: each update consistent → π consistent
        intro hall
        constructor
        · exact (ih hp₀).mpr fun i =>
            ((pureRun_succ_nonzero_iff hPSAR D m h₀ _).mp (hall i)).1
        · intro i
          have := ((pureRun_succ_nonzero_iff hPSAR D m h₀ _).mp (hall i)).2 i
          simp only [Function.update_self] at this
          exact this

end ReachFactor

section Decentralization

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

/-- Generalized step-independence-to-outcome theorem: if a behavioral profile
`σ` satisfies the step-independence property with respect to any
`ν : PMF (PureProfile I)` (not necessarily a product), then
`evalBehavioral k σ = ν.bind (evalPure k)`.

This generalizes `evalBehavioral_eq_mixed_of_stepIndependence` from
`KuhnCore.lean` by replacing `mixedJoint μ` with an arbitrary `ν`. -/
theorem evalBehavioral_eq_of_stepIndependence
    (D : Dynamics I) (ν : PMF (PureProfile I))
    (σ : BehavioralProfile I)
    (hStep : ∀ n,
      ν.bind (fun π =>
        (D.runDistPure n π).bind (fun ss =>
          pushforward (D.stepDist σ ss) (fun t => ss ++ [t]))) =
      ν.bind (fun π =>
        (D.runDistPure n π).bind (fun ss =>
          pushforward (D.stepDist (pureToBehavioral I π) ss)
            (fun t => ss ++ [t])))) (k : Nat) :
    D.evalBehavioral k σ = ν.bind (D.evalPure k) := by
  have hrun : ∀ n,
      D.runDist n σ = ν.bind (fun π => D.runDistPure n π) := by
    intro n
    induction n with
    | zero => simp [runDist, runDistPure]
    | succ n ih =>
      calc D.runDist (n + 1) σ
          = (D.runDist n σ).bind (fun ss =>
              pushforward (D.stepDist σ ss) (fun t => ss ++ [t])) := by
            simp [runDist]
        _ = (ν.bind (fun π => D.runDistPure n π)).bind (fun ss =>
              pushforward (D.stepDist σ ss) (fun t => ss ++ [t])) := by rw [ih]
        _ = ν.bind (fun π =>
              (D.runDistPure n π).bind (fun ss =>
                pushforward (D.stepDist σ ss) (fun t => ss ++ [t]))) := by
            rw [PMF.bind_bind]
        _ = ν.bind (fun π =>
              (D.runDistPure n π).bind (fun ss =>
                pushforward (D.stepDist (pureToBehavioral I π) ss)
                  (fun t => ss ++ [t]))) := by simpa using hStep n
        _ = ν.bind (fun π => D.runDistPure (n + 1) π) := by
            simp [runDist, runDistPure]
  calc D.evalBehavioral k σ
      = pushforward (D.runDist k σ) I.outcomeOfStates := rfl
    _ = pushforward (ν.bind (fun π => D.runDistPure k π)) I.outcomeOfStates := by
        rw [hrun]
    _ = ν.bind (D.evalPure k) := by
        simpa [evalPure] using
          pushforward_bind (μ := ν) (k := fun π => D.runDistPure k π)
            (f := I.outcomeOfStates)

/-- Under `PerStepPlayerRecall`, the pure-step action component for player `i`
depends only on player `i`'s observation at obs-equivalent traces. -/
theorem pureStep_component_eq_of_pspr
    (hPSPR : PerStepPlayerRecall I) (D : Dynamics I)
    (i : ι) {π π' : PureProfile I} {ss ss' : List M.State} {t t' : M.State}
    (hobs_i : I.projectStates i ss = I.projectStates i ss')
    (hobst_i : I.obsEq i t t')
    (h1 : pureStep D π ss t ≠ 0) (h2 : pureStep D π' ss' t' ≠ 0) :
    π i (I.projectStates i ss) = π' i (I.projectStates i ss') := by
  rw [pureStep_eq] at h1 h2
  have hs1 := D.nextState_sound _ _ _ h1
  have hs2 := D.nextState_sound _ _ _ h2
  have hobss_i : I.obsEq i ((ss.getLast?).getD M.init) ((ss'.getLast?).getD M.init) := by
    have hproj := hobs_i
    unfold InfoModel.projectStates InfoModel.projectPublic InfoModel.projectPrivate at hproj
    have hpub : ss.map I.publicView = ss'.map I.publicView := (Prod.ext_iff.mp hproj).1
    have hpriv : ss.map (I.observe i) = ss'.map (I.observe i) := (Prod.ext_iff.mp hproj).2
    constructor
    · have := congr_arg List.getLast? hpub
      simp only [List.getLast?_map] at this
      cases hss : ss.getLast? <;> cases hss' : ss'.getLast? <;>
        simp_all [Option.map]
    · have := congr_arg List.getLast? hpriv
      simp only [List.getLast?_map] at this
      cases hss : ss.getLast? <;> cases hss' : ss'.getLast? <;>
        simp_all [Option.map]
  exact hPSPR i _ _ _ _ _ _ hs1 hs2 hobss_i hobst_i

end Decentralization

section ProductPreservation

open Math.PMFProduct

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]
variable [∀ i, Fintype (I.LocalTrace i)]

open Classical in
/-- Under PSAR, the reach weight `pureRun π ss` satisfies the cross-multiplication
identity with the per-player product weight `∏ᵢ pureRun (update π₀ i (π i)) ss`.
This allows switching between them via `reweightPMF_eq_of_cross_mul`. -/
theorem pureRun_cross_mul_product
    (hPSAR : PerStepActionRecall I) (D : Dynamics I) (ν : PMF (PureProfile I))
    (n : Nat) {π₀ : PureProfile I} {ss : List M.State}
    (h₀ : pureRun (pureStep D) M.init n π₀ ss ≠ 0) (π : PureProfile I) :
    pureRun (pureStep D) M.init n π ss *
      (∑ π' : PureProfile I, ν π' *
        ∏ i, pureRun (pureStep D) M.init n (Function.update π₀ i (π' i)) ss) =
    (∏ i, pureRun (pureStep D) M.init n (Function.update π₀ i (π i)) ss) *
      (∑ π' : PureProfile I, ν π' *
        pureRun (pureStep D) M.init n π' ss) := by
  set C₀ := pureRun (pureStep D) M.init n π₀ ss with hC₀_def
  -- Helper: for consistent π', the reach equals C₀
  have hconst : ∀ π', pureRun (pureStep D) M.init n π' ss ≠ 0 →
      pureRun (pureStep D) M.init n π' ss = C₀ :=
    fun π' h => pureRun_const_of_psar hPSAR D n h h₀
  -- Helper: for consistent π', each per-player weight equals C₀
  have hconst_upd : ∀ (π' : PureProfile I) (i : ι),
      pureRun (pureStep D) M.init n (Function.update π₀ i (π' i)) ss ≠ 0 →
      pureRun (pureStep D) M.init n (Function.update π₀ i (π' i)) ss = C₀ :=
    fun π' i h => pureRun_const_of_psar hPSAR D n h h₀
  -- Distribute multiplication into sums
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro π' _
  -- Pointwise: w(π) * (ν π' * ∏ wᵢ(π'ᵢ)) = (∏ wᵢ(πᵢ)) * (ν π' * w(π'))
  -- Case split on consistency of π and π'
  by_cases hπ : pureRun (pureStep D) M.init n π ss = 0
  · -- π not consistent: w(π) = 0 and ∏ wᵢ(πᵢ) = 0
    rw [hπ, zero_mul]
    have := mt (pureRun_nonzero_iff_update hPSAR D n h₀ π).mpr
      (not_not.mpr hπ)
    push_neg at this; obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, zero_mul]
  · by_cases hπ' : pureRun (pureStep D) M.init n π' ss = 0
    · -- π' not consistent: w(π') = 0 and ∏ wᵢ(π'ᵢ) = 0
      rw [hπ', mul_zero, mul_zero]
      have := mt (pureRun_nonzero_iff_update hPSAR D n h₀ π').mpr
        (not_not.mpr hπ')
      push_neg at this; obtain ⟨j, hj⟩ := this
      rw [Finset.prod_eq_zero (Finset.mem_univ j) hj, mul_zero, mul_zero]
    · -- Both consistent: all values equal C₀
      have hw := hconst π hπ; have hw' := hconst π' hπ'
      have hwi : ∀ i, pureRun (pureStep D) M.init n
          (Function.update π₀ i (π i)) ss = C₀ :=
        fun i => hconst_upd π i
          ((pureRun_nonzero_iff_update hPSAR D n h₀ π).mp hπ i)
      have hwi' : ∀ i, pureRun (pureStep D) M.init n
          (Function.update π₀ i (π' i)) ss = C₀ :=
        fun i => hconst_upd π' i
          ((pureRun_nonzero_iff_update hPSAR D n h₀ π').mp hπ' i)
      rw [hw, hw']; simp_rw [hwi, hwi']; ring

open Classical in
set_option linter.unusedFintypeInType false in
/-- Under PSAR, when `ν = pmfPi σ` (product of per-player strategy distributions)
and the trace `ss` is reachable, the mediator `mixedToMediator ν D n ss` produces
a **product** action distribution: the recommended actions are independent across
players.

This is the "product in → product out" property: independence of the input
strategy distribution is preserved by the mediator construction. Combined with
the observation-level realization, this gives the independent behavioral profile
(Kuhn's theorem for the mixed → behavioral direction). -/
theorem mediator_product_of_product
    (hPSAR : PerStepActionRecall I) (D : Dynamics I)
    (σ : ∀ i, PMF (I.LocalTrace i → Option (M.Act i)))
    (n : Nat) (ss : List M.State)
    {π₀ : PureProfile I}
    (h₀ : pureRun (pureStep D) M.init n π₀ ss ≠ 0) :
    ∃ τ : ∀ i, PMF (Option (M.Act i)),
      mixedToMediator (pmfPi σ) D n ss = pmfPi τ := by
  set ν := pmfPi σ with hν_def
  set w : PureProfile I → ENNReal :=
    fun π => pureRun (pureStep D) M.init n π ss
  set wᵢ : ∀ i, (I.LocalTrace i → Option (M.Act i)) → ENNReal :=
    fun i πᵢ => pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss
  -- Reduce to: reweightPMF ν w is a product PMF
  -- The mediator is a pushforward of (reweightPMF ν w) through the coordwise map
  -- fun π i => π i (projectStates i ss), and pushforward of product
  -- = product (pmfPi_push_coordwise)
  suffices hprod : ∃ ρ : ∀ i, PMF (I.LocalTrace i → Option (M.Act i)),
      reweightPMF ν w = pmfPi ρ by
    obtain ⟨ρ, hρ⟩ := hprod
    exact ⟨fun i => Math.PMFProduct.pushforward (ρ i) (fun πᵢ => πᵢ (I.projectStates i ss)), by
      unfold mixedToMediator; rw [hρ]
      simp only [jointActionDist, pureToBehavioral]
      conv_lhs => arg 2; ext π; rw [pmfPi_pure]
      exact pmfPi_push_coordwise ρ (fun i πᵢ => πᵢ (I.projectStates i ss))⟩
  -- Case split on mass condition for reweightPMF
  by_cases hmass : (∑ π, ν π * w π) = 0 ∨ (∑ π, ν π * w π) = ⊤
  · -- Degenerate: reweightPMF falls back to ν = pmfPi σ
    exact ⟨σ, by rw [reweightPMF_degenerate _ _ hmass, hν_def]⟩
  · -- Non-degenerate: use cross-multiplication to factor the reweighted PMF
    push_neg at hmass; obtain ⟨hCw0, hCwt⟩ := hmass
    -- Extract a witness with nonzero mass
    have ⟨π_w, hπw⟩ : ∃ π, ν π * w π ≠ 0 := by
      by_contra hall; push_neg at hall
      exact hCw0 (Finset.sum_eq_zero fun a _ => hall a)
    have hν_ne : ν π_w ≠ 0 := left_ne_zero_of_mul hπw
    have hw_ne : w π_w ≠ 0 := right_ne_zero_of_mul hπw
    -- Per-player non-degeneracy from the witness
    have hσ_ne : ∀ i, σ i (π_w i) ≠ 0 := by
      intro i hi; apply hν_ne
      rw [hν_def, pmfPi_apply]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi
    have hwi_ne : ∀ i, wᵢ i (π_w i) ≠ 0 := by
      intro i; exact ((pureRun_nonzero_iff_update hPSAR D n h₀ π_w).mp hw_ne) i
    have hCwi0 : ∀ i, ∑ a, σ i a * wᵢ i a ≠ 0 := fun i => by
      apply ne_of_gt
      exact lt_of_lt_of_le (pos_iff_ne_zero.mpr (mul_ne_zero (hσ_ne i) (hwi_ne i)))
        (Finset.single_le_sum (f := fun a => σ i a * wᵢ i a)
          (fun _ _ => zero_le _) (Finset.mem_univ (π_w i)))
    have hCwit : ∀ i, ∑ a, σ i a * wᵢ i a ≠ ⊤ := fun i => by
      apply ne_of_lt; calc
        ∑ a, σ i a * wᵢ i a ≤ ∑ a, σ i a :=
          Finset.sum_le_sum fun a _ =>
            mul_le_of_le_one_right (zero_le _)
              (PMF.coe_le_one (pureRun (pureStep D) M.init n
                (Function.update π₀ i a)) ss)
        _ = 1 := by have := PMF.tsum_coe (σ i); rwa [tsum_fintype] at this
        _ < ⊤ := ENNReal.one_lt_top
    -- Non-degeneracy for the product weight ∏ wᵢ
    have hsum_eq : ∑ π, ν π * ∏ i, wᵢ i (π i) = ∏ i, ∑ a, σ i a * wᵢ i a := by
      rw [hν_def]; conv_lhs => arg 2; ext π; rw [pmfPi_apply, ← Finset.prod_mul_distrib]
      exact (Fintype.prod_sum (fun i a => σ i a * wᵢ i a)).symm
    have hCprod0 : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ 0 := by
      rw [hsum_eq]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hCwi0 i)
    have hCprodt : ∑ π, ν π * ∏ i, wᵢ i (π i) ≠ ⊤ := by
      rw [hsum_eq]
      exact ne_of_lt (ENNReal.prod_lt_top (fun i _ => (hCwit i).lt_top))
    -- Cross-multiplication identity → reweightPMF w = reweightPMF ∏ wᵢ
    have hreweight : reweightPMF ν w = reweightPMF ν (fun π => ∏ i, wᵢ i (π i)) :=
      reweightPMF_eq_of_cross_mul ν w (fun π => ∏ i, wᵢ i (π i))
        hCw0 hCwt hCprod0 hCprodt (pureRun_cross_mul_product hPSAR D ν n h₀)
    -- Factor the product-weighted reweightPMF via reweightPMF_pmfPi
    exact ⟨fun i => reweightPMF (σ i) (wᵢ i), by
      rw [hreweight, hν_def]; exact reweightPMF_pmfPi σ wᵢ hCwi0 hCwit⟩

end ProductPreservation

/-! ## Observation-locality of per-player consistency

Under PSAR, the consistency condition `pureRun (update π₀ i πᵢ) ss ≠ 0` depends
on the trace `ss` only through `projectStates i ss`: it reduces to requiring
`πᵢ` to agree with `π₀ i` at each observation prefix, and these prefixes are
determined by player i's projection of the trace.

Combined with `pureRun_const_of_psar` (all nonzero values are equal), this means
the per-player reweighted PMF `reweightPMF (σ i) (wᵢ_ss)` depends on `ss` only
through `projectStates i ss`, giving **obs-locality of the mediator factors**. -/

section ObsLocality

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

omit [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))] in
/-- Helper: `projectStates` of a prefix can be recovered from the full projection.
If `projectStates i (p ++ [t]) = projectStates i (p' ++ [t'])`, then
`projectStates i p = projectStates i p'`. -/
theorem projectStates_prefix_of_append
    (i : ι) {p p' : List M.State} {t t' : M.State}
    (h : I.projectStates i (p ++ [t]) = I.projectStates i (p' ++ [t'])) :
    I.projectStates i p = I.projectStates i p' := by
  simp only [InfoModel.projectStates, InfoModel.projectPublic, InfoModel.projectPrivate,
    List.map_append, List.map_cons, List.map_nil] at h ⊢
  exact Prod.ext
    (List.append_inj_left' (congr_arg Prod.fst h) (by simp))
    (List.append_inj_left' (congr_arg Prod.snd h) (by simp))

open Classical in
/-- Under PSAR, the per-player consistency condition `pureRun (update π₀ i πᵢ) ss ≠ 0`
depends on `ss` only through `projectStates i ss`. If two traces have the same
player-i projection and both are reachable under π₀, then `update π₀ i πᵢ` reaches
one iff it reaches the other.

The proof uses `pureRun_succ_nonzero_iff`: consistency at `p ++ [t]` reduces to
consistency at `p` plus `πᵢ(projStates i p) = π₀ i(projStates i p)`, and the
latter depends only on `projectStates i p` (extracted from `projectStates i ss`
by `projectStates_prefix_of_append`). -/
theorem pureRun_update_obs_local
    (hPSAR : PerStepActionRecall I) (D : Dynamics I) (n : Nat)
    (i : ι) {π₀ : PureProfile I} {ss₁ ss₂ : List M.State}
    (hobs_i : I.projectStates i ss₁ = I.projectStates i ss₂)
    (h₁ : pureRun (pureStep D) M.init n π₀ ss₁ ≠ 0)
    (h₂ : pureRun (pureStep D) M.init n π₀ ss₂ ≠ 0)
    (πᵢ : I.LocalTrace i → Option (M.Act i)) :
    pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₁ ≠ 0 ↔
    pureRun (pureStep D) M.init n (Function.update π₀ i πᵢ) ss₂ ≠ 0 := by
  induction n generalizing ss₁ ss₂ with
  | zero =>
    simp only [pureRun, ne_eq] at h₁ h₂ ⊢
    exact ⟨fun _ => h₂, fun _ => h₁⟩
  | succ m ih =>
    rcases List.eq_nil_or_concat ss₁ with rfl | ⟨p₁, t₁, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h₁
    rcases List.eq_nil_or_concat ss₂ with rfl | ⟨p₂, t₂, rfl⟩
    · exact absurd (pureRun_succ_nil _ _ _ _) h₂
    simp only [List.concat_eq_append] at hobs_i h₁ h₂ ⊢
    -- Extract prefix obs equality
    have hobs_p : I.projectStates i p₁ = I.projectStates i p₂ :=
      projectStates_prefix_of_append i hobs_i
    -- Prefix reachability
    have hp₁ := left_ne_zero_of_mul (pureRun_succ_append .. ▸ h₁)
    have hp₂ := left_ne_zero_of_mul (pureRun_succ_append .. ▸ h₂)
    have ht₁ := right_ne_zero_of_mul (pureRun_succ_append .. ▸ h₁)
    have ht₂ := right_ne_zero_of_mul (pureRun_succ_append .. ▸ h₂)
    -- Use pureRun_succ_nonzero_iff decomposition
    rw [pureRun_succ_nonzero_iff hPSAR D m h₁, pureRun_succ_nonzero_iff hPSAR D m h₂]
    -- Helper: the action condition for `update π₀ i πᵢ` transfers between p₁ and p₂
    have hact_transfer :
        (∀ j, Function.update π₀ i πᵢ j (I.projectStates j p₁) =
          π₀ j (I.projectStates j p₁)) ↔
        (∀ j, Function.update π₀ i πᵢ j (I.projectStates j p₂) =
          π₀ j (I.projectStates j p₂)) := by
      constructor <;> intro h j <;> by_cases hij : j = i
      · subst hij; rw [← hobs_p]; exact h j
      · simp only [Function.update_of_ne hij] at h ⊢
      · subst hij; rw [hobs_p]; exact h j
      · simp only [Function.update_of_ne hij] at h ⊢
    constructor
    · exact fun ⟨hrec, hact⟩ => ⟨(ih hobs_p hp₁ hp₂).mp hrec, hact_transfer.mp hact⟩
    · exact fun ⟨hrec, hact⟩ => ⟨(ih hobs_p hp₁ hp₂).mpr hrec, hact_transfer.mpr hact⟩

end ObsLocality

/-! ## Decentralization bridge

The final step of Kuhn's theorem (M→B direction) decomposes as:
1. **Correlated realization** (`correlated_realization`): any ν → correlated mediator
2. **Product preservation** (`mediator_product_of_product`): product ν + PSAR →
   product mediator output at each reachable trace
3. **Decentralization**: product-valued correlated profile → independent behavioral

Step 3 reduces to **observation-locality**: each factor τᵢ of the product must
depend only on player i's observation, not on the full state trace.

The bridge theorem below handles step 3, assuming observation-locality.
The observation-locality itself requires per-step player recall + the conditioning
argument (see `KuhnMixedToBehavioral.lean`). -/

section Decentralization

variable [DecidableEq ι] [Fintype ι] [∀ i, Fintype (Option (M.Act i))]

open Math.PMFProduct

/-- If a correlated behavioral profile factors as `pmfPi (fun i => β i (v i))`
at every observation tuple `v`, then its step distribution equals that of the
independent behavioral profile `β`. -/
theorem stepDistCorr_eq_stepDist_of_product
    (D : Dynamics I) (β : BehavioralProfile I) (σ : BehavioralProfileCorr I)
    (hprod : ∀ v, σ v = pmfPi (fun i => β i (v i)))
    (ss : List M.State) :
    D.stepDistCorr σ ss = D.stepDist β ss := by
  simp only [Dynamics.stepDistCorr, Dynamics.stepDist, jointActionDist, hprod]

/-- Independent behavioral realization from correlated one: if a correlated profile
always outputs products with observation-local factors, the independent profile
produces the same outcome distribution. -/
theorem evalIndep_of_corrProduct
    (D : Dynamics I) (β : BehavioralProfile I) (σ : BehavioralProfileCorr I)
    (hprod : ∀ v, σ v = pmfPi (fun i => β i (v i)))
    (k : Nat) :
    D.evalBehavioral k β =
      Math.ProbabilityMassFunction.pushforward
        (seqRun (fun _ ss => D.stepDistCorr σ ss) M.init k)
        I.outcomeOfStates := by
  unfold Dynamics.evalBehavioral
  congr 1
  -- runDist D k β is definitionally seqRun (fun _ ss => D.stepDist β ss) M.init k
  change seqRun (fun _ ss => D.stepDist β ss) M.init k =
       seqRun (fun _ ss => D.stepDistCorr σ ss) M.init k
  congr 1
  funext _ ss
  exact (stepDistCorr_eq_stepDist_of_product D β σ hprod ss).symm

end Decentralization

end GameTheory
