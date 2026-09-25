/-
# Information-local one-shot deviations

The finite-horizon history context and its guarded comparison with whole
policy changes. This leaf consumes the generic assessment interface.
-/

import GameTheory.Protocol.Assessment
import GameTheory.Protocol.Strategic
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability ExecutionProtocol

universe uι uo

variable {ι : Type uι} {E : ExecutionProtocol ι}

namespace InformationModel

variable {M : InformationModel E}
/-! ## Information-local one-shot deviations

The state-indexed principle in `Backward` is deliberately not reused here:
information-local policies are run on histories, and a finite horizon supplies
the induction measure directly. A one-shot change replaces one typed choice at
the current information state, takes exactly one protocol step, and then
returns to the original profile. -/

variable [DecidableEq ι]

/-- Replace one player's choice at the information state reached by `h`, without
changing that player's policy anywhere else. -/
def oneShotProfile (profile : Profile M.strategicSignature) (h : E.History)
    (who : ι) [DecidableEq (M.InfoState who)]
    (choice : M.Choice who (M.infoOf who h.trace)) :
    Profile M.strategicSignature :=
  Profile.update profile who
    ((profile who).replaceAt (M.infoOf who h.trace) choice)

@[simp]
theorem oneShotProfile_same (profile : Profile M.strategicSignature)
    (h : E.History) (who : ι) [DecidableEq (M.InfoState who)]
    (choice : M.Choice who (M.infoOf who h.trace)) :
    M.oneShotProfile profile h who choice who =
      (profile who).replaceAt (M.infoOf who h.trace) choice :=
  Profile.update_same ..

@[simp]
theorem oneShotProfile_of_ne (profile : Profile M.strategicSignature)
    (h : E.History) (who : ι) [DecidableEq (M.InfoState who)]
    (choice : M.Choice who (M.infoOf who h.trace))
    {other : ι} (hne : other ≠ who) :
    M.oneShotProfile profile h who choice other = profile other :=
  Profile.update_of_ne _ _ hne

@[simp]
theorem oneShotProfile_eq_self (profile : Profile M.strategicSignature)
    (h : E.History) (who : ι) [DecidableEq (M.InfoState who)] :
    M.oneShotProfile profile h who
        (profile who (M.infoOf who h.trace)) =
      profile := by
  simp [InformationModel.oneShotProfile]

/-- At the current history, replacing a whole policy is observationally the
same as replacing just the choice that policy makes there. -/
theorem historyChooser_update_eq_oneShotProfile
    (profile : Profile M.strategicSignature) (h : E.History)
    (hterm : ¬ E.terminal h.state) (who : ι)
    [DecidableEq (M.InfoState who)] (alternative : M.Policy who) :
    M.historyChooser (Profile.update profile who alternative) h hterm =
      M.historyChooser
        (M.oneShotProfile profile h who
          (alternative (M.infoOf who h.trace))) h hterm := by
  apply Subtype.ext
  funext other
  by_cases hwho : other = who
  · subst other
    simp [InformationModel.historyChooser, InformationModel.jointAt,
      Policy.act]
  · simp [InformationModel.historyChooser, InformationModel.jointAt,
      Policy.act, hwho]

/-- The history law of one information-local deviation now: take the altered
joint action once, then continue with the original profile for `fuel` steps. -/
def oneShotLaw (profile : Profile M.strategicSignature) (fuel : ℕ)
    (h : E.History) (hterm : ¬ E.terminal h.state) (who : ι)
    [DecidableEq (M.InfoState who)]
    (choice : M.Choice who (M.infoOf who h.trace)) : PMF E.History :=
  let changed := M.oneShotProfile profile h who choice
  let chosen := M.historyChooser changed h hterm
  (E.step h.state chosen).bindOnSupport fun _ realized =>
    M.runFrom profile fuel (h.extend chosen.2 realized)

/-- The actual assessment faced at one history. Its outcome is the next
history, not merely the next state, so continuation play may distinguish two
histories that merge into the same execution state without exposing either
history or state to the policy. -/
def historyContext (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (fuel : ℕ) (h : E.History)
    (hterm : ¬ E.terminal h.state) :
    GameTheory.Protocol.Context
      (M.Choice who (M.infoOf who h.trace)) E.History where
  outcome choice := M.oneShotLaw profile fuel h hterm who choice
  continuation := payoff

/-- Evaluating a typed choice in the history context is exactly evaluating its
one-shot law. This is the profile-plus-continuation bridge that the earlier
state-only context could not express after histories merge. -/
theorem historyContext_value (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (fuel : ℕ) (h : E.History)
    (hterm : ¬ E.terminal h.state)
    (choice : M.Choice who (M.infoOf who h.trace))
    (hintegrable :
      (M.historyContext profile who payoff fuel h hterm).IntegrableAt choice) :
    (M.historyContext profile who payoff fuel h hterm).value
        choice hintegrable =
      expect (M.oneShotLaw profile fuel h hterm who choice)
        payoff hintegrable := rfl

/-- Replacing the current choice by the choice already prescribed by the
profile leaves the current joint action unchanged. -/
theorem historyChooser_oneShotProfile_self
    (profile : Profile M.strategicSignature) (h : E.History)
    (hterm : ¬ E.terminal h.state) (who : ι)
    [DecidableEq (M.InfoState who)] :
    M.historyChooser profile h hterm =
      M.historyChooser
        (M.oneShotProfile profile h who
          (profile who (M.infoOf who h.trace))) h hterm := by
  rw [M.oneShotProfile_eq_self]

/-- The one-shot law for the profile's own current choice is exactly its
ordinary successor run. -/
theorem oneShotLaw_self (profile : Profile M.strategicSignature) (fuel : ℕ)
    (h : E.History) (hterm : ¬ E.terminal h.state) (who : ι)
    [DecidableEq (M.InfoState who)] :
    M.oneShotLaw profile fuel h hterm who
        (profile who (M.infoOf who h.trace)) =
      M.runFrom profile (fuel + 1) h := by
  let changed :=
    M.oneShotProfile profile h who (profile who (M.infoOf who h.trace))
  let chosen := M.historyChooser changed h hterm
  have hchosen : M.historyChooser profile h hterm = chosen := by
    dsimp only [chosen, changed]
    exact M.historyChooser_oneShotProfile_self profile h hterm who
  rw [InformationModel.runFrom,
    ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ fuel hterm,
    hchosen]
  rfl

/-- Every information-local one-shot deviation within the compiled horizon is
weakly worse than following `profile` immediately.

The continuation fuel is coupled to the history depth: a history of depth `d`
is compared with `fuel + 1` steps remaining only when
`d + fuel + 1 = horizon`.  Thus unfinished histories are never evaluated as if
they occurred at several incompatible times in the same finite game.  The
condition is still sequential: it quantifies over every legal history at the
appropriate depth, not only histories reached by `profile`. -/
def IsOneShotOptimalWithin (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (horizon : ℕ) : Prop :=
  ∀ fuel (h : E.History), h.trace.length + fuel + 1 = horizon →
    ∀ (hterm : ¬ E.terminal h.state),
      (M.historyContext profile who payoff fuel h hterm).IsLocallyOptimal
        Set.univ (profile who (M.infoOf who h.trace))

/-- The quantified one-shot condition is exactly sequential rationality in the
history context at every decision history and remaining horizon. -/
theorem isOneShotOptimalWithin_iff_sequentiallyRationalAt_historyContext
    (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (horizon : ℕ) :
    M.IsOneShotOptimalWithin profile who payoff horizon ↔
      ∀ fuel (h : E.History), h.trace.length + fuel + 1 = horizon →
        ∀ (hterm : ¬ E.terminal h.state),
        M.IsSequentiallyRationalAt
          (profile who) (M.infoOf who h.trace)
          (M.historyContext profile who payoff fuel h hterm) := Iff.rfl

/-- Local optimality itself certifies the incumbent continuation law at every
history that can be evaluated with the stated finite horizon. -/
theorem runFrom_integrable_of_isOneShotOptimalWithin
    (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (horizon : ℕ)
    (hopt : M.IsOneShotOptimalWithin profile who payoff horizon)
    {fuel : ℕ} (h : E.History)
    (hdepth : h.trace.length + fuel = horizon) :
    PayoffIntegrable (M.runFrom profile fuel h) payoff := by
  cases fuel with
  | zero =>
      rw [InformationModel.runFrom, ExecutionProtocol.runHistoryFor_zero]
      exact payoffIntegrable_pure h payoff
  | succ fuel =>
      by_cases hterm : E.terminal h.state
      · rw [InformationModel.runFrom,
          ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm]
        exact payoffIntegrable_pure h payoff
      · have hlocal := hopt fuel h (by omega) hterm
        rw [← M.oneShotLaw_self profile fuel h hterm who]
        exact hlocal.1

/-- **Finite-horizon information-local one-shot principle, forward
direction.** If no current information-local choice improves play at any
history, then no replacement policy for that player improves the induced
history law. -/
theorem expect_runFrom_update_le_of_isOneShotOptimalWithin
    (profile : Profile M.strategicSignature) (who : ι)
    [DecidableEq (M.InfoState who)]
    (payoff : E.History → ℝ) (horizon : ℕ)
    (hopt : M.IsOneShotOptimalWithin profile who payoff horizon)
    (alternative : M.Policy who) {fuel : ℕ} (h : E.History)
    (hdepth : h.trace.length + fuel = horizon)
    (hcandidate : PayoffIntegrable
      (M.runFrom (Profile.update profile who alternative) fuel h) payoff) :
    expect (M.runFrom (Profile.update profile who alternative) fuel h)
        payoff hcandidate ≤
      expect (M.runFrom profile fuel h) payoff
        (M.runFrom_integrable_of_isOneShotOptimalWithin
          profile who payoff horizon hopt h hdepth) := by
  induction fuel generalizing h with
  | zero =>
      unfold expect
      simp only [InformationModel.runFrom,
        ExecutionProtocol.runHistoryFor_zero, PMF.pure_apply]
      exact le_refl _
  | succ fuel ih =>
      by_cases hterm : E.terminal h.state
      · unfold expect
        simp only [InformationModel.runFrom,
          ExecutionProtocol.runHistoryFor_of_terminal _ _ hterm]
        exact le_refl _
      · let choice := alternative (M.infoOf who h.trace)
        let changed := M.oneShotProfile profile h who choice
        let chosen := M.historyChooser changed h hterm
        have hchosen :
            M.historyChooser (Profile.update profile who alternative) h hterm =
              chosen := by
          dsimp only [chosen, changed, choice]
          exact M.historyChooser_update_eq_oneShotProfile profile h hterm who alternative
        let stepLaw := E.step h.state chosen
        have hleftLaw :
            M.runFrom (Profile.update profile who alternative) (fuel + 1) h =
              stepLaw.bindOnSupport (fun _ realized =>
                M.runFrom (Profile.update profile who alternative) fuel
                  (h.extend chosen.2 realized)) := by
          rw [InformationModel.runFrom,
            ExecutionProtocol.runHistoryFor_succ_of_not_terminal _ fuel hterm,
            hchosen]
          rfl
        have hrightLaw :
            M.oneShotLaw profile fuel h hterm who choice =
              stepLaw.bindOnSupport (fun _ realized =>
                M.runFrom profile fuel (h.extend chosen.2 realized)) := rfl
        have hleft : PayoffIntegrable
            (stepLaw.bindOnSupport (fun _ realized =>
              M.runFrom (Profile.update profile who alternative) fuel
                (h.extend chosen.2 realized))) payoff := by
          rw [← hleftLaw]
          exact hcandidate
        have hright : PayoffIntegrable
            (stepLaw.bindOnSupport (fun _ realized =>
              M.runFrom profile fuel (h.extend chosen.2 realized))) payoff := by
          rw [← hrightLaw]
          exact (hopt fuel h (by omega) hterm).2.1 choice (Set.mem_univ _)
        have hlocal := (hopt fuel h (by omega) hterm).2.2 choice
          (Set.mem_univ _)
          (hopt fuel h (by omega) hterm).1
          ((hopt fuel h (by omega) hterm).2.1 choice (Set.mem_univ _))
        calc
          expect (M.runFrom (Profile.update profile who alternative)
              (fuel + 1) h) payoff hcandidate =
            expect (stepLaw.bindOnSupport fun _ realized =>
              M.runFrom (Profile.update profile who alternative) fuel
                (h.extend chosen.2 realized)) payoff hleft := by
                  unfold expect
                  rw [hleftLaw]
          _ ≤ expect (stepLaw.bindOnSupport fun _ realized =>
                M.runFrom profile fuel (h.extend chosen.2 realized))
                payoff hright := by
              apply expect_bindOnSupport_mono_on_support
              intro reached hreached hconditional _
              have hchildDepth :
                  (h.extend chosen.2 hreached).trace.length + fuel = horizon := by
                simp only [ExecutionProtocol.History.extend,
                  ExecutionProtocol.Trace.length]
                omega
              simpa only [expect_proof_irrel] using
                ih (h.extend chosen.2 hreached) hchildDepth hconditional
          _ ≤ expect (M.runFrom profile (fuel + 1) h) payoff
                (M.runFrom_integrable_of_isOneShotOptimalWithin
                  profile who payoff horizon hopt h hdepth) := by
              unfold Context.value at hlocal
              unfold expect at hlocal ⊢
              simpa only [historyContext, hrightLaw, M.oneShotLaw_self]
                using hlocal

/-- The static consequence of the information-local one-shot principle.
Compiling the same policy profile introduces no new equilibrium notion: local
optimality at every history implies ordinary expected-utility Nash in the
finite-horizon `GameForm`. -/
theorem isNash_toGameForm_of_isOneShotOptimalWithin
    [∀ i, DecidableEq (M.InfoState i)]
    (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ) (horizon : ℕ)
    (hopt : ∀ who,
      M.IsOneShotOptimalWithin profile who (fun h => utility h who) horizon)
    (hcandidate : ∀ who (alternative : M.Policy who),
      PayoffIntegrable (M.run (Profile.update profile who alternative) horizon)
        (fun h => utility h who)) :
    IsNash (M.toGameForm horizon) (euPreference utility) profile := by
  rw [isNash_iff]
  intro who alternative
  have hdepth : E.initHistory.trace.length + horizon = horizon := by
    simp [ExecutionProtocol.initHistory, ExecutionProtocol.Trace.length]
  have hinc := M.runFrom_integrable_of_isOneShotOptimalWithin
    profile who (fun h => utility h who) horizon (hopt who) E.initHistory hdepth
  have hcand := hcandidate who alternative
  have hle := M.expect_runFrom_update_le_of_isOneShotOptimalWithin
    profile who (fun h => utility h who) horizon (hopt who) alternative
    E.initHistory hdepth hcand
  refine ⟨hinc, hcand, ?_⟩
  simpa only [expectedUtility, InformationModel.run] using hle

end InformationModel

end GameTheory.Protocol
