/-
# A nonvacuous folk-theorem witness

Mutual cooperation in the Prisoner's Dilemma is feasible and strictly above
what the other player can enforce by permanent defection. The analytic
repeated-game theorem therefore supplies patient mixed-action equilibria whose
discounted payoff approaches cooperation.
-/

import GameTheory.Analysis.Repeated.Folk
import GameTheory.Examples.Classic

noncomputable section

namespace GameTheory.Examples

open GameTheory GameTheory.Finite GameTheory.Math.Probability

instance choiceNonempty : Nonempty Choice :=
  ⟨.cooperate⟩

/-- The payoff vector both players receive under mutual cooperation. -/
def cooperationPayoff : PayoffVector (Fin 2) :=
  fun _ => 3

/-- The Prisoner's Dilemma as a utility game, ready to be repeated. -/
@[reducible]
noncomputable def repeatedDilemma : UtilityGame (Fin 2) where
  form := prisonersDilemma.toForm
  utility := prisonersDilemma.utility

instance repeatedDilemmaStrategyNonempty (i : Fin 2) :
    Nonempty (repeatedDilemma.form.sig.Strategy i) := by
  show Nonempty Choice
  exact choiceNonempty

@[simp]
theorem repeatedDilemma_stagePayoff_bothCooperate (who : Fin 2) :
    repeatedDilemma.stagePayoff bothCooperate who
      (repeatedDilemma.form.hasIntegrableUtility_of_finiteOutcome
        repeatedDilemma.utility who bothCooperate) = 3 := by
  rw [UtilityGame.stagePayoff]
  show expectedUtility prisonersDilemma.utility who
    (prisonersDilemma.toForm.play bothCooperate) _ = 3
  simp only [expectedUtility_pure]
  fin_cases who <;>
    simp [TableGame.utility_apply, bothCooperate, prisonersDilemma,
      dilemmaPayoff, opponent]

theorem cooperationPayoff_feasible :
    cooperationPayoff ∈ repeatedDilemma.feasibleSet
      (repeatedDilemma.form.hasIntegrableUtility_of_finiteOutcome
        repeatedDilemma.utility) := by
  have hmember :=
    repeatedDilemma.payoffVector_mem_feasibleSet
      (repeatedDilemma.form.hasIntegrableUtility_of_finiteOutcome
        repeatedDilemma.utility) bothCooperate
  convert hmember using 1
  funext who
  simp [cooperationPayoff]

private def defectPunishment :
    Profile repeatedDilemma.mixed.form.sig :=
  repeatedDilemma.form.purify bothDefect

private theorem opponent_ne_self (who : Fin 2) :
    opponent who ≠ who := by
  fin_cases who <;> decide

private theorem payoff_against_defect_le_one
    (who : Fin 2)
    (own : repeatedDilemma.mixed.form.sig.Strategy who) :
    repeatedDilemma.mixed.stagePayoff
        (Profile.update defectPunishment who own) who
        (repeatedDilemma.mixed.form.hasIntegrableUtility_of_finiteOutcome
          repeatedDilemma.mixed.utility who _) ≤ 1 := by
  let F := prisonersDilemma.toForm
  let mixedProfile : Profile F.mixed.sig :=
    Profile.update (F.purify bothDefect) who own
  let hH : F.mixed.HasIntegrableUtility prisonersDilemma.utility :=
    F.mixed.hasIntegrableUtility_of_finiteOutcome prisonersDilemma.utility
  have hrow (action : Choice) :
      expectedUtility prisonersDilemma.utility who
          (F.mixed.play
            (Profile.update mixedProfile who (PMF.pure action)))
          (hH who _) ≤ 1 := by
    have hlaw :
        F.mixed.play
            (Profile.update mixedProfile who (PMF.pure action)) =
          F.play (Profile.update bothDefect who action) := by
      rw [show Profile.update mixedProfile who (PMF.pure action) =
        Profile.update (F.purify bothDefect) who (PMF.pure action) from
          Profile.update_idem _ _ _ _]
      rw [purify_update, GameForm.mixed_play_purify]
    have hvalue :
        expectedUtility prisonersDilemma.utility who
            (F.mixed.play
              (Profile.update mixedProfile who (PMF.pure action)))
            (hH who _) =
          prisonersDilemma.utility
            (Profile.update bothDefect who action) who := by
      calc
        _ = expectedUtility prisonersDilemma.utility who
            (F.play (Profile.update bothDefect who action))
            (prisonersDilemma.utilityIntegrable who _) :=
          expectedUtility_congr_law _ _ hlaw _ _
        _ = _ := by rw [prisonersDilemma.toForm_play, expectedUtility_pure]
    rw [hvalue, TableGame.utility_apply]
    show ((dilemmaPayoff
      (Profile.update bothDefect who action who)
      (Profile.update bothDefect who action (opponent who)) : ℚ) : ℝ) ≤ 1
    rw [Profile.update_same,
      Profile.update_of_ne _ _ (opponent_ne_self who)]
    cases action <;> norm_num [bothDefect, dilemmaPayoff]
  have hmean := expectedUtility_mixed_eq_expect F prisonersDilemma.utility
    mixedProfile who (hH who mixedProfile)
    (fun action => hH who _)
  have hupper := expect_le_const own
    (f := fun action => expectedUtility prisonersDilemma.utility who
      (F.mixed.play (Profile.update mixedProfile who (PMF.pure action)))
      (hH who _))
    (payoffIntegrable_of_finite _ _) 1
    (fun action _ => hrow action)
  have hupper' :
      expect (mixedProfile who)
        (fun action => expectedUtility prisonersDilemma.utility who
          (F.mixed.play (Profile.update mixedProfile who (PMF.pure action)))
          (hH who _))
        (payoffIntegrable_bind_conditionalExpectation
          (mixedProfile who)
          (fun action => F.mixed.play
            (Profile.update mixedProfile who (PMF.pure action)))
          (fun outcome => prisonersDilemma.utility outcome who)
          (by
            rw [← mixed_play_update_self F mixedProfile who]
            exact hH who mixedProfile)
          (fun action => hH who _)) ≤ 1 := by
    simpa only [mixedProfile, Profile.update_same] using hupper
  simpa [UtilityGame.stagePayoff, F, mixedProfile, defectPunishment] using
    hmean.trans_le hupper'

private theorem opponentMinmax_lt_cooperation (who : Fin 2) :
    repeatedDilemma.mixed.opponentMinmaxLevel
      (repeatedDilemma.mixed.form.hasIntegrableUtility_of_finiteOutcome
        repeatedDilemma.mixed.utility) who < 3 := by
  let H := repeatedDilemma.mixed
  let hH : H.form.HasIntegrableUtility H.utility :=
    H.form.hasIntegrableUtility_of_finiteOutcome H.utility
  let : ∀ i, Nonempty (H.form.sig.Strategy i) :=
    fun _ => ⟨PMF.pure Choice.cooperate⟩
  obtain ⟨bound, _hbound0, hbound⟩ :=
    H.exists_uniform_stagePayoff_abs_bound
  have hlower :
      BddBelow
        (Set.range fun punishment : Profile H.form.sig =>
          H.bestResponseValueAgainstPunishment hH who punishment) := by
    refine ⟨-bound, ?_⟩
    rintro _ ⟨punishment, rfl⟩
    have hbdd :
        BddAbove
          (Set.range fun own : H.form.sig.Strategy who =>
            H.stagePayoff (Profile.update punishment who own) who
              (hH who _)) := by
      refine ⟨bound, ?_⟩
      rintro _ ⟨own, rfl⟩
      exact (abs_le.mp (hbound
        (Profile.update punishment who own) who)).2
    calc
      -bound ≤
          H.stagePayoff
            (Profile.update punishment who
              (PMF.pure Choice.defect)) who (hH who _) :=
        (abs_le.mp (hbound
          (Profile.update punishment who
            (PMF.pure Choice.defect)) who)).1
      _ ≤ H.bestResponseValueAgainstPunishment hH who punishment :=
        le_ciSup hbdd (PMF.pure Choice.defect)
  have hbest :
      H.bestResponseValueAgainstPunishment hH who defectPunishment ≤ 1 :=
    ciSup_le (payoff_against_defect_le_one who)
  exact (ciInf_le_of_le hlower defectPunishment hbest).trans_lt
    (by norm_num)

theorem cooperationPayoff_strictly_individuallyRational :
    cooperationPayoff ∈
      repeatedDilemma.strictIndividuallyRationalPayoffSet
        (repeatedDilemma.form.hasIntegrableUtility_of_finiteOutcome
          repeatedDilemma.utility)
        (repeatedDilemma.mixed.opponentMinmaxVector
          (repeatedDilemma.mixed.form.hasIntegrableUtility_of_finiteOutcome
            repeatedDilemma.mixed.utility)) := by
  refine ⟨cooperationPayoff_feasible, ?_⟩
  intro who
  simpa [cooperationPayoff, UtilityGame.opponentMinmaxVector] using
    opponentMinmax_lt_cooperation who

/-- The theorem instantiated at a familiar payoff that is feasible but not a
one-shot equilibrium payoff. -/
theorem prisonersDilemma_cooperation_approached_by_repeatedNash :
    ∀ ε > 0, ∃ threshold : ℝ,
      0 ≤ threshold ∧ threshold < 1 ∧
        ∀ (discount : ℝ) (hdiscount0 : 0 ≤ discount),
          threshold < discount → (hdiscount1 : discount < 1) →
          ∃ profile : repeatedDilemma.mixed.RepeatedProfile,
            IsNash repeatedDilemma.mixed.repeatedForm
              (euPreference
                (repeatedDilemma.mixed.discountedUtilityOfFiniteOutcome
                  hdiscount0 hdiscount1))
              profile ∧
            ∀ who,
              |repeatedDilemma.mixed.discountedPayoffOfFiniteOutcome
                  hdiscount0 hdiscount1 profile who - cooperationPayoff who| < ε :=
  repeatedDilemma.discounted_folk_theorem_approx
    cooperationPayoff_strictly_individuallyRational

end GameTheory.Examples
