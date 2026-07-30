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

open GameTheory GameTheory.Finite GameTheory.Probability

instance choiceNonempty : Nonempty Choice :=
  ⟨.cooperate⟩

def cooperationPayoff : PayoffVector (Fin 2) :=
  fun _ => 3

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
    repeatedDilemma.stagePayoff bothCooperate who = 3 := by
  rw [UtilityGame.stagePayoff]
  show expectedUtility prisonersDilemma.utility who
    (prisonersDilemma.toForm.play bothCooperate) = 3
  rw [prisonersDilemma.toForm_play, expectedUtility_pure]
  fin_cases who <;>
    simp [TableGame.utility_apply, bothCooperate, prisonersDilemma,
      dilemmaPayoff, opponent]

theorem cooperationPayoff_feasible :
    cooperationPayoff ∈ repeatedDilemma.feasibleSet := by
  have hmember :=
    repeatedDilemma.payoffVector_mem_feasibleSet bothCooperate
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
        (Profile.update defectPunishment who own) who ≤ 1 := by
  rw [UtilityGame.stagePayoff]
  show expectedUtility prisonersDilemma.utility who
      (prisonersDilemma.toForm.mixed.play
        (Profile.update
          (prisonersDilemma.toForm.purify bothDefect) who own)) ≤ 1
  rw [GameForm.mixed_play_update, expectedUtility_bind]
  calc
    own.expect (fun action =>
        expectedUtility prisonersDilemma.utility who
          (prisonersDilemma.toForm.mixed.play
            (Profile.update
              (prisonersDilemma.toForm.purify bothDefect) who
              (FinDist.pure action)))) ≤
        own.expect (fun _ => 1) := by
      apply FinDist.expect_mono
      intro action _
      rw [purify_update, GameForm.mixed_play_purify,
        prisonersDilemma.toForm_play, expectedUtility_pure,
        TableGame.utility_apply]
      show ((dilemmaPayoff
        (Profile.update bothDefect who action who)
        (Profile.update bothDefect who action (opponent who)) : ℚ) : ℝ) ≤ 1
      rw [Profile.update_same,
        Profile.update_of_ne _ _ (opponent_ne_self who)]
      cases action <;> norm_num [bothDefect, dilemmaPayoff]
    _ = 1 := FinDist.expect_const own 1

private theorem opponentMinmax_lt_cooperation (who : Fin 2) :
    repeatedDilemma.mixed.opponentMinmaxLevel who < 3 := by
  let H := repeatedDilemma.mixed
  letI : ∀ i, Nonempty (H.form.sig.Strategy i) :=
    fun _ => ⟨FinDist.pure Choice.cooperate⟩
  obtain ⟨bound, _hbound0, hbound⟩ :=
    H.exists_uniform_stagePayoff_abs_bound
  have hlower :
      BddBelow
        (Set.range fun punishment : Profile H.form.sig =>
          H.bestResponseValueAgainstPunishment who punishment) := by
    refine ⟨-bound, ?_⟩
    rintro _ ⟨punishment, rfl⟩
    have hbdd :
        BddAbove
          (Set.range fun own : H.form.sig.Strategy who =>
            H.stagePayoff (Profile.update punishment who own) who) := by
      refine ⟨bound, ?_⟩
      rintro _ ⟨own, rfl⟩
      exact (abs_le.mp (hbound
        (Profile.update punishment who own) who)).2
    calc
      -bound ≤
          H.stagePayoff
            (Profile.update punishment who
              (FinDist.pure Choice.defect)) who :=
        (abs_le.mp (hbound
          (Profile.update punishment who
            (FinDist.pure Choice.defect)) who)).1
      _ ≤ H.bestResponseValueAgainstPunishment who punishment :=
        le_ciSup hbdd (FinDist.pure Choice.defect)
  have hbest :
      H.bestResponseValueAgainstPunishment who defectPunishment ≤ 1 :=
    ciSup_le (payoff_against_defect_le_one who)
  exact (ciInf_le_of_le hlower defectPunishment hbest).trans_lt
    (by norm_num)

theorem cooperationPayoff_strictly_individuallyRational :
    cooperationPayoff ∈
      repeatedDilemma.strictIndividuallyRationalPayoffSet
        repeatedDilemma.mixed.opponentMinmaxVector := by
  refine ⟨cooperationPayoff_feasible, ?_⟩
  intro who
  simpa [cooperationPayoff, UtilityGame.opponentMinmaxVector] using
    opponentMinmax_lt_cooperation who

/-- The flagship instantiated at a familiar payoff that is feasible but not a
one-shot equilibrium payoff. -/
theorem prisonersDilemma_cooperation_approached_by_repeatedNash :
    ∀ ε > 0, ∃ threshold : ℝ,
      0 ≤ threshold ∧ threshold < 1 ∧
        ∀ discount : ℝ, threshold < discount → discount < 1 →
          ∃ profile : repeatedDilemma.mixed.RepeatedProfile,
            IsNash repeatedDilemma.mixed.repeatedForm
              (euPreference
                (repeatedDilemma.mixed.discountedUtility discount))
              profile ∧
            ∀ who,
              |repeatedDilemma.mixed.discountedPayoff
                  discount profile who - cooperationPayoff who| < ε :=
  repeatedDilemma.discounted_folk_theorem_approx
    cooperationPayoff_strictly_individuallyRational

end GameTheory.Examples
