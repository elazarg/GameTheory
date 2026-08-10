/-
# Mixed versus pure rationalizability hostile fixture

The row player's third action pays `3/4` against every column.  Neither of the
first two actions purely dominates it, but their half/half mixture pays `1`
against every column. This separates the first mixed-elimination round from
the first pure round. No all-round inclusion between the survivor iterations
is assumed.
-/

import GameTheory.Finite.Correctness

noncomputable section

namespace GameTheory.Tests.Rationalizability

open GameTheory GameTheory.Finite Probability

/-- Row payoffs for the hostile three-action game. -/
def rowPayoff (row column : Fin 3) : ℚ :=
  if row = 0 then
    if column = 0 then 2 else if column = 1 then 0 else 1
  else if row = 1 then
    if column = 0 then 0 else if column = 1 then 2 else 1
  else 3 / 4

/-- Only player zero's incentives matter; player one's payoff is constant. -/
@[reducible]
def mixedDominanceGame : TableGame (Fin 2) where
  Action _ := Fin 3
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile player :=
    if player = 0 then rowPayoff (profile 0) (profile 1) else 0

/-- The half/half hedge between the first two row actions. -/
def hedge : FinDist (Fin 3) :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure 0) (FinDist.pure 1)

/-- The hedge strictly dominates the third action against every column. -/
theorem third_strictlyDominatedByMixed :
    StrictlyDominatedByMixed mixedDominanceGame.toForm
      (euPreference mixedDominanceGame.utility) 0 2 := by
  refine ⟨hedge, fun profile => ?_⟩
  rw [euPreference_strict_iff]
  rw [expectedUtility_randomizedDeviationOutcome mixedDominanceGame.toForm
    mixedDominanceGame.utility profile 0 hedge]
  generalize hcolumn : profile (1 : Fin 2) = column
  fin_cases column
  all_goals rw [hedge, FinDist.expect_mix]
  all_goals simp [mixedDominanceGame, rowPayoff, hcolumn]
  all_goals norm_num

/-- A profile exposing one selected column; the row coordinate is overwritten
by every dominance comparison. -/
def atColumn (column : Fin 3) : Profile mixedDominanceGame.sig :=
  fun player => if player = 0 then 2 else column

/-- No pure action strictly dominates the third action. -/
theorem third_not_strictlyDominatedByPure (preferred : Fin 3) :
    ¬ StrictlyDominates mixedDominanceGame.toForm
      (euPreference mixedDominanceGame.utility) 0 preferred 2 := by
  fin_cases preferred
  · intro hdom
    have h := hdom (atColumn 1) (fun _ => Set.mem_univ _)
    rw [euPreference_strict_iff] at h
    norm_num [mixedDominanceGame, rowPayoff, atColumn,
      expectedUtility_pure] at h
    simp at h
    linarith
  · intro hdom
    have h := hdom (atColumn 0) (fun _ => Set.mem_univ _)
    rw [euPreference_strict_iff] at h
    norm_num [mixedDominanceGame, rowPayoff, atColumn,
      expectedUtility_pure] at h
    simp at h
    linarith
  · intro hdom
    have h := hdom (atColumn 0) (fun _ => Set.mem_univ _)
    rw [euPreference_strict_iff] at h
    norm_num [mixedDominanceGame, rowPayoff, atColumn,
      expectedUtility_pure] at h
    simp at h

/-- The third action survives the first pure-elimination round. -/
theorem third_mem_pureSurvivors_one :
    (2 : Fin 3) ∈ pureSurvivors mixedDominanceGame.toForm
      (euPreference mixedDominanceGame.utility) 1 0 := by
  rw [mem_pureSurvivors_succ]
  refine ⟨Set.mem_univ _, ?_⟩
  intro preferred _ hdom
  exact third_not_strictlyDominatedByPure preferred hdom

/-- The executable checker computes that same pure survivor fact. -/
theorem third_mem_executable_pureSurvivors_one :
    (2 : Fin 3) ∈ mixedDominanceGame.pureSurvivors 1 0 :=
  (TableGame.mem_pureSurvivors_iff mixedDominanceGame 1 0 2).2
    third_mem_pureSurvivors_one

/-- Standard mixed elimination removes the third action in the first round. -/
theorem third_not_mem_correlatedSurvivors_one :
    (2 : Fin 3) ∉ correlatedSurvivors mixedDominanceGame.toForm
      (euPreference mixedDominanceGame.utility) 1 0 := by
  intro hsurvives
  apply hsurvives.2
  obtain ⟨replacement, hdominates⟩ := third_strictlyDominatedByMixed
  exact ⟨replacement, fun action _ => Set.mem_univ action,
    fun profile _ => hdominates profile⟩

/-- Consequently the third action is not correlated rationalizable. -/
theorem third_not_isCorrelatedRationalizable :
    ¬ IsCorrelatedRationalizable mixedDominanceGame.toForm
      (euPreference mixedDominanceGame.utility) 0 2 := by
  intro hrationalizable
  exact third_not_mem_correlatedSurvivors_one (hrationalizable 1)

/-! ## Very weak versus textbook weak dominance -/

@[reducible]
def constantGame : TableGame Unit where
  Action _ := Bool
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff _ _ := 0

/-- Equal-payoff actions dominate one another only in the reflexive,
everywhere-weak sense used by dominant strategies. -/
theorem true_veryWeaklyDominates_false :
    VeryWeaklyDominates constantGame.toForm
      (euPreference constantGame.utility) () true false :=
  (TableGame.veryWeaklyDominates_eq_true_iff constantGame () true false).1
    (by decide)

/-- Textbook weak dominance additionally requires a strict witness, so it
correctly rejects two payoff-identical actions. -/
theorem true_not_weaklyDominates_false :
    ¬ WeaklyDominates constantGame.toForm
      (euPreference constantGame.utility) () true false := by
  rw [← TableGame.weaklyDominates_eq_true_iff]
  decide

end GameTheory.Tests.Rationalizability
