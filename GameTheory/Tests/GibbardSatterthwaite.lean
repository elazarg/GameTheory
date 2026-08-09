/-
Hostile Gibbard--Satterthwaite fixture.

The selector reads two reported pairwise comparisons.  Three explicit linear
reports attain all three outcomes.  On the truthful order `0 ≻ 1 ≻ 2`, however,
it selects the bottom alternative; reporting `1 ≻ 0 ≻ 2` changes the result to
the truthful top alternative.  Thus neither strategyproofness nor dictatorship
is being smuggled into the finite one-voter instance.
-/

import GameTheory.Core.GibbardSatterthwaite
import Mathlib.Tactic

namespace GameTheory.Tests.GibbardSatterthwaite

open SocialChoiceFunction

def rankZero : Fin 3 → Fin 3 → Prop := fun preferred alternative => preferred ≤ alternative

def rankOne : Fin 3 → Fin 3 → Prop := fun preferred alternative =>
  match preferred, alternative with
  | 1, _ => True
  | 0, 0 | 0, 2 => True
  | 2, 2 => True
  | _, _ => False

def rankTwo : Fin 3 → Fin 3 → Prop := fun preferred alternative =>
  match preferred, alternative with
  | 2, _ => True
  | 1, 1 | 1, 0 => True
  | 0, 0 => True
  | _, _ => False

theorem rankZero_linear : Rank.Linear rankZero :=
  ⟨fun _ => le_rfl, fun _ _ _ => le_trans, fun _ _ => le_total _ _,
    fun _ _ => le_antisymm⟩

theorem rankOne_linear : Rank.Linear rankOne := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro alternative
    fin_cases alternative <;> simp [rankOne]
  · intro first second third
    fin_cases first <;> fin_cases second <;> fin_cases third <;> simp [rankOne]
  · intro first second
    fin_cases first <;> fin_cases second <;> simp [rankOne]
  · intro first second
    fin_cases first <;> fin_cases second <;> simp [rankOne]

theorem rankTwo_linear : Rank.Linear rankTwo := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro alternative
    fin_cases alternative <;> simp [rankTwo]
  · intro first second third
    fin_cases first <;> fin_cases second <;> fin_cases third <;> simp [rankTwo]
  · intro first second
    fin_cases first <;> fin_cases second <;> simp [rankTwo]
  · intro first second
    fin_cases first <;> fin_cases second <;> simp [rankTwo]

def profile (rank : Fin 3 → Fin 3 → Prop) : Ranking (Fin 1) (Fin 3) :=
  fun _ => rank

theorem profile_linear {rank : Fin 3 → Fin 3 → Prop} (hlinear : Rank.Linear rank) :
    Preference.Linear (profile rank) := by
  intro voter
  simpa [profile] using hlinear

/-- A pairwise-report-sensitive selector with all three alternatives in range. -/
noncomputable def selector : SocialChoiceFunction (Fin 1) (Fin 3) := by
  classical
  exact fun ranks => if ranks 0 0 1 then 2 else if ranks 0 1 2 then 0 else 1

theorem selector_rankZero : selector (profile rankZero) = 2 := by
  simp [selector, profile, rankZero]

theorem selector_rankOne : selector (profile rankOne) = 0 := by
  simp [selector, profile, rankOne]

theorem selector_rankTwo : selector (profile rankTwo) = 1 := by
  simp [selector, profile, rankTwo]

theorem selector_isOnto : selector.IsOnto := by
  intro alternative
  fin_cases alternative
  · exact ⟨profile rankOne, profile_linear rankOne_linear, selector_rankOne⟩
  · exact ⟨profile rankTwo, profile_linear rankTwo_linear, selector_rankTwo⟩
  · exact ⟨profile rankZero, profile_linear rankZero_linear, selector_rankZero⟩

theorem selector_not_isStrategyProof : ¬ selector.IsStrategyProof := by
  intro hstrategy
  have hmanipulation := hstrategy (profile rankZero) (profile_linear rankZero_linear)
    0 rankOne rankOne_linear
  apply hmanipulation
  have hreplace :
      SocialChoiceFunction.replaceRanking (profile rankZero) 0 rankOne = profile rankOne := by
    funext voter preferred alternative
    fin_cases voter
    simp [SocialChoiceFunction.replaceRanking, profile]
  rw [hreplace, selector_rankOne, selector_rankZero]
  show (0 : Fin 3) ≤ 2 ∧ ¬ (2 : Fin 3) ≤ 0
  norm_num [Fin.ext_iff]

theorem selector_not_isDictator_zero : ¬ selector.IsDictator 0 := by
  intro hdictator
  have htop := hdictator (profile rankZero) (profile_linear rankZero_linear) 0
  rw [selector_rankZero] at htop
  simp [profile, rankZero] at htop

/-- The finite-cardinality flagship is usable directly on the same public SCF
surface exercised by the negative fixture. -/
theorem strategyproof_onto_isDictatorial
    (choice : SocialChoiceFunction (Fin 1) (Fin 3))
    (hstrategy : choice.IsStrategyProof) (honto : choice.IsOnto) :
    ∃ dictator, choice.IsDictator dictator := by
  apply GameTheory.GibbardSatterthwaite.impossibility_of_card hstrategy honto
  norm_num

end GameTheory.Tests.GibbardSatterthwaite
