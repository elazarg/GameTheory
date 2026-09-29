/-
# An added counter-action preserves Nash but not truthfulness

An agent reports truthfully or lies; the other party has two actions. In the
source mechanism the other party's action is irrelevant. The target mechanism
lets the other party's second action turn a lie into a side deal, and leaves
truthful reports untouched. At the truthful profile every Nash comparison of
the target is one of the source, so Nash is preserved for every utility. Truth
is dominant in the source for a utility ranking side deal above honesty above
lying, but not in the target: against the new action, lying pays.
-/

import GameTheory.Analysis.DominanceHierarchy

noncomputable section

namespace GameTheory.Tests.DominanceHierarchy

open GameTheory GameTheory.Math.Probability GameTheory.GameForm

inductive Outcome
  | honest
  | lie
  | sideDeal
  deriving DecidableEq

instance : Fintype Outcome :=
  ⟨{.honest, .lie, .sideDeal}, by intro outcome; cases outcome <;> simp⟩

/-- Player `false` is the agent (`true` reports truthfully); player `true` is
the other party. -/
abbrev signature : GameSignature Bool where
  Strategy _ := Bool
  Outcome := Outcome

/-- The other party's action is irrelevant. -/
@[reducible]
def source : GameForm Bool where
  sig := signature
  play profile := PMF.pure (if profile false then .honest else .lie)

/-- The other party's second action turns a lie into a side deal. -/
@[reducible]
def target : GameForm Bool where
  sig := signature
  play profile := PMF.pure
    (if profile false then .honest else if profile true then .sideDeal else .lie)

/-- The agent reports truthfully and the other party takes its first action. -/
def truthful : Profile signature := fun who => !who

def utility : Outcome → Bool → ℝ
  | .sideDeal, false => 2
  | .honest, false => 1
  | _, _ => 0

theorem holds_pure (prescribed alternative : Outcome) (value : Outcome → ℝ) :
    (IncentiveComparison.mk (PMF.pure prescribed) (PMF.pure alternative)).Holds value ↔
      value alternative ≤ value prescribed := by
  rw [IncentiveComparison.holds_iff, expect_pure, expect_pure]

/-- **Nash is preserved for every utility.** -/
theorem nash_preserved :
    IncentiveComparison.Implies
      (equilibriumComparison source (PMF.pure truthful)
        (DeviationScheme.unilateralConstant _) id)
      (equilibriumComparison target (PMF.pure truthful)
        (DeviationScheme.unilateralConstant _) id) := by
  intro value holds who alternative
  have hsource := holds who alternative
  cases who <;> cases alternative <;>
    simp_all [equilibriumComparison, GameForm.outcomeLaw, PMF.pure_map, holds_pure,
      truthful, Profile.update, Function.update]

theorem source_dominant :
    ∀ who deviation,
      (source.dominanceComparison truthful id who deviation).Holds (utility · who) := by
  rintro who ⟨opponents, alternative⟩
  cases who <;> cases alternative <;>
    simp [dominanceComparison, PMF.map_id, holds_pure, truthful, utility, Profile.update,
      Function.update]

theorem target_not_dominant :
    ¬ (target.dominanceComparison truthful id false (fun _ => true, false)).Holds
      (utility · false) := by
  simp [dominanceComparison, PMF.map_id, holds_pure, truthful, utility, Profile.update,
    Function.update]

/-- **Truthfulness is not preserved**, although Nash is. -/
theorem dominance_not_preserved :
    ¬ IncentiveComparison.Implies (source.dominanceComparison truthful id)
      (target.dominanceComparison truthful id) :=
  fun himplies => target_not_dominant (himplies utility source_dominant false _)

end GameTheory.Tests.DominanceHierarchy
