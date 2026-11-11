module

/-
EXP-180 rejection controls: changing the scalar objective can select dominated
points or reverse a utilitarian choice while preserving every Pareto comparison.
-/

public import GameTheory.Math.Scalarization
public import GameTheory.Mechanism.AffineMaximizer

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.ScalarizationBoundary

open scoped BigOperators
open GameTheory.Mechanism

def weighted (weights values : Bool → ℝ) : ℝ := ∑ player, weights player * values player

def zeroBase : Bool → ℝ := fun _ => 0

def improvement : Bool → ℝ := fun player => if player then 1 else 0

@[reducible]
def menu : Set (Bool → ℝ) := {zeroBase, improvement}

def zeroWeight : Bool → ℝ := fun player => if player then 0 else 1

def negativeWeight : Bool → ℝ := fun player => if player then -1 else 1

theorem zeroBase_dominated : zeroBase < improvement := by
  apply Pi.lt_def.mpr
  refine ⟨fun player => ?_, true, by norm_num [zeroBase, improvement]⟩
  cases player <;> norm_num [zeroBase, improvement]

theorem zeroWeight_maximum : IsMaxOn (weighted zeroWeight) menu zeroBase := by
  rintro alternative (rfl | rfl) <;>
    norm_num [weighted, zeroWeight, zeroBase, improvement, Fintype.sum_bool]

theorem negativeWeight_maximum : IsMaxOn (weighted negativeWeight) menu zeroBase := by
  rintro alternative (rfl | rfl) <;>
    norm_num [weighted, negativeWeight, zeroBase, improvement, Fintype.sum_bool]

theorem zeroBase_not_maximal : ¬ Maximal (fun values => values ∈ menu) zeroBase := by
  intro hmaximal
  exact hmaximal.not_gt (by simp [menu]) zeroBase_dominated

/-- Positive welfare weights do not remove a report-independent alternative
bias from the objective. The biased canonical choice is Pareto dominated. -/
@[reducible]
def biased : AffineMaximizer Bool Bool where
  Ty _ := Unit
  value _ _ alternative := if alternative then 1 else 0
  weight _ := 1
  bias alternative := if alternative then 0 else 10

def reports : biased.ReportProfile := fun _ => ()

theorem biased_weights_positive (player : Bool) : 0 < biased.weight player := by
  norm_num [biased]

theorem biased_choose_false : biased.choose reports = false := by
  cases hchoice : biased.choose reports with
  | false => rfl
  | true =>
    have hbound := biased.objective_le_choose reports false
    rw [hchoice] at hbound
    norm_num [AffineMaximizer.objective, biased, Fintype.sum_bool] at hbound

theorem biased_choice_dominated :
    (fun player => biased.value player (reports player) (biased.choose reports)) <
      (fun player => biased.value player (reports player) true) := by
  rw [biased_choose_false]
  apply Pi.lt_def.mpr
  refine ⟨fun _ => by norm_num [biased], false, by norm_num [biased]⟩

def firstTradeoff : Bool → ℝ := fun player => if player then 0 else 2

def secondTradeoff : Bool → ℝ := fun player => if player then 1 else 0

def scale : Bool → ℝ := fun player => if player then 3 else 1

def rescale (values : Bool → ℝ) : Bool → ℝ := fun player => scale player * values player

theorem scale_positive (player : Bool) : 0 < scale player := by
  cases player <;> norm_num [scale]

/-- Changing private units preserves all Pareto comparisons. -/
theorem rescale_le_iff (first second : Bool → ℝ) :
    rescale first ≤ rescale second ↔ first ≤ second := by
  constructor
  · intro hle player
    exact (mul_le_mul_iff_right₀ (scale_positive player)).mp (hle player)
  · intro hle player
    exact (mul_le_mul_iff_right₀ (scale_positive player)).mpr (hle player)

theorem rescale_lt_iff (first second : Bool → ℝ) :
    rescale first < rescale second ↔ first < second := by
  simp only [lt_iff_le_not_ge, rescale_le_iff]

/-- The same change of private units reverses the utilitarian comparison
when the interpersonal weights are held fixed. -/
theorem rescaling_reverses_sum :
    weighted (fun _ => 1) secondTradeoff < weighted (fun _ => 1) firstTradeoff ∧
      weighted (fun _ => 1) (rescale firstTradeoff) <
        weighted (fun _ => 1) (rescale secondTradeoff) := by
  norm_num [weighted, firstTradeoff, secondTradeoff, rescale, scale, Fintype.sum_bool]

theorem sum_maximizer_changes :
    IsMaxOn (weighted (fun _ => 1)) {firstTradeoff, secondTradeoff} firstTradeoff ∧
      IsMaxOn (fun values => weighted (fun _ => 1) (rescale values))
        {firstTradeoff, secondTradeoff} secondTradeoff := by
  constructor
  · rintro _ (rfl | rfl)
    · exact le_rfl
    · exact rescaling_reverses_sum.1.le
  · rintro _ (rfl | rfl)
    · exact rescaling_reverses_sum.2.le
    · exact le_rfl

/-- An empty feasible set makes the objective comparison vacuous, but does
not make an infeasible chosen point maximal. -/
theorem empty_objective_not_maximal :
    IsMaxOn (fun value : ℝ => value) (∅ : Set ℝ) 0 ∧
      ¬ Maximal (fun value : ℝ => value ∈ (∅ : Set ℝ)) 0 := by
  constructor
  · intro _ impossible
    exact impossible.elim
  · intro hmaximal
    exact hmaximal.1

end GameTheory.Experimental.ScalarizationBoundary
