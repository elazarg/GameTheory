module

/-
EXP-181 positive consumer: a changing divisible-consumption budget supports
continuous feasible recovery, maximizer existence and a closed optimizer graph.
-/

public import GameTheory.Math.ParametricOptimality
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.DivisibleBudget

open Set Filter Topology
open scoped NNReal

/-- A divisible good at unit price, with an arbitrary nonnegative budget. -/
def budgetSet (budget : ℝ≥0) : Set ℝ := Icc 0 (budget : ℝ)

theorem budget_graph_closed :
    IsClosed {point : ℝ≥0 × ℝ | point.2 ∈ budgetSet point.1} := by
  have nonnegative : IsClosed {point : ℝ≥0 × ℝ | 0 ≤ point.2} :=
    isClosed_le continuous_const continuous_snd
  have affordable : IsClosed {point : ℝ≥0 × ℝ | point.2 ≤ (point.1 : ℝ)} :=
    isClosed_le continuous_snd (NNReal.continuous_coe.comp continuous_fst)
  exact nonnegative.inter affordable

/-- Recovery clips a feasible quantity at the new budget. It remains feasible
for every new budget and equals the original quantity at the reference one. -/
theorem budget_lowerHemicontinuous : LowerHemicontinuous budgetSet := by
  intro budget
  apply (lowerHemicontinuousAt_iff (f := budgetSet) (x := budget)).mpr
  rintro openSet isOpenSet ⟨quantity, feasible, offered⟩
  have recoveryContinuous : Continuous (fun next : ℝ≥0 => min quantity (next : ℝ)) :=
    continuous_const.min NNReal.continuous_coe
  have recoveryAt : min quantity (budget : ℝ) = quantity := min_eq_left feasible.2
  have recoveryOffered : min quantity (budget : ℝ) ∈ openSet := by
    rwa [recoveryAt]
  filter_upwards [(recoveryContinuous.tendsto budget).eventually
    (isOpenSet.mem_nhds recoveryOffered)] with next recovered
  exact ⟨min quantity (next : ℝ),
    ⟨le_min feasible.1 next.property, min_le_right _ _⟩, recovered⟩

/-- Every continuous objective attains a maximum on each budget set.
Compactness supplies existence independently of the graph-closedness theorem. -/
theorem budget_maximizer_exists (objective : ℝ≥0 × ℝ → ℝ)
    (continuous : Continuous objective) (budget : ℝ≥0) :
    ∃ quantity ∈ budgetSet budget,
      IsMaxOn (fun alternative => objective (budget, alternative)) (budgetSet budget) quantity := by
  exact isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, budget.property⟩
    (continuous.comp (continuous_const.prodMk continuous_id)).continuousOn

/-- The selected set has a closed graph even though the feasible interval
depends on the budget. No utility representation or choice record is stored. -/
theorem budget_maximizers_graph_closed (objective : ℝ≥0 × ℝ → ℝ)
    (continuous : Continuous objective) :
    IsClosed {point : ℝ≥0 × ℝ | point.2 ∈ budgetSet point.1 ∧
      IsMaxOn (fun alternative => objective (point.1, alternative))
        (budgetSet point.1) point.2} :=
  GameTheory.Math.isClosed_feasibleMaximizers budgetSet objective
    budget_graph_closed budget_lowerHemicontinuous continuous

/-- A consumer has a satiation quantity of one, rather than monotone utility. -/
def blissObjective (point : ℝ≥0 × ℝ) : ℝ := -(point.2 - 1) ^ 2

theorem blissObjective_continuous : Continuous blissObjective :=
  ((continuous_snd.sub continuous_const).pow 2).neg

theorem bliss_maximizers_graph_closed :
    IsClosed {point : ℝ≥0 × ℝ | point.2 ∈ budgetSet point.1 ∧
      IsMaxOn (fun alternative => blissObjective (point.1, alternative))
        (budgetSet point.1) point.2} :=
  budget_maximizers_graph_closed blissObjective blissObjective_continuous

theorem zero_budget_optimum :
    0 ∈ budgetSet 0 ∧
      IsMaxOn (fun quantity => blissObjective (0, quantity)) (budgetSet 0) 0 := by
  refine ⟨by norm_num [budgetSet], ?_⟩
  intro quantity feasible
  have zero : quantity = 0 :=
    le_antisymm (by simpa using feasible.2) feasible.1
  subst quantity
  exact le_rfl

/-- Additional budget makes the satiation quantity available; the consumer
need not spend the entire budget. -/
theorem two_budget_optimum :
    1 ∈ budgetSet 2 ∧
      IsMaxOn (fun quantity => blissObjective (2, quantity)) (budgetSet 2) 1 := by
  refine ⟨by norm_num [budgetSet], ?_⟩
  intro quantity _
  simpa [blissObjective] using (neg_nonpos.mpr (sq_nonneg (quantity - 1)))

end GameTheory.Experimental.DivisibleBudget
