module

/-
EXP-181 rejection control: a zero-income free good has a closed feasible graph
and compact convex budget sets, but its optimizer graph is not closed.
-/

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.BudgetBoundary

open Set Filter
open scoped Topology NNReal

/-- One good, quantity cap one, nonnegative price, and zero income. -/
def budget (price : ℝ≥0) : Set ℝ :=
  Icc 0 1 ∩ {quantity | (price : ℝ) * quantity ≤ 0}

def objective (_price : ℝ≥0) (quantity : ℝ) : ℝ := quantity

theorem objective_continuous : Continuous (fun z : ℝ≥0 × ℝ => objective z.1 z.2) :=
  continuous_snd

theorem budget_zero : budget 0 = Icc 0 1 := by
  ext quantity
  simp [budget]

theorem budget_pos (price : ℝ≥0) (positive : 0 < price) : budget price = {0} := by
  ext quantity
  constructor
  · rintro ⟨⟨nonnegative, _⟩, affordable⟩
    have positiveReal : 0 < (price : ℝ) := positive
    have nonpositive : quantity ≤ 0 :=
      (mul_le_mul_iff_right₀ positiveReal).mp (by simpa using affordable)
    exact Set.mem_singleton_iff.mpr (le_antisymm nonpositive nonnegative)
  · rintro rfl
    simp [budget]

theorem budget_nonempty (price : ℝ≥0) : (budget price).Nonempty :=
  ⟨0, by simp [budget]⟩

theorem budget_closed (price : ℝ≥0) : IsClosed (budget price) :=
  isClosed_Icc.inter (isClosed_le (continuous_const.mul continuous_id) continuous_const)

theorem budget_compact (price : ℝ≥0) : IsCompact (budget price) :=
  isCompact_Icc.of_isClosed_subset (budget_closed price) (fun _ member => member.1)

theorem budget_convex (price : ℝ≥0) : Convex ℝ (budget price) := by
  by_cases zero : price = 0
  · rw [zero, budget_zero]
    exact convex_Icc 0 1
  · rw [budget_pos price (pos_iff_ne_zero.mpr zero)]
    exact convex_singleton 0

/-- All feasible sets lie in the same compact interval. -/
theorem budget_uniform_bound (price : ℝ≥0) : budget price ⊆ Icc 0 1 :=
  fun _ member => member.1

def feasibleGraph : Set (ℝ≥0 × ℝ) := {z | z.2 ∈ budget z.1}

theorem feasibleGraph_closed : IsClosed feasibleGraph := by
  change IsClosed (({z : ℝ≥0 × ℝ | 0 ≤ z.2} ∩ {z | z.2 ≤ 1}) ∩
    {z | (z.1 : ℝ) * z.2 ≤ 0})
  exact ((isClosed_le continuous_const continuous_snd).inter
    (isClosed_le continuous_snd continuous_const)).inter
      (isClosed_le ((NNReal.continuous_coe.comp continuous_fst).mul continuous_snd)
        continuous_const)

/-- Upper hemicontinuity controls limits of affordable purchases, but does not
provide nearby approximations to every purchase affordable at the limit. -/
theorem budget_upperHemicontinuous : UpperHemicontinuous budget := by
  intro price
  apply UpperHemicontinuousAt.of_sequences (K := Icc (0 : ℝ) 1)
    (IsCompact.isSeqCompact isCompact_Icc) (Eventually.of_forall budget_uniform_bound)
  intro prices priceLimit quantities affordable quantity quantityLimit
  exact feasibleGraph_closed.mem_of_tendsto (priceLimit.prodMk_nhds quantityLimit)
    (Eventually.of_forall affordable)

/-- Candidate feasibility is retained independently of the maximizing inequalities. -/
def maximizers (price : ℝ≥0) : Set ℝ :=
  {quantity | quantity ∈ budget price ∧ IsMaxOn (objective price) (budget price) quantity}

theorem zero_maximizes_at_positive_price (price : ℝ≥0) (positive : 0 < price) :
    0 ∈ maximizers price := by
  refine ⟨by simp [budget], ?_⟩
  intro alternative offered
  have equal : alternative = 0 := by
    rw [budget_pos price positive] at offered
    exact offered
  subst alternative
  exact le_rfl

theorem zero_not_maximize_at_free_price : 0 ∉ maximizers 0 := by
  intro optimal
  have bound := optimal.2 (show (1 : ℝ) ∈ budget 0 by simp [budget])
  norm_num [objective] at bound

def priceSeq (n : ℕ) : ℝ≥0 := 1 / ((n : ℝ≥0) + 1)

theorem priceSeq_positive (n : ℕ) : 0 < priceSeq n := by
  unfold priceSeq
  positivity

theorem priceSeq_tendsto : Tendsto priceSeq atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- Every nearby optimum is zero, yet zero is not optimal at the free-price
limit. Closed feasible graph, compact convex values and continuous utility
therefore do not suffice for a closed optimizer graph. -/
theorem maximizerGraph_not_closed :
    ¬ IsClosed {z : ℝ≥0 × ℝ | z.2 ∈ maximizers z.1} := by
  intro closed
  have tends : Tendsto (fun n => (priceSeq n, (0 : ℝ))) atTop (𝓝 (0, 0)) :=
    priceSeq_tendsto.prodMk_nhds tendsto_const_nhds
  have limitMember : (0 : ℝ) ∈ maximizers 0 :=
    closed.mem_of_tendsto tends (Eventually.of_forall fun n =>
      zero_maximizes_at_positive_price (priceSeq n) (priceSeq_positive n))
  exact zero_not_maximize_at_free_price limitMember

/-- The failure is precisely a missing feasible approximation at the free
price: the feasible quantity one has no nearby feasible companions. -/
theorem budget_not_lowerHemicontinuousAt_zero : ¬ LowerHemicontinuousAt budget 0 := by
  intro lower
  obtain ⟨quantities, feasibleEventually, converges⟩ :=
    lower.exists_seq_tendsto priceSeq_tendsto
      (show (1 : ℝ) ∈ budget 0 by simp [budget])
  have eventuallyZero : ∀ᶠ n in atTop, quantities n = 0 := by
    filter_upwards [feasibleEventually] with n feasible
    rw [budget_pos (priceSeq n) (priceSeq_positive n)] at feasible
    exact feasible
  have convergesZero : Tendsto quantities atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.congr' (eventuallyZero.mono fun _ equal => equal.symm)
  have impossible : (1 : ℝ) = 0 := tendsto_nhds_unique converges convergesZero
  norm_num at impossible

end GameTheory.Experimental.BudgetBoundary
