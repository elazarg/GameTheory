module

/-
EXP-183 exchange controls: tied and conflicting preferences, clearing versus
individual demand, cap-binding false equilibria, and satiated residual supply.
-/

public import GameTheory.Experimental.Exp183.ExchangeClearing

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.ExchangeControls

open GameTheory.Experimental.Exchange

def bundle (first second : ℝ) : Bundle := fun good => if good then second else first

def halfPrice : Bundle := fun _ => 1 / 2

def sumUtility (_consumer : Bool) (chosen : Bundle) : ℝ := chosen false + chosen true

theorem halfPrice_mem : halfPrice ∈ priceSet := by norm_num [halfPrice, priceSet]

theorem sumUtility_expenditure (consumer : Bool) (chosen : Bundle) :
    sumUtility consumer chosen = expenditure (fun _ => 1) chosen := by
  simp [sumUtility, expenditure]

theorem sumUtility_continuous (consumer : Bool) : Continuous (sumUtility consumer) :=
  (continuous_apply false).add (continuous_apply true)

theorem sumUtility_concave (consumer : Bool) :
    ConcaveOn ℝ nonnegative (sumUtility consumer) := by
  exact ((expenditure (fun _ => 1)).concaveOn nonnegative_convex).congr
    (fun chosen _ => (sumUtility_expenditure consumer chosen).symm)

theorem sumUtility_strictMono (consumer : Bool) :
    StrictMonoOn (sumUtility consumer) nonnegative := by
  intro first _ second _ strict
  obtain ⟨weak, good, strictGood⟩ := Pi.lt_def.mp strict
  change first false + first true < second false + second true
  cases good <;> linarith [weak false, weak true]

def tastes (consumer good : Bool) : ℝ := if consumer = good then 2 else 1

def heterogeneousUtility (consumer : Bool) : Bundle → ℝ := expenditure (tastes consumer)

theorem heterogeneousUtility_continuous (consumer : Bool) :
    Continuous (heterogeneousUtility consumer) :=
  expenditure_continuous.comp (continuous_const.prodMk continuous_id)

theorem heterogeneousUtility_concave (consumer : Bool) :
    ConcaveOn ℝ nonnegative (heterogeneousUtility consumer) :=
  (expenditure (tastes consumer)).concaveOn nonnegative_convex

theorem heterogeneousUtility_strictMono (consumer : Bool) :
    StrictMonoOn (heterogeneousUtility consumer) nonnegative := by
  intro first _ second _ strict
  obtain ⟨weak, good, strictGood⟩ := Pi.lt_def.mp strict
  change expenditure (tastes consumer) first < expenditure (tastes consumer) second
  cases consumer <;> cases good <;> simp [tastes] <;> linarith [weak false, weak true]

/-- The two consumers disagree on the ordering of the unit commodity bundles. -/
theorem heterogeneous_preferences_disagree :
    heterogeneousUtility false (bundle 0 1) < heterogeneousUtility false (bundle 1 0) ∧
      heterogeneousUtility true (bundle 1 0) < heterogeneousUtility true (bundle 0 1) := by
  norm_num [heterogeneousUtility, expenditure, tastes, bundle]

theorem sumUtility_optimal_half (consumer : Bool) (chosen : Bundle)
    (nonnegative_chosen : chosen ∈ nonnegative)
    (total : chosen false + chosen true = 2) :
    consumerOptimal nonnegative sumUtility halfPrice consumer chosen := by
  refine ⟨⟨nonnegative_chosen, ?_⟩, ?_⟩
  · norm_num [expenditure, halfPrice, wealth, endowment]
    linarith
  · intro alternative offered
    have affordable := offered.2
    norm_num [expenditure, halfPrice, wealth, endowment] at affordable
    change alternative false + alternative true ≤ chosen false + chosen true
    linarith

theorem first_corner_optimal (consumer : Bool) :
    consumerOptimal nonnegative sumUtility halfPrice consumer (bundle 2 0) := by
  apply sumUtility_optimal_half
  · intro good
    cases good <;> norm_num [bundle]
  · norm_num [bundle]

theorem second_corner_optimal (consumer : Bool) :
    consumerOptimal nonnegative sumUtility halfPrice consumer (bundle 0 2) := by
  apply sumUtility_optimal_half
  · intro good
    cases good <;> norm_num [bundle]
  · norm_num [bundle]

/-- The full-budget optimum is compatible with an actual clearing allocation. -/
theorem endowment_competitive : competitiveEquilibrium sumUtility halfPrice endowment := by
  refine ⟨halfPrice_mem, ?_, ?_⟩
  · intro consumer
    apply sumUtility_optimal_half
    · intro good
      norm_num [endowment]
    · norm_num [endowment]
  · intro good
    rfl

def bothFirstCorner : Bool → Bundle := fun _ => bundle 2 0

theorem individually_optimal_not_clearing :
    (∀ consumer, consumerOptimal nonnegative sumUtility halfPrice consumer
      (bothFirstCorner consumer)) ∧ ¬ clears bothFirstCorner := by
  refine ⟨first_corner_optimal, ?_⟩
  intro clearing
  have impossible := clearing false
  norm_num [bothFirstCorner, bundle, supply, endowment] at impossible

theorem bothFirstCorner_not_priceResponse : ¬ priceResponse halfPrice bothFirstCorner := by
  intro response
  have impossible := (isMaxOn_iff.mp response.2) (vertex false) (vertex_mem_priceSet false)
  norm_num [expenditure, halfPrice, bothFirstCorner, excess, supply, endowment,
    bundle, vertex] at impossible

/-- A cap at the individual endowment can bind even at a clearing allocation. -/
theorem cap_one_endowment_optimal (consumer : Bool) :
    consumerOptimal (box 1) sumUtility (vertex false) consumer (endowment consumer) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro good
    norm_num [endowment]
  · intro good
    norm_num [endowment]
  · norm_num [wealth, expenditure, vertex, endowment]
  · intro alternative offered
    have first := offered.1.2 false
    have second := offered.1.2 true
    change alternative false + alternative true ≤ 1 + 1
    linarith

theorem endowment_priceResponse : priceResponse (vertex false) endowment := by
  refine ⟨vertex_mem_priceSet false, ?_⟩
  intro proposal _
  simp [expenditure, excess, supply, endowment]

theorem endowment_clears : clears endowment := fun _ => rfl

theorem cap_one_endowment_not_full_optimal (consumer : Bool) :
    ¬ consumerOptimal nonnegative sumUtility (vertex false) consumer (endowment consumer) := by
  intro optimal
  have offered : bundle 1 2 ∈ budgetOn nonnegative (vertex false) consumer := by
    constructor
    · intro good
      cases good <;> norm_num [bundle]
    · norm_num [expenditure, vertex, bundle, wealth, endowment]
  have impossible := (isMaxOn_iff.mp optimal.2) (bundle 1 2) offered
  norm_num [sumUtility, bundle, endowment] at impossible

theorem cap_one_artifact_not_competitive :
    ¬ competitiveEquilibrium sumUtility (vertex false) endowment := by
  intro equilibrium
  exact cap_one_endowment_not_full_optimal false (equilibrium.2.1 false)

def satiatedUtility (_consumer : Bool) (_chosen : Bundle) : ℝ := 0

theorem satiatedUtility_continuous (consumer : Bool) :
    Continuous (satiatedUtility consumer) := continuous_const

theorem satiatedUtility_concave (consumer : Bool) :
    ConcaveOn ℝ nonnegative (satiatedUtility consumer) :=
  concaveOn_const 0 nonnegative_convex

def zeroAllocation : Bool → Bundle := fun _ => 0

theorem satiatedUtility_monotone (consumer : Bool) :
    MonotoneOn (satiatedUtility consumer) nonnegative := by
  intro _ _ _ _ _
  exact le_rfl

theorem satiated_zero_optimal (consumer : Bool) :
    consumerOptimal (box 3) satiatedUtility halfPrice consumer (zeroAllocation consumer) := by
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro good
    simp [zeroAllocation]
  · intro good
    norm_num [zeroAllocation]
  · norm_num [zeroAllocation, expenditure, halfPrice, wealth, endowment]
  · intro alternative _
    exact le_rfl

theorem satiated_zero_priceResponse : priceResponse halfPrice zeroAllocation := by
  refine ⟨halfPrice_mem, ?_⟩
  intro proposal offered
  have normalized := offered.2.2
  norm_num [expenditure, excess, supply, endowment, zeroAllocation, halfPrice]
  linarith

theorem satiated_zero_not_clearing : ¬ clears zeroAllocation := by
  intro clearing
  have impossible := clearing false
  norm_num [zeroAllocation, supply, endowment] at impossible

end GameTheory.Experimental.ExchangeControls
