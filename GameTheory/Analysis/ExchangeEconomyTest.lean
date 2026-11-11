module

/-
# A two-good exchange economy

Consumer budgets depend on normalized commodity prices, and an independent
price response values excess demand. Simultaneous feasible optimization
produces capped choices. Resource accounting and monotonicity give clearing;
concavity then removes the artificial cap from individual optimality.
-/

public import GameTheory.Analysis.FeasibleChoiceFixedPoint
public import GameTheory.Math.LinearBudget
public import GameTheory.Experimental.Exp183.ExchangeClearing
public import GameTheory.Experimental.Exp183.ExchangeControls
public import Mathlib.Data.Fintype.Option

@[expose] public section

noncomputable section

namespace GameTheory.Tests.ExchangeEconomy

open Set Filter Topology
open GameTheory.Experimental.Exchange

abbrev Actor := Option Bool

def outer : Actor → Set Bundle
  | none => priceSet
  | some _ => box 3

abbrev Domain := {point : Actor → Bundle // point ∈ Set.pi Set.univ outer}

def prices (point : Domain) : Bundle := point.val none

def allocation (point : Domain) (consumer : Bool) : Bundle := point.val (some consumer)

theorem prices_mem (point : Domain) : prices point ∈ priceSet :=
  point.property none (Set.mem_univ none)

theorem continuous_prices : Continuous prices :=
  (continuous_apply none).comp continuous_subtype_val

theorem continuous_allocation (consumer : Bool) :
    Continuous (fun point : Domain => allocation point consumer) :=
  (continuous_apply (some consumer)).comp continuous_subtype_val

def feasible : Actor → Domain → Set Bundle
  | none, _ => priceSet
  | some consumer, point => budgetOn (box 3) (prices point) consumer

def objective (utility : Bool → Bundle → ℝ) : Actor → Domain × Bundle → ℝ
  | none, point => expenditure point.2 (excess (allocation point.1))
  | some consumer, point => utility consumer point.2

theorem outer_convex (actor : Actor) : Convex ℝ (outer actor) := by
  cases actor
  · exact priceSet_convex
  · exact box_convex 3

theorem outer_compact (actor : Actor) : IsCompact (outer actor) := by
  cases actor
  · exact priceSet_compact
  · exact box_compact 3

theorem outer_nonempty (actor : Actor) : (outer actor).Nonempty := by
  cases actor
  · exact priceSet_nonempty
  · exact ⟨0, box_zero_mem (by norm_num)⟩

theorem feasible_subset (actor : Actor) (point : Domain) :
    feasible actor point ⊆ outer actor := by
  cases actor
  · exact Set.Subset.refl _
  · exact fun _ offered => offered.1

theorem continuous_wealth (consumer : Bool) :
    Continuous (fun point : Domain => wealth (prices point) consumer) :=
  expenditure_continuous.comp (continuous_prices.prodMk continuous_const)

theorem feasible_graph_closed (actor : Actor) :
    IsClosed {point : Domain × Bundle | point.2 ∈ feasible actor point.1} := by
  cases actor with
  | none => exact priceSet_closed.preimage continuous_snd
  | some consumer =>
      exact ((box_compact 3).isClosed.preimage continuous_snd).inter
        (isClosed_le
          (expenditure_continuous.comp
            ((continuous_prices.comp continuous_fst).prodMk continuous_snd))
          ((continuous_wealth consumer).comp continuous_fst))

theorem feasible_lowerHemicontinuous (actor : Actor) :
    LowerHemicontinuous (feasible actor) := by
  cases actor with
  | none => exact LowerHemicontinuous.const
  | some consumer =>
      apply Math.lowerHemicontinuous_linearBudget (box 3) (box_convex 3)
        (box_zero_mem (by norm_num)) (fun point : Domain => expenditure (prices point))
      · intro bundle
        exact expenditure_continuous.comp (continuous_prices.prodMk continuous_const)
      · exact continuous_wealth consumer
      · intro point
        rw [wealth_eq_one (prices_mem point)]
        norm_num

theorem feasible_nonempty (actor : Actor) (point : Domain) :
    (feasible actor point).Nonempty := by
  cases actor with
  | none => exact priceSet_nonempty
  | some consumer =>
      refine ⟨0, box_zero_mem (by norm_num), ?_⟩
      rw [map_zero, wealth_eq_one (prices_mem point)]
      norm_num

theorem continuous_excess : Continuous (fun point : Domain => excess (allocation point)) := by
  apply continuous_pi
  intro good
  exact (((continuous_apply good).comp (continuous_allocation false)).add
    ((continuous_apply good).comp (continuous_allocation true))).sub continuous_const

theorem objective_continuous (utility : Bool → Bundle → ℝ)
    (continuous_utility : ∀ consumer, Continuous (utility consumer)) (actor : Actor) :
    Continuous (objective utility actor) := by
  cases actor with
  | none =>
      exact expenditure_continuous.comp
        (continuous_snd.prodMk (continuous_excess.comp continuous_fst))
  | some consumer => exact (continuous_utility consumer).comp continuous_snd

theorem objective_quasiconcave (utility : Bool → Bundle → ℝ)
    (concave : ∀ consumer, ConcaveOn ℝ nonnegative (utility consumer))
    (actor : Actor) (point : Domain) :
    QuasiconcaveOn ℝ (feasible actor point)
      (fun choice => objective utility actor (point, choice)) := by
  cases actor with
  | none =>
      apply ConcaveOn.quasiconcaveOn
      exact ((expenditure (excess (allocation point))).concaveOn priceSet_convex).congr
        (fun _ _ => expenditure_comm _ _)
  | some consumer =>
      exact ((concave consumer).subset (fun _ offered => box_nonnegative offered.1)
        (budgetOn_convex (box_convex 3) (prices point) consumer)).quasiconcaveOn

/-- Price response and consumer optimality come from one fixed point while
each consumer retains its own utility function. -/
theorem exists_capped_conditions (utility : Bool → Bundle → ℝ)
    (continuous_utility : ∀ consumer, Continuous (utility consumer))
    (concave : ∀ consumer, ConcaveOn ℝ nonnegative (utility consumer)) :
    ∃ price allocation, priceResponse price allocation ∧
      ∀ consumer, consumerOptimal (box 3) utility price consumer (allocation consumer) := by
  obtain ⟨point, optimal⟩ := exists_feasibleChoice_fixedPoint
    outer outer_convex outer_compact outer_nonempty feasible feasible_subset
    feasible_graph_closed feasible_lowerHemicontinuous feasible_nonempty
    (objective utility) (objective_continuous utility continuous_utility)
    (objective_quasiconcave utility concave)
  exact ⟨prices point, allocation point, optimal none, fun consumer => optimal (some consumer)⟩

/-- The auxiliary capped fixed point supplies a competitive equilibrium on
full nonnegative budgets after the separate clearing and uncapping proofs. -/
theorem exists_competitiveEquilibrium (utility : Bool → Bundle → ℝ)
    (continuous_utility : ∀ consumer, Continuous (utility consumer))
    (concave : ∀ consumer, ConcaveOn ℝ nonnegative (utility consumer))
    (monotone : ∀ consumer, StrictMonoOn (utility consumer) nonnegative) :
    ∃ price allocation, competitiveEquilibrium utility price allocation := by
  obtain ⟨price, allocation, response, optimal⟩ :=
    exists_capped_conditions utility continuous_utility concave
  exact ⟨price, allocation, capped_conditions_competitive response optimal monotone concave⟩

/-- Conflicting consumer preferences instantiate the full-budget existence
result, so its independent utility parameters are used concretely. -/
theorem heterogeneous_exchange_exists : ∃ price allocation,
    competitiveEquilibrium GameTheory.Experimental.ExchangeControls.heterogeneousUtility
      price allocation :=
  exists_competitiveEquilibrium _
    GameTheory.Experimental.ExchangeControls.heterogeneousUtility_continuous
    GameTheory.Experimental.ExchangeControls.heterogeneousUtility_concave
    GameTheory.Experimental.ExchangeControls.heterogeneousUtility_strictMono

end GameTheory.Tests.ExchangeEconomy
