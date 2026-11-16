module

/-
EXP-183 clearing and uncapping: aggregate budget accounting bounds resources;
strict monotonicity eliminates residual goods; concavity removes the cap.
-/

public import GameTheory.Experimental.Exp183.Exchange
public import Mathlib.Analysis.Convex.Extrema
public import Mathlib.Tactic.Positivity

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.Exchange

open Set Filter Topology

theorem excess_expenditure {price : Bundle} (normalized : price ∈ priceSet)
    (allocation : Bool → Bundle) :
    expenditure price (excess allocation) = expenditure price (allocation false) +
      expenditure price (allocation true) - 2 := by
  simp only [expenditure_apply, excess, supply_eq_two]
  nlinarith [normalized.2.2]

/-- Aggregate affordability bounds the auctioneer's current excess value. -/
theorem excess_expenditure_nonpositive {utility : Bool → Bundle → ℝ}
    {price : Bundle} {allocation : Bool → Bundle} (normalized : price ∈ priceSet)
    (optimal : ∀ consumer, consumerOptimal (box 3) utility price consumer (allocation consumer)) :
    expenditure price (excess allocation) ≤ 0 := by
  have first := (optimal false).1.2
  have second := (optimal true).1.2
  rw [wealth_eq_one normalized] at first second
  rw [excess_expenditure normalized]
  linarith

/-- Unit commodity-price responses bound every component of excess demand. -/
theorem aggregate_quantity_bound {utility : Bool → Bundle → ℝ}
    {price : Bundle} {allocation : Bool → Bundle} (response : priceResponse price allocation)
    (optimal : ∀ consumer, consumerOptimal (box 3) utility price consumer (allocation consumer))
    (good : Bool) : allocation false good + allocation true good ≤ 2 := by
  have best := (isMaxOn_iff.mp response.2) (vertex good) (vertex_mem_priceSet good)
  rw [expenditure_vertex] at best
  have value := excess_expenditure_nonpositive response.1 optimal
  have bound := best.trans value
  simpa only [excess, supply_eq_two, sub_nonpos] using bound

theorem consumer_quantity_bound {utility : Bool → Bundle → ℝ}
    {price : Bundle} {allocation : Bool → Bundle} (response : priceResponse price allocation)
    (optimal : ∀ consumer, consumerOptimal (box 3) utility price consumer (allocation consumer))
    (consumer good : Bool) : allocation consumer good ≤ 2 := by
  have total := aggregate_quantity_bound response optimal good
  have first := (optimal false).1.1.1 good
  have second := (optimal true).1.1.1 good
  cases consumer <;> linarith

/-- Give one consumer half the nonnegative aggregate residual. -/
def residualTopup (allocation : Bool → Bundle) (consumer : Bool) : Bundle :=
  fun good => allocation consumer good +
    (2 - allocation false good - allocation true good) / 2

theorem residualTopup_box {utility : Bool → Bundle → ℝ}
    {price : Bundle} {allocation : Bool → Bundle} (response : priceResponse price allocation)
    (optimal : ∀ consumer, consumerOptimal (box 3) utility price consumer (allocation consumer))
    (consumer : Bool) : residualTopup allocation consumer ∈ box 3 := by
  constructor
  · intro good
    have total := aggregate_quantity_bound response optimal good
    have own := (optimal consumer).1.1.1 good
    dsimp [residualTopup]
    linarith
  · intro good
    have firstUpper := consumer_quantity_bound response optimal false good
    have secondUpper := consumer_quantity_bound response optimal true good
    have firstLower := (optimal false).1.1.1 good
    have secondLower := (optimal true).1.1.1 good
    cases consumer <;> dsimp [residualTopup] <;> linarith

theorem expenditure_residualTopup {price : Bundle} (normalized : price ∈ priceSet)
    (allocation : Bool → Bundle) (consumer : Bool) :
    expenditure price (residualTopup allocation consumer) =
      expenditure price (allocation consumer) +
        (2 - expenditure price (allocation false) - expenditure price (allocation true)) / 2 := by
  simp only [expenditure_apply, residualTopup]
  nlinarith [normalized.2.2]

/-- The lower-expenditure consumer can afford half the residual, without any
prior budget-exhaustion hypothesis. -/
theorem residualTopup_affordable {price : Bundle} (normalized : price ∈ priceSet)
    (allocation : Bool → Bundle) (consumer : Bool)
    (lower : expenditure price (allocation consumer) ≤
      expenditure price (allocation (!consumer))) :
    expenditure price (residualTopup allocation consumer) ≤ wealth price consumer := by
  rw [expenditure_residualTopup normalized, wealth_eq_one normalized]
  cases consumer <;> simp only [Bool.not_false, Bool.not_true] at lower ⊢ <;> linarith

theorem residualTopup_strict {utility : Bool → Bundle → ℝ}
    {price : Bundle} {allocation : Bool → Bundle} (response : priceResponse price allocation)
    (optimal : ∀ consumer, consumerOptimal (box 3) utility price consumer (allocation consumer))
    (positiveResidual : ∃ good, allocation false good + allocation true good < 2)
    (consumer : Bool) : allocation consumer < residualTopup allocation consumer := by
  apply Pi.lt_def.mpr
  refine ⟨fun good => ?_, ?_⟩
  · have total := aggregate_quantity_bound response optimal good
    dsimp [residualTopup]
    linarith
  · obtain ⟨good, positive⟩ := positiveResidual
    refine ⟨good, ?_⟩
    dsimp [residualTopup]
    linarith

/-- Strict monotonicity on the nonnegative cone removes every residual good.
This is a product-order comparison, not a sum of consumer utilities. -/
theorem capped_conditions_clear {utility : Bool → Bundle → ℝ}
    {price : Bundle} {allocation : Bool → Bundle} (response : priceResponse price allocation)
    (optimal : ∀ consumer, consumerOptimal (box 3) utility price consumer (allocation consumer))
    (monotone : ∀ consumer, StrictMonoOn (utility consumer) nonnegative) : clears allocation := by
  classical
  by_contra notClearing
  have positiveResidual : ∃ good, allocation false good + allocation true good < 2 := by
    by_contra none
    apply notClearing
    intro good
    rw [supply_eq_two]
    exact le_antisymm (aggregate_quantity_bound response optimal good)
      (not_lt.mp (not_exists.mp none good))
  have impossible (consumer : Bool)
      (lower : expenditure price (allocation consumer) ≤
        expenditure price (allocation (!consumer))) : False := by
    have offered : residualTopup allocation consumer ∈ budgetOn (box 3) price consumer :=
      ⟨residualTopup_box response optimal consumer,
        residualTopup_affordable response.1 allocation consumer lower⟩
    have strict := monotone consumer (box_nonnegative (optimal consumer).1.1)
      (box_nonnegative offered.1) (residualTopup_strict response optimal positiveResidual consumer)
    exact (not_lt_of_ge ((isMaxOn_iff.mp (optimal consumer).2) _ offered)) strict
  rcases le_total (expenditure price (allocation false))
      (expenditure price (allocation true)) with lower | lower
  · exact impossible false (by simpa using lower)
  · exact impossible true (by simpa using lower)

/-- Resource bounds place the chosen bundle strictly below the artificial
upper cap. A local maximum on the full budget is therefore available even when
some chosen coordinates are zero. Concavity supplies global optimality. -/
theorem consumer_uncap {utility : Bool → Bundle → ℝ} {price : Bundle}
    (consumer : Bool) {chosen : Bundle}
    (optimal : consumerOptimal (box 3) utility price consumer chosen)
    (upper : ∀ good, chosen good ≤ 2)
    (concave : ConcaveOn ℝ nonnegative (utility consumer)) :
    consumerOptimal nonnegative utility price consumer chosen := by
  have member : chosen ∈ budgetOn nonnegative price consumer :=
    ⟨box_nonnegative optimal.1.1, optimal.1.2⟩
  have local_max : IsLocalMaxOn (utility consumer) (budgetOn nonnegative price consumer) chosen := by
    change ∀ᶠ alternative in 𝓝[budgetOn nonnegative price consumer] chosen,
      utility consumer alternative ≤ utility consumer chosen
    have first : ∀ᶠ alternative : Bundle in 𝓝 chosen, alternative false < 3 :=
      ((continuous_apply false).tendsto chosen).eventually
        (Iio_mem_nhds (by linarith [upper false]))
    have second : ∀ᶠ alternative : Bundle in 𝓝 chosen, alternative true < 3 :=
      ((continuous_apply true).tendsto chosen).eventually
        (Iio_mem_nhds (by linarith [upper true]))
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (first.and second)] with alternative offered belowCap
    apply (isMaxOn_iff.mp optimal.2) alternative
    refine ⟨⟨offered.1, ?_⟩, offered.2⟩
    intro good
    cases good
    · exact belowCap.1.le
    · exact belowCap.2.le
  exact ⟨member, IsMaxOn.of_isLocalMaxOn_of_concaveOn member local_max
    (concave.subset (fun _ offered => offered.1)
      (budgetOn_convex nonnegative_convex price consumer))⟩

/-- The capped fixed-point conditions reach the full native exchange
equilibrium predicate after resource bounds eliminate the auxiliary cap. -/
theorem capped_conditions_competitive {utility : Bool → Bundle → ℝ}
    {price : Bundle} {allocation : Bool → Bundle} (response : priceResponse price allocation)
    (optimal : ∀ consumer, consumerOptimal (box 3) utility price consumer (allocation consumer))
    (monotone : ∀ consumer, StrictMonoOn (utility consumer) nonnegative)
    (concave : ∀ consumer, ConcaveOn ℝ nonnegative (utility consumer)) :
    competitiveEquilibrium utility price allocation :=
  ⟨response.1,
    fun consumer => consumer_uncap consumer (optimal consumer)
      (consumer_quantity_bound response optimal consumer) (concave consumer),
    capped_conditions_clear response optimal monotone⟩

end GameTheory.Experimental.Exchange
