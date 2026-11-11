module

/-
EXP-183 native exchange semantics: two consumers, two divisible goods and
unit endowments. Budgets, demand optimality, price response and clearing are
separate ordinary operations. A consumption cap is an auxiliary allowed set.
-/

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.Order.Pi
public import Mathlib.Order.Filter.Extr
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.Exchange

abbrev Bundle := Bool → ℝ

/-- The value of a bundle at the supplied commodity prices. -/
def expenditure (price : Bundle) : Bundle →ₗ[ℝ] ℝ where
  toFun bundle := price false * bundle false + price true * bundle true
  map_add' x y := by simp [mul_add]; ring
  map_smul' a x := by simp; ring

@[simp]
theorem expenditure_apply (price bundle : Bundle) :
    expenditure price bundle = price false * bundle false + price true * bundle true := rfl

theorem expenditure_comm (price bundle : Bundle) :
    expenditure price bundle = expenditure bundle price := by
  simp only [expenditure_apply]
  ring

def nonnegative : Set Bundle := {bundle | ∀ good, 0 ≤ bundle good}

def box (cap : ℝ) : Set Bundle := Set.Icc (fun _ => 0) (fun _ => cap)

def priceSet : Set Bundle :=
  {price | 0 ≤ price false ∧ 0 ≤ price true ∧ price false + price true = 1}

def endowment (_consumer : Bool) : Bundle := fun _ => 1

def supply (good : Bool) : ℝ := endowment false good + endowment true good

def wealth (price : Bundle) (consumer : Bool) : ℝ := expenditure price (endowment consumer)

def budgetOn (allowed : Set Bundle) (price : Bundle) (consumer : Bool) : Set Bundle :=
  {bundle | bundle ∈ allowed ∧ expenditure price bundle ≤ wealth price consumer}

def consumerOptimal (allowed : Set Bundle) (utility : Bool → Bundle → ℝ)
    (price : Bundle) (consumer : Bool) (chosen : Bundle) : Prop :=
  chosen ∈ budgetOn allowed price consumer ∧
    IsMaxOn (utility consumer) (budgetOn allowed price consumer) chosen

def excess (allocation : Bool → Bundle) (good : Bool) : ℝ :=
  allocation false good + allocation true good - supply good

def clears (allocation : Bool → Bundle) : Prop :=
  ∀ good, allocation false good + allocation true good = supply good

def priceResponse (price : Bundle) (allocation : Bool → Bundle) : Prop :=
  price ∈ priceSet ∧ IsMaxOn (fun proposal => expenditure proposal (excess allocation)) priceSet price

/-- Individual optimality is on the full nonnegative budget, not its capped
auxiliary counterpart. -/
def competitiveEquilibrium (utility : Bool → Bundle → ℝ)
    (price : Bundle) (allocation : Bool → Bundle) : Prop :=
  price ∈ priceSet ∧ (∀ consumer,
    consumerOptimal nonnegative utility price consumer (allocation consumer)) ∧ clears allocation

theorem wealth_eq_one {price : Bundle} (normalized : price ∈ priceSet) (consumer : Bool) :
    wealth price consumer = 1 := by
  simpa [wealth, endowment, expenditure] using normalized.2.2

theorem supply_eq_two (good : Bool) : supply good = 2 := by norm_num [supply, endowment]

theorem box_nonnegative {cap : ℝ} {bundle : Bundle} (member : bundle ∈ box cap) :
    bundle ∈ nonnegative := member.1

def vertex (good : Bool) : Bundle := fun coordinate => if coordinate = good then 1 else 0

theorem vertex_mem_priceSet (good : Bool) : vertex good ∈ priceSet := by
  cases good <;> norm_num [vertex, priceSet]

theorem expenditure_vertex (good : Bool) (bundle : Bundle) :
    expenditure (vertex good) bundle = bundle good := by
  cases good <;> simp [expenditure, vertex]

theorem nonnegative_convex : Convex ℝ nonnegative := by
  rintro x hx y hy a b ha hb _ good
  exact add_nonneg (mul_nonneg ha (hx good)) (mul_nonneg hb (hy good))

theorem budgetOn_convex {allowed : Set Bundle} (convex : Convex ℝ allowed)
    (price : Bundle) (consumer : Bool) : Convex ℝ (budgetOn allowed price consumer) :=
  convex.inter ((convex_Iic (wealth price consumer)).linear_preimage (expenditure price))

theorem box_convex (cap : ℝ) : Convex ℝ (box cap) := convex_Icc _ _

theorem box_compact (cap : ℝ) : IsCompact (box cap) := isCompact_Icc

theorem box_zero_mem {cap : ℝ} (nonnegative_cap : 0 ≤ cap) : (0 : Bundle) ∈ box cap :=
  ⟨fun _ => le_rfl, fun _ => nonnegative_cap⟩

theorem priceSet_nonnegative {price : Bundle} (normalized : price ∈ priceSet) :
    price ∈ nonnegative := by
  intro good
  cases good
  · exact normalized.1
  · exact normalized.2.1

theorem priceSet_subset_box_one : priceSet ⊆ box 1 := by
  intro price normalized
  refine ⟨priceSet_nonnegative normalized, ?_⟩
  intro good
  cases good <;> linarith [normalized.1, normalized.2.1, normalized.2.2]

theorem priceSet_closed : IsClosed priceSet :=
  (isClosed_le continuous_const (continuous_apply false)).inter
    ((isClosed_le continuous_const (continuous_apply true)).inter
      (isClosed_eq ((continuous_apply false).add (continuous_apply true)) continuous_const))

theorem priceSet_convex : Convex ℝ priceSet := by
  rintro p hp q hq a b ha hb hab
  refine ⟨add_nonneg (mul_nonneg ha hp.1) (mul_nonneg hb hq.1),
    add_nonneg (mul_nonneg ha hp.2.1) (mul_nonneg hb hq.2.1), ?_⟩
  change (a * p false + b * q false) + (a * p true + b * q true) = 1
  calc
    _ = a * (p false + p true) + b * (q false + q true) := by ring
    _ = 1 := by rw [hp.2.2, hq.2.2]; linarith

theorem priceSet_compact : IsCompact priceSet :=
  (box_compact 1).of_isClosed_subset priceSet_closed priceSet_subset_box_one

theorem priceSet_nonempty : priceSet.Nonempty :=
  ⟨fun _ => 1 / 2, by norm_num [priceSet]⟩

theorem expenditure_continuous :
    Continuous (fun point : Bundle × Bundle => expenditure point.1 point.2) :=
  (((continuous_apply false).comp continuous_fst).mul
    ((continuous_apply false).comp continuous_snd)).add
      (((continuous_apply true).comp continuous_fst).mul
        ((continuous_apply true).comp continuous_snd))

end GameTheory.Experimental.Exchange
