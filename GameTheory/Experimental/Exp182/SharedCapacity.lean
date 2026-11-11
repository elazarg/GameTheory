module

/-
EXP-182 native control: affordable local optimality fills shared capacity,
whereas every ordinary Nash profile violates that capacity.
-/

public import GameTheory.Core.Utility
public import GameTheory.Math.GuardedOptimality
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.SharedCapacity

abbrev Qty := Set.Icc (0 : ℝ) 1

@[reducible]
def signature : GameSignature Bool where
  Strategy _ := Qty
  Outcome := Bool → Qty

@[reducible]
def form : GameForm Bool := GameForm.deterministic signature fun profile => profile

def utility (outcome : Bool → Qty) (who : Bool) : ℝ := (outcome who).val

def sharedFeasible (profile : Profile signature) : Prop :=
  (profile false).val + (profile true).val ≤ 1

/-- Own affordability depends on the opponent's prescribed quantity. -/
def affordable (who : Bool) (profile : Profile signature) (alternative : Qty) : Prop :=
  alternative.val + (profile (!who)).val ≤ 1

/-- This fixture-local predicate compares only affordable own alternatives.
The chosen quantity must itself be affordable. -/
def localOptimal (profile : Profile signature) : Prop :=
  ∀ who, GameTheory.Math.IsOptimalOn (affordable who profile)
    (fun chosen alternative => alternative.val ≤ chosen.val)
    {alternative | affordable who profile alternative} (profile who)

/-- Buying all remaining capacity is an admissible local alternative. -/
def remaining (profile : Profile signature) (who : Bool) : Qty :=
  ⟨1 - (profile (!who)).val, by
    constructor
    · exact sub_nonneg.mpr (profile (!who)).property.2
    · linarith [(profile (!who)).property.1]⟩

theorem remaining_affordable (profile : Profile signature) (who : Bool) :
    affordable who profile (remaining profile who) := by
  unfold affordable remaining
  dsimp
  linarith

/-- The incumbent guard enforces shared feasibility. The maximizing comparison
against remaining capacity enforces saturation. -/
theorem localOptimal_iff_capacity_filled (profile : Profile signature) :
    localOptimal profile ↔ (profile false).val + (profile true).val = 1 := by
  constructor
  · intro optimal
    have feasible := (optimal false).1
    change (profile false).val + (profile true).val ≤ 1 at feasible
    have maximal := (optimal false).2.2 (remaining profile false)
      (remaining_affordable profile false)
    change 1 - (profile true).val ≤ (profile false).val at maximal
    linarith
  · intro saturated who
    refine ⟨?_, fun _ admissible => admissible, ?_⟩
    · change (profile who).val + (profile (!who)).val ≤ 1
      cases who with
      | false =>
          change (profile false).val + (profile true).val ≤ 1
          linarith
      | true =>
          change (profile true).val + (profile false).val ≤ 1
          linarith
    · intro alternative admissible
      change alternative.val + (profile (!who)).val ≤ 1 at admissible
      cases who with
      | false =>
          change alternative.val + (profile true).val ≤ 1 at admissible
          linarith
      | true =>
          change alternative.val + (profile false).val ≤ 1 at admissible
          linarith

theorem localOptimal_sharedFeasible {profile : Profile signature} (optimal : localOptimal profile) :
    sharedFeasible profile :=
  (localOptimal_iff_capacity_filled profile).mp optimal |>.le

/-- The original expected-utility preference compares the actual pure play
laws. No finite enumeration of the quantity interval is needed. -/
theorem deviation_comparison_iff (profile : Profile signature) (who : Bool) (alternative : Qty) :
    euPreference utility who (form.play profile)
        (form.play (Profile.update profile who alternative)) ↔
      alternative.val ≤ (profile who).val := by
  simpa [form, utility, Profile.update_same] using
    euPreference_pure_iff utility who profile (Profile.update profile who alternative)

theorem isNash_iff_coordinate_bounds (profile : Profile signature) :
    IsNash form (euPreference utility) profile ↔
      ∀ who (alternative : Qty), alternative.val ≤ (profile who).val := by
  rw [isNash_iff]
  constructor
  · intro optimal who alternative
    exact (deviation_comparison_iff profile who alternative).mp (optimal who alternative)
  · intro maximal who alternative
    exact (deviation_comparison_iff profile who alternative).mpr (maximal who alternative)

def one : Qty := ⟨1, by constructor <;> norm_num⟩

/-- Ordinary product-game Nash makes both players buy one. -/
theorem isNash_iff_both_one (profile : Profile signature) :
    IsNash form (euPreference utility) profile ↔ profile false = one ∧ profile true = one := by
  rw [isNash_iff_coordinate_bounds]
  constructor
  · intro maximal
    have falseValue : (profile false).val = 1 :=
      le_antisymm (profile false).property.2 (maximal false one)
    have trueValue : (profile true).val = 1 :=
      le_antisymm (profile true).property.2 (maximal true one)
    exact ⟨Subtype.ext falseValue, Subtype.ext trueValue⟩
  · rintro ⟨falseOne, trueOne⟩ who alternative
    cases who with
    | false => simpa [falseOne, one] using alternative.property.2
    | true => simpa [trueOne, one] using alternative.property.2

/-- Filtering ordinary Nash by feasible outcomes loses every shared-capacity
solution. It cannot replace opponent-dependent deviation feasibility. -/
theorem no_feasible_ordinary_nash :
    ¬ ∃ profile : Profile signature,
      IsNash form (euPreference utility) profile ∧ sharedFeasible profile := by
  rintro ⟨profile, nash, feasible⟩
  obtain ⟨falseOne, trueOne⟩ := (isNash_iff_both_one profile).mp nash
  change (profile false).val + (profile true).val ≤ 1 at feasible
  rw [falseOne, trueOne] at feasible
  norm_num [one] at feasible

def half : Qty := ⟨1 / 2, by constructor <;> norm_num⟩

def equalSplit : Profile signature := fun _ => half

theorem equalSplit_localOptimal : localOptimal equalSplit :=
  (localOptimal_iff_capacity_filled equalSplit).2 (by norm_num [equalSplit, half])

theorem equalSplit_feasible : sharedFeasible equalSplit :=
  localOptimal_sharedFeasible equalSplit_localOptimal

theorem equalSplit_not_isNash : ¬ IsNash form (euPreference utility) equalSplit := by
  intro nash
  exact no_feasible_ordinary_nash ⟨equalSplit, nash, equalSplit_feasible⟩

end GameTheory.Experimental.SharedCapacity
