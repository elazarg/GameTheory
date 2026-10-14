module

/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

public import GameTheory.Analysis.Enforcement
public import GameTheory.Math.ScalarInequalitiesCorrectness

@[expose] public section

/-! # Certified inference of event penalties

A checked finite rational table certifies canonical incentive comparisons when
its gains bound actual gains and its slopes bound additional collection risk.
Slopes may be negative. The checker certifies the fixed table and event; it
does not search for a monitor, implement a game, or construct equilibrium beliefs.
-/

noncomputable section
namespace GameTheory.Enforcement
open GameTheory.Math.Probability
variable {Index Outcome : Type*}

/-- A successfully checked table certifies actual comparisons when its
rational entries bound gain and additional collection, and the base utility has
finite expectation under every compared law. -/
theorem inferred_deposit_holds (rows : Finset Index) (gain collection : Index → ℚ)
    {deposit : ℚ} (inferred : Math.ScalarInequalities.infer rows gain collection = some deposit)
    (comparisons : Index → IncentiveComparison Outcome) (base : Outcome → ℝ)
    (sanction : Set Outcome)
    (prescribedIntegrable : ∀ index ∈ rows,
      PayoffIntegrable (comparisons index).prescribed base)
    (alternativeIntegrable : ∀ index ∈ rows,
      PayoffIntegrable (comparisons index).alternative base)
    (gain_bound : ∀ index ∈ rows,
      expect ((comparisons index).alternative) base -
        expect ((comparisons index).prescribed) base ≤ (gain index : ℝ))
    (collection_bound : ∀ index ∈ rows, (collection index : ℝ) ≤
      ((comparisons index).alternative.toOuterMeasure sanction).toReal -
        ((comparisons index).prescribed.toOuterMeasure sanction).toReal)
    {index : Index} (member : index ∈ rows) :
    (comparisons index).Holds (penalizedPayoff base sanction deposit) := by
  obtain ⟨nonnegative_deposit, deters⟩ :=
    Math.ScalarInequalities.inferred_sound rows gain collection inferred
  rw [holds_iff_incremental_sanction _ _ _ _ (prescribedIntegrable index member)
    (alternativeIntegrable index member)]
  refine (gain_bound index member).trans ((deters index member).trans ?_)
  apply mul_le_mul_of_nonneg_right (collection_bound index member)
  exact_mod_cast nonnegative_deposit

end GameTheory.Enforcement
