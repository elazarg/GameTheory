import GameTheoryComplexity.SampleTest

/-! Client proofs consume the sample-test facade without naming a machine backend. -/

namespace GameTheory.Complexity.Tests

open GameTheory.Math.Probability

/-- A statistical guarantee supplies indistinguishability for the exposed class
without mentioning its machine implementation. -/
theorem facade_indistinguishable_of_statisticalDistance {X X' : ℕ → PMF Bool}
    (h : GameTheory.Math.Negligible fun κ => statisticalDistance (X κ) (X' κ)) :
    IndistinguishableBy booleanMachineTests X X' :=
  indistinguishableBy_booleanMachineTests_of_polySampleTests
    (indistinguishableBy_polySampleTests_of_statisticalDistance h)

end GameTheory.Complexity.Tests
