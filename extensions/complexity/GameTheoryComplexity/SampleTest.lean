import GameTheoryComplexity.Backend.CompiledSampleTest

/-! A small sample-test facade for the selected computational backend.
Client statements use the library's existing tests and indistinguishability relation;
constructing a machine implementation is confined to the backend module.
-/

namespace GameTheory.Complexity

open GameTheory.Math.Probability

/-- Canonically encoded Boolean tests with certified polynomial machine execution.
One composed probabilistic polynomial-time machine implements serialization and
execution with exactly the same verdict law and a sample-independent security clock. -/
def booleanMachineTests : Set (SampleTest Bool) := Backend.booleanMachineTests

/-- Every exposed test sees only polynomially many samples. -/
theorem booleanMachineTests_subset_polySampleTests :
    booleanMachineTests ⊆ polySampleTests Bool :=
  Backend.booleanMachineTests_subset_polySampleTests

/-- Indistinguishability against all polynomial-sample tests implies
indistinguishability against the selected computational tests. -/
theorem indistinguishableBy_booleanMachineTests_of_polySampleTests {X X' : ℕ → PMF Bool}
    (h : IndistinguishableBy (polySampleTests Bool) X X') :
    IndistinguishableBy booleanMachineTests X X' :=
  h.mono booleanMachineTests_subset_polySampleTests

end GameTheory.Complexity
