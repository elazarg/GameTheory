import Math.CurveSelection.GermComponent
import Mathlib.Data.Nat.Nth

set_option autoImplicit false

noncomputable section

open Filter

namespace Math
namespace CurveSelection.UltrafilterSubsequence

open CurveSelection.GermComponentScratch

/--
Any property holding in the fixed free ultrafilter holds along a strictly
increasing subsequence.  This turns the generic-germ identities used in the
algebraic argument back into an ordinary sequence suitable for the analytic
curve-selection theorem.
-/
theorem exists_strictMono_subsequence_of_eventually
    (p : ℕ → Prop)
    (hp :
      ∀ᶠ n in (sequenceUltrafilter : Filter ℕ), p n) :
    ∃ ns : ℕ → ℕ,
      StrictMono ns ∧
      ∀ n, p (ns n) := by
  have hinfinite : {n : ℕ | p n}.Infinite := by
    intro hfinite
    exact hfinite.notMem_hyperfilter hp
  refine
    ⟨Nat.nth p,
      Nat.nth_strictMono hinfinite,
      Nat.nth_mem_of_infinite hinfinite⟩

end CurveSelection.UltrafilterSubsequence
end Math
