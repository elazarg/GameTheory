import GameTheoryComplexity.Backend.NashNP
import GameTheoryComplexity.Backend.SATReduction

/-! NP-completeness of canonical payoff-constrained mixed Nash existence for
explicit symmetric integer payoff tables. Membership uses bounded rational
witnesses; hardness uses the complete SAT-to-table reduction. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity GameTheory.Finite.BimatrixTable

/-- Mixed Nash existence with both expected payoffs at least one is NP-complete
for the actual explicit symmetric integer-table language. -/
theorem unitPayoffLanguage_NPComplete : NPComplete unitPayoffLanguage :=
  ⟨unitPayoffLanguage_mem_NP, unitPayoffLanguage_NPHard⟩

end GameTheory.Complexity.Backend
