import GameTheory.Concepts.BestResponse
import Math.Probability

/-!
# Best Response Existence in Finite Games

In a finite game where each player has a nonempty finite strategy set,
a best response always exists.

## Main results

* `IsBestResponse.exists_of_finite` — best response existence for finite strategy sets
* `IsBestResponse.of_nash` — in a Nash eq, every player plays a best response
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} {G : KernelGame ι}

set_option linter.unusedFintypeInType false in
open Classical in
/-- In a finite nonempty strategy set, a best response exists for any profile. -/
theorem IsBestResponse.exists_of_finite (who : ι) [Fintype (G.Strategy who)]
    [Nonempty (G.Strategy who)] (σ : Profile G) :
    ∃ s : G.Strategy who, G.IsBestResponse who σ s := by
  have ⟨s, _, hs⟩ := Finset.exists_max_image Finset.univ
    (fun s => G.eu (Function.update σ who s) who) ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  exact ⟨s, fun s' => hs s' (Finset.mem_univ _)⟩

/-- In a Nash equilibrium, every player plays a best response. -/
theorem IsBestResponse.of_nash {σ : Profile G} (hN : G.IsNash σ) (who : ι) :
    G.IsBestResponse who σ (σ who) :=
  (isNash_iff_bestResponse G σ).mp hN who

end KernelGame

end GameTheory
