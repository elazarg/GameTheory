module

/-
# Agreement of negligible-advantage predicates

The machine library's explicit inverse-power bounds and GameTheory's canonical
superpolynomial decay predicate describe the same real-valued advantages.
This bridge keeps probability and security statements on the canonical predicate.
-/
public import GameTheory.Math.Negligible
public import Complexitylib.Classes.Negligible
import all Complexitylib.Classes.Negligible

@[expose] public section

namespace GameTheory.Complexity.Backend

/-- Explicit inverse-power thresholds agree with superpolynomial decay. -/
theorem negligible_iff (f : ℕ → ℝ) :
    _root_.Complexity.Negligible f ↔ GameTheory.Math.Negligible f := by
  constructor
  · intro hf
    apply GameTheory.Math.negligible_of_eventually_abs_le
    intro c
    obtain ⟨N, _, hN⟩ := hf c
    exact Filter.eventually_atTop.mpr ⟨N, fun n hn => by
      simpa only [one_div] using (hN n hn).le⟩
  · intro hf c
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hf.eventually_abs_lt c)
    refine ⟨max N 1, by omega, fun n hn => ?_⟩
    simpa only [one_div] using hN n (le_trans (le_max_left N 1) hn)

end GameTheory.Complexity.Backend
