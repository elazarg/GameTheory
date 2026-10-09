import GameTheory.Math.FiniteSetRank

/-! Canonical finite-set ranks identify selected elements. -/
namespace GameTheory.Tests.FiniteSetRank
open GameTheory.Math.FiniteSetRank

private def selected : Finset ℕ := {1, 4, 7}

example : (selected.filter (fun i => i < 4)).card = 1 := by decide +kernel

example : 4 = selected.orderEmbOfFin (by decide +kernel : selected.card = 3) 1 := by
  apply (eq_orderEmbOfFin_iff selected _ 1 4).mpr
  exact ⟨by decide +kernel, by decide +kernel⟩

example : ¬ 5 = selected.orderEmbOfFin (by decide +kernel : selected.card = 3) 1 := by
  rw [eq_orderEmbOfFin_iff]
  decide +kernel

end GameTheory.Tests.FiniteSetRank
