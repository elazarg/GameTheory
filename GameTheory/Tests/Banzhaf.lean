/-
# Power-index fixture

The three-agent majority game is simple and symmetric.  A designated agent has
raw probabilistic Banzhaf value one half, while every agent has normalized
Shapley--Shubik power one third, so the fixture distinguishes the two indices.
-/

import GameTheory.Cooperative.ShapleyShubik

namespace GameTheory.Tests.Banzhaf

open GameTheory

theorem majorityGame_isSimple : majorityGame.IsSimpleGame := by
  refine ⟨?_, ?_, ?_⟩
  · intro coalition
    by_cases hwinning : 2 ≤ coalition.card
    · exact Or.inr (by simp [majorityGame, hwinning])
    · exact Or.inl (by simp [majorityGame, hwinning])
  · intro smaller larger hsubset hwinning
    have hsmall : 2 ≤ smaller.card := by
      by_contra hnot
      simp [majorityGame, hnot] at hwinning
    have hlarge : 2 ≤ larger.card :=
      hsmall.trans (Finset.card_le_card hsubset)
    simp [majorityGame, hlarge]
  · norm_num [majorityGame]

/-- The generic simple-game theorem exposes the Banzhaf value as a normalized
swing count for the majority fixture. -/
theorem majorityGame_probabilisticBanzhafValue_eq_swingCount :
    majorityGame.probabilisticBanzhafValue 0 =
      (majorityGame.swingCoalitions 0).card /
        (2 ^ (Fintype.card (Fin 3) - 1) : ℝ) :=
  majorityGame_isSimple.probabilisticBanzhafValue_eq_card_swingCoalitions 0

theorem majorityGame_probabilisticBanzhafValue :
    majorityGame.probabilisticBanzhafValue 0 = 1 / 2 := by
  simp only [CoalitionalGame.probabilisticBanzhafValue]
  rw [show
    (Finset.univ : Finset (Finset (Fin 3))).filter
        (fun coalition => (0 : Fin 3) ∉ coalition) =
      {∅, {1}, {2}, {1, 2}} by decide]
  norm_num [CoalitionalGame.marginalContribution, majorityGame]
  rw [show
      ({coalition ∈ ({∅, {1}, {2}, {1, 2}} : Finset (Finset (Fin 3))) |
        2 ≤ (insert 0 coalition).card}).card = 3 by decide,
    show
      ({coalition ∈ ({∅, {1}, {2}, {1, 2}} : Finset (Finset (Fin 3))) |
        2 ≤ coalition.card}).card = 1 by decide]
  norm_num

theorem majorityGame_shapleyShubikIndex (agent : Fin 3) :
    CoalitionalGame.shapleyShubikIndex
        (⟨majorityGame, majorityGame_isSimple⟩ : CoalitionalGame.SimpleGame (Fin 3))
        agent = 1 / 3 := by
  rw [show
      CoalitionalGame.shapleyShubikIndex
          (⟨majorityGame, majorityGame_isSimple⟩ : CoalitionalGame.SimpleGame (Fin 3))
          agent =
      majorityGame.shapleyValue agent from rfl]
  rw [CoalitionalGame.shapleyValue_eq_of_all_symmetric majorityGame]
  · norm_num [majorityGame]
  intro first second _ coalition hfirst hsecond
  simp only [majorityGame]
  rw [Finset.card_insert_of_notMem hfirst,
    Finset.card_insert_of_notMem hsecond]

end GameTheory.Tests.Banzhaf
