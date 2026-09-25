/-
EXP-128 consumer: finite strategic choices, an infinite outcome law, and an
unbounded but integrable utility are fed directly to mixed Nash existence.
-/

import GameTheory.Analysis.Nash
import GameTheory.Experimental.PostArchitecture.PMFStaticGate

noncomputable section

namespace GameTheory.Analysis.PMFExistenceTest

open GameTheory GameTheory.Math.Probability
open GameTheory.Experimental.PMFStaticGate
open GameTheory.Experimental.PMFRestoration

abbrev Player := Fin 2

theorem actions_distinct : (0 : Fin 2) ≠ 1 := by decide

abbrev infiniteOutcomeForm : GameForm Player where
  sig := {
    Strategy := fun _ => Fin 2
    Outcome := ℕ × Fin 2 × Fin 2 }
  play profile := geometric.map fun n => (n, profile 0, profile 1)

def actionBonus (outcome : ℕ × Fin 2 × Fin 2) (player : Player) : ℝ :=
  if (if player = 0 then outcome.2.1 else outcome.2.2) = 1 then 1 else 0

def infiniteLinearUtility (outcome : ℕ × Fin 2 × Fin 2) (player : Player) : ℝ :=
  linearUtility outcome.1 player + actionBonus outcome player

theorem utility_depends_on_action :
    infiniteLinearUtility (0, 0, 0) 0 ≠ infiniteLinearUtility (0, 1, 0) 0 := by
  norm_num [infiniteLinearUtility, actionBonus, linearUtility]

theorem pure_integrable : infiniteOutcomeForm.HasIntegrableUtility infiniteLinearUtility := by
  intro player profile
  show UtilityIntegrable infiniteLinearUtility player
    (geometric.map fun n => (n, profile 0, profile 1))
  unfold UtilityIntegrable
  rw [payoffIntegrable_map_iff]
  have hbase : PayoffIntegrable geometric (fun n : ℕ => linearUtility n player) := by
    simpa [linearUtility, UtilityIntegrable] using linearUtility_integrable_geometric
  have hbonus : PayoffIntegrable geometric
      (fun _ : ℕ => actionBonus (0, profile 0, profile 1) player) :=
    payoffIntegrable_of_bounded geometric _ (C := 1) (by
      intro _
      unfold actionBonus
      split_ifs <;> norm_num)
  have hsum := payoffIntegrable_add hbase hbonus
  apply payoffIntegrable_congr_on_support (μ := geometric)
    (f := fun n => linearUtility n player + actionBonus (0, profile 0, profile 1) player)
    (g := fun n => infiniteLinearUtility (n, profile 0, profile 1) player)
    (fun n _ => by simp [infiniteLinearUtility, actionBonus])
  exact hsum

theorem play_has_infinite_support (profile : Profile infiniteOutcomeForm.sig) :
    (infiniteOutcomeForm.play profile).support.Infinite := by
  show (geometric.map fun n => (n, profile 0, profile 1)).support.Infinite
  have hinj : Function.Injective (fun n : ℕ => (n, profile 0, profile 1)) := by
    intro n m h
    exact congrArg (fun triple : ℕ × Fin 2 × Fin 2 => triple.1) h
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  rw [PMF.mem_support_map_iff]
  exact ⟨n, (geometric_positive n).ne', rfl⟩

theorem utility_unbounded (player : Player) :
    ¬ ∃ C, ∀ outcome : ℕ × Fin 2 × Fin 2,
      |infiniteLinearUtility outcome player| ≤ C := by
  rintro ⟨C, hC⟩
  apply linearUtility_unbounded
  refine ⟨C, fun n => ?_⟩
  simpa [infiniteLinearUtility, actionBonus, linearUtility] using hC (n, 0, 0)

theorem exists_infinite_law_isNash :
    ∃ μ : Profile infiniteOutcomeForm.mixed.sig,
      IsNash infiniteOutcomeForm.mixed (euPreference infiniteLinearUtility) μ := by
  exact exists_isNash_mixed (F := infiniteOutcomeForm)
    infiniteLinearUtility pure_integrable

end GameTheory.Analysis.PMFExistenceTest
