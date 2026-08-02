/-
# Rosenthal potential for congestion games

Rosenthal's finite-player congestion games admit an exact potential: the
negative sum of every occupied resource's cumulative delays.  The canonical
potential theory then supplies pure Nash existence, finite improvement, and
weak acyclicity under exactly the finite-profile assumptions those conclusions
need.

Mathematical provenance: `reference/GameTheory-v1/GameTheory/Congestion/Rosenthal.lean`
at pinned commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
-/

import GameTheory.Congestion.Basic
import GameTheory.Core.Potential

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace CongestionGame

variable {ι : Type*}

/-- Rosenthal's potential: the negative cumulative delay over occupied
resources. -/
def potential [Fintype ι] (C : CongestionGame ι) (σ : C.Profile) : ℝ :=
  - ∑ r ∈ C.usedResources σ,
      ∑ k ∈ Finset.range (C.congestion σ r), C.delay r (k + 1)

open Classical in
/-- Rosenthal's exact-potential identity over the canonical deterministic
game form and negative-cost utility. -/
theorem isExactPotential [Fintype ι] [DecidableEq ι] (C : CongestionGame ι) :
    IsExactPotential C.toGameForm C.utility C.potential := by
  intro who (σ : C.Profile) s'
  simp only [toGameForm, utility, expectedUtility_pure, playerCost, potential,
    Profile.update_same]
  set σ' := GameTheory.Profile.update (sig := C.toGameForm.sig) σ who s' with hσ'
  suffices h : ∑ r ∈ C.resources who (σ who), C.delay r (C.congestion σ r) -
      ∑ r ∈ C.resources who s', C.delay r (C.congestion σ' r) =
      ∑ r ∈ C.usedResources σ,
        ∑ k ∈ Finset.range (C.congestion σ r), C.delay r (k + 1) -
      ∑ r ∈ C.usedResources σ',
        ∑ k ∈ Finset.range (C.congestion σ' r), C.delay r (k + 1) by
    linarith
  have hPσ : ∑ r ∈ C.usedResources σ,
      ∑ k ∈ Finset.range (C.congestion σ r), C.delay r (k + 1) =
      ∑ r ∈ C.usedResources σ ∪ C.usedResources σ',
          ∑ k ∈ Finset.range (C.congestion σ r), C.delay r (k + 1) :=
    Finset.sum_subset Finset.subset_union_left fun r _ hr => by
      rw [congestion_eq_zero_of_not_mem_usedResources hr]
      simp
  have hPσ' : ∑ r ∈ C.usedResources σ',
      ∑ k ∈ Finset.range (C.congestion σ' r), C.delay r (k + 1) =
      ∑ r ∈ C.usedResources σ ∪ C.usedResources σ',
          ∑ k ∈ Finset.range (C.congestion σ' r), C.delay r (k + 1) :=
    Finset.sum_subset Finset.subset_union_right fun r _ hr => by
      rw [congestion_eq_zero_of_not_mem_usedResources hr]
      simp
  rw [hPσ, hPσ']
  have hsub1 : C.resources who (σ who) ⊆ C.usedResources σ ∪ C.usedResources σ' :=
    (C.resources_subset_usedResources σ who).trans Finset.subset_union_left
  have hsub2 : C.resources who s' ⊆ C.usedResources σ ∪ C.usedResources σ' := by
    have h2 := (C.resources_subset_usedResources σ' who).trans
      (Finset.subset_union_right (s₁ := C.usedResources σ))
    rwa [hσ', GameTheory.Profile.update_same] at h2
  have h_sum_eq : ∀ (S : Finset C.Resource) (f : C.Resource → ℝ),
      S ⊆ C.usedResources σ ∪ C.usedResources σ' →
      ∑ r ∈ S, f r =
        ∑ r ∈ C.usedResources σ ∪ C.usedResources σ', if r ∈ S then f r else 0 := by
    intro S f hS
    conv_rhs => rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hS]
  rw [h_sum_eq (C.resources who (σ who)) _ hsub1,
    h_sum_eq (C.resources who s') _ hsub2]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  set n := C.congestionWithout σ who r
  rw [C.congestion_decompose σ who r, C.congestion_update σ who s' r]
  by_cases hold : r ∈ C.resources who (σ who) <;>
    by_cases hnew : r ∈ C.resources who s'
  · simp [hold, hnew]
  · simp only [hold, hnew, ite_true, ite_false, add_zero]
    rw [Finset.sum_range_succ]
    ring
  · simp only [hold, hnew, ite_true, ite_false, add_zero]
    rw [Finset.sum_range_succ]
    ring
  · simp [hold, hnew]

/-- Finite congestion games with nonempty strategy carriers have a pure Nash
equilibrium, by maximizing Rosenthal's potential. -/
theorem nash_exists [Fintype ι] [DecidableEq ι] (C : CongestionGame ι)
    [Finite C.Profile] [Nonempty C.Profile] :
    ∃ σ : C.Profile, IsNash C.toGameForm (euPreference C.utility) σ := by
  letI : Finite (GameTheory.Profile C.toGameForm.sig) := ‹Finite C.Profile›
  letI : Nonempty (GameTheory.Profile C.toGameForm.sig) := ‹Nonempty C.Profile›
  exact C.isExactPotential.exists_isNash

/-- A finite congestion profile space has no infinite chain of strict
unilateral utility improvements. -/
theorem no_infinite_improving_path [Fintype ι] [DecidableEq ι]
    (C : CongestionGame ι) [Finite C.Profile] :
    ¬ ∃ path : ℕ → C.Profile,
        ∀ n, ImprovingStep C.toGameForm C.utility (path n) (path (n + 1)) := by
  letI : Finite (GameTheory.Profile C.toGameForm.sig) := ‹Finite C.Profile›
  exact C.isExactPotential.no_infinite_improving_path

/-- Every finite congestion game is weakly acyclic under strict unilateral
expected-utility improvements. -/
theorem weaklyAcyclic [Fintype ι] [DecidableEq ι]
    (C : CongestionGame ι) [Finite C.Profile] :
    WeaklyAcyclic C.toGameForm C.utility := by
  letI : Finite (GameTheory.Profile C.toGameForm.sig) := ‹Finite C.Profile›
  exact C.isExactPotential.weaklyAcyclic

end CongestionGame

end GameTheory
