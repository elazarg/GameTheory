/-
# Finite-player congestion games

A congestion game gives each player a strategy whose finite resource set is
occupied, and assigns a real delay to each resource at each natural load.
Resource and strategy carriers remain unconstrained.  Finiteness enters only
at load-counting and aggregate operations, never in the semantic data.

The static presentation below deliberately reuses `GameForm`, `UtilityGame`,
`Profile.update`, expected-utility Nash, and the potential/dynamics theory in
`GameTheory.Core`.  It does not introduce a congestion-specific game or
equilibrium predicate.
-/

import GameTheory.Core.Utility

noncomputable section

open scoped BigOperators

namespace GameTheory

universe uι ur us

/-- A congestion game.  The data itself makes no finiteness or decidable-
equality commitment: those capabilities belong only to operations that count
players or compare resource membership. -/
structure CongestionGame (ι : Type uι) where
  /-- Resources that may be occupied by strategies. -/
  Resource : Type ur
  /-- Each player's strategy carrier. -/
  Strategy : ι → Type us
  /-- The finite resource set occupied by a strategy. -/
  resources : ∀ i, Strategy i → Finset Resource
  /-- The delay imposed by a resource at a given load. -/
  delay : Resource → ℕ → ℝ

-- Resources and strategies intentionally have independent universes; the linter
-- sees them only through this record's combined result universe.

namespace CongestionGame

variable {ι : Type uι}

/-- A pure congestion profile. -/
abbrev Profile (C : CongestionGame ι) := ∀ i, C.Strategy i

/-- The canonical strategy/outcome signature: a pure outcome records the
whole pure congestion profile. -/
def signature (C : CongestionGame ι) : GameSignature ι where
  Strategy := C.Strategy
  Outcome := C.Profile

/-- The deterministic static form associated to a congestion game. -/
@[reducible]
def toGameForm (C : CongestionGame ι) : GameForm ι :=
  GameForm.deterministic C.signature fun profile => profile

/-- Count the players whose selected strategies occupy a resource. -/
noncomputable def congestion [Fintype ι] (C : CongestionGame ι) (σ : C.Profile)
    (r : C.Resource) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => r ∈ C.resources i (σ i)).card

/-- The finite set of resources occupied somewhere in a profile. -/
noncomputable def usedResources [Fintype ι] (C : CongestionGame ι) (σ : C.Profile) :
    Finset C.Resource := by
  classical
  exact Finset.univ.biUnion fun i => C.resources i (σ i)

@[simp]
theorem mem_usedResources [Fintype ι] {C : CongestionGame ι} {σ : C.Profile}
    {r : C.Resource} :
    r ∈ C.usedResources σ ↔ ∃ i, r ∈ C.resources i (σ i) := by
  classical
  simp [usedResources]

theorem resources_subset_usedResources [Fintype ι] (C : CongestionGame ι)
    (σ : C.Profile) (i : ι) : C.resources i (σ i) ⊆ C.usedResources σ :=
  fun _ hr => mem_usedResources.mpr ⟨i, hr⟩

/-- A resource absent from the occupied support has zero load. -/
theorem congestion_eq_zero_of_not_mem_usedResources [Fintype ι]
    {C : CongestionGame ι} {σ : C.Profile} {r : C.Resource}
    (h : r ∉ C.usedResources σ) : C.congestion σ r = 0 := by
  classical
  rw [congestion, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  exact fun hri => h (mem_usedResources.mpr ⟨i, hri⟩)

/-- The sum of delays on the resources selected by a player. -/
def playerCost [Fintype ι] (C : CongestionGame ι) (σ : C.Profile) (who : ι) : ℝ :=
  ∑ r ∈ C.resources who (σ who), C.delay r (C.congestion σ r)

/-- Total player cost at a profile. -/
def socialCost [Fintype ι] (C : CongestionGame ι) (σ : C.Profile) : ℝ :=
  ∑ i, C.playerCost σ i

/-- Utility is the negative player cost. -/
def utility [Fintype ι] (C : CongestionGame ι) : Utility C.toGameForm.sig :=
  fun profile who => -C.playerCost profile who

/-- The canonical bundled utility presentation. -/
def toUtilityGame [Fintype ι] (C : CongestionGame ι) : UtilityGame ι where
  form := C.toGameForm
  utility := C.utility

@[simp]
theorem expectedUtility_toGameForm [Fintype ι] (C : CongestionGame ι)
    (σ : C.Profile) (i : ι) :
    expectedUtility C.utility i (C.toGameForm.play σ) = -C.playerCost σ i := by
  simp [toGameForm, utility]

/-- Count the other players whose strategies occupy a resource. -/
noncomputable def congestionWithout [Fintype ι] (C : CongestionGame ι) (σ : C.Profile)
    (who : ι) (r : C.Resource) : ℕ := by
  classical
  exact (Finset.univ.filter fun i => i ≠ who ∧ r ∈ C.resources i (σ i)).card

open Classical in
/-- A full load is the other-player load plus this player's occupancy
indicator. -/
theorem congestion_decompose [Fintype ι] (C : CongestionGame ι) (σ : C.Profile)
    (who : ι) (r : C.Resource) :
    C.congestion σ r = C.congestionWithout σ who r +
      if r ∈ C.resources who (σ who) then 1 else 0 := by
  classical
  simp only [congestion, congestionWithout]
  set S := Finset.univ.filter fun i => r ∈ C.resources i (σ i)
  set T := Finset.univ.filter fun i => i ≠ who ∧ r ∈ C.resources i (σ i)
  have hT_eq : T = S.erase who := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      true_and, T, S, ne_eq]
  rw [hT_eq]
  split_ifs with h
  · have hm : who ∈ S := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
      exact h
    have : 0 < S.card := Finset.card_pos.mpr ⟨who, hm⟩
    rw [Finset.card_erase_of_mem hm]
    omega
  · have hm : who ∉ S := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
      exact h
    rw [Finset.erase_eq_self.mpr hm]
    omega

/-- Other-player congestion is invariant under a unilateral profile update. -/
theorem congestionWithout_update [Fintype ι] [DecidableEq ι]
    (C : CongestionGame ι) (σ : C.Profile) (who : ι) (s' : C.Strategy who)
    (r : C.Resource) :
    C.congestionWithout (GameTheory.Profile.update (sig := C.toGameForm.sig) σ who s') who r =
      C.congestionWithout σ who r := by
  classical
  simp only [congestionWithout]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hne, h⟩
    exact ⟨hne, by rwa [Profile.update_of_ne _ _ hne] at h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, by rwa [Profile.update_of_ne _ _ hne]⟩

open Classical in
/-- Congestion after a unilateral profile update. -/
theorem congestion_update [Fintype ι] [DecidableEq ι]
    (C : CongestionGame ι) (σ : C.Profile) (who : ι) (s' : C.Strategy who)
    (r : C.Resource) :
    C.congestion (GameTheory.Profile.update (sig := C.toGameForm.sig) σ who s') r =
      C.congestionWithout σ who r + if r ∈ C.resources who s' then 1 else 0 := by
  have h := congestion_decompose C
    (GameTheory.Profile.update (sig := C.toGameForm.sig) σ who s') who r
  rw [GameTheory.Profile.update_same] at h
  rw [h, congestionWithout_update]

open Classical in
/-- Other-player congestion is bounded by full congestion. -/
theorem congestionWithout_le_congestion [Fintype ι] (C : CongestionGame ι)
    (σ : C.Profile) (who : ι) (r : C.Resource) :
    C.congestionWithout σ who r ≤ C.congestion σ r := by
  classical
  rw [congestion_decompose C σ who r]
  split_ifs <;> omega

/-- Aggregate any per-resource quantity by its load. -/
theorem sum_players_sum_resources [Fintype ι] (C : CongestionGame ι)
    (σ : C.Profile) (f : C.Resource → ℝ) :
    ∑ i, ∑ r ∈ C.resources i (σ i), f r =
      ∑ r ∈ C.usedResources σ, (C.congestion σ r : ℝ) * f r := by
  classical
  have h : ∀ i, ∑ r ∈ C.resources i (σ i), f r =
      ∑ r ∈ C.usedResources σ, if r ∈ C.resources i (σ i) then f r else 0 := by
    intro i
    conv_rhs => rw [Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr (C.resources_subset_usedResources σ i)]
  simp only [h]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero,
    nsmul_eq_mul]
  rw [congestion]

/-- A load-weighted sum extends from occupied resources to any finite
superset, because outside resources have zero load. -/
theorem sum_congestion_mul_subset [Fintype ι] (C : CongestionGame ι)
    (σ : C.Profile) {S : Finset C.Resource} (hS : C.usedResources σ ⊆ S)
    (f : C.Resource → ℝ) :
    ∑ r ∈ C.usedResources σ, (C.congestion σ r : ℝ) * f r =
      ∑ r ∈ S, (C.congestion σ r : ℝ) * f r :=
  Finset.sum_subset hS fun r _ hr => by
    rw [congestion_eq_zero_of_not_mem_usedResources hr]
    simp

/-- Social cost aggregates by resource: every occupied resource contributes
its delay multiplied by its load. -/
theorem socialCost_eq_sum_load_delay [Fintype ι] (C : CongestionGame ι)
    (σ : C.Profile) :
    C.socialCost σ =
      ∑ r ∈ C.usedResources σ,
        (C.congestion σ r : ℝ) * C.delay r (C.congestion σ r) := by
  rw [socialCost]
  simp only [playerCost]
  exact C.sum_players_sum_resources σ _

end CongestionGame

end GameTheory
