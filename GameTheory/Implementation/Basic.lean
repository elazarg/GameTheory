/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.Subsidy
import GameTheory.Concepts.Dominance.Undominated

/-!
# k-implementation

Definitions from Monderer--Tennenholtz k-implementation for kernel games.

An interested party commits to profile-observed nonnegative transfers. A target
set is implemented when the subsidized game's undominated profiles are nonempty
and all lie in the target. A `k`-implementation additionally bounds total
transfers on every surviving profile by `k`.
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- A transfer scheme implements `O` when transfers are nonnegative, at least
one undominated profile survives, and every surviving undominated profile lies
in `O`. -/
def IsImplementation (G : KernelGame ι) (V : Profile G → Payoff ι)
    (O : Set (Profile G)) : Prop :=
  (∀ σ i, 0 ≤ V σ i) ∧
    ((G.subsidize V).undominatedProfiles).Nonempty ∧
      ∀ σ : Profile G, σ ∈ (G.subsidize V).undominatedProfiles → σ ∈ O

/-- A `k`-implementation is an implementation whose total transfer on every
surviving undominated profile is at most `k`. -/
def IsKImplementation (G : KernelGame ι) [Fintype ι] (V : Profile G → Payoff ι)
    (O : Set (Profile G)) (k : ℝ) : Prop :=
  G.IsImplementation V O ∧
    ∀ σ : Profile G, σ ∈ (G.subsidize V).undominatedProfiles →
      (∑ i, V σ i) ≤ k

/-- Candidate budgets that implement `O`. -/
def implementationCosts (G : KernelGame ι) [Fintype ι] (O : Set (Profile G)) :
    Set ℝ :=
  {k | ∃ V : Profile G → Payoff ι, G.IsKImplementation V O k}

/-- Infimum implementation cost. This is a definition-level wrapper; concrete
theorems should prove attainability or bounds under finite hypotheses. -/
noncomputable def implPrice (G : KernelGame ι) [Fintype ι] (O : Set (Profile G)) :
    ℝ :=
  sInf (G.implementationCosts O)

theorem IsImplementation.nonneg {G : KernelGame ι} {V : Profile G → Payoff ι}
    {O : Set (Profile G)} (h : G.IsImplementation V O) :
    ∀ σ i, 0 ≤ V σ i :=
  h.1

theorem IsImplementation.nonempty {G : KernelGame ι} {V : Profile G → Payoff ι}
    {O : Set (Profile G)} (h : G.IsImplementation V O) :
    ((G.subsidize V).undominatedProfiles).Nonempty :=
  h.2.1

theorem IsImplementation.subset {G : KernelGame ι} {V : Profile G → Payoff ι}
    {O : Set (Profile G)} (h : G.IsImplementation V O) :
    ∀ σ : Profile G, σ ∈ (G.subsidize V).undominatedProfiles → σ ∈ O :=
  h.2.2

theorem IsImplementation.mono_set {G : KernelGame ι} {V : Profile G → Payoff ι}
    {O O' : Set (Profile G)} (h : G.IsImplementation V O) (hOO' : O ⊆ O') :
    G.IsImplementation V O' :=
  ⟨h.nonneg, h.nonempty, fun σ hσ => hOO' (h.subset σ hσ)⟩

theorem IsKImplementation.implementation {G : KernelGame ι} [Fintype ι]
    {V : Profile G → Payoff ι} {O : Set (Profile G)} {k : ℝ}
    (h : G.IsKImplementation V O k) :
    G.IsImplementation V O :=
  h.1

theorem IsKImplementation.cost_bound {G : KernelGame ι} [Fintype ι]
    {V : Profile G → Payoff ι} {O : Set (Profile G)} {k : ℝ}
    (h : G.IsKImplementation V O k) :
    ∀ σ : Profile G, σ ∈ (G.subsidize V).undominatedProfiles → (∑ i, V σ i) ≤ k :=
  h.2

theorem IsKImplementation.nonneg {G : KernelGame ι} [Fintype ι]
    {V : Profile G → Payoff ι} {O : Set (Profile G)} {k : ℝ}
    (h : G.IsKImplementation V O k) :
    ∀ σ i, 0 ≤ V σ i :=
  h.implementation.nonneg

theorem IsKImplementation.mono_cost {G : KernelGame ι} [Fintype ι]
    {V : Profile G → Payoff ι} {O : Set (Profile G)} {k l : ℝ}
    (h : G.IsKImplementation V O k) (hkl : k ≤ l) :
    G.IsKImplementation V O l :=
  ⟨h.implementation, fun σ hσ => (h.cost_bound σ hσ).trans hkl⟩

theorem IsKImplementation.mono_set {G : KernelGame ι} [Fintype ι]
    {V : Profile G → Payoff ι} {O O' : Set (Profile G)} {k : ℝ}
    (h : G.IsKImplementation V O k) (hOO' : O ⊆ O') :
    G.IsKImplementation V O' k :=
  ⟨h.implementation.mono_set hOO', h.cost_bound⟩

/-! ## Transfer-class saturation -/

/-- Two strategies are equivalent relative to a transfer class when every
allowed subsidized game gives them the same utility row.  This is the
contextual equivalence induced by a restricted transfer language. -/
def TransferClassUtilityEquivalent (G : KernelGame ι)
    (C : Set (Profile G → Payoff ι)) (who : ι)
    (s t : G.Strategy who) : Prop :=
  ∀ V ∈ C, (G.subsidize V).UtilityEquivalent who s t

/-- Coordinatewise transfer-class equivalence of profiles. -/
def TransferClassProfileEquivalent (G : KernelGame ι)
    (C : Set (Profile G → Payoff ι)) (σ τ : Profile G) : Prop :=
  ∀ i, G.TransferClassUtilityEquivalent C i (σ i) (τ i)

theorem TransferClassUtilityEquivalent.refl {G : KernelGame ι}
    {C : Set (Profile G → Payoff ι)} {who : ι} (s : G.Strategy who) :
    G.TransferClassUtilityEquivalent C who s s := by
  intro V _hV
  exact UtilityEquivalent.refl (G := G.subsidize V) s

theorem TransferClassUtilityEquivalent.symm {G : KernelGame ι}
    {C : Set (Profile G → Payoff ι)} {who : ι} {s t : G.Strategy who}
    (h : G.TransferClassUtilityEquivalent C who s t) :
    G.TransferClassUtilityEquivalent C who t s := by
  intro V hV
  exact (h V hV).symm

theorem TransferClassUtilityEquivalent.trans {G : KernelGame ι}
    {C : Set (Profile G → Payoff ι)} {who : ι} {s t u : G.Strategy who}
    (hst : G.TransferClassUtilityEquivalent C who s t)
    (htu : G.TransferClassUtilityEquivalent C who t u) :
    G.TransferClassUtilityEquivalent C who s u := by
  intro V hV
  exact (hst V hV).trans (htu V hV)

theorem TransferClassProfileEquivalent.refl {G : KernelGame ι}
    {C : Set (Profile G → Payoff ι)} (σ : Profile G) :
    G.TransferClassProfileEquivalent C σ σ :=
  fun i => TransferClassUtilityEquivalent.refl (G := G) (C := C) (σ i)

theorem TransferClassProfileEquivalent.symm {G : KernelGame ι}
    {C : Set (Profile G → Payoff ι)} {σ τ : Profile G}
    (h : G.TransferClassProfileEquivalent C σ τ) :
    G.TransferClassProfileEquivalent C τ σ :=
  fun i => (h i).symm

theorem TransferClassProfileEquivalent.trans {G : KernelGame ι}
    {C : Set (Profile G → Payoff ι)} {σ τ υ : Profile G}
    (hστ : G.TransferClassProfileEquivalent C σ τ)
    (hτυ : G.TransferClassProfileEquivalent C τ υ) :
    G.TransferClassProfileEquivalent C σ υ :=
  fun i => (hστ i).trans (hτυ i)

/-- For any transfer from the class, transfer-class equivalent profiles are
simultaneously undominated. -/
theorem TransferClassProfileEquivalent.mem_undominatedProfiles_iff_of_mem
    {G : KernelGame ι} {C : Set (Profile G → Payoff ι)}
    {V : Profile G → Payoff ι} (hV : V ∈ C) {σ τ : Profile G}
    (hστ : G.TransferClassProfileEquivalent C σ τ) :
    σ ∈ (G.subsidize V).undominatedProfiles ↔
      τ ∈ (G.subsidize V).undominatedProfiles := by
  constructor
  · intro hσ i
    exact ((hστ i V hV).isUndominated_iff).mp (hσ i)
  · intro hτ i
    exact ((hστ i V hV).isUndominated_iff).mpr (hτ i)

/-- Any implementation using an allowed transfer contains a nonempty subset
that is saturated under the transfer class.  The subset can be taken to be the
undominated-profile set of the subsidized game. -/
theorem IsImplementation.exists_transferClassSaturated_subset
    {G : KernelGame ι} {C : Set (Profile G → Payoff ι)}
    {V : Profile G → Payoff ι} {O : Set (Profile G)}
    (h : G.IsImplementation V O) (hV : V ∈ C) :
    ∃ S : Set (Profile G), S.Nonempty ∧ S ⊆ O ∧
      ∀ σ ∈ S, ∀ τ : Profile G,
        G.TransferClassProfileEquivalent C σ τ → τ ∈ S := by
  refine ⟨(G.subsidize V).undominatedProfiles, h.nonempty, h.subset, ?_⟩
  intro σ hσ τ hστ
  exact (hστ.mem_undominatedProfiles_iff_of_mem hV).mp hσ

/-- A singleton can be implemented by a restricted transfer class only if the
target's transfer-class equivalence class is trivial. -/
theorem IsImplementation.eq_of_transferClassProfileEquivalent_singleton
    {G : KernelGame ι} {C : Set (Profile G → Payoff ι)}
    {V : Profile G → Payoff ι} {z τ : Profile G}
    (h : G.IsImplementation V ({z} : Set (Profile G))) (hV : V ∈ C)
    (hτz : G.TransferClassProfileEquivalent C τ z) :
    τ = z := by
  obtain ⟨σ, hσ⟩ := h.nonempty
  have hσz : σ = z := Set.mem_singleton_iff.mp (h.subset σ hσ)
  subst hσz
  have hτ : τ ∈ (G.subsidize V).undominatedProfiles := by
    exact (hτz.mem_undominatedProfiles_iff_of_mem hV).mpr hσ
  exact Set.mem_singleton_iff.mp (h.subset τ hτ)

/-- A k-implementation cannot have a negative budget: at least one profile
survives, transfers are nonnegative there, and the total surviving transfer is
bounded above by `k`. -/
theorem IsKImplementation.cost_nonneg {G : KernelGame ι} [Fintype ι]
    {V : Profile G → Payoff ι} {O : Set (Profile G)} {k : ℝ}
    (h : G.IsKImplementation V O k) : 0 ≤ k := by
  obtain ⟨σ, hσ⟩ := h.implementation.nonempty
  have hsum_nonneg : 0 ≤ ∑ i, V σ i :=
    Finset.sum_nonneg fun i _ => h.nonneg σ i
  exact hsum_nonneg.trans (h.cost_bound σ hσ)

/-- Feasible implementation budgets are bounded below by zero. -/
theorem implementationCosts_bddBelow (G : KernelGame ι) [Fintype ι]
    (O : Set (Profile G)) : BddBelow (G.implementationCosts O) :=
  ⟨0, fun _ hk => by
    obtain ⟨V, hV⟩ := hk
    exact hV.cost_nonneg⟩

/-- Any feasible budget is an upper bound on `implPrice`. -/
theorem implPrice_le_of_isKImplementation {G : KernelGame ι} [Fintype ι]
    {V : Profile G → Payoff ι} {O : Set (Profile G)} {k : ℝ}
    (h : G.IsKImplementation V O k) : G.implPrice O ≤ k := by
  exact csInf_le (G.implementationCosts_bddBelow O) ⟨V, h⟩

/-- If `O` is implementable at some budget, then `implPrice O` is nonnegative. -/
theorem implPrice_nonneg_of_implementationCosts_nonempty {G : KernelGame ι}
    [Fintype ι] {O : Set (Profile G)} (hne : (G.implementationCosts O).Nonempty) :
    0 ≤ G.implPrice O := by
  rw [implPrice]
  exact le_csInf hne fun _ hk => by
    obtain ⟨V, hV⟩ := hk
    exact hV.cost_nonneg

/-- Implementation feasible-budget sets are upward closed. -/
theorem implementationCosts_upward_closed {G : KernelGame ι} [Fintype ι]
    {O : Set (Profile G)} {k l : ℝ}
    (hk : k ∈ G.implementationCosts O) (hkl : k ≤ l) :
    l ∈ G.implementationCosts O := by
  rcases hk with ⟨V, hV⟩
  exact ⟨V, hV.mono_cost hkl⟩

/-- Every budget strictly above the implementation-price infimum is feasible,
provided the feasible-budget set is nonempty.  Attainment is exactly the
separate boundary question at equality. -/
theorem implementationCosts_mem_of_implPrice_lt {G : KernelGame ι} [Fintype ι]
    {O : Set (Profile G)} (hne : (G.implementationCosts O).Nonempty)
    {k : ℝ} (hk : G.implPrice O < k) :
    k ∈ G.implementationCosts O := by
  rw [implPrice] at hk
  rcases exists_lt_of_csInf_lt hne hk with ⟨l, hl, hlk⟩
  exact G.implementationCosts_upward_closed hl hlk.le

/-- If the infimum implementation price is itself feasible, the feasible-budget
set is exactly the ray above the price. -/
theorem implementationCosts_eq_Ici_implPrice_of_mem {G : KernelGame ι}
    [Fintype ι] {O : Set (Profile G)}
    (hmem : G.implPrice O ∈ G.implementationCosts O) :
    G.implementationCosts O = Set.Ici (G.implPrice O) := by
  ext k
  constructor
  · rintro ⟨V, hV⟩
    exact G.implPrice_le_of_isKImplementation hV
  · intro hk
    exact G.implementationCosts_upward_closed hmem hk

theorem weaklyDominates_subsidize_zero_iff {G : KernelGame ι}
    [Finite G.Outcome] {who : ι} {s t : G.Strategy who} :
    (G.subsidize (fun _ _ => 0)).WeaklyDominates who s t ↔
      G.WeaklyDominates who s t := by
  constructor
  · intro h σ
    have hσ := h σ
    simpa using hσ
  · intro h σ
    have hσ := h σ
    simpa using hσ

theorem weaklyStrictlyDominates_subsidize_zero_iff {G : KernelGame ι}
    [Finite G.Outcome] {who : ι} {s t : G.Strategy who} :
    (G.subsidize (fun _ _ => 0)).WeaklyStrictlyDominates who s t ↔
      G.WeaklyStrictlyDominates who s t := by
  constructor
  · intro h
    refine ⟨(weaklyDominates_subsidize_zero_iff (G := G)).mp h.toWeaklyDominates, ?_⟩
    · obtain ⟨σ, hσ⟩ := h.strict_witness
      exact ⟨σ, by simpa using hσ⟩
  · intro h
    refine ⟨(weaklyDominates_subsidize_zero_iff (G := G)).mpr h.toWeaklyDominates, ?_⟩
    · obtain ⟨σ, hσ⟩ := h.strict_witness
      exact ⟨σ, by simpa using hσ⟩

theorem undominatedProfiles_subsidize_zero_eq (G : KernelGame ι)
    [Finite G.Outcome] :
    (G.subsidize (fun _ _ => 0)).undominatedProfiles = G.undominatedProfiles := by
  ext σ
  constructor
  · intro hσ i t ht
    exact hσ i t ((weaklyStrictlyDominates_subsidize_zero_iff (G := G)).mpr ht)
  · intro hσ i t ht
    exact hσ i t ((weaklyStrictlyDominates_subsidize_zero_iff (G := G)).mp ht)

end KernelGame

end GameTheory
