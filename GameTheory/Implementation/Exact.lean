/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation.Basic

/-!
# Exact k-implementation

Definition layer for exact implementation: the undominated-profile set of the
subsidized game is required to be exactly the target set. The optimal algorithmic
claims in Monderer--Tennenholtz are handled cautiously; later work gives corrected
targets for exact optimal cost, so this file only states definitions and general
facts that are independent of those claims.

The paper's Theorem 4 SAT reduction is also not exposed here as a positive
theorem: later work reports the original two-player reduction false, and the
corrected reductions require external constructions not present in this
library.  Concrete exact-implementation counterexamples and the verified
optimal-perturbation failure live in `GameTheory.Implementation.Examples`.
-/

namespace GameTheory

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- A transfer scheme exactly implements `O` when the subsidized game's
undominated profiles are precisely `O`. -/
def IsExactImplementation (G : KernelGame ι) (V : Profile G → Payoff ι)
    (O : Set (Profile G)) : Prop :=
  (∀ σ i, 0 ≤ V σ i) ∧ (G.subsidize V).undominatedProfiles = O

/-- A `k`-exact implementation is an exact implementation whose total transfer
is at most `k` on each exactly surviving profile. -/
def IsExactKImplementation (G : KernelGame ι) [Fintype ι]
    (V : Profile G → Payoff ι) (O : Set (Profile G)) (k : ℝ) : Prop :=
  G.IsExactImplementation V O ∧ ∀ σ : Profile G, σ ∈ O → (∑ i, V σ i) ≤ k

/-- Candidate budgets that exactly implement `O`. -/
def exactImplementationCosts (G : KernelGame ι) [Fintype ι]
    (O : Set (Profile G)) : Set ℝ :=
  {k | ∃ V : Profile G → Payoff ι, G.IsExactKImplementation V O k}

/-- Infimum exact implementation cost. Concrete theorem statements should prove
the target set is exactly implementable and establish bounds before using it as
an attained optimum. -/
noncomputable def exactImplPrice (G : KernelGame ι) [Fintype ι]
    (O : Set (Profile G)) : ℝ :=
  sInf (G.exactImplementationCosts O)

theorem IsExactImplementation.nonneg {G : KernelGame ι} {V : Profile G → Payoff ι}
    {O : Set (Profile G)} (h : G.IsExactImplementation V O) :
    ∀ σ i, 0 ≤ V σ i :=
  h.1

theorem IsExactImplementation.undominatedProfiles_eq {G : KernelGame ι}
    {V : Profile G → Payoff ι} {O : Set (Profile G)}
    (h : G.IsExactImplementation V O) :
    (G.subsidize V).undominatedProfiles = O :=
  h.2

theorem IsExactImplementation.mem_undominatedProfiles_iff {G : KernelGame ι}
    {V : Profile G → Payoff ι} {O : Set (Profile G)}
    (h : G.IsExactImplementation V O) {σ : Profile G} :
    σ ∈ (G.subsidize V).undominatedProfiles ↔ σ ∈ O := by
  rw [h.undominatedProfiles_eq]
  exact Iff.rfl

theorem IsExactImplementation.toImplementation {G : KernelGame ι}
    {V : Profile G → Payoff ι} {O : Set (Profile G)}
    (h : G.IsExactImplementation V O) (hO : O.Nonempty) :
    G.IsImplementation V O := by
  refine ⟨h.nonneg, ?_, ?_⟩
  · rwa [h.undominatedProfiles_eq]
  · intro σ hσ
    exact (h.mem_undominatedProfiles_iff).mp hσ

theorem IsExactKImplementation.exactImplementation {G : KernelGame ι} [Fintype ι]
    {V : Profile G → Payoff ι} {O : Set (Profile G)} {k : ℝ}
    (h : G.IsExactKImplementation V O k) :
    G.IsExactImplementation V O :=
  h.1

theorem IsExactKImplementation.cost_bound {G : KernelGame ι} [Fintype ι]
    {V : Profile G → Payoff ι} {O : Set (Profile G)} {k : ℝ}
    (h : G.IsExactKImplementation V O k) :
    ∀ σ : Profile G, σ ∈ O → (∑ i, V σ i) ≤ k :=
  h.2

theorem IsExactKImplementation.nonneg {G : KernelGame ι} [Fintype ι]
    {V : Profile G → Payoff ι} {O : Set (Profile G)} {k : ℝ}
    (h : G.IsExactKImplementation V O k) :
    ∀ σ i, 0 ≤ V σ i :=
  h.exactImplementation.nonneg

theorem IsExactKImplementation.mono_cost {G : KernelGame ι} [Fintype ι]
    {V : Profile G → Payoff ι} {O : Set (Profile G)} {k l : ℝ}
    (h : G.IsExactKImplementation V O k) (hkl : k ≤ l) :
    G.IsExactKImplementation V O l :=
  ⟨h.exactImplementation, fun σ hσ => (h.cost_bound σ hσ).trans hkl⟩

theorem zeroTransfer_isExactKImplementation_of_undominatedProfiles_eq
    (G : KernelGame ι) [Fintype ι] [Finite G.Outcome]
    {O : Set (Profile G)} (hO : G.undominatedProfiles = O) :
    G.IsExactKImplementation (fun _ _ => 0) O 0 := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro σ i
    norm_num
  · rw [undominatedProfiles_subsidize_zero_eq, hO]
  · intro σ hσ
    simp

theorem IsExactKImplementation.toKImplementation {G : KernelGame ι} [Fintype ι]
    {V : Profile G → Payoff ι} {O : Set (Profile G)} {k : ℝ}
    (h : G.IsExactKImplementation V O k) (hO : O.Nonempty) :
    G.IsKImplementation V O k := by
  refine ⟨h.exactImplementation.toImplementation hO, ?_⟩
  intro σ hσ
  exact h.cost_bound σ ((h.exactImplementation.mem_undominatedProfiles_iff).mp hσ)

/-- If the target is a singleton, ordinary implementation is automatically exact:
nonemptiness supplies the target profile, and subset containment rules out every
other undominated profile. -/
theorem IsImplementation.toExactImplementation_singleton {G : KernelGame ι}
    {V : Profile G → Payoff ι} {z : Profile G}
    (h : G.IsImplementation V ({z} : Set (Profile G))) :
    G.IsExactImplementation V ({z} : Set (Profile G)) := by
  refine ⟨h.nonneg, ?_⟩
  have hzundom : z ∈ (G.subsidize V).undominatedProfiles := by
    obtain ⟨σ, hσ⟩ := h.nonempty
    have hσz : σ = z := Set.mem_singleton_iff.mp (h.subset σ hσ)
    rw [hσz] at hσ
    exact hσ
  apply Set.Subset.antisymm
  · intro σ hσ
    exact h.subset σ hσ
  · intro σ hσ
    rw [Set.mem_singleton_iff.mp hσ]
    exact hzundom

/-- Singleton ordinary k-implementation is automatically exact
k-implementation. -/
theorem IsKImplementation.toExactKImplementation_singleton {G : KernelGame ι}
    [Fintype ι] {V : Profile G → Payoff ι} {z : Profile G} {k : ℝ}
    (h : G.IsKImplementation V ({z} : Set (Profile G)) k) :
    G.IsExactKImplementation V ({z} : Set (Profile G)) k := by
  let hexact := h.implementation.toExactImplementation_singleton
  refine ⟨hexact, ?_⟩
  intro σ hσ
  exact h.cost_bound σ ((hexact.mem_undominatedProfiles_iff).mpr hσ)

/-- Exact and ordinary feasible budgets coincide for singleton targets. -/
theorem exactImplementationCosts_singleton_eq_implementationCosts
    (G : KernelGame ι) [Fintype ι] (z : Profile G) :
    G.exactImplementationCosts ({z} : Set (Profile G)) =
      G.implementationCosts ({z} : Set (Profile G)) := by
  ext k
  constructor
  · rintro ⟨V, hV⟩
    exact ⟨V, hV.toKImplementation ⟨z, by simp⟩⟩
  · rintro ⟨V, hV⟩
    exact ⟨V, hV.toExactKImplementation_singleton⟩

/-- Exact and ordinary implementation prices coincide for singleton targets. -/
theorem exactImplPrice_singleton_eq_implPrice
    (G : KernelGame ι) [Fintype ι] (z : Profile G) :
    G.exactImplPrice ({z} : Set (Profile G)) =
      G.implPrice ({z} : Set (Profile G)) := by
  rw [exactImplPrice, implPrice,
    exactImplementationCosts_singleton_eq_implementationCosts G z]

theorem IsExactKImplementation.cost_nonneg_of_nonempty {G : KernelGame ι}
    [Fintype ι] {V : Profile G → Payoff ι} {O : Set (Profile G)} {k : ℝ}
    (h : G.IsExactKImplementation V O k) (hO : O.Nonempty) : 0 ≤ k := by
  obtain ⟨σ, hσO⟩ := hO
  have hsum_nonneg : 0 ≤ ∑ i, V σ i :=
    Finset.sum_nonneg fun i _ => h.nonneg σ i
  exact hsum_nonneg.trans (h.cost_bound σ hσO)

/-- Exact feasible budgets for a nonempty target set are bounded below by zero. -/
theorem exactImplementationCosts_bddBelow_of_nonempty
    (G : KernelGame ι) [Fintype ι] {O : Set (Profile G)} (hO : O.Nonempty) :
    BddBelow (G.exactImplementationCosts O) :=
  ⟨0, fun _ hk => by
    obtain ⟨V, hV⟩ := hk
    exact hV.cost_nonneg_of_nonempty hO⟩

/-- Any exact feasible budget for a nonempty target set is an upper bound on
`exactImplPrice`. -/
theorem exactImplPrice_le_of_isExactKImplementation {G : KernelGame ι}
    [Fintype ι] {V : Profile G → Payoff ι} {O : Set (Profile G)} {k : ℝ}
    (h : G.IsExactKImplementation V O k) (hO : O.Nonempty) :
    G.exactImplPrice O ≤ k := by
  exact csInf_le (G.exactImplementationCosts_bddBelow_of_nonempty hO) ⟨V, h⟩

/-- Exact feasible-budget sets are upward closed. -/
theorem exactImplementationCosts_upward_closed {G : KernelGame ι} [Fintype ι]
    {O : Set (Profile G)} {k l : ℝ}
    (hk : k ∈ G.exactImplementationCosts O) (hkl : k ≤ l) :
    l ∈ G.exactImplementationCosts O := by
  rcases hk with ⟨V, hV⟩
  exact ⟨V, hV.mono_cost hkl⟩

/-- Every budget strictly above the exact-implementation-price infimum is
feasible, provided the exact feasible-budget set is nonempty. -/
theorem exactImplementationCosts_mem_of_exactImplPrice_lt
    {G : KernelGame ι} [Fintype ι] {O : Set (Profile G)}
    (hne : (G.exactImplementationCosts O).Nonempty)
    {k : ℝ} (hk : G.exactImplPrice O < k) :
    k ∈ G.exactImplementationCosts O := by
  rw [exactImplPrice] at hk
  rcases exists_lt_of_csInf_lt hne hk with ⟨l, hl, hlk⟩
  exact G.exactImplementationCosts_upward_closed hl hlk.le

/-- If the infimum exact price is itself feasible, the feasible-budget set is
exactly the ray above the exact price. -/
theorem exactImplementationCosts_eq_Ici_exactImplPrice_of_mem {G : KernelGame ι}
    [Fintype ι] {O : Set (Profile G)} (hO : O.Nonempty)
    (hmem : G.exactImplPrice O ∈ G.exactImplementationCosts O) :
    G.exactImplementationCosts O = Set.Ici (G.exactImplPrice O) := by
  ext k
  constructor
  · rintro ⟨V, hV⟩
    exact G.exactImplPrice_le_of_isExactKImplementation hV hO
  · intro hk
    exact G.exactImplementationCosts_upward_closed hmem hk

/-! ## The paper's two-player OP perturbation pattern -/

section OptimalPerturbation

variable (G : KernelGame (Fin 2))

/-- Rectangular target set `O₀ × O₁` for the two-player exact-implementation
algorithm in Section 4 of the paper. -/
def twoPlayerRect (O₀ : Set (G.Strategy 0)) (O₁ : Set (G.Strategy 1)) :
    Set (Profile G) :=
  {σ | σ 0 ∈ O₀ ∧ σ 1 ∈ O₁}

@[simp] theorem mem_twoPlayerRect {O₀ : Set (G.Strategy 0)} {O₁ : Set (G.Strategy 1)}
    {σ : Profile G} :
    σ ∈ G.twoPlayerRect O₀ O₁ ↔ σ 0 ∈ O₀ ∧ σ 1 ∈ O₁ :=
  Iff.rfl

/-- Transfer-agnostic exact implementation criterion for a two-player
rectangular target. If each player's undominated strategies in the subsidized
game are exactly the corresponding side of the rectangle, then the undominated
profiles are exactly the rectangle. -/
theorem transfer_isExactKImplementation_twoPlayerRect_of_checks
    [Finite G.Outcome]
    {V : Profile G → Payoff (Fin 2)}
    {O₀ : Set (G.Strategy 0)} {O₁ : Set (G.Strategy 1)} {k : ℝ}
    (hV : ∀ σ i, 0 ≤ V σ i)
    (h₀ : ∀ s : G.Strategy 0, (G.subsidize V).IsUndominated 0 s ↔ s ∈ O₀)
    (h₁ : ∀ s : G.Strategy 1, (G.subsidize V).IsUndominated 1 s ↔ s ∈ O₁)
    (hcost : ∀ σ : Profile G, σ ∈ G.twoPlayerRect O₀ O₁ → (∑ i, V σ i) ≤ k) :
    G.IsExactKImplementation V (G.twoPlayerRect O₀ O₁) k := by
  refine ⟨?_, hcost⟩
  refine ⟨hV, ?_⟩
  ext σ
  constructor
  · intro hσ
    exact ⟨(h₀ (σ 0)).mp (hσ 0), (h₁ (σ 1)).mp (hσ 1)⟩
  · intro hσ i
    fin_cases i
    · exact (h₀ (σ 0)).mpr hσ.1
    · exact (h₁ (σ 1)).mpr hσ.2

/-- The OP perturbation matrix from Section 4, parameterized by the large
off-rectangle bonus `M` and the two uniform on-target bonuses `e₀`, `e₁`.

The later literature refutes the paper's optimality claim for the loop that
chooses `e₀,e₁`; this definition intentionally records only the perturbation
shape. -/
noncomputable def optimalPerturbationTransfer
    (O₀ : Set (G.Strategy 0)) (O₁ : Set (G.Strategy 1))
    [DecidablePred (fun s : G.Strategy 0 => s ∈ O₀)]
    [DecidablePred (fun s : G.Strategy 1 => s ∈ O₁)]
    (M e₀ e₁ : ℝ) : Profile G → Payoff (Fin 2) :=
  fun σ i =>
    if i = 0 then
      if _h₀ : σ 0 ∈ O₀ then
        if _h₁ : σ 1 ∈ O₁ then e₀ else M
      else 0
    else
      if _h₁ : σ 1 ∈ O₁ then
        if _h₀ : σ 0 ∈ O₀ then e₁ else M
      else 0

@[simp] theorem optimalPerturbationTransfer_zero
    (O₀ : Set (G.Strategy 0)) (O₁ : Set (G.Strategy 1))
    [DecidablePred (fun s : G.Strategy 0 => s ∈ O₀)]
    [DecidablePred (fun s : G.Strategy 1 => s ∈ O₁)]
    (M e₀ e₁ : ℝ) (σ : Profile G) :
    G.optimalPerturbationTransfer O₀ O₁ M e₀ e₁ σ 0 =
      if _h₀ : σ 0 ∈ O₀ then
        if _h₁ : σ 1 ∈ O₁ then e₀ else M
      else 0 := by
  simp [optimalPerturbationTransfer]

@[simp] theorem optimalPerturbationTransfer_one
    (O₀ : Set (G.Strategy 0)) (O₁ : Set (G.Strategy 1))
    [DecidablePred (fun s : G.Strategy 0 => s ∈ O₀)]
    [DecidablePred (fun s : G.Strategy 1 => s ∈ O₁)]
    (M e₀ e₁ : ℝ) (σ : Profile G) :
    G.optimalPerturbationTransfer O₀ O₁ M e₀ e₁ σ 1 =
      if _h₁ : σ 1 ∈ O₁ then
        if _h₀ : σ 0 ∈ O₀ then e₁ else M
      else 0 := by
  simp [optimalPerturbationTransfer]

/-- OP transfers are nonnegative when the three bonuses are nonnegative. -/
theorem optimalPerturbationTransfer_nonneg
    {O₀ : Set (G.Strategy 0)} {O₁ : Set (G.Strategy 1)}
    [DecidablePred (fun s : G.Strategy 0 => s ∈ O₀)]
    [DecidablePred (fun s : G.Strategy 1 => s ∈ O₁)]
    {M e₀ e₁ : ℝ} (hM : 0 ≤ M) (he₀ : 0 ≤ e₀) (he₁ : 0 ≤ e₁) :
    ∀ σ i, 0 ≤ G.optimalPerturbationTransfer O₀ O₁ M e₀ e₁ σ i := by
  classical
  intro σ i
  fin_cases i
  · by_cases h₀ : σ 0 ∈ O₀ <;> by_cases h₁ : σ 1 ∈ O₁ <;>
      simp [h₀, h₁, hM, he₀]
  · by_cases h₀ : σ 0 ∈ O₀ <;> by_cases h₁ : σ 1 ∈ O₁ <;>
      simp [h₀, h₁, hM, he₁]

/-- On the target rectangle, the OP transfer cost is exactly `e₀ + e₁`. -/
theorem optimalPerturbationTransfer_sum_on_rect
    {O₀ : Set (G.Strategy 0)} {O₁ : Set (G.Strategy 1)}
    [DecidablePred (fun s : G.Strategy 0 => s ∈ O₀)]
    [DecidablePred (fun s : G.Strategy 1 => s ∈ O₁)]
    {M e₀ e₁ : ℝ} {σ : Profile G}
    (hσ : σ ∈ G.twoPlayerRect O₀ O₁) :
    (∑ i : Fin 2, G.optimalPerturbationTransfer O₀ O₁ M e₀ e₁ σ i) =
      e₀ + e₁ := by
  classical
  rw [Fin.sum_univ_two]
  simp [hσ.1, hσ.2]

/-- Soundness of the paper's OP perturbation pattern. If the two post-loop
checks hold, namely the undominated strategies of the perturbed game are exactly
`O₀` and `O₁`, then the resulting transfer exactly implements `O₀ × O₁` at
cost `e₀ + e₁`.

This is deliberately not the false optimality claim from Theorem 5; it is only
the construction's exact-implementation certificate once its stated tests pass. -/
theorem optimalPerturbationTransfer_isExactKImplementation_of_checks
    [Finite G.Outcome]
    {O₀ : Set (G.Strategy 0)} {O₁ : Set (G.Strategy 1)}
    [DecidablePred (fun s : G.Strategy 0 => s ∈ O₀)]
    [DecidablePred (fun s : G.Strategy 1 => s ∈ O₁)]
    {M e₀ e₁ : ℝ} (hM : 0 ≤ M) (he₀ : 0 ≤ e₀) (he₁ : 0 ≤ e₁)
    (h₀ : ∀ s : G.Strategy 0,
      (G.subsidize (G.optimalPerturbationTransfer O₀ O₁ M e₀ e₁)).IsUndominated
        0 s ↔ s ∈ O₀)
    (h₁ : ∀ s : G.Strategy 1,
      (G.subsidize (G.optimalPerturbationTransfer O₀ O₁ M e₀ e₁)).IsUndominated
        1 s ↔ s ∈ O₁) :
    G.IsExactKImplementation
      (G.optimalPerturbationTransfer O₀ O₁ M e₀ e₁)
      (G.twoPlayerRect O₀ O₁) (e₀ + e₁) := by
  exact G.transfer_isExactKImplementation_twoPlayerRect_of_checks
    (G.optimalPerturbationTransfer_nonneg hM he₀ he₁) h₀ h₁
    (fun σ hσ => by rw [G.optimalPerturbationTransfer_sum_on_rect hσ])

end OptimalPerturbation

/-! ## A finite OP non-optimality counterexample -/

namespace OptimalPerturbationCounterexample

/-- Row and column strategy spaces for the 3-by-2 exact-implementation
counterexample from later work on the paper's OP algorithm. -/
def Strategy : Fin 2 → Type
  | 0 => Fin 3
  | 1 => Fin 2

instance strategyFintype : (i : Fin 2) → Fintype (Strategy i)
  | 0 => inferInstanceAs (Fintype (Fin 3))
  | 1 => inferInstanceAs (Fintype (Fin 2))

instance strategyDecidableEq : (i : Fin 2) → DecidableEq (Strategy i)
  | 0 => inferInstanceAs (DecidableEq (Fin 3))
  | 1 => inferInstanceAs (DecidableEq (Fin 2))

/-- First row. -/
def row0 : Strategy 0 := by
  change Fin 3
  exact 0

/-- Second row. -/
def row1 : Strategy 0 := by
  change Fin 3
  exact 1

/-- Third row. -/
def row2 : Strategy 0 := by
  change Fin 3
  exact 2

/-- First column. -/
def col0 : Strategy 1 := by
  change Fin 2
  exact 0

/-- Second column. -/
def col1 : Strategy 1 := by
  change Fin 2
  exact 1

/-- A concrete profile in the counterexample. -/
def profile (r : Fin 3) (c : Fin 2) : (i : Fin 2) → Strategy i
  | 0 => r
  | 1 => c

@[simp] theorem profile_zero (r : Fin 3) (c : Fin 2) :
    profile r c 0 = r := rfl

@[simp] theorem profile_one (r : Fin 3) (c : Fin 2) :
    profile r c 1 = c := rfl

/-- Original payoff table `G`. -/
def payoffTable (r : Fin 3) (c : Fin 2) : Payoff (Fin 2) :=
  fun
    | 0 =>
        if r.val = 0 ∧ c.val = 0 then 2
        else if r.val = 1 ∧ c.val = 1 then 2
        else if r.val = 2 ∧ c.val = 0 then 4
        else 0
    | 1 =>
        if r.val = 1 ∧ c.val = 1 then 3 else 0

/-- Original payoff as a profile-indexed function. -/
def payoff (σ : (i : Fin 2) → Strategy i) : Payoff (Fin 2) :=
  payoffTable (σ 0) (σ 1)

/-- The deterministic kernel game for the counterexample. -/
noncomputable abbrev game : KernelGame (Fin 2) :=
  KernelGame.ofPureEU Strategy payoff

instance game_outcome_finite : Finite game.Outcome := by
  change Finite ((i : Fin 2) → Strategy i)
  infer_instance

instance game_row_fintype : Fintype (game.Strategy 0) := by
  change Fintype (Strategy 0)
  infer_instance

instance game_col_fintype : Fintype (game.Strategy 1) := by
  change Fintype (Strategy 1)
  infer_instance

instance game_row_decidableEq : DecidableEq (game.Strategy 0) := by
  change DecidableEq (Strategy 0)
  infer_instance

instance game_col_decidableEq : DecidableEq (game.Strategy 1) := by
  change DecidableEq (Strategy 1)
  infer_instance

@[simp] theorem game_eu (σ : Profile game) (i : Fin 2) :
    game.eu σ i = payoff σ i := by
  simp [game]

/-- Rows retained by the target rectangle. -/
def rowTarget : Set (game.Strategy 0) := {r | r.val = 0 ∨ r.val = 1}

/-- Columns retained by the target rectangle. -/
def colTarget : Set (game.Strategy 1) := {c | c.val = 0}

instance rowTarget_decidablePred :
    DecidablePred (fun r : game.Strategy 0 => r ∈ rowTarget) := by
  intro r
  change Decidable (r.val = 0 ∨ r.val = 1)
  infer_instance

instance colTarget_decidablePred :
    DecidablePred (fun c : game.Strategy 1 => c ∈ colTarget) := by
  intro c
  change Decidable (c.val = 0)
  infer_instance

/-- The target rectangle `({0,1} × {0})`. -/
abbrev target : Set (Profile game) :=
  game.twoPlayerRect rowTarget colTarget

/-- The cheaper transfer `V₁`, with target cost at most `3`. -/
def cheapTransferTable (r : Fin 3) (c : Fin 2) : Payoff (Fin 2) :=
  fun
    | 0 =>
        if r.val = 0 ∧ c.val = 0 then 2
        else if (r.val = 0 ∨ r.val = 1) ∧ c.val = 1 then 5
        else 0
    | 1 =>
        if r.val = 1 ∧ c.val = 0 then 3
        else if r.val = 2 ∧ c.val = 0 then 5
        else 0

/-- The cheaper transfer as a profile-indexed function. -/
def cheapTransfer : Profile game → Payoff (Fin 2) :=
  fun σ => cheapTransferTable (σ 0) (σ 1)

/-- The OP-shaped transfer `V₂`, with target cost `5`. -/
def opTransferTable (r : Fin 3) (c : Fin 2) : Payoff (Fin 2) :=
  fun
    | 0 =>
        if (r.val = 0 ∨ r.val = 1) ∧ c.val = 0 then 2
        else if (r.val = 0 ∨ r.val = 1) ∧ c.val = 1 then 5
        else 0
    | 1 =>
        if (r.val = 0 ∨ r.val = 1) ∧ c.val = 0 then 3
        else if r.val = 2 ∧ c.val = 0 then 5
        else 0

/-- The OP-shaped transfer as a profile-indexed function. -/
def opTransfer : Profile game → Payoff (Fin 2) :=
  fun σ => opTransferTable (σ 0) (σ 1)

instance cheap_subsidize_row_fintype :
    Fintype ((game.subsidize cheapTransfer).Strategy 0) := by
  change Fintype (game.Strategy 0)
  infer_instance

instance cheap_subsidize_col_fintype :
    Fintype ((game.subsidize cheapTransfer).Strategy 1) := by
  change Fintype (game.Strategy 1)
  infer_instance

instance op_subsidize_row_fintype :
    Fintype ((game.subsidize opTransfer).Strategy 0) := by
  change Fintype (game.Strategy 0)
  infer_instance

instance op_subsidize_col_fintype :
    Fintype ((game.subsidize opTransfer).Strategy 1) := by
  change Fintype (game.Strategy 1)
  infer_instance

theorem profile_eta (σ : Profile game) :
    σ = profile (σ 0) (σ 1) := by
  funext i
  fin_cases i <;> simp [profile]

@[simp] theorem profile_update_zero (σ : Profile game) (r : Fin 3) :
    Function.update σ 0 r = profile r (σ 1) := by
  funext i
  fin_cases i <;> simp [profile]

@[simp] theorem profile_update_one (σ : Profile game) (c : Fin 2) :
    Function.update σ 1 c = profile (σ 0) c := by
  funext i
  fin_cases i <;> simp [profile]

theorem cheapTransfer_nonneg :
    ∀ σ i, 0 ≤ cheapTransfer σ i := by
  intro σ i
  fin_cases i <;>
    simp [cheapTransfer, cheapTransferTable] <;>
    split_ifs <;>
    norm_num

theorem opTransfer_nonneg :
    ∀ σ i, 0 ≤ opTransfer σ i := by
  intro σ i
  fin_cases i <;>
    simp [opTransfer, opTransferTable] <;>
    split_ifs <;>
    norm_num

theorem cheap_row0_dominates_row2 :
    (game.subsidize cheapTransfer).WeaklyStrictlyDominates 0
      row0 row2 := by
  refine ⟨?_, ?_⟩
  · intro σ
    let c : Fin 2 := σ 1
    have hrow0 : Function.update σ 0 row0 = profile row0 c := by
      funext i
      fin_cases i <;> simp [profile, c, row0]
    have hrow2 : Function.update σ 0 row2 = profile row2 c := by
      funext i
      fin_cases i <;> simp [profile, c, row2]
    rw [subsidize_eu, subsidize_eu]
    rw [hrow0, hrow2]
    clear_value c
    fin_cases c <;>
      norm_num [payoff, payoffTable, cheapTransfer, cheapTransferTable, profile,
        row0, row2]
  · exact ⟨profile row0 col1, by
      rw [subsidize_eu, subsidize_eu]
      norm_num [payoff, payoffTable, cheapTransfer, cheapTransferTable, profile,
        row0, row2, col1]⟩

theorem cheap_col0_dominates_col1 :
    (game.subsidize cheapTransfer).WeaklyStrictlyDominates 1
      col0 col1 := by
  refine ⟨?_, ?_⟩
  · intro σ
    let r : Fin 3 := σ 0
    have hcol0 : Function.update σ 1 col0 = profile r col0 := by
      funext i
      fin_cases i <;> simp [profile, r, col0]
    have hcol1 : Function.update σ 1 col1 = profile r col1 := by
      funext i
      fin_cases i <;> simp [profile, r, col1]
    rw [subsidize_eu, subsidize_eu]
    rw [hcol0, hcol1]
    clear_value r
    fin_cases r <;>
      norm_num [payoff, payoffTable, cheapTransfer, cheapTransferTable, profile,
        col0, col1]
  · exact ⟨profile row2 col0, by
      rw [subsidize_eu, subsidize_eu]
      norm_num [payoff, payoffTable, cheapTransfer, cheapTransferTable, profile,
        row2, col0, col1]⟩

theorem cheap_rowTarget_undominated_iff
    (r : game.Strategy 0) :
    (game.subsidize cheapTransfer).IsUndominated 0 r ↔ r ∈ rowTarget := by
  constructor
  · intro hr
    fin_cases r
    · norm_num [rowTarget]
    · norm_num [rowTarget]
    · exact False.elim (hr row0 cheap_row0_dominates_row2)
  · intro hr t ht
    fin_cases r <;> fin_cases t
    · exact WeaklyStrictlyDominates.irrefl
        (G := game.subsidize cheapTransfer) (who := 0) row0 ht
    · have hweak := ht.toWeaklyDominates (profile row0 col0)
      norm_num [payoff, payoffTable, cheapTransfer, cheapTransferTable, profile,
        row0, row1, col0] at hweak
    · have hweak := ht.toWeaklyDominates (profile row0 col1)
      norm_num [payoff, payoffTable, cheapTransfer, cheapTransferTable, profile,
        row0, row2, col1] at hweak
    · have hweak := ht.toWeaklyDominates (profile row0 col1)
      norm_num [payoff, payoffTable, cheapTransfer, cheapTransferTable, profile,
        row0, row1, col1] at hweak
    · exact WeaklyStrictlyDominates.irrefl
        (G := game.subsidize cheapTransfer) (who := 0) row1 ht
    · have hweak := ht.toWeaklyDominates (profile row1 col1)
      norm_num [payoff, payoffTable, cheapTransfer, cheapTransferTable, profile,
        row1, row2, col1] at hweak
    · norm_num [rowTarget] at hr
    · norm_num [rowTarget] at hr
    · norm_num [rowTarget] at hr

theorem cheap_colTarget_undominated_iff
    (c : game.Strategy 1) :
    (game.subsidize cheapTransfer).IsUndominated 1 c ↔ c ∈ colTarget := by
  constructor
  · intro hc
    fin_cases c
    · norm_num [colTarget]
    · exact False.elim (hc col0 cheap_col0_dominates_col1)
  · intro hc t ht
    fin_cases c <;> fin_cases t
    · exact WeaklyStrictlyDominates.irrefl
        (G := game.subsidize cheapTransfer) (who := 1) col0 ht
    · have hweak := ht.toWeaklyDominates (profile row2 col0)
      norm_num [payoff, payoffTable, cheapTransfer, cheapTransferTable, profile,
        row2, col0, col1] at hweak
    · norm_num [colTarget] at hc
    · norm_num [colTarget] at hc

theorem cheapTransfer_cost_on_target_le_three
    (σ : Profile game) (hσ : σ ∈ target) :
    (∑ i : Fin 2, cheapTransfer σ i) ≤ 3 := by
  let r : Fin 3 := σ 0
  let c : Fin 2 := σ 1
  have hprofile : σ = profile r c := by
    rw [profile_eta σ]
  rw [hprofile] at hσ
  rw [Fin.sum_univ_two, hprofile]
  rcases hσ with ⟨hr, hc⟩
  clear_value r
  clear_value c
  fin_cases r <;> fin_cases c
  all_goals
    norm_num [rowTarget, colTarget, cheapTransfer, cheapTransferTable,
      profile] at *

theorem cheapTransfer_isExactKImplementation :
    game.IsExactKImplementation cheapTransfer target 3 := by
  exact game.transfer_isExactKImplementation_twoPlayerRect_of_checks
    cheapTransfer_nonneg cheap_rowTarget_undominated_iff
    cheap_colTarget_undominated_iff cheapTransfer_cost_on_target_le_three

theorem opTransfer_eq_optimalPerturbationTransfer :
    opTransfer =
      game.optimalPerturbationTransfer rowTarget colTarget 5 2 3 := by
  funext σ i
  let r : Fin 3 := σ 0
  let c : Fin 2 := σ 1
  have hσ : σ = profile r c := by
    rw [profile_eta σ]
  rw [hσ]
  clear_value r
  clear_value c
  fin_cases i <;> fin_cases r <;> fin_cases c <;>
    norm_num [opTransfer, opTransferTable, rowTarget, colTarget,
      optimalPerturbationTransfer, profile, row0, row1, col0]

theorem op_row0_dominates_row2 :
    (game.subsidize opTransfer).WeaklyStrictlyDominates 0
      row0 row2 := by
  refine ⟨?_, ?_⟩
  · intro σ
    let c : Fin 2 := σ 1
    have hrow0 : Function.update σ 0 row0 = profile row0 c := by
      funext i
      fin_cases i <;> simp [profile, c, row0]
    have hrow2 : Function.update σ 0 row2 = profile row2 c := by
      funext i
      fin_cases i <;> simp [profile, c, row2]
    rw [subsidize_eu, subsidize_eu]
    rw [hrow0, hrow2]
    clear_value c
    fin_cases c <;>
      norm_num [payoff, payoffTable, opTransfer, opTransferTable, profile,
        row0, row2]
  · exact ⟨profile row0 col1, by
      rw [subsidize_eu, subsidize_eu]
      norm_num [payoff, payoffTable, opTransfer, opTransferTable, profile,
        row0, row2, col1]⟩

theorem op_col0_dominates_col1 :
    (game.subsidize opTransfer).WeaklyStrictlyDominates 1
      col0 col1 := by
  refine ⟨?_, ?_⟩
  · intro σ
    let r : Fin 3 := σ 0
    have hcol0 : Function.update σ 1 col0 = profile r col0 := by
      funext i
      fin_cases i <;> simp [profile, r, col0]
    have hcol1 : Function.update σ 1 col1 = profile r col1 := by
      funext i
      fin_cases i <;> simp [profile, r, col1]
    rw [subsidize_eu, subsidize_eu]
    rw [hcol0, hcol1]
    clear_value r
    fin_cases r <;>
      norm_num [payoff, payoffTable, opTransfer, opTransferTable, profile,
        col0, col1]
  · exact ⟨profile row2 col0, by
      rw [subsidize_eu, subsidize_eu]
      norm_num [payoff, payoffTable, opTransfer, opTransferTable, profile,
        row2, col0, col1]⟩

theorem op_rowTarget_undominated_iff
    (r : game.Strategy 0) :
    (game.subsidize opTransfer).IsUndominated 0 r ↔ r ∈ rowTarget := by
  constructor
  · intro hr
    fin_cases r
    · norm_num [rowTarget]
    · norm_num [rowTarget]
    · exact False.elim (hr row0 op_row0_dominates_row2)
  · intro hr t ht
    fin_cases r <;> fin_cases t
    · exact WeaklyStrictlyDominates.irrefl
        (G := game.subsidize opTransfer) (who := 0) row0 ht
    · have hweak := ht.toWeaklyDominates (profile row0 col0)
      norm_num [payoff, payoffTable, opTransfer, opTransferTable, profile,
        row0, row1, col0] at hweak
    · have hweak := ht.toWeaklyDominates (profile row0 col1)
      norm_num [payoff, payoffTable, opTransfer, opTransferTable, profile,
        row0, row2, col1] at hweak
    · have hweak := ht.toWeaklyDominates (profile row0 col1)
      norm_num [payoff, payoffTable, opTransfer, opTransferTable, profile,
        row0, row1, col1] at hweak
    · exact WeaklyStrictlyDominates.irrefl
        (G := game.subsidize opTransfer) (who := 0) row1 ht
    · have hweak := ht.toWeaklyDominates (profile row1 col1)
      norm_num [payoff, payoffTable, opTransfer, opTransferTable, profile,
        row1, row2, col1] at hweak
    · norm_num [rowTarget] at hr
    · norm_num [rowTarget] at hr
    · norm_num [rowTarget] at hr

theorem op_colTarget_undominated_iff
    (c : game.Strategy 1) :
    (game.subsidize opTransfer).IsUndominated 1 c ↔ c ∈ colTarget := by
  constructor
  · intro hc
    fin_cases c
    · norm_num [colTarget]
    · exact False.elim (hc col0 op_col0_dominates_col1)
  · intro hc t ht
    fin_cases c <;> fin_cases t
    · exact WeaklyStrictlyDominates.irrefl
        (G := game.subsidize opTransfer) (who := 1) col0 ht
    · have hweak := ht.toWeaklyDominates (profile row2 col0)
      norm_num [payoff, payoffTable, opTransfer, opTransferTable, profile,
        row2, col0, col1] at hweak
    · norm_num [colTarget] at hc
    · norm_num [colTarget] at hc

theorem opTransfer_isExactKImplementation :
    game.IsExactKImplementation opTransfer target 5 := by
  exact game.transfer_isExactKImplementation_twoPlayerRect_of_checks
    opTransfer_nonneg op_rowTarget_undominated_iff
    op_colTarget_undominated_iff
    (fun σ hσ => by
      rw [opTransfer_eq_optimalPerturbationTransfer,
        game.optimalPerturbationTransfer_sum_on_rect hσ]
      norm_num)

theorem opTransfer_target_cost_eq_five
    (σ : Profile game) (hσ : σ ∈ target) :
    (∑ i : Fin 2, opTransfer σ i) = 5 := by
  rw [opTransfer_eq_optimalPerturbationTransfer,
    game.optimalPerturbationTransfer_sum_on_rect hσ]
  norm_num

theorem optimalPerturbationFamily_e0_ge_two_of_exactImplementation
    {M e₀ e₁ : ℝ}
    (hV : game.IsExactImplementation
      (game.optimalPerturbationTransfer rowTarget colTarget M e₀ e₁) target) :
    2 ≤ e₀ := by
  classical
  let V := game.optimalPerturbationTransfer rowTarget colTarget M e₀ e₁
  have hcol0_undom :
      (game.subsidize V).IsUndominated 1 col0 := by
    have hprof : profile row0 col0 ∈ (game.subsidize V).undominatedProfiles :=
      (hV.mem_undominatedProfiles_iff).mpr
        ⟨by norm_num [rowTarget, row0], by norm_num [colTarget, col0]⟩
    exact hprof 1
  have hrow2_not :
      ¬ (game.subsidize V).IsUndominated 0 row2 := by
    intro hrow2
    have hprof :
        profile row2 col0 ∈ (game.subsidize V).undominatedProfiles := by
      intro i
      fin_cases i
      · exact hrow2
      · exact hcol0_undom
    have htarget : profile row2 col0 ∈ target :=
      (hV.mem_undominatedProfiles_iff).mp hprof
    have hr : row2 ∈ rowTarget := htarget.1
    change (row2 : Fin 3).val = 0 ∨ (row2 : Fin 3).val = 1 at hr
    norm_num [rowTarget, row2] at hr
  have hrow2_dominated :
      ∃ r : game.Strategy 0,
        (game.subsidize V).WeaklyStrictlyDominates 0 r row2 := by
    by_contra hnone
    exact hrow2_not (fun r hr => hnone ⟨r, hr⟩)
  obtain ⟨r, hr⟩ := hrow2_dominated
  fin_cases r
  · have hweak := hr.toWeaklyDominates (profile row2 col0)
    rw [subsidize_eu, subsidize_eu] at hweak
    norm_num [V, payoff, payoffTable, optimalPerturbationTransfer,
      rowTarget, colTarget, profile, Function.update, row0, row2, col0] at hweak
    repeat split_ifs at hweak <;> norm_num at * <;> linarith
  · have hweak := hr.toWeaklyDominates (profile row2 col0)
    rw [subsidize_eu, subsidize_eu] at hweak
    norm_num [V, payoff, payoffTable, optimalPerturbationTransfer,
      rowTarget, colTarget, profile, Function.update, row1, row2, col0] at hweak
    repeat split_ifs at hweak <;> norm_num at * <;> linarith
  · exact False.elim
      (WeaklyStrictlyDominates.irrefl
        (G := game.subsidize V) (who := 0) row2 hr)

theorem optimalPerturbationFamily_e1_ge_three_of_exactImplementation
    {M e₀ e₁ : ℝ}
    (hV : game.IsExactImplementation
      (game.optimalPerturbationTransfer rowTarget colTarget M e₀ e₁) target) :
    3 ≤ e₁ := by
  classical
  let V := game.optimalPerturbationTransfer rowTarget colTarget M e₀ e₁
  have hrow1_undom :
      (game.subsidize V).IsUndominated 0 row1 := by
    have hprof : profile row1 col0 ∈ (game.subsidize V).undominatedProfiles :=
      (hV.mem_undominatedProfiles_iff).mpr
        ⟨by norm_num [rowTarget, row1], by norm_num [colTarget, col0]⟩
    exact hprof 0
  have hcol1_not :
      ¬ (game.subsidize V).IsUndominated 1 col1 := by
    intro hcol1
    have hprof :
        profile row1 col1 ∈ (game.subsidize V).undominatedProfiles := by
      intro i
      fin_cases i
      · exact hrow1_undom
      · exact hcol1
    have htarget : profile row1 col1 ∈ target :=
      (hV.mem_undominatedProfiles_iff).mp hprof
    have hc : col1 ∈ colTarget := htarget.2
    change (col1 : Fin 2).val = 0 at hc
    norm_num [colTarget, col1] at hc
  have hcol1_dominated :
      ∃ c : game.Strategy 1,
        (game.subsidize V).WeaklyStrictlyDominates 1 c col1 := by
    by_contra hnone
    exact hcol1_not (fun c hc => hnone ⟨c, hc⟩)
  obtain ⟨c, hc⟩ := hcol1_dominated
  fin_cases c
  · have hweak := hc.toWeaklyDominates (profile row1 col1)
    rw [subsidize_eu, subsidize_eu] at hweak
    norm_num [V, payoff, payoffTable, optimalPerturbationTransfer,
      rowTarget, colTarget, profile, Function.update, row1, col0, col1] at hweak
    exact hweak
  · exact False.elim
      (WeaklyStrictlyDominates.irrefl
        (G := game.subsidize V) (who := 1) col1 hc)

theorem optimalPerturbationFamily_cost_ge_five_of_exactImplementation
    {M e₀ e₁ : ℝ}
    (hV : game.IsExactImplementation
      (game.optimalPerturbationTransfer rowTarget colTarget M e₀ e₁) target) :
    5 ≤ e₀ + e₁ := by
  have he₀ :=
    optimalPerturbationFamily_e0_ge_two_of_exactImplementation
      (M := M) (e₀ := e₀) (e₁ := e₁) hV
  have he₁ :=
    optimalPerturbationFamily_e1_ge_three_of_exactImplementation
      (M := M) (e₀ := e₀) (e₁ := e₁) hV
  linarith

theorem optimalPerturbationFamily_minimum_cost_eq_five :
    (∃ M e₀ e₁ : ℝ,
      game.IsExactKImplementation
        (game.optimalPerturbationTransfer rowTarget colTarget M e₀ e₁)
        target (e₀ + e₁) ∧ e₀ + e₁ = 5) ∧
      ∀ M e₀ e₁ : ℝ,
        game.IsExactImplementation
          (game.optimalPerturbationTransfer rowTarget colTarget M e₀ e₁) target →
          5 ≤ e₀ + e₁ := by
  refine ⟨?_, ?_⟩
  · refine ⟨5, 2, 3, ?_, by norm_num⟩
    norm_num
    rw [← opTransfer_eq_optimalPerturbationTransfer]
    exact opTransfer_isExactKImplementation
  · intro M e₀ e₁ hV
    exact optimalPerturbationFamily_cost_ge_five_of_exactImplementation hV

theorem three_le_of_isExactKImplementation
    {V : Profile game → Payoff (Fin 2)} {k : ℝ}
    (hV : game.IsExactKImplementation V target k) :
    3 ≤ k := by
  classical
  have hexact := hV.exactImplementation
  have hrow1_undom :
      (game.subsidize V).IsUndominated 0 row1 := by
    have hprof :
        profile row1 col0 ∈ (game.subsidize V).undominatedProfiles := by
      exact (hexact.mem_undominatedProfiles_iff).mpr
        ⟨by norm_num [rowTarget, row1], by norm_num [colTarget, col0]⟩
    exact hprof 0
  have hcol1_not :
      ¬ (game.subsidize V).IsUndominated 1 col1 := by
    intro hcol1
    have hprof :
        profile row1 col1 ∈ (game.subsidize V).undominatedProfiles := by
      intro i
      fin_cases i
      · exact hrow1_undom
      · exact hcol1
    have htarget : profile row1 col1 ∈ target :=
      (hexact.mem_undominatedProfiles_iff).mp hprof
    have hc : col1 ∈ colTarget := htarget.2
    change (col1 : Fin 2).val = 0 at hc
    norm_num [colTarget, col1] at hc
  have hcol1_dominated :
      ∃ c : game.Strategy 1,
        (game.subsidize V).WeaklyStrictlyDominates 1 c col1 := by
    by_contra hnone
    exact hcol1_not (fun c hc => hnone ⟨c, hc⟩)
  obtain ⟨c, hc⟩ := hcol1_dominated
  have hcol0_dom :
      (game.subsidize V).WeaklyStrictlyDominates 1 col0 col1 := by
    fin_cases c
    · exact hc
    · exact False.elim
        (WeaklyStrictlyDominates.irrefl
          (G := game.subsidize V) (who := 1) col1 hc)
  have htransfer_one : 3 ≤ V (profile row1 col0) 1 := by
    change 3 ≤ V (profile (1 : Fin 3) (0 : Fin 2)) 1
    let σ : Profile (game.subsidize V) := profile (1 : Fin 3) (0 : Fin 2)
    have hweak := hcol0_dom.toWeaklyDominates σ
    rw [subsidize_eu, subsidize_eu] at hweak
    have hleft :
        Function.update σ 1 (col0 : (game.subsidize V).Strategy 1) = σ := by
      funext i
      fin_cases i <;> simp [σ, profile, col0]
    have hright :
        Function.update σ 1 (col1 : (game.subsidize V).Strategy 1) =
          (profile (1 : Fin 3) (1 : Fin 2) : Profile (game.subsidize V)) := by
      funext i
      fin_cases i <;> simp [σ, profile, col1]
    rw [hleft, hright] at hweak
    have hweak' :
        game.eu (profile (1 : Fin 3) (0 : Fin 2)) 1 +
            V (profile (1 : Fin 3) (0 : Fin 2)) 1 ≥
          game.eu (profile (1 : Fin 3) (1 : Fin 2)) 1 +
            V (profile (1 : Fin 3) (1 : Fin 2)) 1 := by
      simpa [σ] using hweak
    norm_num [payoff, payoffTable, profile] at hweak'
    have hnonneg := hV.nonneg (profile (1 : Fin 3) (1 : Fin 2)) 1
    linarith
  have hsum_ge : 3 ≤ ∑ i : Fin 2, V (profile row1 col0) i := by
    rw [Fin.sum_univ_two]
    have hnonneg := hV.nonneg (profile row1 col0) 0
    linarith
  exact hsum_ge.trans
    (hV.cost_bound (profile row1 col0)
      ⟨by norm_num [rowTarget, row1], by norm_num [colTarget, col0]⟩)

theorem exactImplPrice_ge_three :
    3 ≤ game.exactImplPrice target := by
  rw [exactImplPrice]
  exact le_csInf
    ⟨3, cheapTransfer, cheapTransfer_isExactKImplementation⟩
    (fun k hk => by
      obtain ⟨V, hV⟩ := hk
      exact three_le_of_isExactKImplementation hV)

theorem exactImplementationCosts_eq_Ici_three :
    game.exactImplementationCosts target = Set.Ici (3 : ℝ) := by
  ext k
  constructor
  · rintro ⟨V, hV⟩
    exact three_le_of_isExactKImplementation hV
  · intro hk
    exact ⟨cheapTransfer, cheapTransfer_isExactKImplementation.mono_cost hk⟩

theorem exactImplPrice_eq_three :
    game.exactImplPrice target = 3 := by
  rw [exactImplPrice, exactImplementationCosts_eq_Ici_three]
  exact csInf_Ici

/-- The paper's OP-shaped output has target cost `5`, while the same target is
exactly implementable at cost `3`. -/
theorem op_algorithm_output_not_optimal_certificate :
    game.exactImplPrice target = 3 ∧
      (∃ σ : Profile game,
        σ ∈ target ∧
          (∑ i : Fin 2, opTransfer σ i) = 5 ∧
            game.exactImplPrice target < (∑ i : Fin 2, opTransfer σ i)) :=
  ⟨exactImplPrice_eq_three,
    ⟨profile row0 col0,
      ⟨by norm_num [rowTarget, row0], by norm_num [colTarget, col0]⟩,
      opTransfer_target_cost_eq_five (profile row0 col0)
        ⟨by norm_num [rowTarget, row0], by norm_num [colTarget, col0]⟩,
      by
        rw [exactImplPrice_eq_three,
          opTransfer_target_cost_eq_five (profile row0 col0)
            ⟨by norm_num [rowTarget, row0], by norm_num [colTarget, col0]⟩]
        norm_num⟩⟩

end OptimalPerturbationCounterexample

end KernelGame

end GameTheory
