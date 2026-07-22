/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Dominance.DominanceRelations
import Math.Fintype
import Mathlib.Data.Rat.Lemmas

/-!
# Undominated strategies

Undominated-strategy rationality for the weak-with-strict-witness dominance
relation `KernelGame.WeaklyDominatesWithStrictWitness` (also exposed under the
compatibility name `WeaklyStrictlyDominates`). This is not the same as
`KernelGame.WeaklyDominatesReflexive`, the reflexive `≥`-everywhere preorder.

This file provides undominated strategies/profiles for that relation, and the
finite ascent lemma used to move from an arbitrary dominated strategy to an
undominated strategy that dominates it.
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι] {G : KernelGame ι}

/-- A strategy is undominated when no other strategy dominates it. -/
def IsUndominated (G : KernelGame ι) (who : ι) (s : G.Strategy who) : Prop :=
  ∀ t : G.Strategy who, ¬ G.WeaklyStrictlyDominates who t s

/-- Profiles whose every coordinate is undominated. -/
def undominatedProfiles (G : KernelGame ι) : Set (Profile G) :=
  {σ | ∀ i, G.IsUndominated i (σ i)}

/-- Two strategies of a player are utility-equivalent when the player receives
the same expected utility from them at every opponent profile. -/
def UtilityEquivalent (G : KernelGame ι) (who : ι)
    (s t : G.Strategy who) : Prop :=
  ∀ σ : Profile G,
    G.eu (Function.update σ who s) who =
      G.eu (Function.update σ who t) who

theorem UtilityEquivalent.refl {who : ι} (s : G.Strategy who) :
    G.UtilityEquivalent who s s := by
  intro σ
  rfl

theorem UtilityEquivalent.symm {who : ι} {s t : G.Strategy who}
    (h : G.UtilityEquivalent who s t) :
    G.UtilityEquivalent who t s := by
  intro σ
  exact (h σ).symm

theorem UtilityEquivalent.trans {who : ι} {s t u : G.Strategy who}
    (hst : G.UtilityEquivalent who s t) (htu : G.UtilityEquivalent who t u) :
    G.UtilityEquivalent who s u := by
  intro σ
  exact (hst σ).trans (htu σ)

/-- Replacing the dominated strategy by a utility-equivalent one preserves
weak dominance with a strict witness. -/
theorem WeaklyStrictlyDominates.congr_dominated_utilityEquivalent
    {who : ι} {u s t : G.Strategy who}
    (hst : G.UtilityEquivalent who s t) :
    G.WeaklyStrictlyDominates who u s ↔
      G.WeaklyStrictlyDominates who u t := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro σ
      have hweak := h.1 σ
      have heq := hst σ
      linarith
    · obtain ⟨σ, hstrict⟩ := h.strict_witness
      have heq := hst σ
      exact ⟨σ, by linarith⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro σ
      have hweak := h.1 σ
      have heq := hst σ
      linarith
    · obtain ⟨σ, hstrict⟩ := h.strict_witness
      have heq := hst σ
      exact ⟨σ, by linarith⟩

/-- Undominatedness is saturated by utility equivalence. -/
theorem UtilityEquivalent.isUndominated_iff
    {who : ι} {s t : G.Strategy who}
    (hst : G.UtilityEquivalent who s t) :
    G.IsUndominated who s ↔ G.IsUndominated who t := by
  constructor
  · intro hs u hut
    exact hs u ((WeaklyStrictlyDominates.congr_dominated_utilityEquivalent
      (G := G) (who := who) (u := u) hst).mpr hut)
  · intro ht u hus
    exact ht u ((WeaklyStrictlyDominates.congr_dominated_utilityEquivalent
      (G := G) (who := who) (u := u) hst).mp hus)

theorem IsUndominated.not_dominated {who : ι} {s t : G.Strategy who}
    (h : G.IsUndominated who s) : ¬ G.WeaklyStrictlyDominates who t s :=
  h t

/-- A weakly dominant strategy is undominated under weak dominance with a
strict witness. -/
theorem IsDominant.isUndominated {who : ι} {s : G.Strategy who}
    (hdom : G.IsDominant who s) : G.IsUndominated who s := by
  intro t hts
  obtain ⟨_, σ, hstrict⟩ := hts
  have hle := hdom σ t
  linarith

/-- If `b` weakly dominates every strategy of player `who`, then the
undominated strategies are exactly those utility-equivalent to `b`. -/
theorem isUndominated_iff_utilityEquivalent_of_forall_weaklyDominates
    {who : ι} {b s : G.Strategy who}
    (hdom : ∀ t : G.Strategy who, G.WeaklyDominates who b t) :
    G.IsUndominated who s ↔ G.UtilityEquivalent who s b := by
  classical
  constructor
  · intro hs
    by_contra hne
    have hnot : ¬ ∀ σ : Profile G,
        G.eu (Function.update σ who s) who =
          G.eu (Function.update σ who b) who := hne
    push Not at hnot
    obtain ⟨σ, hneq⟩ := hnot
    have hle := hdom s σ
    have hstrict :
        G.eu (Function.update σ who b) who >
          G.eu (Function.update σ who s) who := by
      exact lt_of_le_of_ne hle hneq
    exact hs b ⟨hdom s, σ, hstrict⟩
  · intro heq t hts
    obtain ⟨_, σ, hstrict⟩ := hts
    have hbt := hdom t σ
    have hsb := heq σ
    linarith

/-- Set form of `isUndominated_iff_utilityEquivalent_of_forall_weaklyDominates`. -/
theorem undominated_set_eq_utilityEquivalent_of_forall_weaklyDominates
    {who : ι} {b : G.Strategy who}
    (hdom : ∀ t : G.Strategy who, G.WeaklyDominates who b t) :
    {s : G.Strategy who | G.IsUndominated who s} =
      {s : G.Strategy who | G.UtilityEquivalent who s b} := by
  ext s
  exact isUndominated_iff_utilityEquivalent_of_forall_weaklyDominates
    (G := G) (who := who) (b := b) (s := s) hdom

/-- Product-profile form: if each coordinate of `b` weakly dominates every
strategy of that player, then the undominated profiles are exactly the product
of the utility-equivalence classes of the coordinates of `b`. -/
theorem undominatedProfiles_eq_utilityEquivalentClass_of_forall_weaklyDominates
    {b : Profile G}
    (hdom : ∀ i (t : G.Strategy i), G.WeaklyDominates i (b i) t) :
    G.undominatedProfiles =
      {σ : Profile G | ∀ i, G.UtilityEquivalent i (σ i) (b i)} := by
  ext σ
  constructor
  · intro hσ i
    exact
      (isUndominated_iff_utilityEquivalent_of_forall_weaklyDominates
        (G := G) (who := i) (b := b i) (s := σ i) (hdom i)).mp (hσ i)
  · intro hσ i
    exact
      (isUndominated_iff_utilityEquivalent_of_forall_weaklyDominates
        (G := G) (who := i) (b := b i) (s := σ i) (hdom i)).mpr (hσ i)

/-- Under weak dominance of every coordinate of `b`, the undominated profile
set is the singleton `{b}` exactly when each coordinate's utility-equivalence
class is trivial. -/
theorem undominatedProfiles_eq_singleton_iff_utilityEquivalent_eq
    {b : Profile G}
    (hdom : ∀ i (t : G.Strategy i), G.WeaklyDominates i (b i) t) :
    G.undominatedProfiles = ({b} : Set (Profile G)) ↔
      ∀ i (s : G.Strategy i), G.UtilityEquivalent i s (b i) → s = b i := by
  classical
  constructor
  · intro hsingle i s hs
    have hmem :
        Function.update b i s ∈ G.undominatedProfiles := by
      rw [undominatedProfiles_eq_utilityEquivalentClass_of_forall_weaklyDominates
        (G := G) (b := b) hdom]
      intro j
      by_cases hji : j = i
      · subst hji
        simpa using hs
      · simpa [Function.update_of_ne hji] using
          (UtilityEquivalent.refl (G := G) (who := j) (b j))
    have heq : Function.update b i s = b := Set.mem_singleton_iff.mp (by
      simpa [hsingle] using hmem)
    simpa using congrFun heq i
  · intro htriv
    rw [undominatedProfiles_eq_utilityEquivalentClass_of_forall_weaklyDominates
      (G := G) (b := b) hdom]
    ext σ
    constructor
    · intro hσ
      exact Set.mem_singleton_iff.mpr (by
        funext i
        exact htriv i (σ i) (hσ i))
    · intro hσ
      have hσeq : σ = b := Set.mem_singleton_iff.mp hσ
      subst σ
      intro i
      exact UtilityEquivalent.refl (G := G) (who := i) (b i)

@[simp] theorem mem_undominatedProfiles {σ : Profile G} :
    σ ∈ G.undominatedProfiles ↔ ∀ i, G.IsUndominated i (σ i) := Iff.rfl

/-- The undominated-profile set is saturated by coordinatewise utility
equivalence. This is the generic observation-quotient principle behind the
device and VCG nonredundancy obstructions. -/
theorem undominatedProfiles_utilityEquivalent_iff
    {σ τ : Profile G}
    (h : ∀ i, G.UtilityEquivalent i (σ i) (τ i)) :
    σ ∈ G.undominatedProfiles ↔ τ ∈ G.undominatedProfiles := by
  constructor
  · intro hσ i
    exact ((h i).isUndominated_iff (G := G)).mp (hσ i)
  · intro hτ i
    exact ((h i).isUndominated_iff (G := G)).mpr (hτ i)

/-- On a finite strategy set, every strategy is either itself undominated or is
dominated by an undominated strategy. -/
theorem exists_undominated_or_dominator {who : ι} [Finite (G.Strategy who)]
    (s : G.Strategy who) :
    ∃ t : G.Strategy who,
      G.IsUndominated who t ∧ (t = s ∨ G.WeaklyStrictlyDominates who t s) := by
  obtain ⟨t, htmax, htcand⟩ :=
    Math.exists_maximal_or_rel_of_finite_trans_irrefl
      (G.WeaklyStrictlyDominates who)
      (fun a b c hab hbc => WeaklyStrictlyDominates.trans hab hbc)
      (fun a => WeaklyStrictlyDominates.irrefl (G := G) (who := who) a)
      s
  exact ⟨t, htmax, htcand⟩

/-- On a finite strategy set, any dominated strategy is dominated by an
undominated strategy. -/
theorem exists_undominated_dominator {who : ι} [Finite (G.Strategy who)]
    {s : G.Strategy who}
    (hdominated : ∃ t : G.Strategy who, G.WeaklyStrictlyDominates who t s) :
    ∃ t : G.Strategy who,
      G.IsUndominated who t ∧ G.WeaklyStrictlyDominates who t s := by
  obtain ⟨t, htmax, hts⟩ :=
    Math.exists_maximal_rel_of_finite_trans_irrefl
      (G.WeaklyStrictlyDominates who)
      (fun a b c hab hbc => WeaklyStrictlyDominates.trans hab hbc)
      (fun a => WeaklyStrictlyDominates.irrefl (G := G) (who := who) a)
      hdominated
  exact ⟨t, htmax, hts⟩

/-- Every finite nonempty strategy set has at least one undominated strategy. -/
theorem exists_undominated_strategy (who : ι)
    [Nonempty (G.Strategy who)] [Finite (G.Strategy who)] :
    ∃ s : G.Strategy who, G.IsUndominated who s := by
  obtain ⟨s⟩ := ‹Nonempty (G.Strategy who)›
  obtain ⟨t, htundom, _⟩ := exists_undominated_or_dominator (G := G) (who := who) s
  exact ⟨t, htundom⟩

/-- Finite games with nonempty strategy sets have at least one undominated
profile. -/
theorem undominatedProfiles_nonempty
    [∀ i, Nonempty (G.Strategy i)] [∀ i, Finite (G.Strategy i)] :
    G.undominatedProfiles.Nonempty := by
  classical
  choose s hs using fun i => exists_undominated_strategy (G := G) i
  exact ⟨s, hs⟩

end KernelGame

/- A countable strict-order core of the paper's Section 3.2 infinite example.
The isolated point `none` is the only undominated element, while the chain
`some 0 < some 1 < some 2 < ...` has no undominated dominator. -/
namespace InfiniteAscentCounterexample

/-- Strategies for the infinite-ascent counterexample: an isolated target point
and an infinite ascending chain. -/
abbrev Strategy := Option ℕ

/-- The isolated target point. -/
abbrev target : Strategy := none

/-- `some m` dominates `some n` exactly when it is higher in the infinite chain;
the target is isolated. -/
def Dominates : Strategy → Strategy → Prop
  | some m, some n => n < m
  | _, _ => False

/-- Maximality for the counterexample relation. -/
def IsMaximal (s : Strategy) : Prop :=
  ∀ t : Strategy, ¬ Dominates t s

theorem dominates_trans {a b c : Strategy}
    (hab : Dominates a b) (hbc : Dominates b c) :
    Dominates a c := by
  cases a with
  | none =>
      simp [Dominates] at hab
  | some m =>
      cases b with
      | none =>
          simp [Dominates] at hab
      | some n =>
          cases c with
          | none =>
              simp [Dominates] at hbc
          | some k =>
              have hkn : k < n := by
                simpa [Dominates] using hbc
              have hnm : n < m := by
                simpa [Dominates] using hab
              simpa [Dominates] using Nat.lt_trans hkn hnm

theorem dominates_irrefl (s : Strategy) :
    ¬ Dominates s s := by
  cases s <;> simp [Dominates]

theorem isMaximal_iff_eq_target {s : Strategy} :
    IsMaximal s ↔ s = target := by
  constructor
  · intro h
    cases s with
    | none => rfl
    | some n =>
        exfalso
        exact h (some (n + 1)) (by simp [Dominates])
  · intro hs
    subst hs
    intro t
    cases t <;> simp [Dominates]

theorem zero_dominated :
    ∃ t : Strategy, Dominates t (some 0) := by
  exact ⟨some 1, by simp [Dominates]⟩

/-- The finite-ascent conclusion fails without finiteness: `some 0` is
dominated, but none of its dominators is maximal. -/
theorem zero_dominated_without_maximal_dominator :
    ¬ ∃ t : Strategy, IsMaximal t ∧ Dominates t (some 0) := by
  rintro ⟨t, htmax, htdom⟩
  have ht : t = target := isMaximal_iff_eq_target.mp htmax
  subst t
  simp [Dominates] at htdom

/-- A packaged witness that the dominated-to-undominated-dominator ascent lemma
requires a finiteness hypothesis. -/
theorem finite_ascent_conclusion_fails :
    (∃ t : Strategy, Dominates t (some 0)) ∧
      ¬ ∃ t : Strategy, IsMaximal t ∧ Dominates t (some 0) :=
  ⟨zero_dominated, zero_dominated_without_maximal_dominator⟩

end InfiniteAscentCounterexample

/- The paper's Section 3.2 infinite game, instantiated as a concrete
`KernelGame`. Player 1 chooses either `z1` or a rational point in `(0,1)`;
player 2 chooses either `z2` or `x2`. Player 1's payoffs are
`U1(z1,z2)=0.5`, `U1(z1,x2)=10`, and `U1(x1,*)=x1`; player 2's payoff is
arbitrary in the paper, so this formal example fixes it to zero. -/
namespace InfiniteAscentPaperGame

/-- Rational strategies in the open unit interval. -/
abbrev OpenUnitRat := {q : ℚ // 0 < q ∧ q < 1}

/-- Player 1's strategies: the distinguished strategy `none = z1`, or a rational
point in `(0,1)`. -/
abbrev PlayerOneStrategy := Option OpenUnitRat

/-- Player 2's two strategies: `false = z2`, `true = x2`. -/
abbrev PlayerTwoStrategy := Bool

/-- Strategy spaces for the concrete two-player infinite game. -/
def Strategy : Fin 2 → Type
  | 0 => PlayerOneStrategy
  | 1 => PlayerTwoStrategy

/-- Player 1's distinguished strategy from the paper. -/
abbrev z1 : PlayerOneStrategy := none

/-- Player 2's distinguished strategy from the paper. -/
abbrev z2 : PlayerTwoStrategy := false

/-- Player 2's other strategy from the paper. -/
abbrev x2 : PlayerTwoStrategy := true

/-- A profile in the paper's infinite example. -/
def profile (s1 : PlayerOneStrategy) (s2 : PlayerTwoStrategy) :
    (i : Fin 2) → Strategy i
  | 0 => s1
  | 1 => s2

@[simp] theorem profile_zero (s1 : PlayerOneStrategy) (s2 : PlayerTwoStrategy) :
    profile s1 s2 0 = s1 := rfl

@[simp] theorem profile_one (s1 : PlayerOneStrategy) (s2 : PlayerTwoStrategy) :
    profile s1 s2 1 = s2 := rfl

/-- Payoffs for the paper's Section 3.2 example. Player 2's payoff is fixed to
zero because the paper leaves it arbitrary. -/
noncomputable def payoff (σ : (i : Fin 2) → Strategy i) : Payoff (Fin 2) :=
  fun
    | 0 =>
        match σ 0, σ 1 with
        | none, false => (1 / 2 : ℝ)
        | none, true => 10
        | some q, _ => (q.1 : ℚ)
    | 1 => 0

/-- The concrete infinite game from the paper's Section 3.2 example. -/
noncomputable abbrev game : KernelGame (Fin 2) :=
  KernelGame.ofPureEU Strategy payoff

@[simp] theorem game_eu (σ : KernelGame.Profile game) (i : Fin 2) :
    game.eu σ i = payoff σ i := by
  simp [game]

/-- Moving from a rational point to a strictly larger rational point in `(0,1)`.
-/
def midpointToOne (q : OpenUnitRat) : OpenUnitRat :=
  ⟨(q.1 + 1) / 2, by
    constructor <;> linarith [q.2.1, q.2.2]⟩

theorem lt_midpointToOne (q : OpenUnitRat) :
    q.1 < (midpointToOne q).1 := by
  dsimp [midpointToOne]
  linarith [q.2.2]

/-- In the paper's game, every rational point in `(0,1)` is dominated by any
strictly larger rational point in `(0,1)`. -/
theorem some_weaklyStrictlyDominates_of_lt {q r : OpenUnitRat} (hqr : q.1 < r.1) :
    game.WeaklyStrictlyDominates 0 (some r) (some q) := by
  have hqr_real : ((q.1 : ℚ) : ℝ) < (r.1 : ℝ) := by
    exact_mod_cast hqr
  refine ⟨?_, ?_⟩
  · intro σ
    simpa [game, payoff] using le_of_lt hqr_real
  · exact ⟨profile z1 z2, by
      simpa [game, payoff, profile, z1, z2] using hqr_real⟩

theorem some_is_dominated (q : OpenUnitRat) :
    ∃ t : game.Strategy 0, game.WeaklyStrictlyDominates 0 t (some q) :=
  ⟨some (midpointToOne q),
    some_weaklyStrictlyDominates_of_lt (lt_midpointToOne q)⟩

/-- The paper's `z1` is not dominated. -/
theorem target_isUndominated :
    game.IsUndominated 0 z1 := by
  intro t ht
  cases t with
  | none =>
      exact KernelGame.WeaklyStrictlyDominates.irrefl (G := game) (who := 0) z1 ht
  | some q =>
      have hweak := ht.1 (profile z1 x2)
      have hq_ge_ten : (10 : ℝ) ≤ (q.1 : ℝ) := by
        simpa [game, payoff, profile, z1, x2] using hweak
      have hq_lt_one : (q.1 : ℝ) < 1 := by
        exact_mod_cast q.2.2
      linarith

/-- Player 1's undominated strategies in the paper's game are exactly `{z1}`. -/
theorem isUndominated_iff_eq_target (s : game.Strategy 0) :
    game.IsUndominated 0 s ↔ s = z1 := by
  constructor
  · intro h
    cases s with
    | none => rfl
    | some q =>
        exfalso
        obtain ⟨t, ht⟩ := some_is_dominated q
        exact h t ht
  · intro hs
    subst hs
    exact target_isUndominated

theorem playerOne_undominated_set_eq_singleton :
    {s : game.Strategy 0 | game.IsUndominated 0 s} = {z1} := by
  ext s
  exact isUndominated_iff_eq_target s

/-- The concrete rational `3/4`, used for the paper's observation that `z1`
does not dominate points above `0.5`. -/
def threeFour : OpenUnitRat :=
  ⟨(3 / 4 : ℚ), by norm_num⟩

/-- The concrete rational `7/8`, a dominator of `3/4`. -/
def sevenEighths : OpenUnitRat :=
  ⟨(7 / 8 : ℚ), by norm_num⟩

theorem threeFour_dominated :
    ∃ t : game.Strategy 0,
      game.WeaklyStrictlyDominates 0 t (some threeFour) :=
  ⟨some sevenEighths,
    some_weaklyStrictlyDominates_of_lt (by norm_num [threeFour, sevenEighths])⟩

/-- The paper's `z1` does not dominate `3/4 > 0.5`. -/
theorem target_not_weaklyDominates_threeFour :
    ¬ game.WeaklyDominates 0 z1 (some threeFour) := by
  intro h
  have hbad : (1 / 2 : ℝ) ≥ (3 / 4 : ℝ) := by
    simpa [game, payoff, profile, z1, z2, threeFour] using h (profile z1 z2)
  norm_num at hbad

theorem target_not_dominant :
    ¬ game.IsDominant 0 z1 := by
  intro hdom
  exact target_not_weaklyDominates_threeFour
    (fun σ => hdom σ (some threeFour))

/-- The dominated-to-undominated-dominator conclusion fails in the paper's
concrete infinite game: `3/4` is dominated, but no undominated strategy dominates
it. -/
theorem threeFour_no_undominated_dominator :
    ¬ ∃ t : game.Strategy 0,
      game.IsUndominated 0 t ∧
        game.WeaklyStrictlyDominates 0 t (some threeFour) := by
  rintro ⟨t, htundom, htdom⟩
  have ht : t = z1 := (isUndominated_iff_eq_target t).mp htundom
  subst t
  exact target_not_weaklyDominates_threeFour htdom.1

/-- The paper's Section 3.2 game witnesses that the finite-ascent lemma used in
the singleton proof cannot be generalized to arbitrary infinite games. -/
theorem finite_ascent_conclusion_fails :
    (∃ t : game.Strategy 0,
      game.WeaklyStrictlyDominates 0 t (some threeFour)) ∧
      ¬ ∃ t : game.Strategy 0,
        game.IsUndominated 0 t ∧
          game.WeaklyStrictlyDominates 0 t (some threeFour) :=
  ⟨threeFour_dominated, threeFour_no_undominated_dominator⟩

end InfiniteAscentPaperGame

end GameTheory
