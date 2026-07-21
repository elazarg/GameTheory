/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import GameTheory.Concepts.Equilibrium.SolutionConcepts

/-!
# Security Strategies and Maximin Values

A player's security level (maximin value) is the best EU they can
guarantee regardless of opponents' play. A security (maximin) strategy
achieves this guarantee.

## Main definitions

* `worstCaseEUInf` — infimum EU over opponent profiles for a fixed strategy
* `securityLevelSup` — supremum over own strategies of `worstCaseEUInf`
* `IsSecurityStrategySup` / `IsSecurityProfileSup` — attained
  order-theoretic security strategies and profiles
* `mixedWorstCaseEUInf` / `mixedSecurityLevel` — the same with a *mixed* own
  strategy (the mixed maximin value)
* `worstCaseEU` — minimum EU over opponent profiles for a fixed strategy
* `securityLevel` — the max over own strategies of `worstCaseEU`
* `IsSecurityStrategy` / `IsSecurityProfile` — finite-game maximin strategies
  and profiles

## Main results

* `nash_eu_ge_securityLevel` — Nash equilibrium EU ≥ security level
* `IsDominant.eu_ge_securityLevel` — a dominant strategy guarantees ≥ security level
* `securityLevelSup_le_mixedSecurityLevel` — randomizing only raises the
  guaranteed payoff (pure security level ≤ mixed security level)
* `nash_eu_ge_mixedSecurityLevel` — Nash EU ≥ mixed security level
* `exists_securityProfile` — finite games admit a profile of security strategies
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- Player `who` playing strategy `s` guarantees expected payoff at least `v`
against every profile of the other players. -/
def Guarantees [DecidableEq ι]
    (G : KernelGame ι) (who : ι) (s : G.Strategy who) (v : ℝ) : Prop :=
  ∀ σ : Profile G, G.eu (Function.update σ who s) who ≥ v

/-- Lowering the threshold preserves an expected-utility guarantee. -/
theorem Guarantees.mono [DecidableEq ι]
    {G : KernelGame ι} {who : ι} {s : G.Strategy who}
    {v v' : ℝ} (hv : v' ≤ v) (hg : G.Guarantees who s v) :
    G.Guarantees who s v' :=
  fun σ => le_trans hv (hg σ)

section Order

variable (G : KernelGame ι)

open Classical in
/-- Worst-case EU as an order-theoretic infimum over opponent profiles.

Unlike `worstCaseEU`, this definition does not enumerate the profile space.
Useful bounds require the displayed payoff range to be bounded below. -/
noncomputable def worstCaseEUInf (who : ι) (s : G.Strategy who) : ℝ :=
  ⨅ σ : Profile G, G.eu (Function.update σ who s) who

open Classical in
/-- Security level as an order-theoretic supremum over own strategies.

Unlike `securityLevel`, this definition does not enumerate the strategy space.
Upper-bound lemmas require the strategy range to be nonempty. Lower-bound
lemmas additionally require the displayed range to be bounded above. -/
noncomputable def securityLevelSup (who : ι) : ℝ :=
  ⨆ s : G.Strategy who, G.worstCaseEUInf who s

/-- An order-theoretic security strategy attains the supremal security level.
Such a strategy need not exist without an attainment hypothesis. -/
def IsSecurityStrategySup (who : ι) (s : G.Strategy who) : Prop :=
  G.worstCaseEUInf who s = G.securityLevelSup who

/-- A profile consists entirely of order-theoretic security strategies. -/
def IsSecurityProfileSup (σ : Profile G) : Prop :=
  ∀ i, G.IsSecurityStrategySup i (σ i)

open Classical in
/-- The infimum worst-case EU is below every profile payoff when the payoff
    range is bounded below. -/
theorem worstCaseEUInf_le (who : ι) (s : G.Strategy who)
    (hbdd : BddBelow (Set.range (fun σ : Profile G =>
      G.eu (Function.update σ who s) who)))
    (σ : Profile G) :
    G.worstCaseEUInf who s ≤ G.eu (Function.update σ who s) who := by
  exact ciInf_le hbdd σ

open Classical in
/-- The infimum worst case is a guaranteed payoff against every profile, under
    the same bounded-below hypothesis needed to use `iInf` as a lower bound. -/
theorem worstCaseEUInf_guarantees (who : ι) (s : G.Strategy who)
    (hbdd : BddBelow (Set.range (fun σ : Profile G =>
      G.eu (Function.update σ who s) who))) :
    ∀ σ : Profile G, G.eu (Function.update σ who s) who ≥
      G.worstCaseEUInf who s :=
  fun σ => G.worstCaseEUInf_le who s hbdd σ

open Classical in
/-- An attained order-theoretic security strategy guarantees the security
level against every opponent profile. -/
theorem IsSecurityStrategySup.guarantees {who : ι} {s : G.Strategy who}
    (h : G.IsSecurityStrategySup who s)
    (hbdd : BddBelow (Set.range (fun σ : Profile G =>
      G.eu (Function.update σ who s) who))) :
    G.Guarantees who s (G.securityLevelSup who) := by
  intro σ
  rw [← h]
  exact G.worstCaseEUInf_le who s hbdd σ

open Classical in
/-- In a Nash equilibrium, each player's EU is at least their order-theoretic
    security level, assuming each pure-deviation worst-case range is bounded
    below. -/
theorem nash_eu_ge_securityLevelSup {σ : Profile G} (hN : G.IsNash σ)
    (who : ι) [Nonempty (G.Strategy who)]
    (hbddWorst : ∀ s : G.Strategy who,
      BddBelow (Set.range (fun τ : Profile G =>
        G.eu (Function.update τ who s) who))) :
    G.eu σ who ≥ G.securityLevelSup who := by
  simp only [securityLevelSup]
  apply ciSup_le
  intro s
  calc G.worstCaseEUInf who s
      ≤ G.eu (Function.update σ who s) who := G.worstCaseEUInf_le who s (hbddWorst s) σ
    _ ≤ G.eu σ who := by have := hN who s; linarith

open Classical in
/-- A dominant strategy guarantees at least the order-theoretic security level
    against any profile, under bounded-below worst-case ranges. -/
theorem IsDominant.eu_ge_securityLevelSup
    {who : ι} [Nonempty (G.Strategy who)]
    {s : G.Strategy who} (hdom : G.IsDominant who s)
    (σ : Profile G)
    (hbddWorst : ∀ t : G.Strategy who,
      BddBelow (Set.range (fun τ : Profile G =>
        G.eu (Function.update τ who t) who))) :
    G.eu (Function.update σ who s) who ≥ G.securityLevelSup who := by
  simp only [securityLevelSup]
  apply ciSup_le
  intro t
  calc G.worstCaseEUInf who t
      ≤ G.eu (Function.update σ who t) who := G.worstCaseEUInf_le who t (hbddWorst t) σ
    _ ≤ G.eu (Function.update σ who s) who := by
        have := hdom σ t; linarith

open Classical in
/-- The order-theoretic security level is the best guaranteed payoff, provided
    the chosen strategy's profile range is nonempty/bounded below and the
    strategy-level worst-case range is bounded above. -/
theorem le_securityLevelSup_of_forall_eu_ge (who : ι) [Nonempty (Profile G)]
    (s : G.Strategy who) (v : ℝ)
    (hg : ∀ σ : Profile G, G.eu (Function.update σ who s) who ≥ v)
    (hbddSec : BddAbove (Set.range (fun t : G.Strategy who =>
      G.worstCaseEUInf who t))) :
    v ≤ G.securityLevelSup who := by
  calc v ≤ G.worstCaseEUInf who s := by
          exact le_ciInf hg
     _ ≤ G.securityLevelSup who :=
          le_ciSup hbddSec s

open Classical in
/-- Worst-case EU of a *mixed* own strategy `p`: the infimum, over opponent
    profiles, of the expected payoff when `who` randomizes according to `p`.
    Opponents stay pure; by linearity the worst mixed opponent is no worse. -/
noncomputable def mixedWorstCaseEUInf (who : ι) (p : PMF (G.Strategy who)) : ℝ :=
  ⨅ σ : Profile G, expect p (fun a => G.eu (Function.update σ who a) who)

open Classical in
/-- The **mixed security level** (mixed maximin value): the best worst-case
    expected payoff `who` can guarantee by randomizing their own strategy. -/
noncomputable def mixedSecurityLevel (who : ι) : ℝ :=
  ⨆ p : PMF (G.Strategy who), G.mixedWorstCaseEUInf who p

open Classical in
/-- Randomizing can only raise the guaranteed payoff: the pure security level is
    at most the mixed security level, since a pure strategy is the point-mass
    mixed strategy. -/
theorem securityLevelSup_le_mixedSecurityLevel (who : ι) [Nonempty (G.Strategy who)]
    (hbdd : BddAbove (Set.range (fun p : PMF (G.Strategy who) =>
      G.mixedWorstCaseEUInf who p))) :
    G.securityLevelSup who ≤ G.mixedSecurityLevel who := by
  apply ciSup_le
  intro s
  have heq : G.worstCaseEUInf who s = G.mixedWorstCaseEUInf who (PMF.pure s) := by
    simp only [worstCaseEUInf, mixedWorstCaseEUInf, expect_pure]
  rw [heq]
  exact le_ciSup hbdd (PMF.pure s)

open Classical in
/-- In a Nash equilibrium, each player's EU is at least their mixed security
    level: at equilibrium a player does at least as well as the best they could
    guarantee by randomizing. Strengthens `nash_eu_ge_securityLevelSup`, since
    the mixed security level dominates the pure one. -/
theorem nash_eu_ge_mixedSecurityLevel {σ : Profile G} (hN : G.IsNash σ)
    (who : ι) [Nonempty (G.Strategy who)] [Finite (G.Strategy who)]
    (hbddMixed : ∀ p : PMF (G.Strategy who),
      BddBelow (Set.range (fun τ : Profile G =>
        expect p (fun a => G.eu (Function.update τ who a) who)))) :
    G.eu σ who ≥ G.mixedSecurityLevel who := by
  haveI : Nonempty (PMF (G.Strategy who)) := ⟨PMF.pure (Classical.arbitrary _)⟩
  apply ciSup_le
  intro p
  have h1 : G.mixedWorstCaseEUInf who p ≤
      expect p (fun a => G.eu (Function.update σ who a) who) :=
    ciInf_le (hbddMixed p) σ
  have h2 : expect p (fun a => G.eu (Function.update σ who a) who) ≤ G.eu σ who := by
    have hmono := expect_mono p (fun a => G.eu (Function.update σ who a) who)
      (fun _ => G.eu σ who) (fun a => hN who a)
    simpa using hmono
  exact le_trans h1 h2

end Order

section Finite

variable (G : KernelGame ι) [Finite (Profile G)] [Nonempty (Profile G)]

open Classical in
/-- Worst-case EU for player `who` when they play `s`:
    the minimum EU over all possible opponent profiles. -/
noncomputable def worstCaseEU (who : ι) (s : G.Strategy who) : ℝ :=
  letI := Fintype.ofFinite (Profile G)
  Finset.inf' Finset.univ ⟨Classical.arbitrary _, Finset.mem_univ _⟩
    (fun σ => G.eu (Function.update σ who s) who)

open Classical in
/-- The worst-case EU is a lower bound on EU for any profile. -/
theorem worstCaseEU_le (who : ι) (s : G.Strategy who) (σ : Profile G) :
    G.worstCaseEU who s ≤ G.eu (Function.update σ who s) who :=
  by
    letI := Fintype.ofFinite (Profile G)
    exact Finset.inf'_le _ (Finset.mem_univ σ)

open Classical in
/-- The worst-case EU is a lower bound: a strategy guarantees at least
    its worst-case EU against any opponents. -/
theorem worstCaseEU_guarantees (who : ι) (s : G.Strategy who) :
    ∀ σ : Profile G, G.eu (Function.update σ who s) who ≥ G.worstCaseEU who s :=
  fun σ => worstCaseEU_le G who s σ

open Classical in
/-- On a finite nonempty profile space, the enumerated worst-case payoff is
the order-theoretic infimum. -/
theorem worstCaseEU_eq_worstCaseEUInf (who : ι) (s : G.Strategy who) :
    G.worstCaseEU who s = G.worstCaseEUInf who s := by
  letI := Fintype.ofFinite (Profile G)
  unfold worstCaseEU worstCaseEUInf
  exact Finset.inf'_univ_eq_ciInf _

variable [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]

open Classical in
/-- The security level (maximin value) of player `who`:
    the best worst-case EU they can guarantee. -/
noncomputable def securityLevel (who : ι) : ℝ :=
  letI := Fintype.ofFinite (G.Strategy who)
  Finset.sup' Finset.univ ⟨Classical.arbitrary _, Finset.mem_univ _⟩
    (fun s => G.worstCaseEU who s)

open Classical in
/-- On finite nonempty strategy and profile spaces, the enumerated security
level is the order-theoretic supremal security level. -/
theorem securityLevel_eq_securityLevelSup (who : ι) :
    G.securityLevel who = G.securityLevelSup who := by
  letI := Fintype.ofFinite (G.Strategy who)
  unfold securityLevel securityLevelSup
  rw [Finset.sup'_univ_eq_ciSup]
  apply iSup_congr
  intro s
  exact G.worstCaseEU_eq_worstCaseEUInf who s

/-- A finite-game security strategy attains the player's security level. -/
def IsSecurityStrategy (who : ι) (s : G.Strategy who) : Prop :=
  G.worstCaseEU who s = G.securityLevel who

/-- A security profile consists of a security strategy for every player.

This is intentionally not called an equilibrium: outside special classes such
as two-player zero-sum games with a value, it need not be Nash. -/
def IsSecurityProfile (σ : Profile G) : Prop :=
  ∀ i, G.IsSecurityStrategy i (σ i)

open Classical in
/-- A finite-game security strategy guarantees its security level. -/
theorem IsSecurityStrategy.guarantees {who : ι} {s : G.Strategy who}
    (h : G.IsSecurityStrategy who s) :
    G.Guarantees who s (G.securityLevel who) := by
  intro σ
  rw [← h]
  exact G.worstCaseEU_le who s σ

open Classical in
/-- Every coordinate of a security profile guarantees that player's security
level independently of the other coordinates. -/
theorem IsSecurityProfile.guarantees {σ : Profile G}
    (h : G.IsSecurityProfile σ) (who : ι) :
    G.Guarantees who (σ who) (G.securityLevel who) :=
  (h who).guarantees

open Classical in
/-- In a Nash equilibrium, each player's EU is at least their security level. -/
theorem nash_eu_ge_securityLevel {σ : Profile G} (hN : G.IsNash σ) (who : ι) :
    G.eu σ who ≥ G.securityLevel who := by
  letI := Fintype.ofFinite (G.Strategy who)
  simp only [securityLevel]
  apply Finset.sup'_le
  intro s _
  calc G.worstCaseEU who s
      ≤ G.eu (Function.update σ who s) who := worstCaseEU_le G who s σ
    _ ≤ G.eu σ who := by have := hN who s; linarith

open Classical in
/-- A dominant strategy guarantees at least the security level
    against any opponent profile. -/
theorem IsDominant.eu_ge_securityLevel
    {who : ι} {s : G.Strategy who} (hdom : G.IsDominant who s)
    (σ : Profile G) :
    G.eu (Function.update σ who s) who ≥ G.securityLevel who := by
  letI := Fintype.ofFinite (G.Strategy who)
  simp only [securityLevel]
  apply Finset.sup'_le
  intro t _
  calc G.worstCaseEU who t
      ≤ G.eu (Function.update σ who t) who := worstCaseEU_le G who t σ
    _ ≤ G.eu (Function.update σ who s) who := by
        have := hdom σ t; linarith

open Classical in
/-- The security level is the best guarantee: if a strategy guarantees
    at least `v` against all opponent profiles, then `v ≤ securityLevel`. -/
theorem le_securityLevel_of_forall_eu_ge (who : ι) (s : G.Strategy who) (v : ℝ)
    (hg : ∀ σ : Profile G, G.eu (Function.update σ who s) who ≥ v) :
    v ≤ G.securityLevel who := by
  letI := Fintype.ofFinite (G.Strategy who)
  calc v ≤ G.worstCaseEU who s := by
          apply Finset.le_inf'
          intro σ _
          exact hg σ
     _ ≤ G.securityLevel who :=
          Finset.le_sup' _ (Finset.mem_univ s)

open Classical in
/-- A security strategy exists: some strategy achieves the security level. -/
theorem exists_securityStrategy (who : ι) :
    ∃ s : G.Strategy who, G.worstCaseEU who s = G.securityLevel who := by
  letI := Fintype.ofFinite (G.Strategy who)
  obtain ⟨s, _, hs⟩ := Finset.exists_max_image Finset.univ
    (fun s => G.worstCaseEU who s) ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  exact ⟨s, le_antisymm (Finset.le_sup' _ (Finset.mem_univ s))
    (Finset.sup'_le _ _ (fun t _ => hs t (Finset.mem_univ t)))⟩

open Classical in
/-- Predicate-form version of `exists_securityStrategy`. -/
theorem exists_isSecurityStrategy (who : ι) :
    ∃ s : G.Strategy who, G.IsSecurityStrategy who s :=
  G.exists_securityStrategy who

open Classical in
/-- Every finite game has a profile made from independently selected security
strategies.  This profile is not necessarily a Nash equilibrium. -/
theorem exists_securityProfile : ∃ σ : Profile G, G.IsSecurityProfile σ := by
  choose σ hσ using fun i => G.exists_isSecurityStrategy i
  exact ⟨σ, hσ⟩

end Finite

end KernelGame

end GameTheory
