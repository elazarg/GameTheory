/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Dominance.StrictDominance
import GameTheory.Concepts.Dominance.DominanceNash
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import Math.Probability

/-!
# Solvability in dominant strategies

A game is *dominant-strategy solvable* if every player has a strictly dominant
strategy. In such a game, there is a unique Nash equilibrium.

This is a stronger property than the textbook notion of *dominance solvability*
(iterated elimination of dominated strategies leaving a unique surviving
profile); every dominant-strategy-solvable game is dominance-solvable, but not
conversely.

The unqualified notion — iterated elimination of strictly dominated strategies
(IESDS), `SurvivesStrictDominance`/`IsIESDSSolvable` below — is now formalized,
and is genuinely more general than `IsDominantStrategySolvable`: it only ever
tests whether an action is beaten *relative to the opponents' surviving
actions*, round by round, rather than requiring one action to beat every
alternative against *every* opponent profile in a single round.

## Main definitions

* `IsDominantStrategySolvable` — every player has a strictly dominant strategy
* `SurvivesStrictDominance n who s` — `s` survives `n` rounds of iterated
  elimination of strictly dominated strategies
* `IsIESDSSolvable σ` — iterated elimination leaves exactly the profile `σ`

## Main results

* `IsDominantStrategySolvable.unique_nash` — the unique Nash equilibrium
* `IsDominantStrategySolvable.nash_is_dominant` — the Nash profile consists of dominant strategies
* `IsIESDSSolvable.correlatedEq_eq_pure` — a dominance-solvable game has at
  most one correlated equilibrium, the point mass at the surviving profile

Proving the converse (the surviving profile of an IESDS-solvable game *is* a
correlated equilibrium, hence that dominance-solvable games are correlation
saturated in the sense of `CorrelationSaturation.lean`) needs the surviving
profile to be shown Nash, which for the iterated notion requires mixed Nash
existence plus "no mixed Nash puts weight on a dominated action" — genuinely
more machinery than the single-round `IsDominantStrategySolvable` case (where
`dominant_is_nash` suffices directly). Not yet formalized here.
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι] (G : KernelGame ι)

/-- A game is *dominant-strategy solvable* if every player has a strictly
dominant strategy (stronger than textbook dominance solvability). -/
def IsDominantStrategySolvable : Prop :=
  ∀ who : ι, ∃ s : G.Strategy who, G.IsStrictDominant who s

open Classical in
/-- The dominant strategy profile. -/
noncomputable def IsDominantStrategySolvable.dominantProfile
    (h : G.IsDominantStrategySolvable) : Profile G :=
  fun i => (h i).choose

/-- The dominant strategy profile is Nash (follows from dominant_is_nash). -/
theorem IsDominantStrategySolvable.isNash (h : G.IsDominantStrategySolvable) :
    G.IsNash (h.dominantProfile G) := by
  classical
  apply dominant_is_nash
  intro i
  have hdom := (h i).choose_spec
  exact hdom.toDominant

open Classical in
/-- In a dominance-solvable game, the Nash equilibrium is unique:
    any Nash profile must use the dominant strategy for each player. -/
theorem IsDominantStrategySolvable.nash_unique
    (h : G.IsDominantStrategySolvable) {σ : Profile G} (hN : G.IsNash σ) :
    σ = h.dominantProfile G := by
  funext i
  have hdom := (h i).choose_spec
  have hbr : G.IsBestResponse i σ (σ i) := by
    intro s'
    have h := hN i s'
    simpa [Function.update_eq_self] using h
  exact hdom.unique_best_response σ hbr

/-- Combining: the dominant profile is the unique Nash equilibrium. -/
theorem IsDominantStrategySolvable.exists_unique_nash (h : G.IsDominantStrategySolvable) :
    ∃! σ : Profile G, G.IsNash σ :=
  ⟨h.dominantProfile G, h.isNash G, fun _ hN => (h.nash_unique G hN)⟩

/-! ## Iterated elimination of strictly dominated strategies (IESDS) -/

/-- `s` **survives `n` rounds** of iterated elimination of strictly dominated
strategies: every strategy survives round `0`, and `s` survives round `n + 1`
when it survived round `n` and no round-`n` survivor `t` beats it in expected
utility *at every profile built from round-`n` survivors*. This relativization
to survivors (rather than testing against every profile, as `StrictlyDominates`
does) is what makes elimination proceed in rounds. -/
def SurvivesStrictDominance (G : KernelGame ι) : ℕ → ∀ who : ι, G.Strategy who → Prop
  | 0, _, _ => True
  | n + 1, who, s => G.SurvivesStrictDominance n who s ∧
      ¬ ∃ t, G.SurvivesStrictDominance n who t ∧
        ∀ σ : Profile G, (∀ i, G.SurvivesStrictDominance n i (σ i)) →
          G.eu (Function.update σ who t) who > G.eu (Function.update σ who s) who

/-- **A game is IESDS-solvable at `σ`** when some round `N` of iterated
elimination of strictly dominated strategies leaves, for every player, exactly
the action `σ` prescribes. -/
def IsIESDSSolvable (G : KernelGame ι) (σ : Profile G) : Prop :=
  ∃ N, ∀ i s, G.SurvivesStrictDominance N i s ↔ s = σ i

/-- **A correlated equilibrium's support only ever recommends round-`n`
survivors.** By induction on `n`: round `0` is vacuous, and at round `n + 1`, a
recommended action failing to survive is either already ruled out by round `n`
(induction hypothesis), or beaten by some round-`n` survivor `t` relative to
round-`n`-survivor profiles — and the induction hypothesis, applied to every
player, guarantees `μ`'s entire support already consists of round-`n`
survivors, so `t`'s domination applies on all of `μ`'s support, and
`IsCorrelatedEq.support_avoids_dominated_relative` finishes it off. -/
theorem IsCorrelatedEq.support_subset_survives
    {G : KernelGame ι} [Finite (Profile G)] [Finite G.Outcome]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ) :
    ∀ (n : ℕ) (who : ι) (σ : Profile G), μ σ ≠ 0 → G.SurvivesStrictDominance n who (σ who) := by
  intro n
  induction n with
  | zero => intro who σ _; trivial
  | succ n ih =>
    intro who σ0 hσ0
    refine ⟨ih who σ0 hσ0, ?_⟩
    rintro ⟨t, _htsurv, hdomt⟩
    have hS : ∀ τ, μ τ ≠ 0 → ∀ j, G.SurvivesStrictDominance n j (τ j) :=
      fun τ hτ j => ih j τ hτ
    have hcontra := hce.support_avoids_dominated_relative
      (fun τ => ∀ j, G.SurvivesStrictDominance n j (τ j)) hS who hdomt
    exact hcontra σ0 hσ0 rfl

/-- **A dominance-solvable game has at most one correlated equilibrium: the
point mass at the surviving profile.** Every correlated equilibrium's support
consists, coordinatewise, of round-`N` survivors (`support_subset_survives`);
at round `N` the only survivor for player `i` is `σ i`, so the support is
exactly `{σ}`. -/
theorem IsIESDSSolvable.correlatedEq_eq_pure
    {G : KernelGame ι} [Finite (Profile G)] [Finite G.Outcome]
    {σ : Profile G} (hsolv : G.IsIESDSSolvable σ)
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ) :
    μ = PMF.pure σ := by
  obtain ⟨N, hN⟩ := hsolv
  have hsub : ∀ τ, τ ≠ σ → μ τ = 0 := by
    intro τ hτne
    by_contra hτ
    exact hτne (funext fun i => (hN i (τ i)).mp (hce.support_subset_survives N i τ hτ))
  apply PMF.ext
  intro τ
  by_cases hτσ : τ = σ
  · subst hτσ
    have hsum : (∑' x, μ x) = 1 := μ.tsum_coe
    have hsingle : (∑' x, μ x) = μ τ := by
      apply tsum_eq_single τ
      intro x hx
      exact hsub x hx
    rw [hsingle] at hsum
    rw [hsum, PMF.pure_apply, if_pos rfl]
  · rw [hsub τ hτσ, PMF.pure_apply, if_neg hτσ]

end KernelGame

end GameTheory
