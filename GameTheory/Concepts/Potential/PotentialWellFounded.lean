/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability
import GameTheory.Concepts.Potential.PotentialFIP
import GameTheory.Concepts.Foundations.BestResponseDynamics

/-!
# Finite Improvement Property for Potential Games

The finite improvement property (FIP): in a finite exact potential game,
every sequence of improving deviations terminates. Equivalently, there
is no infinite improving path.

## Main results

* `IsExactPotential.no_infinite_improving_path` — no infinite sequence of
  profiles where each step is a single-player improving deviation
* `WeaklyAcyclic` — from every profile some finite improving path reaches a Nash
  equilibrium
* `IsOrdinalPotential.weaklyAcyclic` — every finite ordinal potential game is
  weakly acyclic (with `IsExactPotential.weaklyAcyclic` as the exact special case)
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

open Classical in
/-- An improving step: `τ` is obtained from `σ` by a single player's
    improving deviation. -/
def ImprovingStep (G : KernelGame ι) (σ τ : Profile G) : Prop :=
  ∃ (who : ι) (s' : G.Strategy who),
    τ = Function.update σ who s' ∧
    G.eu τ who > G.eu σ who

open Classical in
/-- Each improving step strictly increases the exact potential. -/
theorem IsExactPotential.improvingStep_increases_potential
    {G : KernelGame ι} {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ)
    {σ τ : Profile G} (hstep : G.ImprovingStep σ τ) :
    Φ τ > Φ σ := by
  obtain ⟨who, s', rfl, himprove⟩ := hstep
  exact hΦ.improving_deviation_increases_potential himprove

open Classical in
/-- **Finite Improvement Property**: in a finite exact potential game,
    there is no infinite improving path. Any sequence of profiles where
    each consecutive pair is an improving step must eventually repeat,
    contradicting strict increase of the potential. -/
theorem IsExactPotential.no_infinite_improving_path
    {G : KernelGame ι} [Finite (Profile G)]
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ) :
    ¬ ∃ (path : ℕ → Profile G),
        ∀ n, G.ImprovingStep (path n) (path (n + 1)) := by
  rintro ⟨path, hstep⟩
  have hincr : ∀ n, Φ (path n) < Φ (path (n + 1)) :=
    fun n => hΦ.improvingStep_increases_potential (hstep n)
  have hmono : StrictMono (Φ ∘ path) := strictMono_nat_of_lt_succ hincr
  have hinj : Function.Injective path := by
    intro a b hab
    have : Φ (path a) = Φ (path b) := by rw [hab]
    exact hmono.injective this
  exact not_injective_infinite_finite path hinj

/-! ## Weak acyclicity

The existence counterpart to the finite improvement property: from *every* profile
*some* finite improving path reaches a Nash equilibrium. FIP says every improving
path is finite; weak acyclicity says a path to equilibrium exists — the property
underlying convergence of better-response dynamics (e.g. iterative voting). -/

open Classical in
/-- A game is **weakly acyclic** if from every profile some finite sequence of
improving deviations reaches a Nash equilibrium. -/
def WeaklyAcyclic (G : KernelGame ι) : Prop :=
  ∀ σ : Profile G, ∃ τ, Relation.ReflTransGen G.ImprovingStep σ τ ∧ G.IsNash τ

open Classical in
/-- A profile fails to be Nash exactly when an improving step leaves it. -/
theorem not_isNash_iff_exists_improvingStep {G : KernelGame ι} (σ : Profile G) :
    ¬ G.IsNash σ ↔ ∃ τ, G.ImprovingStep σ τ := by
  unfold IsNash ImprovingStep
  push Not
  constructor
  · rintro ⟨who, s', h⟩
    exact ⟨Function.update σ who s', who, s', rfl, h⟩
  · rintro ⟨τ, who, s', rfl, h⟩
    exact ⟨who, s', h⟩

open Classical in
/-- An improving step strictly increases an ordinal potential (the forward
direction of the ordinal-potential equivalence applied to the deviator). -/
theorem IsOrdinalPotential.improvingStep_increases_potential
    {G : KernelGame ι} {Φ : Profile G → ℝ} (hΦ : G.IsOrdinalPotential Φ)
    {σ τ : Profile G} (hstep : G.ImprovingStep σ τ) : Φ σ < Φ τ := by
  obtain ⟨who, s', rfl, himprove⟩ := hstep
  exact (hΦ who σ s').mp himprove

open Classical in
/-- An improving step strictly shrinks the set of strictly-higher-potential
profiles: the target dominates the source, so every profile above the target is
above the source, while the target itself is above the source but not above
itself. -/
theorem IsOrdinalPotential.improvingStep_filter_card_lt
    {G : KernelGame ι} [Fintype (Profile G)] {Φ : Profile G → ℝ}
    (hΦ : G.IsOrdinalPotential Φ) {σ τ : Profile G} (hstep : G.ImprovingStep σ τ) :
    (Finset.univ.filter (fun q => Φ τ < Φ q)).card <
      (Finset.univ.filter (fun q => Φ σ < Φ q)).card := by
  have hpot : Φ σ < Φ τ := hΦ.improvingStep_increases_potential hstep
  have hsub : (Finset.univ.filter (fun q => Φ τ < Φ q)) ⊆
      (Finset.univ.filter (fun q => Φ σ < Φ q)) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact lt_trans hpot hq
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset hsub]
  exact ⟨τ, by simp [hpot], by simp⟩

open Classical in
/-- **Potential games are weakly acyclic.** In a finite *ordinal* potential game,
from every profile a finite sequence of improving deviations reaches a Nash
equilibrium: follow improving steps — each raises the potential, so the number of
higher-potential profiles strictly drops — until none remains, i.e. a Nash
equilibrium. -/
theorem IsOrdinalPotential.weaklyAcyclic {G : KernelGame ι} [Finite (Profile G)]
    {Φ : Profile G → ℝ} (hΦ : G.IsOrdinalPotential Φ) : G.WeaklyAcyclic := by
  haveI : Fintype (Profile G) := Fintype.ofFinite _
  suffices H : ∀ n (σ : Profile G),
      (Finset.univ.filter (fun q => Φ σ < Φ q)).card = n →
      ∃ τ, Relation.ReflTransGen G.ImprovingStep σ τ ∧ G.IsNash τ from
    fun σ => H _ σ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hσ
    by_cases hnash : G.IsNash σ
    · exact ⟨σ, Relation.ReflTransGen.refl, hnash⟩
    · obtain ⟨τ', hstep⟩ := (not_isNash_iff_exists_improvingStep σ).mp hnash
      have hlt := hΦ.improvingStep_filter_card_lt hstep
      rw [hσ] at hlt
      obtain ⟨τ, hreach, hτ⟩ := ih _ hlt τ' rfl
      exact ⟨τ, Relation.ReflTransGen.head hstep hreach, hτ⟩

open Classical in
/-- Exact potential games are weakly acyclic (the exact-potential special case of
`IsOrdinalPotential.weaklyAcyclic`). -/
theorem IsExactPotential.weaklyAcyclic {G : KernelGame ι} [Finite (Profile G)]
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ) : G.WeaklyAcyclic :=
  hΦ.toOrdinal.weaklyAcyclic

end KernelGame

end GameTheory
