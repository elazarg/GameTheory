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
* `weaklyAcyclic_of_wellFounded` — weak acyclicity from well-founded improvement
  alone (no finiteness or potential)
* `IsOrdinalPotential.weaklyAcyclic` — every finite ordinal potential game is
  weakly acyclic (via well-foundedness of the potential-rank measure), with
  `IsExactPotential.weaklyAcyclic` as the exact special case
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

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
/-- **Weak acyclicity from well-founded improvement.** If the improvement relation
(`τ` reachable from `σ` by one improving step) has no infinite forward chain — i.e.
it is well-founded — then the game is weakly acyclic: from every profile, follow
improving steps until reaching a Nash equilibrium. This needs neither finiteness nor
a potential; those only serve to establish well-foundedness. -/
theorem weaklyAcyclic_of_wellFounded {G : KernelGame ι}
    (hwf : WellFounded (fun τ σ : Profile G => G.ImprovingStep σ τ)) :
    G.WeaklyAcyclic := by
  intro σ
  induction σ using hwf.induction with
  | _ σ ih =>
    by_cases hnash : G.IsNash σ
    · exact ⟨σ, Relation.ReflTransGen.refl, hnash⟩
    · obtain ⟨τ', hstep⟩ := (G.not_isNash_iff_exists_improvingStep).mp hnash
      obtain ⟨τ, hreach, hτ⟩ := ih τ' hstep
      exact ⟨τ, Relation.ReflTransGen.head hstep hreach, hτ⟩

open Classical in
/-- In a finite ordinal potential game the improvement relation is well-founded:
each improving step strictly drops the (finite, `ℕ`-valued) count of
higher-potential profiles, so improvement is a subrelation of that measure's order. -/
theorem IsOrdinalPotential.improvement_wellFounded {G : KernelGame ι}
    [Finite (Profile G)] {Φ : Profile G → ℝ} (hΦ : G.IsOrdinalPotential Φ) :
    WellFounded (fun τ σ : Profile G => G.ImprovingStep σ τ) := by
  haveI : Fintype (Profile G) := Fintype.ofFinite _
  have hsub : Subrelation (fun τ σ : Profile G => G.ImprovingStep σ τ)
      (InvImage Nat.lt (fun σ => (Finset.univ.filter (fun q => Φ σ < Φ q)).card)) := by
    intro τ σ hstep
    exact hΦ.improvingStep_filter_card_lt hstep
  exact hsub.wf (InvImage.wf _ Nat.lt_wfRel.wf)

open Classical in
/-- **Potential games are weakly acyclic.** Every finite ordinal potential game is
weakly acyclic — improvement is well-founded (each step raises the potential), so
`weaklyAcyclic_of_wellFounded` applies. -/
theorem IsOrdinalPotential.weaklyAcyclic {G : KernelGame ι} [Finite (Profile G)]
    {Φ : Profile G → ℝ} (hΦ : G.IsOrdinalPotential Φ) : G.WeaklyAcyclic :=
  weaklyAcyclic_of_wellFounded hΦ.improvement_wellFounded

open Classical in
/-- Exact potential games are weakly acyclic (the exact-potential special case of
`IsOrdinalPotential.weaklyAcyclic`). -/
theorem IsExactPotential.weaklyAcyclic {G : KernelGame ι} [Finite (Profile G)]
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ) : G.WeaklyAcyclic :=
  hΦ.toOrdinal.weaklyAcyclic

end KernelGame

end GameTheory
