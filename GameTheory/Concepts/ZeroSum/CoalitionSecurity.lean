/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.Coalition
import GameTheory.Core.GameProperties
import GameTheory.Concepts.ZeroSum.SecurityStrategy

/-!
# Coalition Security and Forceability

Coalition-level outcome-law forceability, expected-utility guarantees, and the
lossless reduction of a coalition and its complement to a two-player zero-sum
game.

The protocol-level primitives live in `GameTheory.Core.Coalition`; this module
adds utility-aware `KernelGame` wrappers and connects singleton coalitions to
ordinary security guarantees.
-/

open scoped BigOperators

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

section CoalitionForceability

variable (G : KernelGame ι) [DecidableEq ι]

/-- Kernel-game wrapper around `GameForm.CoalitionStrategy`. -/
abbrev CoalitionStrategy (S : Finset ι) := G.toGameForm.CoalitionStrategy S

/-- Kernel-game wrapper around `GameForm.ComplementStrategy`. -/
abbrev ComplementStrategy (S : Finset ι) := G.toGameForm.ComplementStrategy S

/-- Override a kernel-game profile with a coalition's joint strategy. -/
abbrev coalitionOverride (S : Finset ι) (τ : G.CoalitionStrategy S)
    (σ : Profile G) : Profile G :=
  G.toGameForm.overrideCoalition S τ σ

/-- A fixed joint strategy ensures an outcome-law predicate against every
complementary profile. -/
abbrev CoalitionStrategyEnsuresLaw (S : Finset ι) (τ : G.CoalitionStrategy S)
    (P : PMF G.Outcome → Prop) : Prop :=
  G.toGameForm.CoalitionStrategyEnsuresLaw S τ P

/-- Coalition `S` can force an arbitrary predicate on its induced outcome law. -/
abbrev CoalitionForcesLaw (S : Finset ι) (P : PMF G.Outcome → Prop) : Prop :=
  G.toGameForm.CoalitionForcesLaw S P

/-- Coalition `S`'s worst-case guarantee for a fixed joint strategy.

The target must hold at every outcome in the support of the outcome kernel,
for every profile played by the complement.  For a deterministic kernel this
reduces to requiring the target at its unique realized outcome. -/
abbrev coalitionWorstCase (S : Finset ι) (τ : G.CoalitionStrategy S)
    (target : G.Outcome → Prop) : Prop :=
  G.toGameForm.CoalitionStrategyForces S τ target

/-- Coalition `S` can force `target`: it has a joint strategy under which the
target holds against every complementary profile at every supported outcome. -/
abbrev CoalitionForces (S : Finset ι) (target : G.Outcome → Prop) : Prop :=
  G.toGameForm.CoalitionForces S target

/-- Expected value of the members' total realized utility. -/
def coalitionUtility (S : Finset ι) (ω : G.Outcome) : ℝ :=
  ∑ i ∈ S, G.utility ω i

/-- A fixed joint strategy guarantees expected value at least `v` for the
outcome statistic `u`. -/
noncomputable def CoalitionStrategyGuaranteesEU (S : Finset ι)
    (τ : G.CoalitionStrategy S) (u : G.Outcome → ℝ) (v : ℝ) : Prop :=
  G.CoalitionStrategyEnsuresLaw S τ (fun μ => expect μ u ≥ v)

/-- Coalition `S` has a joint strategy guaranteeing expected value at least
`v` for the outcome statistic `u`. -/
noncomputable def CoalitionGuaranteesEU (S : Finset ι)
    (u : G.Outcome → ℝ) (v : ℝ) : Prop :=
  G.CoalitionForcesLaw S (fun μ => expect μ u ≥ v)

/-- Coalition `S` can guarantee total expected coalition utility at least `v`. -/
noncomputable def CoalitionGuaranteesSum (S : Finset ι) (v : ℝ) : Prop :=
  G.CoalitionGuaranteesEU S (G.coalitionUtility S) v

/-- Attach a scalar zero-sum objective to the coalition merge. Player `0`
receives `value`; the adversarial complement, player `1`, receives its negation. -/
def mergeCoalitionWithValue (S : Finset ι) (value : G.Outcome → ℝ) :
    KernelGame (Fin 2) :=
  (G.toGameForm.mergeCoalition S).withUtility
    (fun ω j => if j = 0 then value ω else -value ω)

/-- Bundle `S` and its complement into a meaningful two-player zero-sum game,
using total realized coalition utility as player `0`'s payoff. -/
def mergeCoalition (S : Finset ι) : KernelGame (Fin 2) :=
  G.mergeCoalitionWithValue S (G.coalitionUtility S)

/-- A scalar coalition merge is zero-sum by construction. -/
theorem mergeCoalitionWithValue_isZeroSum (S : Finset ι)
    (value : G.Outcome → ℝ) :
    (G.mergeCoalitionWithValue S value).IsZeroSum := by
  intro ω
  simp [mergeCoalitionWithValue, Fin.sum_univ_two]

/-- The coalition-sum merge is zero-sum. -/
theorem mergeCoalition_isZeroSum (S : Finset ι) :
    (G.mergeCoalition S).IsZeroSum :=
  G.mergeCoalitionWithValue_isZeroSum S (G.coalitionUtility S)

/-- Attaching a scalar objective does not change the merged strategy spaces. -/
@[simp] theorem mergeCoalitionWithValue_Strategy (S : Finset ι)
    (value : G.Outcome → ℝ) :
    (G.mergeCoalitionWithValue S value).Strategy =
      G.toGameForm.MergedCoalitionStrategy S := rfl

/-- Attaching a scalar objective does not change the merged game form. -/
@[simp] theorem mergeCoalitionWithValue_toGameForm (S : Finset ι)
    (value : G.Outcome → ℝ) :
    (G.mergeCoalitionWithValue S value).toGameForm =
      G.toGameForm.mergeCoalition S := rfl

/-- The strategy space of a coalition merge is the pair of bundled strategy
spaces. -/
@[simp] theorem mergeCoalition_Strategy (S : Finset ι) :
    (G.mergeCoalition S).Strategy = G.toGameForm.MergedCoalitionStrategy S := rfl

@[simp] theorem mergeCoalition_toGameForm (S : Finset ι) :
    (G.mergeCoalition S).toGameForm = G.toGameForm.mergeCoalition S := rfl

/-- Kernel-game profiles are losslessly equivalent to profiles of their
coalition merge. -/
def coalitionProfileEquiv (S : Finset ι) :
    Profile G ≃ Profile (G.mergeCoalition S) :=
  G.toGameForm.coalitionProfileEquiv S

open Classical in
/-- **Coalition merge is lossless for forceability.** Bundling a coalition into
one virtual player preserves exactly the targets that it can force. -/
theorem coalitionForces_iff_mergeCoalition_forces (S : Finset ι)
    (target : G.Outcome → Prop) :
    G.CoalitionForces S target ↔
      (G.mergeCoalition S).CoalitionForces {0} target :=
  G.toGameForm.coalitionForces_iff_mergeCoalition_forces S target

/-- The law-level version of lossless coalition merging. -/
theorem coalitionForcesLaw_iff_mergeCoalition_forcesLaw (S : Finset ι)
    (P : PMF G.Outcome → Prop) :
    G.CoalitionForcesLaw S P ↔
      (G.mergeCoalition S).CoalitionForcesLaw {0} P :=
  G.toGameForm.coalitionForcesLaw_iff_mergeCoalition_forcesLaw S P

/-- Singleton coalition EU guarantees are exactly ordinary player guarantees. -/
theorem coalitionGuaranteesEU_singleton_iff (who : ι) (v : ℝ) :
    G.CoalitionGuaranteesEU {who} (fun ω => G.utility ω who) v ↔
      ∃ s : G.Strategy who, G.Guarantees who s v := by
  constructor
  · rintro ⟨τ, hτ⟩
    let s : G.Strategy who := τ ⟨who, by simp⟩
    refine ⟨s, fun σ => ?_⟩
    have hp : G.coalitionOverride {who} τ σ = Function.update σ who s := by
      funext i
      by_cases hi : i = who
      · subst i
        simp [s]
      · simp [hi]
    change expect (G.outcomeKernel (Function.update σ who s))
        (fun ω => G.utility ω who) ≥ v
    rw [← hp]
    exact hτ σ
  · rintro ⟨s, hs⟩
    let τ : G.CoalitionStrategy {who} := fun i => by
      rcases i with ⟨i, hi⟩
      have hi' : i = who := Finset.mem_singleton.mp hi
      subst i
      exact s
    refine ⟨τ, fun σ => ?_⟩
    have hp : G.coalitionOverride {who} τ σ = Function.update σ who s := by
      funext i
      by_cases hi : i = who
      · subst i
        simp [τ]
      · simp [hi]
    change expect (G.outcomeKernel (G.coalitionOverride {who} τ σ))
      (fun ω => G.utility ω who) ≥ v
    rw [hp]
    exact hs σ

open Classical in
/-- Coalition EU guarantees are precisely ordinary player-`0` guarantees in
the scalar zero-sum coalition merge. -/
theorem coalitionGuaranteesEU_iff_exists_mergeGuarantees (S : Finset ι)
    (u : G.Outcome → ℝ) (v : ℝ) :
    G.CoalitionGuaranteesEU S u v ↔
      ∃ s : (G.mergeCoalitionWithValue S u).Strategy 0,
        (G.mergeCoalitionWithValue S u).Guarantees 0 s v := by
  let H := G.mergeCoalitionWithValue S u
  calc
    G.CoalitionGuaranteesEU S u v ↔
        (G.toGameForm.mergeCoalition S).CoalitionForcesLaw {0}
          (fun μ => expect μ u ≥ v) :=
      G.toGameForm.coalitionForcesLaw_iff_mergeCoalition_forcesLaw S
        (fun μ => expect μ u ≥ v)
    _ ↔ H.CoalitionGuaranteesEU {0} (fun ω => H.utility ω 0) v := by
      change
        (G.toGameForm.mergeCoalition S).CoalitionForcesLaw {0}
            (fun μ => expect μ u ≥ v) ↔
          (G.toGameForm.mergeCoalition S).CoalitionForcesLaw {0}
            (fun μ => expect μ u ≥ v)
      rfl
    _ ↔ ∃ s : H.Strategy 0, H.Guarantees 0 s v :=
      H.coalitionGuaranteesEU_singleton_iff 0 v

/-- Total coalition-utility guarantees become ordinary guarantees in the
default coalition-sum merge. -/
theorem coalitionGuaranteesSum_iff_exists_mergeGuarantees (S : Finset ι)
    (v : ℝ) :
    G.CoalitionGuaranteesSum S v ↔
      ∃ s : (G.mergeCoalition S).Strategy 0,
        (G.mergeCoalition S).Guarantees 0 s v := by
  simpa [CoalitionGuaranteesSum, mergeCoalition] using
    G.coalitionGuaranteesEU_iff_exists_mergeGuarantees S
      (G.coalitionUtility S) v

end CoalitionForceability

end KernelGame

end GameTheory
