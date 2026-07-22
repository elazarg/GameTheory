/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Dominance.DominanceRelations
import GameTheory.Concepts.Dominance.StrictDominance
import GameTheory.Concepts.Mixed.MixedExtension

/-!
# Dominance and mixed extensions

Pure dominance persists when strategies are embedded as point masses in the
mixed extension. The proof averages the original pure-profile dominance
inequalities over the common product distribution of mixed opponents.
-/

namespace GameTheory

open Math.Probability
open Math.PMFProduct
open Math.ProbabilityMassFunction

namespace KernelGame

variable {ι : Type} [DecidableEq ι] [Fintype ι]
variable {G : KernelGame ι}

/-- Weak dominance between pure strategies persists in the mixed extension after
embedding both strategies as point masses. -/
theorem WeaklyDominatesReflexive.pure_to_mixedExtension
    [Finite (Profile G)] [Finite G.Outcome] [∀ i, Finite (G.Strategy i)]
    {who : ι} {s t : G.Strategy who}
    (h : G.WeaklyDominatesReflexive who s t) :
    G.mixedExtension.WeaklyDominatesReflexive who (PMF.pure s)
      (PMF.pure t) := by
  classical
  intro σ
  let σm : ∀ i, PMF (G.Strategy i) := σ
  have hleft :
      G.mixedExtension.eu (Function.update σ who (PMF.pure s)) who =
        expect (pmfPi (Function.update σm who (PMF.pure s)))
          (fun ρ => G.eu ρ who) :=
    G.mixedExtension_eu (Function.update σm who (PMF.pure s)) who
  have hright :
      G.mixedExtension.eu (Function.update σ who (PMF.pure t)) who =
        expect (pmfPi (Function.update σm who (PMF.pure t)))
          (fun ρ => G.eu ρ who) :=
    G.mixedExtension_eu (Function.update σm who (PMF.pure t)) who
  rw [hleft, hright]
  rw [← pmfPi_bind_update_pure σm who s]
  rw [← pmfPi_bind_update_pure σm who t]
  rw [expect_bind, expect_bind]
  exact expect_mono (pmfPi σm) _ _ fun ρ => by
    simp [expect_pure, h ρ]

/-- Weak dominance with a strict pure-profile witness persists in the mixed
extension after embedding both strategies as point masses. -/
theorem WeaklyDominatesWithStrictWitness.pure_to_mixedExtension
    [Finite (Profile G)] [Finite G.Outcome] [∀ i, Finite (G.Strategy i)]
    {who : ι} {s t : G.Strategy who}
    (h : G.WeaklyDominatesWithStrictWitness who s t) :
    G.mixedExtension.WeaklyDominatesWithStrictWitness who (PMF.pure s)
      (PMF.pure t) := by
  classical
  refine ⟨WeaklyDominatesReflexive.pure_to_mixedExtension (G := G) h.1, ?_⟩
  obtain ⟨σ, hstrict⟩ := h.2
  refine ⟨G.pureMixedProfile σ, ?_⟩
  rw [← G.pureMixedProfile_update σ who s]
  rw [← G.pureMixedProfile_update σ who t]
  rw [G.mixedExtension_eu_pureMixedProfile]
  rw [G.mixedExtension_eu_pureMixedProfile]
  exact hstrict

/-- Strict dominance between pure strategies persists in the mixed extension
after embedding both strategies as point masses. The opponent profile may be
genuinely mixed. -/
theorem StrictlyDominates.pure_to_mixedExtension
    [Finite (Profile G)] [Finite G.Outcome] [∀ i, Finite (G.Strategy i)]
    {who : ι} {s t : G.Strategy who}
    (h : G.StrictlyDominates who s t) :
    G.mixedExtension.StrictlyDominates who (PMF.pure s) (PMF.pure t) := by
  classical
  intro σ
  let σm : ∀ i, PMF (G.Strategy i) := σ
  have hleft :
      G.mixedExtension.eu (Function.update σ who (PMF.pure s)) who =
        expect (pmfPi (Function.update σm who (PMF.pure s)))
          (fun ρ => G.eu ρ who) :=
    G.mixedExtension_eu (Function.update σm who (PMF.pure s)) who
  have hright :
      G.mixedExtension.eu (Function.update σ who (PMF.pure t)) who =
        expect (pmfPi (Function.update σm who (PMF.pure t)))
          (fun ρ => G.eu ρ who) :=
    G.mixedExtension_eu (Function.update σm who (PMF.pure t)) who
  rw [hleft, hright]
  rw [← pmfPi_bind_update_pure σm who s]
  rw [← pmfPi_bind_update_pure σm who t]
  rw [expect_bind, expect_bind]
  simpa [expect_pure] using
    expect_lt_of_forall_lt (pmfPi σm)
      (fun ρ => G.eu (Function.update ρ who t) who)
      (fun ρ => G.eu (Function.update ρ who s) who)
      (fun ρ => h ρ)

/-- A pure dominant strategy remains dominant in the mixed extension after
embedding it as a point mass. The opponent profile and the deviating strategy in
the mixed extension may both be genuinely mixed. -/
theorem IsDominant.pure_to_mixedExtension
    [Finite (Profile G)] [Finite G.Outcome] [∀ i, Finite (G.Strategy i)]
    {who : ι} {s : G.Strategy who} (h : G.IsDominant who s) :
    G.mixedExtension.IsDominant who (PMF.pure s) := by
  classical
  intro σ τ
  let σm : ∀ i, PMF (G.Strategy i) := σ
  let ps : G.mixedExtension.Strategy who := PMF.pure s
  change G.mixedExtension.eu (Function.update σ who ps) who ≥
    G.mixedExtension.eu (Function.update σm who τ) who
  rw [G.mixedExtension_eu_update σm who τ]
  have hpoint : ∀ a : G.Strategy who,
      G.mixedExtension.eu (Function.update σm who (PMF.pure a)) who ≤
        G.mixedExtension.eu (Function.update σ who ps) who := by
    intro a
    exact WeaklyDominatesReflexive.pure_to_mixedExtension (G := G)
      (h.weaklyDominatesReflexive a) σ
  have hle := expect_mono τ
    (fun a : G.Strategy who =>
      G.mixedExtension.eu (Function.update σm who (PMF.pure a)) who)
    (fun _ : G.Strategy who =>
      G.mixedExtension.eu (Function.update σ who ps) who)
    hpoint
  rw [expect_const] at hle
  exact hle

/-- If a pure strategy weakly-strictly dominates every distinct pure strategy,
then its point mass weakly-strictly dominates every distinct mixed strategy in
the mixed extension. -/
theorem forall_weaklyDominatesWithStrictWitness_pure_to_mixedExtension
    [Finite (Profile G)] [Finite G.Outcome] [∀ i, Finite (G.Strategy i)]
    {who : ι} {s : G.Strategy who}
    (h : ∀ t : G.Strategy who, t ≠ s →
      G.WeaklyDominatesWithStrictWitness who s t)
    {τ : PMF (G.Strategy who)} (hτ : τ ≠ PMF.pure s) :
    G.mixedExtension.WeaklyDominatesWithStrictWitness who (PMF.pure s) τ := by
  classical
  obtain ⟨a, has, hτa⟩ := exists_ne_of_ne_pure τ hτ
  refine ⟨?_, ?_⟩
  · intro σ
    let σm : ∀ i, PMF (G.Strategy i) := σ
    let ps : G.mixedExtension.Strategy who := PMF.pure s
    change G.mixedExtension.eu (Function.update σ who ps) who ≥
      G.mixedExtension.eu (Function.update σm who τ) who
    rw [G.mixedExtension_eu_update σm who τ]
    have hpoint : ∀ b : G.Strategy who,
        G.mixedExtension.eu (Function.update σm who (PMF.pure b)) who ≤
          G.mixedExtension.eu (Function.update σ who ps) who := by
      intro b
      by_cases hbs : b = s
      · subst b
        exact le_rfl
      · exact WeaklyDominatesReflexive.pure_to_mixedExtension (G := G)
          (WeaklyDominatesWithStrictWitness.toWeaklyDominatesReflexive
            (h b hbs)) σ
    have hle := expect_mono τ
      (fun b : G.Strategy who =>
        G.mixedExtension.eu (Function.update σm who (PMF.pure b)) who)
      (fun _ : G.Strategy who =>
        G.mixedExtension.eu (Function.update σ who ps) who)
      hpoint
    rw [expect_const] at hle
    exact hle
  · have hpure_a :
        G.mixedExtension.WeaklyDominatesWithStrictWitness who (PMF.pure s)
          (PMF.pure a) :=
      WeaklyDominatesWithStrictWitness.pure_to_mixedExtension (G := G) (h a has)
    obtain ⟨σ, hstrict_a⟩ :=
      WeaklyDominatesWithStrictWitness.strict_witness hpure_a
    refine ⟨σ, ?_⟩
    let σm : ∀ i, PMF (G.Strategy i) := σ
    let ps : G.mixedExtension.Strategy who := PMF.pure s
    change G.mixedExtension.eu (Function.update σ who ps) who >
      G.mixedExtension.eu (Function.update σm who τ) who
    rw [G.mixedExtension_eu_update σm who τ]
    have hpoint : ∀ b : G.Strategy who,
        G.mixedExtension.eu (Function.update σm who (PMF.pure b)) who ≤
          G.mixedExtension.eu (Function.update σ who ps) who := by
      intro b
      by_cases hbs : b = s
      · subst b
        exact le_rfl
      · exact WeaklyDominatesReflexive.pure_to_mixedExtension (G := G)
          (WeaklyDominatesWithStrictWitness.toWeaklyDominatesReflexive
            (h b hbs)) σ
    exact expect_lt_const_of_le_of_exists_lt τ
      (fun b : G.Strategy who =>
        G.mixedExtension.eu (Function.update σm who (PMF.pure b)) who)
      hpoint ⟨a, hτa, hstrict_a⟩

/-- A pure strictly dominant strategy remains strictly dominant in the mixed
extension after embedding it as a point mass. The deviating strategy may be a
genuine mixed strategy; if it is not the point mass on `s`, some distinct pure
strategy receives positive probability and supplies the strict loss. -/
theorem IsStrictDominant.pure_to_mixedExtension
    [Finite (Profile G)] [Finite G.Outcome] [∀ i, Finite (G.Strategy i)]
    {who : ι} {s : G.Strategy who} (h : G.IsStrictDominant who s) :
    G.mixedExtension.IsStrictDominant who (PMF.pure s) := by
  classical
  intro σ τ hτ
  let σm : ∀ i, PMF (G.Strategy i) := σ
  let ps : G.mixedExtension.Strategy who := PMF.pure s
  change G.mixedExtension.eu (Function.update σ who ps) who >
    G.mixedExtension.eu (Function.update σm who τ) who
  rw [G.mixedExtension_eu_update σm who τ]
  have hle : ∀ a : G.Strategy who,
      G.mixedExtension.eu (Function.update σm who (PMF.pure a)) who ≤
        G.mixedExtension.eu (Function.update σ who ps) who := by
    intro a
    exact h.toDominant.pure_to_mixedExtension (G := G) σ (PMF.pure a)
  obtain ⟨a, has, hτa⟩ := exists_ne_of_ne_pure τ hτ
  have hstrict_a :
      G.mixedExtension.eu (Function.update σm who (PMF.pure a)) who <
        G.mixedExtension.eu (Function.update σ who ps) who := by
    have hstrict_pure : G.StrictlyDominates who s a := by
      intro ρ
      exact h ρ a has
    exact hstrict_pure.pure_to_mixedExtension (G := G) σ
  exact expect_lt_const_of_le_of_exists_lt τ
    (fun a : G.Strategy who =>
      G.mixedExtension.eu (Function.update σm who (PMF.pure a)) who)
    hle ⟨a, hτa, hstrict_a⟩

end KernelGame

end GameTheory
