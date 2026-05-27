/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.ApproximateNash
import GameTheory.Concepts.Convergence
import GameTheory.Concepts.MixedExtension

/-!
# Trembling-Hand Style Mixed Refinements

Definitions for limit refinements of mixed equilibria.

This file starts with the topology-free core: full-support mixed profiles and
pointwise convergence of mixed profiles. Trembling-hand-style predicates are
then stated as limits of fully mixed equilibria or approximate equilibria of the
mixed extension. The trembling-hand predicate itself is stated using explicit
vanishing lower-bound perturbations of mixed strategy spaces.
-/

namespace GameTheory

open Filter
open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- A mixed profile for a kernel game. This type does not require constructing
`mixedExtension`; it is definitionally the strategy-profile type of the mixed
extension when `ι` is finite. -/
abbrev MixedProfile (G : KernelGame ι) : Type :=
  ∀ i : ι, PMF (G.Strategy i)

namespace MixedProfile

variable {G : KernelGame ι}

/-- A lower-bound perturbation for mixed profiles: `δ i s` is the minimum
probability player `i` must assign to pure strategy `s`. Feasibility is not
part of this raw data; equilibrium predicates require profiles satisfying the
chosen bounds. -/
abbrev Perturbation (G : KernelGame ι) : Type :=
  ∀ i : ι, G.Strategy i → ENNReal

/-- A mixed profile is fully mixed when every player assigns full support to
their pure strategy space. -/
def FullyMixed (σ : G.MixedProfile) : Prop :=
  ∀ i : ι, PMF.FullSupport (σ i)

/-- Pointwise convergence of mixed profiles: each player's mixed strategy
converges pointwise as a PMF. -/
def ConvergesPointwise (σs : ℕ → G.MixedProfile) (σ : G.MixedProfile) : Prop :=
  ProfileConvergesWith (fun _i : ι => PMFConvergesPointwise) σs σ

/-- A mixed strategy respects a player-specific lower-bound perturbation. -/
def StrategyRespectsPerturbation {i : ι}
    (δi : G.Strategy i → ENNReal) (μ : PMF (G.Strategy i)) : Prop :=
  ∀ s : G.Strategy i, δi s ≤ μ s

/-- A mixed profile respects a lower-bound perturbation. -/
def RespectsPerturbation (δ : Perturbation (G := G)) (σ : G.MixedProfile) : Prop :=
  ∀ (i : ι), StrategyRespectsPerturbation (G := G) (δ i) (σ i)

/-- A perturbation is positive when every lower bound is nonzero. -/
def Perturbation.Positive (δ : Perturbation (G := G)) : Prop :=
  ∀ (i : ι) (s : G.Strategy i), δ i s ≠ 0

/-- A sequence of perturbations vanishes pointwise. -/
def Perturbation.ConvergesToZero
    (δs : ℕ → Perturbation (G := G)) : Prop :=
  ∀ (i : ι) (s : G.Strategy i),
    Tendsto (fun n : ℕ => δs n i s) atTop (nhds 0)

theorem FullyMixed.apply {σ : G.MixedProfile}
    (h : σ.FullyMixed) (i : ι) (s : G.Strategy i) :
    σ i s ≠ 0 :=
  h i s

theorem ConvergesPointwise.apply {σs : ℕ → G.MixedProfile} {σ : G.MixedProfile}
    (h : ConvergesPointwise σs σ) (i : ι) (s : G.Strategy i) :
    Tendsto (fun n : ℕ => σs n i s) atTop (nhds (σ i s)) :=
  (h i).apply s

theorem RespectsPerturbation.apply {δ : Perturbation (G := G)}
    {σ : G.MixedProfile} (h : RespectsPerturbation δ σ)
    (i : ι) (s : G.Strategy i) : δ i s ≤ σ i s :=
  h i s

theorem Perturbation.Positive.fullyMixed_of_respects
    {δ : Perturbation (G := G)} (hδ : Perturbation.Positive δ)
    {σ : G.MixedProfile} (hσ : RespectsPerturbation δ σ) :
    σ.FullyMixed := by
  intro i s hzero
  have hle : δ i s ≤ 0 := by simpa [hzero] using hσ.apply i s
  exact hδ i s (le_antisymm hle (zero_le : (0 : ENNReal) ≤ δ i s))

end MixedProfile

section MixedRefinements

variable [Fintype ι] [DecidableEq ι]
variable (G : KernelGame ι)

/-- Preference-parametric limit of fully mixed Nash equilibria of the mixed
extension. This is the clean limit core behind trembling-hand style
refinements, but it is separate from the perturbation-based definition below. -/
noncomputable def IsLimitOfFullyMixedEqFor
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : G.MixedProfile) : Prop :=
  ∃ σs : ℕ → G.MixedProfile,
    (∀ n, (σs n).FullyMixed ∧ G.mixedExtension.IsNashFor pref (σs n)) ∧
      MixedProfile.ConvergesPointwise σs σ

/-- EU-specialized limit of fully mixed Nash equilibria of the mixed extension.
-/
noncomputable def IsLimitOfFullyMixedNash (σ : G.MixedProfile) : Prop :=
  G.IsLimitOfFullyMixedEqFor G.euPref σ

/-- Limit of fully mixed approximate Nash equilibria whose approximation error
vanishes. This is often easier to produce than exact fully mixed equilibria and
is a useful stepping stone toward perturbation-model perfection. -/
noncomputable def IsLimitOfFullyMixedεNash
    (εs : ℕ → ℝ) (σ : G.MixedProfile) : Prop :=
  Tendsto εs atTop (nhds 0) ∧
    ∃ σs : ℕ → G.MixedProfile,
      (∀ n, (σs n).FullyMixed ∧ G.mixedExtension.IsεNash (εs n) (σs n)) ∧
        MixedProfile.ConvergesPointwise σs σ

/-- Equilibrium of a lower-bound perturbed mixed game for a supplied preference
relation. Deviations are restricted to mixed strategies that satisfy the same
player-specific lower bounds. -/
noncomputable def IsPerturbedEqFor
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (δ : MixedProfile.Perturbation (G := G))
    (σ : G.MixedProfile) : Prop :=
  MixedProfile.RespectsPerturbation δ σ ∧
    ∀ (who : ι) (τ : PMF (G.Strategy who)),
      MixedProfile.StrategyRespectsPerturbation (G := G) (δ who) τ →
        pref who
          (G.mixedExtension.outcomeKernel σ)
          (G.mixedExtension.outcomeKernel (Function.update σ who τ))

/-- EU-specialized equilibrium of a lower-bound perturbed mixed game. -/
noncomputable def IsPerturbedEq
    (δ : MixedProfile.Perturbation (G := G))
    (σ : G.MixedProfile) : Prop :=
  G.IsPerturbedEqFor G.euPref δ σ

/-- Preference-parametric trembling-hand perfection predicate: a mixed profile
is the pointwise limit of equilibria of positive lower-bound perturbations whose
bounds vanish pointwise. -/
noncomputable def IsTremblingHandPerfectFor
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : G.MixedProfile) : Prop :=
  ∃ (δs : ℕ → MixedProfile.Perturbation (G := G)) (σs : ℕ → G.MixedProfile),
    (∀ n, MixedProfile.Perturbation.Positive (δs n) ∧
      G.IsPerturbedEqFor pref (δs n) (σs n)) ∧
      MixedProfile.Perturbation.ConvergesToZero δs ∧
        MixedProfile.ConvergesPointwise σs σ

/-- EU-specialized trembling-hand perfection predicate. -/
noncomputable def IsTremblingHandPerfect (σ : G.MixedProfile) : Prop :=
  G.IsTremblingHandPerfectFor G.euPref σ

theorem isLimitOfFullyMixedEqFor_iff
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : G.MixedProfile) :
    G.IsLimitOfFullyMixedEqFor pref σ ↔
      ∃ σs : ℕ → G.MixedProfile,
        (∀ n, (σs n).FullyMixed ∧ G.mixedExtension.IsNashFor pref (σs n)) ∧
          MixedProfile.ConvergesPointwise σs σ := by
  rfl

theorem isLimitOfFullyMixedNash_iff (σ : G.MixedProfile) :
    G.IsLimitOfFullyMixedNash σ ↔
      ∃ σs : ℕ → G.MixedProfile,
        (∀ n, (σs n).FullyMixed ∧ G.mixedExtension.IsNash (σs n)) ∧
          MixedProfile.ConvergesPointwise σs σ := by
  rw [IsLimitOfFullyMixedNash, isLimitOfFullyMixedEqFor_iff]
  constructor
  · intro h
    rcases h with ⟨σs, hseq, hconv⟩
    exact ⟨σs, fun n => ⟨(hseq n).1,
      (G.mixedExtension.IsNash_iff_IsNashFor_eu (σs n)).2 (hseq n).2⟩, hconv⟩
  · intro h
    rcases h with ⟨σs, hseq, hconv⟩
    exact ⟨σs, fun n => ⟨(hseq n).1,
      (G.mixedExtension.IsNash_iff_IsNashFor_eu (σs n)).1 (hseq n).2⟩, hconv⟩

theorem isLimitOfFullyMixedεNash_iff
    (εs : ℕ → ℝ) (σ : G.MixedProfile) :
    G.IsLimitOfFullyMixedεNash εs σ ↔
      Tendsto εs atTop (nhds 0) ∧
        ∃ σs : ℕ → G.MixedProfile,
          (∀ n, (σs n).FullyMixed ∧ G.mixedExtension.IsεNash (εs n) (σs n)) ∧
            MixedProfile.ConvergesPointwise σs σ := by
  rfl

theorem isPerturbedEqFor_iff
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (δ : MixedProfile.Perturbation (G := G))
    (σ : G.MixedProfile) :
    G.IsPerturbedEqFor pref δ σ ↔
      MixedProfile.RespectsPerturbation δ σ ∧
        ∀ (who : ι) (τ : PMF (G.Strategy who)),
          MixedProfile.StrategyRespectsPerturbation (G := G) (δ who) τ →
            pref who
              (G.mixedExtension.outcomeKernel σ)
              (G.mixedExtension.outcomeKernel (Function.update σ who τ)) := by
  rfl

theorem IsPerturbedEqFor.fullyMixed
    {pref : ι → PMF G.Outcome → PMF G.Outcome → Prop}
    {δ : MixedProfile.Perturbation (G := G)} {σ : G.MixedProfile}
    (hδ : MixedProfile.Perturbation.Positive δ)
    (h : G.IsPerturbedEqFor pref δ σ) :
    σ.FullyMixed :=
  MixedProfile.Perturbation.Positive.fullyMixed_of_respects hδ h.1

theorem isTremblingHandPerfectFor_iff
    (pref : ι → PMF G.Outcome → PMF G.Outcome → Prop)
    (σ : G.MixedProfile) :
    G.IsTremblingHandPerfectFor pref σ ↔
      ∃ (δs : ℕ → MixedProfile.Perturbation (G := G)) (σs : ℕ → G.MixedProfile),
        (∀ n, MixedProfile.Perturbation.Positive (δs n) ∧
          G.IsPerturbedEqFor pref (δs n) (σs n)) ∧
          MixedProfile.Perturbation.ConvergesToZero δs ∧
            MixedProfile.ConvergesPointwise σs σ := by
  rfl

theorem isTremblingHandPerfect_iff (σ : G.MixedProfile) :
    G.IsTremblingHandPerfect σ ↔ G.IsTremblingHandPerfectFor G.euPref σ := by
  rfl

end MixedRefinements

end KernelGame

end GameTheory
