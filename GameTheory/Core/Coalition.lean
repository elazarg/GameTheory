/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameForm

/-!
# Coalition Forceability and Merging

Protocol-level vocabulary for coalitions in a game form.  The primitive
guarantee is a predicate on the induced outcome law; sure forceability and
expected-utility guarantees are specializations supplied by later layers.

## Main definitions

* `GameForm.CoalitionStrategy` -- a joint strategy for a finite coalition
* `GameForm.CoalitionForcesLaw` -- forceability of an outcome-law predicate
* `GameForm.CoalitionForces` -- sure forceability of an outcome predicate
* `GameForm.mergeCoalition` -- bundle a coalition and its complement as `Fin 2`
* `GameForm.coalitionProfileEquiv` -- lossless equivalence of profile spaces
-/

namespace GameTheory

namespace GameForm

variable {ι : Type}

section Forceability

variable (F : GameForm ι) [DecidableEq ι]

/-- A joint strategy for the members of `S`. -/
abbrev CoalitionStrategy (S : Finset ι) := ∀ i : S, F.Strategy i

/-- A joint strategy for the players outside `S`.

The subtype formulation does not require the ambient player type to be finite. -/
abbrev ComplementStrategy (S : Finset ι) :=
  ∀ i : {i : ι // i ∉ S}, F.Strategy i

/-- Override a profile with the joint strategy chosen by coalition `S`. -/
def overrideCoalition (S : Finset ι) (τ : F.CoalitionStrategy S)
    (σ : F.Profile) : F.Profile :=
  fun i => if hi : i ∈ S then τ ⟨i, hi⟩ else σ i

@[simp] theorem overrideCoalition_of_mem (S : Finset ι)
    (τ : F.CoalitionStrategy S) (σ : F.Profile) {i : ι} (hi : i ∈ S) :
    F.overrideCoalition S τ σ i = τ ⟨i, hi⟩ := by
  simp [overrideCoalition, hi]

@[simp] theorem overrideCoalition_of_not_mem (S : Finset ι)
    (τ : F.CoalitionStrategy S) (σ : F.Profile) {i : ι} (hi : i ∉ S) :
    F.overrideCoalition S τ σ i = σ i := by
  simp [overrideCoalition, hi]

/-- A fixed joint strategy `τ` ensures the outcome-law property `P` against
every strategy profile of the complement. -/
def CoalitionStrategyEnsuresLaw (S : Finset ι) (τ : F.CoalitionStrategy S)
    (P : PMF F.Outcome → Prop) : Prop :=
  ∀ σ : F.Profile, P (F.outcomeKernel (F.overrideCoalition S τ σ))

/-- Coalition `S` can force an outcome-law property.  This is the general
effectivity operator; qualitative and expected-utility guarantees are
specializations of `P`. -/
def CoalitionForcesLaw (S : Finset ι) (P : PMF F.Outcome → Prop) : Prop :=
  ∃ τ : F.CoalitionStrategy S, F.CoalitionStrategyEnsuresLaw S τ P

/-- Every positive-probability outcome of `μ` satisfies `target`. -/
def SupportSatisfies (target : F.Outcome → Prop) (μ : PMF F.Outcome) : Prop :=
  ∀ ω ∈ μ.support, target ω

omit [DecidableEq ι] in
@[simp] theorem supportSatisfies_pure (target : F.Outcome → Prop) (ω : F.Outcome) :
    F.SupportSatisfies target (PMF.pure ω) ↔ target ω := by
  simp [SupportSatisfies]

/-- A fixed joint strategy surely forces `target`: against every complementary
profile, every supported outcome satisfies it. -/
def CoalitionStrategyForces (S : Finset ι) (τ : F.CoalitionStrategy S)
    (target : F.Outcome → Prop) : Prop :=
  F.CoalitionStrategyEnsuresLaw S τ (F.SupportSatisfies target)

/-- Coalition `S` surely forces `target`. -/
def CoalitionForces (S : Finset ι) (target : F.Outcome → Prop) : Prop :=
  F.CoalitionForcesLaw S (F.SupportSatisfies target)

theorem CoalitionForces.mono {S : Finset ι} {p q : F.Outcome → Prop}
    (hpq : ∀ ω, p ω → q ω) (h : F.CoalitionForces S p) :
    F.CoalitionForces S q := by
  rcases h with ⟨τ, hτ⟩
  exact ⟨τ, fun σ ω hω => hpq ω (hτ σ ω hω)⟩

end Forceability

section Merge

variable (F : GameForm ι) [DecidableEq ι]

/-- Strategy spaces for the two sides of a coalition merge. Player `0` is the
coalition and player `1` is its complement. -/
def MergedCoalitionStrategy (S : Finset ι) : Fin 2 → Type :=
  Fin.cases (F.CoalitionStrategy S) (fun _ : Fin 1 => F.ComplementStrategy S)

/-- Bundle an original profile into the two sides of a coalition merge. -/
def bundleCoalitionProfile (S : Finset ι) (σ : F.Profile) :
    ∀ b, F.MergedCoalitionStrategy S b :=
  Fin.cases (fun i : S => σ i) (fun _ (_ : {i : ι // i ∉ S}) => σ _)

/-- Expand a profile of the two-player coalition merge into an original-game
profile. -/
def unbundleCoalitionProfile (S : Finset ι)
    (σ : ∀ b, F.MergedCoalitionStrategy S b) : F.Profile :=
  fun i => if hi : i ∈ S then σ 0 ⟨i, hi⟩ else σ 1 ⟨i, hi⟩

@[simp] theorem unbundleCoalitionProfile_bundle (S : Finset ι) (σ : F.Profile) :
    F.unbundleCoalitionProfile S (F.bundleCoalitionProfile S σ) = σ := by
  funext i
  by_cases hi : i ∈ S
  · simp [unbundleCoalitionProfile, bundleCoalitionProfile, hi]
  · simp only [unbundleCoalitionProfile, hi, dite_false]
    rfl

@[simp] theorem bundleCoalitionProfile_unbundle (S : Finset ι)
    (σ : ∀ b, F.MergedCoalitionStrategy S b) :
    F.bundleCoalitionProfile S (F.unbundleCoalitionProfile S σ) = σ := by
  funext b
  fin_cases b <;> funext i
  · change (if hi : (i : ι) ∈ S then σ 0 ⟨i, hi⟩ else _) = σ 0 i
    simp [i.2]
  · change (if hi : (i : ι) ∈ S then _ else σ 1 ⟨i, hi⟩) = σ 1 i
    simp [i.2]

/-- Original profiles are equivalent to profiles split into a coalition bundle
and a complementary bundle. -/
def coalitionProfileEquiv (S : Finset ι) :
    F.Profile ≃ (∀ b, F.MergedCoalitionStrategy S b) where
  toFun := F.bundleCoalitionProfile S
  invFun := F.unbundleCoalitionProfile S
  left_inv := F.unbundleCoalitionProfile_bundle S
  right_inv := F.bundleCoalitionProfile_unbundle S

/-- Bundle `S` and its complement into two virtual players, preserving the
outcome space and outcome kernel. -/
def mergeCoalition (S : Finset ι) : GameForm (Fin 2) where
  Strategy := F.MergedCoalitionStrategy S
  Outcome := F.Outcome
  outcomeKernel := fun σ => F.outcomeKernel (F.unbundleCoalitionProfile S σ)

@[simp] theorem mergeCoalition_Strategy (S : Finset ι) :
    (F.mergeCoalition S).Strategy = F.MergedCoalitionStrategy S := rfl

@[simp] theorem mergeCoalition_Outcome (S : Finset ι) :
    (F.mergeCoalition S).Outcome = F.Outcome := rfl

@[simp] theorem mergeCoalition_outcomeKernel_bundle (S : Finset ι)
    (σ : F.Profile) :
    (F.mergeCoalition S).outcomeKernel (F.bundleCoalitionProfile S σ) =
      F.outcomeKernel σ := by
  simp [mergeCoalition]

open Classical in
/-- Expanding a merged profile after player `0` installs a coalition strategy
is the same as installing that strategy after expanding the profile. -/
theorem unbundleCoalitionProfile_override (S : Finset ι)
    (τ : (F.mergeCoalition S).CoalitionStrategy {0})
    (σ : (F.mergeCoalition S).Profile) :
    F.unbundleCoalitionProfile S
        ((F.mergeCoalition S).overrideCoalition {0} τ σ) =
      F.overrideCoalition S (τ ⟨0, by simp⟩)
        (F.unbundleCoalitionProfile S σ) := by
  funext i
  by_cases hi : i ∈ S
  · simp [unbundleCoalitionProfile, overrideCoalition, hi]
  · simp [unbundleCoalitionProfile, overrideCoalition, hi]

open Classical in
/-- **Coalition merge is lossless for law-level forceability.** -/
theorem coalitionForcesLaw_iff_mergeCoalition_forcesLaw (S : Finset ι)
    (P : PMF F.Outcome → Prop) :
    F.CoalitionForcesLaw S P ↔
      (F.mergeCoalition S).CoalitionForcesLaw {0} P := by
  constructor
  · rintro ⟨τ, hτ⟩
    let mergedτ : (F.mergeCoalition S).CoalitionStrategy {0} := fun b => by
      rcases b with ⟨b, hb⟩
      have hb' : b = 0 := Finset.mem_singleton.mp hb
      subst b
      exact τ
    refine ⟨mergedτ, fun σ => ?_⟩
    have hmerge := F.unbundleCoalitionProfile_override S mergedτ σ
    rw [show mergedτ ⟨0, by simp⟩ = τ by rfl] at hmerge
    change P (F.outcomeKernel (F.unbundleCoalitionProfile S
      ((F.mergeCoalition S).overrideCoalition {0} mergedτ σ)))
    rw [hmerge]
    exact hτ (F.unbundleCoalitionProfile S σ)
  · rintro ⟨mergedτ, hτ⟩
    let τ : F.CoalitionStrategy S := mergedτ ⟨0, by simp⟩
    refine ⟨τ, fun σ => ?_⟩
    have h := hτ (F.bundleCoalitionProfile S σ)
    change P (F.outcomeKernel (F.unbundleCoalitionProfile S
      ((F.mergeCoalition S).overrideCoalition {0} mergedτ
        (F.bundleCoalitionProfile S σ)))) at h
    rw [F.unbundleCoalitionProfile_override S mergedτ,
      F.unbundleCoalitionProfile_bundle S] at h
    simpa [τ] using h

/-- Sure forceability is preserved by coalition merging. -/
theorem coalitionForces_iff_mergeCoalition_forces (S : Finset ι)
    (target : F.Outcome → Prop) :
    F.CoalitionForces S target ↔
      (F.mergeCoalition S).CoalitionForces {0} target :=
  F.coalitionForcesLaw_iff_mergeCoalition_forcesLaw S (F.SupportSatisfies target)

end Merge

end GameForm

end GameTheory
