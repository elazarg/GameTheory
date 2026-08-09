/-
# Uniform equilibrium

A uniform equilibrium has a coordinatewise long-run average payoff and is an
approximate Nash equilibrium of every sufficiently long finite truncation.
Finite-horizon rationality is defined through the canonical `IsεNash` surface;
the familiar repeated-game name is a transparent specialization, not a second
equilibrium engine.

The theorem family is adapted from
`reference/GameTheory-v1/GameTheory/Concepts/Repeated/Uniform.lean` and the
long-run definitions from `Concepts/Repeated/Basic.lean`, both at pinned commit
`a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
-/

import GameTheory.Core.Approximate
import GameTheory.Repeated.Basic

noncomputable section

namespace GameTheory.UtilityGame

universe uι

variable {ι : Type uι}

/-- Utility of a repeated strategy profile in a finite average-payoff
truncation. -/
def finiteAverageUtility (G : UtilityGame ι) (horizon : ℕ) :
    Utility G.repeatedSignature :=
  fun profile who => G.finiteAveragePayoff horizon profile who

/-- Approximate Nash in the finite average-payoff truncation, expressed by the
canonical approximate-equilibrium predicate. -/
def IsεFiniteRepeatedNash (G : UtilityGame ι) [DecidableEq ι]
    (horizon : ℕ) (epsilon : ℝ) (profile : G.RepeatedProfile) : Prop :=
  IsεNash G.repeatedForm (G.finiteAverageUtility horizon) epsilon profile

theorem isεFiniteRepeatedNash_iff
    (G : UtilityGame ι) [DecidableEq ι]
    {horizon : ℕ} {epsilon : ℝ} {profile : G.RepeatedProfile} :
    G.IsεFiniteRepeatedNash horizon epsilon profile ↔
      ∀ who deviation,
        G.finiteAveragePayoff horizon
            (Profile.update profile who deviation) who ≤
          G.finiteAveragePayoff horizon profile who + epsilon := by
  rw [IsεFiniteRepeatedNash, isεNash_iff]
  simp only [repeatedForm, expectedUtility_pure]
  rfl

/-- A single horizon threshold makes the profile approximately Nash at every
longer truncation. -/
def IsUniformεEquilibrium (G : UtilityGame ι) [DecidableEq ι]
    (epsilon : ℝ) (profile : G.RepeatedProfile) : Prop :=
  ∃ threshold : ℕ, ∀ horizon, threshold ≤ horizon →
    G.IsεFiniteRepeatedNash horizon epsilon profile

/-- A uniform equilibrium has a long-run average and satisfies every positive
uniform approximation tolerance. -/
def IsUniformEquilibrium (G : UtilityGame ι) [DecidableEq ι]
    (profile : G.RepeatedProfile) : Prop :=
  (∃ value : ι → ℝ, G.HasLongRunAveragePayoff profile value) ∧
    ∀ epsilon : ℝ, 0 < epsilon → G.IsUniformεEquilibrium epsilon profile

/-- Finite-horizon approximate Nash is monotone in the error allowance. -/
theorem IsεFiniteRepeatedNash.mono
    {G : UtilityGame ι} [DecidableEq ι]
    {horizon : ℕ} {epsilon epsilon' : ℝ} {profile : G.RepeatedProfile}
    (h : G.IsεFiniteRepeatedNash horizon epsilon profile)
    (hle : epsilon ≤ epsilon') :
    G.IsεFiniteRepeatedNash horizon epsilon' profile :=
  IsεNash.mono G.repeatedForm (G.finiteAverageUtility horizon) h hle

/-- Uniform approximate equilibrium is monotone in the error allowance. -/
theorem IsUniformεEquilibrium.mono
    {G : UtilityGame ι} [DecidableEq ι]
    {epsilon epsilon' : ℝ} {profile : G.RepeatedProfile}
    (h : G.IsUniformεEquilibrium epsilon profile)
    (hle : epsilon ≤ epsilon') :
    G.IsUniformεEquilibrium epsilon' profile := by
  obtain ⟨threshold, hthreshold⟩ := h
  exact ⟨threshold, fun horizon hhorizon =>
    (hthreshold horizon hhorizon).mono hle⟩

/-- Stationary repetition of a stage Nash equilibrium is uniform: every
nonempty finite truncation is exact Nash and its average payoff is constant. -/
theorem stationaryRepeatedProfile_isUniformEquilibrium_of_isNash
    (G : UtilityGame ι) [DecidableEq ι]
    {profile : Profile G.form.sig}
    (hnash : IsNash G.form (euPreference G.utility) profile) :
    G.IsUniformEquilibrium (G.stationaryRepeatedProfile profile) := by
  refine ⟨⟨fun who => G.stagePayoff profile who,
    G.hasLongRunAveragePayoff_stationaryRepeatedProfile profile⟩, ?_⟩
  intro epsilon hepsilon
  refine ⟨1, fun horizon hhorizon => ?_⟩
  rw [G.isεFiniteRepeatedNash_iff]
  intro who deviation
  have hhorizon0 : horizon ≠ 0 := by omega
  have hdeviation :
      G.finiteAveragePayoff horizon
          (Profile.update (G.stationaryRepeatedProfile profile) who deviation) who ≤
        G.stagePayoff profile who := by
    refine G.finiteAveragePayoff_le_of_forall_stagePayoff_le
      (hT := hhorizon0) (fun period => ?_)
    rw [G.repeatedPlay_update_stationaryRepeatedProfile]
    simpa only [stagePayoff, euPreference_apply] using
      (isNash_iff profile).1 hnash who
        (deviation (List.ofFn fun k : Fin period =>
          G.repeatedPlay
            (Profile.update (G.stationaryRepeatedProfile profile)
              who deviation) k))
  rw [G.finiteAveragePayoff_stationaryRepeatedProfile
    hhorizon0 profile who]
  linarith

end GameTheory.UtilityGame
