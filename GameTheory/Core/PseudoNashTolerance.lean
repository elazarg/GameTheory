/-
# Tolerances for pseudo-Nash equilibria

Pseudo-Nash has a built-in distinguishing tolerance, a negligible probability,
but compares utilities exactly. Two further tolerances are useful.

* **Payoff tolerance.** `IsTolerantPseudoNash G ε` asks the honest utility
  ensemble shifted up by `ε κ` to dominate every deviation. With `ε = 0` it is
  pseudo-Nash, and in a fixed game with bounded utilities and constant `ε` it
  is `ε`-Nash (`GameTheory.Analysis.PseudoNash`). A negligible shift absorbs
  negligible sure gains, which plain pseudo-Nash does not: a sure payoff of
  `1 - 2 ^ (-κ)` against a sure `1` loses every mean comparison. Shifting one
  side of a mean test is shifting the other side the opposite way, so secure
  implementations carry tolerant pseudo-Nash.
* **Concrete tolerance.** At one size and with `m` draws,
  `IsEmpiricalPseudoNashAt` bounds each deviation's gap by `δ`. Replacing
  either side of a comparison moves the gap by at most the mean-test advantage
  of the replacement, so a simulation with advantages `ε₁` and `ε₂` turns
  `(m, δ)` into `(m, δ + ε₁ + ε₂)`; each advantage is at most `4 m` times the
  statistical distance. This is the concrete-security form of the ideal-to-real
  theorem.
-/
import GameTheory.Core.PseudoNash

noncomputable section

namespace GameTheory

open GameTheory.Math GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι} [DecidableEq ι]

/-! ## Payoff tolerance -/

/-- The honest utility ensemble, shifted up by `ε κ`, computationally
mean-dominates that of every unilateral replacement. -/
def ParameterizedGame.IsTolerantPseudoNash (G : ParameterizedGame.{uι, us, uo} ι) (ε : ℕ → ℝ)
    (profile : Profile G.sig) : Prop :=
  ∀ who (replacement : G.sig.Strategy who),
    ComputationallyMeanDominates (shiftEnsemble ε (G.utilityLaw who profile))
      (G.utilityLaw who (Profile.update profile who replacement))

theorem ParameterizedGame.isTolerantPseudoNash_zero (G : ParameterizedGame.{uι, us, uo} ι)
    (profile : Profile G.sig) :
    G.IsTolerantPseudoNash (fun _ => 0) profile ↔ G.IsPseudoNash profile := by
  have hshift : ∀ X : ℕ → PMF ℝ, shiftEnsemble (fun _ => 0) X = X := by
    intro X
    funext κ
    simp only [shiftEnsemble, add_zero]
    exact PMF.map_id _
  rw [ParameterizedGame.isPseudoNash_iff, ParameterizedGame.IsTolerantPseudoNash]
  simp only [hshift]

/-- **Ideal to real, with tolerance.** A secure implementation carries tolerant
pseudo-Nash when the tests can compare means with the utility ensembles of the
real game shifted up and of the ideal game shifted down. -/
theorem SecureImplementation.isTolerantPseudoNash {tests : Set (SampleTest ℝ)}
    {ideal real : ParameterizedGame.{uι, us, uo} ι} (impl : SecureImplementation tests ideal real)
    (ε : ℕ → ℝ)
    (hreal : ∀ who profile, ContainsMeanTests tests (shiftEnsemble ε (real.utilityLaw who profile)))
    (hideal : ∀ who profile,
      ContainsMeanTests tests (shiftEnsemble (fun κ => -ε κ) (ideal.utilityLaw who profile)))
    {profile : Profile ideal.sig} (h : ideal.IsTolerantPseudoNash ε profile) :
    real.IsTolerantPseudoNash ε (Profile.map impl.compile profile) := by
  intro who deviation
  obtain ⟨simulated, hsimulated⟩ := impl.simulate profile who deviation
  have hhonest : MeanTestIndistinguishable
      (ideal.utilityLaw who (Profile.update profile who simulated))
      (shiftEnsemble ε (real.utilityLaw who (Profile.map impl.compile profile)))
      (shiftEnsemble ε (ideal.utilityLaw who profile)) :=
    MeanTestIndistinguishable.shift ε ((impl.honest profile who).meanTestIndistinguishable
      (hideal who (Profile.update profile who simulated)))
  have hdeviation := hsimulated.meanTestIndistinguishable
    (hreal who (Profile.map impl.compile profile))
  exact (ComputationallyMeanDominates.congr_right hdeviation).mpr
    ((ComputationallyMeanDominates.congr_left hhonest).mpr (h who simulated))

/-! ## Concrete tolerance -/

/-- `(m, δ)`-pseudo-Nash at size `κ`: with `m` draws of each, no deviation's
mean reaches the honest mean more than `δ` more often than the reverse. -/
def ParameterizedGame.IsEmpiricalPseudoNashAt (G : ParameterizedGame.{uι, us, uo} ι) (κ m : ℕ)
    (δ : ℝ)
    (profile : Profile G.sig) : Prop :=
  ∀ who (replacement : G.sig.Strategy who),
    EmpiricalMeanDominates m δ (G.utilityLaw who profile κ)
      (G.utilityLaw who (Profile.update profile who replacement) κ)

/-- **Concrete ideal to real.** At one size, the tolerance grows by the
mean-test advantages of the honest and deviation simulations. -/
theorem isEmpiricalPseudoNashAt_of_simulation {ideal real : ParameterizedGame.{uι, us, uo} ι}
    (compile : ∀ who, ideal.sig.Strategy who → real.sig.Strategy who)
    {profile : Profile ideal.sig} {κ m : ℕ} {δ ε₁ ε₂ : ℝ}
    (hsimulate : ∀ who (deviation : real.sig.Strategy who), ∃ simulated : ideal.sig.Strategy who,
      meanTestAdvantage (ideal.utilityLaw who (Profile.update profile who simulated) κ)
          (ideal.utilityLaw who profile κ) (real.utilityLaw who (Profile.map compile profile) κ)
          m ≤ ε₁ ∧
        meanTestAdvantage (real.utilityLaw who (Profile.map compile profile) κ)
          (ideal.utilityLaw who (Profile.update profile who simulated) κ)
          (real.utilityLaw who (Profile.update (Profile.map compile profile) who deviation) κ)
          m ≤ ε₂)
    (h : ideal.IsEmpiricalPseudoNashAt κ m δ profile) :
    real.IsEmpiricalPseudoNashAt κ m (δ + ε₁ + ε₂) (Profile.map compile profile) := by
  intro who deviation
  obtain ⟨simulated, hhonest, hdeviation⟩ := hsimulate who deviation
  have hideal := h who simulated
  have hstep1 := meanComparisonGap_le_of_left (ideal.utilityLaw who profile κ)
    (real.utilityLaw who (Profile.map compile profile) κ)
    (ideal.utilityLaw who (Profile.update profile who simulated) κ) m
  have hstep2 := meanComparisonGap_le_of_right
    (real.utilityLaw who (Profile.map compile profile) κ)
    (ideal.utilityLaw who (Profile.update profile who simulated) κ)
    (real.utilityLaw who (Profile.update (Profile.map compile profile) who deviation) κ) m
  unfold EmpiricalMeanDominates at hideal ⊢
  linarith

/-- **Concrete statistical ideal to real.** If compiled honest play is within
statistical distance `s₁` of ideal honest play and every real deviation within
`s₂` of some ideal deviation, then `(m, δ)`-pseudo-Nash becomes
`(m, δ + 4 m (s₁ + s₂))`-pseudo-Nash. -/
theorem isEmpiricalPseudoNashAt_of_statisticalDistance
    {ideal real : ParameterizedGame.{uι, us, uo} ι}
    (compile : ∀ who, ideal.sig.Strategy who → real.sig.Strategy who)
    {profile : Profile ideal.sig} {κ m : ℕ} {δ s₁ s₂ : ℝ}
    (hhonest : ∀ who, statisticalDistance (ideal.utilityLaw who profile κ)
      (real.utilityLaw who (Profile.map compile profile) κ) ≤ s₁)
    (hdeviation : ∀ who (deviation : real.sig.Strategy who),
      ∃ simulated : ideal.sig.Strategy who,
        statisticalDistance (ideal.utilityLaw who (Profile.update profile who simulated) κ)
          (real.utilityLaw who (Profile.update (Profile.map compile profile) who deviation) κ) ≤
            s₂)
    (h : ideal.IsEmpiricalPseudoNashAt κ m δ profile) :
    real.IsEmpiricalPseudoNashAt κ m (δ + 4 * m * s₁ + 4 * m * s₂)
      (Profile.map compile profile) := by
  refine isEmpiricalPseudoNashAt_of_simulation compile (fun who deviation => ?_) h
  obtain ⟨simulated, hsim⟩ := hdeviation who deviation
  have hm : (0 : ℝ) ≤ 4 * m := by positivity
  exact ⟨simulated,
    (meanTestAdvantage_le _ _ _ m).trans (mul_le_mul_of_nonneg_left (hhonest who) hm),
    (meanTestAdvantage_le _ _ _ m).trans (mul_le_mul_of_nonneg_left hsim hm)⟩

end GameTheory
