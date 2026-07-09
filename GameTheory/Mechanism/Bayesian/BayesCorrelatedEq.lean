/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.Bayesian.InformationDesign
import GameTheory.Concepts.Correlation.CorrelatedNashMixed

/-!
# Bayes Correlated Equilibrium

Finite, PMF-based Bayes correlated equilibrium (BCE) for `BayesianGame`.

A BCE is represented by a joint law over type profiles and recommended action
profiles.  The law is:

* Bayes plausible: its type marginal is the common prior;
* obedient: no player can improve by replacing the recommended action with a
  deviation depending on that player's own type and recommendation.

The file also records the complete-information specialization: a
complete-information BCE projects to a correlated equilibrium of the base
`KernelGame`, and every correlated equilibrium embeds as a complete-information
BCE.
-/

namespace GameTheory

open Math.Probability

namespace BayesianGame

variable {ι : Type}

/-- Joint type profile of a Bayesian game. -/
abbrev TypeProfile (B : BayesianGame ι) := ∀ i, B.Θ i

/-- Joint action profile of a Bayesian game. -/
abbrev ActionProfile (B : BayesianGame ι) := ∀ i, B.Act i

/-- A direct recommendation law: realized types together with recommended
actions. -/
abbrev RecommendationLaw (B : BayesianGame ι) :=
  PMF (B.TypeProfile × B.ActionProfile)

/-- Bayes plausibility for a direct recommendation law: its type-profile marginal is
the prior (the recommendation-law instance of `SignalStructure.HasPriorMarginal`). -/
def BayesPlausible (B : BayesianGame ι) (ψ : B.RecommendationLaw) : Prop :=
  SignalStructure.HasPriorMarginal B.prior ψ

/-- A player can condition a deviation on their own type and recommended action. -/
abbrev ObedienceDeviation (B : BayesianGame ι) (who : ι) :=
  B.Θ who → B.Act who → B.Act who

/-- Expected utility from following the recommendation law. -/
noncomputable def recommendedEU (B : BayesianGame ι)
    (ψ : B.RecommendationLaw) (who : ι) : ℝ :=
  expect ψ fun rec => B.utility rec.1 rec.2 who

/-- The direct recommendation law induced by a strategy profile. -/
noncomputable def strategyRecommendationLaw (B : BayesianGame ι)
    (σ : B.BProfile) : B.RecommendationLaw :=
  B.prior.map fun θ => (θ, fun i => σ i (θ i))

theorem strategyRecommendationLaw_bayesPlausible
    (B : BayesianGame ι) (σ : B.BProfile) :
    B.BayesPlausible (B.strategyRecommendationLaw σ) := by
  unfold BayesPlausible strategyRecommendationLaw SignalStructure.HasPriorMarginal
  rw [PMF.map_comp]
  change PMF.map id B.prior = B.prior
  rw [PMF.map_id]

theorem recommendedEU_strategyRecommendationLaw
    (B : BayesianGame ι) [Finite (B.TypeProfile × B.ActionProfile)]
    (σ : B.BProfile) (who : ι) :
    B.recommendedEU (B.strategyRecommendationLaw σ) who =
      B.exAnteEU σ who := by
  unfold recommendedEU strategyRecommendationLaw exAnteEU
  rw [Math.Probability.expect_map_fintype_target]

/-- A finite information structure for a Bayesian game: a joint law over states
and private signal profiles whose state marginal is the game's prior. -/
structure InformationStructure (B : BayesianGame ι) (Sig : ι → Type) where
  law : PMF (B.TypeProfile × (∀ i, Sig i))
  bayesPlausible : SignalStructure.HasPriorMarginal B.prior law

namespace InformationStructure

variable {B : BayesianGame ι} {Sig : ι → Type}

/-- The Bayesian game induced by adding private signals to the original type. -/
noncomputable def inducedBayesianGame
    (S : InformationStructure B Sig) : BayesianGame ι where
  Θ := fun i => B.Θ i × Sig i
  Act := B.Act
  prior := S.law.map fun rec i => (rec.1 i, rec.2 i)
  utility := fun τ a i => B.utility (fun j => (τ j).1) a i

/-- The original-game recommendation law induced by a strategy profile in the
expanded information-structure game. -/
noncomputable def outcomeLaw
    (S : InformationStructure B Sig)
    (ρ : (S.inducedBayesianGame).BProfile) : B.RecommendationLaw :=
  S.law.map fun rec => (rec.1, fun i => ρ i (rec.1 i, rec.2 i))

theorem outcomeLaw_bayesPlausible
    (S : InformationStructure B Sig)
    (ρ : (S.inducedBayesianGame).BProfile) :
    B.BayesPlausible (S.outcomeLaw ρ) := by
  unfold BayesianGame.BayesPlausible outcomeLaw SignalStructure.HasPriorMarginal
  rw [PMF.map_comp]
  change PMF.map Prod.fst S.law = B.prior
  exact S.bayesPlausible

end InformationStructure

section Decidable

variable [DecidableEq ι]

open Classical in
/-- Apply one player's obedience deviation to an action profile. -/
def applyObedienceDeviation (B : BayesianGame ι)
    (θ : B.TypeProfile) (a : B.ActionProfile) (who : ι)
    (dev : B.ObedienceDeviation who) : B.ActionProfile :=
  Function.update a who (dev (θ who) (a who))

/-- Expected utility after one player applies an obedience deviation. -/
noncomputable def deviatingEU (B : BayesianGame ι)
    (ψ : B.RecommendationLaw) (who : ι)
    (dev : B.ObedienceDeviation who) : ℝ :=
  expect ψ fun rec =>
    B.utility rec.1 (B.applyObedienceDeviation rec.1 rec.2 who dev) who

/-- Bayes correlated equilibrium: Bayes plausibility plus obedience. -/
def BayesCorrelatedEq (B : BayesianGame ι) (ψ : B.RecommendationLaw) : Prop :=
  B.BayesPlausible ψ ∧
    ∀ (who : ι) (dev : B.ObedienceDeviation who),
      B.recommendedEU ψ who ≥ B.deviatingEU ψ who dev

open Classical in
theorem deviatingEU_strategyRecommendationLaw
    (B : BayesianGame ι) [Finite (B.TypeProfile × B.ActionProfile)]
    (σ : B.BProfile) (who : ι)
    (dev : B.ObedienceDeviation who) :
    B.deviatingEU (B.strategyRecommendationLaw σ) who dev =
      B.exAnteEU
        (Function.update σ who (fun θi => dev θi (σ who θi))) who := by
  unfold deviatingEU strategyRecommendationLaw exAnteEU applyObedienceDeviation
  rw [Math.Probability.expect_map_fintype_target]
  congr 1
  funext θ
  congr 1
  ext i
  by_cases hi : i = who
  · subst hi
    simp [Function.update]
  · simp [Function.update_of_ne hi]

/-- A Bayes-Nash equilibrium induces a Bayes correlated equilibrium via its
deterministic recommendation law. -/
theorem BayesNash.strategyRecommendationLaw_bayesCorrelatedEq
    (B : BayesianGame ι) [Finite (B.TypeProfile × B.ActionProfile)]
    {σ : B.BProfile} (hN : B.BayesNash σ) :
    B.BayesCorrelatedEq (B.strategyRecommendationLaw σ) := by
  refine ⟨B.strategyRecommendationLaw_bayesPlausible σ, ?_⟩
  intro who dev
  rw [B.recommendedEU_strategyRecommendationLaw σ who]
  rw [B.deviatingEU_strategyRecommendationLaw σ who dev]
  exact (B.bayesNash_iff_exAnteEU σ).1 hN who
    (fun θi => dev θi (σ who θi))

namespace InformationStructure

variable {B : BayesianGame ι} {Sig : ι → Type}

omit [DecidableEq ι] in
theorem recommendedEU_outcomeLaw
    (S : InformationStructure B Sig)
    [Finite (B.TypeProfile × B.ActionProfile)]
    [Finite ((S.inducedBayesianGame).TypeProfile)]
    (ρ : (S.inducedBayesianGame).BProfile) (who : ι) :
    B.recommendedEU (S.outcomeLaw ρ) who =
      S.inducedBayesianGame.exAnteEU ρ who := by
  unfold recommendedEU outcomeLaw BayesianGame.exAnteEU
  rw [Math.Probability.expect_map_fintype_target]
  letI : Finite ((i : ι) → B.Θ i × Sig i) := by
    change Finite ((S.inducedBayesianGame).TypeProfile)
    infer_instance
  unfold inducedBayesianGame
  rw [Math.Probability.expect_map_fintype_target]

open Classical in
theorem deviatingEU_outcomeLaw
    (S : InformationStructure B Sig)
    [Finite (B.TypeProfile × B.ActionProfile)]
    [Finite ((S.inducedBayesianGame).TypeProfile)]
    (ρ : (S.inducedBayesianGame).BProfile) (who : ι)
    (dev : B.ObedienceDeviation who) :
    B.deviatingEU (S.outcomeLaw ρ) who dev =
      S.inducedBayesianGame.exAnteEU
        (Function.update ρ who
          (fun τi => dev τi.1 (ρ who τi))) who := by
  unfold deviatingEU outcomeLaw BayesianGame.exAnteEU
  unfold applyObedienceDeviation
  rw [Math.Probability.expect_map_fintype_target]
  letI : Finite ((i : ι) → B.Θ i × Sig i) := by
    change Finite ((S.inducedBayesianGame).TypeProfile)
    infer_instance
  unfold inducedBayesianGame
  rw [Math.Probability.expect_map_fintype_target]
  congr 1
  funext rec
  congr 1
  ext i
  by_cases hi : i = who
  · subst hi
    simp [Function.update]
  · simp [Function.update_of_ne hi]

/-- A Bayes-Nash equilibrium under any finite private-signal information
structure induces a BCE outcome law in the original Bayesian game. -/
theorem BayesNash.outcomeLaw_bayesCorrelatedEq
    (S : InformationStructure B Sig)
    [Finite (B.TypeProfile × B.ActionProfile)]
    [Finite ((S.inducedBayesianGame).TypeProfile)]
    {ρ : (S.inducedBayesianGame).BProfile}
    (hN : S.inducedBayesianGame.BayesNash ρ) :
    B.BayesCorrelatedEq (S.outcomeLaw ρ) := by
  refine ⟨S.outcomeLaw_bayesPlausible ρ, ?_⟩
  intro who dev
  rw [S.recommendedEU_outcomeLaw ρ who]
  rw [S.deviatingEU_outcomeLaw ρ who dev]
  exact (S.inducedBayesianGame.bayesNash_iff_exAnteEU ρ).1 hN who
    (fun τi => dev τi.1 (ρ who τi))

end InformationStructure

end Decidable

end BayesianGame

namespace KernelGame

variable {ι : Type} (G : KernelGame ι)

/-- View a complete-information kernel game as a Bayesian game with singleton
type spaces and the same action spaces. -/
noncomputable def toCompleteInfoBayesianGame : BayesianGame ι where
  Θ := fun _ => Unit
  Act := G.Strategy
  prior := PMF.pure (fun _ => ())
  utility := fun _ a i => G.eu a i

/-- Embed a base-game action law as a complete-information recommendation law. -/
noncomputable def completeInfoRecommendationLaw
    (μ : PMF (Profile G)) :
    (G.toCompleteInfoBayesianGame).RecommendationLaw :=
  μ.map fun a => ((fun _ => ()), a)

theorem completeInfoRecommendationLaw_bayesPlausible
    (μ : PMF (Profile G)) :
    (G.toCompleteInfoBayesianGame).BayesPlausible
      (G.completeInfoRecommendationLaw μ) := by
  unfold BayesianGame.BayesPlausible completeInfoRecommendationLaw
  unfold SignalStructure.HasPriorMarginal toCompleteInfoBayesianGame
  rw [PMF.map_comp]
  change PMF.map (Function.const (Profile G) (fun _ : ι => ())) μ =
    PMF.pure (fun _ : ι => ())
  rw [PMF.map_const]

theorem completeInfoRecommendationLaw_actionMarginal
    (μ : PMF (Profile G)) :
    PMF.map Prod.snd (G.completeInfoRecommendationLaw μ) = μ := by
  unfold completeInfoRecommendationLaw
  rw [PMF.map_comp]
  change PMF.map id μ = μ
  rw [PMF.map_id]

theorem completeInfo_recommendedEU_eq_correlatedEu
    [Finite (Profile G)] [Finite G.Outcome]
    (ψ : (G.toCompleteInfoBayesianGame).RecommendationLaw) (who : ι) :
    (G.toCompleteInfoBayesianGame).recommendedEU ψ who =
      G.correlatedEu (PMF.map Prod.snd ψ) who := by
  rw [G.correlatedEu_eq_expect_eu]
  unfold BayesianGame.recommendedEU toCompleteInfoBayesianGame
  rw [Math.Probability.expect_map_fintype_target]

section Decidable

variable [DecidableEq ι]

theorem completeInfo_deviatingEU_eq_correlatedEu_deviation
    [Finite (Profile G)] [Finite G.Outcome]
    (ψ : (G.toCompleteInfoBayesianGame).RecommendationLaw)
    (who : ι)
    (dev : (G.toCompleteInfoBayesianGame).ObedienceDeviation who) :
    (G.toCompleteInfoBayesianGame).deviatingEU ψ who dev =
      G.correlatedEu
        (G.unilateralDeviationDistribution (PMF.map Prod.snd ψ) who
          (fun s => dev () s)) who := by
  rw [G.correlatedEu_eq_expect_eu]
  unfold BayesianGame.deviatingEU BayesianGame.applyObedienceDeviation
  unfold toCompleteInfoBayesianGame KernelGame.unilateralDeviationDistribution
  unfold KernelGame.deviationDistribution KernelGame.unilateralDeviation
  rw [Math.Probability.expect_bind]
  simp only [Math.Probability.expect_pure]
  rw [Math.Probability.expect_map_fintype_target]

/-- Any complete-information BCE projects to a correlated equilibrium of the
base game. -/
theorem BayesCorrelatedEq.to_completeInfo_correlatedEq
    [Finite (Profile G)] [Finite G.Outcome]
    {ψ : (G.toCompleteInfoBayesianGame).RecommendationLaw}
    (hBCE : (G.toCompleteInfoBayesianGame).BayesCorrelatedEq ψ) :
    G.IsCorrelatedEq (PMF.map Prod.snd ψ) := by
  intro who dev
  have h := hBCE.2 who (fun _ s => dev s)
  rw [G.completeInfo_recommendedEU_eq_correlatedEu ψ who] at h
  rw [G.completeInfo_deviatingEU_eq_correlatedEu_deviation ψ who (fun _ s => dev s)] at h
  exact h

/-- Any correlated equilibrium of a complete-information base game embeds as a
BCE of the singleton-type Bayesian game. -/
theorem IsCorrelatedEq.completeInfo_bayesCorrelatedEq
    [Finite (Profile G)] [Finite G.Outcome]
    {μ : PMF (Profile G)} (hCE : G.IsCorrelatedEq μ) :
    (G.toCompleteInfoBayesianGame).BayesCorrelatedEq
      (G.completeInfoRecommendationLaw μ) := by
  refine ⟨G.completeInfoRecommendationLaw_bayesPlausible μ, ?_⟩
  intro who dev
  rw [G.completeInfo_recommendedEU_eq_correlatedEu
    (G.completeInfoRecommendationLaw μ) who]
  rw [G.completeInfo_deviatingEU_eq_correlatedEu_deviation
    (G.completeInfoRecommendationLaw μ) who dev]
  have hm := G.completeInfoRecommendationLaw_actionMarginal μ
  have hleft :
      G.correlatedEu (PMF.map Prod.snd (G.completeInfoRecommendationLaw μ)) who =
        G.correlatedEu μ who :=
    congrArg (fun ν => G.correlatedEu ν who) hm
  have hright :
      G.correlatedEu
          (G.unilateralDeviationDistribution
            (PMF.map Prod.snd (G.completeInfoRecommendationLaw μ)) who
            (fun s => dev () s)) who =
        G.correlatedEu
          (G.unilateralDeviationDistribution μ who (fun s => dev () s)) who :=
    congrArg
      (fun ν => G.correlatedEu
        (G.unilateralDeviationDistribution ν who (fun s => dev () s)) who) hm
  rw [hleft, hright]
  exact hCE who (fun s => dev () s)

end Decidable

end KernelGame

end GameTheory
