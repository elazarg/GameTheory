/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.KernelGame

/-!
# Sequential Assessments

Generic assessment predicates for dynamic games.

This file is deliberately language-independent. A language-specific game
provides:

* player-indexed strategy spaces,
* an outcome type,
* a history type,
* player-indexed information states,
* probabilities of histories under a strategy profile,
* the relation saying which histories reach which information state,
* continuation outcome distributions from beliefs over histories.

From those ingredients we derive belief support, on-path Bayes consistency, and
sequential rationality. EFG/PBE definitions are then thin adapters over this
generic layer.
-/

namespace GameTheory

open Math.Probability

/-- Language-independent form of the data needed to state sequential
assessment predicates. -/
structure AssessmentForm (ι : Type) where
  Strategy : ι → Type
  Outcome : Type
  History : Type
  Info : ι → Type
  historyProb : (∀ i, Strategy i) → History → ENNReal
  reachesInfo : ∀ {i : ι}, Info i → History → Prop
  continuationOutcome : PMF History → (∀ i, Strategy i) → PMF Outcome

namespace AssessmentForm

variable {ι : Type} (F : AssessmentForm ι)

/-- Strategy profile for an assessment form. -/
abbrev Profile := ∀ i, F.Strategy i

/-- Strategy + belief system. -/
structure Assessment where
  strategy : F.Profile
  beliefs : ∀ {i : ι}, F.Info i → PMF F.History

/-- Total probability mass of histories that reach an information state. -/
noncomputable def infoMass (σ : F.Profile) {i : ι} (I : F.Info i) : ENNReal :=
  by
    classical
    exact ∑' h : F.History, if F.reachesInfo I h then F.historyProb σ h else 0

/-- An information state is on path under `σ` if histories reaching it have
nonzero total probability. -/
def IsOnPath (σ : F.Profile) {i : ι} (I : F.Info i) : Prop :=
  F.infoMass σ I ≠ 0

/-- A belief at an information state assigns mass only to histories that reach
that information state. -/
def BeliefSupportedAt (A : F.Assessment) {i : ι} (I : F.Info i) : Prop :=
  ∀ h : F.History, A.beliefs I h ≠ 0 → F.reachesInfo I h

/-- Every belief in the assessment is supported on its information state. -/
def BeliefsSupported (A : F.Assessment) : Prop :=
  ∀ (i : ι) (I : F.Info i), F.BeliefSupportedAt A I

/-- Pointwise Bayes rule at an information state. The right-hand side is only
meaningful on path; callers normally guard this with `IsOnPath`. -/
noncomputable def BayesRuleAt (A : F.Assessment) {i : ι} (I : F.Info i) : Prop :=
  by
    classical
    exact ∀ h : F.History,
      A.beliefs I h =
        if F.reachesInfo I h then F.historyProb A.strategy h / F.infoMass A.strategy I else 0

/-- Bayes consistency at all on-path information states. -/
noncomputable def BayesConsistentOnPath (A : F.Assessment) : Prop :=
  ∀ (i : ι) (I : F.Info i), F.IsOnPath A.strategy I → F.BayesRuleAt A I

/-- Weak consistency for PBE-style assessments: support everywhere and Bayes'
rule on path. Stronger sequential-equilibrium consistency can replace this
predicate without changing sequential rationality. -/
noncomputable def WeaklyConsistentAssessment (A : F.Assessment) : Prop :=
  F.BeliefsSupported A ∧ F.BayesConsistentOnPath A

section StrategicDeviation

variable [DecidableEq ι]

/-- Preference-parametric sequential rationality at one information state.

The deviation set is full replacement of the active player's strategy. In a
language where strategies are behavioral policies, only future choices in the
sampled continuation can affect `continuationOutcome`; irrelevant coordinates
are semantically ignored. -/
noncomputable def SequentiallyRationalAtFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (A : F.Assessment) {i : ι} (I : F.Info i) : Prop :=
  ∀ τ : F.Strategy i,
    pref i
      (F.continuationOutcome (A.beliefs I) A.strategy)
      (F.continuationOutcome (A.beliefs I) (Function.update A.strategy i τ))

/-- Preference-parametric sequential rationality at every information state. -/
noncomputable def SequentiallyRationalFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (A : F.Assessment) : Prop :=
  ∀ (i : ι) (I : F.Info i), F.SequentiallyRationalAtFor pref A I

/-- Concrete perfect-Bayesian equilibrium for a supplied preference relation. -/
noncomputable def IsPerfectBayesianEqFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (A : F.Assessment) : Prop :=
  F.SequentiallyRationalFor pref A ∧ F.WeaklyConsistentAssessment A

/-- Sequential-equilibrium shape with an explicit consistency predicate. This is
the extension point for stronger limit-consistency notions. -/
noncomputable def IsSequentialEqWithConsistencyFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (Consistent : F.Assessment → Prop)
    (A : F.Assessment) : Prop :=
  F.SequentiallyRationalFor pref A ∧ Consistent A

/-- The on-path/Bayes concrete specialization. Full Kreps-Wilson sequential
equilibrium can be obtained by replacing `WeaklyConsistentAssessment` above with
a stronger limit-consistency predicate. -/
noncomputable def IsSequentialEqFor
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (A : F.Assessment) : Prop :=
  F.IsSequentialEqWithConsistencyFor pref F.WeaklyConsistentAssessment A

/-- Expected-utility preference induced by a utility function. -/
noncomputable def euOutcomePref (utility : F.Outcome → Payoff ι) :
    ι → PMF F.Outcome → PMF F.Outcome → Prop :=
  fun who d₁ d₂ =>
    expect d₁ (fun ω => utility ω who) ≥ expect d₂ (fun ω => utility ω who)

/-- EU-specialized perfect-Bayesian equilibrium. -/
noncomputable def IsPerfectBayesianEq
    (utility : F.Outcome → Payoff ι) (A : F.Assessment) : Prop :=
  F.IsPerfectBayesianEqFor (F.euOutcomePref utility) A

/-- EU-specialized sequential-equilibrium predicate using weak consistency. -/
noncomputable def IsSequentialEq
    (utility : F.Outcome → Payoff ι) (A : F.Assessment) : Prop :=
  F.IsSequentialEqFor (F.euOutcomePref utility) A

theorem isPerfectBayesianEqFor_iff
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (A : F.Assessment) :
    F.IsPerfectBayesianEqFor pref A ↔
      F.SequentiallyRationalFor pref A ∧ F.WeaklyConsistentAssessment A := by
  rfl

theorem isSequentialEqFor_iff
    (pref : ι → PMF F.Outcome → PMF F.Outcome → Prop)
    (A : F.Assessment) :
    F.IsSequentialEqFor pref A ↔
      F.SequentiallyRationalFor pref A ∧ F.WeaklyConsistentAssessment A := by
  rfl

theorem IsPerfectBayesianEqFor.sequentiallyRational
    {pref : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    {A : F.Assessment} (h : F.IsPerfectBayesianEqFor pref A) :
    F.SequentiallyRationalFor pref A :=
  h.1

theorem IsPerfectBayesianEqFor.weaklyConsistent
    {pref : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    {A : F.Assessment} (h : F.IsPerfectBayesianEqFor pref A) :
    F.WeaklyConsistentAssessment A :=
  h.2

theorem IsPerfectBayesianEqFor.beliefsSupported
    {pref : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    {A : F.Assessment} (h : F.IsPerfectBayesianEqFor pref A) :
    F.BeliefsSupported A :=
  h.2.1

theorem IsPerfectBayesianEqFor.bayesConsistentOnPath
    {pref : ι → PMF F.Outcome → PMF F.Outcome → Prop}
    {A : F.Assessment} (h : F.IsPerfectBayesianEqFor pref A) :
    F.BayesConsistentOnPath A :=
  h.2.2

end StrategicDeviation

end AssessmentForm

end GameTheory
