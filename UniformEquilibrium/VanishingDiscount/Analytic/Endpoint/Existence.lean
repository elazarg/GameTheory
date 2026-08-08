/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.AnalyticBellmanExistence
import UniformEquilibrium.VanishingDiscount.Analytic.Endpoint.Atlas

/-!
# Initial analytic endpoint existence

This file connects the unconditional analytic Bellman-germ construction to
the first endpoint classification.  It deliberately stops at an honest
`AnalyticEndpointAtlasLeaf`: no nonsemantic leaf is promoted to an adaptive
certificate without its missing strategic reconstruction.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type} (G : StochasticGame ι)
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ who, Fintype (G.Act who)]
  [∀ who, DecidableEq (G.Act who)]
  [∀ who, Nonempty (G.Act who)]

/-- Every finite stochastic game has one analytic Bellman germ whose first
hierarchy response is classified at every admissible endpoint-harmonic span. -/
theorem exists_analyticBellmanGermWithFirstHierarchyResponses :
    ∃ germ : G.AnalyticBellmanGerm,
      ∀ span : germ.EndpointHarmonicJetSpan,
        Nonempty (germ.FirstHierarchyResponse span) := by
  obtain ⟨germ⟩ := analyticBellmanGermExistence.forGame G
  exact ⟨germ, germ.exists_firstHierarchyResponse⟩

/-- In particular, every finite stochastic game has a first hierarchy
response from the empty processed harmonic span. -/
theorem exists_initialAnalyticFirstHierarchyResponse :
    ∃ germ : G.AnalyticBellmanGerm,
      Nonempty
        (germ.FirstHierarchyResponse
          (AnalyticBellmanGerm.EndpointHarmonicJetSpan.empty germ)) := by
  obtain ⟨germ, responses⟩ :=
    G.exists_analyticBellmanGermWithFirstHierarchyResponses
  exact
    ⟨germ,
      responses
        (AnalyticBellmanGerm.EndpointHarmonicJetSpan.empty germ)⟩

/-- Every finite stochastic game has one analytic Bellman germ whose endpoint
classification is available at every admissible endpoint-harmonic span and
every public entry state.

This is an exhaustive classification only.  It does not resolve any
nonsemantic leaf. -/
theorem exists_analyticBellmanGermWithEndpointLeaves :
    ∃ germ : G.AnalyticBellmanGerm,
      ∀ (span : germ.EndpointHarmonicJetSpan) (entry : G.State),
        Nonempty (germ.AnalyticEndpointAtlasLeaf span entry) := by
  obtain ⟨germ, responses⟩ :=
    G.exists_analyticBellmanGermWithFirstHierarchyResponses
  refine ⟨germ, ?_⟩
  intro span entry
  exact
    (responses span).elim fun response =>
      AnalyticBellmanGerm.AnalyticEndpointAtlasLeaf.ofFirstHierarchyResponse
        (entry := entry) response

/-- Every finite stochastic game reaches one honestly labelled initial
analytic endpoint leaf at a prescribed public entry state.

The conclusion is a classification result, not a strategic closure: every
nonsemantic leaf constructor still carries an explicit reconstruction
obligation. -/
theorem exists_initialAnalyticEndpointLeaf (entry : G.State) :
    ∃ germ : G.AnalyticBellmanGerm,
      Nonempty
        (germ.AnalyticEndpointAtlasLeaf
          (AnalyticBellmanGerm.EndpointHarmonicJetSpan.empty germ)
          entry) := by
  obtain ⟨germ, leaves⟩ :=
    G.exists_analyticBellmanGermWithEndpointLeaves
  exact
    ⟨germ,
      leaves
        (AnalyticBellmanGerm.EndpointHarmonicJetSpan.empty germ)
        entry⟩

end StochasticGame
end GameTheory
