/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameMorphism
import GameTheory.Concepts.Correlation.CorrelatedNashMixed

/-!
# GameTheory.Concepts.Correlation.GameMorphism

Correlated- and coarse-correlated-equilibrium corollaries for game morphisms,
completing the solution-concept family already covered for Nash and dominance
in `GameTheory.Concepts.Foundations.GameMorphism`.

Provides:
- `Morphism.realizeLaw` -- push a profile-law through a morphism's strategy map
- `Morphism.correlatedEu_preserved_of_bounded` -- correlated EU is preserved
  along a realized profile-law, under bounded utility
- `EUGameIsomorphism.correlatedEq_iff` -- correlated equilibrium is invariant
  across a bijective, EU-preserving relabeling, under bounded utility
- `EUGameIsomorphism.coarseCorrelatedEq_iff` -- likewise for coarse correlated
  equilibrium

Unlike Nash and dominance, which are stated directly in terms of `eu` and so
transfer along an `EUGameIsomorphism` with no further hypotheses, correlated
and coarse correlated equilibrium are stated in terms of `correlatedEu`
(an expectation over a profile *law*, not a single profile). Relating
`correlatedEu` back to `eu` requires the same bounded-utility hypothesis
`correlatedEu_eq_expect_eu_of_bounded` already needs, so the corollaries here
carry that hypothesis even though `eu_preserved` itself does not. -/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- Push a profile-law through a morphism's per-player strategy map. -/
noncomputable def Morphism.realizeLaw {G H : KernelGame ι} (f : Morphism G H)
    (μ : PMF (Profile G)) : PMF (Profile H) :=
  PMF.map (fun σ i => f.stratMap i (σ i)) μ

omit [DecidableEq ι] in
/-- Correlated EU is preserved along a realized profile-law, under bounded
utility. The semantic content is already `Morphism.eu_preserved_of_bounded`;
boundedness only justifies reading correlated EU as an expectation of `eu`. -/
theorem Morphism.correlatedEu_preserved_of_bounded {G H : KernelGame ι}
    (f : Morphism G H)
    {C_G C_H : ι → ℝ}
    (hbdG : ∀ who ω, |G.utility ω who| ≤ C_G who)
    (hbdH : ∀ who ω, |H.utility ω who| ≤ C_H who)
    (μ : PMF (Profile G)) (who : ι) :
    H.correlatedEu (f.realizeLaw μ) who = G.correlatedEu μ who := by
  rw [Morphism.realizeLaw, correlatedEu_eq_expect_eu_of_bounded _ who (hbdH who), expect_map,
    correlatedEu_eq_expect_eu_of_bounded μ who (hbdG who)]
  exact congrArg (expect μ) (funext fun σ => f.eu_preserved_of_bounded hbdG hbdH σ who)

namespace EUGameIsomorphism

variable {G H : KernelGame ι}

/-- Realize a profile-law of `G` as a profile-law of `H` through the
isomorphism's per-player bijection. -/
noncomputable def realize (e : EUGameIsomorphism G H) : PMF (Profile G) → PMF (Profile H) :=
  fun μ => PMF.map (fun σ i => e.stratEquiv i (σ i)) μ

omit [DecidableEq ι] in
theorem realize_eq_toMorphism_realizeLaw (e : EUGameIsomorphism G H)
    (μ : PMF (Profile G)) :
    e.realize μ = e.toGameIsomorphism.toMorphism.realizeLaw μ := rfl

/-- Pushing a unilateral (recommendation-dependent) deviation of the realized
profile-law backtranslates exactly to the corresponding source-side deviation,
via the isomorphism's per-player bijection. -/
private theorem unilateralDeviationDistribution_realize (e : EUGameIsomorphism G H)
    (μ : PMF (Profile G)) (who : ι) (dH : H.Strategy who → H.Strategy who) :
    H.unilateralDeviationDistribution (e.realize μ) who dH =
      e.realize
        (G.unilateralDeviationDistribution μ who
          ((e.stratEquiv who).symm ∘ dH ∘ e.stratEquiv who)) := by
  unfold unilateralDeviationDistribution deviationDistribution unilateralDeviation realize
  rw [PMF.bind_map, PMF.map_bind]
  refine congrArg μ.bind (funext fun σ => ?_)
  simp only [Function.comp_apply, PMF.pure_map]
  congr 1
  funext i
  rcases eq_or_ne i who with rfl | hne
  · simp
  · simp [Function.update_of_ne hne]

/-- Pushing a constant deviation of the realized profile-law backtranslates
exactly to the corresponding source-side constant deviation. -/
private theorem constantDeviationDistribution_realize (e : EUGameIsomorphism G H)
    (μ : PMF (Profile G)) (who : ι) (s'' : H.Strategy who) :
    H.constantDeviationDistribution (e.realize μ) who s'' =
      e.realize
        (G.constantDeviationDistribution μ who ((e.stratEquiv who).symm s'')) := by
  unfold constantDeviationDistribution deviationDistribution constantDeviation realize
  rw [PMF.bind_map, PMF.map_bind]
  refine congrArg μ.bind (funext fun σ => ?_)
  simp only [Function.comp_apply, PMF.pure_map]
  congr 1
  funext i
  rcases eq_or_ne i who with rfl | hne
  · simp
  · simp [Function.update_of_ne hne]

/-- Correlated equilibrium is invariant across a bijective, EU-preserving
relabeling, under bounded utility on both games. -/
theorem correlatedEq_iff (e : EUGameIsomorphism G H)
    {C_G C_H : ι → ℝ}
    (hbdG : ∀ who ω, |G.utility ω who| ≤ C_G who)
    (hbdH : ∀ who ω, |H.utility ω who| ≤ C_H who)
    (μ : PMF (Profile G)) :
    G.IsCorrelatedEq μ ↔ H.IsCorrelatedEq (e.realize μ) := by
  have hbase : ∀ who, H.correlatedEu (e.realize μ) who = G.correlatedEu μ who := by
    intro who
    rw [realize_eq_toMorphism_realizeLaw]
    exact e.toGameIsomorphism.toMorphism.correlatedEu_preserved_of_bounded hbdG hbdH μ who
  have hdevEu : ∀ (who : ι) (dG : G.Strategy who → G.Strategy who),
      H.correlatedEu (e.realize (G.unilateralDeviationDistribution μ who dG)) who =
        G.correlatedEu (G.unilateralDeviationDistribution μ who dG) who := by
    intro who dG
    rw [realize_eq_toMorphism_realizeLaw]
    exact e.toGameIsomorphism.toMorphism.correlatedEu_preserved_of_bounded hbdG hbdH
      (G.unilateralDeviationDistribution μ who dG) who
  constructor
  · intro hCE who dH
    rw [hbase who, unilateralDeviationDistribution_realize,
      hdevEu who ((e.stratEquiv who).symm ∘ dH ∘ e.stratEquiv who)]
    exact hCE who _
  · intro hCE who dG
    have hkey := hCE who (e.stratEquiv who ∘ dG ∘ (e.stratEquiv who).symm)
    rw [hbase who] at hkey
    rw [unilateralDeviationDistribution_realize] at hkey
    have hdG : (e.stratEquiv who).symm ∘ (e.stratEquiv who ∘ dG ∘ (e.stratEquiv who).symm) ∘
        e.stratEquiv who = dG := by
      funext s; simp
    rw [hdG, hdevEu who dG] at hkey
    exact hkey

/-- Coarse correlated equilibrium is invariant across a bijective,
EU-preserving relabeling, under bounded utility on both games. -/
theorem coarseCorrelatedEq_iff (e : EUGameIsomorphism G H)
    {C_G C_H : ι → ℝ}
    (hbdG : ∀ who ω, |G.utility ω who| ≤ C_G who)
    (hbdH : ∀ who ω, |H.utility ω who| ≤ C_H who)
    (μ : PMF (Profile G)) :
    G.IsCoarseCorrelatedEq μ ↔ H.IsCoarseCorrelatedEq (e.realize μ) := by
  have hbase : ∀ who, H.correlatedEu (e.realize μ) who = G.correlatedEu μ who := by
    intro who
    rw [realize_eq_toMorphism_realizeLaw]
    exact e.toGameIsomorphism.toMorphism.correlatedEu_preserved_of_bounded hbdG hbdH μ who
  have hdevEu : ∀ (who : ι) (s' : G.Strategy who),
      H.correlatedEu (e.realize (G.constantDeviationDistribution μ who s')) who =
        G.correlatedEu (G.constantDeviationDistribution μ who s') who := by
    intro who s'
    rw [realize_eq_toMorphism_realizeLaw]
    exact e.toGameIsomorphism.toMorphism.correlatedEu_preserved_of_bounded hbdG hbdH
      (G.constantDeviationDistribution μ who s') who
  constructor
  · intro hCCE who s''
    rw [hbase who, constantDeviationDistribution_realize, hdevEu who ((e.stratEquiv who).symm s'')]
    exact hCCE who _
  · intro hCCE who s'
    have hkey := hCCE who (e.stratEquiv who s')
    rw [hbase who] at hkey
    rw [constantDeviationDistribution_realize] at hkey
    simp only [Equiv.symm_apply_apply] at hkey
    rw [hdevEu who s'] at hkey
    exact hkey

end EUGameIsomorphism

end KernelGame

end GameTheory
