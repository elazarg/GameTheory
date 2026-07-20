/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameMorphism
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import GameTheory.Concepts.Foundations.StrategicEquivalence

/-!
# GameTheory.Concepts.Correlation.GameMorphism

Correlated- and coarse-correlated-equilibrium corollaries for game morphisms,
completing the solution-concept family already covered for Nash and dominance
in `GameTheory.Concepts.Foundations.GameMorphism`.

Provides:
- `Morphism.realizeLaw` -- push a profile-law through a morphism's strategy map
- `Morphism.correlatedEu_preserved_of_bounded` -- correlated EU is preserved
  along a realized profile-law, under bounded utility
- `EUGameIsomorphism.toUtilityStrategicEquivalence` -- the utility-law
  strategic equivalence induced by a game isomorphism
- `EUGameIsomorphism.correlatedEq_iff` -- correlated equilibrium is invariant
  across a bijective, utility-distribution-preserving relabeling
- `EUGameIsomorphism.coarseCorrelatedEq_iff` -- likewise for coarse correlated
  equilibrium

The equilibrium invariance theorems are instances of the generic transport
corner: an isomorphism induces a `GameForm.StrategicEquivalence` between the
two utility-law views, and CE/CCE transfer through its recommendation/constant
deviation transports. The standalone `correlatedEu` lemma retains its bounded
form because it explicitly factors through profile-level expected utilities. -/

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

/-- The utility-law strategic equivalence induced by a game isomorphism.

Pointwise law preservation is the per-player projection of the isomorphism's
joint utility-distribution preservation. This is the common transport object
from which the CE and CCE invariance theorems below are derived. -/
noncomputable def toUtilityStrategicEquivalence (e : EUGameIsomorphism G H) :
    GameForm.StrategicEquivalence G.toGameForm H.toGameForm ℝ where
  viewG := G.utilityView
  viewH := H.utilityView
  equivStrategy := e.stratEquiv
  law_eq := by
    intro σ who
    change Math.ProbabilityMassFunction.pushforward (G.outcomeKernel σ)
        (fun o => G.utility o who) =
      Math.ProbabilityMassFunction.pushforward
        (H.outcomeKernel (fun j => e.stratEquiv j (σ j)))
        (fun o => H.utility o who)
    rw [← Math.ProbabilityMassFunction.bind_pure_eq_pushforward,
      ← Math.ProbabilityMassFunction.bind_pure_eq_pushforward]
    exact (e.toGameIsomorphism.udistPlayer_preserved σ who).symm

/-- Correlated equilibrium is invariant across a bijective,
utility-distribution-preserving relabeling.

This is the correlated-deviation-family instance of generic strategic-
equivalence transport. -/
theorem correlatedEq_iff (e : EUGameIsomorphism G H) (μ : PMF (Profile G)) :
    G.IsCorrelatedEq μ ↔ H.IsCorrelatedEq (e.realize μ) := by
  rw [G.IsCorrelatedEq_iff_IsCorrelatedEqFor_eu,
    H.IsCorrelatedEq_iff_IsCorrelatedEqFor_eu]
  rw [← observedPref_utilityView G, ← observedPref_utilityView H]
  change G.toGameForm.IsCorrelatedEqFor
      (GameForm.observedPref G.utilityView (fun _ => expectationPref)) μ ↔
    H.toGameForm.IsCorrelatedEqFor
      (GameForm.observedPref H.utilityView (fun _ => expectationPref)) (e.realize μ)
  let E := e.toUtilityStrategicEquivalence
  have hmap : PMF.map E.realize μ = e.realize μ := by
    congr 1
  have hbackmap : PMF.map E.symm.realize (e.realize μ) = μ := by
    rw [← hmap, PMF.map_comp]
    rw [show E.symm.realize ∘ E.realize = id from ?_, PMF.map_id]
    funext σ
    exact E.realizeSymm_realize σ
  constructor
  · intro h
    have h' : G.toGameForm.IsCorrelatedEqFor
        (GameForm.observedPref E.viewG (fun _ => expectationPref)) μ := by
      simpa [E, toUtilityStrategicEquivalence] using h
    have ht := E.target_correlatedEq μ h'
    rw [hmap] at ht
    simpa [E, toUtilityStrategicEquivalence] using ht
  · intro h
    have h' : H.toGameForm.IsCorrelatedEqFor
        (GameForm.observedPref E.symm.viewG (fun _ => expectationPref))
        (e.realize μ) := by
      simpa [E, toUtilityStrategicEquivalence,
        GameForm.StrategicEquivalence.symm] using h
    have hback := E.symm.target_correlatedEq (e.realize μ) h'
    rw [hbackmap] at hback
    simpa [E, toUtilityStrategicEquivalence,
      GameForm.StrategicEquivalence.symm] using hback

/-- Coarse correlated equilibrium is invariant across a bijective,
utility-distribution-preserving relabeling.

This is the constant-deviation-family instance of generic strategic-
equivalence transport. -/
theorem coarseCorrelatedEq_iff (e : EUGameIsomorphism G H) (μ : PMF (Profile G)) :
    G.IsCoarseCorrelatedEq μ ↔ H.IsCoarseCorrelatedEq (e.realize μ) := by
  rw [G.IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu,
    H.IsCoarseCorrelatedEq_iff_IsCoarseCorrelatedEqFor_eu]
  rw [← observedPref_utilityView G, ← observedPref_utilityView H]
  change G.toGameForm.IsCoarseCorrelatedEqFor
      (GameForm.observedPref G.utilityView (fun _ => expectationPref)) μ ↔
    H.toGameForm.IsCoarseCorrelatedEqFor
      (GameForm.observedPref H.utilityView (fun _ => expectationPref)) (e.realize μ)
  let E := e.toUtilityStrategicEquivalence
  have hmap : PMF.map E.realize μ = e.realize μ := by
    congr 1
  have hbackmap : PMF.map E.symm.realize (e.realize μ) = μ := by
    rw [← hmap, PMF.map_comp]
    rw [show E.symm.realize ∘ E.realize = id from ?_, PMF.map_id]
    funext σ
    exact E.realizeSymm_realize σ
  constructor
  · intro h
    have h' : G.toGameForm.IsCoarseCorrelatedEqFor
        (GameForm.observedPref E.viewG (fun _ => expectationPref)) μ := by
      simpa [E, toUtilityStrategicEquivalence] using h
    have ht := E.target_coarseCorrelatedEq μ h'
    rw [hmap] at ht
    simpa [E, toUtilityStrategicEquivalence] using ht
  · intro h
    have h' : H.toGameForm.IsCoarseCorrelatedEqFor
        (GameForm.observedPref E.symm.viewG (fun _ => expectationPref))
        (e.realize μ) := by
      simpa [E, toUtilityStrategicEquivalence,
        GameForm.StrategicEquivalence.symm] using h
    have hback := E.symm.target_coarseCorrelatedEq (e.realize μ) h'
    rw [hbackmap] at hback
    simpa [E, toUtilityStrategicEquivalence,
      GameForm.StrategicEquivalence.symm] using hback

end EUGameIsomorphism

end KernelGame

end GameTheory
