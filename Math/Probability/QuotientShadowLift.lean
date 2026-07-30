/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.PredictableCoreShadow

/-!
# Causal lifting of finite quotient shadows

A legal shadow may be constructed on a finite quotient of the controlled
state rather than on the original state space.  This file gives the exact
lifting step needed to return to the original process.

Given a law `q` on `S`, a quotient map `χ : S → C`, and a joint law on
`C × R` whose first marginal is `q.map χ`, the heterogeneous fiber lift:

* has first marginal exactly `q`;
* has the same second marginal as the quotient joint law; and
* maps back to the original joint law under `(s, r) ↦ (χ s, r)`.

The construction is then iterated on the finite history tree.  If the
controlled kernels commute with the quotient and the supplied quotient
joint step has the prescribed quotient first marginal, the lifted process
has both the exact controlled full-state history law and the exact supplied
quotient-pair history law.

This is a sufficiency theorem for a supplied finite quotient.  It does not
construct a quotient, prove strong lumpability of a game kernel, or show that
the quotient shadow is strategically legal.
-/

set_option autoImplicit false

noncomputable section

namespace Math
namespace Probability

variable {S C R : Type*}

/-- Mapping a full-state/core pair to its quotient-state/core pair. -/
def quotientPairMap (χ : S → C) : S × R → C × R :=
  fun pair => (χ pair.1, pair.2)

@[simp]
theorem quotientPairMap_apply (χ : S → C) (pair : S × R) :
    quotientPairMap χ pair = (χ pair.1, pair.2) :=
  rfl

/-- Two maps that agree on the support of a PMF have the same pushforward. -/
theorem pmf_map_eq_of_eq_on_support
    (μ : PMF S) (f g : S → C)
    (hfg : ∀ s, s ∈ μ.support → f s = g s) :
    μ.map f = μ.map g := by
  rw [← PMF.bind_pure_comp f μ, ← PMF.bind_pure_comp g μ]
  apply ProbabilityMassFunction.bind_congr_on_support
  intro s hs
  simpa only [Function.comp_apply] using
    congrArg PMF.pure (hfg s hs)

/-- Lift a joint law of `(χ s, r)` to a joint law of `(s, r)` by
disintegrating the full-state law over its quotient coordinate. -/
noncomputable def heterogeneousFiberLift
    [Finite S] [Finite C]
    (q : PMF S) (χ : S → C) (ξ : PMF (C × R)) : PMF (S × R) :=
  ξ.bind fun pair =>
    (ProbabilityMassFunction.condOn q χ pair.1).map
      fun state => (state, pair.2)

theorem heterogeneousFiberLift_map_fst
    [Finite S] [Finite C]
    (q : PMF S) (χ : S → C) (ξ : PMF (C × R))
    (hfst : ξ.map Prod.fst = q.map χ) :
    (heterogeneousFiberLift q χ ξ).map Prod.fst = q := by
  rw [heterogeneousFiberLift, PMF.map_bind]
  have hkernel (pair : C × R) :
      ((ProbabilityMassFunction.condOn q χ pair.1).map
          fun state => (state, pair.2)).map Prod.fst =
        ProbabilityMassFunction.condOn q χ pair.1 := by
    rw [PMF.map_comp]
    change
      (ProbabilityMassFunction.condOn q χ pair.1).map id =
        ProbabilityMassFunction.condOn q χ pair.1
    exact PMF.map_id _
  conv_lhs =>
    enter [2, pair]
    rw [hkernel pair]
  calc
    ξ.bind
          (fun pair =>
            ProbabilityMassFunction.condOn q χ pair.1) =
        (ξ.map Prod.fst).bind
          (fun cell =>
            ProbabilityMassFunction.condOn q χ cell) := by
      rw [PMF.bind_map]
      rfl
    _ =
        (q.map χ).bind
          (fun cell =>
            ProbabilityMassFunction.condOn q χ cell) := by
      rw [hfst]
    _ = q := by
      simpa [ProbabilityMassFunction.pushforward] using
        (ProbabilityMassFunction.bind_pushforward_condOn_pure q χ).symm

theorem heterogeneousFiberLift_map_snd
    [Finite S] [Finite C]
    (q : PMF S) (χ : S → C) (ξ : PMF (C × R)) (k : PMF R)
    (hsnd : ξ.map Prod.snd = k) :
    (heterogeneousFiberLift q χ ξ).map Prod.snd = k := by
  rw [heterogeneousFiberLift, PMF.map_bind]
  have hkernel (pair : C × R) :
      ((ProbabilityMassFunction.condOn q χ pair.1).map
          fun state => (state, pair.2)).map Prod.snd =
        PMF.pure pair.2 := by
    rw [PMF.map_comp]
    change
      (ProbabilityMassFunction.condOn q χ pair.1).map
          (Function.const S pair.2) =
        PMF.pure pair.2
    exact PMF.map_const _ _
  conv_lhs =>
    enter [2, pair]
    rw [hkernel pair]
  calc
    ξ.bind (fun pair => PMF.pure pair.2) =
        ξ.map Prod.snd := by
      exact PMF.bind_pure_comp Prod.snd ξ
    _ = k := hsnd

/-- The heterogeneous lift maps back to the complete quotient joint law,
not merely to its two marginals. -/
theorem heterogeneousFiberLift_map_quotientPair
    [Finite S] [Finite C]
    (q : PMF S) (χ : S → C) (ξ : PMF (C × R))
    (hfst : ξ.map Prod.fst = q.map χ) :
    (heterogeneousFiberLift q χ ξ).map (quotientPairMap χ) = ξ := by
  rw [heterogeneousFiberLift, PMF.map_bind]
  calc
    ξ.bind
          (fun pair =>
            ((ProbabilityMassFunction.condOn q χ pair.1).map
              fun state => (state, pair.2)).map
                (quotientPairMap χ)) =
        ξ.bind (fun pair => PMF.pure pair) := by
      apply ProbabilityMassFunction.bind_congr_on_support
      intro pair hpair
      rw [PMF.map_comp]
      have hcellSupport :
          pair.1 ∈ (q.map χ).support := by
        rw [← hfst, PMF.support_map]
        exact ⟨pair, hpair, rfl⟩
      have hcellNe : q.map χ pair.1 ≠ 0 := by
        change q.map χ pair.1 ≠ 0 at hcellSupport
        exact hcellSupport
      calc
        (ProbabilityMassFunction.condOn q χ pair.1).map
              (quotientPairMap χ ∘
                fun state => (state, pair.2)) =
            (ProbabilityMassFunction.condOn q χ pair.1).map
              (Function.const S pair) := by
          apply pmf_map_eq_of_eq_on_support
          intro state hstate
          rw [Function.comp_apply, quotientPairMap_apply]
          have hproject :=
            ProbabilityMassFunction.condOn_support_project
              q χ pair.1 hcellNe hstate
          exact Prod.ext hproject rfl
        _ = PMF.pure pair := by
          exact PMF.map_const _ _
    _ = ξ := PMF.bind_pure ξ

/-- Lift a supplied quotient-pair step predictably from the full joint
history. -/
noncomputable def quotientShadowLiftStep
    [Finite S] [Finite C]
    (χ : S → C)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (quotientStep : ∀ n, (Fin n → C × R) → PMF (C × R)) :
    ∀ n, (Fin n → S × R) → PMF (S × R) :=
  fun n history =>
    heterogeneousFiberLift
      (controlled n (mapFiniteHistory Prod.fst history))
      χ
      (quotientStep n
        (mapFiniteHistory (quotientPairMap χ) history))

theorem mapFiniteHistory_quotientPair_fst
    (χ : S → C) {n : ℕ} (history : Fin n → S × R) :
    mapFiniteHistory Prod.fst
        (mapFiniteHistory (quotientPairMap χ) history) =
      mapFiniteHistory χ
        (mapFiniteHistory Prod.fst history) := by
  rfl

theorem quotientShadowLiftStep_map_fst
    [Finite S] [Finite C]
    (χ : S → C)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (quotientControlled : ∀ n, (Fin n → C) → PMF C)
    (quotientStep : ∀ n, (Fin n → C × R) → PMF (C × R))
    (controlled_quotient :
      ∀ n history,
        (controlled n history).map χ =
          quotientControlled n (mapFiniteHistory χ history))
    (quotientStep_fst :
      ∀ n history,
        (quotientStep n history).map Prod.fst =
          quotientControlled n
            (mapFiniteHistory Prod.fst history))
    (n : ℕ) (history : Fin n → S × R) :
    (quotientShadowLiftStep χ controlled quotientStep n history).map
        Prod.fst =
      controlled n (mapFiniteHistory Prod.fst history) := by
  apply heterogeneousFiberLift_map_fst
  rw [quotientStep_fst,
    mapFiniteHistory_quotientPair_fst,
    controlled_quotient]

theorem quotientShadowLiftStep_map_quotientPair
    [Finite S] [Finite C]
    (χ : S → C)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (quotientControlled : ∀ n, (Fin n → C) → PMF C)
    (quotientStep : ∀ n, (Fin n → C × R) → PMF (C × R))
    (controlled_quotient :
      ∀ n history,
        (controlled n history).map χ =
          quotientControlled n (mapFiniteHistory χ history))
    (quotientStep_fst :
      ∀ n history,
        (quotientStep n history).map Prod.fst =
          quotientControlled n
            (mapFiniteHistory Prod.fst history))
    (n : ℕ) (history : Fin n → S × R) :
    (quotientShadowLiftStep χ controlled quotientStep n history).map
        (quotientPairMap χ) =
      quotientStep n
        (mapFiniteHistory (quotientPairMap χ) history) := by
  apply heterogeneousFiberLift_map_quotientPair
  rw [quotientStep_fst,
    mapFiniteHistory_quotientPair_fst,
    controlled_quotient]

/-- The lifted finite-history process has exactly the prescribed controlled
full-state marginal. -/
theorem adaptiveHistoryLaw_quotientShadowLift_map_fst
    [Finite S] [Finite C] [Finite R]
    (χ : S → C)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (quotientControlled : ∀ n, (Fin n → C) → PMF C)
    (quotientStep : ∀ n, (Fin n → C × R) → PMF (C × R))
    (controlled_quotient :
      ∀ n history,
        (controlled n history).map χ =
          quotientControlled n (mapFiniteHistory χ history))
    (quotientStep_fst :
      ∀ n history,
        (quotientStep n history).map Prod.fst =
          quotientControlled n
            (mapFiniteHistory Prod.fst history))
    (T : ℕ) :
    (adaptiveHistoryLaw
        (quotientShadowLiftStep χ controlled quotientStep) T).map
        (mapFiniteHistory Prod.fst) =
      adaptiveHistoryLaw controlled T := by
  apply adaptiveHistoryLaw_map
  exact quotientShadowLiftStep_map_fst
    χ controlled quotientControlled quotientStep
    controlled_quotient quotientStep_fst

/-- The lifted process also has exactly the supplied quotient-pair history
law.  Consequently every public additive or terminal functional that factors
through the quotient has the same distribution under the supplied quotient
shadow and its full-state causal lift. -/
theorem adaptiveHistoryLaw_quotientShadowLift_map_quotientPair
    [Finite S] [Finite C] [Finite R]
    (χ : S → C)
    (controlled : ∀ n, (Fin n → S) → PMF S)
    (quotientControlled : ∀ n, (Fin n → C) → PMF C)
    (quotientStep : ∀ n, (Fin n → C × R) → PMF (C × R))
    (controlled_quotient :
      ∀ n history,
        (controlled n history).map χ =
          quotientControlled n (mapFiniteHistory χ history))
    (quotientStep_fst :
      ∀ n history,
        (quotientStep n history).map Prod.fst =
          quotientControlled n
            (mapFiniteHistory Prod.fst history))
    (T : ℕ) :
    (adaptiveHistoryLaw
        (quotientShadowLiftStep χ controlled quotientStep) T).map
        (mapFiniteHistory (quotientPairMap χ)) =
      adaptiveHistoryLaw quotientStep T := by
  apply adaptiveHistoryLaw_map
  exact quotientShadowLiftStep_map_quotientPair
    χ controlled quotientControlled quotientStep
    controlled_quotient quotientStep_fst

end Probability
end Math
