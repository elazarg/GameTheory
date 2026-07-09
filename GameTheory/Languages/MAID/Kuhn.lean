/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.PMFProduct
import GameTheory.Languages.Kuhn
import GameTheory.Languages.MAID.CompileObsFacts

/-!
# GameTheory.Languages.MAID.Kuhn

Native Kuhn theorem assembly for MAIDs via the compiled perfect-recall
`ObsModelCore` facts in `GameTheory.Languages.MAID.CompileObsFacts`.
-/

namespace GameTheory.Languages.MAID

open _root_.MAID
open GameTheory.Theorems

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

-- ============================================================================
-- B→M native theorem (Task 6)
-- ============================================================================

section NativeBToM

variable (S : Struct Player n) (sem : Sem S)

open Math.PMFProduct Math.ProbabilityMassFunction

/-- **Kuhn B→M (fully native MAID)**: under perfect recall, every behavioral
policy can be realized by a product mixed strategy with the same outcome
distribution via `frontierEval`.

Both LHS and RHS use native MAID types — no compiled model types in the statement.
The compiled model is used internally to construct the mixed strategy
via the core B→M theorem. -/
theorem kuhn_behavioral_to_mixed
    (hPR : S.PerfectRecall) (pol : Policy S) :
    ∃ μ : ∀ p, PMF (PureStrategy S p),
      frontierEval S sem pol =
        (pmfPi μ).bind (fun π => frontierEval S sem (pureToPolicy π)) := by
  -- 1. Lift native policy to compiled behavioral profile
  set β := liftBehavioralProfile S sem pol
  -- 2. Apply compiled B→M (NNISIR holds unconditionally)
  have hNR := noNontrivialInfoStateRepeat_compiledPR S sem
  have hbm := ObsModelCore.kuhn_behavioral_to_mixed hNR β n
  -- hbm : runDist n β = (behavioralToMixedJoint β).bind (runDistPure n)
  -- 3. Define native μ by descending the compiled mixed strategies
  set μ : ∀ p, PMF (PureStrategy S p) :=
    fun p => ((compiledPRObs S sem).behavioralToMixed β p).map
      (descendPureStrategy S sem)
  refine ⟨μ, ?_⟩
  -- 4. LHS: frontierEval pol = (runDist n β).bind extractTAssign  (adequacy)
  rw [← compiledPR_runDist_eq_frontierEval S sem hPR pol]
  -- 5. Apply hbm
  rw [hbm, PMF.bind_bind]
  -- 6. RHS: (pmfPi μ).bind (frontierEval ∘ pureToPolicy) via pure adequacy
  -- Connect pmfPi μ with pmfPi (behavioralToMixed β) via push
  have hpush : pmfPi μ =
      pushforward (pmfPi ((compiledPRObs S sem).behavioralToMixed β))
        (descendPureProfile S sem) := by
    exact (pmfPi_push_coordwise
      ((compiledPRObs S sem).behavioralToMixed β)
      (fun p => descendPureStrategy S sem (p := p))).symm
  rw [hpush]
  rw [pushforward]
  trans (pmfPi (ObsModelCore.behavioralToMixed β)).bind
      (fun π' => frontierEval S sem (pureToPolicy (descendPureProfile S sem π')))
  · unfold ObsModelCore.behavioralToMixedJoint
    apply bind_congr_on_support
    intro π' _hπ'
    -- Show: (runDistPure n π').bind extract = frontierEval (pureToPolicy (descendPureProfile π'))
    rw [← compiledPR_runDistPure_eq_frontierEval S sem hPR (descendPureProfile S sem π')]
    -- Need: runDistPure n π' = runDistPure n (liftPureProfile (descendPureProfile π'))
    congr 1
    simp only [ObsModelCore.runDistPure]
    apply ObsModelCore.runDist_congr
    intro m p ss _hss
    -- lift ∘ descend agrees with original on each info state:
    -- some I → rfl, none → PUnit.ext
    unfold ObsModelCore.pureToBehavioral
    congr 1
    unfold liftPureProfile liftPureStrategy descendPureProfile descendPureStrategy
    cases (compiledPRObs S sem).projectStates p ss with
    | none => exact PUnit.ext _ _
    | some I => rfl
  · exact (PMF.bind_map (pmfPi (ObsModelCore.behavioralToMixed β))
      (descendPureProfile S sem)
      (fun π => frontierEval S sem (pureToPolicy π))).symm

end NativeBToM
-- ============================================================================
-- M→B native theorem (Task 8)
-- ============================================================================

section NativeMToB

variable (S : Struct Player n) (sem : Sem S)

open Math.PMFProduct Math.ProbabilityMassFunction

set_option maxHeartbeats 400000 in
-- congrFun/congrArg for PMF.bind rewriting needs extra unification work
/-- **Kuhn M→B (fully native MAID)**: under perfect recall, every product
mixed strategy can be realized by a behavioral policy with the same outcome
distribution via `frontierEval`.

Both LHS and RHS use native MAID types. The compiled model is used
internally to construct the behavioral profile. -/
theorem kuhn_mixed_to_behavioral
    (hPR : S.PerfectRecall)
    (μ : ∀ p, PMF (PureStrategy S p)) :
    ∃ pol : Policy S,
      frontierEval S sem pol =
        (pmfPi μ).bind (fun π => frontierEval S sem (pureToPolicy π)) := by
  -- 1. Lift native mixed strategies to compiled PR model
  -- Use liftMixedProfile directly (no set, to allow rewriting)
  -- 2. Apply core M→B with conditions:
  --    - StepMassInvariant (Task 5)
  --    - StepSupportFactorization (Task 5)
  --    - ActionPosteriorLocal (Task 7)
  have hMass : ObsModelCore.StepMassInvariant (compiledPRObs S sem) :=
    stepMassInvariant_compiledPR S sem
  have hFactor : ObsModelCore.StepSupportFactorization (compiledPRObs S sem) :=
    stepSupportFactorization_compiledPR S sem
  have hAPL : ∀ p, ObsModelCore.ActionPosteriorLocal (compiledPRObs S sem) p :=
    fun p => actionPosteriorLocal_compiledPR S sem hPR p
  obtain ⟨β, hβ⟩ := ObsModelCore.kuhn_mixed_to_behavioral_semantic
    hMass hFactor hAPL (liftMixedProfile S sem μ) n
  -- hβ : runDist n β = (pmfPi μ').bind (runDistPure n)
  -- 3. Descend compiled behavioral profile to native policy
  set pol := descendBehavioralProfile S sem β
  refine ⟨pol, ?_⟩
  -- 4. LHS: frontierEval pol
  rw [← compiledPR_runDist_eq_frontierEval S sem hPR pol]
  -- 5. Connect: runDist n (liftBehavioralProfile pol) ≈ runDist n β
  --    They agree on reachable info states
  have hcongr : (compiledPRObs S sem).runDist n (liftBehavioralProfile S sem pol) =
      (compiledPRObs S sem).runDist n β := by
    symm
    apply ObsModelCore.runDist_congr
    intro m p ss _hss
    -- pol = descendBehavioralProfile β, so liftBehavioralProfile pol = lift (descend β)
    -- At `some I`: lift (descend β) = β (definitionally)
    -- At `none`: both are PMF PUnit = subsingleton
    change β p _ =
      (liftBehavioralProfile S sem (descendBehavioralProfile S sem β))
        p ((compiledPRObs S sem).projectStates p ss)
    simp only [liftBehavioralProfile, descendBehavioralProfile]
    cases (compiledPRObs S sem).projectStates p ss with
    | none =>
        -- Both sides are PMF over CompiledMAIDAct S p (currentObs p none) = PMF PUnit
        -- currentObs p none = none for identity info state, so type is PUnit
        -- All PMF over PUnit are equal (only PMF.pure PUnit.unit)
        change β p none = PMF.pure PUnit.unit
        ext ⟨⟩
        change (β p none : PMF PUnit) PUnit.unit =
          (PMF.pure PUnit.unit : PMF PUnit) PUnit.unit
        have := PMF.tsum_coe (show PMF PUnit from β p none)
        change (∑' a : PUnit, (β p none : PMF PUnit) a) = 1 at this
        simpa [tsum_fintype] using this
    | some I => rfl
  rw [hcongr, hβ, PMF.bind_bind]
  -- 6. RHS: connect frontierEval with (pmfPi μ').bind ...
  -- pmfPi μ' = (pmfPi μ).map liftPureProfile
  -- runDistPure n π' .bind extract = frontierEval (pureToPolicy (descend π'))
  -- via pure adequacy
  -- Goal: (pmfPi μ').bind (fun π' => (runDistPure n π').bind extract) =
  --   (pmfPi μ).bind (fun π => frontierEval (pureToPolicy π))
  -- pmfPi μ' = (pmfPi μ).map liftPureProfile
  -- RHS: pmfPi μ' = (pmfPi μ).map liftPureProfile
  -- Connect via liftMixedProfile_joint + pure adequacy
  have hpush : pmfPi (liftMixedProfile S sem μ) =
      (pmfPi μ).map (liftPureProfile S sem) :=
    (pmfPi_push_coordwise μ
      (fun p => liftPureStrategy S sem (p := p))).symm
  -- Factor through liftPureProfile via hpush + PMF.bind_map
  -- Direct approach: prove equality via PMF.ext + bind_map at point level
  ext x
  simp only [PMF.bind_apply]
  -- LHS sums over compiled strategies; change of variables via liftPureProfile
  -- Use hpush to relate pmfPi (liftMixed μ) = (pmfPi μ).map (liftPure)
  -- Then PMF.bind_map: ∑_a (map f d)(a) * g(a) = ∑_π d(π) * g(f(π))
  have hbm := PMF.bind_map (pmfPi μ) (liftPureProfile S sem)
    (fun π' => ((compiledPRObs S sem).runDistPure n π').bind
      (fun ss => PMF.pure (extractTAssign S
        ((compiledPRObs S sem).lastState ss))))
  -- hbm : (map liftPure (pmfPi μ)).bind g = (pmfPi μ).bind (g ∘ liftPure)
  -- We need: (pmfPi liftMixed).bind g = (pmfPi μ).bind (frontierEval ∘ pureToPolicy)
  -- i.e., hpush says pmfPi liftMixed = map liftPure (pmfPi μ)
  -- So (pmfPi liftMixed).bind g = (map liftPure (pmfPi μ)).bind g = (pmfPi μ).bind (g ∘ liftPure)
  -- and g ∘ liftPure = frontierEval ∘ pureToPolicy by pure adequacy
  have hlhs : (pmfPi (liftMixedProfile S sem μ)).bind
      (fun a => ((compiledPRObs S sem).runDistPure n a).bind
        (fun ss => PMF.pure (extractTAssign S
          ((compiledPRObs S sem).lastState ss)))) =
    (pmfPi μ).bind (fun π => frontierEval S sem (pureToPolicy π)) := by
    have : pmfPi (liftMixedProfile S sem μ) =
        PMF.map (liftPureProfile S sem) (pmfPi μ) := hpush
    rw [show (pmfPi (liftMixedProfile S sem μ)).bind _ =
        (PMF.map (liftPureProfile S sem) (pmfPi μ)).bind _ from
      congrFun (congrArg PMF.bind this) _,
      PMF.bind_map]
    congr 1; funext π
    exact compiledPR_runDistPure_eq_frontierEval S sem hPR π
  exact congrFun (congrArg DFunLike.coe hlhs) x

end NativeMToB

end GameTheory.Languages.MAID
