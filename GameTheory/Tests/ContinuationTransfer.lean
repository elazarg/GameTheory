/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.Continuation
import GameTheory.Tests.IrreversibleFailure

/-! # Continuation transfer: identity and the irreversible-failure boundary

The positive case uses the canonical root and policy types. The negative case
proves that no fixed playerwise compiler can supply uniform public continuation
laws for the checked pair of atomic protocols, even for their common source SPE.
-/

noncomputable section

namespace GameTheory.Tests.ContinuationTransfer

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open GameTheory.Tests.IrreversibleFailure

/-- Retaining the same game supplies a continuation witness at every root. -/
example (source : Bool) (profile : Profile (model source).strategicSignature)
    (value : (arena source).History → Unit → ℝ)
    (perfect : (model source).IsSubgamePerfect (terminates source) profile value) :
    (model source).IsSubgamePerfect (terminates source) profile value := by
  apply (model source).isSubgamePerfect_of_continuation_laws (model source)
    (terminates source) (terminates source) (bounded source) (bounded source)
    (fun _ policy => policy) id id profile ?_ value perfect
  intro root proper
  refine ⟨root, proper, rfl, ?_⟩
  intro who alternative
  refine ⟨FinDist.pure alternative, ?_⟩
  rw [FinDist.pure_bind]
  rfl

/-- Continuation laws are stronger than the initial public-outcome simulation.
This theorem refutes those laws for the added irreversible-failure interface
using only the atomic protocol semantics. -/
theorem no_uniform_failure_continuation_laws
    (compile : ∀ who, (model true).Policy who → (model false).Policy who)
    (coverage : ∀ targetRoot, (model false).IsSubgameRoot targetRoot →
      ∃ sourceRoot, (model true).IsSubgameRoot sourceRoot ∧
        ((model false).runFrom
          (Profile.map (target := (model false).strategicSignature) compile sourceProfile)
          4 targetRoot).map (fun history => outcome history.state) =
          ((model true).runFrom sourceProfile 4 sourceRoot).map
            (fun history => outcome history.state) ∧
        ∀ who (alternative : (model false).Policy who),
          ∃ mixture : FinDist ((model true).Policy who),
            ((model false).runFrom (Profile.update
              (Profile.map (target := (model false).strategicSignature) compile sourceProfile)
              who alternative) 4 targetRoot).map (fun history => outcome history.state) =
            mixture.bind fun replacement =>
              ((model true).runFrom (Profile.update sourceProfile who replacement)
                4 sourceRoot).map (fun history => outcome history.state)) : False := by
  apply no_common_target_spe
  refine ⟨Profile.map compile sourceProfile, ?_, ?_⟩
  · exact (model true).isSubgamePerfect_of_continuation_laws (model false)
      (terminates true) (terminates false) (bounded true) (bounded false)
      compile (fun history => outcome history.state) (fun history => outcome history.state)
      sourceProfile coverage (fun result _ => utility false result) (source_subgamePerfect false)
  · exact (model true).isSubgamePerfect_of_continuation_laws (model false)
      (terminates true) (terminates false) (bounded true) (bounded false)
      compile (fun history => outcome history.state) (fun history => outcome history.state)
      sourceProfile coverage (fun result _ => utility true result) (source_subgamePerfect true)

end GameTheory.Tests.ContinuationTransfer
