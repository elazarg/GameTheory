import GameTheory.Languages.MAID.Compile
import GameTheory.Model.Lemmas.HistoryCover
import GameTheory.Theorems.Kuhn

/-!
# GameTheory.Theorems.MAID

Target-side reduction lemmas for compiled MAIDs.

This file packages the structural equivalence between native frontier semantics
and the compiled `InfoModel` presentation so later theorem ports can ignore the
surface syntax.
-/

namespace GameTheory.Theorems.MAID

open _root_.MAID
open GameTheory.Theorems

variable {Player : Type} [DecidableEq Player] [Fintype Player] {n : Nat}

/-- Finite public-observation alphabet for one frontier step of a MAID. -/
noncomputable def publicFrontierAlphabet (_S : Struct Player n) :
    Finset (List (Fin n)) :=
  InfoModel.listsUpToLength (Finset.univ : Finset (Fin n)) n

/-- Finite private-observation alphabet for player `p` at one frontier step. -/
noncomputable def privateFrontierAlphabet (S : Struct Player n) (p : Player) :
    Finset (List (Infoset S p)) :=
  InfoModel.listsUpToLength (Finset.univ : Finset (Infoset S p)) n

/-- Canonical finite local-history cover for compiled MAIDs up to horizon `k`. -/
noncomputable def canonicalHistoryCover
    (S : Struct Player n) (sem : Sem S) (k : Nat) :
    ∀ p, Finset ((compileInfoOn S sem).LocalTrace p) := by
  classical
  intro p
  exact
    ((InfoModel.listsUpToLength (publicFrontierAlphabet S) (k + 1)).product
      (InfoModel.listsUpToLength (privateFrontierAlphabet S p) (k + 1))).image
      (fun q => (q.1, q.2))

private theorem frontierList_mem_publicFrontierAlphabet
    (S : Struct Player n) (cfg : FrontierCfg S) :
    frontierList S cfg ∈ publicFrontierAlphabet S := by
  classical
  exact InfoModel.mem_listsUpToLength_of_forall_mem
    (s := (Finset.univ : Finset (Fin n)))
    (n := n)
    (xs := frontierList S cfg)
    (Nat.le_trans (List.length_filter_le _ _) (by simp [S.topo_length]))
    (fun x _ => by simp)

private theorem frontierInfosets_mem_privateFrontierAlphabet
    (S : Struct Player n) (cfg : FrontierCfg S) (p : Player) :
    frontierInfosets S cfg p ∈ privateFrontierAlphabet S p := by
  classical
  exact InfoModel.mem_listsUpToLength_of_forall_mem
    (s := (Finset.univ : Finset (Infoset S p)))
    (n := n)
    (xs := frontierInfosets S cfg p)
    (Nat.le_trans (List.length_filterMap_le _ _) (by simp [S.topo_length]))
    (fun x _ => by simp)

/-- The canonical bounded-history cover is sufficient for the compiled MAID up
to horizon `k`. -/
theorem canonicalHistoryCover_spec
    (S : Struct Player n) (sem : Sem S) (k : Nat) :
    (compileInfoOn S sem).CoversHistoriesUpTo (canonicalHistoryCover S sem k) k := by
  classical
  intro p ss _ hlen
  change ((compileInfoOn S sem).projectPublic ss, (compileInfoOn S sem).projectPrivate p ss) ∈
    (canonicalHistoryCover S sem k) p
  refine Finset.mem_image.mpr ?_
  refine
    ⟨((compileInfoOn S sem).projectPublic ss, (compileInfoOn S sem).projectPrivate p ss),
      ?_, rfl⟩
  simp only [compileInfoOn, InfoModel.projectPublic, InfoModel.projectPrivate]
  refine Finset.mem_product.mpr ?_
  refine ⟨?_, ?_⟩
  · apply InfoModel.mem_listsUpToLength_of_forall_mem
    · simpa using hlen
    · intro x hx
      rcases List.mem_map.mp hx with ⟨cfg, hcfg, rfl⟩
      exact frontierList_mem_publicFrontierAlphabet S cfg
  · apply InfoModel.mem_listsUpToLength_of_forall_mem
    · simpa using hlen
    · intro x hx
      rcases List.mem_map.mp hx with ⟨cfg, hcfg, rfl⟩
      exact frontierInfosets_mem_privateFrontierAlphabet S cfg p

/-- The compiled MAID machine has exactly the native frontier step relation. -/
theorem step_iff
    (S : Struct Player n) (sem : Sem S)
    (a : ∀ p : Player, Option (FrontierAct S p))
    (src dst : FrontierCfg S) :
    (compileInfoOn S sem).step a src dst ↔ Step S sem a src dst :=
  compile_step_iff S sem a src dst

/-- Reachability in the compiled machine is exactly native frontier reachability. -/
theorem reach_iff
    (S : Struct Player n) (sem : Sem S)
    (ha : List (∀ p : Player, Option (FrontierAct S p)))
    (src dst : FrontierCfg S) :
    Semantics.Transition.ReachBy (compileInfoOn S sem).step ha src dst ↔
      ReachBy S sem ha src dst :=
  compile_reach_iff S sem ha src dst

/-- The compiled information model exposes the native frontier list. -/
theorem publicView_eq
    (S : Struct Player n) (sem : Sem S)
    (cfg : FrontierCfg S) :
    (compileInfoOn S sem).publicView cfg = frontierList S cfg :=
  compile_publicView_eq_frontier S sem cfg

/-- The compiled information model exposes the native frontier infosets. -/
theorem observe_eq
    (S : Struct Player n) (sem : Sem S)
    (p : Player) (cfg : FrontierCfg S) :
    (compileInfoOn S sem).observe p cfg = frontierInfosets S cfg p :=
  compile_observe_eq_frontierInfosets S sem p cfg

/-- The finite-horizon language-specific obligation for the restricted Kuhn
reduction over compiled MAIDs. -/
abbrev compiledHistoryCover
    (S : Struct Player n) (sem : Sem S)
    (k : Nat)
    (H : ∀ p, Finset ((compileInfoOn S sem).LocalTrace p)) : Prop :=
  (compileInfoOn S sem).CoversHistoriesUpTo H k

/-- Restricted finite-cover mixed-to-behavioral reduction for compiled MAIDs. -/
theorem kuhn_mixed_to_behavioral_of_compiled_restricted
    (S : Struct Player n) (sem : Sem S)
    (D : Execution.Dynamics (compileInfoOn S sem))
    (k : Nat)
    (H : ∀ p, Finset ((compileInfoOn S sem).LocalTrace p))
    [∀ p, DecidableEq ((compileInfoOn S sem).LocalTrace p)]
    [∀ p, Fintype ((compileInfoOn S sem).RestrictedLocalCoord H p)]
    [∀ p, Fintype ((compileInfoOn S sem).RestrictedLocalPure H p)]
    [∀ p, Fintype (Option (FrontierAct S p))]
    (hStepIndep : ∀ μ n, (compileInfoOn S sem).RestrictedStepIndependence D H μ n) :
    KuhnMixedToBehavioralViaOutcome
      ((compileInfoOn S sem).RestrictedBehavioralProfile H)
      ((compileInfoOn S sem).RestrictedMixedProfile H)
      ((compileInfoOn S sem).RestrictedPureProfile H)
      (compileInfoOn S sem).Outcome
      ((compileInfoOn S sem).restrictedMixedJointRaw H)
      (GameTheory.Theorems.evalRestrictedBehavioral (I := compileInfoOn S sem) D k H)
      (GameTheory.Theorems.evalRestrictedPure (I := compileInfoOn S sem) D k H) := by
  simpa using
    (GameTheory.Theorems.kuhn_mixed_to_behavioral_restricted
      (I := compileInfoOn S sem) (D := D) (k := k) H hStepIndep)

/-- Cover-based mixed-to-behavioral reduction for compiled MAIDs. -/
theorem kuhn_mixed_to_behavioral_of_compiled_via_cover
    (S : Struct Player n) (sem : Sem S)
    (D : Execution.Dynamics (compileInfoOn S sem))
    (k : Nat)
    (H : ∀ p, Finset ((compileInfoOn S sem).LocalTrace p))
    [∀ p, DecidableEq ((compileInfoOn S sem).LocalTrace p)]
    [∀ p, Fintype ((compileInfoOn S sem).RestrictedLocalCoord H p)]
    [∀ p, Fintype ((compileInfoOn S sem).RestrictedLocalPure H p)]
    [∀ p, Finite ((compileInfoOn S sem).LocalTrace p)]
    [∀ p, Fintype (InfoModel.LocalPure (I := compileInfoOn S sem) p)]
    [∀ p, Fintype (Option (FrontierAct S p))]
    (hCover : compiledHistoryCover S sem k H)
    (hStepIndep : ∀ μ n, (compileInfoOn S sem).RestrictedStepIndependence D H μ n) :
    KuhnMixedToBehavioralViaOutcome
      (Execution.BehavioralProfile (compileInfoOn S sem))
      (InfoModel.MixedProfile (I := compileInfoOn S sem))
      (Execution.PureProfile (compileInfoOn S sem))
      (compileInfoOn S sem).Outcome
      (InfoModel.mixedJoint (I := compileInfoOn S sem))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  simpa [compiledHistoryCover] using
    (GameTheory.Theorems.kuhn_mixed_to_behavioral_via_cover
      (I := compileInfoOn S sem) (D := D) (k := k) H hCover hStepIndep)

/-- Restricted finite-cover Kuhn reduction for compiled MAIDs. -/
theorem kuhn_complete_of_compiled_restricted
    (S : Struct Player n) (sem : Sem S)
    (D : Execution.Dynamics (compileInfoOn S sem))
    (k : Nat)
    (H : ∀ p, Finset ((compileInfoOn S sem).LocalTrace p))
    [∀ p, DecidableEq ((compileInfoOn S sem).LocalTrace p)]
    [∀ p, Fintype ((compileInfoOn S sem).RestrictedLocalCoord H p)]
    [∀ p, Fintype ((compileInfoOn S sem).RestrictedLocalPure H p)]
    [∀ p, Fintype (Option (FrontierAct S p))]
    (hStepIndep : ∀ μ n, (compileInfoOn S sem).RestrictedStepIndependence D H μ n) :
    KuhnCompleteViaOutcome
      ((compileInfoOn S sem).RestrictedBehavioralProfile H)
      ((compileInfoOn S sem).RestrictedMixedProfile H)
      ((compileInfoOn S sem).RestrictedPureProfile H)
      (compileInfoOn S sem).Outcome
      (GameTheory.Theorems.mixedOfBehavioralCanonicalRestricted (I := compileInfoOn S sem) H)
      ((compileInfoOn S sem).restrictedMixedJointRaw H)
      (GameTheory.Theorems.evalRestrictedBehavioral (I := compileInfoOn S sem) D k H)
      (GameTheory.Theorems.evalRestrictedPure (I := compileInfoOn S sem) D k H) := by
  simpa using
    (GameTheory.Theorems.kuhn_complete_restricted
      (I := compileInfoOn S sem) (D := D) (k := k) H hStepIndep)

/-- Cover-based full Kuhn reduction for compiled MAIDs. -/
theorem kuhn_complete_of_compiled_via_cover
    (S : Struct Player n) (sem : Sem S)
    (D : Execution.Dynamics (compileInfoOn S sem))
    (k : Nat)
    (H : ∀ p, Finset ((compileInfoOn S sem).LocalTrace p))
    [∀ p, DecidableEq ((compileInfoOn S sem).LocalTrace p)]
    [∀ p, Fintype ((compileInfoOn S sem).RestrictedLocalCoord H p)]
    [∀ p, Fintype ((compileInfoOn S sem).RestrictedLocalPure H p)]
    [∀ p, Finite ((compileInfoOn S sem).LocalTrace p)]
    [∀ p, Fintype ((compileInfoOn S sem).LocalTrace p)]
    [∀ p, Fintype (InfoModel.LocalPure (I := compileInfoOn S sem) p)]
    [∀ p, Fintype (Option (FrontierAct S p))]
    (hCover : compiledHistoryCover S sem k H)
    (hStepIndep : ∀ μ n, (compileInfoOn S sem).RestrictedStepIndependence D H μ n) :
    KuhnCompleteViaOutcome
      (Execution.BehavioralProfile (compileInfoOn S sem))
      (InfoModel.MixedProfile (I := compileInfoOn S sem))
      (Execution.PureProfile (compileInfoOn S sem))
      (compileInfoOn S sem).Outcome
      (mixedOfBehavioralCanonical (I := compileInfoOn S sem))
      (InfoModel.mixedJoint (I := compileInfoOn S sem))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  simpa [compiledHistoryCover] using
    (GameTheory.Theorems.kuhn_complete_via_cover
      (I := compileInfoOn S sem) (D := D) (k := k) H hCover hStepIndep)

/-- Canonical-cover mixed-to-behavioral reduction for compiled MAIDs. The
finite cover is the bounded list-enumeration built from frontier observations. -/
theorem kuhn_mixed_to_behavioral_of_compiled
    (S : Struct Player n) (sem : Sem S)
    (D : Execution.Dynamics (compileInfoOn S sem))
    (k : Nat)
    [∀ p, DecidableEq ((compileInfoOn S sem).LocalTrace p)]
    [∀ p, Fintype ((compileInfoOn S sem).RestrictedLocalCoord (canonicalHistoryCover S sem k) p)]
    [∀ p, Fintype ((compileInfoOn S sem).RestrictedLocalPure (canonicalHistoryCover S sem k) p)]
    [∀ p, Finite ((compileInfoOn S sem).LocalTrace p)]
    [∀ p, Fintype (InfoModel.LocalPure (I := compileInfoOn S sem) p)]
    [∀ p, Fintype (Option (FrontierAct S p))]
    (hStepIndep :
      ∀ μ n,
        (compileInfoOn S sem).RestrictedStepIndependence D (canonicalHistoryCover S sem k) μ n) :
    KuhnMixedToBehavioralViaOutcome
      (Execution.BehavioralProfile (compileInfoOn S sem))
      (InfoModel.MixedProfile (I := compileInfoOn S sem))
      (Execution.PureProfile (compileInfoOn S sem))
      (compileInfoOn S sem).Outcome
      (InfoModel.mixedJoint (I := compileInfoOn S sem))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  exact kuhn_mixed_to_behavioral_of_compiled_via_cover
    (S := S) (sem := sem) (D := D) (k := k) (H := canonicalHistoryCover S sem k)
    (hCover := canonicalHistoryCover_spec S sem k)
    hStepIndep

/-- Canonical-cover full Kuhn reduction for compiled MAIDs. -/
theorem kuhn_complete_of_compiled
    (S : Struct Player n) (sem : Sem S)
    (D : Execution.Dynamics (compileInfoOn S sem))
    (k : Nat)
    [∀ p, DecidableEq ((compileInfoOn S sem).LocalTrace p)]
    [∀ p, Fintype ((compileInfoOn S sem).RestrictedLocalCoord (canonicalHistoryCover S sem k) p)]
    [∀ p, Fintype ((compileInfoOn S sem).RestrictedLocalPure (canonicalHistoryCover S sem k) p)]
    [∀ p, Finite ((compileInfoOn S sem).LocalTrace p)]
    [∀ p, Fintype ((compileInfoOn S sem).LocalTrace p)]
    [∀ p, Fintype (InfoModel.LocalPure (I := compileInfoOn S sem) p)]
    [∀ p, Fintype (Option (FrontierAct S p))]
    (hStepIndep :
      ∀ μ n,
        (compileInfoOn S sem).RestrictedStepIndependence D (canonicalHistoryCover S sem k) μ n) :
    KuhnCompleteViaOutcome
      (Execution.BehavioralProfile (compileInfoOn S sem))
      (InfoModel.MixedProfile (I := compileInfoOn S sem))
      (Execution.PureProfile (compileInfoOn S sem))
      (compileInfoOn S sem).Outcome
      (mixedOfBehavioralCanonical (I := compileInfoOn S sem))
      (InfoModel.mixedJoint (I := compileInfoOn S sem))
      (D.evalBehavioral k)
      (D.evalPure k) := by
  exact kuhn_complete_of_compiled_via_cover
    (S := S) (sem := sem) (D := D) (k := k) (H := canonicalHistoryCover S sem k)
    (hCover := canonicalHistoryCover_spec S sem k)
    hStepIndep

end GameTheory.Theorems.MAID
