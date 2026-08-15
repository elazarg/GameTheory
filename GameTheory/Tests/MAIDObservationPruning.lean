/-
# Hostile MAID observation-pruning witness

A chance signal is an observed parent of one decision.  Pruning removes that
input from the reduced policy domain. Constant policies factor through the
smaller domain and keep their native/compiled assignment law; a signal-reading
full policy is proved outside the image of every reduced policy.
-/

import GameTheory.Languages.MAID.ObservationPruning

noncomputable section

namespace GameTheory.Tests.MAIDObservationPruning

open GameTheory
open GameTheory.Math.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.ObservationPruning
open GameTheory.Languages.MAID.Strategic
open GameTheory.Languages.MAID.ToEFG

inductive Node
  | signal
  | decision
  deriving DecidableEq, Fintype

def parents : Node → Finset Node
  | .signal => ∅
  | .decision => {.signal}

def observedParents : Node → Finset Node
  | .signal => ∅
  | .decision => {.signal}

def topologicalParents : GameTheory.Math.DAG.TopologicalOrder parents where
  order := [.signal, .decision]
  nodup := by decide
  complete node := by cases node <;> simp
  respects := by
    intro index parent hparent
    fin_cases index
    · simp [parents] at hparent
    · have hsignal : parent = .signal := by
        simpa [parents] using hparent
      subst parent
      exact ⟨0, by decide, rfl⟩

@[reducible]
def diagram : Structure Unit Node where
  kind
    | .signal => .chance
    | .decision => .decision ()
  parents := parents
  observedParents := observedParents
  Value _ := Bool
  observed_sub node := by cases node <;> simp [parents, observedParents]
  observed_eq_of_chance node hchance := by
    cases node <;> simp [parents, observedParents] at hchance ⊢
  acyclic := GameTheory.Math.DAG.acyclic_of_topologicalOrder
    topologicalParents

def topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents :=
  topologicalParents

@[reducible]
def semantics : Semantics diagram where
  defaultValue _ := false
  chanceLaw node hchance _ := by
    cases node with
    | signal => exact FinDist.pure true
    | decision => simp at hchance
  utility _ assignment := if assignment .decision then 1 else 0

/-- Remove the signal from the decision policy's input. -/
def pruning : Pruning diagram where
  kept _ := ∅
  kept_sub_observed _ := by simp

def decisionSite : DecisionSite diagram () := ⟨.decision, rfl⟩

def observedConfig (value : Bool) :
    Config diagram (diagram.observedParents .decision) :=
  fun _ => value

/-- A reduced policy can choose a constant without receiving the signal. -/
def reducedChoose (value : Bool) : pruning.ReducedPolicy :=
  fun _ _ _ => FinDist.pure value

def fullChoose (value : Bool) : Policy diagram :=
  pruning.expandPolicy (reducedChoose value)

/-- The constant full policy is represented by the genuinely smaller policy
domain. -/
theorem pruning_represents_fullChoose (value : Bool) :
    pruning.Represents (fullChoose value) :=
  ⟨reducedChoose value, rfl⟩

/-- Its native law is literally the reduced native law. -/
theorem full_native_eq_reduced_native (value : Bool) :
    (nativeBehavioralGameForm semantics).play (fullChoose value) =
      (pruning.reducedNativeGameForm semantics).play
        (reducedChoose value) :=
  pruning.native_play_eq_reducedNative_play_of_expands
    semantics (fullChoose value) (reducedChoose value) rfl

/-- The same pruning preserves the actual compiled EFG assignment law. -/
theorem full_compiled_eq_reduced_compiled (value : Bool) :
    (compiledBehavioralGameForm topological semantics).play
        (behavioralProfile topological semantics (fullChoose value)) =
      (pruning.reducedCompiledGameForm topological semantics).play
        (reducedChoose value) :=
  pruning.compiled_play_eq_reducedCompiled_play_of_expands
    topological semantics (fullChoose value) (reducedChoose value) rfl

/-- Every expanded reduced policy ignores the removed signal. -/
theorem expanded_ignores_signal (reduced : pruning.ReducedPolicy) :
    pruning.expandPolicy reduced () decisionSite (observedConfig false) =
      pruning.expandPolicy reduced () decisionSite (observedConfig true) := by
  unfold Pruning.expandPolicy Pruning.expandOwnerPolicy
  apply congrArg (reduced () decisionSite)
  funext node
  have hmem : node.1 ∈ (∅ : Finset Node) := by
    exact node.2
  have hnone : ∀ value : Node, value ∉ (∅ : Finset Node) :=
    Finset.eq_empty_iff_forall_notMem.mp rfl
  exact False.elim (hnone node.1 hmem)

/-- A full policy that reads the signal. -/
def signalSensitive : Policy diagram :=
  fun _ site observed =>
    match hnode : site.1 with
    | .signal => by
        have hkind := site.2
        simp [diagram, hnode] at hkind
    | .decision =>
        FinDist.pure (observed ⟨.signal, by
          simp [diagram, observedParents, hnode]⟩)

/-- The removed observation is semantically live in the full policy domain. -/
theorem signalSensitive_reads_signal :
    signalSensitive () decisionSite (observedConfig false) ≠
      signalSensitive () decisionSite (observedConfig true) := by
  simp only [signalSensitive, decisionSite, observedConfig]
  intro hequal
  have hprob := congrArg
    (fun law : FinDist Bool => law.prob false) hequal
  norm_num [FinDist.prob_pure_eq_ite] at hprob

/-- Consequently no reduced policy expands to the signal-sensitive policy. -/
theorem pruning_does_not_represent_signalSensitive :
    ¬ pruning.Represents signalSensitive := by
  rintro ⟨reduced, hexpands⟩
  have howner := congrFun hexpands ()
  have hsite := congrFun howner decisionSite
  have hfalse := congrFun hsite (observedConfig false)
  have htrue := congrFun hsite (observedConfig true)
  apply signalSensitive_reads_signal
  calc
    signalSensitive () decisionSite (observedConfig false) =
        pruning.expandPolicy reduced () decisionSite
          (observedConfig false) := hfalse.symm
    _ = pruning.expandPolicy reduced () decisionSite
          (observedConfig true) := expanded_ignores_signal reduced
    _ = signalSensitive () decisionSite (observedConfig true) := htrue

/-- Reduced native and compiled Nash questions use the same canonical
predicate and have the same answer. -/
theorem reduced_nash_iff_compiled (value : Bool) :
    IsNash (pruning.reducedNativeGameForm semantics)
        (euPreference fun assignment _ => semantics.utility () assignment)
        (reducedChoose value) ↔
      IsNash (pruning.reducedCompiledGameForm topological semantics)
        (euPreference fun assignment _ => semantics.utility () assignment)
        (reducedChoose value) :=
  pruning.isNash_reducedNative_iff_reducedCompiled
    topological semantics (reducedChoose value)

end GameTheory.Tests.MAIDObservationPruning
