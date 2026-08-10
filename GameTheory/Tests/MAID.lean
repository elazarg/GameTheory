/-
# General MAID bridge fixture

A one-decision typed diagram is enough to exercise the general native frontier
semantics, its compiled EFG semantics, and source-player Nash transfer. The two
pure policies induce different assignment laws, so the bridge cannot pass by
ignoring the decision node.
-/

import GameTheory.Languages.MAID.Strategic

noncomputable section

namespace GameTheory.Tests.MAID

open GameTheory
open GameTheory.Probability
open GameTheory.Languages.MAID
open GameTheory.Languages.MAID.Strategic
open GameTheory.Languages.MAID.ToEFG

inductive Node
  | decision
  deriving DecidableEq

instance : Fintype Node :=
  Fintype.ofList [.decision] (by
    intro node
    cases node
    simp)

def parents (_ : Node) : Finset Node := ∅

private theorem acyclic :
    GameTheoryMath.DAG.Acyclic
      (fun first second => first ∈ parents second) := by
  have noEdge : ∀ {first second : Node}, first ∈ parents second → False := by
    intro first second hedge
    simp [parents] at hedge
  intro node cycle
  induction cycle with
  | single hedge => exact noEdge hedge
  | tail _ hedge _ => exact noEdge hedge

@[reducible]
def diagram : Structure Unit Node where
  kind _ := .decision ()
  parents := parents
  observedParents _ := ∅
  Value _ := Bool
  observed_sub _ := by simp
  observed_eq_of_chance node hkind := by
    cases node
    simp at hkind
  acyclic := acyclic

def topological : GameTheoryMath.DAG.TopologicalOrder diagram.parents where
  order := [.decision]
  nodup := by decide
  complete := by
    intro node
    cases node
    simp
  respects := by
    intro index parent hparent
    simp [parents] at hparent

@[reducible]
def semantics : Semantics diagram where
  defaultValue _ := false
  chanceLaw node hkind _ := by
    cases node
    simp at hkind
  utility _ assignment := if assignment .decision then 1 else 0

/-- Choose one Boolean value at the diagram's only decision site. -/
def choose (value : Bool) : Policy diagram :=
  fun _ _ _ => FinDist.pure value

def initial : FrontierState diagram :=
  FrontierState.initial semantics

theorem initial_frontier : initial.frontier = {.decision} := by
  ext node
  rw [FrontierState.mem_frontier_iff]
  cases node
  simp [initial, FrontierState.initial, diagram, parents]

def draw (value : Bool) :
    (node : {node // node ∈ initial.frontier}) → diagram.Value node.1 :=
  fun _ => value

def reached (value : Bool) : FrontierState diagram :=
  initial.extend (draw value)

theorem reached_value (value : Bool) :
    (reached value).values .decision = value := by
  have hmem : Node.decision ∈ initial.frontier := by
    rw [initial_frontier]
    simp
  exact FrontierState.extend_value_of_frontier initial (draw value)
    ⟨.decision, hmem⟩

private theorem step_initial (value : Bool) :
    step diagram semantics (choose value) initial = FinDist.pure (reached value) := by
  rw [step, frontierLaw]
  have hlaws :
      (fun node => nodeLaw diagram semantics (choose value) initial node) =
        fun _ => FinDist.pure value := by
    funext node
    simp [nodeLaw, choose, diagram]
  rw [hlaws, FinDist.pi_pure, FinDist.map_pure]
  rfl

theorem native_law (value : Bool) :
    (nativeBehavioralGameForm semantics).play (choose value) =
      FinDist.pure (reached value).values := by
  show FinDist.map (fun reached => reached.values)
      (run diagram semantics (choose value) (Fintype.card Node) initial) = _
  have hcard : Fintype.card Node = 1 := by decide
  rw [hcard, run]
  have hincomplete : ¬ initial.IsComplete := by
    intro hcomplete
    have hempty : (∅ : Finset Node) = Finset.univ := by
      simpa [initial, FrontierState.IsComplete, FrontierState.initial] using hcomplete
    have hmem : Node.decision ∈ (∅ : Finset Node) := by
      rw [hempty]
      simp
    simp at hmem
  rw [if_neg hincomplete, step_initial]
  rw [FinDist.pure_bind, run, FinDist.map_pure]

/-- The two policies have distinct native laws; the decision coordinate is
semantically reachable. -/
theorem native_laws_distinct :
    (nativeBehavioralGameForm semantics).play (choose false) ≠
      (nativeBehavioralGameForm semantics).play (choose true) := by
  rw [native_law, native_law]
  intro hequal
  have hpure : (reached false).values = (reached true).values := by
    have hmem : (reached false).values ∈
        (FinDist.pure (reached true).values).support := by
      rw [← hequal]
      simp
    simpa using hmem
  have hvalue := congrFun hpure Node.decision
  rw [reached_value, reached_value] at hvalue
  exact Bool.false_ne_true hvalue

/-- The general native and compiled evaluators agree on this concrete,
nonconstant policy family. -/
theorem native_compiled_law (value : Bool) :
    (nativeBehavioralGameForm semantics).play (choose value) =
      (compiledBehavioralGameForm topological semantics).play
        (behavioralProfile topological semantics (choose value)) :=
  native_play_eq_compiled_play topological semantics (choose value)

/-- Compilation preserves the observable distinction between the two source
policies. -/
theorem compiled_laws_distinct :
    (compiledBehavioralGameForm topological semantics).play
        (behavioralProfile topological semantics (choose false)) ≠
      (compiledBehavioralGameForm topological semantics).play
        (behavioralProfile topological semantics (choose true)) := by
  intro hequal
  apply native_laws_distinct
  rw [native_compiled_law, native_compiled_law]
  exact hequal

/-- Source-player Nash equilibrium is invariant under compilation for the
concrete typed diagram. -/
theorem native_nash_iff_compiled (value : Bool) :
    IsNash (nativeBehavioralGameForm semantics)
        (euPreference fun assignment _ => semantics.utility () assignment)
        (choose value) ↔
      IsNash (compiledBehavioralGameForm topological semantics)
        (euPreference fun assignment _ => semantics.utility () assignment)
        (behavioralProfileEquiv topological semantics (choose value)) :=
  isNash_native_iff_compiled topological semantics (choose value)

end GameTheory.Tests.MAID
