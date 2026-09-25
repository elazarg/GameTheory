/-
# EXP-140: ordinary-PMF typed MAID gate

An infinite chance node and a Boolean decision site exercise native and
compiled assignment laws, guarded Nash transfer, and an undefined actual
deviation. The value carrier at the chance node remains infinite.
-/

import GameTheory.Languages.MAID.Strategic
import GameTheory.Experimental.PostArchitecture.PMFRestorationProbe

noncomputable section

namespace GameTheory.Experimental.PMFMAIDGate

open GameTheory GameTheory.Languages.MAID GameTheory.Languages.MAID.Strategic
open GameTheory.Math.Probability GameTheory.Experimental.PMFRestoration

inductive Node
  | chance
  | decision
  deriving DecidableEq

instance : Fintype Node :=
  Fintype.ofList [.chance, .decision] (by intro node; cases node <;> simp)

def parents (_ : Node) : Finset Node := ∅

private theorem acyclic :
    GameTheory.Math.DAG.Acyclic
      (fun first second : Node => first ∈ parents second) := by
  have rank_lt_of_predecessor : ∀ {first second : Node},
      first ∈ parents second → (0 : ℕ) < 0 := by
    intro first second edge
    simp [parents] at edge
  have rank_lt_of_path : ∀ {first second : Node},
      Relation.TransGen (fun source target => source ∈ parents target)
        first second → (0 : ℕ) < 0 := by
    intro first second path
    induction path with
    | single edge => exact rank_lt_of_predecessor edge
    | tail _ edge _ => exact rank_lt_of_predecessor edge
  intro node cycle
  exact Nat.lt_irrefl _ (rank_lt_of_path cycle)

@[reducible]
def diagram : Structure Unit Node where
  kind
    | .chance => .chance
    | .decision => .decision ()
  parents := parents
  observedParents _ := ∅
  Value
    | .chance => ℕ
    | .decision => Bool
  observed_sub _ := by simp
  observed_eq_of_chance _ _ := rfl
  acyclic := acyclic

def topological : GameTheory.Math.DAG.TopologicalOrder diagram.parents where
  order := [.chance, .decision]
  nodup := by decide
  complete := by intro node; cases node <;> simp
  respects := by intro index parent hparent; simp [parents] at hparent

def semantics : Semantics diagram where
  defaultValue
    | .chance => 0
    | .decision => false
  chanceLaw node hkind _ := by
    cases node with
    | chance => exact geometric
    | decision => simp at hkind
  utility _ assignment :=
    if assignment .decision then exploding (assignment .chance) else 0

def boundedSemantics : Semantics diagram :=
  { semantics with utility := fun _ _ => 0 }

def purePolicy (action : Bool) : Policy diagram :=
  fun _ site _ => by
    rcases site with ⟨node, hkind⟩
    cases node with
    | chance => simp at hkind
    | decision => exact PMF.pure action

def initial : FrontierState diagram := FrontierState.initial semantics

private theorem initial_frontier : initial.frontier = Finset.univ := by
  ext node
  rw [FrontierState.mem_frontier_iff]
  simp [initial, FrontierState.initial, diagram, parents]

private theorem initial_incomplete : ¬ initial.IsComplete := by
  intro hcomplete
  have hchance : Node.chance ∈ initial.resolved := by
    rw [hcomplete]
    simp
  simp [initial, FrontierState.initial] at hchance

def chanceIndex : {node // node ∈ initial.frontier} :=
  ⟨.chance, by rw [initial_frontier]; simp⟩

def decisionIndex : {node // node ∈ initial.frontier} :=
  ⟨.decision, by rw [initial_frontier]; simp⟩

def chanceDraw
    (draw : (node : {node // node ∈ initial.frontier}) → diagram.Value node.1) :
    ℕ := draw chanceIndex

private theorem initial_nodeLaw_chance (action : Bool) :
    nodeLaw diagram semantics (purePolicy action) initial chanceIndex = geometric := by
  rfl

private theorem initial_nodeLaw_decision (action : Bool) :
    nodeLaw diagram semantics (purePolicy action) initial decisionIndex =
      PMF.pure action := by
  rfl

private theorem step_complete (action : Bool) :
    ∀ reached ∈ (step diagram semantics (purePolicy action) initial).support,
      reached.IsComplete := by
  intro reached hreached
  obtain ⟨draw, rfl⟩ :=
    eq_extend_of_mem_support_step diagram semantics (purePolicy action)
      initial reached hreached
  simp [FrontierState.IsComplete, initial_frontier]

private theorem run_two_eq_step (action : Bool) :
    run diagram semantics (purePolicy action) 2 initial =
      step diagram semantics (purePolicy action) initial := by
  rw [run, ite_eq_right initial_incomplete]
  calc
    _ = (step diagram semantics (purePolicy action) initial).bind PMF.pure := by
      apply bind_congr_on_support
      intro reached hreached
      exact run_of_complete diagram semantics (purePolicy action) 1 reached
        (step_complete action reached hreached)
    _ = _ := PMF.bind_pure _

private theorem chance_marginal (action : Bool) :
    (frontierLaw diagram semantics (purePolicy action) initial).map
        chanceDraw = geometric := by
  have heval := independentProduct_map_eval
    (fun node => nodeLaw diagram semantics (purePolicy action) initial node)
    chanceIndex
  exact heval.trans (initial_nodeLaw_chance action)

private theorem decision_on_support (action : Bool)
    (draw : (node : {node // node ∈ initial.frontier}) → diagram.Value node.1)
    (hdraw : draw ∈ (frontierLaw diagram semantics
      (purePolicy action) initial).support) :
    draw decisionIndex = action := by
  have hdecision := (independentProduct_support_iff
    (fun node => nodeLaw diagram semantics (purePolicy action) initial node)
    draw).mp hdraw decisionIndex
  simp only [decisionIndex, nodeLaw, purePolicy, diagram,
    PMF.support_pure] at hdecision
  exact Set.mem_singleton_iff.mp hdecision

private theorem native_play_eq_frontier_map (action : Bool) :
    (nativeBehavioralGameForm semantics).play (purePolicy action) =
      (frontierLaw diagram semantics (purePolicy action) initial).map
        (fun draw => (initial.extend draw).values) := by
  have hcard : Fintype.card Node = 2 := by decide
  rw [nativeBehavioralGameForm_play, hcard]
  show PMF.map (fun reached => reached.values)
      (run diagram semantics (purePolicy action) 2 initial) = _
  rw [run_two_eq_step, step, PMF.map_comp]
  rfl

private theorem exploding_not_integrable :
    ¬ PayoffIntegrable geometric exploding := by
  intro h
  apply exploding_not_summable
  have hnonneg (n : ℕ) : 0 ≤ exploding n := by
    unfold exploding
    positivity
  simpa only [PayoffIntegrable, abs_of_nonneg (hnonneg _)] using h

private theorem utility_on_supported_draw (action : Bool)
    (draw : (node : {node // node ∈ initial.frontier}) → diagram.Value node.1)
    (hdraw : draw ∈ (frontierLaw diagram semantics
      (purePolicy action) initial).support) :
    semantics.utility () (initial.extend draw).values =
      if action then exploding (chanceDraw draw) else 0 := by
  have hchance := FrontierState.extend_value_of_frontier initial draw chanceIndex
  have hdecision := FrontierState.extend_value_of_frontier initial draw decisionIndex
  have haction := decision_on_support action draw hdraw
  have hchance' : (initial.extend draw).values .chance = draw chanceIndex :=
    hchance
  have hdecision' : (initial.extend draw).values .decision = draw decisionIndex :=
    hdecision
  calc
    semantics.utility () (initial.extend draw).values =
        if (initial.extend draw).values .decision then
          exploding ((initial.extend draw).values .chance) else 0 := rfl
    _ = if action then exploding (chanceDraw draw) else 0 := by
      rw [hdecision', hchance', haction]
      rfl

def trueLaw : PMF (Assignment diagram) :=
  (nativeBehavioralGameForm semantics).play (purePolicy true)

def falseLaw : PMF (Assignment diagram) :=
  (nativeBehavioralGameForm semantics).play (purePolicy false)

/-- The incumbent's actual payoff is zero and therefore integrable. -/
theorem false_incumbent_integrable :
    PayoffIntegrable falseLaw (semantics.utility ()) := by
  let μ := frontierLaw diagram semantics (purePolicy false) initial
  have hzero : PayoffIntegrable μ (fun _ => (0 : ℝ)) :=
    payoffIntegrable_zero μ
  have hfrontier : PayoffIntegrable μ
      (fun draw => semantics.utility () (initial.extend draw).values) := by
    apply payoffIntegrable_congr_on_support
      (fun draw hdraw => by
        simpa using (utility_on_supported_draw false draw hdraw).symm)
    exact hzero
  have hmap : PayoffIntegrable
      (μ.map (fun draw => (initial.extend draw).values))
      (semantics.utility ()) :=
    (payoffIntegrable_map_iff _ μ _).mpr hfrontier
  exact payoffIntegrable_congr_law
    (show μ.map (fun draw => (initial.extend draw).values) = falseLaw from
      (native_play_eq_frontier_map false).symm) hmap

theorem false_incumbent_value_zero :
    expect falseLaw (semantics.utility ()) false_incumbent_integrable = 0 := by
  have hvalue : ∀ assignment ∈ falseLaw.support,
      semantics.utility () assignment = 0 := by
    intro assignment hassignment
    rw [falseLaw, native_play_eq_frontier_map false, PMF.support_map]
      at hassignment
    obtain ⟨draw, hdraw, rfl⟩ := hassignment
    simpa using utility_on_supported_draw false draw hdraw
  have hzero := expect_congr_on_support hvalue
    false_incumbent_integrable (payoffIntegrable_zero falseLaw)
  simpa only [expect_zero] using hzero

/-- The pure true deviation has an undefined actual expected payoff under the
infinite chance draw. -/
theorem true_deviation_not_integrable :
    ¬ PayoffIntegrable trueLaw (semantics.utility ()) := by
  intro hplay
  have hfrontier : PayoffIntegrable
      (frontierLaw diagram semantics (purePolicy true) initial)
      (fun draw => semantics.utility () (initial.extend draw).values) := by
    apply (payoffIntegrable_map_iff
      (fun draw => (initial.extend draw).values)
      (frontierLaw diagram semantics (purePolicy true) initial)
      (fun assignment => semantics.utility () assignment)).mp
    exact payoffIntegrable_congr_law
      (show trueLaw = _ from native_play_eq_frontier_map true) hplay
  have hexploding : PayoffIntegrable
      (frontierLaw diagram semantics (purePolicy true) initial)
      (fun draw => exploding (chanceDraw draw)) := by
    apply payoffIntegrable_congr_on_support
      (fun draw hdraw => by
        simpa using utility_on_supported_draw true draw hdraw)
    exact hfrontier
  let μ : PMF ((node : {node // node ∈ initial.frontier}) →
      diagram.Value node.1) :=
    frontierLaw diagram semantics (purePolicy true) initial
  have hμ : PayoffIntegrable μ (fun draw => exploding (chanceDraw draw)) :=
    hexploding
  have hmap : PayoffIntegrable (μ.map chanceDraw)
      exploding := by
    exact (payoffIntegrable_map_iff chanceDraw μ exploding).mpr hμ
  have heq : μ.map chanceDraw = geometric :=
    chance_marginal true
  exact exploding_not_integrable (payoffIntegrable_congr_law heq hmap)

/-- Nash fails because the actual true-policy deviation has no expected
utility, despite the incumbent's defined zero payoff. -/
theorem divergent_false_not_native_nash :
    ¬ IsNash (nativeBehavioralGameForm semantics)
      (euPreference fun assignment owner => semantics.utility owner assignment)
      (purePolicy false) := by
  intro hnash
  have hupdate : Profile.update (sig := nativeBehavioralSignature diagram)
      (purePolicy false) ()
      (purePolicy true ()) = purePolicy true := by
    funext owner
    cases owner
    exact Profile.update_same _ _ _
  obtain ⟨_, htrue, _⟩ :=
    (isNash_iff (F := nativeBehavioralGameForm semantics)
      (weaklyPrefers := euPreference
        fun assignment owner => semantics.utility owner assignment)
      (purePolicy false)).mp hnash () (purePolicy true ())
  apply true_deviation_not_integrable
  simpa only [hupdate, trueLaw] using htrue

theorem divergent_false_not_compiled_nash :
    ¬ IsNash (compiledBehavioralGameForm topological semantics)
      (euPreference fun assignment owner => semantics.utility owner assignment)
      (behavioralProfileEquiv topological semantics (purePolicy false)) := by
  intro hnash
  exact divergent_false_not_native_nash
    ((isNash_native_iff_compiled topological semantics (purePolicy false)).mpr hnash)

/-- Compilation preserves the entire native assignment law, not merely an
expected score, even when nature has infinite support. -/
theorem native_compiled_law (action : Bool) :
    (nativeBehavioralGameForm semantics).play (purePolicy action) =
      (compiledBehavioralGameForm topological semantics).play
        (behavioralProfileEquiv topological semantics (purePolicy action)) :=
  native_play_eq_compiled_play_equiv topological semantics (purePolicy action)

theorem bounded_native_compiled_nash (action : Bool) :
    IsNash (nativeBehavioralGameForm boundedSemantics)
        (euPreference fun assignment owner => boundedSemantics.utility owner assignment)
        (purePolicy action) ↔
      IsNash (compiledBehavioralGameForm topological boundedSemantics)
        (euPreference fun assignment owner => boundedSemantics.utility owner assignment)
        (behavioralProfileEquiv topological boundedSemantics (purePolicy action)) :=
  isNash_native_iff_compiled topological boundedSemantics (purePolicy action)

/-- Zero payoff gives a genuine Nash profile under an infinite chance law:
every actual comparison is integrable. -/
theorem bounded_native_nash (action : Bool) :
    IsNash (nativeBehavioralGameForm boundedSemantics)
      (euPreference fun assignment owner => boundedSemantics.utility owner assignment)
      (purePolicy action) := by
  rw [isNash_iff]
  intro who replacement
  rw [euPreference_apply]
  refine ⟨?_, ?_, ?_⟩
  · simpa [boundedSemantics] using
      (payoffIntegrable_zero
        ((nativeBehavioralGameForm boundedSemantics).play (purePolicy action)))
  · simpa [boundedSemantics] using
      (payoffIntegrable_zero
        ((nativeBehavioralGameForm boundedSemantics).play
          (Profile.update (purePolicy action) who replacement)))
  · simp [expectedUtility, boundedSemantics, expect_zero]

theorem bounded_compiled_nash (action : Bool) :
    IsNash (compiledBehavioralGameForm topological boundedSemantics)
      (euPreference fun assignment owner => boundedSemantics.utility owner assignment)
      (behavioralProfileEquiv topological boundedSemantics (purePolicy action)) :=
  (bounded_native_compiled_nash action).mp (bounded_native_nash action)

end GameTheory.Experimental.PMFMAIDGate
