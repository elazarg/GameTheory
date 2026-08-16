/-
# EXP-108: an infinite law above the canonical stochastic runner

The path at coordinate `n` is a canonical Protocol history certified to have
length `n`.  Its transition kernel is one step of `runBehavioralFrom`; this
file introduces no second evaluator.  Ionescu--Tulcea then supplies the
infinite law, and the main theorem identifies every chronological projection
with the existing fixed-horizon law.
-/

import GameTheory.Stochastic.History
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Integrals

noncomputable section

open scoped ENNReal

namespace GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure

open MeasureTheory ProbabilityTheory
open GameTheory.Math.Probability
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Stochastic

universe uι us ua

namespace Game

variable {ι : Type uι} (G : Stochastic.Game.{uι, us, ua} ι)

/-- The canonical Protocol history carrier used by the stochastic runner. -/
abbrev CanonicalHistory (initial : G.State) [∀ i, Nonempty (G.Action i)] :=
  (G.toExecution initial).History

/-- A canonical accumulated history at an exact stage index. -/
abbrev PathHistory (initial : G.State) [∀ i, Nonempty (G.Action i)]
    (n : ℕ) :=
  {history : CanonicalHistory G initial // history.trace.length = n}

@[reducible]
instance pathHistoryMeasurableSpace (initial : G.State)
    [∀ i, Nonempty (G.Action i)] (n : ℕ) :
    MeasurableSpace (PathHistory G initial n) :=
  ⊤

instance stageRecordMeasurableSpace : MeasurableSpace G.StageRecord := ⊤

/-- The exact-length empty canonical history. -/
def initialPathHistory (initial : G.State) [∀ i, Nonempty (G.Action i)] :
    PathHistory G initial 0 :=
  ⟨(G.toExecution initial).initHistory, rfl⟩

section FinitePlayers

variable [Fintype ι]
variable (initial : G.State) [∀ i, Nonempty (G.Action i)]
variable (profile : G.BehaviorProfile initial)

private theorem step_length (n : ℕ) (history : PathHistory G initial n)
    (result : CanonicalHistory G initial)
    (hresult : result ∈
      ((G.perfectMonitoring initial).runBehavioralFrom profile 1 history.1).support) :
    result.trace.length = n + 1 := by
  have hlength :=
    (G.toExecution initial).trace_length_eq_of_mem_support_runRandomizedFor
      ((G.perfectMonitoring initial).randomizedChooser profile)
      (fun state => by simp) 1 history.1 result hresult
  simpa [history.2] using hlength

/-- One canonical behavioral step, with the runner's length invariant retained. -/
def pathStepLaw (n : ℕ) (history : PathHistory G initial n) :
    FinDist (PathHistory G initial (n + 1)) :=
  ((G.perfectMonitoring initial).runBehavioralFrom profile 1 history.1).bindOnSupport
    fun result hresult =>
      FinDist.pure ⟨result, step_length G initial profile n history result hresult⟩

/-- The canonical horizon law with its exact trace length retained. -/
def finitePathHistoryLaw (n : ℕ) : FinDist (PathHistory G initial n) :=
  ((G.perfectMonitoring initial).runBehavioral profile n).bindOnSupport
    fun history hhistory =>
      FinDist.pure ⟨history, by
        have hlength :=
          (G.toExecution initial).trace_length_eq_of_mem_support_runRandomizedFor
            ((G.perfectMonitoring initial).randomizedChooser profile)
            (fun state => by simp) n (G.toExecution initial).initHistory
            history hhistory
        simpa [ExecutionProtocol.initHistory, Trace.length] using hlength⟩

private theorem map_val_pathStepLaw (n : ℕ)
    (history : PathHistory G initial n) :
    FinDist.map Subtype.val (pathStepLaw G initial profile n history) =
      (G.perfectMonitoring initial).runBehavioralFrom profile 1 history.1 := by
  unfold pathStepLaw
  rw [FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun result => FinDist.pure result)]
  · exact FinDist.bind_pure _
  · intro result hresult
    rw [FinDist.map_pure]

private theorem map_val_finitePathHistoryLaw (n : ℕ) :
    FinDist.map Subtype.val (finitePathHistoryLaw G initial profile n) =
      (G.perfectMonitoring initial).runBehavioral profile n := by
  unfold finitePathHistoryLaw
  rw [FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun history => FinDist.pure history)]
  · exact FinDist.bind_pure _
  · intro history hhistory
    rw [FinDist.map_pure]

private theorem finitePathHistoryLaw_zero :
    finitePathHistoryLaw G initial profile 0 =
      FinDist.pure (initialPathHistory G initial) := by
  apply FinDist.map_injective (f := Subtype.val) Subtype.val_injective
  rw [map_val_finitePathHistoryLaw G initial profile 0, FinDist.map_pure]
  unfold InformationModel.runBehavioral InformationModel.runBehavioralFrom
  rw [ExecutionProtocol.runRandomizedFor_zero]
  apply congrArg FinDist.pure
  rfl

private theorem finitePathHistoryLaw_succ (n : ℕ) :
    (finitePathHistoryLaw G initial profile n).bind
        (pathStepLaw G initial profile n) =
      finitePathHistoryLaw G initial profile (n + 1) := by
  apply FinDist.map_injective (f := Subtype.val) Subtype.val_injective
  rw [FinDist.map_bind,
    map_val_finitePathHistoryLaw G initial profile (n + 1)]
  simp_rw [map_val_pathStepLaw G initial profile n]
  unfold finitePathHistoryLaw
  rw [FinDist.bind_bindOnSupport]
  simp only [FinDist.pure_bind]
  rw [FinDist.bindOnSupport_eq_bind]
  unfold InformationModel.runBehavioral
  rw [← (G.perfectMonitoring initial).runBehavioralFrom_add
    profile n 1 (G.toExecution initial).initHistory]

/-- The measure kernel corresponding to one canonical runner step. -/
def pathStepKernel [Countable (CanonicalHistory G initial)] (n : ℕ) :
    Kernel (PathHistory G initial n) (PathHistory G initial (n + 1)) where
  toFun history := (pathStepLaw G initial profile n history).toPMF.toMeasure
  measurable' := Measurable.of_discrete

instance pathStepKernel_isMarkov [Countable (CanonicalHistory G initial)] (n : ℕ) :
    IsMarkovKernel (pathStepKernel G initial profile n) :=
  ⟨fun history => PMF.toMeasure.isProbabilityMeasure
    (pathStepLaw G initial profile n history).toPMF⟩

/-- Select the accumulated history at the end of a finite trajectory prefix. -/
def lastPathHistory (n : ℕ)
    (historyPrefix : ∀ i : Finset.Iic n, PathHistory G initial i) :
    PathHistory G initial n :=
  historyPrefix ⟨n, Finset.mem_Iic.mpr le_rfl⟩

omit [Fintype ι] in
private theorem measurable_lastPathHistory [Countable (CanonicalHistory G initial)]
    (n : ℕ) : Measurable (lastPathHistory G initial n) := by
  exact Measurable.of_discrete

/-- Ionescu--Tulcea's prefix kernel, factored through the latest history. -/
def trajectoryKernel [Countable (CanonicalHistory G initial)] (n : ℕ) :
    Kernel (∀ i : Finset.Iic n, PathHistory G initial i)
      (PathHistory G initial (n + 1)) :=
  pathStepKernel G initial profile n ∘ₖ
    Kernel.deterministic (lastPathHistory G initial n)
      (measurable_lastPathHistory G initial n)

instance trajectoryKernel_isMarkov [Countable (CanonicalHistory G initial)]
    (n : ℕ) : IsMarkovKernel (trajectoryKernel G initial profile n) := by
  unfold trajectoryKernel
  infer_instance

/-- The singleton initial prefix expected by `Kernel.traj`. -/
def initialPathPrefix :
    ∀ i : Finset.Iic 0, PathHistory G initial i :=
  (MeasurableEquiv.piUnique
    (fun i : Finset.Iic 0 => PathHistory G initial i)).symm
      (initialPathHistory G initial)

/-- One infinite play law induced by the canonical stochastic behavior profile. -/
def infinitePlayMeasure [Countable (CanonicalHistory G initial)]
    (behavior : G.BehaviorProfile initial) :
    Measure (∀ n, PathHistory G initial n) :=
  Kernel.traj (trajectoryKernel G initial behavior) 0
    (initialPathPrefix G initial)

instance infinitePlayMeasure_isProbability
    [Countable (CanonicalHistory G initial)] :
    IsProbabilityMeasure (infinitePlayMeasure G initial profile) := by
  unfold infinitePlayMeasure
  infer_instance

/-- Read the chronological stage records from one exact-length path history. -/
def chronologicalAt (n : ℕ) (history : PathHistory G initial n) :
    G.ChronologicalHistory n :=
  G.chronologicalOfPublicHistory
    (G.publicHistoryOfTrace initial history.1.trace)
    (by
      rw [G.publicHistoryOfTrace_length]
      exact history.2)

/-- Project an infinite canonical path to its first `n` chronological records. -/
def chronologicalProjection (n : ℕ) (play : ∀ k, PathHistory G initial k) :
    G.ChronologicalHistory n :=
  chronologicalAt G initial n (play n)

omit [Fintype ι] in
private theorem measurable_chronologicalAt
    [Countable (CanonicalHistory G initial)] (n : ℕ) :
    Measurable (chronologicalAt G initial n) :=
  Measurable.of_discrete

omit [Fintype ι] in
private theorem measurable_chronologicalProjection
    [Countable (CanonicalHistory G initial)] (n : ℕ) :
    Measurable (chronologicalProjection G initial n) := by
  exact (measurable_chronologicalAt G initial n).comp (measurable_pi_apply n)

end FinitePlayers

end Game

/-! ## The local finite-law-to-measure bridge -/

/-- The sanctioned local bridge from the library's finite law to a measure. -/
def finDistMeasure {α : Type*} [MeasurableSpace α]
    (law : FinDist α) : Measure α :=
  law.toPMF.toMeasure

private theorem finDistMeasure_pure {α : Type*} [MeasurableSpace α]
    (a : α) : finDistMeasure (FinDist.pure a) = Measure.dirac a := by
  exact PMF.toMeasure_pure a

private theorem finDistMeasure_map {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (law : FinDist α) (f : α → β) (hf : Measurable f) :
    (finDistMeasure law).map f = finDistMeasure (FinDist.map f law) := by
  unfold finDistMeasure
  rw [PMF.toMeasure_map (f := f) (p := law.toPMF) hf]
  rfl

private theorem finDistMeasure_bind {α β : Type*}
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (law : FinDist α) (next : α → FinDist β) :
    Measure.bind (finDistMeasure law) (fun a => finDistMeasure (next a)) =
      finDistMeasure (law.bind next) := by
  ext s hs
  unfold finDistMeasure
  rw [Measure.bind_apply hs Measurable.of_discrete.aemeasurable,
    MeasureTheory.lintegral_countable']
  simp only [FinDist.toPMF_bind]
  rw [PMF.toMeasure_bind_apply
    (p := law.toPMF) (f := fun a => (next a).toPMF) (s := s) hs]
  refine tsum_congr fun a => ?_
  rw [PMF.toMeasure_apply_singleton (p := law.toPMF) a
    (measurableSet_singleton a), mul_comm]

namespace Game

variable {ι : Type uι} (G : Stochastic.Game.{uι, us, ua} ι)
variable [Fintype ι]
variable (initial : G.State) [∀ i, Nonempty (G.Action i)]
variable (profile : G.BehaviorProfile initial)
variable [Countable (CanonicalHistory G initial)]

private theorem coordinate_zero :
    (infinitePlayMeasure G initial profile).map (fun play => play 0) =
      Measure.dirac (initialPathHistory G initial) := by
  let start : ∀ i : Finset.Iic 0, PathHistory G initial i :=
    initialPathPrefix G initial
  have hprefix := Kernel.traj_map_frestrictLe_apply
    (X := fun n => PathHistory G initial n)
    (κ := trajectoryKernel G initial profile) 0 0 start
  rw [Kernel.partialTraj_self, Kernel.id_apply] at hprefix
  unfold infinitePlayMeasure
  calc
    ((Kernel.traj (trajectoryKernel G initial profile) 0) start).map
          (fun play => play 0) =
        (((Kernel.traj (trajectoryKernel G initial profile) 0) start).map
          (Preorder.frestrictLe 0)).map
            (fun historyPrefix =>
              lastPathHistory G initial 0 historyPrefix) := by
      rw [Measure.map_map (measurable_lastPathHistory G initial 0)
        (Preorder.measurable_frestrictLe 0)]
      rfl
    _ = (Measure.dirac start).map
        (fun historyPrefix =>
          lastPathHistory G initial 0 historyPrefix) := by rw [hprefix]
    _ = Measure.dirac (initialPathHistory G initial) := by
      rw [Measure.map_dirac' (measurable_lastPathHistory G initial 0)]
      apply congrArg Measure.dirac
      exact Subtype.ext rfl

private theorem coordinate_succ (n : ℕ) :
    (infinitePlayMeasure G initial profile).map (fun play => play (n + 1)) =
      pathStepKernel G initial profile n ∘ₘ
        (infinitePlayMeasure G initial profile).map (fun play => play n) := by
  let law := infinitePlayMeasure G initial profile
  let restrict := Preorder.frestrictLe
    (π := fun k : ℕ => PathHistory G initial k) n
  have hprefix := Kernel.traj_map_frestrictLe_apply
    (X := fun k => PathHistory G initial k)
    (κ := trajectoryKernel G initial profile) 0 n
    (initialPathPrefix G initial)
  have hpair := Kernel.partialTraj_compProd_eq_map_traj
    (X := fun k => PathHistory G initial k)
    (κ := trajectoryKernel G initial profile) (a := 0) (b := n)
    (x₀ := initialPathPrefix G initial) (Nat.zero_le n)
  rw [← hprefix] at hpair
  have hsnd := congrArg Measure.snd hpair
  rw [Measure.snd_compProd] at hsnd
  have hpairMeasurable : Measurable
      (fun play : ∀ k, PathHistory G initial k =>
        (restrict play, play (n + 1))) := by
    fun_prop
  unfold Measure.snd at hsnd
  rw [Measure.map_map measurable_snd hpairMeasurable] at hsnd
  have hnext :
      trajectoryKernel G initial profile n ∘ₘ law.map restrict =
        law.map (fun play => play (n + 1)) := by
    exact hsnd
  have hlast :
      (law.map restrict).map (lastPathHistory G initial n) =
        law.map (fun play => play n) := by
    rw [Measure.map_map (measurable_lastPathHistory G initial n)
      (Preorder.measurable_frestrictLe n)]
    rfl
  rw [← hnext]
  unfold trajectoryKernel
  rw [← Measure.comp_assoc, Measure.deterministic_comp_eq_map, hlast]

private theorem pathStepKernel_comp_finiteLaw (n : ℕ) :
    pathStepKernel G initial profile n ∘ₘ
        finDistMeasure (finitePathHistoryLaw G initial profile n) =
      finDistMeasure
        ((finitePathHistoryLaw G initial profile n).bind
          (pathStepLaw G initial profile n)) := by
  exact finDistMeasure_bind
    (finitePathHistoryLaw G initial profile n)
    (pathStepLaw G initial profile n)

private theorem coordinate_finitePathHistoryLaw (n : ℕ) :
    (infinitePlayMeasure G initial profile).map (fun play => play n) =
      finDistMeasure (finitePathHistoryLaw G initial profile n) := by
  induction n with
  | zero =>
      rw [coordinate_zero G initial profile,
        finitePathHistoryLaw_zero G initial profile, finDistMeasure_pure]
  | succ n ih =>
      rw [coordinate_succ G initial profile n, ih,
        pathStepKernel_comp_finiteLaw G initial profile n,
        finitePathHistoryLaw_succ G initial profile n]

omit [Fintype ι] [∀ i, Nonempty (G.Action i)] in
private theorem publicHistoryOfChronological_injective (n : ℕ) :
    Function.Injective
      (fun history : G.ChronologicalHistory n =>
        G.publicHistoryOfChronological history) := by
  intro first second heq
  unfold GameTheory.Stochastic.Game.publicHistoryOfChronological at heq
  have hlists := List.reverse_injective heq
  have hvectors :
      (Equiv.vectorEquivFin G.StageRecord n).symm first =
        (Equiv.vectorEquivFin G.StageRecord n).symm second :=
    Subtype.ext hlists
  exact (Equiv.vectorEquivFin G.StageRecord n).symm.injective hvectors

omit [Countable (CanonicalHistory G initial)] in
private theorem map_chronologicalAt_finitePathHistoryLaw (n : ℕ) :
    FinDist.map (chronologicalAt G initial n)
        (finitePathHistoryLaw G initial profile n) =
      G.chronologicalHistoryLaw initial profile n := by
  apply FinDist.map_injective
    (publicHistoryOfChronological_injective G n)
  rw [FinDist.map_comp,
    G.map_publicHistoryOfChronological_chronologicalHistoryLaw]
  unfold finitePathHistoryLaw GameTheory.Stochastic.Game.publicHistoryLaw
  rw [FinDist.map_bindOnSupport]
  rw [FinDist.bindOnSupport_eq_bind_of_eq_on_support
    (g := fun history => FinDist.pure
      (G.publicHistoryOfTrace initial history.trace))]
  · rfl
  · intro history hhistory
    rw [FinDist.map_pure]
    apply congrArg FinDist.pure
    exact G.publicHistoryOfChronological_chronologicalOfPublicHistory _ _

/-- Every finite chronological projection is the existing canonical law. -/
theorem map_chronologicalProjection_infinitePlayMeasure (n : ℕ) :
    (infinitePlayMeasure G initial profile).map
        (chronologicalProjection G initial n) =
      finDistMeasure (G.chronologicalHistoryLaw initial profile n) := by
  have hprojection : chronologicalProjection G initial n =
      chronologicalAt G initial n ∘ fun play => play n := rfl
  rw [hprojection]
  rw [← Measure.map_map (measurable_chronologicalAt G initial n)
    (measurable_pi_apply n)]
  rw [coordinate_finitePathHistoryLaw G initial profile n]
  rw [finDistMeasure_map _ _ (measurable_chronologicalAt G initial n)]
  rw [map_chronologicalAt_finitePathHistoryLaw G initial profile n]

end Game

end GameTheory.Experimental.PostArchitecture.StochasticInfinitePlayMeasure
