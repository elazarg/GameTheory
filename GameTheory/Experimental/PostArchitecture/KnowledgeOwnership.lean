/-
# EXP-043: epistemic ownership

The first half is the positive mathematical target: finite-cell epistemic
partitions and Aumann agreement over the canonical finite-support prior. The
second half is the ownership falsifier: Protocol information is history-local,
and a merging state can belong to two distinct information sets.
-/

import GameTheory.Protocol.Information

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.KnowledgeOwnership

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open ExecutionProtocol

universe uι uΩ

/-! ## The separate epistemic object -/

variable {Ω : Type uΩ}

/-- A finite-cell information partition. The state carrier itself need not
carry a stored finiteness capability. -/
structure InfoPartition (Ω : Type uΩ) where
  /-- The states considered possible at the current state. -/
  cell : Ω → Finset Ω
  /-- Truth lies in its own information cell. -/
  reflexive : ∀ state, state ∈ cell state
  /-- Membership in a cell determines that same cell. -/
  coherent :
    ∀ state other, other ∈ cell state → cell other = cell state

/-- Posterior probability of a finite event conditional on the current cell. -/
def posterior [DecidableEq Ω] (prior : FinDist Ω) (partition : InfoPartition Ω)
    (event : Finset Ω) (state : Ω) : ℝ :=
  (∑ other ∈ partition.cell state ∩ event, prior.prob other) /
    ∑ other ∈ partition.cell state, prior.prob other

/-- States in one cell have the same posterior. -/
theorem posterior_eq_of_mem_cell [DecidableEq Ω] (prior : FinDist Ω)
    (partition : InfoPartition Ω) (event : Finset Ω)
    (state other : Ω) (hother : other ∈ partition.cell state) :
    posterior prior partition event state =
      posterior prior partition event other := by
  simp only [posterior, partition.coherent state other hother]

/-- An event is self-evident when every cell meeting it is contained in it. -/
def IsSelfEvident (partition : InfoPartition Ω) (event : Finset Ω) : Prop :=
  ∀ state ∈ event, partition.cell state ⊆ event

/-- Distinct cells of a partition are disjoint. -/
theorem cells_disjoint (partition : InfoPartition Ω) {first second : Ω}
    (hne : partition.cell first ≠ partition.cell second) :
    Disjoint (partition.cell first) (partition.cell second) := by
  rw [Finset.disjoint_left]
  intro state hfirst hsecond
  apply hne
  rw [← partition.coherent first state hfirst,
    partition.coherent second state hsecond]

/-- A self-evident event is the disjoint union of the cells it contains. -/
theorem selfEvident_eq_biUnion_cells [DecidableEq Ω]
    (partition : InfoPartition Ω)
    {event : Finset Ω} (hself : IsSelfEvident partition event) :
    event = (event.image partition.cell).biUnion id := by
  ext state
  simp only [Finset.mem_biUnion, Finset.mem_image, id]
  refine ⟨fun hstate => ?_, ?_⟩
  · exact ⟨partition.cell state, ⟨state, hstate, rfl⟩,
      partition.reflexive state⟩
  · rintro ⟨_, ⟨source, hsource, rfl⟩, hstate⟩
    exact hself source hsource hstate

/-- Finite sums over a self-evident event decompose over its distinct cells. -/
theorem selfEvident_sum_decomp [DecidableEq Ω]
    (partition : InfoPartition Ω)
    {event : Finset Ω} (hself : IsSelfEvident partition event)
    (value : Ω → ℝ) :
    ∑ state ∈ event, value state =
      ∑ cell ∈ event.image partition.cell, ∑ state ∈ cell, value state := by
  have hdisjoint :
      (event.image partition.cell : Set (Finset Ω)).PairwiseDisjoint id := by
    intro first hfirst second hsecond hne
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hfirst hsecond
    obtain ⟨firstState, _, rfl⟩ := hfirst
    obtain ⟨secondState, _, rfl⟩ := hsecond
    exact cells_disjoint partition (fun h => hne h)
  conv_lhs => rw [selfEvident_eq_biUnion_cells partition hself]
  rw [Finset.sum_biUnion hdisjoint]
  rfl

/-- **Aumann full agreement.** On a common nonempty event that is
self-evident for both partitions, two posteriors that are constant throughout
that event are equal. -/
theorem aumann_full_agreement
    [DecidableEq Ω] (prior : FinDist Ω) (hfull : prior.FullSupport)
    (first second : InfoPartition Ω) (event : Finset Ω)
    {publicEvent : Finset Ω} (hnonempty : publicEvent.Nonempty)
    (hfirst : IsSelfEvident first publicEvent)
    (hsecond : IsSelfEvident second publicEvent)
    {firstReport secondReport : ℝ}
    (hfirstReport :
      ∀ state ∈ publicEvent,
        posterior prior first event state = firstReport)
    (hsecondReport :
      ∀ state ∈ publicEvent,
        posterior prior second event state = secondReport) :
    firstReport = secondReport := by
  have hprior_pos : ∀ state, 0 < prior.prob state :=
    fun state => FinDist.prob_pos_iff.mpr (hfull state)
  have hpublic_pos : 0 < ∑ state ∈ publicEvent, prior.prob state :=
    Finset.sum_pos (fun state _ => hprior_pos state) hnonempty
  have hcellIdentity : ∀ {partition : InfoPartition Ω} {report : ℝ},
      IsSelfEvident partition publicEvent →
      (∀ state ∈ publicEvent,
        posterior prior partition event state = report) →
      ∀ {cell : Finset Ω}, cell ∈ publicEvent.image partition.cell →
        ∑ state ∈ cell ∩ event, prior.prob state =
          report * ∑ state ∈ cell, prior.prob state := by
    intro partition report hself hreport cell hcell
    rw [Finset.mem_image] at hcell
    obtain ⟨state, hstate, hcellState⟩ := hcell
    have hposterior := hreport state hstate
    have hcell_pos : 0 < ∑ other ∈ partition.cell state, prior.prob other :=
      Finset.sum_pos (fun other _ => hprior_pos other)
        ⟨state, partition.reflexive state⟩
    have hquotient :
        (∑ other ∈ partition.cell state ∩ event, prior.prob other) /
            ∑ other ∈ partition.cell state, prior.prob other =
          report :=
      hposterior
    field_simp at hquotient
    rw [← hcellState]
    linarith
  have htotal : ∀ {partition : InfoPartition Ω} {report : ℝ},
      IsSelfEvident partition publicEvent →
      (∀ state ∈ publicEvent,
        posterior prior partition event state = report) →
      ∑ state ∈ publicEvent ∩ event, prior.prob state =
        report * ∑ state ∈ publicEvent, prior.prob state := by
    intro partition report hself hreport
    rw [selfEvident_sum_decomp partition hself prior.prob,
      Finset.mul_sum]
    have hinter :
        publicEvent ∩ event =
          (publicEvent.image partition.cell).biUnion
            (fun cell => cell ∩ event) := by
      conv_lhs => rw [selfEvident_eq_biUnion_cells partition hself]
      rw [Finset.biUnion_inter]
      rfl
    rw [hinter]
    have hdisjoint :
        (publicEvent.image partition.cell : Set (Finset Ω)).PairwiseDisjoint
          (fun cell => cell ∩ event) := by
      intro firstCell hfirstCell secondCell hsecondCell hne
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hfirstCell hsecondCell
      obtain ⟨firstState, _, rfl⟩ := hfirstCell
      obtain ⟨secondState, _, rfl⟩ := hsecondCell
      exact (cells_disjoint partition (fun h => hne h)).mono
        Finset.inter_subset_left Finset.inter_subset_left
    rw [Finset.sum_biUnion hdisjoint]
    exact Finset.sum_congr rfl fun cell hmem =>
      hcellIdentity hself hreport hmem
  have hfirstTotal := htotal hfirst hfirstReport
  have hsecondTotal := htotal hsecond hsecondReport
  have hequal :
      firstReport * ∑ state ∈ publicEvent, prior.prob state =
        secondReport * ∑ state ∈ publicEvent, prior.prob state := by
    rw [← hfirstTotal, ← hsecondTotal]
  exact mul_right_cancel₀ hpublic_pos.ne' hequal

/-! ## Why Protocol information is not this object -/

/-- One decision followed by a merged terminal state. -/
inductive MergeState
  | initial
  | merged

/-- Both actions reach the same execution state. -/
@[reducible]
def mergingExecution : ExecutionProtocol Unit where
  State := MergeState
  Action _ := Bool
  init := .initial
  active state _ :=
    match state with
    | .initial => True
    | .merged => False
  available _ _ := Set.univ
  terminal state :=
    match state with
    | .initial => False
    | .merged => True
  step state joint :=
    match state with
    | .initial => FinDist.pure .merged
    | .merged => False.elim (joint.2.1 trivial)
  progress := by
    intro state hterminal
    cases state with
    | initial =>
        exact ⟨fun _ => some false, fun _ =>
          ⟨trivial, Set.mem_univ _⟩⟩
    | merged =>
        exact False.elim (hterminal trivial)

/-- The player remembers which action led to the merged state. -/
inductive MergeView
  | acting
  | done (action : Bool)
  deriving DecidableEq

/-- History-local signals for the merging execution. -/
@[reducible]
def mergingSignals : InfoSignals mergingExecution where
  PublicSignal := Unit
  PrivateSignal _ := Unit
  initialPublic := ()
  initialPrivate _ := ()
  publicSignal _ := ()
  privateSignal _ _ := ()
  InfoState _ := MergeView
  initInfo _ _ _ := .acting
  pushInfo _ prior ownAction _ _ :=
    match ownAction with
    | some action => .done action
    | none => prior

/-- The local menu depends only on the history-local phase. -/
def mergingMenu (_ : Unit) : MergeView → Set (Option Bool)
  | .acting => { choice | ∃ action, choice = some action }
  | .done _ => {none}

/-- Menu adequacy holds even though the final execution state has two views. -/
theorem mergingMenu_adequate {state : mergingExecution.State}
    (trace : Trace mergingExecution state)
    (choice : Option Bool) :
    choice ∈ mergingMenu () (mergingSignals.infoOf () trace) ↔
      LegalOption mergingExecution state () choice := by
  cases trace with
  | start =>
      cases choice <;> simp [mergingMenu, LegalOption, mergingExecution]
  | @extend source target prior joint isLegal realized =>
      cases source with
      | merged =>
          exact False.elim (isLegal.1 trivial)
      | initial =>
          have htarget : state = MergeState.merged := by
            simpa [mergingExecution] using realized
          subst state
          have hjoint := isLegal.2 ()
          cases h : joint () with
          | none =>
              rw [h] at hjoint
              exact False.elim (hjoint trivial)
          | some action =>
              rw [InfoSignals.infoOf_extend]
              cases choice <;>
                simp [mergingMenu, LegalOption, mergingExecution, h]

/-- The accepted information model on the merging execution. -/
@[reducible]
def mergingInformation : InformationModel mergingExecution where
  toInfoSignals := mergingSignals
  menu := mergingMenu
  menu_adequate := by
    intro _ _ trace choice
    exact mergingMenu_adequate trace choice

/-- The legal joint action selecting `action`. -/
def mergeJoint (action : Bool) : ∀ _ : Unit, Option Bool :=
  fun _ => some action

theorem mergeJoint_legal (action : Bool) :
    mergingExecution.Legal .initial (mergeJoint action) :=
  ⟨by simp, fun _ =>
    ⟨trivial, Set.mem_univ _⟩⟩

theorem mergeJoint_realized (action : Bool) :
    MergeState.merged ∈
      (mergingExecution.step .initial
        ⟨mergeJoint action, mergeJoint_legal action⟩).support := by
  simp [mergingExecution]

/-- The history remembering one of the two actions. -/
def mergeTrace (action : Bool) : Trace mergingExecution .merged :=
  .extend .start (mergeJoint action) (mergeJoint_legal action)
    (mergeJoint_realized action)

@[simp]
theorem infoOf_mergeTrace (action : Bool) :
    mergingInformation.infoOf () (mergeTrace action) = .done action := rfl

/-- The one terminal execution state belongs to both distinct information
sets. Hence Protocol `InfoSet`s are not a partition of states in general. -/
theorem merged_mem_two_infoSets :
    MergeState.merged ∈
        mergingInformation.InfoSet () (.done false) ∩
      mergingInformation.InfoSet () (.done true) :=
  ⟨⟨mergeTrace false, infoOf_mergeTrace false⟩,
    ⟨mergeTrace true, infoOf_mergeTrace true⟩⟩

/-- No function of execution state alone can recover all history-local
information states of this valid model. -/
theorem no_state_view_represents_infoOf :
    ¬ ∃ view : MergeState → MergeView,
      ∀ {state : MergeState} (trace : Trace mergingExecution state),
        view state = mergingInformation.infoOf () trace := by
  rintro ⟨view, hview⟩
  have hfalse := hview (mergeTrace false)
  have htrue := hview (mergeTrace true)
  have hequal : MergeView.done false = .done true :=
    hfalse.symm.trans htrue
  cases hequal

end GameTheory.Experimental.PostArchitecture.KnowledgeOwnership
