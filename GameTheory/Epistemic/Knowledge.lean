/-
# Finite S5 and common knowledge

The knowledge operator enumerates the state space, so finiteness is requested
by this module's operations rather than stored in `InfoPartition`.
-/

import GameTheory.Epistemic.Basic

noncomputable section

namespace GameTheory.Epistemic

universe uι uΩ

variable {Ω : Type uΩ} [DecidableEq Ω] [Fintype Ω]

/-- States at which the current information cell is contained in an event. -/
def Knows (partition : InfoPartition Ω) (event : Finset Ω) : Finset Ω :=
  Finset.univ.filter fun state => partition.cell state ⊆ event

@[simp]
theorem mem_Knows_iff (partition : InfoPartition Ω)
    (event : Finset Ω) (state : Ω) :
    state ∈ Knows partition event ↔ partition.cell state ⊆ event := by
  simp [Knows]

/-- S5 axiom T: knowing an event implies that it is true. -/
theorem Knows_subset (partition : InfoPartition Ω) (event : Finset Ω) :
    Knows partition event ⊆ event := by
  intro state hstate
  rw [mem_Knows_iff] at hstate
  exact hstate (partition.reflexive state)

/-- S5 axiom 4 in fixed-point form: knowing implies knowing that one knows. -/
theorem Knows_idem (partition : InfoPartition Ω) (event : Finset Ω) :
    Knows partition (Knows partition event) = Knows partition event := by
  apply Finset.Subset.antisymm
  · exact Knows_subset partition (Knows partition event)
  · intro state hstate
    rw [mem_Knows_iff] at hstate ⊢
    intro other hother
    rw [mem_Knows_iff, partition.coherent state other hother]
    exact hstate

/-- S5 axiom 5 in fixed-point form: not knowing implies knowing that one does
not know. -/
theorem Knows_not_Knows (partition : InfoPartition Ω) (event : Finset Ω) :
    Knows partition (Finset.univ \ Knows partition event) =
      Finset.univ \ Knows partition event := by
  apply Finset.Subset.antisymm
  · exact Knows_subset partition (Finset.univ \ Knows partition event)
  · intro state hstate
    rw [mem_Knows_iff]
    rw [Finset.mem_sdiff, mem_Knows_iff] at hstate
    intro other hother
    rw [Finset.mem_sdiff, mem_Knows_iff]
    refine ⟨Finset.mem_univ other, ?_⟩
    rw [partition.coherent state other hother]
    exact hstate.2

/-- Knowledge is monotone in its event. -/
theorem Knows_mono (partition : InfoPartition Ω)
    {smaller larger : Finset Ω} (hsubset : smaller ⊆ larger) :
    Knows partition smaller ⊆ Knows partition larger := by
  intro state hstate
  rw [mem_Knows_iff] at hstate ⊢
  exact hstate.trans hsubset

/-- Knowledge distributes over conjunction. -/
theorem Knows_inter (partition : InfoPartition Ω)
    (first second : Finset Ω) :
    Knows partition (first ∩ second) =
      Knows partition first ∩ Knows partition second := by
  ext state
  simp only [Finset.mem_inter, mem_Knows_iff, Finset.subset_inter_iff]

/-- Self-evidence means that truth of the event implies knowledge of it. -/
theorem isSelfEvident_iff_subset_Knows
    (partition : InfoPartition Ω) (event : Finset Ω) :
    IsSelfEvident partition event ↔ event ⊆ Knows partition event := by
  constructor
  · intro hself state hstate
    rw [mem_Knows_iff]
    exact hself state hstate
  · intro hsubset state hstate
    have hknows := hsubset hstate
    rw [mem_Knows_iff] at hknows
    exact hknows

/-- Self-evident events are exactly the fixed points of knowledge. -/
theorem isSelfEvident_iff_Knows_eq
    (partition : InfoPartition Ω) (event : Finset Ω) :
    IsSelfEvident partition event ↔ Knows partition event = event := by
  rw [isSelfEvident_iff_subset_Knows]
  exact ⟨fun hsubset =>
      Finset.Subset.antisymm (Knows_subset partition event) hsubset,
    fun hequal => hequal.ge⟩

/-! ## Common knowledge -/

/-- `event` is common knowledge at `state` when a public event containing the
state is self-evident for every agent and contained in `event`. -/
def CommonKnowledgeAt {ι : Type uι}
    (partition : ι → InfoPartition Ω) (event : Finset Ω)
    (state : Ω) : Prop :=
  ∃ publicEvent : Finset Ω,
    publicEvent ⊆ event ∧
      state ∈ publicEvent ∧
        ∀ agent, IsSelfEvident (partition agent) publicEvent

/-- The finite event at which `event` is common knowledge. -/
def CommonKnowledge {ι : Type uι}
    (partition : ι → InfoPartition Ω) (event : Finset Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter fun state =>
    CommonKnowledgeAt partition event state

omit [DecidableEq Ω] in
@[simp]
theorem mem_CommonKnowledge_iff {ι : Type uι}
    (partition : ι → InfoPartition Ω) (event : Finset Ω) (state : Ω) :
    state ∈ CommonKnowledge partition event ↔
      CommonKnowledgeAt partition event state := by
  simp [CommonKnowledge]

omit [DecidableEq Ω] [Fintype Ω] in
/-- Common knowledge implies truth. -/
theorem CommonKnowledgeAt.implies_mem {ι : Type uι}
    {partition : ι → InfoPartition Ω} {event : Finset Ω} {state : Ω}
    (h : CommonKnowledgeAt partition event state) :
    state ∈ event := by
  obtain ⟨publicEvent, hsubset, hstate, _⟩ := h
  exact hsubset hstate

/-- Common knowledge implies that every agent knows the event. -/
theorem CommonKnowledgeAt.implies_Knows {ι : Type uι}
    {partition : ι → InfoPartition Ω} {event : Finset Ω} {state : Ω}
    (h : CommonKnowledgeAt partition event state) (agent : ι) :
    state ∈ Knows (partition agent) event := by
  obtain ⟨publicEvent, hsubset, hstate, hself⟩ := h
  rw [mem_Knows_iff]
  exact (hself agent state hstate).trans hsubset

omit [DecidableEq Ω] in
/-- Common knowledge is positively introspective at the group level. -/
theorem CommonKnowledgeAt.idem {ι : Type uι}
    {partition : ι → InfoPartition Ω} {event : Finset Ω} {state : Ω}
    (h : CommonKnowledgeAt partition event state) :
    CommonKnowledgeAt partition (CommonKnowledge partition event) state := by
  obtain ⟨publicEvent, hsubset, hstate, hself⟩ := h
  refine ⟨publicEvent, ?_, hstate, hself⟩
  intro other hother
  rw [mem_CommonKnowledge_iff]
  exact ⟨publicEvent, hsubset, hother, hself⟩

end GameTheory.Epistemic
