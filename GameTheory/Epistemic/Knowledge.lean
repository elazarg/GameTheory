/-
# S5 knowledge and common knowledge

Knowledge is set-valued and does not enumerate the state space. Probability
enters only in posterior and agreement operations.
-/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Disjoint

noncomputable section

namespace GameTheory.Epistemic

universe uι uΩ

variable {Ω : Type uΩ}

/-- The states possible at `state` under a setoid information partition. -/
def cell (partition : Setoid Ω) (state : Ω) : Set Ω :=
  {other | partition.r state other}

/-- Membership in a cell determines the whole equivalence class. -/
theorem cell_eq_of_mem (partition : Setoid Ω) {state other : Ω}
    (hother : other ∈ cell partition state) :
    cell partition state = cell partition other := by
  ext candidate
  constructor
  · intro hcandidate
    exact partition.trans (partition.symm hother) hcandidate
  · intro hcandidate
    exact partition.trans hother hcandidate

/-- Distinct cells of a setoid partition are disjoint. -/
theorem cells_disjoint (partition : Setoid Ω) {first second : Ω}
    (hne : cell partition first ≠ cell partition second) :
    Disjoint (cell partition first) (cell partition second) := by
  rw [Set.disjoint_left]
  intro state hfirst hsecond
  apply hne
  calc
    cell partition first = cell partition state :=
      cell_eq_of_mem partition hfirst
    _ = cell partition second :=
      (cell_eq_of_mem partition hsecond).symm

/-- An event is self-evident when every cell meeting it is contained in it. -/
def IsSelfEvident (partition : Setoid Ω) (event : Set Ω) : Prop :=
  ∀ state ∈ event, cell partition state ⊆ event

/-- A cell outside a self-evident event is disjoint from that event. -/
theorem cell_disjoint_of_not_mem_selfEvident (partition : Setoid Ω)
    (event : Set Ω) (state : Ω) (hstate : state ∉ event)
    (hself : IsSelfEvident partition event) :
    Disjoint (cell partition state) event := by
  rw [Set.disjoint_left]
  intro other hcell hevent
  exact hstate (hself other hevent (partition.symm hcell))

/-- A self-evident event is the union of the cells it contains. -/
theorem selfEvident_eq_iUnion_cells (partition : Setoid Ω)
    {event : Set Ω} (hself : IsSelfEvident partition event) :
    event = {state | ∃ source, source ∈ event ∧
      state ∈ cell partition source} := by
  ext state
  constructor
  · intro hstate
    exact ⟨state, hstate, partition.refl state⟩
  · intro hstate
    obtain ⟨source, hsource, hcell⟩ := hstate
    exact hself source hsource hcell

/-- States at which the current information cell is contained in an event. -/
def Knows (partition : Setoid Ω) (event : Set Ω) : Set Ω :=
  {state | cell partition state ⊆ event}

@[simp]
theorem mem_Knows_iff (partition : Setoid Ω)
    (event : Set Ω) (state : Ω) :
    state ∈ Knows partition event ↔ cell partition state ⊆ event := Iff.rfl

/-- S5 axiom T: knowing an event implies that it is true. -/
theorem Knows_subset (partition : Setoid Ω) (event : Set Ω) :
    Knows partition event ⊆ event := by
  intro state hstate
  exact hstate (partition.refl state)

/-- S5 axiom 4 in fixed-point form: knowing implies knowing that one knows. -/
theorem Knows_idem (partition : Setoid Ω) (event : Set Ω) :
    Knows partition (Knows partition event) = Knows partition event := by
  apply Set.Subset.antisymm
  · exact Knows_subset partition (Knows partition event)
  · intro state hstate other hother
    rw [mem_Knows_iff, ← cell_eq_of_mem partition hother]
    exact (mem_Knows_iff partition event state).mp hstate

/-- S5 axiom 5 in fixed-point form: not knowing implies knowing that one does
not know. -/
theorem Knows_not_Knows (partition : Setoid Ω) (event : Set Ω) :
    Knows partition ((Set.univ : Set Ω) \ Knows partition event) =
      (Set.univ : Set Ω) \ Knows partition event := by
  apply Set.Subset.antisymm
  · exact Knows_subset partition _
  · intro state hstate other hother
    have hnot : state ∉ Knows partition event := hstate.2
    refine ⟨Set.mem_univ other, ?_⟩
    intro hknown
    apply hnot
    rw [mem_Knows_iff]
    intro candidate hcandidate
    have hcandidate' : candidate ∈ cell partition other := by
      rw [← cell_eq_of_mem partition hother]
      exact hcandidate
    exact hknown hcandidate'

/-- Knowledge is monotone in its event. -/
theorem Knows_mono (partition : Setoid Ω)
    {smaller larger : Set Ω} (hsubset : smaller ⊆ larger) :
    Knows partition smaller ⊆ Knows partition larger := by
  intro state hstate other hother
  exact hsubset (hstate hother)

/-- Knowledge distributes over conjunction. -/
theorem Knows_inter (partition : Setoid Ω)
    (first second : Set Ω) :
    Knows partition (first ∩ second) =
      Knows partition first ∩ Knows partition second := by
  ext state
  simp only [Set.mem_inter_iff, mem_Knows_iff, Set.subset_inter_iff]

/-- Self-evident events are exactly events known wherever they are true. -/
theorem isSelfEvident_iff_subset_Knows
    (partition : Setoid Ω) (event : Set Ω) :
    IsSelfEvident partition event ↔ event ⊆ Knows partition event := by
  constructor
  · intro hself state hstate
    exact hself state hstate
  · intro hsubset state hstate
    exact hsubset hstate

/-- Self-evident events are exactly the fixed points of knowledge. -/
theorem isSelfEvident_iff_Knows_eq
    (partition : Setoid Ω) (event : Set Ω) :
    IsSelfEvident partition event ↔ Knows partition event = event := by
  rw [isSelfEvident_iff_subset_Knows]
  exact ⟨fun hsubset => Set.Subset.antisymm (Knows_subset partition _) hsubset,
    fun hequal => hequal.ge⟩

/-! ## Common knowledge -/

/-- `event` is common knowledge at `state` when a public event containing the
state is self-evident for every agent and contained in `event`. -/
def CommonKnowledgeAt {ι : Type uι}
    (partition : ι → Setoid Ω) (event : Set Ω) (state : Ω) : Prop :=
  ∃ publicEvent : Set Ω,
    publicEvent ⊆ event ∧ state ∈ publicEvent ∧
      ∀ agent, IsSelfEvident (partition agent) publicEvent

/-- States at which `event` is common knowledge. -/
def CommonKnowledge {ι : Type uι}
    (partition : ι → Setoid Ω) (event : Set Ω) : Set Ω :=
  {state | CommonKnowledgeAt partition event state}

@[simp]
theorem mem_CommonKnowledge_iff {ι : Type uι}
    (partition : ι → Setoid Ω) (event : Set Ω) (state : Ω) :
    state ∈ CommonKnowledge partition event ↔
      CommonKnowledgeAt partition event state := Iff.rfl

/-- Common knowledge implies truth. -/
theorem CommonKnowledgeAt.implies_mem {ι : Type uι}
    {partition : ι → Setoid Ω} {event : Set Ω} {state : Ω}
    (h : CommonKnowledgeAt partition event state) : state ∈ event := by
  obtain ⟨publicEvent, hsubset, hstate, _⟩ := h
  exact hsubset hstate

/-- Common knowledge implies that every agent knows the event. -/
theorem CommonKnowledgeAt.implies_Knows {ι : Type uι}
    {partition : ι → Setoid Ω} {event : Set Ω} {state : Ω}
    (h : CommonKnowledgeAt partition event state) (agent : ι) :
    state ∈ Knows (partition agent) event := by
  obtain ⟨publicEvent, hsubset, hstate, hself⟩ := h
  exact (hself agent state hstate).trans hsubset

/-- Common knowledge is positively introspective at the group level. -/
theorem CommonKnowledgeAt.idem {ι : Type uι}
    {partition : ι → Setoid Ω} {event : Set Ω} {state : Ω}
    (h : CommonKnowledgeAt partition event state) :
    CommonKnowledgeAt partition (CommonKnowledge partition event) state := by
  obtain ⟨publicEvent, hsubset, hstate, hself⟩ := h
  refine ⟨publicEvent, ?_, hstate, hself⟩
  intro other hother
  exact ⟨publicEvent, hsubset, hother, hself⟩

end GameTheory.Epistemic
