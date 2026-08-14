/-
# Finite directed acyclic graphs

Game-independent relation and topological-order facts over arbitrary vertex
types. Finiteness and decidable equality are required only by order
construction.
-/

import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Order.WellFoundedSet

namespace GameTheoryMath.DAG

variable {α : Type*}

/-- A directed relation has no nonempty path from a vertex to itself. -/
def Acyclic (relation : α → α → Prop) : Prop :=
  ∀ vertex, ¬ Relation.TransGen relation vertex vertex

namespace Acyclic

variable {relation : α → α → Prop}

theorem asymm (hrelation : Acyclic relation) {first second : α}
    (hpath : Relation.TransGen relation first second) :
    ¬ Relation.TransGen relation second first :=
  fun hreturn => hrelation first (hpath.trans hreturn)

/-- Acyclicity becomes well-foundedness when the carrier is finite. -/
theorem wellFounded [Finite α] (hrelation : Acyclic relation) :
    WellFounded relation := by
  have : Std.Irrefl (Relation.TransGen relation) := ⟨hrelation⟩
  have : IsTrans α (Relation.TransGen relation) :=
    ⟨fun _ _ _ => Relation.TransGen.trans⟩
  exact (Finite.wellFounded_of_trans_of_irrefl
    (Relation.TransGen relation)).mono
      (fun _ _ edge => Relation.TransGen.single edge)

end Acyclic

/-- A list containing every vertex once, with each predecessor earlier than
its successor. The certificate itself stores no finite-carrier instance. -/
structure TopologicalOrder (predecessors : α → Finset α) where
  order : List α
  nodup : order.Nodup
  complete : ∀ vertex, vertex ∈ order
  respects : ∀ (index : Fin order.length),
    ∀ parent ∈ predecessors order[index],
      ∃ earlier : Fin order.length,
        earlier.val < index.val ∧ order[earlier] = parent

namespace TopologicalOrder

variable {predecessors : α → Finset α}

theorem predecessor_lt (topological : TopologicalOrder predecessors)
    {parent child : α} (hedge : parent ∈ predecessors child)
    {childIndex : Fin topological.order.length}
    (hchild : topological.order[childIndex] = child) :
    ∃ parentIndex : Fin topological.order.length,
      parentIndex.val < childIndex.val ∧
        topological.order[parentIndex] = parent := by
  exact topological.respects childIndex parent
    (by simpa only [hchild] using hedge)

/-- Every transitive predecessor occurs earlier than its descendant. -/
theorem ancestor_lt (topological : TopologicalOrder predecessors)
    {ancestor descendant : α}
    (hpath :
      Relation.TransGen (fun first second =>
        first ∈ predecessors second) ancestor descendant)
    {ancestorIndex descendantIndex : Fin topological.order.length}
    (hancestor : topological.order[ancestorIndex] = ancestor)
    (hdescendant : topological.order[descendantIndex] = descendant) :
    ancestorIndex.val < descendantIndex.val := by
  have index_eq : ∀ (first second : Fin topological.order.length),
      topological.order[first] = topological.order[second] →
        first = second :=
    fun first second heq => topological.nodup.get_inj_iff.mp heq
  suffices key : ∀ first second,
      Relation.TransGen
        (fun source target => source ∈ predecessors target)
        first second →
      ∀ (firstIndex secondIndex : Fin topological.order.length),
        topological.order[firstIndex] = first →
        topological.order[secondIndex] = second →
        firstIndex.val < secondIndex.val from
    key ancestor descendant hpath ancestorIndex descendantIndex
      hancestor hdescendant
  intro first second path
  induction path with
  | single hedge =>
      intro firstIndex secondIndex hfirst hsecond
      obtain ⟨parentIndex, hlt, hparent⟩ :=
        topological.respects secondIndex _
          (by simpa only [hsecond] using hedge)
      have heq := index_eq firstIndex parentIndex
        (hfirst.trans hparent.symm)
      simpa [heq] using hlt
  | tail firstMiddle middleSecond ih =>
      intro firstIndex secondIndex hfirst hsecond
      obtain ⟨middleIndex, hmiddleBound, hmiddle⟩ :=
        List.mem_iff_getElem.mp (topological.complete _)
      have hfirstMiddle := ih firstIndex ⟨middleIndex, hmiddleBound⟩
        hfirst hmiddle
      obtain ⟨parentIndex, hparentLt, hparent⟩ :=
        topological.respects secondIndex _
          (by simpa only [hsecond] using middleSecond)
      have heq := index_eq ⟨middleIndex, hmiddleBound⟩ parentIndex
        (hmiddle.trans hparent.symm)
      have hvalueEq : middleIndex = parentIndex.val :=
        congrArg Fin.val heq
      omega

end TopologicalOrder

/-- A topological order is an acyclicity certificate. -/
theorem acyclic_of_topologicalOrder
    {predecessors : α → Finset α}
    (topological : TopologicalOrder predecessors) :
    Acyclic (fun first second => first ∈ predecessors second) := by
  intro vertex hcycle
  obtain ⟨index, hbound, hvertex⟩ :=
    List.mem_iff_getElem.mp (topological.complete vertex)
  let vertexIndex : Fin topological.order.length := ⟨index, hbound⟩
  exact Nat.lt_irrefl _
    (topological.ancestor_lt hcycle
      (ancestorIndex := vertexIndex)
      (descendantIndex := vertexIndex) hvertex hvertex)

/-- Every finite acyclic predecessor relation has a topological order.

The proof repeatedly removes a well-founded-minimal remaining vertex. -/
theorem topologicalOrder_of_acyclic [Fintype α] [DecidableEq α]
    {predecessors : α → Finset α}
    (hacyclic :
      Acyclic (fun first second => first ∈ predecessors second)) :
    Nonempty (TopologicalOrder predecessors) := by
  classical
  have wellFounded := hacyclic.wellFounded
  suffices key : ∀ vertices : Finset α,
      ∃ order : List α,
        order.Nodup ∧
        order.toFinset = vertices ∧
        ∀ (index : Fin order.length) (parent : α),
          parent ∈ predecessors order[index] →
          parent ∈ vertices →
          ∃ earlier : Fin order.length,
            earlier.val < index.val ∧ order[earlier] = parent by
    obtain ⟨order, hnodup, hall, hrespects⟩ := key Finset.univ
    exact ⟨
      { order := order
        nodup := hnodup
        complete := fun vertex => by
          rw [← List.mem_toFinset, hall]
          exact Finset.mem_univ vertex
        respects := fun index parent hedge =>
          hrespects index parent hedge (Finset.mem_univ parent) }⟩
  intro vertices
  induction vertices using Finset.strongInductionOn with
  | _ vertices ih =>
      by_cases hnonempty : vertices.Nonempty
      · let minimal := wellFounded.min (vertices : Set α) hnonempty
        have hminimal : minimal ∈ vertices :=
          wellFounded.min_mem (vertices : Set α) hnonempty
        have hnoParent : ∀ parent ∈ vertices,
            parent ∉ predecessors minimal :=
          fun parent hparent hedge =>
            wellFounded.not_lt_min (vertices : Set α) hparent hedge
        let remaining := vertices.erase minimal
        have hremaining : remaining ⊂ vertices :=
          Finset.erase_ssubset hminimal
        obtain ⟨tail, htailNodup, htailVertices, htailRespects⟩ :=
          ih remaining hremaining
        refine ⟨minimal :: tail, ?_, ?_, ?_⟩
        · rw [List.nodup_cons]
          exact ⟨by
            rw [← List.mem_toFinset, htailVertices]
            exact Finset.notMem_erase minimal vertices,
            htailNodup⟩
        · simp only [List.toFinset_cons, htailVertices, remaining]
          exact Finset.insert_erase hminimal
        · intro ⟨index, hindex⟩ parent hedge hparent
          simp only [List.length_cons] at hindex
          match index, hindex, hedge with
          | 0, _, hedge =>
              exact absurd hedge (hnoParent parent hparent)
          | tailIndex + 1, htailIndex, hedge =>
              have htailBound : tailIndex < tail.length := by omega
              by_cases hisMinimal : parent = minimal
              · subst hisMinimal
                exact ⟨⟨0, Nat.succ_pos tail.length⟩,
                  Nat.succ_pos tailIndex, rfl⟩
              · have hparentRemaining : parent ∈ remaining :=
                  Finset.mem_erase.mpr ⟨hisMinimal, hparent⟩
                obtain ⟨earlier, hearlier, heq⟩ :=
                  htailRespects ⟨tailIndex, htailBound⟩ parent
                    hedge hparentRemaining
                exact ⟨
                  ⟨earlier.val + 1,
                    Nat.succ_lt_succ
                      (Nat.lt_of_lt_of_le earlier.isLt
                        (Nat.le_refl tail.length))⟩,
                  Nat.succ_lt_succ hearlier,
                  heq⟩
      · exact ⟨[], List.nodup_nil, by
          simp [Finset.not_nonempty_iff_eq_empty.mp hnonempty],
          fun ⟨index, hindex⟩ =>
            absurd hindex (by simp)⟩

end GameTheoryMath.DAG
