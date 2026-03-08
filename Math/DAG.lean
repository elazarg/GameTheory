import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Nodup
import Mathlib.Order.WellFoundedSet

set_option autoImplicit false

/-!
# Directed Acyclic Graphs

General theory of directed acyclic graphs (DAGs) expressed as binary relations.

A relation `R : α → α → Prop` is **acyclic** when the transitive closure
`Relation.TransGen R` is irreflexive — equivalently, there is no directed cycle.

For finite DAGs on `Fin n` given by predecessor sets, we define **topological
orders** and prove the equivalence between acyclicity and existence of a
topological order.

## Main definitions

- `DAG.Acyclic R` — `R` has no directed cycles
- `DAG.TopologicalOrder preds` — a topological ordering of `Fin n`

## Main results

- `DAG.Acyclic.wellFounded` — an acyclic relation on a finite type is well-founded
- `DAG.acyclic_of_topologicalOrder` — a topological order witnesses acyclicity
- `DAG.topologicalOrder_of_acyclic` — acyclicity implies a topological order exists
-/

namespace DAG

variable {α : Type*}

-- ============================================================================
-- Acyclicity
-- ============================================================================

/-- A relation is acyclic when its transitive closure is irreflexive:
no element can reach itself via a non-empty sequence of `R`-steps. -/
def Acyclic (R : α → α → Prop) : Prop :=
  ∀ a, ¬ Relation.TransGen R a a

namespace Acyclic

variable {R : α → α → Prop}

/-- Reachability is asymmetric in an acyclic relation. -/
theorem asymm (hR : Acyclic R) {a b : α}
    (hab : Relation.TransGen R a b) : ¬ Relation.TransGen R b a :=
  fun hba => hR a (hab.trans hba)

/-- An acyclic relation on a finite type is well-founded. -/
theorem wellFounded [Finite α] (hR : Acyclic R) : WellFounded R := by
  have : Std.Irrefl (Relation.TransGen R) := ⟨hR⟩
  have : IsTrans α (Relation.TransGen R) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  exact (Finite.wellFounded_of_trans_of_irrefl (Relation.TransGen R)).mono
    (fun _ _ h => Relation.TransGen.single h)

end Acyclic

-- ============================================================================
-- Topological orders on Fin n
-- ============================================================================

/-- A topological order for a DAG on `Fin n`.

`preds nd` gives the set of predecessors of node `nd`. A topological order lists
all `n` nodes exactly once, with every predecessor appearing before its
successor. -/
structure TopologicalOrder {n : Nat} (preds : Fin n → Finset (Fin n)) where
  /-- The linear ordering of nodes. -/
  order : List (Fin n)
  /-- No duplicates. -/
  nodup : order.Nodup
  /-- Every node appears exactly once. -/
  length : order.length = n
  /-- Every predecessor appears earlier in the order. -/
  respects : ∀ (i : Fin order.length),
    ∀ p ∈ preds (order[i]),
      ∃ j : Fin order.length, j.val < i.val ∧ order[j] = p

namespace TopologicalOrder

variable {n : Nat} {preds : Fin n → Finset (Fin n)}

/-- Every node appears in a topological order. -/
theorem mem (σ : TopologicalOrder preds) (nd : Fin n) :
    nd ∈ σ.order := by
  have hfs : σ.order.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup σ.nodup, σ.length, Fintype.card_fin]
  rw [← List.mem_toFinset, hfs]
  exact Finset.mem_univ nd

end TopologicalOrder

-- ============================================================================
-- Acyclicity ↔ topological order existence
-- ============================================================================

/-- A topological order witnesses acyclicity: if there is a topological
order, then the predecessor relation has no directed cycles. -/
theorem acyclic_of_topologicalOrder {n : Nat} {preds : Fin n → Finset (Fin n)}
    (σ : TopologicalOrder preds) : Acyclic (fun a b => a ∈ preds b) := by
  -- We show: TransGen R x y implies any order index of x is less than
  -- any order index of y. Then TransGen R a a is impossible.
  suffices ∀ x y, Relation.TransGen (fun a b => a ∈ preds b) x y →
      ∀ (ix iy : Fin σ.order.length),
      σ.order[ix] = x → σ.order[iy] = y →
      ix.val < iy.val by
    intro a ha
    obtain ⟨ia, hia, hia_eq⟩ := List.mem_iff_getElem.mp (σ.mem a)
    exact Nat.lt_irrefl _ (this a a ha ⟨ia, hia⟩ ⟨ia, hia⟩ hia_eq hia_eq)
  -- In a Nodup list, equal values ⟹ equal Fin indices
  have idx_eq : ∀ (i j : Fin σ.order.length),
      σ.order[i] = σ.order[j] → i = j :=
    fun i j h => σ.nodup.get_inj_iff.mp h
  intro x y hxy
  induction hxy with
  | single hstep =>
    intro ix iy hix hiy
    subst hix; subst hiy
    obtain ⟨j, hj_lt, hj_eq⟩ := σ.respects iy _ hstep
    have := idx_eq ix j hj_eq.symm; omega
  | tail hab hbc ih =>
    intro ix iy hix hiy
    subst hiy
    obtain ⟨ib, hib, hib_eq⟩ := List.mem_iff_getElem.mp (σ.mem _)
    have hxb : ix.val < (⟨ib, hib⟩ : Fin σ.order.length).val :=
      ih ix ⟨ib, hib⟩ hix hib_eq
    obtain ⟨jb, hjb_lt, hjb_eq⟩ := σ.respects iy _ hbc
    have := idx_eq ⟨ib, hib⟩ jb (hib_eq.trans hjb_eq.symm); omega

/-- Acyclicity implies existence of a topological order.

On a finite set `Fin n`, if the predecessor relation `(· ∈ preds ·)` is acyclic,
then there exists a topological ordering. The proof constructs the order
greedily: at each step, pick a remaining node whose predecessors have all been
placed (such a node exists by well-foundedness). -/
theorem topologicalOrder_of_acyclic {n : Nat} {preds : Fin n → Finset (Fin n)}
    (hR : Acyclic (fun a b => a ∈ preds b)) :
    Nonempty (TopologicalOrder preds) := by
  classical
  have wf := hR.wellFounded
  -- For any S, build a list enumerating S with predecessors-within-S ordered.
  suffices key : ∀ (S : Finset (Fin n)),
      ∃ (l : List (Fin n)), l.Nodup ∧ l.toFinset = S ∧
        ∀ (i : Fin l.length) (p : Fin n), p ∈ preds l[i] → p ∈ S →
          ∃ j : Fin l.length, j.val < i.val ∧ l[j] = p by
    obtain ⟨l, hl_nd, hl_eq, hl_resp⟩ := key Finset.univ
    have hlen : l.length = n := by
      have := (List.toFinset_card_of_nodup hl_nd).symm
      rw [hl_eq, Finset.card_univ, Fintype.card_fin] at this; exact this
    exact ⟨⟨l, hl_nd, hlen,
      fun i p hp => hl_resp i p hp (Finset.mem_univ _)⟩⟩
  intro S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hne : S.Nonempty
    · -- Pick a WF-minimal element (source) from S
      set m := wf.min (S : Set (Fin n)) hne
      have hm_mem : m ∈ S := wf.min_mem (S : Set (Fin n)) hne
      have hm_min : ∀ y ∈ S, y ∉ preds m :=
        fun y hy h => wf.not_lt_min (S : Set (Fin n)) hne hy h
      set S' := S.erase m
      have hS'_lt : S' ⊂ S := Finset.erase_ssubset hm_mem
      obtain ⟨l', hl'_nd, hl'_eq, hl'_resp⟩ := ih S' hS'_lt
      refine ⟨m :: l', ?_, ?_, ?_⟩
      · -- Nodup
        rw [List.nodup_cons]
        exact ⟨by rw [← List.mem_toFinset, hl'_eq]; exact Finset.notMem_erase m S, hl'_nd⟩
      · -- toFinset = S
        simp only [List.toFinset_cons, hl'_eq, S']
        exact Finset.insert_erase hm_mem
      · -- Respects: predecessors within S appear earlier
        intro ⟨i, hi⟩ p hp hpS
        simp only [List.length_cons] at hi
        match i, hi, hp with
        | 0, _, hp =>
          -- Position 0 is m; it has no predecessors in S
          exact absurd hp (hm_min p hpS)
        | k + 1, hk, hp =>
          -- Position k+1: element is l'[k]
          have hk' : k < l'.length := by omega
          by_cases hpm : p = m
          · -- p = m, at position 0
            subst hpm
            exact ⟨⟨0, Nat.succ_pos l'.length⟩, Nat.succ_pos k, rfl⟩
          · -- p ∈ S', use IH
            have hpS' : p ∈ S' := Finset.mem_erase.mpr ⟨hpm, hpS⟩
            obtain ⟨j, hj_lt, hj_eq⟩ := hl'_resp ⟨k, hk'⟩ p hp (hl'_eq ▸ hpS')
            have hj_val_lt : j.val < k := hj_lt
            refine ⟨⟨j.val + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.isLt (Nat.le_refl _))⟩,
                    Nat.succ_lt_succ hj_val_lt, hj_eq⟩
    · -- S is empty
      exact ⟨[], List.nodup_nil, by simp [Finset.not_nonempty_iff_eq_empty.mp hne],
        fun ⟨i, hi⟩ => absurd hi (by simp)⟩

end DAG
