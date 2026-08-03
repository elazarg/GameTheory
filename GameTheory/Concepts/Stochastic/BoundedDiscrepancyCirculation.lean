/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Chain
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic
import Math.Periodicity

/-!
# Bounded-discrepancy walks and zero-charge lassos

This file begins the exact finite kernel of Question 104.  A finite directed
multigraph is represented by a finite edge type with source and target maps,
so parallel edges retain their identities.  Charges take values in a finite
integer lattice.  This is the denominator-cleared form of finite rational
charge data.

The first theorem is the lattice pigeonhole step: an infinite walk whose
prefix-charge range is finite contains a reachable nonempty closed segment of
exactly zero charge.  The conclusion is packaged as a finite lasso
certificate (a transient prefix followed by a nonempty zero-charge closed
walk).  This is an offline existential result; it supplies no causal policy
against an adaptive edge chooser.
-/

noncomputable section

namespace GameTheory

namespace BoundedDiscrepancy

universe uV uE uκ

/-- A directed multigraph with explicit edge identities. -/
structure EdgeGraph (V : Type uV) (E : Type uE) where
  source : E → V
  target : E → V

namespace EdgeGraph

variable {V : Type uV} {E : Type uE} (G : EdgeGraph V E)

/-- A finite directed walk, retaining the list of edge identities. -/
inductive Walk (start : V) : V → Type (max uV uE)
  | nil : Walk start start
  | concat {finish : V} (walkSoFar : Walk start finish) (edge : E)
      (legal : G.source edge = finish) : Walk start (G.target edge)

namespace Walk

variable {G} {start finish middle previous base : V}

/-- Number of edges in a finite walk. -/
def length {start : V} : {finish : V} → G.Walk start finish → ℕ
  | _, .nil => 0
  | _, .concat walkSoFar _ _ => walkSoFar.length + 1

/-- Edge identities in chronological order. -/
def edges {start : V} : {finish : V} → G.Walk start finish → List E
  | _, .nil => []
  | _, .concat walkSoFar edge _ => walkSoFar.edges ++ [edge]

@[simp] theorem length_nil : (Walk.nil : G.Walk start start).length = 0 := rfl

@[simp] theorem length_concat (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).length = walkSoFar.length + 1 := rfl

@[simp] theorem edges_nil : (Walk.nil : G.Walk start start).edges = [] := rfl

@[simp] theorem edges_concat (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).edges = walkSoFar.edges ++ [edge] := rfl

@[simp] theorem edges_length (walk : G.Walk start finish) :
    walk.edges.length = walk.length := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih => simp [edges, length, ih]

/-- Consecutive edge identities in a typed walk have matching endpoints. -/
theorem edges_isChain (walk : G.Walk start finish) :
    walk.edges.IsChain fun first second => G.target first = G.source second := by
  induction walk with
  | nil => exact List.isChain_nil
  | @concat middle walkSoFar edge legal ih =>
      cases walkSoFar with
      | nil => exact List.isChain_singleton edge
      | @concat previous walkBefore finalEdge finalLegal =>
          rw [edges, List.isChain_append]
          refine ⟨ih, List.isChain_singleton edge, ?_⟩
          simp [edges, legal]

private theorem head_append_of_ne_nil (left right : List E)
    (hleft : left ≠ []) (happend : left ++ right ≠ []) :
    (left ++ right).head happend = left.head hleft := by
  cases left with
  | nil => exact (hleft rfl).elim
  | cons first rest => rfl

/-- The first edge of a nonempty typed walk starts at its initial vertex. -/
theorem source_head (walk : G.Walk start finish) (hne : walk.edges ≠ []) :
    G.source (walk.edges.head hne) = start := by
  induction walk with
  | nil => simp [edges] at hne
  | @concat middle walkSoFar edge legal ih =>
      cases walkSoFar with
      | nil => simpa [edges] using legal
      | @concat previous walkBefore finalEdge finalLegal =>
          have hleft : walkBefore.edges ++ [finalEdge] ≠ [] := by simp
          change G.source (((walkBefore.edges ++ [finalEdge]) ++ [edge]).head _) = start
          rw [head_append_of_ne_nil _ _ hleft]
          simpa only [edges] using ih hleft

/-- The last edge of a nonempty typed walk ends at its terminal vertex. -/
theorem target_getLast (walk : G.Walk start finish) (hne : walk.edges ≠ []) :
    G.target (walk.edges.getLast hne) = finish := by
  cases walk with
  | nil => simp [edges] at hne
  | concat walkSoFar edge legal => simp [edges]

/-- Total integer charge of a finite walk. -/
def charge {κ : Type uκ} (edgeCharge : E → κ → ℤ) {start : V} :
    {finish : V} → G.Walk start finish → κ → ℤ
  | _, .nil => 0
  | _, .concat walkSoFar edge _ => walkSoFar.charge edgeCharge + edgeCharge edge

@[simp] theorem charge_nil {κ : Type uκ} (edgeCharge : E → κ → ℤ) :
    (Walk.nil : G.Walk start start).charge edgeCharge = 0 := rfl

@[simp] theorem charge_concat {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).charge edgeCharge =
      walkSoFar.charge edgeCharge + edgeCharge edge := rfl

/-- The recursive charge agrees with summing the chronological edge list. -/
theorem charge_eq_sum_map {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    (walk : G.Walk start finish) :
    walk.charge edgeCharge = (walk.edges.map edgeCharge).sum := by
  induction walk with
  | nil => rfl
  | concat walkSoFar edge legal ih => simp [charge, edges, ih]

/-- Multiplicity of an edge identity in a finite walk. -/
def edgeMultiplicity [DecidableEq E] {start : V} : {finish : V} →
    G.Walk start finish → E → ℕ
  | _, .nil => 0
  | _, .concat walkSoFar edge _ => fun candidate =>
      walkSoFar.edgeMultiplicity candidate + if candidate = edge then 1 else 0

@[simp] theorem edgeMultiplicity_nil [DecidableEq E] (candidate : E) :
    (Walk.nil : G.Walk start start).edgeMultiplicity candidate = 0 := rfl

@[simp] theorem edgeMultiplicity_concat [DecidableEq E]
    (walkSoFar : G.Walk start finish) (edge candidate : E)
    (legal : G.source edge = finish) :
    (Walk.concat walkSoFar edge legal).edgeMultiplicity candidate =
      walkSoFar.edgeMultiplicity candidate + if candidate = edge then 1 else 0 := rfl

theorem edgeMultiplicity_pos_iff_mem_edges [DecidableEq E]
    (walk : G.Walk start finish) (edge : E) :
    0 < walk.edgeMultiplicity edge ↔ edge ∈ walk.edges := by
  induction walk with
  | nil => simp [edgeMultiplicity, edges]
  | concat walkSoFar finalEdge legal ih =>
      by_cases h : edge = finalEdge <;> simp [edgeMultiplicity, edges, ih, h]

theorem edgeMultiplicity_eq_count [DecidableEq E]
    (walk : G.Walk start finish) (edge : E) :
    walk.edgeMultiplicity edge = walk.edges.count edge := by
  induction walk with
  | nil => rfl
  | concat walkSoFar finalEdge legal ih =>
      by_cases h : edge = finalEdge
      · subst edge
        simp [edgeMultiplicity, edges, List.count_append, ih]
      · simp [edgeMultiplicity, edges, List.count_append, ih, h, eq_comm]

theorem edgeMultiplicity_eq_one_iff_mem_edges [DecidableEq E]
    (walk : G.Walk start finish) (hnodup : walk.edges.Nodup) (edge : E) :
    walk.edgeMultiplicity edge = 1 ↔ edge ∈ walk.edges := by
  rw [walk.edgeMultiplicity_eq_count]
  exact ⟨fun h => List.count_pos_iff.mp (by omega),
    fun h => List.count_eq_one_of_mem hnodup h⟩

theorem edgeMultiplicity_le_one [DecidableEq E]
    (walk : G.Walk start finish) (hnodup : walk.edges.Nodup) (edge : E) :
    walk.edgeMultiplicity edge ≤ 1 := by
  rw [walk.edgeMultiplicity_eq_count]
  exact (List.nodup_iff_count_le_one.mp hnodup) edge

/-- Change only the terminal index of a typed walk along an equality. -/
def castFinish {start finish finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') : G.Walk start finish' :=
  hfinish ▸ walk

@[simp] theorem length_castFinish {start finish finish' : V}
    (walk : G.Walk start finish) (hfinish : finish = finish') :
    (walk.castFinish hfinish).length = walk.length := by
  subst finish'
  rfl

@[simp] theorem edges_castFinish {start finish finish' : V}
    (walk : G.Walk start finish) (hfinish : finish = finish') :
    (walk.castFinish hfinish).edges = walk.edges := by
  subst finish'
  rfl

@[simp] theorem charge_castFinish {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    {start finish finish' : V} (walk : G.Walk start finish)
    (hfinish : finish = finish') :
    (walk.castFinish hfinish).charge edgeCharge = walk.charge edgeCharge := by
  subst finish'
  rfl

/-- Concatenate two typed walks at their common endpoint. -/
def append {start middle : V} (first : G.Walk start middle) :
    {finish : V} → G.Walk middle finish → G.Walk start finish
  | _, .nil => first
  | _, .concat second edge legal =>
      .concat (first.append second) edge legal

@[simp] theorem append_nil (first : G.Walk start middle) :
    first.append (.nil : G.Walk middle middle) = first := rfl

@[simp] theorem append_concat (first : G.Walk start middle)
    (second : G.Walk middle finish) (edge : E)
    (legal : G.source edge = finish) :
    first.append (.concat second edge legal) =
      .concat (first.append second) edge legal := rfl

@[simp] theorem edges_append (first : G.Walk start middle)
    (second : G.Walk middle finish) :
    (first.append second).edges = first.edges ++ second.edges := by
  induction second with
  | nil => simp
  | concat second edge legal ih => simp [ih, List.append_assoc]

@[simp] theorem length_append (first : G.Walk start middle)
    (second : G.Walk middle finish) :
    (first.append second).length = first.length + second.length := by
  induction second with
  | nil => simp
  | concat second edge legal ih => simp [ih, Nat.add_assoc]

@[simp] theorem charge_append {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    (first : G.Walk start middle) (second : G.Walk middle finish) :
    (first.append second).charge edgeCharge =
      first.charge edgeCharge + second.charge edgeCharge := by
  induction second with
  | nil => simp
  | concat second edge legal ih => simp [ih, add_assoc]

/-- The one-edge walk carrying a prescribed edge identity. -/
def singleton (edge : E) : G.Walk (G.source edge) (G.target edge) :=
  .concat .nil edge rfl

@[simp] theorem edges_singleton (edge : E) :
    (singleton (G := G) edge).edges = [edge] := rfl

@[simp] theorem length_singleton (edge : E) :
    (singleton (G := G) edge).length = 1 := rfl

/-- A typed decomposition of a walk at an occurrence of an edge. -/
theorem exists_splitAtEdge (walk : G.Walk start finish) (edge : E)
    (hmem : edge ∈ walk.edges) :
    ∃ (before : G.Walk start (G.source edge))
      (after : G.Walk (G.target edge) finish),
      walk.edges = before.edges ++ edge :: after.edges := by
  induction walk with
  | nil => simp at hmem
  | @concat middle walkSoFar finalEdge legal ih =>
      simp only [edges_concat, List.mem_append, List.mem_singleton] at hmem
      rcases hmem with hmem | heq
      · obtain ⟨before, after, hsplit⟩ := ih hmem
        refine ⟨before, after.concat finalEdge legal, ?_⟩
        simp only [edges_concat, hsplit]
        simp [List.append_assoc]
      · subst finalEdge
        exact ⟨walkSoFar.castFinish legal.symm, .nil, by simp⟩

/-- A witness that a typed walk passes through a specified vertex. -/
structure VertexSplit (walk : G.Walk start finish) (vertex : V) where
  before : G.Walk start vertex
  after : G.Walk vertex finish
  edges_eq : walk.edges = before.edges ++ after.edges

/-- The source of every used edge is a visited vertex. -/
noncomputable def vertexSplitAtSource (walk : G.Walk start finish) (edge : E)
    (hmem : edge ∈ walk.edges) : walk.VertexSplit (G.source edge) := by
  apply Classical.choice
  obtain ⟨before, after, hsplit⟩ := walk.exists_splitAtEdge edge hmem
  refine ⟨⟨before, (singleton (G := G) edge).append after, ?_⟩⟩
  simpa [List.append_assoc] using hsplit

/-- The target of every used edge is a visited vertex. -/
noncomputable def vertexSplitAtTarget (walk : G.Walk start finish) (edge : E)
    (hmem : edge ∈ walk.edges) : walk.VertexSplit (G.target edge) := by
  apply Classical.choice
  obtain ⟨before, after, hsplit⟩ := walk.exists_splitAtEdge edge hmem
  refine ⟨⟨before.append (singleton (G := G) edge), after, ?_⟩⟩
  simpa [List.append_assoc] using hsplit

namespace VertexSplit

/-- Insert a closed walk at a visited vertex. -/
def splice {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex) :
    G.Walk start finish :=
  (split.before.append inserted).append split.after

@[simp] theorem edges_splice {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex) :
    (split.splice inserted).edges =
      split.before.edges ++ inserted.edges ++ split.after.edges := by
  simp [splice, List.append_assoc]

theorem edges_splice_perm {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex) :
    (split.splice inserted).edges.Perm (walk.edges ++ inserted.edges) := by
  rw [split.edges_eq]
  simpa [List.append_assoc] using
    (List.Perm.refl split.before.edges).append
      (List.perm_append_comm :
        (inserted.edges ++ split.after.edges).Perm
          (split.after.edges ++ inserted.edges))

@[simp] theorem length_splice {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex) :
    (split.splice inserted).length = walk.length + inserted.length := by
  rw [← Walk.edges_length, ← Walk.edges_length, ← Walk.edges_length]
  simpa using (split.edges_splice_perm inserted).length_eq

end VertexSplit

end Walk

/-- Total multiplicity leaving a vertex. -/
def outgoingMultiplicity [Fintype E] [DecidableEq V]
    (multiplicity : E → ℕ) (vertex : V) : ℕ :=
  ∑ edge with G.source edge = vertex, multiplicity edge

/-- Total multiplicity entering a vertex. -/
def incomingMultiplicity [Fintype E] [DecidableEq V]
    (multiplicity : E → ℕ) (vertex : V) : ℕ :=
  ∑ edge with G.target edge = vertex, multiplicity edge

/-- Total charge carried by an integer edge multiplicity. -/
def multiplicityCharge (_G : EdgeGraph V E) [Fintype E] {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (multiplicity : E → ℕ) : κ → ℤ :=
  ∑ edge, multiplicity edge • edgeCharge edge

/-- Two edge identities meet in the underlying undirected support graph. -/
def SharesEndpoint (first second : E) : Prop :=
  G.source first = G.source second ∨ G.source first = G.target second ∨
    G.target first = G.source second ∨ G.target first = G.target second

/-- A finite traversal certificate for weak connectivity of a nonempty edge
support. Repetitions are allowed; every positive-support edge must occur. -/
def HasWalkConnectedSupport (multiplicity : E → ℕ) : Prop :=
  ∃ traversal : List E,
    traversal ≠ [] ∧
    (∀ edge, edge ∈ traversal ↔ 0 < multiplicity edge) ∧
    traversal.IsChain G.SharesEndpoint

private theorem exists_boundary_of_isChain
    {α : Type*} (relation : α → α → Prop)
    (hsymmetric : ∀ {first second}, relation first second → relation second first)
    (marked : α → Prop) (items : List α)
    (hchain : items.IsChain relation)
    (hmarked : ∃ item ∈ items, marked item)
    (hunmarked : ∃ item ∈ items, ¬ marked item) :
    ∃ first ∈ items, ∃ second ∈ items,
      marked first ∧ ¬ marked second ∧ relation first second := by
  induction items with
  | nil => simp at hmarked
  | cons first tail ih =>
      cases tail with
      | nil => simp_all
      | cons second rest =>
          have hrelation : relation first second :=
            (List.isChain_cons_cons.mp hchain).1
          have htailChain : (second :: rest).IsChain relation :=
            (List.isChain_cons_cons.mp hchain).2
          by_cases hfirst : marked first
          · by_cases hsecond : marked second
            · have htailUnmarked : ∃ item ∈ second :: rest, ¬ marked item := by
                obtain ⟨item, hitem, hunmarkedItem⟩ := hunmarked
                simp only [List.mem_cons] at hitem
                rcases hitem with rfl | hitem
                · exact (hunmarkedItem hfirst).elim
                · exact ⟨item, by simpa only [List.mem_cons] using hitem,
                    hunmarkedItem⟩
              obtain ⟨markedEdge, hmarkedMem, unmarkedEdge, hunmarkedMem,
                hmarkedEdge, hunmarkedEdge, hboundary⟩ :=
                  ih htailChain ⟨second, by simp, hsecond⟩ htailUnmarked
              exact ⟨markedEdge, by simp [hmarkedMem], unmarkedEdge,
              by simp [hunmarkedMem], hmarkedEdge, hunmarkedEdge, hboundary⟩
            · exact ⟨first, by simp, second, by simp, hfirst, hsecond, hrelation⟩
          · by_cases hsecond : marked second
            · exact ⟨second, by simp, first, by simp, hsecond, hfirst,
                hsymmetric hrelation⟩
            · have htailMarked : ∃ item ∈ second :: rest, marked item := by
                obtain ⟨item, hitem, hmarkedItem⟩ := hmarked
                simp only [List.mem_cons] at hitem
                rcases hitem with rfl | hitem
                · exact (hfirst hmarkedItem).elim
                · exact ⟨item, by simpa only [List.mem_cons] using hitem,
                    hmarkedItem⟩
              obtain ⟨markedEdge, hmarkedMem, unmarkedEdge, hunmarkedMem,
                hmarkedEdge, hunmarkedEdge, hboundary⟩ :=
                  ih htailChain htailMarked ⟨second, by simp, hsecond⟩
              exact ⟨markedEdge, by simp [hmarkedMem], unmarkedEdge,
                by simp [hunmarkedMem], hmarkedEdge, hunmarkedEdge, hboundary⟩

private theorem isChain_flatMap_of_nonempty
    {α β : Type*} (relation : α → α → Prop)
    (liftedRelation : β → β → Prop) (block : α → List β)
    (items : List α) (hitems : items.IsChain relation)
    (hnonempty : ∀ item ∈ items, block item ≠ [])
    (hblock : ∀ item ∈ items, (block item).IsChain liftedRelation)
    (hcross : ∀ {first second}, relation first second →
      ∀ x ∈ block first, ∀ y ∈ block second, liftedRelation x y) :
    (items.flatMap block).IsChain liftedRelation := by
  induction items with
  | nil => exact List.isChain_nil
  | cons first tail ih =>
      cases tail with
      | nil => simpa using hblock first (by simp)
      | cons second rest =>
          have hrelation : relation first second :=
            (List.isChain_cons_cons.mp hitems).1
          have htailChain : (second :: rest).IsChain relation :=
            (List.isChain_cons_cons.mp hitems).2
          have hsecondNonempty : block second ≠ [] :=
            hnonempty second (by simp)
          have htailNonempty :
              ∀ item ∈ second :: rest, block item ≠ [] := by
            intro item hitem
            exact hnonempty item (by simp [hitem])
          have htailBlock :
              ∀ item ∈ second :: rest,
                (block item).IsChain liftedRelation := by
            intro item hitem
            exact hblock item (by simp [hitem])
          have htailResult :
              ((second :: rest).flatMap block).IsChain liftedRelation :=
            ih htailChain htailNonempty htailBlock
          change
            (block first ++ (second :: rest).flatMap block).IsChain
              liftedRelation
          apply (hblock first (by simp)).append htailResult
          intro x hx y hy
          have hxMem : x ∈ block first := List.mem_of_mem_getLast? hx
          have hyInHead : y ∈ (block second).head? := by
            rw [show (second :: rest).flatMap block =
              block second ++ rest.flatMap block by rfl] at hy
            rw [List.head?_append_of_ne_nil _ hsecondNonempty] at hy
            exact hy
          exact hcross hrelation x hxMem y
            (List.mem_of_mem_head? hyInHead)

private theorem count_map_eq_sum_toFinset_ite
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (mapValue : α → β) (items : List α) (hnodup : items.Nodup)
    (value : β) :
    (items.map mapValue).count value =
      ∑ item ∈ items.toFinset,
        if mapValue item = value then 1 else 0 := by
  induction items with
  | nil => simp
  | cons first rest ih =>
      rw [List.nodup_cons] at hnodup
      simp only [List.map_cons, List.count_cons, List.toFinset_cons]
      rw [Finset.sum_insert (by simpa using hnodup.1), ih hnodup.2]
      by_cases hvalue : mapValue first = value
      · simp [hvalue]
        omega
      · simp [hvalue]

/-- A walk-connected positive support cannot be split into two nonempty edge
sets without a pair of positive-support edges sharing an endpoint across the
split. -/
theorem HasWalkConnectedSupport.exists_boundary
    (multiplicity : E → ℕ) (hconnected : G.HasWalkConnectedSupport multiplicity)
    (marked : Finset E)
    (hmarked : ∃ edge, 0 < multiplicity edge ∧ edge ∈ marked)
    (hunmarked : ∃ edge, 0 < multiplicity edge ∧ edge ∉ marked) :
    ∃ first second,
      0 < multiplicity first ∧ first ∈ marked ∧
       0 < multiplicity second ∧ second ∉ marked ∧
       G.SharesEndpoint first second := by
  classical
  obtain ⟨traversal, _, hsupport, hchain⟩ := hconnected
  have hmarkedTraversal : ∃ edge ∈ traversal, edge ∈ marked := by
    obtain ⟨edge, hpositive, hedgeMarked⟩ := hmarked
    exact ⟨edge, (hsupport edge).2 hpositive, hedgeMarked⟩
  have hunmarkedTraversal : ∃ edge ∈ traversal, edge ∉ marked := by
    obtain ⟨edge, hpositive, hedgeUnmarked⟩ := hunmarked
    exact ⟨edge, (hsupport edge).2 hpositive, hedgeUnmarked⟩
  obtain ⟨first, hfirstTraversal, second, hsecondTraversal,
    hfirstMarked, hsecondUnmarked, hshares⟩ :=
      exists_boundary_of_isChain G.SharesEndpoint
        (by
          intro first second h
          rcases h with h | h | h | h
          · exact Or.inl h.symm
          · exact Or.inr (Or.inr (Or.inl h.symm))
          · exact Or.inr (Or.inl h.symm)
          · exact Or.inr (Or.inr (Or.inr h.symm)))
        (fun edge => edge ∈ marked) traversal hchain
        hmarkedTraversal hunmarkedTraversal
  exact ⟨first, second, (hsupport first).1 hfirstTraversal, hfirstMarked,
    (hsupport second).1 hsecondTraversal, hsecondUnmarked, hshares⟩

/-- The `0`-`1` multiplicity of a finite edge set. -/
def edgeSetMultiplicity [DecidableEq E] (allowed : Finset E) : E → ℕ :=
  fun edge => if edge ∈ allowed then 1 else 0

@[simp] theorem edgeSetMultiplicity_pos_iff [DecidableEq E]
    (allowed : Finset E) (edge : E) :
    0 < edgeSetMultiplicity allowed edge ↔ edge ∈ allowed := by
  by_cases hedge : edge ∈ allowed <;> simp [edgeSetMultiplicity, hedge]

/-- Flow balance for a finite set of distinguishable edge tokens. -/
def IsBalancedEdgeSet [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) : Prop :=
  ∀ vertex,
    G.outgoingMultiplicity (edgeSetMultiplicity allowed) vertex =
      G.incomingMultiplicity (edgeSetMultiplicity allowed) vertex

/-- In a balanced edge set, any edge entering a vertex certifies that some
allowed edge also leaves that vertex. -/
theorem IsBalancedEdgeSet.exists_outgoing_of_mem_of_target_eq
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (edge : E) (hedge : edge ∈ allowed) (vertex : V)
    (htarget : G.target edge = vertex) :
    ∃ outgoing, outgoing ∈ allowed ∧ G.source outgoing = vertex := by
  have hincomingPositive :
      0 < G.incomingMultiplicity (edgeSetMultiplicity allowed) vertex := by
    unfold incomingMultiplicity
    rw [Finset.sum_pos_iff]
    refine ⟨edge, ?_, ?_⟩
    · simp [htarget]
    · simp [edgeSetMultiplicity, hedge]
  have houtgoingPositive :
      0 < G.outgoingMultiplicity (edgeSetMultiplicity allowed) vertex := by
    rw [hbalanced vertex]
    exact hincomingPositive
  unfold outgoingMultiplicity at houtgoingPositive
  rw [Finset.sum_pos_iff] at houtgoingPositive
  obtain ⟨outgoing, houtgoingFilter, houtgoingPositive⟩ := houtgoingPositive
  have hsource : G.source outgoing = vertex :=
    (Finset.mem_filter.mp houtgoingFilter).2
  have hallowed : outgoing ∈ allowed := by
    by_contra hnotAllowed
    simp [edgeSetMultiplicity, hnotAllowed] at houtgoingPositive
  exact ⟨outgoing, hallowed, hsource⟩

/-- A nonzero nonnegative integer circulation with zero total charge and a
finite certificate that its positive support is weakly connected. -/
structure ConnectedIntegerCirculation {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) [Fintype E] [DecidableEq V] where
  multiplicity : E → ℕ
  nonzero : ∃ edge, 0 < multiplicity edge
  balanced : ∀ vertex,
    G.outgoingMultiplicity multiplicity vertex =
      G.incomingMultiplicity multiplicity vertex
  charge_zero : G.multiplicityCharge edgeCharge multiplicity = 0
  connected : G.HasWalkConnectedSupport multiplicity

/-- A connected circulation together with an explicit finite route from the
prescribed start into its positive support. -/
structure ReachableConnectedIntegerCirculation {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) [Fintype E] [DecidableEq V]
    (start : V) extends G.ConnectedIntegerCirculation edgeCharge where
  entry : V
  initialWalk : G.Walk start entry
  entry_mem_support : ∃ edge, 0 < multiplicity edge ∧
    (G.source edge = entry ∨ G.target edge = entry)

/-- Distinguishable copies of an edge under a finite integer multiplicity. -/
abbrev MultiplicityToken (multiplicity : E → ℕ) :=
  Σ edge : E, Fin (multiplicity edge)

namespace MultiplicityToken

def edge {multiplicity : E → ℕ} (token : MultiplicityToken multiplicity) : E :=
  token.1

theorem card_filter_edge_eq_sum_filter [Fintype E]
    (multiplicity : E → ℕ) (predicate : E → Prop)
    [DecidablePred predicate] :
       (Finset.univ.filter
      (fun token : MultiplicityToken multiplicity => predicate token.edge)).card =
      ∑ edge with predicate edge, multiplicity edge := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ token : MultiplicityToken multiplicity,
    if predicate token.edge then 1 else 0) = _
  rw [Fintype.sum_sigma]
  conv_rhs => rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro edge _
  by_cases hedge : predicate edge <;>
    simp [MultiplicityToken.edge, hedge]

/-- All distinguishable copies of one original edge. -/
def listForEdge (multiplicity : E → ℕ) (edge : E) :
    List (MultiplicityToken multiplicity) :=
  List.ofFn fun index : Fin (multiplicity edge) => ⟨edge, index⟩

theorem listForEdge_ne_nil_of_pos (multiplicity : E → ℕ) (edge : E)
    (hpositive : 0 < multiplicity edge) :
    listForEdge multiplicity edge ≠ [] := by
  intro hempty
  have hlength := congrArg List.length hempty
  simp [listForEdge] at hlength
  omega

theorem edge_eq_of_mem_listForEdge {multiplicity : E → ℕ} {edge : E}
    {token : MultiplicityToken multiplicity}
    (hmem : token ∈ listForEdge multiplicity edge) :
    token.edge = edge := by
  rw [listForEdge, List.mem_ofFn'] at hmem
  obtain ⟨index, rfl⟩ := hmem
  rfl

theorem self_mem_listForEdge {multiplicity : E → ℕ}
    (token : MultiplicityToken multiplicity) :
    token ∈ listForEdge multiplicity token.edge := by
  rcases token with ⟨edge, index⟩
  rw [listForEdge, List.mem_ofFn']
  exact ⟨index, rfl⟩

theorem sum_ite_edge_eq (multiplicity : E → ℕ) [Fintype E]
    [DecidableEq E] (edge : E) :
    (∑ token : MultiplicityToken multiplicity,
      if token.edge = edge then 1 else 0) = multiplicity edge := by
  rw [Fintype.sum_sigma]
  rw [Finset.sum_eq_single edge]
  · simp [MultiplicityToken.edge]
  · intro other _ hne
    simp [MultiplicityToken.edge, hne]
  · simp

end MultiplicityToken

/-- Expand an integer edge multiplicity into a directed graph of
distinguishable edge tokens. -/
def tokenGraph (multiplicity : E → ℕ) :
    EdgeGraph V (MultiplicityToken multiplicity) where
  source token := G.source token.edge
  target token := G.target token.edge

@[simp] theorem tokenGraph_source (multiplicity : E → ℕ)
    (token : MultiplicityToken multiplicity) :
    (G.tokenGraph multiplicity).source token = G.source token.edge := rfl

@[simp] theorem tokenGraph_target (multiplicity : E → ℕ)
    (token : MultiplicityToken multiplicity) :
    (G.tokenGraph multiplicity).target token = G.target token.edge := rfl

theorem tokenGraph_outgoingMultiplicity_univ
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (multiplicity : E → ℕ) (vertex : V) :
    (G.tokenGraph multiplicity).outgoingMultiplicity
        (edgeSetMultiplicity (Finset.univ : Finset (MultiplicityToken multiplicity))) vertex =
      G.outgoingMultiplicity multiplicity vertex := by
  classical
  calc
    (G.tokenGraph multiplicity).outgoingMultiplicity
        (edgeSetMultiplicity
          (Finset.univ : Finset (MultiplicityToken multiplicity))) vertex =
        (Finset.univ.filter (fun token : MultiplicityToken multiplicity =>
          G.source token.edge = vertex)).card := by
            simp [outgoingMultiplicity, edgeSetMultiplicity]
    _ = ∑ edge with G.source edge = vertex, multiplicity edge :=
      MultiplicityToken.card_filter_edge_eq_sum_filter multiplicity
        (fun edge => G.source edge = vertex)
    _ = G.outgoingMultiplicity multiplicity vertex := rfl

theorem tokenGraph_incomingMultiplicity_univ
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (multiplicity : E → ℕ) (vertex : V) :
    (G.tokenGraph multiplicity).incomingMultiplicity
        (edgeSetMultiplicity (Finset.univ : Finset (MultiplicityToken multiplicity))) vertex =
      G.incomingMultiplicity multiplicity vertex := by
  classical
  calc
    (G.tokenGraph multiplicity).incomingMultiplicity
        (edgeSetMultiplicity
          (Finset.univ : Finset (MultiplicityToken multiplicity))) vertex =
        (Finset.univ.filter (fun token : MultiplicityToken multiplicity =>
          G.target token.edge = vertex)).card := by
            simp [incomingMultiplicity, edgeSetMultiplicity]
    _ = ∑ edge with G.target edge = vertex, multiplicity edge :=
      MultiplicityToken.card_filter_edge_eq_sum_filter multiplicity
        (fun edge => G.target edge = vertex)
    _ = G.incomingMultiplicity multiplicity vertex := rfl

theorem tokenGraph_univ_balanced_of_balanced
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (multiplicity : E → ℕ)
    (hbalanced : ∀ vertex,
      G.outgoingMultiplicity multiplicity vertex =
        G.incomingMultiplicity multiplicity vertex) :
    (G.tokenGraph multiplicity).IsBalancedEdgeSet Finset.univ := by
  intro vertex
  rw [G.tokenGraph_outgoingMultiplicity_univ multiplicity vertex,
    G.tokenGraph_incomingMultiplicity_univ multiplicity vertex]
  exact hbalanced vertex

theorem tokenGraph_listForEdge_isChain
    (multiplicity : E → ℕ) (edge : E) :
    (MultiplicityToken.listForEdge multiplicity edge).IsChain
      (G.tokenGraph multiplicity).SharesEndpoint := by
  rw [MultiplicityToken.listForEdge, List.isChain_ofFn]
  intro index hindex
  exact Or.inl rfl

theorem tokenGraph_sharesEndpoint_of_mem_listForEdge
    (multiplicity : E → ℕ) {first second : E}
    (hshares : G.SharesEndpoint first second)
    {firstToken secondToken : MultiplicityToken multiplicity}
    (hfirst : firstToken ∈ MultiplicityToken.listForEdge multiplicity first)
    (hsecond : secondToken ∈ MultiplicityToken.listForEdge multiplicity second) :
    (G.tokenGraph multiplicity).SharesEndpoint firstToken secondToken := by
  have hfirstEdge := MultiplicityToken.edge_eq_of_mem_listForEdge hfirst
  have hsecondEdge := MultiplicityToken.edge_eq_of_mem_listForEdge hsecond
  simpa [SharesEndpoint, hfirstEdge, hsecondEdge] using hshares

/-- Weak connectivity of the original positive support lifts to weak
connectivity of all distinguishable multiplicity tokens. -/
theorem tokenGraph_univ_hasWalkConnectedSupport
    [Fintype E] [DecidableEq E] (multiplicity : E → ℕ)
    (hnonzero : ∃ edge, 0 < multiplicity edge)
    (hconnected : G.HasWalkConnectedSupport multiplicity) :
    (G.tokenGraph multiplicity).HasWalkConnectedSupport
      (edgeSetMultiplicity
        (Finset.univ : Finset (MultiplicityToken multiplicity))) := by
  obtain ⟨traversal, _, hsupport, hchain⟩ := hconnected
  let block : E → List (MultiplicityToken multiplicity) :=
    MultiplicityToken.listForEdge multiplicity
  let tokenTraversal := traversal.flatMap block
  have hblockNonempty : ∀ edge ∈ traversal, block edge ≠ [] := by
    intro edge hedge
    exact MultiplicityToken.listForEdge_ne_nil_of_pos multiplicity edge
      ((hsupport edge).1 hedge)
  have hblockChain : ∀ edge ∈ traversal,
      (block edge).IsChain (G.tokenGraph multiplicity).SharesEndpoint := by
    intro edge _
    exact G.tokenGraph_listForEdge_isChain multiplicity edge
  have htokenChain :
      tokenTraversal.IsChain (G.tokenGraph multiplicity).SharesEndpoint := by
    exact isChain_flatMap_of_nonempty G.SharesEndpoint
      (G.tokenGraph multiplicity).SharesEndpoint block traversal hchain
      hblockNonempty hblockChain fun hshares firstToken hfirst secondToken hsecond =>
        G.tokenGraph_sharesEndpoint_of_mem_listForEdge multiplicity hshares
          hfirst hsecond
  have hall : ∀ token : MultiplicityToken multiplicity,
      token ∈ tokenTraversal := by
    intro token
    have hpositive : 0 < multiplicity token.edge := by
      exact Nat.zero_lt_of_lt token.2.isLt
    have hedgeTraversal : token.edge ∈ traversal :=
      (hsupport token.edge).2 hpositive
    apply List.mem_flatMap.mpr
    exact ⟨token.edge, hedgeTraversal,
      MultiplicityToken.self_mem_listForEdge token⟩
  have htokenNonempty : tokenTraversal ≠ [] := by
    obtain ⟨edge, hpositive⟩ := hnonzero
    let token : MultiplicityToken multiplicity :=
      ⟨edge, ⟨0, hpositive⟩⟩
    exact List.ne_nil_of_mem (hall token)
  refine ⟨tokenTraversal, htokenNonempty, ?_, htokenChain⟩
  intro token
  constructor
  · intro _
    exact (edgeSetMultiplicity_pos_iff Finset.univ token).2
      (Finset.mem_univ token)
  · intro _
    exact hall token

namespace Walk

variable {G} {start finish middle previous base : V}

/-- Forget token indices in a typed walk through the multiplicity-expanded
graph. -/
def detokenize (multiplicity : E → ℕ) {start : V} : {finish : V} →
    (G.tokenGraph multiplicity).Walk start finish → G.Walk start finish
  | _, .nil => .nil
  | _, .concat walkSoFar token legal =>
      .concat (detokenize multiplicity walkSoFar) token.edge legal

@[simp] theorem edges_detokenize (multiplicity : E → ℕ)
    (walk : (G.tokenGraph multiplicity).Walk start finish) :
    (walk.detokenize multiplicity).edges =
      walk.edges.map MultiplicityToken.edge := by
  induction walk with
  | nil => rfl
  | concat walkSoFar token legal ih =>
      change
        (detokenize multiplicity walkSoFar).edges ++ [token.edge] =
          (walkSoFar.edges ++ [token]).map MultiplicityToken.edge
      rw [ih, List.map_append]
      rfl

@[simp] theorem length_detokenize (multiplicity : E → ℕ)
    (walk : (G.tokenGraph multiplicity).Walk start finish) :
    (walk.detokenize multiplicity).length = walk.length := by
  rw [← Walk.edges_length, ← Walk.edges_length, edges_detokenize,
    List.length_map]

@[simp] theorem charge_detokenize {κ : Type uκ}
    (multiplicity : E → ℕ) (edgeCharge : E → κ → ℤ)
    (walk : (G.tokenGraph multiplicity).Walk start finish) :
    (walk.detokenize multiplicity).charge edgeCharge =
      walk.charge (fun token => edgeCharge token.edge) := by
  induction walk with
  | nil => rfl
  | concat walkSoFar token legal ih =>
      change
        (detokenize multiplicity walkSoFar).charge edgeCharge +
            edgeCharge token.edge =
          walkSoFar.charge (fun token => edgeCharge token.edge) +
            edgeCharge token.edge
      rw [ih]

/-- A token trail containing every distinguishable token detokenizes to the
prescribed original integer edge multiplicity. -/
theorem edgeMultiplicity_detokenize_of_nodup_all
    [Finite E] [DecidableEq E] (multiplicity : E → ℕ)
    (walk : (G.tokenGraph multiplicity).Walk start finish)
    (hnodup : walk.edges.Nodup)
    (hall : ∀ token : MultiplicityToken multiplicity, token ∈ walk.edges)
    (edge : E) :
    (walk.detokenize multiplicity).edgeMultiplicity edge =
      multiplicity edge := by
  letI : Fintype E := Fintype.ofFinite E
  rw [(walk.detokenize multiplicity).edgeMultiplicity_eq_count,
    edges_detokenize,
    count_map_eq_sum_toFinset_ite MultiplicityToken.edge walk.edges hnodup edge]
  have hfinset : walk.edges.toFinset = Finset.univ := by
    ext token
    simp [hall token]
  rw [hfinset]
  exact MultiplicityToken.sum_ite_edge_eq multiplicity edge

/-- A trail whose distinct edge identities all belong to `allowed`. -/
def IsTrailWithin [DecidableEq E] (walk : G.Walk start finish)
    (allowed : Finset E) : Prop :=
  walk.edges.Nodup ∧ ∀ edge ∈ walk.edges, edge ∈ allowed

/-- Splicing a residual closed trail into a trail preserves edge uniqueness
and the original allowed-edge bound. -/
theorem VertexSplit.isTrailWithin_splice [DecidableEq E]
    {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex)
    (allowed : Finset E) (hwalk : walk.IsTrailWithin allowed)
    (hinserted : inserted.IsTrailWithin (allowed \ walk.edges.toFinset)) :
    (split.splice inserted).IsTrailWithin allowed := by
  have hdisjoint : walk.edges.Disjoint inserted.edges := by
    rw [List.disjoint_left]
    intro edge hedgeWalk hedgeInserted
    have hresidual := hinserted.2 edge hedgeInserted
    exact (Finset.mem_sdiff.mp hresidual).2
      (List.mem_toFinset.mpr hedgeWalk)
  have hconcatNodup : (walk.edges ++ inserted.edges).Nodup :=
    List.nodup_append'.2 ⟨hwalk.1, hinserted.1, hdisjoint⟩
  constructor
  · exact (split.edges_splice_perm inserted).symm.nodup hconcatNodup
  · intro edge hedge
    have : edge ∈ walk.edges ++ inserted.edges :=
      (split.edges_splice_perm inserted).mem_iff.mp hedge
    rcases List.mem_append.mp this with hedgeWalk | hedgeInserted
    · exact hwalk.2 edge hedgeWalk
    · exact (Finset.mem_sdiff.mp (hinserted.2 edge hedgeInserted)).1

theorem VertexSplit.length_lt_splice
    {walk : G.Walk start finish} {vertex : V}
    (split : walk.VertexSplit vertex) (inserted : G.Walk vertex vertex)
    (hne : 0 < inserted.length) :
    walk.length < (split.splice inserted).length := by
  rw [split.length_splice]
  omega

theorem length_le_card_of_isTrailWithin [DecidableEq E]
    (walk : G.Walk start finish) (allowed : Finset E)
    (htrail : walk.IsTrailWithin allowed) :
    walk.length ≤ allowed.card := by
  have hsubset : walk.edges.toFinset ⊆ allowed := by
    intro edge hedge
    exact htrail.2 edge (List.mem_toFinset.mp hedge)
  calc
    walk.length = walk.edges.length := walk.edges_length.symm
    _ = walk.edges.toFinset.card := (List.toFinset_card_of_nodup htrail.1).symm
    _ ≤ allowed.card := Finset.card_le_card hsubset

/-- A longest allowed trail from a prescribed starting vertex exists because
no trail can use more than `allowed.card` distinct edges. -/
theorem exists_maximalTrailWithin [DecidableEq E]
    (allowed : Finset E) (start : V) :
    ∃ (finish : V) (walk : G.Walk start finish),
      walk.IsTrailWithin allowed ∧
      ∀ (finish' : V) (other : G.Walk start finish'),
        other.IsTrailWithin allowed → other.length ≤ walk.length := by
  classical
  let feasible : ℕ → Prop := fun length =>
    ∃ (finish : V) (walk : G.Walk start finish),
      walk.IsTrailWithin allowed ∧ walk.length = length
  have hzero : feasible 0 := by
    exact ⟨start, Walk.nil, ⟨by simp [Walk.edges], by simp [Walk.edges]⟩, rfl⟩
  let maximum := Nat.findGreatest feasible allowed.card
  have hmaximum : feasible maximum :=
    Nat.findGreatest_spec (Nat.zero_le _) hzero
  obtain ⟨finish, walk, htrail, hlength⟩ := hmaximum
  refine ⟨finish, walk, htrail, ?_⟩
  intro finish' other hother
  rw [hlength]
  exact Nat.le_findGreatest (other.length_le_card_of_isTrailWithin allowed hother)
    ⟨finish', other, hother, rfl⟩

theorem edgeMultiplicity_le_edgeSetMultiplicity [DecidableEq E]
    (walk : G.Walk start finish) (allowed : Finset E)
    (htrail : walk.IsTrailWithin allowed) (edge : E) :
    walk.edgeMultiplicity edge ≤ edgeSetMultiplicity allowed edge := by
  by_cases hedge : edge ∈ walk.edges
  · have hallowed : edge ∈ allowed := htrail.2 edge hedge
    rw [(walk.edgeMultiplicity_eq_one_iff_mem_edges htrail.1 edge).2 hedge]
    simp [edgeSetMultiplicity, hallowed]
  · have hzero : walk.edgeMultiplicity edge = 0 := by
      exact Nat.eq_zero_of_not_pos fun hpos =>
        hedge ((walk.edgeMultiplicity_pos_iff_mem_edges edge).1 hpos)
    simp [hzero]

/-- A longest allowed trail cannot leave an unused allowed edge at its
terminal vertex. -/
theorem edge_mem_of_maximalTrailWithin_of_source_eq
    [DecidableEq E] (allowed : Finset E) (walk : G.Walk start finish)
    (htrail : walk.IsTrailWithin allowed)
    (hmaximal : ∀ (finish' : V) (other : G.Walk start finish'),
      other.IsTrailWithin allowed → other.length ≤ walk.length)
    (edge : E) (hedgeAllowed : edge ∈ allowed)
    (hsource : G.source edge = finish) :
    edge ∈ walk.edges := by
  by_contra hedgeUnused
  let longer : G.Walk start (G.target edge) := Walk.concat walk edge hsource
  have hlongerTrail : longer.IsTrailWithin allowed := by
    constructor
    · change (walk.edges ++ [edge]).Nodup
      exact List.nodup_append'.2 ⟨htrail.1, List.nodup_singleton edge,
        List.disjoint_singleton.mpr hedgeUnused⟩
    · intro candidate hcandidate
      simp only [longer, Walk.edges, List.mem_append, List.mem_singleton] at hcandidate
      rcases hcandidate with hcandidate | rfl
      · exact htrail.2 candidate hcandidate
      · exact hedgeAllowed
  have hle := hmaximal _ longer hlongerTrail
  simp [longer, Walk.length] at hle

/-- On outgoing edges of the terminal vertex, maximality identifies the
trail multiplicity with the allowed-edge indicator. -/
theorem outgoingMultiplicity_eq_edgeSetMultiplicity_of_maximal
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (walk : G.Walk start finish)
    (htrail : walk.IsTrailWithin allowed)
    (hmaximal : ∀ (finish' : V) (other : G.Walk start finish'),
      other.IsTrailWithin allowed → other.length ≤ walk.length) :
    G.outgoingMultiplicity walk.edgeMultiplicity finish =
      G.outgoingMultiplicity (edgeSetMultiplicity allowed) finish := by
  classical
  unfold outgoingMultiplicity
  apply Finset.sum_congr rfl
  intro edge hedge
  have hsource : G.source edge = finish := (Finset.mem_filter.mp hedge).2
  by_cases hallowed : edge ∈ allowed
  · have hmem := walk.edge_mem_of_maximalTrailWithin_of_source_eq
      allowed htrail hmaximal edge hallowed hsource
    rw [(walk.edgeMultiplicity_eq_one_iff_mem_edges htrail.1 edge).2 hmem]
    simp [edgeSetMultiplicity, hallowed]
  · have hnotmem : edge ∉ walk.edges := fun hmem =>
      hallowed (htrail.2 edge hmem)
    have hzero : walk.edgeMultiplicity edge = 0 := by
      exact Nat.eq_zero_of_not_pos fun hpos =>
        hnotmem ((walk.edgeMultiplicity_pos_iff_mem_edges edge).1 hpos)
    simp [edgeSetMultiplicity, hallowed, hzero]

theorem incomingMultiplicity_le_edgeSetMultiplicity_of_trail
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (walk : G.Walk start finish)
    (htrail : walk.IsTrailWithin allowed) (vertex : V) :
    G.incomingMultiplicity walk.edgeMultiplicity vertex ≤
      G.incomingMultiplicity (edgeSetMultiplicity allowed) vertex := by
  classical
  unfold incomingMultiplicity
  exact Finset.sum_le_sum fun edge _ =>
    walk.edgeMultiplicity_le_edgeSetMultiplicity allowed htrail edge

@[simp] theorem outgoingMultiplicity_edgeMultiplicity_nil
    [Fintype E] [DecidableEq E] [DecidableEq V] (vertex : V) :
    G.outgoingMultiplicity
      ((Walk.nil : G.Walk start start).edgeMultiplicity) vertex = 0 := by
  simp [outgoingMultiplicity]

@[simp] theorem incomingMultiplicity_edgeMultiplicity_nil
    [Fintype E] [DecidableEq E] [DecidableEq V] (vertex : V) :
    G.incomingMultiplicity
      ((Walk.nil : G.Walk start start).edgeMultiplicity) vertex = 0 := by
  simp [incomingMultiplicity]

theorem outgoingMultiplicity_edgeMultiplicity_concat
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) (vertex : V) :
    G.outgoingMultiplicity (Walk.concat walkSoFar edge legal).edgeMultiplicity vertex =
      G.outgoingMultiplicity walkSoFar.edgeMultiplicity vertex +
        if G.source edge = vertex then 1 else 0 := by
  classical
  simp [outgoingMultiplicity, edgeMultiplicity, Finset.sum_add_distrib]

theorem incomingMultiplicity_edgeMultiplicity_concat
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walkSoFar : G.Walk start finish) (edge : E)
    (legal : G.source edge = finish) (vertex : V) :
    G.incomingMultiplicity (Walk.concat walkSoFar edge legal).edgeMultiplicity vertex =
      G.incomingMultiplicity walkSoFar.edgeMultiplicity vertex +
        if G.target edge = vertex then 1 else 0 := by
  classical
  simp [incomingMultiplicity, edgeMultiplicity, Finset.sum_add_distrib]

theorem multiplicityCharge_edgeMultiplicity
    [Fintype E] [DecidableEq E] {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (walk : G.Walk start finish) :
    G.multiplicityCharge edgeCharge walk.edgeMultiplicity =
      walk.charge edgeCharge := by
  induction walk with
  | nil => simp [multiplicityCharge]
  | concat walkSoFar edge legal ih =>
      funext coordinate
      simp only [multiplicityCharge, edgeMultiplicity, Walk.charge_concat,
        Pi.add_apply, Finset.sum_apply, nsmul_eq_mul]
      simp_rw [Nat.cast_add, add_mul, Pi.add_apply, Pi.mul_apply]
      have ihCoordinate := congrFun ih coordinate
      simp only [multiplicityCharge, Finset.sum_apply, nsmul_eq_mul,
        Pi.mul_apply] at ihCoordinate
      rw [Finset.sum_add_distrib, ihCoordinate]
      simp

/-- Endpoint-corrected flow conservation for every finite typed walk. -/
theorem edgeMultiplicity_flow_with_endpoints
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walk : G.Walk start finish) (vertex : V) :
    G.outgoingMultiplicity walk.edgeMultiplicity vertex +
        (if finish = vertex then 1 else 0) =
      G.incomingMultiplicity walk.edgeMultiplicity vertex +
        (if start = vertex then 1 else 0) := by
  induction walk with
  | nil => simp
  | @concat middle walkSoFar edge legal ih =>
      rw [outgoingMultiplicity_edgeMultiplicity_concat,
        incomingMultiplicity_edgeMultiplicity_concat, legal]
      omega

/-- Edge multiplicities of a closed typed walk are balanced at every
vertex. -/
theorem edgeMultiplicity_balanced
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (walk : G.Walk base base) (vertex : V) :
    G.outgoingMultiplicity walk.edgeMultiplicity vertex =
      G.incomingMultiplicity walk.edgeMultiplicity vertex := by
  have hflow := walk.edgeMultiplicity_flow_with_endpoints vertex
  omega

/-- A maximal trail in a balanced allowed edge set returns to its start. -/
theorem maximalTrailWithin_isClosed
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (walk : G.Walk start finish) (htrail : walk.IsTrailWithin allowed)
    (hmaximal : ∀ (finish' : V) (other : G.Walk start finish'),
      other.IsTrailWithin allowed → other.length ≤ walk.length) :
    finish = start := by
  by_contra hfinish
  have hflow := walk.edgeMultiplicity_flow_with_endpoints finish
  have hout := walk.outgoingMultiplicity_eq_edgeSetMultiplicity_of_maximal
    allowed htrail hmaximal
  have hin := walk.incomingMultiplicity_le_edgeSetMultiplicity_of_trail
    allowed htrail finish
  have hallowedBalance := hbalanced finish
  have hstartFinish : start ≠ finish := Ne.symm hfinish
  simp [hstartFinish] at hflow
  omega

/-- From any vertex with an allowed outgoing edge, a balanced finite edge set
contains a nonempty closed trail based at that vertex. -/
theorem exists_nonempty_closedTrailWithin_of_exists_outgoing
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (start : V)
    (houtgoing : ∃ edge, edge ∈ allowed ∧ G.source edge = start) :
    ∃ walk : G.Walk start start,
      walk.IsTrailWithin allowed ∧ 0 < walk.length := by
  obtain ⟨finish, walk, htrail, hmaximal⟩ :=
    Walk.exists_maximalTrailWithin (G := G) allowed start
  have hclosed : finish = start :=
    walk.maximalTrailWithin_isClosed allowed hbalanced htrail hmaximal
  subst finish
  obtain ⟨edge, hedgeAllowed, hsource⟩ := houtgoing
  have hedgeMem := walk.edge_mem_of_maximalTrailWithin_of_source_eq
    allowed htrail hmaximal edge hedgeAllowed hsource
  have hlength : 0 < walk.length := by
    rw [← walk.edges_length, List.length_pos_iff]
    exact List.ne_nil_of_mem hedgeMem
  exact ⟨walk, htrail, hlength⟩

theorem edgeSetMultiplicity_decompose_trail
    [DecidableEq E] (allowed : Finset E) (walk : G.Walk start finish)
    (htrail : walk.IsTrailWithin allowed) (edge : E) :
    edgeSetMultiplicity allowed edge =
      walk.edgeMultiplicity edge +
        edgeSetMultiplicity (allowed \ walk.edges.toFinset) edge := by
  by_cases hmem : edge ∈ walk.edges
  · have hallowed := htrail.2 edge hmem
    have hone := (walk.edgeMultiplicity_eq_one_iff_mem_edges htrail.1 edge).2 hmem
    simp [edgeSetMultiplicity, hallowed, hmem, hone]
  · have hzero : walk.edgeMultiplicity edge = 0 := by
      exact Nat.eq_zero_of_not_pos fun hpos =>
        hmem ((walk.edgeMultiplicity_pos_iff_mem_edges edge).1 hpos)
    simp [edgeSetMultiplicity, hmem, hzero]

/-- Removing the edges of a closed allowed trail preserves balance of the
remaining distinguishable edge set. -/
theorem isBalancedEdgeSet_sdiff_closedTrail
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (walk : G.Walk base base) (htrail : walk.IsTrailWithin allowed) :
    G.IsBalancedEdgeSet (allowed \ walk.edges.toFinset) := by
  intro vertex
  have houtDecompose :
      G.outgoingMultiplicity (edgeSetMultiplicity allowed) vertex =
        G.outgoingMultiplicity walk.edgeMultiplicity vertex +
          G.outgoingMultiplicity
            (edgeSetMultiplicity (allowed \ walk.edges.toFinset)) vertex := by
    unfold outgoingMultiplicity
    simp_rw [edgeSetMultiplicity_decompose_trail allowed walk htrail]
    exact Finset.sum_add_distrib
  have hinDecompose :
      G.incomingMultiplicity (edgeSetMultiplicity allowed) vertex =
        G.incomingMultiplicity walk.edgeMultiplicity vertex +
          G.incomingMultiplicity
            (edgeSetMultiplicity (allowed \ walk.edges.toFinset)) vertex := by
    unfold incomingMultiplicity
    simp_rw [edgeSetMultiplicity_decompose_trail allowed walk htrail]
    exact Finset.sum_add_distrib
  have hwalkBalance := walk.edgeMultiplicity_balanced vertex
  have hallowedBalance := hbalanced vertex
  omega

/-- If an unused allowed edge shares an endpoint with a closed trail, residual
balance supplies a nonempty residual closed trail at a vertex visited by the
old trail.  This is the local augmentation step in Hierholzer's argument. -/
theorem exists_residualClosedTrailAt_of_sharesEndpoint
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (walk : G.Walk base base) (htrail : walk.IsTrailWithin allowed)
    (used unused : E) (hused : used ∈ walk.edges)
    (hunusedAllowed : unused ∈ allowed) (hunused : unused ∉ walk.edges)
    (hshares : G.SharesEndpoint used unused) :
    ∃ (vertex : V) (_split : walk.VertexSplit vertex)
      (inserted : G.Walk vertex vertex),
      inserted.IsTrailWithin (allowed \ walk.edges.toFinset) ∧
        0 < inserted.length := by
  let residual := allowed \ walk.edges.toFinset
  have hresidualBalanced : G.IsBalancedEdgeSet residual :=
    walk.isBalancedEdgeSet_sdiff_closedTrail allowed hbalanced htrail
  have hunusedResidual : unused ∈ residual := by
    simp [residual, hunusedAllowed, hunused]
  rcases hshares with hsourceSource | hsourceTarget |
      htargetSource | htargetTarget
  · let split := walk.vertexSplitAtSource used hused
    obtain ⟨inserted, hinserted, hpositive⟩ :=
      Walk.exists_nonempty_closedTrailWithin_of_exists_outgoing
        (G := G) residual hresidualBalanced (G.source used)
        ⟨unused, hunusedResidual, hsourceSource.symm⟩
    exact ⟨G.source used, split, inserted, hinserted, hpositive⟩
  · let split := walk.vertexSplitAtSource used hused
    obtain ⟨outgoing, houtgoingResidual, hsource⟩ :=
      IsBalancedEdgeSet.exists_outgoing_of_mem_of_target_eq
        (G := G) residual hresidualBalanced unused hunusedResidual
          (G.source used) hsourceTarget.symm
    obtain ⟨inserted, hinserted, hpositive⟩ :=
      Walk.exists_nonempty_closedTrailWithin_of_exists_outgoing
        (G := G) residual hresidualBalanced (G.source used)
        ⟨outgoing, houtgoingResidual, hsource⟩
    exact ⟨G.source used, split, inserted, hinserted, hpositive⟩
  · let split := walk.vertexSplitAtTarget used hused
    obtain ⟨inserted, hinserted, hpositive⟩ :=
      Walk.exists_nonempty_closedTrailWithin_of_exists_outgoing
        (G := G) residual hresidualBalanced (G.target used)
        ⟨unused, hunusedResidual, htargetSource.symm⟩
    exact ⟨G.target used, split, inserted, hinserted, hpositive⟩
  · let split := walk.vertexSplitAtTarget used hused
    obtain ⟨outgoing, houtgoingResidual, hsource⟩ :=
      IsBalancedEdgeSet.exists_outgoing_of_mem_of_target_eq
        (G := G) residual hresidualBalanced unused hunusedResidual
          (G.target used) htargetTarget.symm
    obtain ⟨inserted, hinserted, hpositive⟩ :=
      Walk.exists_nonempty_closedTrailWithin_of_exists_outgoing
        (G := G) residual hresidualBalanced (G.target used)
        ⟨outgoing, houtgoingResidual, hsource⟩
    exact ⟨G.target used, split, inserted, hinserted, hpositive⟩

/-- A longest nonempty closed trail in a walk-connected balanced support uses
every allowed distinguishable edge. -/
theorem all_edges_mem_of_maximal_closedTrailWithin_of_connected
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (hconnected : G.HasWalkConnectedSupport (edgeSetMultiplicity allowed))
    (walk : G.Walk base base) (htrail : walk.IsTrailWithin allowed)
    (hnonempty : 0 < walk.length)
    (hmaximal : ∀ (finish : V) (other : G.Walk base finish),
      other.IsTrailWithin allowed → other.length ≤ walk.length) :
    ∀ edge, edge ∈ allowed → edge ∈ walk.edges := by
  intro unused hunusedAllowed
  by_contra hunused
  have hwalkEdges : walk.edges ≠ [] := by
    intro hempty
    have : walk.edges.length = 0 := by simp [hempty]
    rw [walk.edges_length] at this
    omega
  let used := walk.edges.head hwalkEdges
  have husedMem : used ∈ walk.edges := List.head_mem hwalkEdges
  have husedAllowed : used ∈ allowed := htrail.2 used husedMem
  have hmarked :
      ∃ edge, 0 < edgeSetMultiplicity allowed edge ∧
        edge ∈ walk.edges.toFinset := by
    exact ⟨used, (edgeSetMultiplicity_pos_iff allowed used).2 husedAllowed,
      List.mem_toFinset.mpr husedMem⟩
  have hunmarked :
      ∃ edge, 0 < edgeSetMultiplicity allowed edge ∧
        edge ∉ walk.edges.toFinset := by
    exact ⟨unused, (edgeSetMultiplicity_pos_iff allowed unused).2 hunusedAllowed,
      by simpa using hunused⟩
  obtain ⟨usedBoundary, unusedBoundary, _, husedBoundary,
    hunusedBoundaryPositive, hunusedBoundary, hshares⟩ :=
      HasWalkConnectedSupport.exists_boundary (G := G)
        (edgeSetMultiplicity allowed) hconnected walk.edges.toFinset
          hmarked hunmarked
  have husedBoundaryMem : usedBoundary ∈ walk.edges :=
    List.mem_toFinset.mp husedBoundary
  have hunusedBoundaryAllowed : unusedBoundary ∈ allowed :=
    (edgeSetMultiplicity_pos_iff allowed unusedBoundary).1
      hunusedBoundaryPositive
  have hunusedBoundaryMem : unusedBoundary ∉ walk.edges := by
    simpa using hunusedBoundary
  obtain ⟨vertex, split, inserted, hinserted, hinsertedPositive⟩ :=
    walk.exists_residualClosedTrailAt_of_sharesEndpoint allowed hbalanced htrail
      usedBoundary unusedBoundary husedBoundaryMem hunusedBoundaryAllowed
      hunusedBoundaryMem hshares
  have hsplicedTrail : (split.splice inserted).IsTrailWithin allowed :=
    split.isTrailWithin_splice inserted allowed htrail hinserted
  have hle := hmaximal base (split.splice inserted) hsplicedTrail
  have hlt := split.length_lt_splice inserted hinsertedPositive
  omega

/-- Directed Euler theorem for a finite set of distinguishable edge tokens:
a nonempty walk-connected balanced support has a closed trail using every
allowed token exactly once.  The base may be any vertex with an allowed
outgoing token. -/
theorem exists_closedTrail_covering_of_balanced_connected
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (allowed : Finset E) (hbalanced : G.IsBalancedEdgeSet allowed)
    (hconnected : G.HasWalkConnectedSupport (edgeSetMultiplicity allowed))
    (base : V) (houtgoing : ∃ edge, edge ∈ allowed ∧ G.source edge = base) :
    ∃ walk : G.Walk base base,
      walk.IsTrailWithin allowed ∧
      ∀ edge, edge ∈ walk.edges ↔ edge ∈ allowed := by
  obtain ⟨finish, walk, htrail, hmaximal⟩ :=
    Walk.exists_maximalTrailWithin (G := G) allowed base
  have hclosed : finish = base :=
    walk.maximalTrailWithin_isClosed allowed hbalanced htrail hmaximal
  subst finish
  obtain ⟨initialEdge, hinitialAllowed, hinitialSource⟩ := houtgoing
  have hinitialMem := walk.edge_mem_of_maximalTrailWithin_of_source_eq
    allowed htrail hmaximal initialEdge hinitialAllowed hinitialSource
  have hnonempty : 0 < walk.length := by
    rw [← walk.edges_length, List.length_pos_iff]
    exact List.ne_nil_of_mem hinitialMem
  have hcover := walk.all_edges_mem_of_maximal_closedTrailWithin_of_connected
    allowed hbalanced hconnected htrail hnonempty hmaximal
  exact ⟨walk, htrail, fun edge => ⟨htrail.2 edge, hcover edge⟩⟩

/-- The positive edge support of a nonempty walk is walk-connected in the
underlying undirected incidence graph. -/
theorem edgeMultiplicity_hasWalkConnectedSupport
    [DecidableEq E] (walk : G.Walk start finish) (hne : 0 < walk.length) :
    G.HasWalkConnectedSupport walk.edgeMultiplicity := by
  have hedges : walk.edges ≠ [] := by
    intro hempty
    have : walk.edges.length = 0 := by simp [hempty]
    rw [walk.edges_length] at this
    omega
  refine ⟨walk.edges, hedges, ?_, ?_⟩
  · intro edge
    exact (walk.edgeMultiplicity_pos_iff_mem_edges edge).symm
  · exact walk.edges_isChain.imp fun first second hmatch =>
      Or.inr (Or.inr (Or.inl hmatch))

/-- A nonempty zero-charge closed walk induces its exact connected integer
circulation of edge occurrence counts. -/
def toConnectedIntegerCirculation
    [Fintype E] [DecidableEq E] [DecidableEq V] {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (walk : G.Walk base base)
    (hne : 0 < walk.length) (hzero : walk.charge edgeCharge = 0) :
    G.ConnectedIntegerCirculation edgeCharge where
  multiplicity := walk.edgeMultiplicity
  nonzero := by
    have hedges : walk.edges ≠ [] := by
      intro hempty
      have : walk.edges.length = 0 := by simp [hempty]
      rw [walk.edges_length] at this
      omega
    let edge := walk.edges.head hedges
    exact ⟨edge, (walk.edgeMultiplicity_pos_iff_mem_edges edge).2
      (List.head_mem hedges)⟩
  balanced := walk.edgeMultiplicity_balanced
  charge_zero := by
    rw [walk.multiplicityCharge_edgeMultiplicity]
    exact hzero
  connected := walk.edgeMultiplicity_hasWalkConnectedSupport hne

end Walk

namespace ConnectedIntegerCirculation

variable {G} {κ : Type uκ} {edgeCharge : E → κ → ℤ}

/-- A connected integer circulation has an exact closed-walk realization at
any incident support vertex.  Integer multiplicities are expanded to
distinguishable tokens, traversed by the finite directed Euler theorem, and
then detokenized. -/
theorem exists_closedWalk_exactMultiplicity_at
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (circulation : G.ConnectedIntegerCirculation edgeCharge)
    (base : V)
    (hbase : ∃ edge, 0 < circulation.multiplicity edge ∧
      (G.source edge = base ∨ G.target edge = base)) :
    ∃ walk : G.Walk base base,
      0 < walk.length ∧
      (∀ edge, walk.edgeMultiplicity edge = circulation.multiplicity edge) ∧
      walk.charge edgeCharge = 0 := by
  let multiplicity := circulation.multiplicity
  let tokenG := G.tokenGraph multiplicity
  let allowed : Finset (MultiplicityToken multiplicity) := Finset.univ
  have htokenBalanced : tokenG.IsBalancedEdgeSet allowed := by
    exact G.tokenGraph_univ_balanced_of_balanced multiplicity circulation.balanced
  have htokenConnected :
      tokenG.HasWalkConnectedSupport (edgeSetMultiplicity allowed) := by
    exact G.tokenGraph_univ_hasWalkConnectedSupport multiplicity
      circulation.nonzero circulation.connected
  have htokenOutgoing :
      ∃ token, token ∈ allowed ∧ tokenG.source token = base := by
    obtain ⟨edge, hpositive, hsource | htarget⟩ := hbase
    · let token : MultiplicityToken multiplicity := ⟨edge, ⟨0, hpositive⟩⟩
      have htokenSource : tokenG.source token = base := by
        change G.source edge = base
        exact hsource
      exact ⟨token, Finset.mem_univ token, htokenSource⟩
    · let token : MultiplicityToken multiplicity := ⟨edge, ⟨0, hpositive⟩⟩
      have htokenTarget : tokenG.target token = base := by
        change G.target edge = base
        exact htarget
      exact IsBalancedEdgeSet.exists_outgoing_of_mem_of_target_eq
        (G := tokenG) allowed htokenBalanced token (Finset.mem_univ token)
          base htokenTarget
  obtain ⟨tokenWalk, htokenTrail, htokenCover⟩ :=
    Walk.exists_closedTrail_covering_of_balanced_connected
      (G := tokenG) allowed htokenBalanced htokenConnected base htokenOutgoing
  let walk : G.Walk base base := tokenWalk.detokenize multiplicity
  have hall : ∀ token : MultiplicityToken multiplicity,
      token ∈ tokenWalk.edges := by
    intro token
    exact (htokenCover token).2 (Finset.mem_univ token)
  have hexact : ∀ edge,
      walk.edgeMultiplicity edge = circulation.multiplicity edge := by
    intro edge
    exact tokenWalk.edgeMultiplicity_detokenize_of_nodup_all multiplicity
      htokenTrail.1 hall edge
  have hnonempty : 0 < walk.length := by
    obtain ⟨edge, hpositive⟩ := circulation.nonzero
    have hwalkPositive : 0 < walk.edgeMultiplicity edge := by
      rw [hexact edge]
      exact hpositive
    have hedgeMem := (walk.edgeMultiplicity_pos_iff_mem_edges edge).1
      hwalkPositive
    rw [← walk.edges_length, List.length_pos_iff]
    exact List.ne_nil_of_mem hedgeMem
  have hcharge : walk.charge edgeCharge = 0 := by
    calc
      walk.charge edgeCharge =
          G.multiplicityCharge edgeCharge walk.edgeMultiplicity :=
        (walk.multiplicityCharge_edgeMultiplicity edgeCharge).symm
      _ = G.multiplicityCharge edgeCharge circulation.multiplicity := by
        congr 1
        funext edge
        exact hexact edge
      _ = 0 := circulation.charge_zero
  exact ⟨walk, hnonempty, hexact, hcharge⟩

end ConnectedIntegerCirculation

/-- A nonempty cyclic word of edge identities based at `base`.  The endpoint
conditions include the wraparound edge compatibility. -/
structure CyclicWord (base : V) where
  word : List E
  nonempty : word ≠ []
  compatible : word.IsChain fun first second => G.target first = G.source second
  first_source : G.source (word.head nonempty) = base
  last_target : G.target (word.getLast nonempty) = base

namespace CyclicWord

variable {G} {base : V}

/-- The positive length of the cyclic word. -/
abbrev periodLength (cycle : G.CyclicWord base) : ℕ := cycle.word.length

theorem periodLength_pos (cycle : G.CyclicWord base) : 0 < cycle.periodLength := by
  simpa [periodLength, List.length_pos_iff] using cycle.nonempty

/-- The edge at time `n` in the infinite repetition of a cyclic word. -/
def edgeAt (cycle : G.CyclicWord base) (n : ℕ) : E :=
  cycle.word[n % cycle.periodLength]'(Nat.mod_lt _ cycle.periodLength_pos)

theorem source_edgeAt_zero (cycle : G.CyclicWord base) :
    G.source (cycle.edgeAt 0) = base := by
  change G.source (cycle.word[0 % cycle.word.length]'(by
    exact Nat.mod_lt _ cycle.periodLength_pos)) = base
  simpa [List.head_eq_getElem_zero] using cycle.first_source

theorem edgeAt_add_period (cycle : G.CyclicWord base) (n : ℕ) :
    cycle.edgeAt (n + cycle.periodLength) = cycle.edgeAt n := by
  simp [edgeAt, periodLength]

/-- Successive entries of the cyclic repetition remain graph-compatible,
including the last-to-first wraparound. -/
theorem target_edgeAt_eq_source_succ (cycle : G.CyclicWord base) (n : ℕ) :
    G.target (cycle.edgeAt n) = G.source (cycle.edgeAt (n + 1)) := by
  let length := cycle.periodLength
  have hlength : 0 < length := cycle.periodLength_pos
  have hmodlt : n % length < length := Nat.mod_lt _ hlength
  by_cases hnext : n % length + 1 < length
  · have hone : 1 % length = 1 := Nat.mod_eq_of_lt (by omega)
    have hmod : (n + 1) % length = n % length + 1 := by
      rw [Nat.add_mod_of_add_mod_lt]
      · rw [hone]
      · simpa [hone] using hnext
    change
      G.target (cycle.word[n % length]'(by simpa [length] using hmodlt)) =
        G.source (cycle.word[(n + 1) % length]'(by
          simpa [length] using Nat.mod_lt (n + 1) hlength))
    simpa only [hmod] using cycle.compatible.getElem (n % length) hnext
  · have hwrap : n % length + 1 = length := by omega
    have hmod : (n + 1) % length = 0 := by
      by_cases honeLength : length = 1
      · rw [honeLength]
        exact Nat.mod_one (n + 1)
      · have hone : 1 % length = 1 := Nat.mod_eq_of_lt (by omega)
        have hadd := Nat.add_mod_add_of_le_add_mod
          (a := n) (b := 1) (c := length) (by omega)
        rw [hone, hwrap] at hadd
        omega
    have hwrap' : n % cycle.word.length + 1 = cycle.word.length := by
      simpa only [length] using hwrap
    have hlastIndex : n % length = cycle.word.length - 1 := by
      change n % cycle.word.length = cycle.word.length - 1
      omega
    change
      G.target (cycle.word[n % length]'(by simpa [length] using hmodlt)) =
        G.source (cycle.word[(n + 1) % length]'(by
          simpa [length] using Nat.mod_lt (n + 1) hlength))
    simp only [hmod]
    have hboundary := cycle.last_target.trans cycle.first_source.symm
    rw [List.getLast_eq_getElem, List.head_eq_getElem_zero] at hboundary
    simpa only [hlastIndex] using hboundary

end CyclicWord

namespace Walk

variable {G} {base : V}

/-- A nonempty closed typed walk, viewed as a cyclic edge word. -/
def toCyclicWord (walk : G.Walk base base) (hne : 0 < walk.length) :
    G.CyclicWord base where
  word := walk.edges
  nonempty := by
    intro hempty
    have : walk.edges.length = 0 := by simp [hempty]
    rw [walk.edges_length] at this
    omega
  compatible := walk.edges_isChain
  first_source := walk.source_head (by
    intro hempty
    have : walk.edges.length = 0 := by simp [hempty]
    rw [walk.edges_length] at this
    omega)
  last_target := walk.target_getLast (by
    intro hempty
    have : walk.edges.length = 0 := by simp [hempty]
    rw [walk.edges_length] at this
    omega)

@[simp] theorem toCyclicWord_word (walk : G.Walk base base) (hne : 0 < walk.length) :
    (walk.toCyclicWord hne).word = walk.edges := rfl

@[simp] theorem toCyclicWord_periodLength (walk : G.Walk base base)
    (hne : 0 < walk.length) :
    (walk.toCyclicWord hne).periodLength = walk.length := by
  exact walk.edges_length

end Walk

/-- An infinite directed walk from a prescribed initial vertex.  Its vertex
at time `n` is derived from the preceding edge, so the only compatibility data
are the initial source and consecutive edge endpoints. -/
structure InfiniteWalk (start : V) where
  edge : ℕ → E
  source_zero : G.source (edge 0) = start
  consecutive : ∀ n, G.target (edge n) = G.source (edge (n + 1))

namespace CyclicWord

variable {G} {base : V}

/-- Infinite repetition of a graph-compatible cyclic word. -/
def toInfiniteWalk (cycle : G.CyclicWord base) : G.InfiniteWalk base where
  edge := cycle.edgeAt
  source_zero := cycle.source_edgeAt_zero
  consecutive := cycle.target_edgeAt_eq_source_succ

end CyclicWord

namespace InfiniteWalk

variable {G} {start : V}

/-- Vertex occupied before edge `n` is traversed. -/
def vertex (walk : G.InfiniteWalk start) : ℕ → V
  | 0 => start
  | n + 1 => G.target (walk.edge n)

theorem source_edge (walk : G.InfiniteWalk start) (n : ℕ) :
    G.source (walk.edge n) = walk.vertex n := by
  cases n with
  | zero => exact walk.source_zero
  | succ n => exact (walk.consecutive n).symm

/-- Integer cumulative charge before time `n`. -/
def prefixCharge (walk : G.InfiniteWalk start) {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) : ℕ → κ → ℤ
  | 0 => 0
  | n + 1 => prefixCharge walk edgeCharge n + edgeCharge (walk.edge n)

/-- Prefix charge as a finite sum over elapsed times. -/
theorem prefixCharge_eq_sum_range (walk : G.InfiniteWalk start) {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (horizon : ℕ) :
    walk.prefixCharge edgeCharge horizon =
      ∑ n ∈ Finset.range horizon, edgeCharge (walk.edge n) := by
  induction horizon with
  | zero => simp [prefixCharge]
  | succ horizon ih => simp [prefixCharge, Finset.sum_range_succ, ih]

/-- Finite-range form of bounded discrepancy.  For a finite-dimensional
integer lattice this is equivalent to boundedness in any norm. -/
def HasBoundedDiscrepancy (walk : G.InfiniteWalk start) {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) : Prop :=
  Set.Finite (Set.range (walk.prefixCharge edgeCharge))


/-- The first `n` edges as a finite walk. -/
def take (walk : G.InfiniteWalk start) : (n : ℕ) → G.Walk start (walk.vertex n)
  | 0 => .nil
  | n + 1 => .concat (take walk n) (walk.edge n) (walk.source_edge n)

@[simp] theorem take_length (walk : G.InfiniteWalk start) (n : ℕ) :
    (walk.take n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [take, Walk.length, ih]

@[simp] theorem take_charge (walk : G.InfiniteWalk start) {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (n : ℕ) :
    (walk.take n).charge edgeCharge = walk.prefixCharge edgeCharge n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [take, Walk.charge, prefixCharge, ih]

/-- The next `length` edges beginning at time `startTime`. -/
def segment (walk : G.InfiniteWalk start) (startTime : ℕ) : (length : ℕ) →
    G.Walk (walk.vertex startTime) (walk.vertex (startTime + length))
  | 0 => by simpa using (Walk.nil : G.Walk (walk.vertex startTime) (walk.vertex startTime))
  | length + 1 =>
      Walk.concat (segment walk startTime length)
        (walk.edge (startTime + length)) (walk.source_edge _)

@[simp] theorem segment_length (walk : G.InfiniteWalk start) (startTime length : ℕ) :
    (walk.segment startTime length).length = length := by
  induction length with
  | zero => simp [segment]
  | succ length ih => simp [segment, Walk.length, ih]

theorem segment_charge (walk : G.InfiniteWalk start) {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (startTime length : ℕ) :
    (walk.segment startTime length).charge edgeCharge =
      walk.prefixCharge edgeCharge (startTime + length) -
        walk.prefixCharge edgeCharge startTime := by
  induction length with
  | zero => simp [segment]
  | succ length ih =>
      simp only [segment, Walk.charge, prefixCharge]
      rw [ih]
      funext coordinate
      simp [Pi.add_apply, Pi.sub_apply]
      ring

end InfiniteWalk

namespace InfiniteWalk

variable {G} {start : V}

/-- Put one legal edge in front of an infinite walk. -/
def prependEdge (before : V) (edge : E) (hsource : G.source edge = before)
    (tail : G.InfiniteWalk (G.target edge)) : G.InfiniteWalk before where
  edge
    | 0 => edge
    | n + 1 => tail.edge n
  source_zero := hsource
  consecutive
    | 0 => tail.source_zero.symm
    | n + 1 => tail.consecutive n

@[simp] theorem prependEdge_edge_zero (before : V) (edge : E)
    (hsource : G.source edge = before) (tail : G.InfiniteWalk (G.target edge)) :
    (prependEdge before edge hsource tail).edge 0 = edge := rfl

@[simp] theorem prependEdge_edge_succ (before : V) (edge : E)
    (hsource : G.source edge = before) (tail : G.InfiniteWalk (G.target edge))
    (n : ℕ) :
    (prependEdge before edge hsource tail).edge (n + 1) = tail.edge n := rfl

theorem prefixCharge_prependEdge_succ {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (before : V) (edge : E)
    (hsource : G.source edge = before) (tail : G.InfiniteWalk (G.target edge))
    (n : ℕ) :
    (prependEdge before edge hsource tail).prefixCharge edgeCharge (n + 1) =
      edgeCharge edge + tail.prefixCharge edgeCharge n := by
  induction n with
  | zero => simp [prefixCharge]
  | succ n ih =>
      calc
        (prependEdge before edge hsource tail).prefixCharge edgeCharge (n + 1 + 1) =
            (prependEdge before edge hsource tail).prefixCharge edgeCharge (n + 1) +
              edgeCharge (tail.edge n) := rfl
        _ = (edgeCharge edge + tail.prefixCharge edgeCharge n) +
              edgeCharge (tail.edge n) := by rw [ih]
        _ = edgeCharge edge + tail.prefixCharge edgeCharge (n + 1) := by
          rw [prefixCharge]
          abel

/-- Adding one finite initial edge preserves finite-range discrepancy. -/
theorem hasBoundedDiscrepancy_prependEdge {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (before : V) (edge : E)
    (hsource : G.source edge = before) (tail : G.InfiniteWalk (G.target edge))
    (hbounded : tail.HasBoundedDiscrepancy edgeCharge) :
    (prependEdge before edge hsource tail).HasBoundedDiscrepancy edgeCharge := by
  let shift : (κ → ℤ) → (κ → ℤ) := fun value => edgeCharge edge + value
  refine ((Set.finite_singleton 0).union (hbounded.image shift)).subset ?_
  rintro value ⟨n, rfl⟩
  cases n with
  | zero => exact Set.mem_union_left _ (Set.mem_singleton 0)
  | succ n =>
      refine Set.mem_union_right _ ⟨tail.prefixCharge edgeCharge n, ⟨n, rfl⟩, ?_⟩
      exact (prefixCharge_prependEdge_succ edgeCharge before edge hsource tail n).symm

/-- Edge-level eventual periodicity, with an explicit finite transient and
positive period. -/
def IsEventuallyPeriodic (walk : G.InfiniteWalk start) : Prop :=
  ∃ transient period, 0 < period ∧
    ∀ n, walk.edge (transient + n + period) = walk.edge (transient + n)

end InfiniteWalk

namespace Walk

variable {G} {start finish : V}

/-- Put a finite typed walk in front of an infinite continuation. -/
def prependInfinite {start : V} : {finish : V} →
    G.Walk start finish → G.InfiniteWalk finish → G.InfiniteWalk start
  | _, .nil, tail => tail
  | _, .concat walkSoFar edge legal, tail =>
      prependInfinite walkSoFar
        (InfiniteWalk.prependEdge _ edge legal tail)

/-- After the finite prefix length, the prepended walk is exactly its
continuation. -/
theorem prependInfinite_edge_length_add (walk : G.Walk start finish)
    (tail : G.InfiniteWalk finish) (n : ℕ) :
    (walk.prependInfinite tail).edge (walk.length + n) = tail.edge n := by
  induction walk generalizing n with
  | nil => simp [prependInfinite, length]
  | concat walkSoFar edge legal ih =>
      change
        (walkSoFar.prependInfinite
          (InfiniteWalk.prependEdge _ edge legal tail)).edge
            (walkSoFar.length + 1 + n) = tail.edge n
      rw [show walkSoFar.length + 1 + n = walkSoFar.length + (n + 1) by omega]
      rw [ih]
      rfl

/-- Every finite legal transient preserves bounded discrepancy. -/
theorem hasBoundedDiscrepancy_prependInfinite {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (walk : G.Walk start finish)
    (tail : G.InfiniteWalk finish)
    (hbounded : tail.HasBoundedDiscrepancy edgeCharge) :
    (walk.prependInfinite tail).HasBoundedDiscrepancy edgeCharge := by
  induction walk with
  | nil => exact hbounded
  | concat walkSoFar edge legal ih =>
      exact ih _ (InfiniteWalk.hasBoundedDiscrepancy_prependEdge
        edgeCharge _ edge legal tail hbounded)

end Walk

namespace CyclicWord

variable {G} {base : V}

/-- One full period of the canonical repetition has the charge obtained by
summing the finite cyclic word. -/
theorem prefixCharge_periodLength {κ : Type uκ} (cycle : G.CyclicWord base)
    (edgeCharge : E → κ → ℤ) :
    cycle.toInfiniteWalk.prefixCharge edgeCharge cycle.periodLength =
      (cycle.word.map edgeCharge).sum := by
  rw [InfiniteWalk.prefixCharge_eq_sum_range, ← Fin.sum_univ_eq_sum_range]
  calc
    (∑ i : Fin cycle.periodLength, edgeCharge (cycle.toInfiniteWalk.edge i)) =
        (List.ofFn fun i : Fin cycle.word.length => edgeCharge cycle.word[i]).sum := by
          rw [List.sum_ofFn]
          apply Finset.sum_congr rfl
          intro i hi
          simp [toInfiniteWalk, edgeAt, Nat.mod_eq_of_lt i.isLt]
    _ = (cycle.word.map edgeCharge).sum := by
      congr 1
      simp

/-- Zero charge over one cyclic word makes every prefix-charge coordinate
periodic with the same positive period. -/
theorem prefixCharge_add_period_of_wordCharge_zero {κ : Type uκ}
    (cycle : G.CyclicWord base) (edgeCharge : E → κ → ℤ)
    (hzero : (cycle.word.map edgeCharge).sum = 0) (n : ℕ) :
    cycle.toInfiniteWalk.prefixCharge edgeCharge (n + cycle.periodLength) =
      cycle.toInfiniteWalk.prefixCharge edgeCharge n := by
  induction n with
  | zero => simpa [InfiniteWalk.prefixCharge] using
      (cycle.prefixCharge_periodLength edgeCharge).trans hzero
  | succ n ih =>
      rw [show n + 1 + cycle.periodLength = (n + cycle.periodLength) + 1 by omega]
      simp only [InfiniteWalk.prefixCharge]
      rw [ih]
      change _ + edgeCharge (cycle.edgeAt (n + cycle.periodLength)) =
        _ + edgeCharge (cycle.edgeAt n)
      rw [cycle.edgeAt_add_period]

/-- Repeating a nonempty zero-charge cyclic word has bounded discrepancy. -/
theorem hasBoundedDiscrepancy_of_wordCharge_zero {κ : Type uκ}
    (cycle : G.CyclicWord base) (edgeCharge : E → κ → ℤ)
    (hzero : (cycle.word.map edgeCharge).sum = 0) :
    cycle.toInfiniteWalk.HasBoundedDiscrepancy edgeCharge := by
  exact Math.finite_range_of_add_period
    (cycle.toInfiniteWalk.prefixCharge edgeCharge)
    cycle.periodLength cycle.periodLength_pos
    (cycle.prefixCharge_add_period_of_wordCharge_zero edgeCharge hzero)

end CyclicWord

/-- A finite reachable lasso: first follow `prefix`, then repeat the nonempty
closed `period`.  Exact zero period charge is the finite certificate for
bounded discrepancy of the canonical eventually periodic repetition. -/
structure ZeroChargeLasso {κ : Type uκ} (edgeCharge : E → κ → ℤ)
    (start : V) where
  base : V
  initialWalk : G.Walk start base
  periodFinish : V
  period : G.Walk base periodFinish
  period_closed : periodFinish = base
  period_nonempty : 0 < period.length
  period_zero : period.charge edgeCharge = 0

namespace ReachableConnectedIntegerCirculation

variable {G} {start : V} {κ : Type uκ} {edgeCharge : E → κ → ℤ}

/-- The Euler realization of a reachable connected circulation is a
zero-charge lasso whose transient is the supplied route to the support. -/
theorem exists_zeroChargeLasso
    [Fintype E] [DecidableEq V]
    (circulation : G.ReachableConnectedIntegerCirculation edgeCharge start) :
    Nonempty (G.ZeroChargeLasso edgeCharge start) := by
  classical
  obtain ⟨period, hnonempty, _, hzero⟩ :=
    circulation.toConnectedIntegerCirculation.exists_closedWalk_exactMultiplicity_at
      circulation.entry circulation.entry_mem_support
  exact ⟨{
    base := circulation.entry
    initialWalk := circulation.initialWalk
    periodFinish := circulation.entry
    period := period
    period_closed := rfl
    period_nonempty := hnonempty
    period_zero := hzero
  }⟩

end ReachableConnectedIntegerCirculation

namespace ZeroChargeLasso

variable {G} {start : V} {κ : Type uκ} {edgeCharge : E → κ → ℤ}

/-- Regard the lasso period as a genuinely closed typed walk. -/
def closedPeriod (lasso : G.ZeroChargeLasso edgeCharge start) :
    G.Walk lasso.base lasso.base :=
  lasso.period.castFinish lasso.period_closed

@[simp] theorem closedPeriod_length (lasso : G.ZeroChargeLasso edgeCharge start) :
    lasso.closedPeriod.length = lasso.period.length := by
  simp [closedPeriod]

@[simp] theorem closedPeriod_charge (lasso : G.ZeroChargeLasso edgeCharge start) :
    lasso.closedPeriod.charge edgeCharge = 0 := by
  simpa [closedPeriod] using lasso.period_zero

/-- A lasso certificate constructs a genuine eventually periodic infinite
walk from the prescribed start, and its prefix-charge range is finite. -/
theorem exists_eventuallyPeriodic_boundedDiscrepancy
    (lasso : G.ZeroChargeLasso edgeCharge start) :
    ∃ walk : G.InfiniteWalk start,
      walk.HasBoundedDiscrepancy edgeCharge ∧ walk.IsEventuallyPeriodic := by
  let closed := lasso.closedPeriod
  have hclosedNonempty : 0 < closed.length := by
    simpa [closed] using lasso.period_nonempty
  let cycle : G.CyclicWord lasso.base := closed.toCyclicWord hclosedNonempty
  have hwordZero : (cycle.word.map edgeCharge).sum = 0 := by
    change (closed.edges.map edgeCharge).sum = 0
    rw [← closed.charge_eq_sum_map]
    exact lasso.closedPeriod_charge
  let periodicTail : G.InfiniteWalk lasso.base := cycle.toInfiniteWalk
  have htailBounded : periodicTail.HasBoundedDiscrepancy edgeCharge := by
    exact cycle.hasBoundedDiscrepancy_of_wordCharge_zero edgeCharge hwordZero
  let result : G.InfiniteWalk start := lasso.initialWalk.prependInfinite periodicTail
  refine ⟨result, lasso.initialWalk.hasBoundedDiscrepancy_prependInfinite
    edgeCharge periodicTail htailBounded, ?_⟩
  refine ⟨lasso.initialWalk.length, cycle.periodLength,
    cycle.periodLength_pos, ?_⟩
  intro n
  calc
    result.edge (lasso.initialWalk.length + n + cycle.periodLength) =
        periodicTail.edge (n + cycle.periodLength) := by
          rw [show lasso.initialWalk.length + n + cycle.periodLength =
            lasso.initialWalk.length + (n + cycle.periodLength) by omega]
          exact lasso.initialWalk.prependInfinite_edge_length_add periodicTail _
    _ = periodicTail.edge n := by
      exact cycle.edgeAt_add_period n
    _ = result.edge (lasso.initialWalk.length + n) := by
      exact (lasso.initialWalk.prependInfinite_edge_length_add periodicTail n).symm

/-- The exact edge counts of a lasso period form a reachable connected
integer circulation. -/
def toReachableConnectedIntegerCirculation
    [Fintype E] [DecidableEq E] [DecidableEq V]
    (lasso : G.ZeroChargeLasso edgeCharge start) :
    G.ReachableConnectedIntegerCirculation edgeCharge start := by
  let closed := lasso.closedPeriod
  have hclosedNonempty : 0 < closed.length := by
    simpa [closed] using lasso.period_nonempty
  let circulation : G.ConnectedIntegerCirculation edgeCharge :=
    closed.toConnectedIntegerCirculation edgeCharge hclosedNonempty
      lasso.closedPeriod_charge
  refine {
    toConnectedIntegerCirculation := circulation
    entry := lasso.base
    initialWalk := lasso.initialWalk
    entry_mem_support := ?_
  }
  have hedges : closed.edges ≠ [] := by
    intro hempty
    have : closed.edges.length = 0 := by simp [hempty]
    rw [closed.edges_length] at this
    omega
  let firstEdge := closed.edges.head hedges
  refine ⟨firstEdge, ?_, Or.inl ?_⟩
  · change 0 < closed.edgeMultiplicity firstEdge
    exact (closed.edgeMultiplicity_pos_iff_mem_edges firstEdge).2
      (List.head_mem hedges)
  · exact closed.source_head hedges

end ZeroChargeLasso

namespace ReachableConnectedIntegerCirculation

variable {G} {start : V} {κ : Type uκ} {edgeCharge : E → κ → ℤ}

/-- A reachable connected zero-charge integer circulation constructs a
genuine eventually periodic infinite walk of bounded discrepancy. -/
theorem exists_eventuallyPeriodic_boundedDiscrepancy
    [Fintype E] [DecidableEq V]
    (circulation : G.ReachableConnectedIntegerCirculation edgeCharge start) :
    ∃ walk : G.InfiniteWalk start,
      walk.HasBoundedDiscrepancy edgeCharge ∧ walk.IsEventuallyPeriodic := by
  classical
  obtain ⟨lasso⟩ := circulation.exists_zeroChargeLasso
  exact lasso.exists_eventuallyPeriodic_boundedDiscrepancy

end ReachableConnectedIntegerCirculation

/-- The exact repeated-configuration extraction.  Finiteness of the vertex
type and of the prefix-charge range forces two distinct times to have the same
vertex and cumulative lattice charge; the intervening segment is the desired
nonempty zero-charge closed walk. -/
theorem exists_zeroChargeLasso_of_boundedDiscrepancy
    [Finite V] {κ : Type uκ}
    (edgeCharge : E → κ → ℤ) (start : V)
    (walk : G.InfiniteWalk start)
    (hbounded : walk.HasBoundedDiscrepancy edgeCharge) :
    Nonempty (G.ZeroChargeLasso edgeCharge start) := by
  classical
  let prefixRange : Set (κ → ℤ) := Set.range (walk.prefixCharge edgeCharge)
  letI : Fintype prefixRange := hbounded.fintype
  let state : ℕ → V × prefixRange := fun n =>
    (walk.vertex n, ⟨walk.prefixCharge edgeCharge n, ⟨n, rfl⟩⟩)
  obtain ⟨r, s, hrs, heq⟩ := Finite.exists_ne_map_eq_of_infinite state
  have makeLasso : ∀ {r s : ℕ}, r < s → state r = state s →
      Nonempty (G.ZeroChargeLasso edgeCharge start) := by
    intro r s hlt hstate
    have hvertex : walk.vertex r = walk.vertex s :=
      congrArg Prod.fst hstate
    have hcharge :
        walk.prefixCharge edgeCharge r = walk.prefixCharge edgeCharge s := by
      exact congrArg (fun x => x.2.1) hstate
    let length : ℕ := s - r
    have hrlength : r + length = s := by
      dsimp [length]
      omega
    have hlength : 0 < length := by
      dsimp [length]
      omega
    let period : G.Walk (walk.vertex r) (walk.vertex (r + length)) :=
      walk.segment r length
    have hperiodZero : period.charge edgeCharge = 0 := by
      rw [show period = walk.segment r length from rfl,
        walk.segment_charge edgeCharge, hrlength, ← hcharge]
      simp
    exact ⟨{
      base := walk.vertex r
      initialWalk := walk.take r
      periodFinish := walk.vertex (r + length)
      period := period
      period_closed := by simpa [hrlength] using hvertex.symm
      period_nonempty := by simpa [period] using hlength
      period_zero := hperiodZero
    }⟩
  rcases lt_or_gt_of_ne hrs with hlt | hgt
  · exact makeLasso hlt heq
  · exact makeLasso hgt heq.symm

/-- For finite vertices and integer-lattice charges, existence of any bounded-
discrepancy path is equivalent to existence of an eventually periodic one.
The witness is offline and existential. -/
theorem exists_boundedDiscrepancy_iff_exists_eventuallyPeriodic
    [Finite V] {κ : Type uκ} (edgeCharge : E → κ → ℤ) (start : V) :
    (∃ walk : G.InfiniteWalk start, walk.HasBoundedDiscrepancy edgeCharge) ↔
      ∃ walk : G.InfiniteWalk start,
        walk.HasBoundedDiscrepancy edgeCharge ∧ walk.IsEventuallyPeriodic := by
  constructor
  · rintro ⟨walk, hbounded⟩
    obtain ⟨lasso⟩ := G.exists_zeroChargeLasso_of_boundedDiscrepancy
      edgeCharge start walk hbounded
    exact lasso.exists_eventuallyPeriodic_boundedDiscrepancy
  · rintro ⟨walk, hbounded, _⟩
    exact ⟨walk, hbounded⟩

/-- The bounded-discrepancy pigeonhole certificate also yields a reachable
connected integer circulation. This is the extraction direction of the
circulation equivalence below. -/
theorem exists_reachableConnectedIntegerCirculation_of_boundedDiscrepancy
    [Finite V] [Fintype E] [DecidableEq V]
    {κ : Type uκ} (edgeCharge : E → κ → ℤ) (start : V)
    (walk : G.InfiniteWalk start)
    (hbounded : walk.HasBoundedDiscrepancy edgeCharge) :
    Nonempty (G.ReachableConnectedIntegerCirculation edgeCharge start) := by
  classical
  obtain ⟨lasso⟩ := G.exists_zeroChargeLasso_of_boundedDiscrepancy
    edgeCharge start walk hbounded
  exact ⟨lasso.toReachableConnectedIntegerCirculation⟩

/-- Exact finite certificate theorem for offline bounded discrepancy.  Over a
finite vertex set and an integer charge lattice, a bounded-discrepancy walk
exists exactly when a reachable connected zero-charge integer circulation
exists.  The reverse construction is eventually periodic. -/
theorem exists_boundedDiscrepancy_iff_reachableConnectedIntegerCirculation
    [Finite V] [Fintype E] [DecidableEq V]
    {κ : Type uκ} (edgeCharge : E → κ → ℤ) (start : V) :
    (∃ walk : G.InfiniteWalk start,
      walk.HasBoundedDiscrepancy edgeCharge) ↔
      Nonempty (G.ReachableConnectedIntegerCirculation edgeCharge start) := by
  classical
  constructor
  · rintro ⟨walk, hbounded⟩
    exact G.exists_reachableConnectedIntegerCirculation_of_boundedDiscrepancy
      edgeCharge start walk hbounded
  · rintro ⟨circulation⟩
    obtain ⟨walk, hbounded, _⟩ :=
      circulation.exists_eventuallyPeriodic_boundedDiscrepancy
    exact ⟨walk, hbounded⟩

end EdgeGraph

end BoundedDiscrepancy

end GameTheory
