/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.List.Chain
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

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

variable {G}

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

end Walk

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

/-- A positive additive period forces a sequence on `ℕ` to have finite
range. -/
theorem finite_range_of_add_period {α : Type*} (sequence : ℕ → α)
    (period : ℕ) (hperiodPos : 0 < period)
    (hperiod : ∀ n, sequence (n + period) = sequence n) :
    Set.Finite (Set.range sequence) := by
  have hremainder : ∀ n, ∃ r < period, sequence n = sequence r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        by_cases hn : n < period
        · exact ⟨n, hn, rfl⟩
        · let earlier := n - period
          have hearlier : earlier < n := by
            dsimp [earlier]
            omega
          obtain ⟨r, hr, her⟩ := ih earlier hearlier
          refine ⟨r, hr, ?_⟩
          have hnEq : earlier + period = n := by
            dsimp [earlier]
            omega
          rw [← hnEq, hperiod earlier]
          exact her
  have hfiniteDomain : Set.Finite (↑(Finset.range period) : Set ℕ) :=
    Finset.finite_toSet _
  refine (hfiniteDomain.image sequence).subset ?_
  rintro value ⟨n, rfl⟩
  obtain ⟨r, hr, heq⟩ := hremainder n
  refine ⟨r, ?_, heq.symm⟩
  simpa using hr

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
  exact InfiniteWalk.finite_range_of_add_period
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

end ZeroChargeLasso

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

end EdgeGraph

end BoundedDiscrepancy

end GameTheory
