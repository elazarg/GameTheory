/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Basic
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

end Walk

/-- An infinite directed walk from a prescribed initial vertex.  Its vertex
at time `n` is derived from the preceding edge, so the only compatibility data
are the initial source and consecutive edge endpoints. -/
structure InfiniteWalk (start : V) where
  edge : ℕ → E
  source_zero : G.source (edge 0) = start
  consecutive : ∀ n, G.target (edge n) = G.source (edge (n + 1))

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

end EdgeGraph

end BoundedDiscrepancy

end GameTheory
