module

public import Complexity.Computability.Complexity.Classes.TFNP.Subclasses
public import Complexity.Computability.Complexity.Classes.TFNP.Subclasses.Principles
public import GameTheory.Math.EndOfLine

@[expose] public section

/-! The native active-edge convention and mutually consistent pointers describe
the same graph when the predecessor fixes the distinguished zero vertex. A
genuine source then turns native parity witnesses into non-source endpoints. -/

namespace GameTheory.Complexity.Backend.NativeEndOfLine

variable {α : Type} (n : α → ℕ) (P S : α × List Bool → List Bool) (a : α)

/-- Fixing the source predecessor makes its exclusion from outgoing edges automatic. -/
theorem hasOut_iff_hasSuccessor
    (hP : P (a, Cslib.Complexity.zeroVertex (n a)) =
      Cslib.Complexity.zeroVertex (n a)) (u : List Bool) :
    Cslib.Complexity.hasOut n P S a u = true ↔
      GameTheory.Math.EndOfLine.HasSuccessor (fun v => P (a, v)) (fun v => S (a, v)) u := by
  simp only [Cslib.Complexity.hasOut, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨h.2.1, h.1⟩
  · intro h
    refine ⟨h.2, h.1, ?_⟩
    intro hz
    have hu : u = Cslib.Complexity.zeroVertex (n a) := by
      simpa only [hz, hP] using h.2.symm
    exact h.1 (hz.trans hu.symm)

/-- A fixed predecessor at the source already prevents an incoming edge there. -/
theorem hasIn_iff_hasPredecessor
    (hP : P (a, Cslib.Complexity.zeroVertex (n a)) =
      Cslib.Complexity.zeroVertex (n a)) (u : List Bool) :
    Cslib.Complexity.hasIn n P S a u = true ↔
      GameTheory.Math.EndOfLine.HasPredecessor (fun v => P (a, v)) (fun v => S (a, v)) u := by
  simp only [Cslib.Complexity.hasIn, decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨h.2.1, h.1⟩
  · intro h
    refine ⟨h.2, h.1, ?_⟩
    rintro rfl
    exact h.1 hP

/-- With a genuine source, native parity witnesses are exactly fixed-width
endpoints different from that source. -/
theorem endOfLineRel_iff
    (hP : P (a, Cslib.Complexity.zeroVertex (n a)) =
      Cslib.Complexity.zeroVertex (n a))
    (hS : S (a, Cslib.Complexity.zeroVertex (n a)) ≠
      Cslib.Complexity.zeroVertex (n a))
    (hlink : P (a, S (a, Cslib.Complexity.zeroVertex (n a))) =
      Cslib.Complexity.zeroVertex (n a)) (u : List Bool) :
    Cslib.Complexity.endOfLineRel n P S a u ↔
      u.length = n a ∧ u ≠ Cslib.Complexity.zeroVertex (n a) ∧
        GameTheory.Math.EndOfLine.IsEndpoint (fun v => P (a, v)) (fun v => S (a, v)) u := by
  by_cases hu : u = Cslib.Complexity.zeroVertex (n a)
  · subst u
    have hout : Cslib.Complexity.hasOut n P S a
        (Cslib.Complexity.zeroVertex (n a)) = true :=
      (hasOut_iff_hasSuccessor n P S a hP _).mpr ⟨hS, hlink⟩
    simp [Cslib.Complexity.endOfLineRel, hout]
  · have hin := hasIn_iff_hasPredecessor n P S a hP u
    have hout := hasOut_iff_hasSuccessor n P S a hP u
    simp only [GameTheory.Math.EndOfLine.IsEndpoint, ← hin, ← hout]
    cases hi : Cslib.Complexity.hasIn n P S a u <;>
      cases ho : Cslib.Complexity.hasOut n P S a u <;>
        simp [Cslib.Complexity.endOfLineRel, hi, ho, hu]

/-- Keep only native active incoming edges; inactive pointers become self-loops. -/
def activePredecessor (input : α × List Bool) : List Bool :=
  if Cslib.Complexity.hasIn n P S input.1 input.2 then P input else input.2

/-- Filtering incoming edges always fixes the distinguished source. -/
@[simp] theorem activePredecessor_zero :
    activePredecessor n P S (a, Cslib.Complexity.zeroVertex (n a)) =
      Cslib.Complexity.zeroVertex (n a) := by
  simp [activePredecessor, Cslib.Complexity.hasIn]

open Turing.MultiTapeTM in
/-- Active-edge filtering composes native machines on the full instance/vertex input. -/
@[fun_prop] theorem activePredecessor_polyTime {enc : α ↪ List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits) :
    ComputableInPolyTime (activePredecessor n P S) (encPair enc encBits) encBits :=
  (Cslib.Complexity.computableInPolyTime_hasIn hn hP hS).ite hP (.snd enc encBits)

open Turing.MultiTapeTM in
@[fun_prop] theorem ppadToPppMap_polyTime {enc : α ↪ List Bool}
    (hn : ComputableInPolyTime n enc encUnary)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBits)
    (hS : ComputableInPolyTime S (encPair enc encBits) encBits) :
    ComputableInPolyTime (Cslib.Complexity.ppadToPppMap n P S) (encPair enc encBits) encBits :=
  (Cslib.Complexity.computableInPolyTime_hasOut hn hP hS).ite hS (.snd enc encBits)

/-- Filtering inactive edges gives exactly the native outgoing-edge predicate. -/
theorem hasSuccessor_active_iff (u : List Bool) :
    GameTheory.Math.EndOfLine.HasSuccessor
      (fun v => activePredecessor n P S (a, v))
      (fun v => Cslib.Complexity.ppadToPppMap n P S (a, v)) u ↔
      Cslib.Complexity.hasOut n P S a u = true := by
  cases hout : Cslib.Complexity.hasOut n P S a u with
  | false =>
    simp [GameTheory.Math.EndOfLine.HasSuccessor, Cslib.Complexity.ppadToPppMap, hout]
  | true =>
    have hin := Cslib.Complexity.hasIn_of_hasOut hout
    have hparts : P (a, S (a, u)) = u ∧ S (a, u) ≠ u ∧
        S (a, u) ≠ Cslib.Complexity.zeroVertex (n a) := by
      simpa only [Cslib.Complexity.hasOut, decide_eq_true_eq] using hout
    simp [GameTheory.Math.EndOfLine.HasSuccessor, activePredecessor,
      Cslib.Complexity.ppadToPppMap, hout, hin, hparts.1, hparts.2.1]

/-- Filtering inactive edges gives exactly the native incoming-edge predicate. -/
theorem hasPredecessor_active_iff (u : List Bool) :
    GameTheory.Math.EndOfLine.HasPredecessor
      (fun v => activePredecessor n P S (a, v))
      (fun v => Cslib.Complexity.ppadToPppMap n P S (a, v)) u ↔
      Cslib.Complexity.hasIn n P S a u = true := by
  cases hin : Cslib.Complexity.hasIn n P S a u with
  | false =>
    simp [GameTheory.Math.EndOfLine.HasPredecessor, activePredecessor, hin]
  | true =>
    have hout := Cslib.Complexity.hasOut_of_hasIn hin
    have hparts : S (a, P (a, u)) = u ∧ P (a, u) ≠ u ∧
        u ≠ Cslib.Complexity.zeroVertex (n a) := by
      simpa only [Cslib.Complexity.hasIn, decide_eq_true_eq] using hin
    simp [GameTheory.Math.EndOfLine.HasPredecessor, activePredecessor,
      Cslib.Complexity.ppadToPppMap, hin, hout, hparts.1, hparts.2.1]

/-- Endpoints of filtered pointers are exactly native parity imbalances. -/
theorem isEndpoint_active_iff (u : List Bool) :
    GameTheory.Math.EndOfLine.IsEndpoint
      (fun v => activePredecessor n P S (a, v))
      (fun v => Cslib.Complexity.ppadToPppMap n P S (a, v)) u ↔
      (Cslib.Complexity.hasIn n P S a u != Cslib.Complexity.hasOut n P S a u) = true := by
  simp only [GameTheory.Math.EndOfLine.IsEndpoint, hasSuccessor_active_iff,
    hasPredecessor_active_iff]
  cases hin : Cslib.Complexity.hasIn n P S a u <;>
    cases hout : Cslib.Complexity.hasOut n P S a u <;> decide

/-- The filtered pointers have a genuine source exactly when its native outgoing edge is active. -/
theorem active_source_iff :
    (activePredecessor n P S (a, Cslib.Complexity.zeroVertex (n a)) =
        Cslib.Complexity.zeroVertex (n a) ∧
      Cslib.Complexity.ppadToPppMap n P S (a, Cslib.Complexity.zeroVertex (n a)) ≠
        Cslib.Complexity.zeroVertex (n a) ∧
      activePredecessor n P S
        (a, Cslib.Complexity.ppadToPppMap n P S (a, Cslib.Complexity.zeroVertex (n a))) =
        Cslib.Complexity.zeroVertex (n a)) ↔
      Cslib.Complexity.hasOut n P S a (Cslib.Complexity.zeroVertex (n a)) = true := by
  constructor
  · rintro ⟨_, hne, hlink⟩
    exact (hasSuccessor_active_iff n P S a _).mp ⟨hne, hlink⟩
  · intro hout
    exact ⟨activePredecessor_zero n P S a,
      (hasSuccessor_active_iff n P S a _).mpr hout⟩

/-- Filtering preserves a width invariant carried by the original predecessor. -/
theorem activePredecessor_length
    (hP : ∀ u, u.length = n a → (P (a, u)).length = n a)
    (u : List Bool) (hu : u.length = n a) :
    (activePredecessor n P S (a, u)).length = n a := by
  unfold activePredecessor
  split
  · exact hP u hu
  · exact hu

/-- Every non-source endpoint of the filtered pointers is a native search answer. -/
theorem endOfLineRel_of_active_endpoint (u : List Bool) (hlen : u.length = n a)
    (hne : u ≠ Cslib.Complexity.zeroVertex (n a))
    (hend : GameTheory.Math.EndOfLine.IsEndpoint
      (fun v => activePredecessor n P S (a, v))
      (fun v => Cslib.Complexity.ppadToPppMap n P S (a, v)) u) :
    Cslib.Complexity.endOfLineRel n P S a u := by
  have hxor := (isEndpoint_active_iff n P S a u).mp hend
  simp [Cslib.Complexity.endOfLineRel, hlen, hne, hxor]

end GameTheory.Complexity.Backend.NativeEndOfLine
