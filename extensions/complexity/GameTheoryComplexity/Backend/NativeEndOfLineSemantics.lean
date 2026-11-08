module

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

end GameTheory.Complexity.Backend.NativeEndOfLine
