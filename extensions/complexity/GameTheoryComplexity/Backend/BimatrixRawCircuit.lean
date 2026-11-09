module

public import GameTheoryComplexity.Backend.BimatrixRawGate

@[expose] public section

/-! A single paired-action game evaluates a checked native circuit code.
Only the relocated live memo wires need input approximation bounds. Each
comparator resets its output error to the common block normalization bound,
independently of circuit depth. -/

namespace GameTheory.Complexity.Backend.BimatrixRawCircuit

open Cslib.Circuits
open GameTheory.Finite GameTheory.Finite.BimatrixCertificate
open GameTheory.Finite.BimatrixAffineGate GameTheory.Finite.BimatrixGateProgram

variable {k : ℕ}

/-- Every live wire in native evaluation retains the common approximation bound. -/
theorem evalCode_correct_at (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (ε : ℚ)
    (hε : ε < 1 / 4) (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (offset : ℕ) (gates : List (CircuitFormat.signature.Op × List ℕ)) (memo : List Bool)
    (htopo : Program.IsCodeFrom CircuitFormat.signature memo.length 0 gates)
    (hsize : offset + memo.length + gates.length ≤ k)
    (hplace : ∀ t : Fin gates.length,
      ∀ href : Program.IsCodeFrom CircuitFormat.signature k 0
        [(gates[t].1, gates[t].2.map (offset + ·))],
      g ⟨offset + memo.length + t.val, by omega⟩ =
        BimatrixRawGate.gate (gates[t].1, gates[t].2.map (offset + ·)) href)
    (hinput : ∀ j : Fin k, offset ≤ j.val → j.val < offset + memo.length →
      |(k : ℚ) * value c j - (if memo.getD (j.val - offset) false then 1 else 0)| ≤ ε) :
    ∀ j : Fin k, offset ≤ j.val →
      j.val < offset + (evalCode CircuitFormat.interpretation false memo gates).length →
      |(k : ℚ) * value c j -
        (if (evalCode CircuitFormat.interpretation false memo gates).getD
          (j.val - offset) false then 1 else 0)| ≤ ε := by
  induction gates generalizing memo with
  | nil => exact hinput
  | cons raw tail ih =>
    rcases raw with ⟨op, args⟩
    have hargs : args.length = 2 := htopo.1.1
    obtain ⟨left, right, rfl⟩ := List.length_eq_two.mp hargs
    have hleft : left < memo.length := htopo.1.2 left (by simp)
    have hright : right < memo.length := htopo.1.2 right (by simp)
    have hslot : offset + memo.length < k := by simp only [List.length_cons] at hsize; omega
    have hshift : Program.IsCodeFrom CircuitFormat.signature k 0
        [(op, [offset + left, offset + right])] := by
      refine ⟨⟨rfl, ?_⟩, trivial⟩
      intro i hi
      simp at hi
      rcases hi with rfl | rfl <;> omega
    let bit := CircuitFormat.opValue op (memo.getD left false) (memo.getD right false)
    have htail : Program.IsCodeFrom CircuitFormat.signature (memo ++ [bit]).length 0 tail := by
      apply Program.isCodeFrom_of_getElem
      intro j hj
      obtain ⟨harity, href⟩ := htopo.2.getElem j hj
      refine ⟨harity, ?_⟩
      intro i hi
      have hh := href i hi
      simp only [List.length_append, List.length_singleton]
      omega
    have hsz : offset + (memo ++ [bit]).length + tail.length ≤ k := by
      have hlen : ((op, [left, right]) :: tail).length = tail.length + 1 := rfl
      simp only [List.length_append, List.length_singleton]
      omega
    have hp : ∀ t : Fin tail.length,
        ∀ href : Program.IsCodeFrom CircuitFormat.signature k 0
          [(tail[t].1, tail[t].2.map (offset + ·))],
        g ⟨offset + (memo ++ [bit]).length + t.val, by omega⟩ =
          BimatrixRawGate.gate (tail[t].1, tail[t].2.map (offset + ·)) href := by
      intro t href
      have hh := hplace t.succ href
      change g ⟨offset + memo.length + (t.val + 1), _⟩ =
        BimatrixRawGate.gate (tail[t].1, tail[t].2.map (offset + ·)) href at hh
      simpa only [List.length_append, List.length_singleton, Fin.val_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
    have hnew : |(k : ℚ) * value c ⟨offset + memo.length, hslot⟩ -
        (if bit then 1 else 0)| ≤ ε := by
      have he := (BimatrixRawGate.gate_output_error H M
        (op, [offset + left, offset + right]) hshift hk g c hc hM hg hscale
        ⟨offset + memo.length, hslot⟩
        (by simpa using hplace ⟨0, by simp⟩ hshift)
        (memo.getD left false) (memo.getD right false) ε
        (by simpa only [List.getD_cons_zero, Nat.add_sub_cancel_left] using
          hinput ⟨offset + left, by omega⟩ (by dsimp; omega) (by dsimp; omega))
        (by simpa only [List.getD_cons_succ, List.getD_cons_zero,
          Nat.add_sub_cancel_left] using
          hinput ⟨offset + right, by omega⟩ (by dsimp; omega) (by dsimp; omega)) hε).trans hδ
      exact he
    have hin : ∀ j : Fin k, offset ≤ j.val → j.val < offset + (memo ++ [bit]).length →
        |(k : ℚ) * value c j -
          (if (memo ++ [bit]).getD (j.val - offset) false then 1 else 0)| ≤ ε := by
      intro j hj0 hj
      by_cases hlt : j.val - offset < memo.length
      · rw [List.getD_append _ _ _ _ hlt]
        exact hinput j hj0 (by omega)
      · have heq : j.val = offset + memo.length := by
          simp only [List.length_append, List.length_singleton] at hj
          omega
        have hjEq : j = ⟨offset + memo.length, hslot⟩ := Fin.ext heq
        simpa only [hjEq, Nat.add_sub_cancel_left,
          List.getD_append_right memo [bit] false memo.length (Nat.le_refl _),
          Nat.sub_self, List.getD_cons_zero] using hnew
    have heval : evalCode CircuitFormat.interpretation false memo ((op, [left, right]) :: tail) =
        evalCode CircuitFormat.interpretation false (memo ++ [bit]) tail := rfl
    rw [heval]
    exact ih (memo ++ [bit]) htail hsz hp hin

/-- Any valid designated circuit output is approximated at its relocated game slot. -/
theorem evalOutput_correct_at (H M : ℤ) (hk : 0 < k) (g : Fin k → Gate k)
    (c : BimatrixCertificate (k * 2) (k * 2))
    (hc : c.Valid (rowPayoff H (2 * (k : ℤ))) (columnPayoff H (2 * (k : ℤ)) g))
    (hM : 0 ≤ M) (hg : ∀ j r, |(g j).coefficients r| ≤ M)
    (hscale : (k : ℤ) * (M + 2 * (k : ℤ)) < H) (ε : ℚ)
    (hε : ε < 1 / 4) (hδ : (k : ℚ) * (((M + 2 * (k : ℤ) : ℤ) : ℚ) / H) ≤ ε)
    (offset : ℕ) (gates : List (CircuitFormat.signature.Op × List ℕ)) (input : List Bool)
    (htopo : Program.IsCodeFrom CircuitFormat.signature input.length 0 gates)
    (hsize : offset + input.length + gates.length ≤ k)
    (hplace : ∀ t : Fin gates.length,
      ∀ href : Program.IsCodeFrom CircuitFormat.signature k 0
        [(gates[t].1, gates[t].2.map (offset + ·))],
      g ⟨offset + input.length + t.val, by omega⟩ =
        BimatrixRawGate.gate (gates[t].1, gates[t].2.map (offset + ·)) href)
    (hinput : ∀ j : Fin k, offset ≤ j.val → j.val < offset + input.length →
      |(k : ℚ) * value c j - (if input.getD (j.val - offset) false then 1 else 0)| ≤ ε)
    (output : Fin (input.length + gates.length)) :
    |(k : ℚ) * value c ⟨offset + output.val, by omega⟩ -
      (if CircuitFormat.evalOutput input gates output.val then 1 else 0)| ≤ ε := by
  have h := evalCode_correct_at H M hk g c hc hM hg hscale ε hε hδ offset gates input
    htopo hsize hplace hinput ⟨offset + output.val, by omega⟩ (by dsimp; omega)
    (by simp only [length_evalCode]; omega)
  change |(k : ℚ) * value c ⟨offset + output.val, _⟩ -
    (if (evalCode CircuitFormat.interpretation false input gates).getD
      (offset + output.val - offset) false then 1 else 0)| ≤ ε at h
  rw [Nat.add_sub_cancel_left] at h
  exact h

end GameTheory.Complexity.Backend.BimatrixRawCircuit
