import GameTheory.Finite.BimatrixPathEndOfLine
import GameTheory.Math.OrientedInvolutionPathWitness

/-! Soundness of raw witnesses on the canonical complementary path.
An inconsistent pointer identifies a complementary non-source basis, including
when the outgoing branch of the witness carries no explicit source exclusion. -/
namespace GameTheory.Finite.BimatrixPathPort
open GameTheory.Math
variable {m n : ℕ} {A B : Fin m → Fin n → ℤ} {d : Fin (m + n)}

/-- Raw pointer inconsistencies are precisely switching terminals away from the source. -/
theorem rawWitness_iff (hm : 0 < m) (hn : 0 < n)
    (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) (port : BimatrixPathPort A B d) :
    EndOfLine.RawWitness (predecessor hm hn hA hB) (successor hm hn hA hB)
      (bimatrixSourcePort A B d) port ↔ port.switch = port ∧ port ≠ bimatrixSourcePort A B d :=
  OrientedInvolutionPath.rawWitness_iff _ _ _
    (fun p => p.pivot_pivot hm hn hA hB) switch_switch
    (fun p => p.pivot_ne_self hm hn hA hB)
    (fun p => p.color_pivot hm hn hA hB) color_switch
    (bimatrixSourcePort A B d) (bimatrixSourcePort_switch A B d) source_color port

/-- Every raw witness has a complementary basis distinct from the artificial source. -/
theorem rawWitness_terminal (hm : 0 < m) (hn : 0 < n)
    (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) (port : BimatrixPathPort A B d)
    (hw : EndOfLine.RawWitness (predecessor hm hn hA hB) (successor hm hn hA hB)
      (bimatrixSourcePort A B d) port) :
    port.switch = port ∧ ComplementaryLabels.IsComplementary port.node.basis.nonbasic ∧
      port.node.basis ≠ bimatrixSourceBasis A B := by
  obtain ⟨ht, hn⟩ := (rawWitness_iff hm hn hA hB port).mp hw
  exact ⟨ht, port.switch_eq_self_iff.mp ht, fun hb => hn (bimatrixSourcePort_unique port hb)⟩

end GameTheory.Finite.BimatrixPathPort
