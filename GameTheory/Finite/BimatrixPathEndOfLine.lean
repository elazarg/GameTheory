import GameTheory.Finite.BimatrixPathOrientation

/-! Directed End-of-Line paths on canonical bimatrix ports.
The determinant orientation supplies actual predecessor and successor pointers.
Endpoints are exactly complementary bases, and the unique artificial source is
the only endpoint representing zero payoff coordinates. Pointer computation is
mathematical here; binary codecs and machine-cost certificates are separate.
-/
namespace GameTheory.Finite.BimatrixPathPort
open GameTheory.Math
variable {m n : ℕ} {A B : Fin m → Fin n → ℤ} {d : Fin (m + n)}

/-- The outgoing pointer of the determinant-oriented complementary path. -/
noncomputable def successor (hm : 0 < m) (hn : 0 < n)
    (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    BimatrixPathPort A B d → BimatrixPathPort A B d :=
  OrientedInvolutionPath.successor (fun port => port.pivot hm hn hA hB) switch color

/-- The incoming pointer of the determinant-oriented complementary path. -/
noncomputable def predecessor (hm : 0 < m) (hn : 0 < n)
    (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    BimatrixPathPort A B d → BimatrixPathPort A B d :=
  OrientedInvolutionPath.predecessor (fun port => port.pivot hm hn hA hB) switch color

variable (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j)
include hm hn hA hB

theorem predecessor_successor (port : BimatrixPathPort A B d) (h : port.switch ≠ port) :
    predecessor hm hn hA hB (successor hm hn hA hB port) = port :=
  OrientedInvolutionPath.predecessor_successor _ _ _
    (fun port => port.pivot_pivot hm hn hA hB) switch_switch
    (fun port => port.color_pivot hm hn hA hB) color_switch port h

theorem successor_predecessor (port : BimatrixPathPort A B d) (h : port.switch ≠ port) :
    successor hm hn hA hB (predecessor hm hn hA hB port) = port :=
  OrientedInvolutionPath.successor_predecessor _ _ _
    (fun port => port.pivot_pivot hm hn hA hB) switch_switch
    (fun port => port.color_pivot hm hn hA hB) color_switch port h

/-- Directed endpoints are exactly the complementary-label terminals. -/
theorem isEndpoint_iff (port : BimatrixPathPort A B d) :
    EndOfLine.IsEndpoint (predecessor hm hn hA hB) (successor hm hn hA hB) port ↔
      ComplementaryLabels.IsComplementary port.node.basis.nonbasic :=
  (OrientedInvolutionPath.isEndpoint_iff _ _ _
    (fun port => port.pivot_pivot hm hn hA hB) switch_switch
    (fun port => port.pivot_ne_self hm hn hA hB)
    (fun port => port.color_pivot hm hn hA hB) color_switch port).trans port.switch_eq_self_iff

/-- The canonical source has no incoming edge and a consistent nontrivial outgoing edge. -/
theorem source_pointers (d : Fin (m + n)) :
    predecessor hm hn hA hB (bimatrixSourcePort A B d) = bimatrixSourcePort A B d ∧
      successor hm hn hA hB (bimatrixSourcePort A B d) ≠ bimatrixSourcePort A B d ∧
        predecessor hm hn hA hB (successor hm hn hA hB (bimatrixSourcePort A B d)) =
          bimatrixSourcePort A B d :=
  OrientedInvolutionPath.source_pointers _ _ _
    (fun port => port.pivot_pivot hm hn hA hB)
    (fun port => port.pivot_ne_self hm hn hA hB)
    (fun port => port.color_pivot hm hn hA hB) (bimatrixSourcePort A B d)
    (bimatrixSourcePort_switch A B d) source_color

/-- Every directed endpoint except the known source yields a nonzero rational solution. -/
theorem endpoint_solution (port : BimatrixPathPort A B d)
    (he : EndOfLine.IsEndpoint (predecessor hm hn hA hB) (successor hm hn hA hB) port)
    (hs : port ≠ bimatrixSourcePort A B d) :
    port.node.basis.payoffPoint ≠ 0 ∧
      LinearComplementarity.IsSolution (fun _ => 1) (bimatrixComplementaryMatrix A B)
        port.node.basis.payoffPoint :=
  port.non_source_terminal_solution (port.switch_eq_self_iff.mpr
    ((isEndpoint_iff hm hn hA hB port).mp he)) hs

/-- The finite directed graph has an endpoint distinct from its canonical source. -/
theorem exists_endpoint_ne_source (d : Fin (m + n)) :
    ∃ port : BimatrixPathPort A B d, port ≠ bimatrixSourcePort A B d ∧
      EndOfLine.IsEndpoint (predecessor hm hn hA hB) (successor hm hn hA hB) port := by
  classical
  let := Fintype.ofFinite (BimatrixPathPort A B d)
  obtain ⟨hp, hs, hlink⟩ := source_pointers hm hn hA hB d
  exact EndOfLine.exists_endpoint_ne_origin _ _ _ hp hs hlink

/-- Positive nonempty bimatrix games have a nonzero rational complementary solution. -/
theorem exists_nonzero_complementary_solution :
    ∃ z : Fin m ⊕ Fin n → ℚ, z ≠ 0 ∧
      LinearComplementarity.IsSolution (fun _ => 1) (bimatrixComplementaryMatrix A B) z := by
  let dropped : Fin (m + n) := ⟨0, by omega⟩
  obtain ⟨port, hs, he⟩ := exists_endpoint_ne_source hm hn hA hB dropped
  exact ⟨port.node.basis.payoffPoint, endpoint_solution hm hn hA hB port he hs⟩

end GameTheory.Finite.BimatrixPathPort
