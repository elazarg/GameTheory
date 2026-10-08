import GameTheory.Finite.BimatrixPivot
import GameTheory.Finite.BimatrixBasisSolution
import GameTheory.Math.ComplementaryPorts
import Mathlib.Data.Fintype.Powerset

/-! Ports of almost complementary bimatrix paths.
A complementary node has one port at the dropped label. An internal node has
two ports at its unique duplicated nonbasic label. Pivots pair ports of distinct
bases; switching pairs the two ports of an internal node and fixes terminals.
-/
namespace GameTheory.Finite
open GameTheory.Math GameTheory.Math.CanonicalDictionary
variable {m n : ℕ} {A B : Fin m → Fin n → ℤ} {d : Fin (m + n)}

/-- A feasible almost complementary node with a permitted nonbasic entering variable. -/
structure BimatrixPathPort (A B : Fin m → Fin n → ℤ) (d : Fin (m + n)) where
  /-- The basis and coverage certificate of the underlying node. -/
  node : BimatrixPathNode A B d
  /-- The entering slack or payoff variable. -/
  entering : BimatrixVariable m n
  permitted : ComplementaryPorts.IsPort node.basis.nonbasic d (ofLex entering)

namespace BimatrixPathPort
@[ext] theorem ext {port other : BimatrixPathPort A B d}
    (hb : port.node.basis = other.node.basis) (he : port.entering = other.entering) :
    port = other := by
  rcases port with ⟨⟨pb, pc⟩, pe, ph⟩
  rcases other with ⟨⟨qb, qc⟩, qe, qh⟩
  cases hb
  cases he
  rfl

instance : Finite (BimatrixPathPort A B d) :=
  Finite.of_injective (fun port : BimatrixPathPort A B d => (port.node.basis.basic, port.entering))
    (by
      intro port other h
      apply ext
      · exact BimatrixBasis.ext (congrArg Prod.fst h)
      · exact congrArg Prod.snd h)

/-- Forget the complementary-label restrictions to obtain the underlying pivot port. -/
def toPivotPort (port : BimatrixPathPort A B d) : BimatrixPivotPort A B where
  basis := port.node.basis
  entering := port.entering
  nonbasic := by
    have h := (port.node.basis.mem_nonbasic (ofLex port.entering)).mp port.permitted.1
    simpa only [toLex_ofLex] using h

/-- Switch to the other port at an internal node; complementary ports are fixed. -/
def switch (port : BimatrixPathPort A B d) : BimatrixPathPort A B d where
  node := port.node
  entering := toLex (ComplementaryPorts.switch port.node.basis.nonbasic d (ofLex port.entering))
  permitted := ComplementaryPorts.switch_isPort port.permitted

theorem switch_switch (port : BimatrixPathPort A B d) : port.switch.switch = port := by
  apply ext
  · rfl
  · exact congrArg toLex (ComplementaryPorts.switch_switch _ _ _)

theorem switch_eq_self_iff (port : BimatrixPathPort A B d) :
    port.switch = port ↔ ComplementaryLabels.IsComplementary port.node.basis.nonbasic := by
  have hg := ComplementaryPorts.switch_eq_self_iff_complementary
    (by simpa using port.node.basis.nonbasic_card) port.node.coverage port.permitted
  constructor
  · intro h
    apply hg.mp
    exact congrArg ofLex (congrArg BimatrixPathPort.entering h)
  · intro h
    apply ext
    · rfl
    · exact congrArg toLex (hg.mpr h)

/-- The paired pivot remains a valid almost complementary path port. -/
noncomputable def pivot (port : BimatrixPathPort A B d)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    BimatrixPathPort A B d := by
  let l := port.toPivotPort.leavingRow hm hn hA hB
  let hl := port.toPivotPort.leavingRow_spec hm hn hA hB
  let old := port.toPivotPort.leavingVariable l
  have ho : ofLex old ∉ port.node.basis.nonbasic := by
    intro h
    have hh := (port.node.basis.mem_nonbasic (ofLex old)).mp h
    rw [toLex_ofLex] at hh
    exact hh (Finset.orderEmbOfFin_mem _ _ _)
  let next := port.node.exchange l port.entering port.toPivotPort.nonbasic hl port.permitted.2
  have hnbs : next.basis.nonbasic = FiniteBasisExchange.exchange port.node.basis.nonbasic
      (ofLex port.entering) (ofLex old) :=
    port.node.basis.nonbasic_exchange l port.entering port.toPivotPort.nonbasic hl
  refine ⟨next, old, ?_⟩
  rw [hnbs]
  exact ComplementaryPorts.exchange_isPort port.node.coverage port.permitted ho

@[simp] theorem toPivotPort_pivot (port : BimatrixPathPort A B d)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    (port.pivot hm hn hA hB).toPivotPort = port.toPivotPort.pivot hm hn hA hB := rfl

theorem pivot_pivot (port : BimatrixPathPort A B d)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    (port.pivot hm hn hA hB).pivot hm hn hA hB = port := by
  have hh : ((port.pivot hm hn hA hB).pivot hm hn hA hB).toPivotPort = port.toPivotPort := by
    rw [toPivotPort_pivot, toPivotPort_pivot]
    exact port.toPivotPort.pivot_pivot hm hn hA hB
  apply ext
  · exact congrArg BimatrixPivotPort.basis hh
  · exact congrArg BimatrixPivotPort.entering hh

theorem pivot_ne_self (port : BimatrixPathPort A B d)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    port.pivot hm hn hA hB ≠ port := by
  intro h
  have hh := congrArg toPivotPort h
  rw [toPivotPort_pivot] at hh
  exact port.toPivotPort.pivot_ne_self hm hn hA hB hh

/-- Every non-source switching terminal yields a nonzero rational complementary solution. -/
theorem terminal_solution (port : BimatrixPathPort A B d)
    (ht : port.switch = port) (hs : port.node.basis ≠ bimatrixSourceBasis A B) :
    port.node.basis.payoffPoint ≠ 0 ∧
      LinearComplementarity.IsSolution (fun _ => 1) (bimatrixComplementaryMatrix A B)
        port.node.basis.payoffPoint :=
  port.node.basis.nonzero_payoffPoint_isSolution (port.switch_eq_self_iff.mp ht) hs

end BimatrixPathPort

/-- The sole source port enters the dropped label's payoff variable. -/
def bimatrixSourcePort (A B : Fin m → Fin n → ℤ) (d : Fin (m + n)) :
    BimatrixPathPort A B d where
  node := bimatrixSourceNode A B d
  entering := toLex (d, true)
  permitted := ⟨(bimatrixSource_nonbasic_mem A B (d, true)).mpr rfl, Or.inl rfl⟩


/-- All-slack source labels are complementary. -/
theorem bimatrixSource_complementary (A B : Fin m → Fin n → ℤ) :
    ComplementaryLabels.IsComplementary (bimatrixSourceBasis A B).nonbasic := by
  intro i
  rw [bimatrixSource_nonbasic_mem A B (i, false),
    bimatrixSource_nonbasic_mem A B (i, true)]
  simp

theorem bimatrixSourcePort_switch (A B : Fin m → Fin n → ℤ) (d : Fin (m + n)) :
    (bimatrixSourcePort A B d).switch = bimatrixSourcePort A B d :=
  (bimatrixSourcePort A B d).switch_eq_self_iff.mpr (bimatrixSource_complementary A B)

/-- The artificial source basis supports a single dropped-label path port. -/
theorem bimatrixSourcePort_unique (port : BimatrixPathPort A B d)
    (hsource : port.node.basis = bimatrixSourceBasis A B) : port = bimatrixSourcePort A B d := by
  apply BimatrixPathPort.ext hsource
  have hp := port.permitted
  rw [hsource] at hp
  obtain ⟨hl, hm⟩ := (ComplementaryPorts.complementary_port_iff
    (bimatrixSource_complementary A B) (ofLex port.entering)).mp hp
  have hk := (bimatrixSource_nonbasic_mem A B (ofLex port.entering)).mp hm
  have hv : ofLex port.entering = (d, true) := Prod.ext hl hk
  exact congrArg toLex hv

/-- Every switching endpoint except the unique source supplies a nonzero solution. -/
theorem BimatrixPathPort.non_source_terminal_solution (port : BimatrixPathPort A B d)
    (ht : port.switch = port) (hs : port ≠ bimatrixSourcePort A B d) :
    port.node.basis.payoffPoint ≠ 0 ∧
      LinearComplementarity.IsSolution (fun _ => 1) (bimatrixComplementaryMatrix A B)
        port.node.basis.payoffPoint :=
  port.terminal_solution ht (fun h => hs (bimatrixSourcePort_unique port h))

end GameTheory.Finite
