import GameTheory.Finite.BimatrixPath
import GameTheory.Math.FacetOrientation
import GameTheory.Math.ComplementaryPortOrder
import GameTheory.Math.OrientedInvolutionPath

/-! Determinant orientation of almost complementary bimatrix path ports.
Signed canonical facet minors reverse across a positive pivot. Counting payoff
variables outside the dropped label reverses the two ports of an internal node.
Calibrating this sign against the source gives actual directed path pointers.
-/
namespace GameTheory.Finite.BimatrixPathPort
open GameTheory.Math GameTheory.Math.CanonicalDictionary
open FacetOrientation ComplementaryPortOrder
variable {m n : ℕ} {A B : Fin m → Fin n → ℤ} {d : Fin (m + n)}

private noncomputable def scoreAt (basis : BimatrixBasis A B)
    (entering : BimatrixVariable m n) (he : entering ∉ basis.basic) (d : Fin (m + n)) : ℚ :=
  canonicalOrientation (bimatrixBasisColumns A B) (insert entering basis.basic)
    ((Finset.card_insert_of_notMem he).trans (congrArg (· + 1) basis.cardinality))
    entering (Finset.mem_insert_self _ _) * payoffParity (insert entering basis.basic) d

/-- Signed facet determinant with complementary-label parity. -/
noncomputable def orientationScore (port : BimatrixPathPort A B d) : ℚ :=
  scoreAt port.node.basis port.entering port.toPivotPort.nonbasic d

theorem orientationScore_ne_zero (port : BimatrixPathPort A B d) :
    port.orientationScore ≠ 0 := by
  unfold orientationScore scoreAt
  apply mul_ne_zero
  · exact (canonicalOrientation_insert_ne_zero_iff (bimatrixBasisColumns A B)
      port.node.basis.basic port.node.basis.cardinality port.entering
      port.toPivotPort.nonbasic).mpr port.node.basis.feasible.1
  · exact pow_ne_zero _ (by norm_num)

/-- Opposite pivot ports use the same augmented set of system columns. -/
theorem pivot_augmented (port : BimatrixPathPort A B d)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    insert (port.pivot hm hn hA hB).entering (port.pivot hm hn hA hB).node.basis.basic =
      insert port.entering port.node.basis.basic := by
  let l := port.toPivotPort.leavingRow hm hn hA hB
  let old := port.toPivotPort.leavingVariable l
  change insert old (FiniteBasisExchange.exchange port.node.basis.basic old port.entering) = _
  have hold : old ∈ port.node.basis.basic := Finset.orderEmbOfFin_mem _ _ l
  rw [FiniteBasisExchange.exchange, Finset.insert_comm old port.entering,
    Finset.insert_erase hold]

private theorem canonicalOrientation_congr
    (columns : Matrix (Fin (m + n)) (BimatrixVariable m n) ℚ)
    {S T : Finset (BimatrixVariable m n)} (hS : S.card = m + n + 1)
    (hT : T.card = m + n + 1) (a b : BimatrixVariable m n) (ha : a ∈ S) (hb : b ∈ T)
    (hST : S = T) (hab : a = b) :
    canonicalOrientation columns S hS a ha = canonicalOrientation columns T hT b hb := by
  cases hST
  cases hab
  rfl

/-- Pivoting reverses the signed facet orientation by a strictly positive direction. -/
theorem orientationScore_pivot (port : BimatrixPathPort A B d)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    (port.pivot hm hn hA hB).orientationScore =
      -((basisMatrix (bimatrixBasisColumns A B) port.node.basis.basic port.node.basis.cardinality)⁻¹.mulVec
        (fun i => bimatrixBasisColumns A B i port.entering)
          (port.toPivotPort.leavingRow hm hn hA hB)) * port.orientationScore := by
  let next := port.pivot hm hn hA hB
  let l := port.toPivotPort.leavingRow hm hn hA hB
  have hfacet := canonicalOrientation_congr (bimatrixBasisColumns A B)
    ((Finset.card_insert_of_notMem next.toPivotPort.nonbasic).trans
      (congrArg (· + 1) next.node.basis.cardinality))
    ((Finset.card_insert_of_notMem port.toPivotPort.nonbasic).trans
      (congrArg (· + 1) port.node.basis.cardinality))
    next.entering (port.node.basis.basic.orderEmbOfFin port.node.basis.cardinality l)
    (Finset.mem_insert_self _ _)
    (Finset.mem_insert_of_mem (Finset.orderEmbOfFin_mem _ _ l))
    (port.pivot_augmented hm hn hA hB) rfl
  have hpar := congrArg (fun S => payoffParity (R := ℚ) S d)
    (port.pivot_augmented hm hn hA hB)
  have h := canonical_exchange_orientation (bimatrixBasisColumns A B)
    port.node.basis.basic port.node.basis.cardinality port.entering port.toPivotPort.nonbasic
    l port.node.basis.feasible.1
  exact (congrArg₂ (fun x y : ℚ => x * y) hfacet hpar).trans
    ((congrArg (fun x : ℚ => x * payoffParity (insert port.entering port.node.basis.basic) d) h).trans
      (mul_assoc _ _ _))

private theorem twin_score (basis : BimatrixBasis A B) (k d : Fin (m + n))
    (hf : toLex (k, false) ∉ basis.basic) (ht : toLex (k, true) ∉ basis.basic)
    (hd : k ≠ d) :
    scoreAt basis (toLex (k, true)) ht d = -scoreAt basis (toLex (k, false)) hf d := by
  unfold scoreAt
  rw [canonicalOrientation_insert (bimatrixBasisColumns A B) basis.basic basis.cardinality
      (toLex (k, true)) ht,
    canonicalOrientation_insert (bimatrixBasisColumns A B) basis.basic basis.cardinality
      (toLex (k, false)) hf]
  have hi := twin_index basis.basic basis.cardinality k hf ht
  change labelIndex _ _ _ _ = labelIndex _ _ _ _ at hi
  rw [← hi, twin_payoffParity (R := ℚ) basis.basic k d ht hd]
  ring

private theorem scoreAt_congr (basis : BimatrixBasis A B)
    (e f : BimatrixVariable m n) (he : e ∉ basis.basic) (hf : f ∉ basis.basic)
    (h : e = f) : scoreAt basis e he d = scoreAt basis f hf d := by
  cases h
  rfl

/-- The two permitted ports of an internal node have opposite scores. -/
theorem orientationScore_switch (port : BimatrixPathPort A B d) (hne : port.switch ≠ port) :
    port.switch.orientationScore = -port.orientationScore := by
  have hd : (ofLex port.entering).1 ≠ d := by
    intro hd
    apply hne
    refine BimatrixPathPort.ext (port := port.switch) (other := port) rfl ?_
    simp only [switch, ComplementaryPorts.switch, hd, ↓reduceIte, toLex_ofLex]
  have hp := port.permitted.2.resolve_left hd
  have hf := (port.node.basis.mem_nonbasic ((ofLex port.entering).1, false)).mp hp.1
  have ht := (port.node.basis.mem_nonbasic ((ofLex port.entering).1, true)).mp hp.2
  rcases hv : ofLex port.entering with ⟨k, b⟩
  have he : port.entering = toLex (k, b) := congrArg toLex hv
  have hkd : k ≠ d := by simpa only [hv] using hd
  have hswitch : port.switch.entering = toLex (k, !b) := by
    change toLex (ComplementaryPorts.switch _ d (ofLex port.entering)) = _
    simp only [ComplementaryPorts.switch, hv, ite_eq_right hkd]
  simp only [hv] at hf ht hd
  have hh := twin_score port.node.basis k d hf ht hd
  cases b
  · calc
      port.switch.orientationScore = scoreAt port.node.basis (toLex (k, true)) ht d :=
        scoreAt_congr _ _ _ _ _ hswitch
      _ = -scoreAt port.node.basis (toLex (k, false)) hf d := hh
      _ = -port.orientationScore := congrArg Neg.neg (scoreAt_congr _ _ _ _ _ he).symm
  · calc
      port.switch.orientationScore = scoreAt port.node.basis (toLex (k, false)) hf d :=
        scoreAt_congr _ _ _ _ _ hswitch
      _ = -scoreAt port.node.basis (toLex (k, true)) ht d := by
        simpa only [neg_neg] using (congrArg Neg.neg hh).symm
      _ = -port.orientationScore := congrArg Neg.neg (scoreAt_congr _ _ _ _ _ he).symm

/-- Source-calibrated direction bit, computed from the exact rational orientation. -/
noncomputable def color (port : BimatrixPathPort A B d) : Bool :=
  decide (0 < port.orientationScore * (bimatrixSourcePort A B d).orientationScore)

private theorem decide_sign_neg_mul (x a : ℚ) (hx : x ≠ 0) (ha : 0 < a) :
    decide (0 < -a * x) = !decide (0 < x) := by
  have h : 0 < -a * x ↔ ¬0 < x := by
    constructor
    · intro h hp
      exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) hp.le)) h
    · intro h
      have hn : x < 0 := lt_of_le_of_ne (le_of_not_gt h) hx
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos ha) hn
  simp only [h, decide_not]

theorem color_pivot (port : BimatrixPathPort A B d)
    (hm : 0 < m) (hn : 0 < n) (hA : ∀ i j, 0 < A i j) (hB : ∀ i j, 0 < B i j) :
    (port.pivot hm hn hA hB).color = !port.color := by
  unfold color
  rw [orientationScore_pivot, mul_assoc]
  exact decide_sign_neg_mul _ _
    (mul_ne_zero port.orientationScore_ne_zero (bimatrixSourcePort A B d).orientationScore_ne_zero)
    (port.toPivotPort.leavingRow_spec hm hn hA hB).1

theorem color_switch (port : BimatrixPathPort A B d) (hne : port.switch ≠ port) :
    port.switch.color = !port.color := by
  unfold color
  rw [orientationScore_switch port hne, neg_mul]
  simpa only [neg_one_mul] using decide_sign_neg_mul
    (port.orientationScore * (bimatrixSourcePort A B d).orientationScore) 1
    (mul_ne_zero port.orientationScore_ne_zero (bimatrixSourcePort A B d).orientationScore_ne_zero)
    (by norm_num)

theorem source_color : (bimatrixSourcePort A B d).color = true := by
  unfold color
  exact decide_eq_true (mul_self_pos.mpr (bimatrixSourcePort A B d).orientationScore_ne_zero)

end GameTheory.Finite.BimatrixPathPort
