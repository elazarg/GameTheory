import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Mathlib.Algebra.Ring.Basic

/-! Canonical ordering and parity of complementary ports.
If a variable set contains neither variable of a label, inserting either one
places it at the same sorted index. Counting payoff variables outside a
designated label changes parity when those two ports are exchanged.
-/

namespace GameTheory.Math.ComplementaryPortOrder

variable {α : Type*} [LinearOrder α] {n : ℕ}

omit [LinearOrder α] in
private theorem label_ne_of_mem (s : Finset (α ×ₗ Bool)) (k : α)
    (hf : toLex (k, false) ∉ s) (ht : toLex (k, true) ∉ s)
    (v : α ×ₗ Bool) (hv : v ∈ s) : (ofLex v).1 ≠ k := by
  intro he
  have hv' : v = toLex (k, (ofLex v).2) := by
    apply ofLex.injective
    exact Prod.ext he rfl
  cases hb : (ofLex v).2
  · rw [hb] at hv'
    rw [hv'] at hv
    exact hf hv
  · rw [hb] at hv'
    rw [hv'] at hv
    exact ht hv

private theorem port_lt_iff {k : α} {v : α ×ₗ Bool} (b : Bool)
    (hv : (ofLex v).1 ≠ k) : toLex (k, b) < v ↔ k < (ofLex v).1 := by
  change toLex (k, b) < toLex (ofLex v) ↔ _
  rw [Prod.Lex.toLex_lt_toLex]
  simp [Ne.symm hv]

private theorem lt_port_iff {k : α} {v : α ×ₗ Bool} (b : Bool)
    (hv : (ofLex v).1 ≠ k) : v < toLex (k, b) ↔ (ofLex v).1 < k := by
  change toLex (ofLex v) < toLex (k, b) ↔ _
  rw [Prod.Lex.toLex_lt_toLex]
  simp [hv]

private def replacePort (k : α) (v : α ×ₗ Bool) : α ×ₗ Bool :=
  if v = toLex (k, false) then toLex (k, true) else v

private theorem replacePort_mem (s : Finset (α ×ₗ Bool)) (k : α)
    (v : α ×ₗ Bool) (hv : v ∈ insert (toLex (k, false)) s) :
    replacePort k v ∈ insert (toLex (k, true)) s := by
  by_cases he : v = toLex (k, false)
  · simp [replacePort, he]
  · simp only [replacePort, he, ↓reduceIte]
    exact Finset.mem_insert_of_mem ((Finset.mem_insert.mp hv).resolve_left he)

private theorem replacePort_strictMonoOn (s : Finset (α ×ₗ Bool)) (k : α)
    (hf : toLex (k, false) ∉ s) (ht : toLex (k, true) ∉ s) :
    StrictMonoOn (replacePort k) (↑(insert (toLex (k, false)) s) : Set (α ×ₗ Bool)) := by
  intro x hx y hy hxy
  by_cases hxf : x = toLex (k, false)
  · subst x
    have hyf : y ≠ toLex (k, false) := ne_of_gt hxy
    have hym := (Finset.mem_insert.mp hy).resolve_left hyf
    have hyl := label_ne_of_mem s k hf ht y hym
    simp only [replacePort, ↓reduceIte, hyf]
    exact (port_lt_iff true hyl).mpr ((port_lt_iff false hyl).mp hxy)
  · by_cases hyf : y = toLex (k, false)
    · subst y
      have hxm := (Finset.mem_insert.mp hx).resolve_left hxf
      have hxl := label_ne_of_mem s k hf ht x hxm
      simp only [replacePort, hxf, ↓reduceIte]
      exact (lt_port_iff true hxl).mpr ((lt_port_iff false hxl).mp hxy)
    · simpa only [replacePort, hxf, hyf, ↓reduceIte] using hxy

/-- The two complementary ports occupy the same canonical sorted coordinate. -/
theorem twin_index (s : Finset (α ×ₗ Bool)) (hs : s.card = n) (k : α)
    (hf : toLex (k, false) ∉ s) (ht : toLex (k, true) ∉ s) :
    ((insert (toLex (k, false)) s).orderIsoOfFin
      ((Finset.card_insert_of_notMem hf).trans (congrArg (· + 1) hs))).symm
        ⟨toLex (k, false), Finset.mem_insert_self _ _⟩ =
    ((insert (toLex (k, true)) s).orderIsoOfFin
      ((Finset.card_insert_of_notMem ht).trans (congrArg (· + 1) hs))).symm
        ⟨toLex (k, true), Finset.mem_insert_self _ _⟩ := by
  let sf := insert (toLex (k, false)) s
  let st := insert (toLex (k, true)) s
  have hsf : sf.card = n + 1 :=
    (Finset.card_insert_of_notMem hf).trans (congrArg (· + 1) hs)
  have hst : st.card = n + 1 :=
    (Finset.card_insert_of_notMem ht).trans (congrArg (· + 1) hs)
  have henum : (fun i : Fin (n + 1) => replacePort k (sf.orderEmbOfFin hsf i)) =
      st.orderEmbOfFin hst := by
    apply Finset.orderEmbOfFin_unique
    · intro i
      exact replacePort_mem s k _ (Finset.orderEmbOfFin_mem sf hsf i)
    · intro i j hij
      exact replacePort_strictMonoOn s k hf ht
        (Finset.orderEmbOfFin_mem sf hsf i) (Finset.orderEmbOfFin_mem sf hsf j)
        ((sf.orderEmbOfFin hsf).strictMono hij)
  let jf := (sf.orderIsoOfFin hsf).symm ⟨toLex (k, false), Finset.mem_insert_self _ _⟩
  have hjf : sf.orderEmbOfFin hsf jf = toLex (k, false) :=
    congrArg Subtype.val ((sf.orderIsoOfFin hsf).apply_symm_apply _)
  have hjt : st.orderEmbOfFin hst jf = toLex (k, true) := by
    rw [← congrFun henum jf, hjf]
    simp [replacePort]
  have he : st.orderIsoOfFin hst jf = ⟨toLex (k, true), Finset.mem_insert_self _ _⟩ :=
    Subtype.ext hjt
  apply (st.orderIsoOfFin hst).injective
  exact he.trans ((st.orderIsoOfFin hst).apply_symm_apply _).symm

/-- Parity of payoff variables whose label differs from the designated one. -/
def payoffParity {R : Type*} [Ring R] (s : Finset (α ×ₗ Bool)) (d : α) : R :=
  (-1 : R) ^ (s.filter (fun v => (ofLex v).2 = true ∧ (ofLex v).1 ≠ d)).card

/-- Exchanging complementary ports outside the designated label reverses parity. -/
theorem twin_payoffParity {R : Type*} [Ring R] (s : Finset (α ×ₗ Bool)) (k d : α)
    (ht : toLex (k, true) ∉ s) (hkd : k ≠ d) :
    payoffParity (R := R) (insert (toLex (k, true)) s) d =
      -payoffParity (R := R) (insert (toLex (k, false)) s) d := by
  have htrue : ((insert (toLex (k, true)) s).filter
      (fun v => (ofLex v).2 = true ∧ (ofLex v).1 ≠ d)).card =
      (s.filter (fun v => (ofLex v).2 = true ∧ (ofLex v).1 ≠ d)).card + 1 := by
    simp [Finset.filter_insert, hkd, ht]
  have hfalse : ((insert (toLex (k, false)) s).filter
      (fun v => (ofLex v).2 = true ∧ (ofLex v).1 ≠ d)).card =
      (s.filter (fun v => (ofLex v).2 = true ∧ (ofLex v).1 ≠ d)).card := by
    simp [Finset.filter_insert]
  simp only [payoffParity, htrue, hfalse, pow_succ, mul_neg_one]

end GameTheory.Math.ComplementaryPortOrder
