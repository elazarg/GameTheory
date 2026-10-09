import GameTheoryComplexity.Backend.BinaryIndexedLexicographic

/-! A certified universal scan of indexed Boolean predicates. -/

namespace GameTheory.Complexity.Backend
open _root_.Complexity _root_.Complexity.Cobham

/-- Check every index below the clock length; clock contents are immaterial. -/
def binaryIndexedAll {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) : List Bool :=
  bitAt [] (binaryIndexedLexState (fun _ => [false]) term clock params)

theorem binaryIndexedAll_cobham {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool} (ht : Cobham term) :
    Cobham fun v : Fin (p + 1) → List Bool =>
      binaryIndexedAll term (v 0) (Fin.tail v) :=
  Cobham.comp₂ Cobham.bitAtFn (Cobham.const [])
    (binaryIndexedLexState_cobham (Cobham.const [false]) ht)

theorem binaryIndexedAll_mem_FPn {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool} (ht : Cobham term) :
    FPn (fun v : Fin (p + 1) → List Bool => binaryIndexedAll term (v 0) (Fin.tail v)) :=
  cobham_iff_FPn.mp (binaryIndexedAll_cobham ht)

theorem binaryIndexedAll_value {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (params : Fin p → List Bool) (E : ℕ → Prop) [DecidablePred E]
    (ht : ∀ r, term (Fin.cons r params) = [decide (E r.length)]) (clock : List Bool) :
    binaryIndexedAll term clock params = [decide (∀ i < clock.length, E i)] := by
  rw [binaryIndexedAll, binaryIndexedLexState_value _ _ params (fun i => decide (E i))
    (fun _ => false) ht (fun _ => rfl)]
  simp only [decide_eq_true_eq]
  generalize decide (∀ i < clock.length, E i) = b
  cases b <;> rfl

end GameTheory.Complexity.Backend
