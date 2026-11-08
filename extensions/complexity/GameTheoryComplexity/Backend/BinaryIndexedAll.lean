module

public import GameTheoryComplexity.Backend.BinaryIndexedLexicographic

@[expose] public section

/-! A certified universal scan of indexed Boolean predicates. -/

namespace GameTheory.Complexity.Backend
open Cslib.BitString Turing.MultiTapeTM

/-- Check every index below the clock length; clock contents are immaterial. -/
def binaryIndexedAll {p : ℕ} (term : (Fin (p + 1) → List Bool) → List Bool)
    (clock : List Bool) (params : Fin p → List Bool) : List Bool :=
  [(binaryIndexedLexState (fun _ => [false]) term clock params).headD false]

/-- The universal scan is the non-strict specialization of the lexicographic scan. -/
@[fun_prop] theorem binaryIndexedAll_polyTime {p : ℕ}
    {term : (Fin (p + 1) → List Bool) → List Bool}
    (hterm : ComputableInPolyTime term (encPi encBits) encBits) :
    ComputableInPolyTime
      (fun v : Fin (p + 1) → List Bool => binaryIndexedAll term (v 0) (Fin.tail v))
      (encPi encBits) encBits := by
  have hclock : ComputableInPolyTime
      (fun v : Fin (p + 1) → List Bool => v 0) (encPi encBits) encBits :=
    ComputableInPolyTime.pi_apply encBits 0
  have hparams : ComputableInPolyTime
      (fun v : Fin (p + 1) → List Bool => Fin.tail v)
      (encPi encBits) (encPi encBits) := by
    apply ComputableInPolyTime.pi
    intro i
    exact ComputableInPolyTime.pi_apply encBits (Fin.succ i)
  have hlt : ComputableInPolyTime
      (fun _ : Fin (p + 1) → List Bool => [false])
      (encPi encBits) encBits := .const [false]
  have hstate := binaryIndexedLexState_polyTime hlt hterm hclock hparams
  exact ComputableInPolyTime.bitsCons
    ((ComputableInPolyTime.headD false).comp hstate) (.const [])

/-- The result bit is true exactly when every indexed predicate holds. -/
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
