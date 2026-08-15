/-
# Rotations of finite indices

Equivalences between residues and finite indices, and invariance of finite sums
under cyclic rotation.
-/

import Mathlib.Analysis.SumOverResidueClass

noncomputable section

namespace GameTheory.Math

/-- Equivalence between residues modulo a positive natural and `Fin n`. -/
def zmodFinEquiv (n : ℕ) [NeZero n] : ZMod n ≃ Fin n where
  toFun j := ⟨j.val, j.val_lt⟩
  invFun k := (k.val : ZMod n)
  left_inv j := by
    apply ZMod.val_injective n
    simp
  right_inv k := by
    ext
    simp [Nat.mod_eq_of_lt k.isLt]

theorem finRotate_injective (n : ℕ) [NeZero n] (start : ℕ) :
    Function.Injective (fun j : Fin n => Fin.ofNat n (start + j)) := by
  intro j k h
  apply Fin.ext
  have hval : (start + (j : ℕ)) % n = (start + (k : ℕ)) % n := by
    simpa [Fin.ofNat] using congrArg Fin.val h
  have hz : ((j : ℕ) : ZMod n) = ((k : ℕ) : ZMod n) := by
    have hsum : ((start + (j : ℕ) : ℕ) : ZMod n) =
        ((start + (k : ℕ) : ℕ) : ZMod n) := by
      rw [ZMod.natCast_eq_natCast_iff']
      exact hval
    have hsum' :
        ((start : ZMod n) + ((j : ℕ) : ZMod n)) =
          ((start : ZMod n) + ((k : ℕ) : ZMod n)) := by
      simpa using hsum
    exact add_left_cancel hsum'
  have hmod : (j : ℕ) % n = (k : ℕ) % n := by
    rw [← ZMod.natCast_eq_natCast_iff']
    exact hz
  simpa [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt k.isLt] using hmod

/-- Rotation by `start` permutes the phases of a nonempty cycle. -/
def finRotateEquiv (n : ℕ) [NeZero n] (start : ℕ) : Fin n ≃ Fin n :=
  Equiv.ofBijective (fun j : Fin n => Fin.ofNat n (start + j))
    ⟨finRotate_injective n start,
      Finite.injective_iff_surjective.mp (finRotate_injective n start)⟩

@[simp]
theorem finRotateEquiv_apply (n : ℕ) [NeZero n] (start : ℕ) (j : Fin n) :
    finRotateEquiv n start j = Fin.ofNat n (start + j) :=
  rfl

/-- Rotation does not change a finite sum. -/
theorem sum_finRotate {n : ℕ} [NeZero n] (start : ℕ) (f : Fin n → ℝ) :
    (∑ j : Fin n, f (Fin.ofNat n (start + j))) = ∑ j : Fin n, f j := by
  exact Fintype.sum_equiv (finRotateEquiv n start)
    (fun j : Fin n => f (Fin.ofNat n (start + j))) f
    (fun j => by simp)

end GameTheory.Math
