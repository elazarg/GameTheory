import Mathlib

set_option autoImplicit false

namespace Fixpoint

/-- Integer grid points on a simplex with denominator `m`. -/
abbrev GridPoint (ι : Type*) [Fintype ι] (m : ℕ) : Type _ :=
  {w : ι → ℕ // ∑ i, w i = m}

namespace GridPoint

variable {ι : Type*} [Fintype ι]

/-- Normalize a grid point to a point in the real standard simplex. -/
noncomputable def toStdSimplex {m : ℕ} (hm : 0 < m) :
    GridPoint ι m → stdSimplex Real ι := by
  intro p
  refine ⟨fun i => (p.1 i : Real) / m, ?_⟩
  refine ⟨?_, ?_⟩
  · intro i
    refine div_nonneg (Nat.cast_nonneg (p.1 i)) ?_
    exact le_of_lt (Nat.cast_pos.mpr hm)
  · have hsumNat : (∑ i, (p.1 i : Real)) = m := by
      exact_mod_cast p.2
    calc
      (∑ i : ι, ((p.1 i : Real) / m))
          = (∑ i : ι, (p.1 i : Real)) / m := by
              rw [Finset.sum_div]
      _ = (m : Real) / m := by rw [hsumNat]
      _ = 1 := by
            exact div_self (Nat.cast_ne_zero.mpr hm.ne')

@[simp] theorem toStdSimplex_apply {m : ℕ} (hm : 0 < m)
    (p : GridPoint ι m) (i : ι) :
    (toStdSimplex hm p : ι → Real) i = (p.1 i : Real) / m := rfl

end GridPoint

end Fixpoint
