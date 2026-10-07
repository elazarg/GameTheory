import GameTheory.Math.Probability.Uniform

/-! Uniform bounded random tapes connect fair-coin execution to probability laws.
Every verdict has a dyadic probability, with denominator bounded by the tape length.
-/

noncomputable section

namespace GameTheory.Complexity

/-- The law of the verdict obtained from a fixed number of independent fair bits. -/
def randomTapeLaw (steps : ℕ) (verdict : (Fin steps → Bool) → Bool) : PMF Bool :=
  (PMF.uniformOfFintype (Fin steps → Bool)).map verdict

/-- Acceptance is the fraction of random tapes giving a positive verdict. -/
theorem randomTapeLaw_true (steps : ℕ) (verdict : (Fin steps → Bool) → Bool) :
    (randomTapeLaw steps verdict true).toReal =
      ((Finset.univ.filter fun tape => verdict tape = true).card : ℝ) / 2 ^ steps := by
  rw [randomTapeLaw, Math.Probability.uniformOfFintype_map_apply,
    ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  simp

/-- A bounded fair-coin test cannot accept with exact probability one third. -/
theorem randomTapeLaw_ne_one_third (steps : ℕ) (verdict : (Fin steps → Bool) → Bool) :
    (randomTapeLaw steps verdict true).toReal ≠ 1 / 3 := by
  rw [randomTapeLaw_true]
  intro h
  have hpow : (2 : ℝ) ^ steps ≠ 0 := pow_ne_zero _ (by norm_num)
  have heq :
      (3 : ℝ) * (Finset.univ.filter fun tape => verdict tape = true).card = 2 ^ steps := by
    field_simp at h
    nlinarith
  have hnat : 3 * (Finset.univ.filter fun tape => verdict tape = true).card = 2 ^ steps := by
    exact_mod_cast heq
  have hdiv : 3 ∣ 2 ^ steps := ⟨_, hnat.symm⟩
  have hdivTwo : 3 ∣ 2 := (by decide : Nat.Prime 3).dvd_of_dvd_pow hdiv
  norm_num at hdivTwo

end GameTheory.Complexity
