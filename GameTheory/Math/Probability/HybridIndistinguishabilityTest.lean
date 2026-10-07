/-
# Consumers and limits of uniform hybrid bounds

Exponential adjacent bounds tolerate polynomially many steps. A moving jump
shows why negligible differences for each fixed hybrid index are insufficient.
-/
import GameTheory.Math.Probability.HybridIndistinguishability

noncomputable section

namespace GameTheory.Math.Probability.HybridTest

open GameTheory.Math Filter

/-- Exponentially small adjacent advantages can be composed through a
polynomial number of hybrids. -/
theorem exponential_hybrid {α : Type*} {tests : Set (SampleTest α)}
    {H : ℕ → ℕ → PMF α} (d : ℕ)
    (hgap : ∀ T ∈ tests, ∀ κ j, j < κ ^ d →
      |T.acceptProb (fun κ => H κ j) κ -
        T.acceptProb (fun κ => H κ (j + 1)) κ| ≤ 1 / (2 : ℝ) ^ κ) :
    IndistinguishableBy tests (fun κ => H κ 0) (fun κ => H κ (κ ^ d)) := by
  apply indistinguishableBy_of_uniform_hybrid
    ⟨d, Eventually.of_forall fun _ => le_rfl⟩
  constructor
  intro T hT
  refine ⟨fun κ => 1 / (2 : ℝ) ^ κ, negligible_inv_two_pow,
    Eventually.of_forall fun κ j hj => ?_⟩
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (2 : ℝ) ^ κ)]
  exact hgap T hT κ j hj

/-- Read one Boolean draw without extra randomness. -/
def readBit : SampleTest Bool where
  samples _ := 1
  accept _ z := PMF.pure (z 0)

theorem readBit_accept_pure (b : ℕ → Bool) (κ : ℕ) :
    readBit.acceptProb (fun κ => PMF.pure (b κ)) κ = if b κ then 1 else 0 := by
  change (((independentProduct fun _ : Fin 1 => PMF.pure (b κ)).bind
    fun z => PMF.pure (z 0)) true).toReal = _
  rw [show (independentProduct fun _ : Fin 1 => PMF.pure (b κ)) =
    PMF.pure (fun _ : Fin 1 => b κ) from independentProduct_pure _, PMF.pure_bind]
  cases b κ <;> simp

/-- A distinguishing jump located at the current security parameter. -/
def movingJump (κ j : ℕ) : PMF Bool := PMF.pure (decide (κ < j))

/-- Every fixed adjacent pair is eventually identical, hence is
indistinguishable even by unrestricted tests. -/
theorem movingJump_fixed_adjacent (j : ℕ) :
    IndistinguishableBy Set.univ (fun κ => movingJump κ j)
      (fun κ => movingJump κ (j + 1)) := by
  intro T _
  apply negligible_zero.congr'
  filter_upwards [eventually_ge_atTop (j + 1)] with κ hκ
  have hsame : movingJump κ j = movingJump κ (j + 1) := by
    simp only [movingJump]
    have hj : ¬κ < j := by omega
    have hj' : ¬κ < j + 1 := by omega
    simp [hj, hj']
  simp only [SampleTest.acceptProb, hsame, sub_self]

/-- The number of steps has a polynomial eventual bound. -/
theorem movingJump_steps_polynomial :
    ∃ d : ℕ, ∀ᶠ κ : ℕ in atTop, κ + 1 ≤ κ ^ d := by
  refine ⟨2, ?_⟩
  filter_upwards [eventually_ge_atTop 2] with κ hκ
  nlinarith

/-- Despite fixed-index indistinguishability, the endpoint jump is perfectly
visible to one draw. -/
theorem movingJump_endpoints_distinguishable :
    ¬IndistinguishableBy {readBit} (fun κ => movingJump κ 0)
      (fun κ => movingJump κ (κ + 1)) := by
  intro h
  have hneg := h readBit (Set.mem_singleton _)
  have hleft : (fun κ => movingJump κ 0) = fun _ => PMF.pure false := by
    funext κ
    simp [movingJump]
  have hright : (fun κ => movingJump κ (κ + 1)) = fun _ => PMF.pure true := by
    funext κ
    simp [movingJump]
  rw [hleft, hright] at hneg
  have hsmall := hneg.eventually_abs_lt 0
  obtain ⟨κ, hκ⟩ := hsmall.exists
  simp only [readBit_accept_pure, Bool.false_eq_true, ↓reduceIte,
    zero_sub, abs_neg, abs_one, pow_zero, inv_one] at hκ
  exact (lt_irrefl (1 : ℝ)) hκ

/-- No uniform negligible certificate can cover the moving jump. -/
theorem movingJump_not_uniform :
    ¬UniformHybridBound {readBit} movingJump (fun κ => κ + 1) := by
  intro h
  exact movingJump_endpoints_distinguishable
    (indistinguishableBy_of_uniform_hybrid movingJump_steps_polynomial h)

end GameTheory.Math.Probability.HybridTest
