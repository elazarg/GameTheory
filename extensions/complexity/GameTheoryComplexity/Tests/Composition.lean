import GameTheoryComplexity.Backend.CompiledSampleTest
import GameTheoryComplexity.Tests.RandomTape

/-! End-to-end fair-coin consumers cover nonmonotone clocks and immediate rejection. -/

namespace GameTheory.Complexity.Tests

open _root_.Complexity _root_.Complexity.Cobham
open GameTheory.Complexity.Backend

/-- A valid all-path clock may decrease as input length increases. -/
def descendingClock : PolynomialClock coinMachine where
  steps len := if len = 0 then 3 else 2
  halts := NTM.AllPathsHaltIn.mono (by intro len; split_ifs <;> omega) coinMachine_halts
  degree := 0
  asymptotic := (BigO.of_le (g := fun _ => 3) (by intro len; split_ifs <;> omega)).trans
    (BigO.const_le_pow 3 0)
  constant := 3
  bound := by intro len; simp only [pow_zero, mul_one]; split_ifs <;> omega

example : ¬ Monotone descendingClock.steps := by
  intro h
  have hbad := h (show 0 ≤ 1 from by omega)
  norm_num [descendingClock] at hbad

/-- Serialization followed by a fair-coin test remains exactly fair, even when
its source clock is nonmonotone. One machine and one clock work for every draw. -/
theorem composed_coin_probability :
    ∃ (n : ℕ) (composite : NTM n), composite.IsPPT ∧ ∃ bound : Polynomial ℕ,
      ∀ (κ : ℕ) (draws : Fin ((κ + 1) ^ 2) → Bool),
        (∀ choices : Fin (bound.eval κ) → Bool,
          composite.halted (composite.trace (bound.eval κ) choices
            (composite.initCfg (encodeVec (booleanTuple 2 κ draws))))) ∧
        composite.acceptProb (encodeVec (booleanTuple 2 κ draws)) (bound.eval κ) = 1 / 2 := by
  obtain ⟨n, composite, hppt, hdegrees⟩ := exists_composed_booleanMachine coinMachine descendingClock
  obtain ⟨bound, hcert⟩ := hdegrees 2
  refine ⟨n, composite, hppt, bound, fun κ draws => ?_⟩
  obtain ⟨hhalt, hlaw⟩ := hcert κ draws
  refine ⟨hhalt, ?_⟩
  have hcoin : machineLaw coinMachine (booleanInput 2 κ draws)
      (descendingClock.steps (booleanInput 2 κ draws).length) =
      machineLaw coinMachine (booleanInput 2 κ draws) 2 := by
    apply machineLaw_of_le_of_halts
    · change 2 ≤ if (booleanInput 2 κ draws).length = 0 then 3 else 2
      split_ifs <;> omega
    · exact coinMachine_halts _
  have hprob : (composite.acceptProb (encodeVec (booleanTuple 2 κ draws))
      (bound.eval κ) : ℝ) = 1 / 2 := by
    rw [← machineLaw_acceptProb, hlaw]
    change (machineLaw coinMachine (booleanInput 2 κ draws)
      (descendingClock.steps (booleanInput 2 κ draws).length) true).toReal = 1 / 2
    rw [hcoin]
    exact coinMachine_probability _
  apply Rat.cast_injective (α := ℝ)
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hprob

/-- This source test begins halted, so it consumes zero random bits and rejects. -/
def stoppedMachine : NTM 0 where
  Q := Fin 1
  qstart := 0
  qhalt := 0
  δ _ _ _ _ _ := (0, fun _ => Γw.blank, Γw.blank, Dir3.right,
    fun _ => Dir3.right, Dir3.right)
  δ_right_of_start := by intros; exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

def stoppedClock : PolynomialClock stoppedMachine where
  steps _ := 0
  halts := by intro input choices; rfl
  degree := 0
  asymptotic := BigO.const_le_pow 0 0
  constant := 0
  bound := by intro len; simp

/-- The end-to-end certificate includes tests whose start state is already halted. -/
theorem composed_immediate_rejection :
    ∃ (n : ℕ) (composite : NTM n), composite.IsPPT ∧ ∃ bound : Polynomial ℕ,
      ∀ (κ : ℕ) (draws : Fin ((κ + 1) ^ 0) → Bool),
        (∀ choices : Fin (bound.eval κ) → Bool,
          composite.halted (composite.trace (bound.eval κ) choices
            (composite.initCfg (encodeVec (booleanTuple 0 κ draws))))) ∧
        machineLaw composite (encodeVec (booleanTuple 0 κ draws)) (bound.eval κ) = PMF.pure false := by
  obtain ⟨n, composite, hppt, hdegrees⟩ := exists_composed_booleanMachine stoppedMachine stoppedClock
  obtain ⟨bound, hcert⟩ := hdegrees 0
  refine ⟨n, composite, hppt, bound, fun κ draws => ?_⟩
  obtain ⟨hhalt, hlaw⟩ := hcert κ draws
  refine ⟨hhalt, ?_⟩
  rw [hlaw]
  exact machineLaw_start_halted stoppedMachine rfl _ _

end GameTheory.Complexity.Tests
