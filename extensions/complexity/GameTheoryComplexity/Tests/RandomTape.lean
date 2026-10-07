import GameTheoryComplexity.SampleTest
import GameTheoryComplexity.Backend.Complexitylib

/-! A two-step fair-coin machine exercises the probability bridge and its sampling limits. -/

noncomputable section

namespace GameTheory.Complexity.Tests

open _root_.Complexity
open GameTheory.Complexity.Backend

/-- The first step passes the immutable marker; the second writes a fair verdict and halts. -/
def coinMachine : NTM 0 where
  Q := Fin 3
  qstart := 0
  qhalt := 2
  δ bit state _ _ _ :=
    (if state = 0 then 1 else 2, fun _ => Γw.blank,
      if bit then Γw.one else Γw.zero, Dir3.right, fun _ => Dir3.right, Dir3.right)
  δ_right_of_start := by intros; exact ⟨fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem coinMachine_halts : coinMachine.AllPathsHaltIn (fun _ => 2) := by
  intro input tape
  simp [NTM.trace, coinMachine]

/-- A constant-time certificate for the same fixed machine on every input. -/
def coinClock : PolynomialClock coinMachine where
  steps := fun _ => 2
  halts := coinMachine_halts
  degree := 0
  asymptotic := BigO.const_le_pow 2 0
  constant := 2
  bound := by intro len; simp

example : coinMachine.IsPPT := coinClock.isPPT

example : booleanMachineTest coinMachine coinClock 0 ∈ GameTheory.Complexity.booleanMachineTests :=
  ⟨0, coinMachine, coinClock, 0, rfl⟩

theorem coinMachine_verdict (input : List Bool) (tape : Fin 2 → Bool) :
    machineVerdict coinMachine input 2 tape = tape 1 := by
  cases h : tape 1 <;>
    simp [machineVerdict, NTM.trace, coinMachine, Tape.write, Tape.move, h]

/-- An actual probabilistic machine consumer, with positive acceptance probability. -/
theorem coinMachine_probability (input : List Bool) :
    (machineLaw coinMachine input 2 true).toReal = 1 / 2 := by
  rw [machineLaw, randomTapeLaw_true]
  simp only [coinMachine_verdict]
  have hcount : (Finset.univ.filter fun tape : Fin 2 → Bool => tape 1 = true).card = 2 := by
    decide
  rw [hcount]
  norm_num

/-- Neither this machine nor any other bounded fair-coin verdict realizes an exact third. -/
example (steps : ℕ) (verdict : (Fin steps → Bool) → Bool) :
    (randomTapeLaw steps verdict true).toReal ≠ 1 / 3 :=
  randomTapeLaw_ne_one_third steps verdict

end GameTheory.Complexity.Tests
