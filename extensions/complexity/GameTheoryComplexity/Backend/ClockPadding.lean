import GameTheoryComplexity.Backend.Complexitylib
import GameTheoryComplexity.RandomTapeComposition

/-! Extra independent random bits do not change the law after every path has halted. -/

namespace GameTheory.Complexity.Backend

open _root_.Complexity

/-- Enlarging a clock preserves all-path halting on a fixed input. -/
theorem machine_halts_of_le {n : ℕ} (machine : NTM n) (input : List Bool)
    {s t : ℕ} (hle : s ≤ t)
    (halts : ∀ choices : Fin s → Bool,
      machine.halted (machine.trace s choices (machine.initCfg input))) :
    ∀ choices : Fin t → Bool,
      machine.halted (machine.trace t choices (machine.initCfg input)) := by
  intro choices
  have htrace := machine.trace_mono hle
    (choices := fun i => choices ⟨i.val, lt_of_lt_of_le i.isLt hle⟩) (choices' := choices)
    (fun _ => rfl) (halts _)
  rw [htrace]
  exact halts _

/-- Enlarging a clock preserves the complete verdict law once every path halts. -/
theorem machineLaw_of_le_of_halts {n : ℕ} (machine : NTM n) (input : List Bool)
    {s t : ℕ} (hle : s ≤ t)
    (halts : ∀ choices : Fin s → Bool,
      machine.halted (machine.trace s choices (machine.initCfg input))) :
    machineLaw machine input t = machineLaw machine input s := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
  have hverdict : machineVerdict machine input (s + extra) =
      fun choices => machineVerdict machine input s
        (fun i => choices ⟨i.val, by omega⟩) := by
    funext choices
    have htrace := machine.trace_mono (by omega : s ≤ s + extra)
      (choices := fun i => choices ⟨i.val, by omega⟩) (choices' := choices)
      (fun _ => rfl) (halts _)
    simp only [machineVerdict, htrace]
  change randomTapeLaw (s + extra) _ = randomTapeLaw s _
  rw [hverdict]
  exact randomTapeLaw_prefix s extra _

end GameTheory.Complexity.Backend
