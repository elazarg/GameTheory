import GameTheory.Languages.Intrinsic.Examples

/-!
# Tests for Games in Intrinsic Form

Verified properties of the concrete W-game examples.
-/

namespace Intrinsic

-- ============================================================================
-- Matching Pennies tests
-- ============================================================================

/-- Matching Pennies has 2 agents. -/
example : Fintype.card matchingPenniesModel.A = 2 := by decide

/-- Each agent in Matching Pennies has 2 decisions. -/
example : ∀ a : matchingPenniesModel.A, Fintype.card (matchingPenniesModel.U a) = 2 := by
  intro a; fin_cases a <;> decide

/-- A constant-heads strategy is a valid pure strategy in Matching Pennies
    (trivial info means any constant function is measurable). -/
def alwaysHeads : PureStrategy matchingPenniesModel a where
  act := fun _ => Coin.heads
  meas := fun _ _ _ => rfl

/-- Matching Pennies: when both play heads, player 0 gets +1. -/
example : mpUtility 0 ⟨(), fun _ => Coin.heads⟩ = 1 := by
  simp [mpUtility]

/-- Matching Pennies: when players differ, player 0 gets -1. -/
example : mpUtility 0 ⟨(), fun a => if a = 0 then Coin.heads else Coin.tails⟩ = -1 := by
  simp [mpUtility]

-- ============================================================================
-- Signaling game tests
-- ============================================================================

/-- The signaling game has 2 agents. -/
example : Fintype.card signalingModel.A = 2 := by decide

/-- Helper: construct a signaling config from nature, message, and action. -/
def mkSigConfig (ω : SigType) (m : Message) (r : RcvAction) :
    Config SigType (Fin 2) sigDecision :=
  ⟨ω, fun a => match a with | 0 => m | 1 => r⟩

/-- Signaling utility: high type + accept = 1. -/
example : signalingUtility 0 (mkSigConfig SigType.high Message.msgA RcvAction.accept) = 1 := by
  unfold signalingUtility sigReceiverAction mkSigConfig; rfl

/-- Signaling utility: low type + accept = 0. -/
example : signalingUtility 0 (mkSigConfig SigType.low Message.msgA RcvAction.accept) = 0 := by
  unfold signalingUtility sigReceiverAction mkSigConfig; rfl

/-- Signaling utility: low type + reject = 1. -/
example : signalingUtility 0 (mkSigConfig SigType.low Message.msgA RcvAction.reject) = 1 := by
  unfold signalingUtility sigReceiverAction mkSigConfig; rfl

end Intrinsic
