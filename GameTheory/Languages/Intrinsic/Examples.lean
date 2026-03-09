import GameTheory.Languages.Intrinsic.Compile

/-!
# Examples of Games in Intrinsic Form

Concrete W-game instances demonstrating the intrinsic form framework.

## Examples

1. **Matching Pennies** — simultaneous 2-player game with no information
2. **Simple Signaling** — nature chooses a type, sender observes it,
   receiver observes the sender's action but not nature
-/

namespace Intrinsic

-- ============================================================================
-- Example 1: Matching Pennies
-- ============================================================================

/-- Binary decisions (Heads or Tails). -/
inductive Coin | heads | tails
  deriving DecidableEq, Fintype

instance : Nonempty Coin := ⟨Coin.heads⟩

/-- Matching Pennies as a W-model.
    - 2 agents (player 1 and player 2), each choosing Heads or Tails
    - Trivial nature (single state)
    - No information: each agent's info field is trivial (all configs equivalent) -/
def matchingPenniesModel : WModel where
  A := Fin 2
  Ω := Unit
  U := fun _ => Coin
  info := fun _ => ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial,
    fun _ _ => trivial⟩⟩

/-- Utility for Matching Pennies. Player 0 wins when coins match. -/
def mpUtility (p : Fin 2)
    (h : Config Unit (Fin 2) (fun _ => Coin)) : ℝ :=
  if p = 0 then (if h.decision 0 = h.decision 1 then 1 else -1)
  else (if h.decision 0 = h.decision 1 then -1 else 1)

/-- Matching Pennies as a W-game. -/
noncomputable def matchingPennies : WGame :=
  { matchingPenniesModel with
    P := Fin 2
    owner := id
    utility := mpUtility
    prior := PMF.pure () }

-- ============================================================================
-- Example 2: Simple Signaling Game
-- ============================================================================

/-- Two types for the signaling game. -/
inductive SigType | high | low
  deriving DecidableEq, Fintype

instance : Nonempty SigType := ⟨SigType.high⟩

/-- Two messages for the signaling game. -/
inductive Message | msgA | msgB
  deriving DecidableEq, Fintype

instance : Nonempty Message := ⟨Message.msgA⟩

/-- Two actions for the receiver. -/
inductive RcvAction | accept | reject
  deriving DecidableEq, Fintype

instance : Nonempty RcvAction := ⟨RcvAction.accept⟩

/-- Signaling game decision types: sender chooses a message,
    receiver chooses an action. -/
def sigDecision : Fin 2 → Type
  | 0 => Message     -- sender
  | 1 => RcvAction   -- receiver

instance sigDecisionFintype : ∀ a, Fintype (sigDecision a) :=
  fun a => match a with
  | 0 => inferInstanceAs (Fintype Message)
  | 1 => inferInstanceAs (Fintype RcvAction)

instance sigDecisionNonempty : ∀ a, Nonempty (sigDecision a) :=
  fun a => match a with
  | 0 => inferInstanceAs (Nonempty Message)
  | 1 => inferInstanceAs (Nonempty RcvAction)

/-- Simple signaling game as a W-model.
    - Nature: 2 types (high/low)
    - Agent 0 (sender): observes nature's type, chooses a message
    - Agent 1 (receiver): observes the sender's message, chooses accept/reject -/
def signalingModel : WModel where
  A := Fin 2
  Ω := SigType
  U := sigDecision
  info := fun a => match a with
    | 0 => {  -- Sender knows nature's type
        r := fun h h' => h.nature = h'.nature
        iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩ }
    | 1 => {  -- Receiver knows sender's message
        r := fun h h' => h.decision 0 = h'.decision 0
        iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩ }

/-- Extract the receiver's action from a signaling config. -/
def sigReceiverAction (h : Config SigType (Fin 2) sigDecision) : RcvAction :=
  h.decision 1

def signalingUtility (_p : Fin 2) (h : signalingModel.H) : ℝ :=
  match h.nature, sigReceiverAction h with
  | SigType.high, RcvAction.accept => 1
  | SigType.low, RcvAction.reject => 1
  | _, _ => 0

/-- Simple signaling W-game. -/
noncomputable def signalingGame : WGame :=
  { signalingModel with
    P := Fin 2
    owner := id
    utility := signalingUtility
    prior := PMF.pure SigType.high }

-- ============================================================================
-- Solvability witnesses
-- ============================================================================

/-- Matching Pennies is solvable: with trivial info, every strategy is constant
    so the fixed-point equation has a trivially unique solution. -/
theorem matchingPennies_solvable : Solvable matchingPenniesModel := by
  intro strat ω
  have hmeas : ∀ (a : Fin 2) (h h' : matchingPenniesModel.H),
      (strat a).act h = (strat a).act h' :=
    fun a h h' => (strat a).meas h h' trivial
  let u₀ : ∀ a : Fin 2, Coin :=
    fun a => (strat a).act ⟨(), fun _ => Coin.heads⟩
  refine ⟨u₀, ?_, ?_⟩
  · intro a; simp only [u₀]; exact hmeas a _ _
  · intro u hu; funext a; rw [hu a]; simp only [u₀]; exact hmeas a _ _

end Intrinsic
