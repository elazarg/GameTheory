/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Languages.Intrinsic.Examples
import GameTheory.Languages.Intrinsic.PerfectRecall

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

-- ============================================================================
-- Solvability and order tests
-- ============================================================================

/-- The expected-utility wrapper still exposes the original W-model. -/
example : Solvable matchingPennies.toWModel :=
  matchingPennies_solvable

/-- Expected-utility W-games still compile to `KernelGame`. -/
noncomputable example : GameTheory.KernelGame matchingPennies.P :=
  matchingPennies.toKernelGame matchingPennies_solvable

/-- A fixed ordering for the two matching-pennies agents. -/
def matchingPenniesOrdering : ConfigOrdering matchingPenniesModel :=
  fun _ => ⟨([(0 : Fin 2), (1 : Fin 2)] : List matchingPenniesModel.A), by decide⟩

/-- With trivial information, matching pennies is causal for the fixed order. -/
example : CausalWith matchingPenniesModel matchingPenniesOrdering := by
  intro κ hne
  dsimp [CausalWith]
  intro h h' hh hh' hagree
  trivial

example : OrderInfoCompatibleWith matchingPenniesModel matchingPenniesOrdering := by
  intro a h h' hinfo
  rfl

-- ============================================================================
-- Perfect recall smoke tests
-- ============================================================================

/-- A one-agent model with singleton nature and action. -/
def oneAgentModel : WModel where
  A := Unit
  Ω := Unit
  U := fun _ => Unit
  info := fun _ => ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial,
    fun _ _ => trivial⟩⟩

/-- A one-player W-game over the one-agent model. -/
def oneAgentGame : WGame :=
  { oneAgentModel with
    P := Unit
    owner := fun _ => ()
    owner_nonempty := fun _ => ⟨(), rfl⟩
    pref := fun _ _ _ => True }

/-- The only ordering of the one-agent model. -/
def oneAgentOrdering : ConfigOrdering oneAgentModel :=
  fun _ => ⟨([()] : List oneAgentModel.A), by decide⟩

example : CausalWith oneAgentModel oneAgentOrdering := by
  intro κ hne
  dsimp [CausalWith]
  intro h h' hh hh' hagree
  trivial

example : OrderInfoCompatibleWith oneAgentModel oneAgentOrdering := by
  intro a h h' hinfo
  rfl

/-- Perfect recall is trivial when every decision coordinate is a singleton. -/
example : PerfectRecall oneAgentGame oneAgentOrdering () := by
  intro κ hne
  dsimp [PerfectRecall]
  intro howner h h' hh hinfo
  constructor
  · simpa [configSet, oneAgentOrdering] using hh
  · intro a ha hp
    constructor
    · trivial
    · cases h.decision a
      cases h'.decision a
      rfl

-- ============================================================================
-- Guard against the old causality direction
-- ============================================================================

/-- Agent 0 observes agent 1's decision, which is future-looking for order
    `[0, 1]`. -/
def futureLookingModel : WModel where
  A := Fin 2
  Ω := Unit
  U := fun _ => Coin
  info := fun a => match a with
    | 0 => {
        r := fun h h' => h.decision (1 : Fin 2) = h'.decision (1 : Fin 2)
        iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩ }
    | 1 => ⟨fun _ _ => True, ⟨fun _ => trivial, fun _ => trivial,
        fun _ _ => trivial⟩⟩

def futureLookingOrdering : ConfigOrdering futureLookingModel :=
  fun _ => ⟨([(0 : Fin 2), (1 : Fin 2)] : List futureLookingModel.A), by decide⟩

/-- Correct causality rejects an agent whose information depends on a future
    decision. -/
example : ¬ CausalWith futureLookingModel futureLookingOrdering := by
  intro hc
  let κ : OrderingPrefix futureLookingModel :=
    ⟨([(0 : Fin 2)] : List futureLookingModel.A), by decide⟩
  let h : futureLookingModel.H := ⟨(), fun _ => Coin.heads⟩
  let h' : futureLookingModel.H :=
    ⟨(), fun a => if a = (1 : Fin 2) then Coin.tails else Coin.heads⟩
  have hinfo := hc κ (by decide) h h' (by rfl) (by rfl) (by
    constructor
    · rfl
    · intro a ha
      simp [OrderingPrefix.predecessors, κ] at ha)
  have hlast : κ.last (by decide) = ((0 : Fin 2) : futureLookingModel.A) := by
    rfl
  rw [hlast] at hinfo
  change h.decision (1 : Fin 2) = h'.decision (1 : Fin 2) at hinfo
  simp [h, h'] at hinfo

-- ============================================================================
-- Kuhn statement shape
-- ============================================================================

/-- Outcome point masses expand into player consistency-event masses. -/
example (G : WGame) (hsolv : Solvable G.toWModel)
    (μ : MixedProfile G) (ω : G.Ω) (u : ∀ a : G.A, G.U a) :
    mixedOutcomeAt G hsolv μ ω u =
      ∏ p : G.P, Math.ProbabilityMassFunction.pmfMass
        (μ := μ p) (playerSolutionEvent G p ω u) :=
  mixedOutcomeAt_apply_eq_prod G hsolv μ ω u

/-- Product-mixed player event masses factor over the player's agents. -/
example (G : WGame) (p : G.P) (πp : ProductMixedStrategy G p)
    (ω : G.Ω) (u : ∀ a : G.A, G.U a) :
    Math.ProbabilityMassFunction.pmfMass
        (μ := productMixedAsMixed G p πp) (playerSolutionEvent G p ω u) =
      ∏ a : G.agents p,
        Math.ProbabilityMassFunction.pmfMass
          (μ := πp a) (fun s => u a = s.act ⟨ω, u⟩) :=
  productMixed_playerSolutionEvent_mass_eq_prod G p πp ω u

/-- `kuhn_equivalence` returns the full outcome-distribution statement from
    solvability and perfect recall, without causality or a separate
    event-realizability assumption. -/
example (G : WGame) (hsolv : Solvable G.toWModel)
    (ϕ : ConfigOrdering G.toWModel) (p : G.P)
    (hpr : PerfectRecall G ϕ p) (μp : MixedStrategy G p) :
      ∃ πp : ProductMixedStrategy G p,
        ∀ (μminus : OpponentMixedProfile G p) (ω : G.Ω),
          mixedOutcomeAt G hsolv (assembleMixedProfile G p μp μminus) ω =
            mixedOutcomeAt G hsolv
              (assembleMixedProfile G p (productMixedAsMixed G p πp) μminus) ω := by
  exact kuhn_equivalence G hsolv ϕ p hpr μp

end Intrinsic
