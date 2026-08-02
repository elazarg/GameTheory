/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingStationarySnellCap

/-!
# Stationary quitting gains and complementarity

This file isolates the scalar algebra behind stationary quitting profiles
before specializing it to the game-facing quantities.  The exceptional
zero- and singleton-support boundaries are kept separate from the later
contracting equivalences.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

/-! ## Scalar balance algebra -/

/-- The two exact stationary gap factorizations.  Here `x` is the player's
quit probability, `c` is the opponents' continue mass, `Q` is the pure-Quit
value, `A` is the unconditional absorbing contribution under pure Continue,
`h` is total absorption mass, `W` is the prescribed stationary payoff, and
`G = (1-c)Q-A` is the stationary gain.

No division, positivity, or contraction hypothesis is needed for these
identities. -/
theorem stationaryQuittingGain_balance_identities
    (c x Q A h W G : ℝ)
    (habsorption : h = 1 - (1 - x) * c)
    (hpayoff : h * W = x * Q + (1 - x) * A)
    (hgain : G = (1 - c) * Q - A) :
    h * (Q - W) = (1 - x) * G ∧
      h * (A - (1 - c) * W) = -x * G := by
  rw [habsorption] at hpayoff ⊢
  constructor
  · rw [hgain]
    linear_combination -hpayoff
  · rw [hgain]
    linear_combination -(1 - c) * hpayoff

/-- With positive total absorption, the factored gain signs are exactly the
two pure endpoint inequalities against the stationary payoff. -/
theorem stationaryQuittingGain_complementarity_iff_endpoints
    (c x Q A h W G : ℝ)
    (habsorption : h = 1 - (1 - x) * c)
    (hpayoff : h * W = x * Q + (1 - x) * A)
    (hgain : G = (1 - c) * Q - A)
    (hpos : 0 < h) :
    ((1 - x) * G ≤ 0 ∧ 0 ≤ x * G) ↔
      (Q ≤ W ∧ A + c * W ≤ W) := by
  obtain ⟨hquit, hcontinue⟩ :=
    stationaryQuittingGain_balance_identities
      c x Q A h W G habsorption hpayoff hgain
  constructor
  · rintro ⟨hquitSign, hcontinueSign⟩
    constructor
    · nlinarith
    · nlinarith
  · rintro ⟨hquitEndpoint, hcontinueEndpoint⟩
    constructor
    · nlinarith
    · nlinarith

end GameTheory
