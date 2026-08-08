/-
Hostile finite consumer for the fictitious-play trajectory interface.

The alternating history gives non-point-mass empirical beliefs, while the
constant coordination history proves the best-response recurrence through the
canonical pure-to-mixed Nash bridge.
-/

import GameTheory.Core.FictitiousPlay

noncomputable section

namespace GameTheory.Tests.FictitiousPlay

open Probability

@[reducible]
def signature : GameSignature (Fin 2) where
  Strategy _ := Bool
  Outcome := Bool × Bool

@[reducible]
def form : GameForm (Fin 2) where
  sig := signature
  play profile := FinDist.pure (profile 0, profile 1)

def utility (outcome : Bool × Bool) (_who : Fin 2) : ℝ :=
  if outcome.1 = outcome.2 then 1 else 0

@[reducible]
def game : UtilityGame (Fin 2) where
  form := form
  utility := utility

def coordinated : Profile signature := fun _ => false

def constantHistory (_round : ℕ) : Profile signature := coordinated

def alternatingHistory (round : ℕ) : Profile signature :=
  fun _ => round % 2 = 1

def trueValue (action : Bool) : ℝ := if action then 1 else 0

/-- Two alternating observations produce a genuinely mixed empirical law. -/
theorem alternating_prob_true :
    (game.empiricalMarginal alternatingHistory 0 2).prob true = 1 / 2 := by
  rw [game.empiricalMarginal_prob]
  have hcard :
      ((Finset.univ.filter fun round : Fin 2 => round.val % 2 = 1).card) = 1 := by
    decide
  simp [alternatingHistory, hcard]

/-- The running-average recurrence sees the new false observation: after
`false, true, false`, the expected Boolean value is `1/3`. -/
theorem alternating_expect_three :
    (game.empiricalMarginal alternatingHistory 0 3).expect trueValue = 1 / 3 := by
  rw [game.empiricalMarginal_expect]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num [alternatingHistory, trueValue]

/-- The successor theorem specializes to the nonconstant alternating trace. -/
theorem alternating_successor_identity :
    (game.empiricalMarginal alternatingHistory 0 3).expect trueValue =
      ((1 + 1 : ℝ) / (1 + 2 : ℝ)) *
          (game.empiricalMarginal alternatingHistory 0 2).expect trueValue +
        (1 / (1 + 2 : ℝ)) * trueValue (alternatingHistory 2 0) :=
  by
    convert game.empiricalMarginal_succ_expect alternatingHistory 0 1 trueValue using 1
    all_goals norm_num

/-- Coordinating on `false` is a pure Nash profile. -/
theorem coordinated_isNash :
    IsNash game.form (euPreference game.utility) coordinated := by
  rw [isNash_iff]
  intro who replacement
  rw [euPreference_apply]
  simp only [game, form, expectedUtility_pure, coordinated]
  unfold utility
  split <;> norm_num

/-- Every positive-horizon empirical belief of the constant history is the
canonical pure embedding of the coordinated profile. -/
theorem constant_empiricalBelief (t : ℕ) :
    game.empiricalBelief constantHistory (t + 1) = game.form.purify coordinated := by
  funext who
  change (FinDist.uniformFin (t + 1)).map (fun _ => false) = FinDist.pure false
  rw [FinDist.map_const]

/-- The constant coordination path is genuine fictitious play.  The proof does
not unfold a second payoff comparison: it consumes the canonical mixed Nash
best-response theorem. -/
theorem constant_isFictitiousPlay : game.IsFictitiousPlay constantHistory := by
  intro t who
  have hmixed := coordinated_isNash.purify
  rw [isNash_iff_isBestResponse] at hmixed
  rw [constant_empiricalBelief]
  change IsBestResponse game.form.mixed (euPreference game.utility) who
    (game.form.purify coordinated) (FinDist.pure false)
  convert hmixed who using 1
  change FinDist.pure false = FinDist.pure false
  rfl

end GameTheory.Tests.FictitiousPlay
