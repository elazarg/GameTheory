/-
Hostile finite consumer for the fictitious-play trajectory interface.

The alternating history gives non-point-mass empirical beliefs, while the
constant coordination history proves the best-response recurrence through the
canonical pure-to-mixed Nash bridge.
-/

import GameTheory.Core.FictitiousPlay

noncomputable section

namespace GameTheory.Tests.FictitiousPlay

open GameTheory.Math.Probability

@[reducible]
def signature : GameSignature (Fin 2) where
  Strategy _ := Bool
  Outcome := Bool × Bool

@[reducible]
def form : GameForm (Fin 2) :=
  GameForm.deterministic signature fun profile => (profile 0, profile 1)

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
    game.form.empiricalMarginal alternatingHistory 0 2 true = 1 / 2 := by
  rw [game.form.empiricalMarginal_prob]
  have hcard :
      ((Finset.univ.filter fun round : Fin 2 => round.val % 2 = 1).card) = 1 := by
    decide
  simp [alternatingHistory, hcard]

/-- The running-average recurrence sees the new false observation: after
`false, true, false`, the expected Boolean value is `1/3`. -/
theorem alternating_expect_three :
    expect (game.form.empiricalMarginal alternatingHistory 0 3) trueValue
      (payoffIntegrable_of_finite _ _) = 1 / 3 := by
  rw [game.form.empiricalMarginal_expect]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one]
  norm_num [alternatingHistory, trueValue]

/-- The successor theorem specializes to the nonconstant alternating trace. -/
theorem alternating_successor_identity :
    expect (game.form.empiricalMarginal alternatingHistory 0 3) trueValue
        (payoffIntegrable_of_finite _ _) =
      ((1 + 1 : ℝ) / (1 + 2 : ℝ)) *
          expect (game.form.empiricalMarginal alternatingHistory 0 2) trueValue
            (payoffIntegrable_of_finite _ _) +
        (1 / (1 + 2 : ℝ)) * trueValue (alternatingHistory 2 0) :=
  by
    convert game.form.empiricalMarginal_succ_expect alternatingHistory 0 1 trueValue using 1
    all_goals norm_num

/-- Coordinating on `false` is a pure Nash profile. -/
theorem coordinated_isNash :
    IsNash game.form (euPreference game.utility) coordinated := by
  rw [isNash_iff]
  intro who replacement
  rw [euPreference_apply]
  simp only [game, form, expectedUtility_pure, coordinated]
  unfold utility
  split <;> norm_num <;>
    exact ⟨payoffIntegrable_pure _ _, payoffIntegrable_pure _ _⟩

/-- Every positive-horizon empirical belief of the constant history is the
canonical pure embedding of the coordinated profile. -/
theorem constant_empiricalBelief (t : ℕ) :
    game.form.empiricalBelief constantHistory (t + 1) = game.form.purify coordinated := by
  funext who
  simp only [GameForm.empiricalBelief, GameForm.empiricalMarginal,
    constantHistory, coordinated, GameForm.purify]
  have hconst : (fun _ : Fin (t + 1) => false) =
      Function.const (Fin (t + 1)) false := rfl
  rw [hconst, PMF.map_const]

/-- The constant coordination path is genuine fictitious play.  The proof does
not unfold a second payoff comparison: it consumes the canonical mixed Nash
best-response theorem. -/
theorem constant_isFictitiousPlay : game.IsFictitiousPlay constantHistory := by
  intro t who
  have hmixed := coordinated_isNash.purify_of_finite
  rw [isNash_iff_isBestResponse] at hmixed
  rw [constant_empiricalBelief]
  have hplayed : PMF.pure (constantHistory (t + 1) who) =
      game.form.purify coordinated who := rfl
  rw [hplayed]
  exact hmixed who

/-- The general finite existence theorem constructs a fictitious-play history
without assuming that a Nash equilibrium or constant best-response path is
already known. -/
theorem exists_generatedFictitiousPlay :
    ∃ history : ℕ → Profile game.form.sig, game.IsFictitiousPlay history :=
  game.exists_isFictitiousPlay <| by
    intro who profile
    exact payoffIntegrable_of_finite _ _

/-- Alternating away from the initially coordinated action is not fictitious
play: in round one, `true` is not a best response to the empirical all-false
profile. -/
theorem alternating_not_isFictitiousPlay :
    ¬ game.IsFictitiousPlay alternatingHistory := by
  intro hplay
  have hempirical :
      game.form.empiricalBelief alternatingHistory 1 =
        game.form.purify coordinated := by
    funext who
    show PMF.map (fun round : Fin 1 => alternatingHistory round who)
        (PMF.uniformOfFintype (Fin 1)) = PMF.pure false
    rw [show (fun round : Fin 1 => alternatingHistory round who) = fun _ => false by
      funext round
      have hround : round = 0 := Subsingleton.elim _ _
      subst round
      rfl]
    exact (PMF.uniformOfFintype (Fin 1)).map_const false
  have hbest := hplay 0 0 (PMF.pure false)
  have hplayed : alternatingHistory 1 0 = true := by
    norm_num [alternatingHistory]
  rw [hempirical, hplayed, euPreference_apply] at hbest
  rcases hbest with ⟨_, _, hbest⟩
  have hfalseLaw : game.form.mixed.play
      (Profile.update (game.form.purify coordinated) 0 (PMF.pure false)) =
      PMF.pure (false, false) := by
    rw [purify_update, GameForm.mixed_play_purify]
    rfl
  have htrueLaw : game.form.mixed.play
      (Profile.update (game.form.purify coordinated) 0 (PMF.pure true)) =
      PMF.pure (true, false) := by
    rw [purify_update, GameForm.mixed_play_purify]
    rfl
  have hfalseLaw' :
      (independentProduct
        (Profile.update (form.purify coordinated) 0 (PMF.pure false))).bind
          (fun profile => PMF.pure (profile 0, profile 1)) =
        PMF.pure (false, false) := by
    simpa only [game, form] using hfalseLaw
  have htrueLaw' :
      (independentProduct
        (Profile.update (form.purify coordinated) 0 (PMF.pure true))).bind
          (fun profile => PMF.pure (profile 0, profile 1)) =
        PMF.pure (true, false) := by
    simpa only [game, form] using htrueLaw
  have hnumeric : utility (false, false) 0 ≤ utility (true, false) 0 := by
    simpa only [hfalseLaw', htrueLaw', expectedUtility_pure] using hbest
  norm_num [utility] at hnumeric

end GameTheory.Tests.FictitiousPlay
