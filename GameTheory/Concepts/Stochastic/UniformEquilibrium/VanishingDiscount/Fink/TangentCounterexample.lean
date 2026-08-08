/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.UniformEquilibrium.VanishingDiscount.Fink.Dual

/-!
# A supported-tangent obstruction at a finite Fink limit

This file gives a three-state, two-player family of genuine discounted Fink
fixed points whose relative bias and Bellman forcing both vanish identically,
but whose limiting supported tangent target is not in the range of the
supported tangent operator.  The obstruction is produced by an opponent's
action whose probability vanishes at the same rate as `1 - β`: its two
possible transitions have opposite values and therefore cancel on profile,
while separately balancing two nonzero supported stage gains.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace FinkTangentCounterexample

open Filter
open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction

/-- The live state and two absorbing states of the counterexample. -/
inductive State
  | live
  | high
  | low
  deriving DecidableEq, Fintype

/-- `false` is player 1 and `true` is player 2.  Both have two actions.
At the live state, player 1's `false/true` actions are `A/B`, and player 2's
`false/true` actions are `C/Q`. -/
abbrev Player := Bool

abbrev Action (_ : Player) := Bool

/-- Player 1 gets `-1/+1` from `A/B` at the live state and the corresponding
constant payoff in the two absorbing states.  Player 2 always gets zero. -/
def payoff (s : State) (a : ∀ _ : Player, Bool) (who : Player) : ℝ :=
  if who then 0 else
    match s with
    | .live => if a false then 1 else -1
    | .high => 1
    | .low => -1

/-- Under player 2's limiting action `C`, the live state is absorbing.  Under
the rare action `Q`, player 1's `A` goes to the high state and `B` to the low
state. -/
def transition (s : State) (a : ∀ _ : Player, Bool) : PMF State :=
  match s with
  | .live =>
      if a true then
        if a false then PMF.pure .low else PMF.pure .high
      else PMF.pure .live
  | .high => PMF.pure .high
  | .low => PMF.pure .low

def nextState (s : State) (a : Player → Bool) : State :=
  match s with
  | .live => if a true then if a false then .low else .high else .live
  | .high => .high
  | .low => .low

lemma transition_eq_pure (s : State) (a : Player → Bool) :
    transition s a = PMF.pure (nextState s a) := by
  cases s <;> simp [transition, nextState]
  by_cases htwo : a true <;> by_cases hone : a false <;> simp [htwo, hone]

@[simp] lemma expect_transition (s : State) (a : Player → Bool)
    (A : State → Player → ℝ) (who : Player) :
    expect (transition s a) (fun t => A t who) = A (nextState s a) who := by
  rw [transition_eq_pure, expect_pure]

/-- The stochastic game used by the tangent counterexample. -/
abbrev game : StochasticGame Player where
  State := State
  Act := Action
  stagePayoff := payoff
  transition := transition
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

instance : Fintype game.State := inferInstanceAs (Fintype State)
instance : DecidableEq game.State := inferInstanceAs (DecidableEq State)
instance (who : Player) : Fintype (game.Act who) := inferInstanceAs (Fintype Bool)

/-- Discount factors tending to one. -/
def discount (n : ℕ) : ℝ := (n + 1 : ℝ) / (n + 2 : ℝ)

/-- Probability of player 2's rare action. -/
def rareProbability (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

/-- The normalized discounted value, independent of the discount factor. -/
def value (s : State) (who : Player) : ℝ :=
  if who then 0 else
    match s with
    | .live => 0
    | .high => 1
    | .low => -1

/-- Real simplex coordinates of the stationary profile.  Player 1 mixes
equally at the live state.  Player 2 uses `Q` with probability `1/(n+1)`.
At absorbing states both players use `false`. -/
def weight (n : ℕ) (p : State × Player) (d : Bool) : ℝ :=
  match p.1 with
  | .live =>
      if p.2 then
        if d then rareProbability n else 1 - rareProbability n
      else 1 / 2
  | .high | .low => if d then 0 else 1

lemma discount_nonneg (n : ℕ) : 0 ≤ discount n := by
  unfold discount
  positivity

lemma discount_le_one (n : ℕ) : discount n ≤ 1 := by
  unfold discount
  apply (div_le_one (by positivity : (0 : ℝ) < n + 2)).2
  norm_num

lemma discount_lt_one (n : ℕ) : discount n < 1 := by
  unfold discount
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_lt_one (by positivity : (0 : ℝ) < n + 2)]
  linarith

lemma rareProbability_nonneg (n : ℕ) : 0 ≤ rareProbability n := by
  unfold rareProbability
  positivity

lemma rareProbability_le_one (n : ℕ) : rareProbability n ≤ 1 := by
  unfold rareProbability
  apply (div_le_one (by positivity : (0 : ℝ) < n + 1)).2
  norm_num

lemma discount_mul_rareProbability (n : ℕ) :
    discount n * rareProbability n = 1 - discount n := by
  unfold discount rareProbability
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma weight_mem_simplex (n : ℕ) (p : State × Player) :
    weight n p ∈ stdSimplex ℝ Bool := by
  constructor
  · intro d
    cases p with
    | mk s who =>
      cases s <;> cases who <;> cases d <;>
        simp [weight, rareProbability_nonneg, rareProbability_le_one]
  · rw [Fintype.sum_bool]
    cases p with
    | mk s who =>
      cases s <;> cases who
      all_goals norm_num [weight]

/-- The stationary profile represented by `weight`. -/
def profile (n : ℕ) : game.StationaryMixedProfile := fun s who =>
  (stdSimplexEquiv (α := Bool)).symm
    ⟨weight n (s, who), weight_mem_simplex n (s, who)⟩

@[simp] lemma profile_apply_toReal (n : ℕ) (s : State) (who : Player)
    (d : Bool) : ((profile n s who) d).toReal = weight n (s, who) d := by
  change ((ofVector (weight n (s, who))
    (weight_mem_simplex n (s, who)) d).toReal = weight n (s, who) d)
  exact ofVector_toReal (weight_mem_simplex n (s, who)) d

lemma abs_value_le_one (s : State) (who : Player) : |value s who| ≤ 1 := by
  cases s <;> cases who <;> simp [value]

/-- The canonical Fink-domain encoding of the profile and value. -/
def point (n : ℕ) : game.finkDomain 1 :=
  game.finkPointOfProfileValue (profile n) value abs_value_le_one

@[simp] lemma finkValue_point (n : ℕ) : game.finkValue (point n) = value :=
  rfl

@[simp] lemma point_weight (n : ℕ) (s : State) (who : Player) (d : Bool) :
    (point n).1.1 (s, who) d = weight n (s, who) d :=
  by
    have hp : game.finkProfile (point n) = profile n := by
      simpa only [point] using
        game.finkProfile_finkPointOfProfileValue
          (profile n) value abs_value_le_one
    calc
      (point n).1.1 (s, who) d =
          ((game.finkProfile (point n) s who) d).toReal :=
        (game.finkProfile_apply_toReal (point n) s who d).symm
      _ = ((profile n s who) d).toReal := by rw [hp]
      _ = weight n (s, who) d := profile_apply_toReal n s who d

/-- Two-coordinate Fubini formula for the product of two Boolean PMFs. -/
lemma expect_pmfPi_bool (sigma : Player → PMF Bool)
    (f : (Player → Bool) → ℝ) :
    expect (pmfPi sigma) f =
      expect (sigma false) (fun a =>
        expect (sigma true) (fun b => f (fun who => if who then b else a))) := by
  classical
  have hfalse : Function.update sigma false (sigma false) = sigma := by
    exact Function.update_eq_self false sigma
  rw [← hfalse, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma false))
  funext a
  have htrue : Function.update (Function.update sigma false (PMF.pure a))
      true (sigma true) = Function.update sigma false (PMF.pure a) := by
    funext who
    cases who <;> simp
  rw [← htrue, pmfPi_update_bind, expect_bind]
  apply congrArg (expect (sigma true))
  funext b
  have hpure : Function.update (Function.update sigma false (PMF.pure a))
        true (PMF.pure b) =
      fun who => PMF.pure (if who then b else a) := by
    funext who
    cases who <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

/-- Continuation value of a pure joint action, before wrapping it in the
deterministic transition PMF. -/
def continuationValue (s : State) (a : Player → Bool) (who : Player) : ℝ :=
  if who then 0 else
    match s with
    | .live => if a true then if a false then -1 else 1 else 0
    | .high => 1
    | .low => -1

@[simp] lemma expect_transition_value (s : State) (a : Player → Bool)
    (who : Player) :
    expect (transition s a) (fun t => value t who) =
      continuationValue s a who := by
  cases s <;> cases who <;> simp [transition, value, continuationValue]
  · by_cases htwo : a true <;> by_cases hone : a false <;> simp [htwo, hone]

/-- Every pure action of either player has exactly the encoded value in the
discounted auxiliary game.  For player 1 at the live state this is the exact
identity `discount n * rareProbability n = 1 - discount n`. -/
lemma pure_discountedAuxEU_eq (n : ℕ) (s : State) (who : Player) (d : Bool) :
    game.discountedAuxEU (discount n) value s
        (Function.update (profile n s) who (PMF.pure d)) who =
      value s who := by
  unfold StochasticGame.discountedAuxEU
  rw [expect_pmfPi_bool]
  simp only [discountedAuxPayoff, expect_transition_value]
  cases s <;> cases who <;> cases d <;>
    simp only [payoff, value, continuationValue, expect_eq_sum,
      Fintype.sum_bool, Function.update_self, ne_eq,
      Bool.true_eq_false, Bool.false_eq_true, not_false_eq_true,
      Function.update_of_ne, Bool.if_false_right, Bool.if_true_right]
  all_goals
    rw [profile_apply_toReal, profile_apply_toReal]
    simp [weight]
    try nlinarith [discount_mul_rareProbability n]

lemma mixedDeviation_discountedAuxEU_eq (n : ℕ) (s : State) (who : Player)
    (dev : PMF Bool) :
    game.discountedAuxEU (discount n) value s
        (Function.update (profile n s) who dev) who = value s who := by
  unfold StochasticGame.discountedAuxEU
  rw [pmfPi_update_bind, expect_bind]
  change expect dev (fun d => game.discountedAuxEU (discount n) value s
    (Function.update (profile n s) who (PMF.pure d)) who) = value s who
  have hfun : (fun d => game.discountedAuxEU (discount n) value s
      (Function.update (profile n s) who (PMF.pure d)) who) =
      fun _ => value s who := by
    funext d
    exact pure_discountedAuxEU_eq n s who d
  rw [hfun, expect_const]

lemma profile_discountedAuxEU_eq (n : ℕ) (s : State) (who : Player) :
    game.discountedAuxEU (discount n) value s (profile n s) who =
      value s who := by
  rw [← Function.update_eq_self who (profile n s)]
  exact mixedDeviation_discountedAuxEU_eq n s who (profile n s who)

/-- The explicit profile/value pair is a discounted stationary Bellman
equilibrium for every member of the sequence. -/
lemma isDiscountedStationaryBellmanEq (n : ℕ) :
    game.IsDiscountedStationaryBellmanEq (discount n) (profile n) value := by
  constructor
  · intro s who dev
    rw [mixedDeviation_discountedAuxEU_eq, profile_discountedAuxEU_eq]
  · exact profile_discountedAuxEU_eq n

lemma abs_payoff_le_one (s : State) (a : Player → Bool) (who : Player) :
    |game.stagePayoff s a who| ≤ 1 := by
  cases s <;> cases who <;> (try by_cases h : a false) <;> simp [payoff, h]

/-- Every encoded point in the family is literally a fixed point of Fink's
finite-dimensional map. -/
theorem finkMap_point_eq (n : ℕ) :
    game.finkMap (discount n) 1 (discount_nonneg n) (discount_le_one n)
        abs_payoff_le_one (point n) = point n := by
  exact game.finkMap_finkPointOfProfileValue_eq_self
    (discount n) 1 (discount_nonneg n) (discount_le_one n)
      abs_payoff_le_one (profile n) value abs_value_le_one
        (isDiscountedStationaryBellmanEq n)

/-- Limiting real simplex coordinates. -/
def limitWeight (p : State × Player) (d : Bool) : ℝ :=
  match p.1 with
  | .live => if p.2 then if d then 0 else 1 else 1 / 2
  | .high | .low => if d then 0 else 1

lemma limitWeight_mem_simplex (p : State × Player) :
    limitWeight p ∈ stdSimplex ℝ Bool := by
  constructor
  · intro d
    cases p with
    | mk s who => cases s <;> cases who <;> cases d <;> simp [limitWeight]
  · rw [Fintype.sum_bool]
    cases p with
    | mk s who => cases s <;> cases who <;> norm_num [limitWeight]

def limitProfile : game.StationaryMixedProfile := fun s who =>
  (stdSimplexEquiv (α := Bool)).symm
    ⟨limitWeight (s, who), limitWeight_mem_simplex (s, who)⟩

@[simp] lemma limitProfile_apply_toReal (s : State) (who : Player) (d : Bool) :
    ((limitProfile s who) d).toReal = limitWeight (s, who) d := by
  change ((ofVector (limitWeight (s, who))
    (limitWeight_mem_simplex (s, who)) d).toReal = limitWeight (s, who) d)
  exact ofVector_toReal (limitWeight_mem_simplex (s, who)) d

def limitPoint : game.finkDomain 1 :=
  game.finkPointOfProfileValue limitProfile value abs_value_le_one

@[simp] lemma finkValue_limitPoint : game.finkValue limitPoint = value := rfl

@[simp] lemma limitPoint_weight (s : State) (who : Player) (d : Bool) :
    limitPoint.1.1 (s, who) d = limitWeight (s, who) d := by
  have hp : game.finkProfile limitPoint = limitProfile := by
    simpa only [limitPoint] using
      game.finkProfile_finkPointOfProfileValue
        limitProfile value abs_value_le_one
  calc
    limitPoint.1.1 (s, who) d =
        ((game.finkProfile limitPoint s who) d).toReal :=
      (game.finkProfile_apply_toReal limitPoint s who d).symm
    _ = ((limitProfile s who) d).toReal := by rw [hp]
    _ = limitWeight (s, who) d := limitProfile_apply_toReal s who d

lemma tendsto_rareProbability_zero :
    Tendsto rareProbability atTop (nhds 0) := by
  change Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

lemma tendsto_weight (p : State × Player) (d : Bool) :
    Tendsto (fun n => weight n p d) atTop (nhds (limitWeight p d)) := by
  cases p with
  | mk s who =>
    cases s <;> cases who <;> cases d
    all_goals simp only [weight, limitWeight, if_true, if_false,
      Bool.false_eq_true, tendsto_const_nhds]
    · simpa using tendsto_rareProbability_zero.const_sub 1
    · exact tendsto_rareProbability_zero

/-- The explicit fixed points converge to the profile where player 2's rare
action has disappeared. -/
theorem tendsto_point : Tendsto point atTop (nhds limitPoint) := by
  rw [tendsto_subtype_rng]
  apply (Prod.tendsto_iff _ _).2
  constructor
  · apply tendsto_pi_nhds.2
    intro p
    rcases p with ⟨s, who⟩
    apply tendsto_pi_nhds.2
    intro d
    rw [limitPoint_weight]
    apply (tendsto_weight (s, who) d).congr'
    exact Filter.Eventually.of_forall fun n => (point_weight n s who d).symm
  · exact tendsto_const_nhds

lemma discount_eq_one_sub (n : ℕ) :
    discount n = 1 - 1 / (n + 2 : ℝ) := by
  unfold discount
  have hn : (n + 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem tendsto_discount_one : Tendsto discount atTop (nhds 1) := by
  have hzero := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hzero' : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 2))
      atTop (nhds 0) := by
    apply (hzero.comp (tendsto_add_atTop_nat 1)).congr'
    exact Filter.Eventually.of_forall fun n => by
      simp [Nat.cast_add]
      ring
  have h : Tendsto (fun n : ℕ => 1 - (1 : ℝ) / (n + 2))
      atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hzero')
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => (discount_eq_one_sub n).symm

lemma finkProfile_limitPoint_eq : game.finkProfile limitPoint = limitProfile := by
  simpa only [limitPoint] using
    game.finkProfile_finkPointOfProfileValue
      limitProfile value abs_value_le_one

lemma limit_live_playerOne_actionA_support :
    game.finkProfile limitPoint .live false false ≠ 0 := by
  intro hzero
  have hreal : ((game.finkProfile limitPoint .live false false).toReal : ℝ) = 0 := by
    simp [hzero]
  rw [game.finkProfile_apply_toReal, limitPoint_weight] at hreal
  norm_num [limitWeight] at hreal

/-- At the limiting profile, both supported actions of player 1 keep the live
state fixed, so no state potential can create a continuation gain there. -/
lemma finkContinuationGain_limit_live_playerOne (A : State → Payoff Player)
    (d : Bool) :
    game.finkContinuationGain A limitPoint .live false d = 0 := by
  unfold finkContinuationGain
  rw [finkProfile_limitPoint_eq]
  rw [expect_pmfPi_bool, expect_pmfPi_bool]
  simp only [expect_transition]
  simp only [expect_eq_sum, nextState, Fintype.sum_bool,
    Function.update_self, ne_eq, Bool.true_eq_false,
    not_false_eq_true, Function.update_of_ne]
  rw [limitProfile_apply_toReal]
  norm_num [limitWeight]
  rw [limitProfile_apply_toReal]
  norm_num [limitWeight]
  rw [limitProfile_apply_toReal]
  cases d <;> norm_num [limitWeight]
  all_goals
    rw [limitProfile_apply_toReal]
    norm_num [limitWeight]
    ring

/-- Player 1's supported action `A` has tangent target coordinate `-1`. -/
lemma finkStageGain_limit_live_playerOne_actionA :
    game.finkStageGain limitPoint .live false false = -1 := by
  unfold finkStageGain mixedStageEU
  rw [finkProfile_limitPoint_eq]
  rw [expect_pmfPi_bool, expect_pmfPi_bool]
  simp only [payoff, expect_eq_sum, Fintype.sum_bool,
    Function.update_self, ne_eq, Bool.true_eq_false,
    not_false_eq_true, Function.update_of_ne,
    Bool.if_false_right, Bool.decide_eq_true]
  rw [limitProfile_apply_toReal]
  norm_num [limitWeight]
  rw [limitProfile_apply_toReal]
  norm_num [limitWeight]
  rw [limitProfile_apply_toReal]
  norm_num [limitWeight]
  rw [limitProfile_apply_toReal]
  norm_num [limitWeight]

/-- The limiting supported tangent target is not in the supported tangent
operator's range, even for the zero Poisson correction. -/
theorem no_finkSupportHarmonicAdjustment :
    ¬ ∃ A : State → Payoff Player,
      game.finkContinuationResidualVector A limitPoint = 0 ∧
        ∀ s who (d : Bool), game.finkProfile limitPoint s who d ≠ 0 →
          game.finkContinuationGain A limitPoint s who d =
            game.finkStageGain limitPoint s who d +
              game.finkContinuationGain
                ((0 : State → Payoff Player) - 0) limitPoint s who d := by
  apply game.not_exists_finkSupportHarmonicAdjustment_of_actionCoordinate
    limitPoint (0 : State → Payoff Player) 0 .live false false
  · exact limit_live_playerOne_actionA_support
  · intro A
    exact finkContinuationGain_limit_live_playerOne A false
  · rw [finkStageGain_limit_live_playerOne_actionA]
    have hzero : game.finkContinuationGain
        ((0 : State → Payoff Player) - 0) limitPoint .live false false = 0 := by
      simpa using finkContinuationGain_limit_live_playerOne
        (0 : State → Payoff Player) false
    rw [hzero]
    norm_num

/-- The relative bias is identically zero along the whole fixed-point
sequence because its value coordinate is exactly the limiting value. -/
lemma finkRelativeBias_point_eq_zero (n : ℕ) :
    game.finkRelativeBias (discount n) value (point n) = 0 := by
  ext s who
  simp [finkRelativeBias]

lemma finkStageEU_limitPoint (s : State) (who : Player) :
    game.finkStageEU limitPoint s who = value s who := by
  unfold finkStageEU
  rw [finkProfile_limitPoint_eq, expect_pmfPi_bool]
  cases s <;> cases who <;> simp only [payoff, value, expect_eq_sum,
    Fintype.sum_bool, Bool.false_eq_true, Bool.if_false_right,
    Bool.if_true_right]
  all_goals
    rw [limitProfile_apply_toReal]
    norm_num [limitWeight]
  all_goals
    rw [limitProfile_apply_toReal]
    norm_num [limitWeight]
  all_goals
    rw [limitProfile_apply_toReal]
    norm_num [limitWeight]
  all_goals
    rw [limitProfile_apply_toReal]
    norm_num [limitWeight]

/-- The limiting Bellman forcing is exactly zero; hence `K = 0` is a valid
Poisson correction in the strongest possible sense. -/
lemma finkBellmanForcingVector_limit_eq_zero :
    game.finkBellmanForcingVector value 0 limitPoint = 0 := by
  ext s who
  unfold finkBellmanForcingVector
  rw [finkStageEU_limitPoint]
  simp [finkContinuationEU]

/-- Bundled counterexample: actual vanishing-discount Fink fixed points with
zero relative bias and zero limiting Bellman forcing converge to a supported
tangent system which has no harmonic adjustment. -/
theorem vanishingDiscount_fixedPoints_with_zeroForcing_and_tangentObstruction :
    (∀ n, game.finkMap (discount n) 1 (discount_nonneg n) (discount_le_one n)
        abs_payoff_le_one (point n) = point n) ∧
      Tendsto discount atTop (nhds 1) ∧
      Tendsto point atTop (nhds limitPoint) ∧
      (∀ n, game.finkRelativeBias (discount n) value (point n) = 0) ∧
      game.finkBellmanForcingVector value 0 limitPoint = 0 ∧
      ¬ ∃ A : State → Payoff Player,
        game.finkContinuationResidualVector A limitPoint = 0 ∧
          ∀ s who (d : Bool), game.finkProfile limitPoint s who d ≠ 0 →
            game.finkContinuationGain A limitPoint s who d =
              game.finkStageGain limitPoint s who d +
                game.finkContinuationGain
                  ((0 : State → Payoff Player) - 0) limitPoint s who d := by
  exact ⟨finkMap_point_eq, tendsto_discount_one, tendsto_point,
    finkRelativeBias_point_eq_zero, finkBellmanForcingVector_limit_eq_zero,
      no_finkSupportHarmonicAdjustment⟩

end FinkTangentCounterexample
end StochasticGame
end GameTheory
