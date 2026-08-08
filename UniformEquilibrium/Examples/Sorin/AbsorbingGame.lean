/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import UniformEquilibrium.VanishingDiscount.Bellman.Variety
import UniformEquilibrium.Examples.BigMatch.Uniform

/-!
# Sorin's absorbing game: a discount-constant stationary equilibrium

Sorin's two-player absorbing game (Sorin 1986, *International Journal of Game
Theory* **15**, 101–107, DOI `10.1007/BF01770978`).  There is one nonabsorbing
state; player 1 chooses `Top`/`Bottom`, player 2 chooses `Left`/`Right`:

```text
              Left           Right
Top        (0, 2)*        (1, 0)*
Bottom     (1, 0)         (0, 1)
```

`*` means absorption at the displayed payoff, which is then received at every
later stage as well.  `Bottom` never absorbs.

## What is proved

For every discount factor `β` the stationary profile

```text
  Pr₁(Top) = λ / (2 + λ),      Pr₂(Left) = 1 / 2,      λ := 1 - β
```

together with the continuation value `(1/2, 2/3)` at the live state satisfies
**all** of Fink's discounted stationary Bellman conditions, and the resulting
discounted value is exactly `(1/2, 2/3)` — *constant in the discount*.  The
mechanism is double indifference: against `Pr₂(Left) = 1/2` both of player 1's
actions have auxiliary value exactly `1/2`, and against `Pr₁(Top) = λ/(2+λ)`
both of player 2's actions have auxiliary value exactly `2/3`
(`auxEU_pure_eq_value`).

## Strength achieved

Full **behavioral** discounted Nash, not merely stationary-deviation optimality:
`isDiscountedNash` states `IsDiscountedεNash β s₀ 0`, i.e. no unilateral
*history-dependent, randomized* behavior strategy gains anything.  This is
obtained from the Fink certificate `isDiscountedStationaryBellmanEq` through the
historywise Bellman inequalities of `Fink.lean` together with the two telescoping
lemmas `le_discountedPayoff_of_bellman_le` and its exact dual
`discountedPayoff_le_of_bellman_ge`, both in `Discounted.lean`.

## Discount convention

The repository normalizes the discounted payoff as

`discountedPayoff β σ s₀ who = (1 - β) * ∑ₜ βᵗ · (stage-`t` expected payoff)`,

so the *current stage* carries weight `1 - β` and the continuation carries
weight `β`.  Sorin's `λ` (weight of the current stage) is therefore `λ = 1 - β`,
and the mixing probability `λ / (2 + λ)` becomes `(1 - β) / (3 - β)`; this is
`topProb`, with `topProb_eq_stageWeightRatio` recording the translation.

## Uniform-payoff separation

The later module `SorinUniformSeparation` machine-checks the exact
accounting identity

`2·averagePayoff₁ + averagePayoff₂ = 2 - bottomRightOccupation`,

the limit passage from vanishing live `(Bottom, Right)` occupation to the line
`2w₁ + w₂ = 2`, and the arithmetic fact that `(1/2, 2/3)` is not on that line.
It isolates the genuinely substantive stopping assertion—sufficiently accurate
uniform approximate equilibria force that occupation to vanish—as a concrete,
target-independent proposition.  `SorinOccupationVanishing` discharges that
proposition from the quantitative bound `survivalLimit ≤ 14 * epsilon` and
thereby proves the separation line and endpoint exclusion unconditionally.

## File status

Result / falsifier: a permanently kept worked instance.  Sorry-free; the
capstones `isDiscountedStationaryBellmanEq`, `discountedPayoff_eq_value`,
`discountedPayoff_live`, and `isDiscountedNash` are axiom-audited.

## Main definitions

* `SorinAbsorbingGame.game` — the stochastic game
* `SorinAbsorbingGame.topProb` — `Pr₁(Top)` as a function of the discount factor
* `SorinAbsorbingGame.profile` — the stationary mixed profile
* `SorinAbsorbingGame.value` — the continuation value vector

## Main results

* `SorinAbsorbingGame.payoff_live_top_left` and its seven companions — the
  cell-by-cell `rfl` fencing of the payoff and transition tables
* `SorinAbsorbingGame.absTL_isAbsorbingState`,
  `SorinAbsorbingGame.absTR_isAbsorbingState`,
  `SorinAbsorbingGame.live_not_isAbsorbingState` — the absorbing structure
* `SorinAbsorbingGame.auxEU_pure_eq_value` — double indifference: **every** pure
  action of **either** player has discounted auxiliary value exactly `value s who`
* `SorinAbsorbingGame.isDiscountedStationaryBellmanEq` — the Fink certificate,
  for every `β ∈ [0, 1]`
* `SorinAbsorbingGame.discountedPayoff_eq_value` — the exact discounted value
* `SorinAbsorbingGame.discountedPayoff_live` — that value is `(1/2, 2/3)` at the
  live state, for every discount factor
* `SorinAbsorbingGame.isDiscountedNash` — exact (`ε = 0`) discounted Nash against
  arbitrary history-dependent unilateral deviations
* `SorinAbsorbingGame.topProb_eq_stageWeightRatio` — rationality of the mixing
  coordinate in `λ`
* `SorinAbsorbingGame.mixedStageEU_live_player_one` /
  `SorinAbsorbingGame.mixedStageEU_live_player_two` — the *stage* payoffs, which
  show the discount-constancy of the value is a genuine aggregation effect
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace StochasticGame

open Math.Probability Math.PMFProduct

variable {ι : Type}

namespace SorinAbsorbingGame

open Math.Probability Math.PMFProduct

/-! ## The game -/

/-- The two players: `false` is player 1 (rows), `true` is player 2 (columns). -/
abbrev Player := Bool

/-- Both players have two actions.  For player 1, `true` is `Top` and `false` is
`Bottom`; for player 2, `true` is `Left` and `false` is `Right`. -/
abbrev Action (_ : Player) : Type := Bool

/-- Three states: the unique nonabsorbing (live) state, and the two absorbing
states entered by `(Top, Left)` and `(Top, Right)`. -/
inductive State
  | live
  | absTL
  | absTR
  deriving DecidableEq, Fintype

/-- The payoff vector paying `u₁` to player 1 and `u₂` to player 2. -/
def pair (u₁ u₂ : ℝ) : Payoff Player := fun who => if who then u₂ else u₁

@[simp] theorem pair_apply_false (u₁ u₂ : ℝ) : pair u₁ u₂ false = u₁ := rfl

@[simp] theorem pair_apply_true (u₁ u₂ : ℝ) : pair u₁ u₂ true = u₂ := rfl

/-- The joint pure action in which player 1 plays `x` and player 2 plays `y`. -/
def act (x y : Bool) : ∀ i : Player, Action i := fun i => if i then y else x

@[simp] theorem act_false (x y : Bool) : act x y false = x := rfl

@[simp] theorem act_true (x y : Bool) : act x y true = y := rfl

/-- Sorin's stage-payoff table.  At the live state, `(Top, Left)` pays `(0, 2)`,
`(Top, Right)` pays `(1, 0)`, `(Bottom, Left)` pays `(1, 0)` and `(Bottom, Right)`
pays `(0, 1)`; the absorbing states pay their entry payoff forever. -/
def payoff (s : State) (a : ∀ i : Player, Action i) (who : Player) : ℝ :=
  match s with
  | .live =>
      if a false then
        (if a true then pair 0 2 who else pair 1 0 who)
      else
        (if a true then pair 1 0 who else pair 0 1 who)
  | .absTL => pair 0 2 who
  | .absTR => pair 1 0 who

/-- The deterministic transition rule: only `Top` absorbs, into the state named
after the column that was played against it. -/
def nextState (s : State) (a : ∀ i : Player, Action i) : State :=
  match s with
  | .live => if a false then (if a true then .absTL else .absTR) else .live
  | .absTL => .absTL
  | .absTR => .absTR

/-- The transition kernel: a Dirac mass on `nextState`. -/
def transition (s : State) (a : ∀ i : Player, Action i) : PMF State :=
  PMF.pure (nextState s a)

/-- Sorin's absorbing game.  The `discount` field is irrelevant: the discounted
evaluation used below takes its discount factor as an explicit parameter. -/
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
instance : Finite game.State := inferInstanceAs (Finite State)
instance (i : Player) : Fintype (game.Act i) := inferInstanceAs (Fintype Bool)
instance (i : Player) : DecidableEq (game.Act i) :=
  inferInstanceAs (DecidableEq Bool)
instance (i : Player) : Finite (game.Act i) := inferInstanceAs (Finite Bool)
instance (i : Player) : Nonempty (game.Act i) := inferInstanceAs (Nonempty Bool)

@[simp] theorem stagePayoff_eq (s : State) (a : ∀ i : Player, Action i)
    (who : Player) : game.stagePayoff s a who = payoff s a who := rfl

@[simp] theorem transition_eq (s : State) (a : ∀ i : Player, Action i) :
    game.transition s a = PMF.pure (nextState s a) := rfl

@[simp] theorem expect_transition (s : State) (a : ∀ i : Player, Action i)
    (f : State → ℝ) : expect (transition s a) f = f (nextState s a) := by
  simp only [transition, expect_pure]

@[simp] theorem expect_game_transition (s : State)
    (a : ∀ i : Player, Action i) (f : State → ℝ) :
    expect (game.transition s a) f = f (nextState s a) := by
  rw [transition_eq, expect_pure]

/-! ### The payoff table and the transition table, cell by cell

These eight `rfl` lemmas are the machine-checked statement that the encoding
above is Sorin's table: they fence the model against a silent transposition of
players, actions, or payoff coordinates. -/

@[simp] theorem payoff_live_top_left :
    payoff State.live (act true true) = pair 0 2 := rfl

@[simp] theorem payoff_live_top_right :
    payoff State.live (act true false) = pair 1 0 := rfl

@[simp] theorem payoff_live_bottom_left :
    payoff State.live (act false true) = pair 1 0 := rfl

@[simp] theorem payoff_live_bottom_right :
    payoff State.live (act false false) = pair 0 1 := rfl

@[simp] theorem nextState_live_top_left :
    nextState State.live (act true true) = State.absTL := rfl

@[simp] theorem nextState_live_top_right :
    nextState State.live (act true false) = State.absTR := rfl

@[simp] theorem nextState_live_bottom_left :
    nextState State.live (act false true) = State.live := rfl

@[simp] theorem nextState_live_bottom_right :
    nextState State.live (act false false) = State.live := rfl

/-! ## Absorbing-state structure -/

theorem absTL_isAbsorbingState : game.IsAbsorbingState State.absTL := by
  intro a
  simp [transition, nextState]

theorem absTR_isAbsorbingState : game.IsAbsorbingState State.absTR := by
  intro a
  simp [transition, nextState]

/-- The live state is genuinely nonabsorbing: `(Top, Left)` leaves it. -/
theorem live_not_isAbsorbingState : ¬ game.IsAbsorbingState State.live := by
  intro habs
  have h := habs (fun _ => true)
  have h2 := congrArg (fun μ : PMF State => μ State.live) h
  simp [transition, nextState] at h2

/-- Player 1's stage payoff never leaves `[0, 1]` and player 2's never leaves
`[0, 2]`, so `2` bounds every stage payoff. -/
theorem abs_stagePayoff_le_two (s : State) (a : ∀ i : Player, Action i)
    (who : Player) : |game.stagePayoff s a who| ≤ 2 := by
  have h1 := Bool.eq_false_or_eq_true (a false)
  have h2 := Bool.eq_false_or_eq_true (a true)
  cases s <;> cases who <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    norm_num [payoff, pair, h1, h2]

/-! ## The stationary profile -/

/-- Player 1's probability of `Top` at discount factor `β`.  In the stage-weight
coordinate `λ = 1 - β` of Sorin's paper this is `λ / (2 + λ)`. -/
def topProb (β : ℝ) : ℝ := (1 - β) / (3 - β)

theorem three_sub_pos {β : ℝ} (hβ1 : β ≤ 1) : (0 : ℝ) < 3 - β := by linarith

theorem three_sub_ne_zero {β : ℝ} (hβ1 : β ≤ 1) : (3 : ℝ) - β ≠ 0 :=
  ne_of_gt (three_sub_pos hβ1)

theorem topProb_nonneg {β : ℝ} (hβ1 : β ≤ 1) : 0 ≤ topProb β :=
  div_nonneg (by linarith) (three_sub_pos hβ1).le

theorem topProb_le_one {β : ℝ} (hβ1 : β ≤ 1) : topProb β ≤ 1 := by
  rw [topProb, div_le_one (three_sub_pos hβ1)]
  linarith

/-- **Rationality of the selection, mixing coordinate.**  Written in Sorin's
stage-weight coordinate `λ = 1 - β`, the mixing probability is the ratio of
polynomials `λ / (2 + λ)`.  The value coordinate is rational too, being the
*constant* `(1/2, 2/3)` — see `discountedPayoff_live`. -/
theorem topProb_eq_stageWeightRatio (lam : ℝ) :
    topProb (1 - lam) = lam / (2 + lam) := by
  unfold topProb
  congr 1 <;> ring

/-- Player 2's mixed action: `Left` with probability one half. -/
def leftCoin : PMF Bool := BigMatch.coinPMF (1 / 2) (by norm_num) (by norm_num)

/-- Player 1's mixed action at discount factor `β`: `Top` with probability
`topProb β`. -/
def topCoin (β : ℝ) (hβ1 : β ≤ 1) : PMF Bool :=
  BigMatch.coinPMF (topProb β) (topProb_nonneg hβ1) (topProb_le_one hβ1)

@[simp] theorem leftCoin_true_toReal : (leftCoin true).toReal = 1 / 2 :=
  BigMatch.coinPMF_apply_true_toReal _ _ _

@[simp] theorem topCoin_true_toReal (β : ℝ) (hβ1 : β ≤ 1) :
    ((topCoin β hβ1) true).toReal = topProb β :=
  BigMatch.coinPMF_apply_true_toReal _ _ _

/-- The stationary profile: player 1 plays `Top` with probability `topProb β`,
player 2 plays `Left` with probability `1/2`, at every state. -/
def profile (β : ℝ) (hβ1 : β ≤ 1) : game.StationaryMixedProfile :=
  fun _ who => if who then leftCoin else topCoin β hβ1

@[simp] theorem profile_apply_false (β : ℝ) (hβ1 : β ≤ 1) (s : State) :
    profile β hβ1 s false = topCoin β hβ1 := rfl

@[simp] theorem profile_apply_true (β : ℝ) (hβ1 : β ≤ 1) (s : State) :
    profile β hβ1 s true = leftCoin := rfl

/-- The continuation value: `(1/2, 2/3)` at the live state, and the absorbing
payoffs at the two absorbing states. -/
def value : State → Payoff Player
  | .live => pair (1 / 2) (2 / 3)
  | .absTL => pair 0 2
  | .absTR => pair 1 0

@[simp] theorem value_live : value State.live = pair (1 / 2) (2 / 3) := rfl
@[simp] theorem value_absTL : value State.absTL = pair 0 2 := rfl
@[simp] theorem value_absTR : value State.absTR = pair 1 0 := rfl

/-! ## The discounted auxiliary matrix -/

/-- One cell of the discounted auxiliary matrix at state `s`: normalized current
payoff plus discounted continuation value. -/
def cellValue (β : ℝ) (s : State) (x y : Bool) (who : Player) : ℝ :=
  (1 - β) * payoff s (act x y) who + β * value (nextState s (act x y)) who

/-- The shared two-player Fubini expansion, specialized to this game. -/
private theorem expect_pmfPi_bool (m : ∀ i : Player, PMF (game.Act i))
    (f : game.JointAct → ℝ) :
    expect (pmfPi m) f =
      expect (m false) (fun x => expect (m true) (fun y => f (act x y))) :=
  BigMatch.expect_pmfPi_bool m f

/-- Expectation against a `PMF Bool`, written with the `true`-probability only. -/
private theorem expect_bool (μ : PMF Bool) (f : Bool → ℝ) :
    expect μ f = (μ true).toReal * f true + (1 - (μ true).toReal) * f false := by
  rw [expect_eq_sum, Fintype.sum_bool, BigMatch.pmfBool_false_toReal]

/-- **Cell decomposition of the auxiliary payoff.**  Independent mixing makes the
discounted auxiliary payoff the bilinear form of the auxiliary matrix in the two
`true`-probabilities. -/
theorem discountedAuxEU_eq_cells (β : ℝ) (s : State)
    (m : ∀ i : Player, PMF (game.Act i)) (who : Player) :
    game.discountedAuxEU β value s m who =
      (m false true).toReal *
          ((m true true).toReal * cellValue β s true true who +
            (1 - (m true true).toReal) * cellValue β s true false who) +
        (1 - (m false true).toReal) *
          ((m true true).toReal * cellValue β s false true who +
            (1 - (m true true).toReal) * cellValue β s false false who) := by
  unfold StochasticGame.discountedAuxEU StochasticGame.discountedAuxPayoff
  rw [expect_pmfPi_bool, expect_bool, expect_bool, expect_bool]
  simp only [expect_transition, cellValue]

@[simp] theorem cellValue_absTL (β : ℝ) (x y : Bool) (who : Player) :
    cellValue β State.absTL x y who = pair 0 2 who := by
  change (1 - β) * pair 0 2 who + β * pair 0 2 who = pair 0 2 who
  ring

@[simp] theorem cellValue_absTR (β : ℝ) (x y : Bool) (who : Player) :
    cellValue β State.absTR x y who = pair 1 0 who := by
  change (1 - β) * pair 1 0 who + β * pair 1 0 who = pair 1 0 who
  ring

@[simp] theorem cellValue_live_top_left (β : ℝ) (who : Player) :
    cellValue β State.live true true who = pair 0 2 who := by
  change (1 - β) * pair 0 2 who + β * pair 0 2 who = pair 0 2 who
  ring

@[simp] theorem cellValue_live_top_right (β : ℝ) (who : Player) :
    cellValue β State.live true false who = pair 1 0 who := by
  change (1 - β) * pair 1 0 who + β * pair 1 0 who = pair 1 0 who
  ring

@[simp] theorem cellValue_live_bottom_left (β : ℝ) (who : Player) :
    cellValue β State.live false true who =
      (1 - β) * pair 1 0 who + β * value State.live who := rfl

@[simp] theorem cellValue_live_bottom_right (β : ℝ) (who : Player) :
    cellValue β State.live false false who =
      (1 - β) * pair 0 1 who + β * value State.live who := rfl

/-! ## Double indifference -/

/-- **The verification identity.**  For every discount factor, every state, every
player and every *pure* action of that player, the discounted auxiliary payoff of
deviating to that action against the profile equals exactly `value s who`.

At the live state this is Sorin's double indifference: against `Pr₂(Left) = 1/2`
both `Top` and `Bottom` are worth exactly `1/2` to player 1, and against
`Pr₁(Top) = λ/(2+λ)` both `Left` and `Right` are worth exactly `2/3` to
player 2.  At the absorbing states it holds because no action matters there. -/
theorem auxEU_pure_eq_value (β : ℝ) (hβ1 : β ≤ 1) (s : State) (who : Player)
    (b : game.Act who) :
    game.discountedAuxEU β value s
        (Function.update (profile β hβ1 s) who (PMF.pure b)) who =
      value s who := by
  have hne : (3 : ℝ) - β ≠ 0 := three_sub_ne_zero hβ1
  rw [discountedAuxEU_eq_cells]
  cases who <;> cases s <;> cases b <;>
    simp [Function.update, topProb, value, pair] <;> field_simp <;> ring

/-- **Value consistency.**  On the profile itself, the auxiliary payoff is again
`value s who`: it is the average of the pure-action values, which all coincide. -/
theorem auxEU_onProfile_eq_value (β : ℝ) (hβ1 : β ≤ 1) (s : State)
    (who : Player) :
    game.discountedAuxEU β value s (profile β hβ1 s) who = value s who := by
  have hself : Function.update (profile β hβ1 s) who (profile β hβ1 s who) =
      profile β hβ1 s := Function.update_eq_self who _
  calc game.discountedAuxEU β value s (profile β hβ1 s) who
      = game.discountedAuxEU β value s
          (Function.update (profile β hβ1 s) who (profile β hβ1 s who)) who := by
        rw [hself]
    _ = expect (profile β hβ1 s who) (fun b =>
          game.discountedAuxEU β value s
            (Function.update (profile β hβ1 s) who (PMF.pure b)) who) :=
        game.discountedAuxEU_update_eq_expect_pure β value (profile β hβ1) s who _
    _ = expect (profile β hβ1 s who) (fun _ => value s who) := by
        refine congrArg (expect (profile β hβ1 s who)) (funext fun b => ?_)
        exact auxEU_pure_eq_value β hβ1 s who b
    _ = value s who := expect_const _ _

/-- **The Fink certificate.**  For every discount factor `β ∈ [0, 1]`, the
stationary profile and the value vector `(1/2, 2/3)` solve all of the discounted
stationary Bellman conditions: statewise best response against arbitrary mixed
deviations, and value consistency. -/
theorem isDiscountedStationaryBellmanEq (β : ℝ) (hβ1 : β ≤ 1) :
    game.IsDiscountedStationaryBellmanEq β (profile β hβ1) value := by
  refine ⟨fun s who d => ?_, fun s who => auxEU_onProfile_eq_value β hβ1 s who⟩
  refine game.discountedAuxEU_update_le_of_forall_pure (fun b => ?_) d
  rw [auxEU_pure_eq_value β hβ1 s who b, auxEU_onProfile_eq_value β hβ1 s who]

/-! ## Exact discounted value and exact discounted Nash -/

/-- **Exact value.**  The normalized discounted payoff of the stationary profile
is exactly `value s₀ who`, from every initial state and for every discount
factor. -/
theorem discountedPayoff_eq_value (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (s₀ : State) (who : Player) :
    game.discountedPayoff β (game.markovBehaviorProfile (profile β hβ1.le))
        s₀ who = value s₀ who := by
  have hF := isDiscountedStationaryBellmanEq β hβ1.le
  refine le_antisymm ?_ ?_
  · exact game.discountedPayoff_le_of_bellman_ge
      (fun s a => abs_stagePayoff_le_two s a who) _ s₀ (fun s => value s who)
      hβ0 hβ1 (fun t h => le_of_eq (hF.onProfile_bellman_eq who t h).symm)
  · exact game.le_discountedPayoff_of_bellman_le
      (fun s a => abs_stagePayoff_le_two s a who) _ s₀ (fun s => value s who)
      hβ0 hβ1 (fun t h => le_of_eq (hF.onProfile_bellman_eq who t h))

/-- **The discount-constant value.**  From the live state the stationary profile
is worth exactly `(1/2, 2/3)`, for *every* discount factor: player 1 gets `1/2`
and player 2 gets `2/3`, with no dependence on `β` (equivalently, on `λ`). -/
theorem discountedPayoff_live (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    game.discountedPayoff β (game.markovBehaviorProfile (profile β hβ1.le))
        State.live = pair (1 / 2) (2 / 3) := by
  funext who
  rw [discountedPayoff_eq_value β hβ0 hβ1 State.live who]
  rfl

/-- **Exact discounted Nash, behavioral form.**  No unilateral deviation to an
arbitrary history-dependent randomized behavior strategy gains anything against
the stationary profile, at any discount factor and from any initial state. -/
theorem isDiscountedNash (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (s₀ : State) :
    game.IsDiscountedεNash β s₀ 0
      (game.markovBehaviorProfile (profile β hβ1.le)) := by
  intro who dev
  have hF := isDiscountedStationaryBellmanEq β hβ1.le
  have hdev : game.discountedPayoff β
      (Function.update (game.markovBehaviorProfile (profile β hβ1.le)) who dev)
        s₀ who ≤ value s₀ who :=
    game.discountedPayoff_le_of_bellman_ge
      (fun s a => abs_stagePayoff_le_two s a who) _ s₀ (fun s => value s who)
      hβ0 hβ1 (fun t h => hF.deviation_bellman_ge who dev t h)
  rw [discountedPayoff_eq_value β hβ0 hβ1 s₀ who]
  linarith

/-! ## The value is not the stage payoff

The discount-constancy of the value is an infinite-horizon aggregation effect,
not a stagewise triviality: player 1's *stage* payoff under the profile is the
constant `1/2`, but player 2's *stage* payoff genuinely moves with the discount.
-/

/-- At auxiliary discount `0` the auxiliary payoff is the plain expected stage
payoff. -/
theorem discountedAuxEU_zero_eq_mixedStageEU (s : State)
    (m : ∀ i : Player, PMF (game.Act i)) (who : Player) :
    game.discountedAuxEU 0 value s m who = game.mixedStageEU s m who := by
  unfold StochasticGame.discountedAuxEU StochasticGame.discountedAuxPayoff
    StochasticGame.mixedStageEU
  refine congrArg (expect (pmfPi m)) (funext fun a => ?_)
  ring

/-- Player 1's expected stage payoff at the live state is exactly `1/2`, for
every discount factor — the mixing weight `topProb β` cancels out. -/
theorem mixedStageEU_live_player_one (β : ℝ) (hβ1 : β ≤ 1) :
    game.mixedStageEU State.live (profile β hβ1 State.live) false = 1 / 2 := by
  rw [← discountedAuxEU_zero_eq_mixedStageEU, discountedAuxEU_eq_cells]
  simp only [profile_apply_false, profile_apply_true, topCoin_true_toReal,
    leftCoin_true_toReal, cellValue_live_top_left, cellValue_live_top_right,
    cellValue_live_bottom_left, cellValue_live_bottom_right, value_live,
    pair_apply_false]
  ring

/-- Player 2's expected stage payoff at the live state is `(1 + λ/(2 + λ))/2`,
which **does** depend on the discount: it is `2/3` at `β = 0` but `3/5` at
`β = 1/2`.  Contrast `discountedPayoff_live`, where the aggregate is `2/3` for
every discount factor. -/
theorem mixedStageEU_live_player_two (β : ℝ) (hβ1 : β ≤ 1) :
    game.mixedStageEU State.live (profile β hβ1 State.live) true =
      (1 + topProb β) / 2 := by
  rw [← discountedAuxEU_zero_eq_mixedStageEU, discountedAuxEU_eq_cells]
  simp only [profile_apply_false, profile_apply_true, topCoin_true_toReal,
    leftCoin_true_toReal, cellValue_live_top_left, cellValue_live_top_right,
    cellValue_live_bottom_left, cellValue_live_bottom_right, value_live,
    pair_apply_true]
  ring

/-- Concretely: at `β = 1/2` player 2's stage payoff is `3/5`, while the
discounted value is `2/3`. -/
theorem mixedStageEU_live_player_two_half :
    game.mixedStageEU State.live
        (profile (1 / 2) (by norm_num) State.live) true = 3 / 5 := by
  rw [mixedStageEU_live_player_two]
  norm_num [topProb]

end SorinAbsorbingGame

end StochasticGame

end GameTheory
