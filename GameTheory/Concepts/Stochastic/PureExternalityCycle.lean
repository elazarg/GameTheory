/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.Discounted

/-!
# The two-state pure-externality cycle

The two-player, two-state stochastic game in which **every action is a pure
externality**: a player's own stage payoff never depends on that player's own
action, only on the opponent's.

```text
states            x  ⟶  y  ⟶  x  ⟶ ⋯          (every action switches the state)

at x   player 1 controls:   a = 0 ↦ (1, -1)     a = 1 ↦ (1, 1)
at y   player 2 controls:   b = 0 ↦ (-1, 1)     b = 1 ↦ (1, 1)
```

Transitions ignore all actions, so the state path is the deterministic
alternation `x, y, x, y, …`.  At `x` player 1's own payoff is `1` under both of
their actions; at `y` player 2's own payoff is `1` under both of theirs.  The
controller's action moves only the *other* player's payoff.  The prescribed
profile plays action `0` at both states.

## Provenance

This is the counterexample game of Part E (§11–§13) of an untracked local
research note on mixed-context strategic routing: a finite genuine source
datum for which all four routing strategies of the mixed-context
strategic-routing theorem fail.  **This file is only the raw layer** — the game
itself and its direct equilibrium facts.  The four-route no-go theorems need
the routing interfaces (schedulers, owner purification, common accounts,
strict children) and are deliberately not stated here.

## Encoding

Players and states are both `Bool`.  Player `false` is player 1, player `true`
is player 2; state `x = false`, state `y = true`.  The encoding is chosen so
that **state `s` is the state controlled by player `s`**, which turns the
payoff table into the single formula `stagePayoffOf`:  at state `s` under
controller action `b`, player `who` receives `1` if `who = s`, and otherwise
`1` if `b` and `-1` if `¬ b`.

## Main definitions

* `PureExternalityCycle.game` — the stochastic game
* `PureExternalityCycle.statePath` — the deterministic state alternation
* `PureExternalityCycle.constProfile` — the profile playing a fixed action
  after every history; `constProfile false` is the prescribed profile

## Main results

* `PureExternalityCycle.stagePayoff_indep_own_action` — the pure-externality
  property: a player's stage payoff is invariant under changing their own
  action
* `PureExternalityCycle.finiteAveragePayoff_of_opponents_const` — **payoff
  invariance**: against opponents that always play a fixed action, a player's
  finite-horizon average payoff is a closed-form constant, independent of that
  player's own (arbitrary, history-dependent) behavior strategy
* `PureExternalityCycle.finiteAveragePayoff_update_constProfile` — the
  concrete corollary: no unilateral deviation changes the deviator's average
  payoff at all
* `PureExternalityCycle.isUniformEquilibriumPayoff_zero_x` — the capstone: the
  prescribed profile witnesses the uniform equilibrium payoff `(0, 0)` from
  state `x`
* `PureExternalityCycle.isUniformEquilibriumPayoff_one_x` — the constant-`1`
  profile witnesses the uniform equilibrium payoff `(1, 1)` from `x`, so the
  game has several uniform equilibrium payoffs
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace StochasticGame

namespace PureExternalityCycle

open Math.Probability Math.PMFProduct

/-- The two players: `false` is player 1, `true` is player 2. -/
abbrev Player := Bool

/-- Both players have two actions: `false` is action `0`, `true` is action
`1`. -/
abbrev Action (_ : Player) : Type := Bool

/-- The state `x`, whose controller is player 1. -/
def x : Bool := false

/-- The state `y`, whose controller is player 2. -/
def y : Bool := true

/-- Stage payoff of player `who` at state `s` when the controller of `s`
(namely player `s`) plays action `b`.

The controller is paid `1` whatever they do — this is the pure-externality
property — while the other player is paid `1` under the controller's action
`1` and `-1` under the controller's action `0`. -/
def stagePayoffOf (s : Bool) (who : Player) (b : Bool) : ℝ :=
  if who = s then 1 else if b then 1 else -1

/-- The stage payoff table: at state `s` only player `s`'s action matters. -/
def payoff (s : Bool) (a : Player → Bool) (who : Player) : ℝ :=
  stagePayoffOf s who (a s)

/-- Transitions ignore every action and switch the state. -/
def transition (s : Bool) (_a : Player → Bool) : PMF Bool :=
  PMF.pure (!s)

/-- The two-state pure-externality cycle as a `StochasticGame`.  The discount
factor is irrelevant here: uniform notions quantify over finite-horizon
averages. -/
abbrev game : StochasticGame Player where
  State := Bool
  Act := Action
  stagePayoff := payoff
  transition := transition
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := zero_lt_one

instance : Fintype game.State := inferInstanceAs (Fintype Bool)
instance : DecidableEq game.State := inferInstanceAs (DecidableEq Bool)
instance : Finite game.State := inferInstanceAs (Finite Bool)
instance (i : Player) : Fintype (game.Act i) := inferInstanceAs (Fintype Bool)
instance (i : Player) : DecidableEq (game.Act i) :=
  inferInstanceAs (DecidableEq Bool)
instance (i : Player) : Finite (game.Act i) := inferInstanceAs (Finite Bool)

@[simp] theorem stagePayoff_eq (s : Bool) (a : Player → Bool)
    (who : Player) :
    game.stagePayoff s a who = stagePayoffOf s who (a s) :=
  rfl

@[simp] theorem transition_eq (s : Bool) (a : Player → Bool) :
    game.transition s a = PMF.pure (!s) :=
  rfl

/-- **Pure externality.**  A player's own stage payoff never depends on that
player's own action: replacing `who`'s component of the joint action leaves
`who`'s payoff unchanged, at every state. -/
theorem stagePayoff_indep_own_action (s : Bool) (a : Player → Bool)
    (who : Player) (b : Bool) :
    game.stagePayoff s (Function.update a who b) who =
      game.stagePayoff s a who := by
  by_cases hs : who = s
  · subst hs
    simp [payoff, stagePayoffOf]
  · rw [stagePayoff_eq, stagePayoff_eq, Function.update_of_ne (Ne.symm hs)]

/-! ## The deterministic state path -/

/-- The state after `t` completed stages, starting from `s₀`.  No action can
influence it. -/
def statePath (s₀ : Bool) : ℕ → Bool
  | 0 => s₀
  | t + 1 => !(statePath s₀ t)

@[simp] theorem statePath_zero (s₀ : Bool) : statePath s₀ 0 = s₀ := rfl

@[simp] theorem statePath_succ (s₀ : Bool) (t : ℕ) :
    statePath s₀ (t + 1) = !(statePath s₀ t) := rfl

/-- The state path out of `x` alternates `x, y, x, y, …` (equation (56)). -/
theorem statePath_x_one : statePath x 1 = y := rfl

/-- The state path out of `y` alternates `y, x, y, x, …` (equation (56)). -/
theorem statePath_y_one : statePath y 1 = x := rfl

/-- Marginalization of the independent stage randomization onto one player's
coordinate. -/
private theorem expect_stageActionDist_coord (τ : game.BehaviorProfile)
    {t : ℕ} (h : game.Hist t) (j : Player) (u : Bool → ℝ) :
    expect (game.stageActionDist τ h) (fun a => u (a j)) =
      expect (τ j t h) u := by
  have hmap :
      PMF.map (fun a : game.JointAct => a j) (game.stageActionDist τ h) =
        τ j t h :=
    pmfPi_push_coord (fun i => τ i t h) j
  calc expect (game.stageActionDist τ h) (fun a => u (a j))
      = expect (PMF.map (fun a : game.JointAct => a j)
          (game.stageActionDist τ h)) u := (expect_map _ _ _).symm
    _ = expect (τ j t h) u := by rw [hmap]

/-- **The state process is deterministic.**  Whatever the behavior profile,
the expected value of any state function after `t` stages is its value at the
alternation `statePath s₀ t`. -/
theorem expectedStateValue_eq (τ : game.BehaviorProfile) (s₀ : Bool) (t : ℕ) :
    ∀ v : Bool → ℝ, game.expectedStateValue τ s₀ t v = v (statePath s₀ t) := by
  induction t with
  | zero => intro v; simp
  | succ t ih =>
    intro v
    rw [game.expectedStateValue_succ]
    have hstep : ∀ h : game.Hist t,
        expect (game.stageActionDist τ h)
            (fun a => expect (game.transition h.2 a) v) = v (!h.2) := by
      intro h
      have hinner : ∀ a : game.JointAct,
          expect (game.transition h.2 a) v = v (!h.2) := by
        intro a
        rw [transition_eq, expect_pure]
      simp only [hinner]
      exact expect_const _ _
    simp_rw [hstep]
    have h2 := ih (fun s => v (!s))
    unfold expectedStateValue at h2
    exact h2

/-! ## Payoff invariance against a constant opponent -/

/-- Against opponents who always play the fixed action `b`, player `who`'s
expected stage payoff after any history is the deterministic value
`stagePayoffOf` at the current state — whatever `who` themselves do. -/
theorem stageEUAt_of_opponents_const {b : Bool} {who : Player}
    {τ : game.BehaviorProfile}
    (hτ : ∀ i, i ≠ who → ∀ (t : ℕ) (h : game.Hist t), τ i t h = PMF.pure b)
    {t : ℕ} (h : game.Hist t) :
    game.stageEUAt τ h who = stagePayoffOf h.2 who b := by
  have hrw : game.stageEUAt τ h who =
      expect (τ h.2 t h) (fun c => stagePayoffOf h.2 who c) :=
    expect_stageActionDist_coord τ h h.2 (fun c => stagePayoffOf h.2 who c)
  rw [hrw]
  by_cases hs : h.2 = who
  · have hconst : (fun c : Bool => stagePayoffOf h.2 who c) = fun _ => (1 : ℝ) := by
      funext c
      simp [stagePayoffOf, hs]
    rw [hconst, expect_const]
    simp [stagePayoffOf, hs]
  · rw [hτ h.2 hs t h, expect_pure]

/-- Against opponents who always play the fixed action `b`, player `who`'s
expected payoff at stage `t` is determined by the state path alone. -/
theorem expectedStagePayoff_of_opponents_const {b : Bool} {who : Player}
    {τ : game.BehaviorProfile}
    (hτ : ∀ i, i ≠ who → ∀ (t : ℕ) (h : game.Hist t), τ i t h = PMF.pure b)
    (s₀ : Bool) (t : ℕ) :
    game.expectedStagePayoff τ s₀ t who =
      stagePayoffOf (statePath s₀ t) who b := by
  unfold expectedStagePayoff
  simp_rw [stageEUAt_of_opponents_const hτ]
  have h2 := expectedStateValue_eq τ s₀ t (fun s => stagePayoffOf s who b)
  unfold expectedStateValue at h2
  exact h2

/-- **Payoff invariance.**  Against opponents who always play the fixed action
`b`, player `who`'s finite-horizon average payoff is the closed-form constant
below.  It does not mention `τ who` at all: no behavior strategy of `who`,
however history-dependent or randomized, changes `who`'s own payoff stream.
This is the exact formal content of §13 of the source note. -/
theorem finiteAveragePayoff_of_opponents_const {b : Bool} {who : Player}
    {τ : game.BehaviorProfile}
    (hτ : ∀ i, i ≠ who → ∀ (t : ℕ) (h : game.Hist t), τ i t h = PMF.pure b)
    (s₀ : Bool) (T : ℕ) :
    game.finiteAveragePayoff s₀ T τ who =
      (T : ℝ)⁻¹ *
        ∑ t ∈ Finset.range T, stagePayoffOf (statePath s₀ t) who b := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  congr 1
  exact Finset.sum_congr rfl fun t _ =>
    expectedStagePayoff_of_opponents_const hτ s₀ t

/-! ## The constant profiles -/

/-- The stationary profile playing the pure action `b` after every history.
`constProfile false` is the prescribed profile of the source note. -/
def constProfile (b : Bool) : game.BehaviorProfile :=
  game.stationaryBehaviorProfile (fun _ => PMF.pure b)

@[simp] theorem constProfile_apply (b : Bool) (i : Player) (t : ℕ)
    (h : game.Hist t) : constProfile b i t h = PMF.pure b :=
  rfl

/-- Every player is a constant-`b` opponent under `constProfile b`. -/
theorem constProfile_opponents (b : Bool) (who : Player) :
    ∀ i, i ≠ who → ∀ (t : ℕ) (h : game.Hist t),
      constProfile b i t h = PMF.pure b :=
  fun i _ t h => constProfile_apply b i t h

/-- After a unilateral deviation by `who`, every *other* player is still a
constant-`b` opponent. -/
theorem update_constProfile_opponents (b : Bool) (who : Player)
    (dev : game.BehaviorStrategy who) :
    ∀ i, i ≠ who → ∀ (t : ℕ) (h : game.Hist t),
      Function.update (constProfile b) who dev i t h = PMF.pure b := by
  intro i hi t h
  rw [Function.update_of_ne hi]
  rfl

/-- **No unilateral deviation changes the deviator's payoff.**  Against the
constant profile, every behavior strategy of `who` — including the prescribed
one — yields exactly the same finite-horizon average payoff for `who`. -/
theorem finiteAveragePayoff_update_constProfile (b : Bool) (who : Player)
    (dev : game.BehaviorStrategy who) (s₀ : Bool) (T : ℕ) :
    game.finiteAveragePayoff s₀ T
        (Function.update (constProfile b) who dev) who =
      game.finiteAveragePayoff s₀ T (constProfile b) who := by
  rw [finiteAveragePayoff_of_opponents_const
      (update_constProfile_opponents b who dev) s₀ T,
    finiteAveragePayoff_of_opponents_const (constProfile_opponents b who) s₀ T]

/-! ## The prescribed profile: alternating ±1 payoffs, uniform value `(0, 0)` -/

/-- Switching the state flips the sign of every prescribed stage payoff. -/
theorem stagePayoffOf_not (s : Bool) (who : Player) :
    stagePayoffOf (!s) who false = -stagePayoffOf s who false := by
  cases s <;> cases who <;> norm_num [stagePayoffOf]

/-- Under the prescribed profile the stage payoffs alternate in sign. -/
theorem stagePayoffOf_statePath_false (s₀ : Bool) (who : Player) (t : ℕ) :
    stagePayoffOf (statePath s₀ t) who false =
      stagePayoffOf s₀ who false * (-1) ^ t := by
  induction t with
  | zero => simp
  | succ t ih => rw [statePath_succ, stagePayoffOf_not, ih, pow_succ]; ring

theorem abs_stagePayoffOf_false (s : Bool) (who : Player) :
    |stagePayoffOf s who false| = 1 := by
  cases s <;> cases who <;> norm_num [stagePayoffOf]

/-- The alternating prescribed payoffs cancel in pairs: every partial sum is
`0` or `±1`. -/
theorem abs_sum_stagePayoffOf_statePath_false (s₀ : Bool) (who : Player)
    (T : ℕ) :
    |∑ t ∈ Finset.range T, stagePayoffOf (statePath s₀ t) who false| ≤ 1 := by
  simp_rw [stagePayoffOf_statePath_false]
  rw [← Finset.mul_sum, neg_one_geom_sum, abs_mul, abs_stagePayoffOf_false,
    one_mul]
  split_ifs <;> norm_num

/-- Equation (72) of the source note: from `x`, player 1's prescribed stage
payoffs are `1, -1, 1, -1, …`. -/
theorem expectedStagePayoff_prescribed_player1 (t : ℕ) :
    game.expectedStagePayoff (constProfile false) x t false = (-1) ^ t := by
  rw [expectedStagePayoff_of_opponents_const (constProfile_opponents false false) x t,
    stagePayoffOf_statePath_false]
  norm_num [stagePayoffOf, x]

/-- Equation (73) of the source note: from `x`, player 2's prescribed stage
payoffs are `-1, 1, -1, 1, …`. -/
theorem expectedStagePayoff_prescribed_player2 (t : ℕ) :
    game.expectedStagePayoff (constProfile false) x t true = -(-1) ^ t := by
  rw [expectedStagePayoff_of_opponents_const (constProfile_opponents false true) x t,
    stagePayoffOf_statePath_false]
  norm_num [stagePayoffOf, x]

/-- Against constant-`0` opponents, every average payoff of player `who` is
within `1 / T` of `0` — both on path and after any deviation. -/
theorem abs_finiteAveragePayoff_of_opponents_const_false {who : Player}
    {τ : game.BehaviorProfile}
    (hτ : ∀ i, i ≠ who → ∀ (t : ℕ) (h : game.Hist t),
      τ i t h = PMF.pure false)
    (s₀ : Bool) (T : ℕ) :
    |game.finiteAveragePayoff s₀ T τ who| ≤ (T : ℝ)⁻¹ := by
  have hTinv : (0 : ℝ) ≤ (T : ℝ)⁻¹ := by positivity
  rw [finiteAveragePayoff_of_opponents_const hτ s₀ T, abs_mul,
    abs_of_nonneg hTinv]
  calc (T : ℝ)⁻¹ *
        |∑ t ∈ Finset.range T, stagePayoffOf (statePath s₀ t) who false|
      ≤ (T : ℝ)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left
          (abs_sum_stagePayoffOf_statePath_false s₀ who T) hTinv
    _ = (T : ℝ)⁻¹ := mul_one _

/-- **Capstone.**  The prescribed constant-`0` profile witnesses the uniform
equilibrium payoff `(0, 0)` from every initial state.  On path the alternating
`±1` stage payoffs average to within `1 / T` of `0`, and by payoff invariance
every unilateral deviation earns *exactly* the on-path payoff. -/
theorem isUniformEquilibriumPayoff_zero (s₀ : Bool) :
    game.IsUniformEquilibriumPayoff s₀ (fun _ => 0) := by
  refine game.isUniformEquilibriumPayoff_of_deviation_caps s₀ (fun _ => 0) ?_
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨constProfile false, N + 1, fun T hT => ?_⟩
  have hNT : (N : ℝ) ≤ (T : ℝ) := by
    exact_mod_cast Nat.le_of_succ_le hT
  have hTN : (1 : ℝ) / δ < (T : ℝ) := lt_of_lt_of_le hN hNT
  have hTpos : (0 : ℝ) < (T : ℝ) := lt_trans (one_div_pos.mpr hδ) hTN
  have hinv : (T : ℝ)⁻¹ ≤ δ := by
    have h1 : (1 : ℝ) < (T : ℝ) * δ := by rwa [div_lt_iff₀ hδ] at hTN
    have h2 : (T : ℝ)⁻¹ * 1 < (T : ℝ)⁻¹ * ((T : ℝ) * δ) :=
      mul_lt_mul_of_pos_left h1 (inv_pos.mpr hTpos)
    rw [mul_one, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hTpos), one_mul] at h2
    linarith
  constructor
  · intro who
    have hbound := abs_finiteAveragePayoff_of_opponents_const_false
      (constProfile_opponents false who) s₀ T
    simpa using hbound.trans hinv
  · intro who dev
    have heq := finiteAveragePayoff_update_constProfile false who dev s₀ T
    have hbound := abs_finiteAveragePayoff_of_opponents_const_false
      (constProfile_opponents false who) s₀ T
    rw [heq]
    have hup := (abs_le.mp hbound).2
    simpa using hup.trans hinv

/-- The capstone at the initial state `x`, as in the source note. -/
theorem isUniformEquilibriumPayoff_zero_x :
    game.IsUniformEquilibriumPayoff x (fun _ => 0) :=
  isUniformEquilibriumPayoff_zero x

/-! ## The constant-`1` profile: uniform value `(1, 1)` -/

@[simp] theorem stagePayoffOf_true (s : Bool) (who : Player) :
    stagePayoffOf s who true = 1 := by
  simp [stagePayoffOf]

/-- Against constant-`1` opponents every average payoff of `who` is exactly
`1`, on path and after any deviation. -/
theorem finiteAveragePayoff_of_opponents_const_true {who : Player}
    {τ : game.BehaviorProfile}
    (hτ : ∀ i, i ≠ who → ∀ (t : ℕ) (h : game.Hist t), τ i t h = PMF.pure true)
    (s₀ : Bool) {T : ℕ} (hT : 0 < T) :
    game.finiteAveragePayoff s₀ T τ who = 1 := by
  rw [finiteAveragePayoff_of_opponents_const hτ s₀ T]
  simp only [stagePayoffOf_true, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hT.ne')

/-- The constant-`1` profile witnesses the uniform equilibrium payoff `(1, 1)`
from every initial state: the game has several uniform equilibrium payoffs. -/
theorem isUniformEquilibriumPayoff_one (s₀ : Bool) :
    game.IsUniformEquilibriumPayoff s₀ (fun _ => 1) := by
  refine game.isUniformEquilibriumPayoff_of_deviation_caps s₀ (fun _ => 1) ?_
  intro δ hδ
  refine ⟨constProfile true, 1, fun T hT => ?_⟩
  have hTpos : 0 < T := hT
  refine ⟨fun who => ?_, fun who dev => ?_⟩
  · rw [finiteAveragePayoff_of_opponents_const_true
      (constProfile_opponents true who) s₀ hTpos]
    simpa using hδ.le
  · rw [finiteAveragePayoff_of_opponents_const_true
      (update_constProfile_opponents true who dev) s₀ hTpos]
    linarith

/-- The constant-`1` value at the initial state `x`. -/
theorem isUniformEquilibriumPayoff_one_x :
    game.IsUniformEquilibriumPayoff x (fun _ => 1) :=
  isUniformEquilibriumPayoff_one x

end PureExternalityCycle

end StochasticGame

end GameTheory
