/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Architectures.PublicResponse.CredibilityCriterion
import GameTheory.Concepts.Stochastic.Core.StageGame
import GameTheory.Concepts.Welfare.FolkTheorem.Feasible

/-!
# Regression examples separating architecture caps from static tests

This file formalizes two small separators between architecture caps and
static tests.

* `ArchitectureCapVsMinmax` is the one-state two-player game which pays
  `(1, 1)` only at `(A, L)`.  The one-node architecture prescribing `(A, L)`
  has exact unilateral cap `(1, 1)`, while the row player's opponent-enforced
  one-shot minmax is zero.
* `OneStageDeviationInsufficient` is the `Stay`/`Go`/`Back`/`Exploit`
  example.  A deviation `Go` followed by prescribed `Back` earns zero, but
  the history-dependent strategy which chooses `Go` and then `Exploit`
  reaches an absorbing payoff-one state after two transitions.

The second game uses one Boolean action whose interpretation is
state-dependent: `false` is `Stay` at `x` and `Back` at `y`, while `true` is
`Go` at `x` and `Exploit` at `y`.  This is the smallest faithful model of the
example; it deliberately does not add off-node named actions whose effects
are left unspecified.
-/

noncomputable section

open scoped BigOperators

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.PMFProduct Filter

namespace ArchitectureCapVsMinmax

/-- `false` is the row player and `true` is the column player. -/
abbrev Player := Bool

/-- The distinguished actions `A` and `L` are both represented by `false`. -/
abbrev Action := Bool

/-- Both players receive one exactly at `(A, L)`, and zero otherwise. -/
def payoff (a : Player → Action) (_who : Player) : ℝ :=
  if a false = false ∧ a true = false then 1 else 0

/-- The one-state repeated stochastic game used by the separator. -/
def game : StochasticGame Player where
  State := Unit
  Act := fun _ => Action
  stagePayoff := fun _ a => payoff a
  transition := fun _ _ => PMF.pure ()
  discount := 0
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

private instance gameStateFinite : Finite game.State :=
  inferInstanceAs (Finite Unit)

private instance gameActionFinite (who : Player) : Finite (game.Act who) :=
  inferInstanceAs (Finite Bool)

/-- The one-node public architecture which prescribes `(A, L)`. -/
def architecture : game.FiniteResponseArchitecture () where
  Config := Unit
  start := ()
  publicState := fun _ => ()
  play := fun _ _ => PMF.pure false
  step := fun _ _ _ => ()
  start_publicState := rfl
  step_publicState := by
    intro z a s'
    cases s'
    rfl

@[simp] theorem architecture_behavior (who : Player) (t : ℕ)
    (h : game.Hist t) :
    architecture.phaseProfile.behaviorProfile who t h = PMF.pure false :=
  rfl

@[simp] theorem prescribed_stageEUAt (t : ℕ) (h : game.Hist t)
    (who : Player) :
    game.stageEUAt architecture.phaseProfile.behaviorProfile h who = 1 := by
  let prescribedAction : game.JointAct := fun _ => false
  have hdist :
      game.stageActionDist architecture.phaseProfile.behaviorProfile h =
        PMF.pure prescribedAction := by
    change pmfPi (fun i =>
      architecture.phaseProfile.behaviorProfile i t h) = _
    rw [show (fun i => architecture.phaseProfile.behaviorProfile i t h) =
        (fun i => PMF.pure (prescribedAction i)) by
          funext i
          rw [architecture_behavior]
          rfl]
    exact Math.PMFProduct.pmfPi_pure prescribedAction
  unfold StochasticGame.stageEUAt
  rw [hdist]
  calc
    expect (PMF.pure prescribedAction)
        (fun a => game.stagePayoff h.2 a who) =
        game.stagePayoff h.2 prescribedAction who := expect_pure _ _
    _ = 1 := by simp [game, payoff, prescribedAction]

@[simp] theorem prescribed_expectedStagePayoff (t : ℕ) (who : Player) :
    game.expectedStagePayoff architecture.phaseProfile.behaviorProfile () t who = 1 := by
  unfold expectedStagePayoff
  simp

/-- The architecture attains payoff one for both players at every positive
horizon. -/
theorem prescribed_finiteAveragePayoff_eq_one {T : ℕ} (hT : 0 < T)
    (who : Player) :
    game.finiteAveragePayoff () T architecture.phaseProfile.behaviorProfile who = 1 := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simp [hT.ne']

/-- No unilateral behavior strategy can earn more than one against the
architecture, at any finite horizon. -/
theorem unilateral_finiteAveragePayoff_le_one (who : Player)
    (dev : game.BehaviorStrategy who) (T : ℕ) :
    game.finiteAveragePayoff () T
        (Function.update architecture.phaseProfile.behaviorProfile who dev) who ≤ 1 := by
  have hbound : ∀ (s : game.State) (a : game.JointAct),
      |game.stagePayoff s a who| ≤ 1 := by
    intro s a
    simp only [game, payoff]
    split <;> norm_num
  exact (le_abs_self _).trans
    (game.abs_finiteAveragePayoff_le (by norm_num) hbound () T _)

/-- Thus one is an exact, horizon-by-horizon unilateral cap for each player:
the prescribed profile attains it and every behavior deviation is below it. -/
theorem exact_architecture_cap (who : Player) :
    (∀ T, 0 < T →
      game.finiteAveragePayoff () T architecture.phaseProfile.behaviorProfile who = 1) ∧
    (∀ (dev : game.BehaviorStrategy who) T,
      game.finiteAveragePayoff () T
        (Function.update architecture.phaseProfile.behaviorProfile who dev) who ≤ 1) := by
  exact ⟨fun _ hT => prescribed_finiteAveragePayoff_eq_one hT who,
    unilateral_finiteAveragePayoff_le_one who⟩

/-- The one-shot game at the unique state, used for the static minmax test. -/
abbrev rowStageGame : KernelGame Player := game.stageGame ()

private lemma rowStageGame_eu_nonneg (ρ : KernelGame.Profile rowStageGame) :
    0 ≤ rowStageGame.eu ρ false := by
  simp only [rowStageGame, StochasticGame.stageGame, KernelGame.eu_ofPureEU,
    game, payoff]
  split <;> norm_num

private lemma rowStageGame_eu_le_one (ρ : KernelGame.Profile rowStageGame) :
    rowStageGame.eu ρ false ≤ 1 := by
  simp only [rowStageGame, StochasticGame.stageGame, KernelGame.eu_ofPureEU,
    game, payoff]
  split <;> norm_num

/-- The column player's pure punishment plays the non-`L` column. -/
private def otherColumn : rowStageGame.OpponentProfile false :=
  fun _ => true

private instance rowStrategyNonempty (who : Player) :
    Nonempty (rowStageGame.Strategy who) :=
  inferInstanceAs (Nonempty Bool)

private instance rowOpponentProfileNonempty :
    Nonempty (rowStageGame.OpponentProfile false) :=
  ⟨otherColumn⟩

private lemma bestResponse_bddAbove
    (opp : rowStageGame.OpponentProfile false) :
    BddAbove (Set.range fun own : rowStageGame.Strategy false =>
      rowStageGame.eu (rowStageGame.profileWithOpponent false own opp) false) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨own, rfl⟩
  exact rowStageGame_eu_le_one _

private lemma bestResponse_nonneg
    (opp : rowStageGame.OpponentProfile false) :
    0 ≤ rowStageGame.bestResponseValueAgainstOpponents false opp := by
  unfold KernelGame.bestResponseValueAgainstOpponents
  exact (rowStageGame_eu_nonneg _).trans
    (le_ciSup (bestResponse_bddAbove opp) false)

private lemma bestResponse_otherColumn_eq_zero :
    rowStageGame.bestResponseValueAgainstOpponents false otherColumn = 0 := by
  apply le_antisymm
  · unfold KernelGame.bestResponseValueAgainstOpponents
    refine ciSup_le fun own => ?_
    simp [rowStageGame, StochasticGame.stageGame, game, payoff, otherColumn,
      KernelGame.profileWithOpponent]
  · exact bestResponse_nonneg otherColumn

private lemma bestResponse_values_bddBelow :
    BddBelow (Set.range fun opp : rowStageGame.OpponentProfile false =>
      rowStageGame.bestResponseValueAgainstOpponents false opp) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨opp, rfl⟩
  exact bestResponse_nonneg opp

/-- In contrast with the architecture cap, the row player's opponent-enforced
one-shot minmax level is zero: the column player can choose the other column. -/
theorem row_opponentMinmaxLevel_eq_zero :
    rowStageGame.opponentMinmaxLevel false = 0 := by
  apply le_antisymm
  · calc
      rowStageGame.opponentMinmaxLevel false
          ≤ rowStageGame.bestResponseValueAgainstOpponents false otherColumn := by
            exact ciInf_le bestResponse_values_bddBelow otherColumn
      _ = 0 := bestResponse_otherColumn_eq_zero
  · unfold KernelGame.opponentMinmaxLevel
    exact le_ciInf fun opp => bestResponse_nonneg opp

end ArchitectureCapVsMinmax

namespace OneStageDeviationInsufficient

/-- The two live nodes and the absorbing payoff-one node. -/
inductive State
  | x
  | y
  | absorbed
  deriving DecidableEq, Fintype

/-- State-dependent action interpretation:
`false = Stay/Back`, `true = Go/Exploit`. -/
abbrev Action := Bool

/-- Deterministic transition table for the separator. -/
def nextState : State → Action → State
  | .x, false => .x
  | .x, true => .y
  | .y, false => .x
  | .y, true => .absorbed
  | .absorbed, _ => .absorbed

/-- The payoff is one in the absorbing state and zero at the live nodes. -/
def reward : State → ℝ
  | .absorbed => 1
  | _ => 0

/-- A one-player stochastic game is sufficient to separate a single
deviation followed by obedience from an unrestricted unilateral strategy. -/
def game : StochasticGame Unit where
  State := State
  Act := fun _ => Action
  stagePayoff := fun s _ _ => reward s
  transition := fun s a => PMF.pure (nextState s (a ()))
  discount := 0
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

private instance gameStateFinite : Finite game.State :=
  inferInstanceAs (Finite State)

private instance gameActionFinite (who : Unit) : Finite (game.Act who) :=
  inferInstanceAs (Finite Bool)

@[simp] theorem transition_eq (s : State) (a : game.JointAct) :
    game.transition s a = PMF.pure (nextState s (a ())) :=
  rfl

@[simp] theorem stagePayoff_eq (s : State) (a : game.JointAct) :
    game.stagePayoff s a () = reward s :=
  rfl

/-- A deterministic action schedule, viewed as a behavior profile. -/
def scheduledProfile (action : ℕ → Action) : game.BehaviorProfile :=
  fun _ t _ => PMF.pure (action t)

/-- The deterministic state path induced by a schedule from `x`. -/
def scheduledPath (action : ℕ → Action) : ℕ → State
  | 0 => .x
  | t + 1 => nextState (scheduledPath action t) (action t)

@[simp] theorem scheduledPath_zero (action : ℕ → Action) :
    scheduledPath action 0 = .x :=
  rfl

@[simp] theorem scheduledPath_succ (action : ℕ → Action) (t : ℕ) :
    scheduledPath action (t + 1) =
      nextState (scheduledPath action t) (action t) :=
  rfl

/-- Under a deterministic schedule the state law is a point mass at the
corresponding scheduled path. -/
theorem expectedStateValue_scheduled (action : ℕ → Action) (t : ℕ)
    (v : State → ℝ) :
    game.expectedStateValue (scheduledProfile action) .x t v =
      v (scheduledPath action t) := by
  induction t generalizing v with
  | zero => simp
  | succ t ih =>
      rw [game.expectedStateValue_succ]
      have hstep : ∀ h : game.Hist t,
          expect (game.stageActionDist (scheduledProfile action) h) (fun a =>
            expect (game.transition h.2 a) v) =
              v (nextState h.2 (action t)) := by
        intro h
        simp only [StochasticGame.stageActionDist, scheduledProfile,
          Math.PMFProduct.pmfPi_pure, expect_pure, transition_eq]
        exact expect_pure _ _
      simp_rw [hstep]
      have h := ih (fun s => v (nextState s (action t)))
      unfold expectedStateValue at h
      exact h

@[simp] theorem stageEUAt_eq_reward (σ : game.BehaviorProfile) {t : ℕ}
    (h : game.Hist t) :
    game.stageEUAt σ h () = reward h.2 := by
  unfold StochasticGame.stageEUAt
  exact expect_const _ _

theorem expectedStagePayoff_scheduled (action : ℕ → Action) (t : ℕ) :
    game.expectedStagePayoff (scheduledProfile action) .x t () =
      reward (scheduledPath action t) := by
  rw [show game.expectedStagePayoff (scheduledProfile action) .x t () =
      game.expectedStateValue (scheduledProfile action) .x t reward by
        unfold expectedStagePayoff expectedStateValue
        congr 1
        funext h
        exact stageEUAt_eq_reward _ h]
  exact expectedStateValue_scheduled action t reward

/-- `Go` once, then obey the prescribed `Stay/Back` action forever. -/
def oneDeviationSchedule (t : ℕ) : Action := decide (t = 0)

/-- The unrestricted two-step deviation plays `Go` and then `Exploit`.
Continuing with `true` after absorption is immaterial. -/
def exploitSchedule (_t : ℕ) : Action := true

abbrev oneDeviationThenObey : game.BehaviorProfile :=
  scheduledProfile oneDeviationSchedule

abbrev exploitProfile : game.BehaviorProfile :=
  scheduledProfile exploitSchedule

@[simp] theorem oneDeviationPath_zero :
    scheduledPath oneDeviationSchedule 0 = .x :=
  rfl

@[simp] theorem oneDeviationPath_one :
    scheduledPath oneDeviationSchedule 1 = .y :=
  rfl

@[simp] theorem oneDeviationPath_add_two (t : ℕ) :
    scheduledPath oneDeviationSchedule (t + 2) = .x := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [show t + 1 + 2 = (t + 2) + 1 by omega, scheduledPath_succ, ih]
      simp [oneDeviationSchedule, nextState]

@[simp] theorem exploitPath_zero :
    scheduledPath exploitSchedule 0 = .x :=
  rfl

@[simp] theorem exploitPath_one :
    scheduledPath exploitSchedule 1 = .y :=
  rfl

@[simp] theorem exploitPath_add_two (t : ℕ) :
    scheduledPath exploitSchedule (t + 2) = .absorbed := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [show t + 1 + 2 = (t + 2) + 1 by omega, scheduledPath_succ, ih]
      rfl

/-- A one-shot deviation followed by obedience has zero expected stage payoff
at every date. -/
@[simp] theorem oneDeviation_expectedStagePayoff_eq_zero (t : ℕ) :
    game.expectedStagePayoff oneDeviationThenObey .x t () = 0 := by
  rw [expectedStagePayoff_scheduled]
  rcases t with _ | _ | t
  · rfl
  · rfl
  · change reward (scheduledPath oneDeviationSchedule (t + 2)) = 0
    rw [oneDeviationPath_add_two]
    rfl

/-- Consequently the one-shot deviation followed by obedience earns zero at
every finite horizon. -/
@[simp] theorem oneDeviation_finiteAveragePayoff_eq_zero (T : ℕ) :
    game.finiteAveragePayoff .x T oneDeviationThenObey () = 0 := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff]
  simp

/-- The unrestricted strategy has zero payoff in its first two stages and
payoff one from stage two onward. -/
theorem exploit_expectedStagePayoff (t : ℕ) :
    game.expectedStagePayoff exploitProfile .x t () =
      if t < 2 then 0 else 1 := by
  rw [expectedStagePayoff_scheduled]
  rcases t with _ | _ | t
  · rfl
  · rfl
  · change reward (scheduledPath exploitSchedule (t + 2)) = 1
    rw [exploitPath_add_two]
    rfl

/-- After the two transition stages, the exact finite-horizon average of the
unrestricted strategy is `T / (T + 2)`. -/
theorem exploit_finiteAveragePayoff_add_two (T : ℕ) :
    game.finiteAveragePayoff .x (2 + T) exploitProfile () =
      (T : ℝ) / (T + 2) := by
  rw [game.finiteAveragePayoff_eq_sum_expectedStagePayoff,
    Finset.sum_range_add]
  have hfirst :
      (∑ t ∈ Finset.range 2,
        game.expectedStagePayoff exploitProfile .x t ()) = 0 := by
    norm_num [exploit_expectedStagePayoff, Finset.sum_range_succ]
  have htail :
      (∑ t ∈ Finset.range T,
        game.expectedStagePayoff exploitProfile .x (2 + t) ()) = T := by
    calc
      (∑ t ∈ Finset.range T,
          game.expectedStagePayoff exploitProfile .x (2 + t) ()) =
          ∑ _t ∈ Finset.range T, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [exploit_expectedStagePayoff]
            have hnot : ¬ 2 + t < 2 := by omega
            simp [hnot]
      _ = T := by simp
  rw [hfirst, htail]
  simp [Nat.cast_add, div_eq_mul_inv]
  ring

/-- The unrestricted strategy's finite-horizon averages converge to the
absorbing payoff one. -/
theorem exploit_finiteAveragePayoff_tendsto_one :
    Tendsto (fun T : ℕ => game.finiteAveragePayoff .x (2 + T) exploitProfile ())
      atTop (nhds 1) := by
  have hzero : Tendsto (fun T : ℕ => (2 : ℝ) / (T + 2 : ℝ))
      atTop (nhds 0) := by
    apply ((tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)).comp
      (tendsto_add_atTop_nat 2)).congr'
    exact Eventually.of_forall fun T => by
      simp [Nat.cast_add]
  have hlim : Tendsto (fun T : ℕ => 1 - (2 : ℝ) / (T + 2 : ℝ))
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hzero
  apply hlim.congr'
  filter_upwards with T
  rw [exploit_finiteAveragePayoff_add_two]
  have hne : (T : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring

end OneStageDeviationInsufficient

end StochasticGame
end GameTheory
