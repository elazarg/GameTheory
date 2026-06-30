/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Equilibrium.SolutionConcepts
import GameTheory.Concepts.Equilibrium.NashCorrelatedEq
import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import Mathlib.Probability.Distributions.Uniform

/-!
# GameTheory.Concepts.Correlation.SignalTiming

Signal timing and the value of information in games.

Two information devices can expose the same exogenous randomness and still differ
strategically, because the randomness is revealed at different times.  A public
coin is revealed either before or after player `0`'s irreversible entry decision,
and this changes the equilibrium payoff set.

For player `1`, the late-signal game has a Nash equilibrium of value `3`, while
every early-signal equilibrium caps player `1` strictly below it:

```
Nash cap = CE cap = 5/2   <   CCE cap = 11/4   <   late Nash value = 3
```

All three caps are proved tight.  So the early/late separation survives at every
level — Nash, correlated, and coarse correlated — and on the early game coarse
correlation strictly beats correlation (`11/4 > 5/2`): the correlated payoff set
is a strict subset of the coarse-correlated one.

For a single decision-maker, earlier information is weakly valuable (Blackwell);
in games that monotonicity fails.

## Provenance

* Blackwell, *Equivalent comparisons of experiments* (1953): single-agent
  monotonicity, broken here in the multi-agent setting.
* Hirshleifer (1971); Bassan–Gossner–Scarsini–Zamir, *Positive value of
  information in games* (IJGT 2003): negative value of information in games.
* von Stengel–Forges, *Extensive-Form Correlated Equilibrium* (Math. OR 2008);
  Lehrer–Rosenberg–Shmaya (GEB 2010, 2013): outcome equivalence is
  solution-concept dependent.
* Thompson (1952); Elmes–Reny (JET 1994): interchange of moves is inessential
  only without information change.
* Bergemann–Morris (Theoretical Economics 2016): more information shrinks the
  Bayes-correlated-equilibrium set (motivation; cf. `Mechanism/BayesCorrelatedEq`).
-/

namespace GameTheory

open Math.Probability

namespace SignalTiming

/-- The two players: `p0` makes an entry decision, `p1` chooses a continuation. -/
inductive Player | p0 | p1
  deriving DecidableEq, Fintype

/-- A fair public coin. -/
inductive Coin | H | T
  deriving DecidableEq, Fintype

/-- The entry move. -/
inductive Move | In | Out
  deriving DecidableEq, Fintype

/-- The continuation action. -/
inductive Act | playH | playT
  deriving DecidableEq, Fintype

/-- The action recommended by the coin. -/
def recommended : Coin → Act
  | Coin.H => Act.playH
  | Coin.T => Act.playT

/-- Per-coin payoff.  `Out` pays `(2,2)`; `In` with both continuation actions
matching the coin pays `(4,3)` at `H` and `(1,3)` at `T`; any other `In` pays
`(0,0)`. -/
def branchPayoff (m : Move) (a0 a1 : Act) (c : Coin) : Payoff Player :=
  match m with
  | Move.Out => fun _ => 2
  | Move.In =>
      if a0 = recommended c ∧ a1 = recommended c then
        fun i => match c, i with
          | Coin.H, Player.p0 => 4
          | Coin.H, Player.p1 => 3
          | Coin.T, Player.p0 => 1
          | Coin.T, Player.p1 => 3
      else fun _ => 0

/-- Player `0`'s strategy in the early-signal game: entry may depend on the coin. -/
structure EarlyP0Strategy where
  move : Coin → Move
  act : Coin → Act
  deriving DecidableEq, Fintype

/-- Player `0`'s strategy in the late-signal game: entry is coin-blind; the
continuation action is coin-aware. -/
structure LateP0Strategy where
  move : Move
  act : Coin → Act
  deriving DecidableEq, Fintype

/-- Player `1` always acts after the coin. -/
abbrev P1Strategy := Coin → Act

/-- Strategy assignment for the early-signal game. -/
abbrev EarlyStrategy : Player → Type
  | Player.p0 => EarlyP0Strategy
  | Player.p1 => P1Strategy

/-- Strategy assignment for the late-signal game. -/
abbrev LateStrategy : Player → Type
  | Player.p0 => LateP0Strategy
  | Player.p1 => P1Strategy

/-- Average of a coin-indexed payoff under the fair coin. -/
noncomputable def avgFair (f : Coin → Payoff Player) : Payoff Player :=
  fun i => (f Coin.H i + f Coin.T i) / 2

/-- Expected utility in the early-signal game (coin averaged in). -/
noncomputable def earlyEU (σ : ∀ i, EarlyStrategy i) : Payoff Player :=
  avgFair fun c =>
    branchPayoff ((σ Player.p0).move c) ((σ Player.p0).act c) ((σ Player.p1) c) c

/-- Expected utility in the late-signal game; differs from `earlyEU` only in that
the entry move is coin-blind. -/
noncomputable def lateEU (σ : ∀ i, LateStrategy i) : Payoff Player :=
  avgFair fun c =>
    branchPayoff ((σ Player.p0).move) ((σ Player.p0).act c) ((σ Player.p1) c) c

/-- The early-signal game. -/
noncomputable def earlySignalGame : KernelGame Player :=
  KernelGame.ofPureEU EarlyStrategy earlyEU

/-- The late-signal game. -/
noncomputable def lateSignalGame : KernelGame Player :=
  KernelGame.ofPureEU LateStrategy lateEU

instance instFintypeEarlyStrategy : (i : Player) → Fintype (EarlyStrategy i)
  | Player.p0 => inferInstanceAs (Fintype EarlyP0Strategy)
  | Player.p1 => inferInstanceAs (Fintype P1Strategy)

instance instFintypeLateStrategy : (i : Player) → Fintype (LateStrategy i)
  | Player.p0 => inferInstanceAs (Fintype LateP0Strategy)
  | Player.p1 => inferInstanceAs (Fintype P1Strategy)

instance : Finite earlySignalGame.Outcome :=
  (inferInstance : Finite (∀ i, EarlyStrategy i))

instance : Finite lateSignalGame.Outcome :=
  (inferInstance : Finite (∀ i, LateStrategy i))

instance : Finite earlySignalGame.Profile :=
  (inferInstance : Finite (∀ i, EarlyStrategy i))

instance : Finite lateSignalGame.Profile :=
  (inferInstance : Finite (∀ i, LateStrategy i))

@[simp] theorem eu_earlySignalGame (σ : earlySignalGame.Profile) (i : Player) :
    earlySignalGame.eu σ i = earlyEU σ i := by
  simp only [earlySignalGame, KernelGame.eu_ofPureEU]

@[simp] theorem eu_lateSignalGame (σ : lateSignalGame.Profile) (i : Player) :
    lateSignalGame.eu σ i = lateEU σ i := by
  simp only [lateSignalGame, KernelGame.eu_ofPureEU]

/-- The late-signal coordinating profile: player `0` enters blind and both
players follow the coin's recommendation. -/
def lateCoordinateProfile : lateSignalGame.Profile :=
  fun i => match i with
    | Player.p0 => ({ move := Move.In, act := recommended } : LateP0Strategy)
    | Player.p1 => (recommended : P1Strategy)

theorem late_coordinate_isNash : lateSignalGame.IsNash lateCoordinateProfile := by
  intro who s'
  simp only [eu_lateSignalGame, ge_iff_le]
  match who, s' with
  | Player.p0, ⟨m, a⟩ =>
      cases m
      · -- In: coordination averages (4,1) to 5/2; deviating the act only loses
        simp only [lateEU, avgFair, lateCoordinateProfile, branchPayoff, recommended,
          and_true, Function.update_self,
          Function.update_of_ne (by decide : Player.p1 ≠ Player.p0)]
        split_ifs <;> norm_num
      · -- Out: payoff 2 < 5/2
        simp only [lateEU, avgFair, lateCoordinateProfile, branchPayoff, recommended]
        norm_num
  | Player.p1, s' =>
      simp only [lateEU, avgFair, lateCoordinateProfile, branchPayoff, recommended,
        and_true, true_and, Function.update_self,
        Function.update_of_ne (by decide : Player.p0 ≠ Player.p1)]
      split_ifs <;> norm_num

/-- Player `1`'s value `3` at the late coordinating profile. -/
theorem lateEU_coordinate_p1 : lateEU lateCoordinateProfile Player.p1 = 3 := by
  simp only [lateEU, avgFair, lateCoordinateProfile, branchPayoff, recommended]
  norm_num

/-- `3` is a late-signal Nash value for player `1`. -/
theorem late_nash_p1_three :
    ∃ v ∈ lateSignalGame.nashPayoffSet, v Player.p1 = 3 := by
  refine ⟨fun i => lateSignalGame.eu lateCoordinateProfile i,
    ⟨lateCoordinateProfile, late_coordinate_isNash, rfl⟩, ?_⟩
  simp only [eu_lateSignalGame, lateEU_coordinate_p1]

/-- The deviation that opts out specifically in the bad (`T`) branch, leaving the
`H` branch untouched. -/
def forceOutAtT (s : EarlyP0Strategy) : EarlyP0Strategy where
  move := fun c => match c with | Coin.H => s.move Coin.H | Coin.T => Move.Out
  act := s.act

/-- At any early-signal Nash equilibrium, player `0` opts out in the bad branch:
entering at `T` pays at most `1 < 2`, so `forceOutAtT` is a strict improvement on
the positive-probability `T` branch. -/
theorem early_nash_move_T_eq_out {σ : earlySignalGame.Profile}
    (hN : earlySignalGame.IsNash σ) : (σ Player.p0).move Coin.T = Move.Out := by
  have h := hN Player.p0 (forceOutAtT (σ Player.p0))
  simp only [eu_earlySignalGame, earlyEU, avgFair, forceOutAtT, ge_iff_le,
    Function.update_self,
    Function.update_of_ne (by decide : Player.p1 ≠ Player.p0)] at h
  have hout : branchPayoff Move.Out ((σ Player.p0).act Coin.T) (σ Player.p1 Coin.T)
      Coin.T Player.p0 = 2 := by simp [branchPayoff]
  rw [hout] at h
  cases hm : (σ Player.p0).move Coin.T with
  | Out => rfl
  | In =>
      exfalso
      rw [hm] at h
      have hle : branchPayoff Move.In ((σ Player.p0).act Coin.T) (σ Player.p1 Coin.T)
          Coin.T Player.p0 ≤ 1 := by
        simp only [branchPayoff, recommended]; split_ifs <;> norm_num
      linarith

@[simp] theorem branchPayoff_out (a0 a1 : Act) (c : Coin) (i : Player) :
    branchPayoff Move.Out a0 a1 c i = 2 := rfl

/-- Player `1`'s `H`-branch payoff never exceeds `3`. -/
theorem branchPayoff_H_p1_le (m : Move) (a0 a1 : Act) :
    branchPayoff m a0 a1 Coin.H Player.p1 ≤ 3 := by
  cases m with
  | In => simp only [branchPayoff, recommended]; split_ifs <;> norm_num
  | Out => simp only [branchPayoff_out]; norm_num

/-- In the `T` branch the two players' payoffs sum to at most `4`: `(2,2)` when
out, `(1,3)` when coordinated, `(0,0)` otherwise. -/
theorem branchPayoff_T_sum_le (m : Move) (a0 a1 : Act) :
    branchPayoff m a0 a1 Coin.T Player.p1 + branchPayoff m a0 a1 Coin.T Player.p0 ≤ 4 := by
  cases m with
  | In => simp only [branchPayoff, recommended]; split_ifs <;> norm_num
  | Out => simp only [branchPayoff_out]; norm_num

/-- At `H`, player `0`'s payoffs against the two opposing actions `playH`/`playT`
sum to at most `4`: only one of them can coordinate. -/
theorem branchPayoff_HH_p0_le (m : Move) (a : Act) :
    branchPayoff m a Act.playH Coin.H Player.p0
      + branchPayoff m a Act.playT Coin.H Player.p0 ≤ 4 := by
  cases m <;> cases a <;> simp [branchPayoff, recommended] <;> norm_num

/-- Player `0`'s `T`-branch payoff never exceeds `2`. -/
theorem branchPayoff_T_p0_le (m : Move) (a0 a1 : Act) :
    branchPayoff m a0 a1 Coin.T Player.p0 ≤ 2 := by
  cases m with
  | In => simp only [branchPayoff, recommended]; split_ifs <;> norm_num
  | Out => simp only [branchPayoff_out]; norm_num

/-- Player `1`'s `T`-branch payoff never exceeds `3`. -/
theorem branchPayoff_T_p1_le (m : Move) (a0 a1 : Act) :
    branchPayoff m a0 a1 Coin.T Player.p1 ≤ 3 := by
  cases m with
  | In => simp only [branchPayoff, recommended]; split_ifs <;> norm_num
  | Out => simp only [branchPayoff_out]; norm_num

/-- `T`-branch certificate for the CCE cap: `2·u₁ + u₀ ≤ 7` (out `6`, coordinated
`7`, miscoordinated `0`). -/
theorem branchPayoff_T_cce_bound (m : Move) (a b : Act) :
    2 * branchPayoff m a b Coin.T Player.p1 + branchPayoff m a b Coin.T Player.p0 ≤ 7 := by
  cases m with
  | In => simp only [branchPayoff, recommended]; split_ifs <;> norm_num
  | Out => simp only [branchPayoff_out]; norm_num

/-- `H`-branch certificate for the CCE cap: `2·u₁ + u₀` is dominated by `6` plus
player `0`'s payoff from deviating to the entry `(In, playH)` against player `1`'s
action `b`.  The indicator `branchPayoff In playH b H p0 = if b = playH then 4
else 0` is exactly the gain that player `0`'s constant deviation extracts. -/
theorem branchPayoff_H_cce_bound (m : Move) (a b : Act) :
    2 * branchPayoff m a b Coin.H Player.p1 + branchPayoff m a b Coin.H Player.p0 ≤
      6 + branchPayoff Move.In Act.playH b Coin.H Player.p0 := by
  cases m <;> cases a <;> cases b <;> simp [branchPayoff, recommended] <;> norm_num

/-- Every early-signal Nash equilibrium caps player `1` at `5/2`: the `T` branch
opts out (`2`) and the `H` branch pays at most `3`. -/
theorem early_nash_p1_cap :
    ∀ v ∈ earlySignalGame.nashPayoffSet, v Player.p1 ≤ (5 : ℝ) / 2 := by
  rintro v ⟨σ, hN, rfl⟩
  simp only [eu_earlySignalGame, earlyEU, avgFair]
  rw [early_nash_move_T_eq_out hN, branchPayoff_out]
  have hH := branchPayoff_H_p1_le ((σ Player.p0).move Coin.H) ((σ Player.p0).act Coin.H)
    (σ Player.p1 Coin.H)
  linarith

/-- Player `0`'s `H`-branch payoff never exceeds `4`. -/
theorem branchPayoff_H_p0_le (m : Move) (a0 a1 : Act) :
    branchPayoff m a0 a1 Coin.H Player.p0 ≤ 4 := by
  cases m with
  | In => simp only [branchPayoff, recommended]; split_ifs <;> norm_num
  | Out => simp only [branchPayoff_out]; norm_num

/-- The early-signal cap profile that attains player-`1` value `5/2`: player `0`
enters and coordinates at `H`, opts out at `T`; player `1` follows the coin. -/
def earlyCapProfile : earlySignalGame.Profile := fun i => match i with
  | Player.p0 => ({ move := fun c => match c with | Coin.H => Move.In | Coin.T => Move.Out,
                    act := recommended } : EarlyP0Strategy)
  | Player.p1 => (recommended : P1Strategy)

theorem earlyCapProfile_p0 : earlyEU earlyCapProfile Player.p0 = 3 := by
  simp only [earlyEU, avgFair, earlyCapProfile, branchPayoff, recommended]; norm_num

theorem earlyCapProfile_p1 : earlyEU earlyCapProfile Player.p1 = (5 : ℝ) / 2 := by
  simp only [earlyEU, avgFair, earlyCapProfile, branchPayoff, recommended]; norm_num

/-- The cap profile is an early-signal Nash equilibrium: entering at `H` (payoff
`4 > 2`) and out at `T` (payoff `2 > 1`) is optimal for player `0`, and player `1`
coordinates where it matters. -/
theorem early_coordinate_isNash : earlySignalGame.IsNash earlyCapProfile := by
  intro who s'
  simp only [eu_earlySignalGame, ge_iff_le]
  match who, s' with
  | Player.p0, s' =>
      rw [earlyCapProfile_p0]
      simp only [earlyEU, avgFair, earlyCapProfile, recommended,
        Function.update_self, Function.update_of_ne (by decide : Player.p1 ≠ Player.p0)]
      have hH := branchPayoff_H_p0_le (s'.move Coin.H) (s'.act Coin.H) Act.playH
      have hT := branchPayoff_T_p0_le (s'.move Coin.T) (s'.act Coin.T) Act.playT
      linarith
  | Player.p1, s' =>
      rw [earlyCapProfile_p1]
      simp only [earlyEU, avgFair, earlyCapProfile, branchPayoff_out, recommended,
        Function.update_self, Function.update_of_ne (by decide : Player.p0 ≠ Player.p1)]
      have h1 := branchPayoff_H_p1_le Move.In Act.playH (s' Coin.H)
      linarith

/-- The early-signal Nash cap `5/2` is attained — so it is tight. -/
theorem early_nash_p1_cap_tight :
    ∃ v ∈ earlySignalGame.nashPayoffSet, v Player.p1 = (5 : ℝ) / 2 := by
  refine ⟨fun i => earlySignalGame.eu earlyCapProfile i,
    ⟨earlyCapProfile, early_coordinate_isNash, rfl⟩, ?_⟩
  simp only [eu_earlySignalGame, earlyCapProfile_p1]

-- `correlatedEu` collapses to the expectation of `earlyEU`/`lateEU` over the
-- recommendation distribution (the games have a deterministic kernel).
theorem correlatedEu_earlySignalGame (μ : PMF earlySignalGame.Profile) (i : Player) :
    earlySignalGame.correlatedEu μ i = expect μ (fun σ => earlyEU σ i) := by
  rw [KernelGame.correlatedEu_eq_expect_eu]; simp only [eu_earlySignalGame]

theorem correlatedEu_lateSignalGame (μ : PMF lateSignalGame.Profile) (i : Player) :
    lateSignalGame.correlatedEu μ i = expect μ (fun σ => lateEU σ i) := by
  rw [KernelGame.correlatedEu_eq_expect_eu]; simp only [eu_lateSignalGame]

/-- The correlated EU after a recommendation-dependent deviation by `who` is the
expectation of the per-recommendation deviated payoff (a `KernelGame`-generic
fact specialized to `earlyEU`). -/
theorem correlatedEu_unilat_early (μ : PMF earlySignalGame.Profile) (who : Player)
    (dev : earlySignalGame.Strategy who → earlySignalGame.Strategy who) :
    earlySignalGame.correlatedEu
        (earlySignalGame.unilateralDeviationDistribution μ who dev) who
      = expect μ (fun σ => earlyEU (Function.update σ who (dev (σ who))) who) := by
  rw [KernelGame.correlatedEu_unilateralDeviationDistribution_eq_expect_update]
  simp only [eu_earlySignalGame]; rfl

/-- The correlated EU after a constant deviation by `who`, specialized to
`earlyEU`. -/
theorem correlatedEu_const_early (μ : PMF earlySignalGame.Profile) (who : Player)
    (s' : earlySignalGame.Strategy who) :
    earlySignalGame.correlatedEu
        (earlySignalGame.constantDeviationDistribution μ who s') who
      = expect μ (fun σ => earlyEU (Function.update σ who s') who) := by
  rw [KernelGame.correlatedEu_constantDeviationDistribution_eq_expect_update]
  simp only [eu_earlySignalGame]; rfl

/-- **Nash separation.** Player `1` realizes value `3` at a late-signal Nash
equilibrium, but no early-signal Nash equilibrium gives player `1` value `3`. -/
theorem late_not_covered_by_early_nash :
    (∃ v ∈ lateSignalGame.nashPayoffSet, v Player.p1 = 3) ∧
    (∀ v ∈ earlySignalGame.nashPayoffSet, v Player.p1 ≠ 3) := by
  refine ⟨late_nash_p1_three, ?_⟩
  intro v hv hv3
  have hcap := early_nash_p1_cap v hv
  rw [hv3] at hcap
  norm_num at hcap

/-- `3` is a late-signal correlated-equilibrium value for player `1` (the pure
Nash profile is a correlated equilibrium). -/
theorem late_correlated_p1_three :
    ∃ v ∈ lateSignalGame.correlatedPayoffSet, v Player.p1 = 3 := by
  refine ⟨fun i => lateSignalGame.correlatedEu (PMF.pure lateCoordinateProfile) i,
    ⟨PMF.pure lateCoordinateProfile,
      KernelGame.nash_pure_isCorrelatedEq late_coordinate_isNash, rfl⟩, ?_⟩
  simp only [correlatedEu_lateSignalGame, expect_pure, lateEU_coordinate_p1]

/-- Pointwise budget inequality behind the CE cap: per recommendation, player
`1`'s value is dominated by `5/2` plus player `0`'s gain from `forceOutAtT`.
Combines `Hp1 ≤ 3` with `Tp1 + Tp0 ≤ 4`. -/
theorem early_p1_le_pointwise (σ : earlySignalGame.Profile) :
    earlyEU σ Player.p1 ≤ (5 : ℝ) / 2 +
      (earlyEU (Function.update σ Player.p0 (forceOutAtT (σ Player.p0))) Player.p0
        - earlyEU σ Player.p0) := by
  simp only [earlyEU, avgFair, forceOutAtT, Function.update_self,
    Function.update_of_ne (by decide : Player.p1 ≠ Player.p0)]
  have hH := branchPayoff_H_p1_le ((σ Player.p0).move Coin.H) ((σ Player.p0).act Coin.H)
    (σ Player.p1 Coin.H)
  have hT := branchPayoff_T_sum_le ((σ Player.p0).move Coin.T) ((σ Player.p0).act Coin.T)
    (σ Player.p1 Coin.T)
  have hout : branchPayoff Move.Out ((σ Player.p0).act Coin.T) (σ Player.p1 Coin.T)
      Coin.T Player.p0 = 2 := by simp [branchPayoff]
  rw [hout]
  linarith

/-- Every early-signal correlated equilibrium caps player `1` at `5/2`. The
recommendation-dependent deviation `forceOutAtT` forces player `0` out of the bad
branch in expectation. -/
theorem early_correlated_p1_cap :
    ∀ v ∈ earlySignalGame.correlatedPayoffSet, v Player.p1 ≤ (5 : ℝ) / 2 := by
  rintro v ⟨μ, hCE, rfl⟩
  change earlySignalGame.correlatedEu μ Player.p1 ≤ (5 : ℝ) / 2
  have hCEdev := hCE Player.p0 forceOutAtT
  rw [correlatedEu_unilat_early, correlatedEu_earlySignalGame] at hCEdev
  rw [correlatedEu_earlySignalGame]
  calc expect μ (fun σ => earlyEU σ Player.p1)
      ≤ expect μ (fun σ => (5 : ℝ) / 2 +
          (earlyEU (Function.update σ Player.p0 (forceOutAtT (σ Player.p0))) Player.p0
            - earlyEU σ Player.p0)) := by
        apply expect_mono
        intro σ; exact early_p1_le_pointwise σ
    _ = (5 : ℝ) / 2 +
          (expect μ (fun σ => earlyEU (Function.update σ Player.p0
              (forceOutAtT (σ Player.p0))) Player.p0)
            - expect μ (fun σ => earlyEU σ Player.p0)) := by
        rw [expect_add, expect_const, expect_sub]
    _ ≤ (5 : ℝ) / 2 := by linarith [hCEdev]

/-- The early-signal correlated cap `5/2` is attained (the Nash cap profile, as a
pure correlated equilibrium) — so it is tight. -/
theorem early_correlated_p1_cap_tight :
    ∃ v ∈ earlySignalGame.correlatedPayoffSet, v Player.p1 = (5 : ℝ) / 2 := by
  refine ⟨fun i => earlySignalGame.correlatedEu (PMF.pure earlyCapProfile) i,
    ⟨PMF.pure earlyCapProfile,
      KernelGame.nash_pure_isCorrelatedEq early_coordinate_isNash, rfl⟩, ?_⟩
  simp only [correlatedEu_earlySignalGame, expect_pure, earlyCapProfile_p1]

/-- **Correlated-equilibrium separation.** Player `1` realizes value `3` at a
late-signal correlated equilibrium, but no early-signal correlated equilibrium
gives player `1` value `3`. -/
theorem late_not_covered_by_early_correlated :
    (∃ v ∈ lateSignalGame.correlatedPayoffSet, v Player.p1 = 3) ∧
    (∀ v ∈ earlySignalGame.correlatedPayoffSet, v Player.p1 ≠ 3) := by
  refine ⟨late_correlated_p1_three, ?_⟩
  intro v hv hv3
  have hcap := early_correlated_p1_cap v hv
  rw [hv3] at hcap
  norm_num at hcap

/-! ## Single-agent contrast (Blackwell)

For a single decision-maker the multi-agent effect reverses: earlier information
is weakly valuable.  With the same numbers (`In` pays `4` at `H`, `1` at `T`;
`Out` pays `2`), seeing the coin first lets the agent pick per branch
(`(max 4 2 + max 1 2)/2 = 3`); deciding blind gives `max((4+1)/2, 2) = 5/2`.
This is the Blackwell monotonicity that the two-player example breaks; the `3` the
lone agent grabs is exactly the deviation that destroys player `1`'s equilibrium. -/

/-- The single-agent decision payoff. -/
def dmPayoff (m : Move) (c : Coin) : ℝ :=
  match m, c with
  | Move.Out, _ => 2
  | Move.In, Coin.H => 4
  | Move.In, Coin.T => 1

/-- Early single-agent value: choose the move per coin, then average. -/
noncomputable def earlyDMValue : ℝ :=
  (max (dmPayoff Move.In Coin.H) (dmPayoff Move.Out Coin.H)
    + max (dmPayoff Move.In Coin.T) (dmPayoff Move.Out Coin.T)) / 2

/-- Late single-agent value: choose one coin-blind move, then average. -/
noncomputable def lateDMValue : ℝ :=
  max ((dmPayoff Move.In Coin.H + dmPayoff Move.In Coin.T) / 2)
      ((dmPayoff Move.Out Coin.H + dmPayoff Move.Out Coin.T) / 2)

/-- **Single-agent Blackwell contrast.** Earlier information is weakly valuable to
a lone decision-maker (`3 ≥ 5/2`). -/
theorem single_agent_early_ge_late : earlyDMValue ≥ lateDMValue := by
  simp only [earlyDMValue, lateDMValue, dmPayoff]
  norm_num

/-! ## Coarse-correlated equilibrium: cap `11/4` and `CE ⊊ CCE`

CCE permits only constant deviations, so it cannot express `forceOutAtT`; player
`0` can be induced to enter at `T`, lifting player `1` above the CE cap `5/2` to
`11/4`.  This is tight: the binding constant deviation `deviateInHOutT` caps every
early CCE at `11/4`, which is still below the late value `3`. -/

/-- Recommendation `A`: player `0` enters and coordinates everywhere; player `1`
follows the coin. -/
def earlyA : earlySignalGame.Profile := fun i => match i with
  | Player.p0 => ({ move := fun _ => Move.In, act := recommended } : EarlyP0Strategy)
  | Player.p1 => (recommended : P1Strategy)

/-- Recommendation `B`: player `0` opts out at `H` and coordinates at `T`; player
`1` plays `playT` (mismatching at `H`, where player `0` is out, harmlessly). -/
def earlyB : earlySignalGame.Profile := fun i => match i with
  | Player.p0 => ({ move := fun c => match c with | Coin.H => Move.Out | Coin.T => Move.In,
                    act := recommended } : EarlyP0Strategy)
  | Player.p1 => ((fun _ => Act.playT) : P1Strategy)

/-- The coarse-correlated witness: the fair mixture of `A` and `B`. -/
noncomputable def earlyCCEWitness : PMF earlySignalGame.Profile :=
  (PMF.uniformOfFintype Bool).bind (fun b => PMF.pure (bif b then earlyA else earlyB))

theorem expect_earlyCCEWitness (f : earlySignalGame.Profile → ℝ) :
    expect earlyCCEWitness f = (f earlyA + f earlyB) / 2 := by
  rw [earlyCCEWitness, expect_bind]
  simp only [expect_pure, expect_eq_sum, Fintype.sum_bool, cond_true, cond_false,
    PMF.uniformOfFintype_apply]
  norm_num
  ring

/-- Player `1`'s value `3` at `A` and `5/2` at `B`, averaging to `11/4`. -/
theorem earlyA_p1 : earlyEU earlyA Player.p1 = 3 := by
  simp only [earlyEU, avgFair, earlyA, branchPayoff, recommended]; norm_num

theorem earlyB_p1 : earlyEU earlyB Player.p1 = (5 : ℝ) / 2 := by
  simp only [earlyEU, avgFair, earlyB, branchPayoff, recommended]; norm_num

/-- Player `0`'s value `5/2` at `A` and `3/2` at `B`. -/
theorem earlyA_p0 : earlyEU earlyA Player.p0 = (5 : ℝ) / 2 := by
  simp only [earlyEU, avgFair, earlyA, branchPayoff, recommended]; norm_num

theorem earlyB_p0 : earlyEU earlyB Player.p0 = (3 : ℝ) / 2 := by
  simp only [earlyEU, avgFair, earlyB, branchPayoff, recommended]; norm_num

theorem earlyCCE_p1_value :
    earlySignalGame.correlatedEu earlyCCEWitness Player.p1 = (11 : ℝ) / 4 := by
  rw [correlatedEu_earlySignalGame, expect_earlyCCEWitness, earlyA_p1, earlyB_p1]
  norm_num

/-- The witness is a coarse correlated equilibrium. Player `0`'s best constant
deviation cannot beat `4 = u₀(A) + u₀(B)` (HH-bound `≤ 4` plus two `T`-terms
`≤ 2`); player `1`'s cannot beat `11/2` (`Hp1 ≤ 3` plus two `Tp1 ≤ 3`). -/
theorem earlyCCEWitness_isCCE : earlySignalGame.IsCoarseCorrelatedEq earlyCCEWitness := by
  intro who s'
  rw [correlatedEu_const_early, correlatedEu_earlySignalGame,
      expect_earlyCCEWitness, expect_earlyCCEWitness, ge_iff_le]
  match who, s' with
  | Player.p0, s' =>
      rw [earlyA_p0, earlyB_p0]
      simp only [earlyEU, avgFair, earlyA, earlyB, recommended,
        Function.update_self, Function.update_of_ne (by decide : Player.p1 ≠ Player.p0)]
      have h1 := branchPayoff_HH_p0_le (s'.move Coin.H) (s'.act Coin.H)
      have h2 := branchPayoff_T_p0_le (s'.move Coin.T) (s'.act Coin.T) Act.playT
      linarith
  | Player.p1, s' =>
      rw [earlyA_p1, earlyB_p1]
      simp only [earlyEU, avgFair, earlyA, earlyB, recommended, branchPayoff_out,
        Function.update_self, Function.update_of_ne (by decide : Player.p0 ≠ Player.p1)]
      have h1 := branchPayoff_H_p1_le Move.In Act.playH (s' Coin.H)
      have h2 := branchPayoff_T_p1_le Move.In Act.playT (s' Coin.T)
      linarith

/-- The constant deviation behind the CCE cap: enter and coordinate (`playH`) at
`H`, opt out at `T`.  Against the witness it is exactly indifferent. -/
def deviateInHOutT : EarlyP0Strategy where
  move := fun c => match c with | Coin.H => Move.In | Coin.T => Move.Out
  act := fun _ => Act.playH

/-- Pointwise certificate for the CCE cap: per recommendation, player `1`'s value
is dominated by `11/4` plus half of player `0`'s gain from `deviateInHOutT`.
Combines the per-branch certificates `2u₁+u₀ ≤ 6+(deviation gain)` at `H` and
`2u₁+u₀ ≤ 7` at `T`; the multiplier is `1/2`. -/
theorem early_p1_le_pointwise_cce (σ : earlySignalGame.Profile) :
    earlyEU σ Player.p1 ≤ (11 : ℝ) / 4 +
      (1 / 2) * (earlyEU (Function.update σ Player.p0 deviateInHOutT) Player.p0
        - earlyEU σ Player.p0) := by
  simp only [earlyEU, avgFair, deviateInHOutT, branchPayoff_out, Function.update_self,
    Function.update_of_ne (by decide : Player.p1 ≠ Player.p0)]
  have hH := branchPayoff_H_cce_bound ((σ Player.p0).move Coin.H) ((σ Player.p0).act Coin.H)
    (σ Player.p1 Coin.H)
  have hT := branchPayoff_T_cce_bound ((σ Player.p0).move Coin.T) ((σ Player.p0).act Coin.T)
    (σ Player.p1 Coin.T)
  linarith

/-- **Coarse-correlated cap.** Every early-signal coarse correlated equilibrium
caps player `1` at `11/4`.  Player `0`'s constant deviation `deviateInHOutT`
forces the bound in expectation. -/
theorem early_coarseCorrelated_p1_cap :
    ∀ v ∈ earlySignalGame.coarseCorrelatedPayoffSet, v Player.p1 ≤ (11 : ℝ) / 4 := by
  rintro v ⟨μ, hCCE, rfl⟩
  change earlySignalGame.correlatedEu μ Player.p1 ≤ (11 : ℝ) / 4
  have hCCEdev := hCCE Player.p0 deviateInHOutT
  rw [correlatedEu_const_early, correlatedEu_earlySignalGame] at hCCEdev
  rw [correlatedEu_earlySignalGame]
  calc expect μ (fun σ => earlyEU σ Player.p1)
      ≤ expect μ (fun σ => (11 : ℝ) / 4 +
          (1 / 2) * (earlyEU (Function.update σ Player.p0 deviateInHOutT) Player.p0
            - earlyEU σ Player.p0)) := by
        apply expect_mono
        intro σ; exact early_p1_le_pointwise_cce σ
    _ = (11 : ℝ) / 4 +
          (1 / 2) * (expect μ (fun σ => earlyEU (Function.update σ Player.p0
              deviateInHOutT) Player.p0)
            - expect μ (fun σ => earlyEU σ Player.p0)) := by
        rw [expect_add, expect_const, expect_const_mul, expect_sub]
    _ ≤ (11 : ℝ) / 4 := by linarith [hCCEdev]

/-- `3` is a late-signal coarse-correlated value for player `1`. -/
theorem late_coarseCorrelated_p1_three :
    ∃ v ∈ lateSignalGame.coarseCorrelatedPayoffSet, v Player.p1 = 3 := by
  refine ⟨fun i => lateSignalGame.correlatedEu (PMF.pure lateCoordinateProfile) i,
    ⟨PMF.pure lateCoordinateProfile,
      KernelGame.nash_pure_isCoarseCorrelatedEq late_coordinate_isNash, rfl⟩, ?_⟩
  simp only [correlatedEu_lateSignalGame, expect_pure, lateEU_coordinate_p1]

/-- **Coarse-correlated separation.** Player `1` realizes value `3` at a
late-signal coarse correlated equilibrium, but no early-signal coarse correlated
equilibrium reaches `3` (the cap `11/4 < 3`).  The timing separation survives even
under coarse correlation. -/
theorem late_not_covered_by_early_coarseCorrelated :
    (∃ v ∈ lateSignalGame.coarseCorrelatedPayoffSet, v Player.p1 = 3) ∧
    (∀ v ∈ earlySignalGame.coarseCorrelatedPayoffSet, v Player.p1 ≠ 3) := by
  refine ⟨late_coarseCorrelated_p1_three, ?_⟩
  intro v hv hv3
  have hcap := early_coarseCorrelated_p1_cap v hv
  rw [hv3] at hcap
  norm_num at hcap

/-- Player `1`'s value at the coarse-correlated witness, `11/4`, exceeds the
correlated-equilibrium cap `5/2`. -/
theorem earlyCCE_p1_value_gt_cap :
    (5 : ℝ) / 2 < earlySignalGame.correlatedEu earlyCCEWitness Player.p1 := by
  rw [earlyCCE_p1_value]; norm_num

/-- **Correlated payoff set ⊊ coarse-correlated payoff set on the early game.**
Every correlated equilibrium is a coarse one (`⊆`), and the inclusion is strict:
the witness payoff vector lies in the coarse-correlated set (player-`1` value
`11/4`, realized by a CCE) but not in the correlated set (every correlated
equilibrium caps player `1` at `5/2`).  This is the finite normal-form witness
that coarse correlation can strictly beat correlation when an early signal would
otherwise let a player condition an irreversible move. -/
theorem early_correlatedPayoffSet_ssub_coarse :
    earlySignalGame.correlatedPayoffSet ⊂ earlySignalGame.coarseCorrelatedPayoffSet := by
  have hsub : earlySignalGame.correlatedPayoffSet ⊆
      earlySignalGame.coarseCorrelatedPayoffSet := by
    rintro v ⟨μ, hCE, rfl⟩
    exact ⟨μ, hCE.toCoarseCorrelatedEq, rfl⟩
  rw [Set.ssubset_iff_of_subset hsub]
  refine ⟨fun i => earlySignalGame.correlatedEu earlyCCEWitness i,
    ⟨earlyCCEWitness, earlyCCEWitness_isCCE, rfl⟩, ?_⟩
  intro hmem
  have hcap : earlySignalGame.correlatedEu earlyCCEWitness Player.p1 ≤ (5 : ℝ) / 2 :=
    early_correlated_p1_cap _ hmem
  exact absurd hcap (not_le.mpr earlyCCE_p1_value_gt_cap)

end SignalTiming

end GameTheory
