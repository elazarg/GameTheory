/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.Transform.ActionLegality.BehaviorTransfer
import Math.PMFProduct.Update

/-!
# A padded uniform equilibrium payoff with no legal witness

`ActionLegalityDisintegration.lean` proves the padding transfer only under a
label-blindness hypothesis on the background profile, and records the
unconditional direction — an arbitrary witness of
`(G.normalizedGame Legal hLegal).IsUniformEquilibriumPayoff s₀ v` should yield
`G.IsLegalUniformEquilibriumPayoff Legal s₀ v` — as open.  This file refutes
that direction with an explicit three-state, two-player, three-action system.

## The mechanism

Padding makes every action available everywhere and gives an illegal action
the stage data of a legal one, but histories still record the **raw** label.
Two raw labels with the same normalization are therefore a public coin that
each player half-controls.  Playing them at a state whose transition ignores
actions costs nothing and publishes the XOR of the two private bits, which
neither player can bias alone.  A legal profile has no such coin: on the live
path its history is forced, so the two players' survival probabilities
multiply, and the always-continue deviation collects a single factor.

## The system

States `lottery`, `decision`, `dead`; actions `stay`, `dupe`, `quit`; two
players.  Only `stay` is legal at `lottery` and only `dupe` is illegal at
`decision`.  Reward `1` off `dead` and `0` at `dead`, independent of actions.
`lottery` always moves to `decision`; `decision` stays iff neither player
quits; `dead` absorbs.

The question's minimal system has two states.  Three are needed here because
`normalizeAct` retracts an illegal action onto `Classical.choose (hLegal s i)`
— an *opaque* legal action, not a designated one — so the duplicate fiber has
to sit at a state where the transition ignores actions (`lottery`, whose legal
set is the singleton `{stay}`), and quitting has to happen at a separate state
(`decision`).  With one live state the padded game's `dupe` might normalize to
`quit` and the lottery would kill instead of signalling.

## Main definitions

* `PaddedLotterySeparation.sepGame` / `SepLegal` — the system and its legality
  predicate
* `PaddedLotterySeparation.paddedGame` — its `normalizedGame` padding
* `PaddedLotterySeparation.xorProfile` — the jointly controlled lottery
* `StochasticGame.stateExpectation` / `stepExpectation` — occupation
  bookkeeping for a game whose stage payoff depends only on the state

## Main results

* `PaddedLotterySeparation.not_isLegalUniformEquilibriumPayoff_half` — no legal
  profile witnesses `(1/2, 1/2)` in the original game
* `PaddedLotterySeparation.isUniformEquilibriumPayoff_paddedGame_half` — the
  padded game does attain it
* `PaddedLotterySeparation.not_forall_isLegalUniformEquilibriumPayoff_of_padded`
  — the unconditional padding transfer is false
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace StochasticGame

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct

-- ============================================================================
-- Occupation bookkeeping for state-determined stage payoffs
-- ============================================================================

section StateValue

variable {ι : Type} [Fintype ι]

/-- Expected value of a state function at decision epoch `t`: for the indicator
of "not absorbed", this is the probability that play is still alive. -/
def stateExpectation (Q : StochasticGame ι) (av : Q.State → ℝ)
    (σ : Q.BehaviorProfile) (s₀ : Q.State) (t : ℕ) : ℝ :=
  expect (Q.histDist σ s₀ t) fun h => av h.2

/-- Expected value of `av` at the state one stage after history `h`. -/
def stepExpectation (Q : StochasticGame ι) (av : Q.State → ℝ)
    (σ : Q.BehaviorProfile) {t : ℕ} (h : Q.Hist t) : ℝ :=
  expect (Q.stageActionDist σ h) fun a => expect (Q.transition h.2 a) av

/-- At epoch zero the state value is just the initial state's value. -/
@[simp] theorem stateExpectation_zero (Q : StochasticGame ι) (av : Q.State → ℝ)
    (σ : Q.BehaviorProfile) (s₀ : Q.State) :
    Q.stateExpectation av σ s₀ 0 = av s₀ := by
  simp [stateExpectation, emptyHist]

/-- One-step recursion: the state value at epoch `t + 1` is the expected
one-step value over the epoch-`t` histories. -/
theorem stateExpectation_succ (Q : StochasticGame ι) [Finite Q.State]
    [∀ i, Finite (Q.Act i)] (av : Q.State → ℝ) (σ : Q.BehaviorProfile)
    (s₀ : Q.State) (t : ℕ) :
    Q.stateExpectation av σ s₀ (t + 1) =
      expect (Q.histDist σ s₀ t) fun h => Q.stepExpectation av σ h := by
  unfold stateExpectation stepExpectation
  rw [histDist_succ, expect_bind]
  refine congrArg (expect (Q.histDist σ s₀ t)) (funext fun h => ?_)
  rw [expect_bind]
  refine congrArg (expect (Q.stageActionDist σ h)) (funext fun a => ?_)
  rw [expect_bind]
  simp

/-- Expanding the epoch-one history distribution: draw the first joint action
and the successor state. -/
theorem expect_histDist_one (Q : StochasticGame ι) [Finite Q.State]
    [∀ i, Finite (Q.Act i)] (σ : Q.BehaviorProfile) (s₀ : Q.State)
    (F : Q.Hist 1 → ℝ) :
    expect (Q.histDist σ s₀ 1) F =
      expect (Q.stageActionDist σ (Q.emptyHist s₀)) fun a =>
        expect (Q.transition s₀ a) fun s' =>
          F (Fin.snoc (Q.emptyHist s₀).1 (s₀, a), s') := by
  rw [histDist_succ, histDist_zero, PMF.pure_bind, expect_bind]
  refine congrArg (expect (Q.stageActionDist σ (Q.emptyHist s₀))) (funext fun a => ?_)
  rw [expect_bind]
  simp [emptyHist]

/-- If the stage payoff depends only on the current state, the expected total
payoff is the sum of the state values over the horizon. -/
theorem expect_totalPayoff_eq_sum_stateExpectation (Q : StochasticGame ι)
    [Finite Q.State] [∀ i, Finite (Q.Act i)] (av : Q.State → ℝ)
    (hpay : ∀ s a who, Q.stagePayoff s a who = av s) (σ : Q.BehaviorProfile)
    (s₀ : Q.State) (who : ι) (T : ℕ) :
    expect (Q.histDist σ s₀ T) (fun h => Q.totalPayoff who h) =
      ∑ t ∈ Finset.range T, Q.stateExpectation av σ s₀ t := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [expect_totalPayoff_succ, ih, Finset.sum_range_succ]
    refine congrArg _ ?_
    unfold stateExpectation
    refine congrArg (expect (Q.histDist σ s₀ T)) (funext fun h => ?_)
    simp [stageEUAt, hpay]

/-- The finite-horizon average payoff of a state-determined stage payoff is the
average of the state values. -/
theorem finiteAveragePayoff_eq_sum_stateExpectation (Q : StochasticGame ι)
    [Finite Q.State] [∀ i, Finite (Q.Act i)] (av : Q.State → ℝ)
    (hpay : ∀ s a who, Q.stagePayoff s a who = av s) (σ : Q.BehaviorProfile)
    (s₀ : Q.State) (who : ι) (T : ℕ) :
    Q.finiteAveragePayoff s₀ T σ who =
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T, Q.stateExpectation av σ s₀ t := by
  unfold finiteAveragePayoff
  rw [Q.expect_totalPayoff_eq_sum_stateExpectation av hpay σ s₀ who T]

/-- If every one-step value is bounded by the current state's value, the state
value is nonincreasing in the epoch. -/
theorem stateExpectation_antitone (Q : StochasticGame ι) [Finite Q.State]
    [∀ i, Finite (Q.Act i)] (av : Q.State → ℝ) (σ : Q.BehaviorProfile)
    (s₀ : Q.State)
    (hstep : ∀ (t : ℕ) (h : Q.Hist t), Q.stepExpectation av σ h ≤ av h.2)
    {m n : ℕ} (hmn : m ≤ n) :
    Q.stateExpectation av σ s₀ n ≤ Q.stateExpectation av σ s₀ m := by
  induction n with
  | zero => simp_all
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hlt | hge
    · have hmn' : m ≤ n := Nat.lt_succ_iff.mp hlt
      refine le_trans ?_ (ih hmn')
      rw [Q.stateExpectation_succ av σ s₀ n]
      exact expect_mono _ _ _ fun h => hstep n h
    · have : m = n + 1 := le_antisymm hmn hge
      subst this
      exact le_rfl

end StateValue

end StochasticGame

-- ============================================================================
-- The separating system
-- ============================================================================

namespace PaddedLotterySeparation

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open GameTheory.StochasticGame

/-- The three states: the lottery stage, the quitting stage, and the absorbing
zero-payoff state. -/
inductive Site
  | lottery
  | decision
  | dead
  deriving DecidableEq, Fintype

/-- The three actions: the reduced continuation label, its payoff-irrelevant
duplicate, and the quitting action. -/
inductive Label
  | stay
  | dupe
  | quit
  deriving DecidableEq, Fintype

/-- Indicator of "not absorbed", which is also the stage reward. -/
def aliveVal : Site → ℝ := fun s => if s = Site.dead then 0 else 1

/-- Indicator of "does not quit". -/
def keepVal : Label → ℝ := fun l => if l = Label.quit then 0 else 1

/-- The lottery state is alive. -/
@[simp] theorem aliveVal_lottery : aliveVal Site.lottery = 1 := rfl

/-- The decision state is alive. -/
@[simp] theorem aliveVal_decision : aliveVal Site.decision = 1 := rfl

/-- The absorbing state is not alive. -/
@[simp] theorem aliveVal_dead : aliveVal Site.dead = 0 := rfl

/-- Continuing carries full continuation weight. -/
@[simp] theorem keepVal_stay : keepVal Label.stay = 1 := rfl

/-- Quitting carries zero continuation weight. -/
@[simp] theorem keepVal_quit : keepVal Label.quit = 0 := rfl

/-- `keepVal` is an indicator, hence between `0` and `1`. -/
theorem keepVal_mem_unitInterval (l : Label) : 0 ≤ keepVal l ∧ keepVal l ≤ 1 := by
  cases l <;> simp [keepVal]

/-- Any label other than `quit` carries full continuation weight. -/
theorem keepVal_of_ne_quit {l : Label} (hl : l ≠ Label.quit) : keepVal l = 1 := by
  simp [keepVal, hl]

/-- The transition kernel: `lottery` always moves on, `decision` survives iff
neither player quits, `dead` absorbs. -/
def sepTransition : Site → (Bool → Label) → PMF Site
  | Site.lottery, _ => PMF.pure Site.decision
  | Site.decision, a =>
      if a false = Label.quit ∨ a true = Label.quit then PMF.pure Site.dead
      else PMF.pure Site.decision
  | Site.dead, _ => PMF.pure Site.dead

/-- `lottery` moves on to `decision` whatever the players do. -/
@[simp] theorem sepTransition_lottery (a : Bool → Label) :
    sepTransition Site.lottery a = PMF.pure Site.decision := rfl

/-- `dead` absorbs. -/
@[simp] theorem sepTransition_dead (a : Bool → Label) :
    sepTransition Site.dead a = PMF.pure Site.dead := rfl

/-- At `decision` the state survives exactly when neither player quits. -/
theorem sepTransition_decision (a : Bool → Label) :
    sepTransition Site.decision a =
      if a false = Label.quit ∨ a true = Label.quit then PMF.pure Site.dead
      else PMF.pure Site.decision := rfl

/-- The separating stochastic game: two players, three states, three actions,
and a stage reward that only records whether play is still alive. -/
@[reducible] def sepGame : StochasticGame Bool where
  State := Site
  Act := fun _ => Label
  stagePayoff := fun s _ _ => aliveVal s
  transition := sepTransition
  discount := 0
  discount_nonneg := le_rfl
  discount_lt_one := by norm_num

/-- Legality: only the reduced label is legal at `lottery`, only the duplicate
is illegal at `decision`, and everything is legal once absorbed. -/
def SepLegal : Site → Bool → Label → Prop
  | Site.lottery, _, l => l = Label.stay
  | Site.decision, _, l => l ≠ Label.dupe
  | Site.dead, _, _ => True

/-- Every state has a legal action for every player: `stay` always is one. -/
theorem sepLegal_nonempty : ∀ (s : Site) (i : Bool), ∃ l : Label, SepLegal s i l := by
  intro s i
  exact ⟨Label.stay, by cases s <;> simp [SepLegal]⟩

/-- `stay` is legal everywhere. -/
theorem sepLegal_stay (s : Site) (i : Bool) : SepLegal s i Label.stay := by
  cases s <;> simp [SepLegal]

/-- The padded game: every action legal everywhere, illegal actions carrying
the stage data of `normalizeAct`'s fallback. -/
@[reducible] def paddedGame : StochasticGame Bool :=
  sepGame.normalizedGame SepLegal sepLegal_nonempty

/-- The label a single component is normalized to at `decision`: itself when
legal, and otherwise the opaque fallback `normalizeAct` chooses. -/
def padLabel (i : Bool) (l : Label) : Label :=
  sepGame.normalizeAct SepLegal sepLegal_nonempty Site.decision (fun _ => l) i

/-- `normalizeAct` at `decision` is componentwise `padLabel`. -/
theorem normalizeAct_decision (a : Bool → Label) (i : Bool) :
    sepGame.normalizeAct SepLegal sepLegal_nonempty Site.decision a i =
      padLabel i (a i) := rfl

/-- The padded game's continuation weight for a single label at `decision`. -/
def padKeep (i : Bool) (l : Label) : ℝ := keepVal (padLabel i l)

/-- A legal label is normalized to itself. -/
theorem padLabel_of_legal (i : Bool) (l : Label) (hl : SepLegal Site.decision i l) :
    padLabel i l = l := by
  unfold padLabel normalizeAct
  rw [if_pos hl]

/-- Continuing is legal at `decision`, so padding leaves its weight alone. -/
@[simp] theorem padKeep_stay (i : Bool) : padKeep i Label.stay = 1 := by
  rw [padKeep, padLabel_of_legal i Label.stay (sepLegal_stay Site.decision i)]
  simp

/-- Quitting is legal at `decision`, so padding leaves its weight alone. -/
@[simp] theorem padKeep_quit (i : Bool) : padKeep i Label.quit = 0 := by
  have hq : SepLegal Site.decision i Label.quit := by simp [SepLegal]
  rw [padKeep, padLabel_of_legal i Label.quit hq]
  simp

/-- The fallback is unknown, but `padKeep` is still an indicator. -/
theorem padKeep_mem_unitInterval (i : Bool) (l : Label) :
    0 ≤ padKeep i l ∧ padKeep i l ≤ 1 := keepVal_mem_unitInterval _

-- ============================================================================
-- Two-coordinate product expectations
-- ============================================================================

/-- Fubini for a two-coordinate independent product of `Label`-valued draws. -/
theorem expect_pmfPi_bool (m : Bool → PMF Label) (f : (Bool → Label) → ℝ) :
    expect (pmfPi (A := fun _ : Bool => Label) m) f =
      expect (m false) fun x => expect (m true) fun y =>
        f (fun c => if c then y else x) := by
  classical
  have hfalse : Function.update m false (m false) = m :=
    Function.update_eq_self false m
  rw [← hfalse, pmfPi_update_bind, expect_bind]
  refine congrArg (expect (m false)) (funext fun x => ?_)
  have htrue : Function.update (Function.update m false (PMF.pure x)) true (m true) =
      Function.update m false (PMF.pure x) := by
    funext c; cases c <;> simp
  rw [← htrue, pmfPi_update_bind, expect_bind]
  refine congrArg (expect (m true)) (funext fun y => ?_)
  have hpure : Function.update (Function.update m false (PMF.pure x)) true (PMF.pure y) =
      fun c => PMF.pure (if c then y else x) := by
    funext c; cases c <;> simp
  rw [hpure, pmfPi_pure, expect_pure]

/-- A product integrand factorizes over an independent two-coordinate product. -/
theorem expect_pmfPi_mul (m : Bool → PMF Label) (w : Bool → Label → ℝ) :
    expect (pmfPi (A := fun _ : Bool => Label) m)
        (fun a => w false (a false) * w true (a true)) =
      expect (m false) (w false) * expect (m true) (w true) := by
  rw [expect_pmfPi_bool]
  have hinner : ∀ x : Label,
      expect (m true) (fun y => w false x * w true y) =
        w false x * expect (m true) (w true) := fun x => expect_const_mul _ _ _
  simp only [Bool.false_eq_true, if_false, if_true, hinner]
  have hcomm : (fun x => w false x * expect (m true) (w true)) =
      fun x => expect (m true) (w true) * w false x := by
    funext x; ring
  rw [hcomm, expect_const_mul, mul_comm]

/-- An indicator-valued integrand has expectation in `[0, 1]`. -/
theorem expect_unitInterval (μ : PMF Label) (w : Label → ℝ)
    (hw : ∀ l, 0 ≤ w l ∧ w l ≤ 1) : 0 ≤ expect μ w ∧ expect μ w ≤ 1 := by
  refine ⟨expect_nonneg _ _ fun l => (hw l).1, ?_⟩
  calc expect μ w ≤ expect μ (fun _ => 1) := expect_mono _ _ _ fun l => (hw l).2
    _ = 1 := expect_const _ _

-- ============================================================================
-- One-step alive values in both games
-- ============================================================================

/-- In the original game, `lottery` always moves on to `decision`. -/
theorem stepExpectation_sep_lottery (σ : sepGame.BehaviorProfile) {t : ℕ}
    (h : sepGame.Hist t) (hs : h.2 = Site.lottery) :
    sepGame.stepExpectation aliveVal σ h = 1 := by
  have hinner : (fun a : Bool → Label => expect (sepGame.transition h.2 a) aliveVal) =
      fun _ => (1 : ℝ) := by
    funext a; rw [hs]; change expect (sepTransition Site.lottery a) aliveVal = 1; simp
  unfold stepExpectation
  rw [hinner]
  exact expect_const _ _

/-- In the original game, `decision` survives iff neither player quits, so the
one-step alive value is the product of the two players' continuation masses. -/
theorem stepExpectation_sep_decision (σ : sepGame.BehaviorProfile) {t : ℕ}
    (h : sepGame.Hist t) (hs : h.2 = Site.decision) :
    sepGame.stepExpectation aliveVal σ h =
      expect (σ false t h) keepVal * expect (σ true t h) keepVal := by
  have hinner : (fun a : Bool → Label => expect (sepGame.transition h.2 a) aliveVal) =
      fun a : Bool → Label => keepVal (a false) * keepVal (a true) := by
    funext a
    rw [hs]
    change expect (sepTransition Site.decision a) aliveVal = _
    rw [sepTransition_decision]
    split_ifs with hq
    · rcases hq with hq | hq <;> simp [hq]
    · rw [not_or] at hq
      rw [keepVal_of_ne_quit hq.1, keepVal_of_ne_quit hq.2]
      simp
  unfold stepExpectation
  rw [hinner]
  exact expect_pmfPi_mul (fun i => σ i t h) (fun _ => keepVal)

/-- The absorbing state has zero one-step alive value. -/
theorem stepExpectation_sep_dead (σ : sepGame.BehaviorProfile) {t : ℕ}
    (h : sepGame.Hist t) (hs : h.2 = Site.dead) :
    sepGame.stepExpectation aliveVal σ h = 0 := by
  have hinner : (fun a : Bool → Label => expect (sepGame.transition h.2 a) aliveVal) =
      fun _ => (0 : ℝ) := by
    funext a; rw [hs]; change expect (sepTransition Site.dead a) aliveVal = 0; simp
  unfold stepExpectation
  rw [hinner]
  exact expect_const _ _

/-- Padding leaves `lottery` alone: its transition never looked at actions. -/
theorem stepExpectation_padded_lottery (σ : paddedGame.BehaviorProfile) {t : ℕ}
    (h : paddedGame.Hist t) (hs : h.2 = Site.lottery) :
    paddedGame.stepExpectation aliveVal σ h = 1 := by
  have hinner : (fun a : Bool → Label => expect (paddedGame.transition h.2 a) aliveVal) =
      fun _ => (1 : ℝ) := by
    funext a
    rw [hs]
    change expect (sepTransition Site.lottery
      (sepGame.normalizeAct SepLegal sepLegal_nonempty Site.lottery a)) aliveVal = 1
    simp
  unfold stepExpectation
  rw [hinner]
  exact expect_const _ _

/-- At `decision` the padded game's one-step alive value is the product of the
two players' `padKeep` masses. -/
theorem stepExpectation_padded_decision (σ : paddedGame.BehaviorProfile) {t : ℕ}
    (h : paddedGame.Hist t) (hs : h.2 = Site.decision) :
    paddedGame.stepExpectation aliveVal σ h =
      expect (σ false t h) (padKeep false) * expect (σ true t h) (padKeep true) := by
  have hinner : (fun a : Bool → Label => expect (paddedGame.transition h.2 a) aliveVal) =
      fun a : Bool → Label => padKeep false (a false) * padKeep true (a true) := by
    funext a
    rw [hs]
    change expect (sepTransition Site.decision
      (sepGame.normalizeAct SepLegal sepLegal_nonempty Site.decision a)) aliveVal = _
    rw [sepTransition_decision]
    simp only [normalizeAct_decision]
    split_ifs with hq
    · rcases hq with hq | hq <;> simp [padKeep, hq]
    · rw [not_or] at hq
      change expect (PMF.pure Site.decision) aliveVal =
        keepVal (padLabel false (a false)) * keepVal (padLabel true (a true))
      rw [keepVal_of_ne_quit hq.1, keepVal_of_ne_quit hq.2]
      simp
  unfold stepExpectation
  rw [hinner]
  exact expect_pmfPi_mul (fun i => σ i t h) padKeep

/-- The absorbing state has zero one-step alive value in the padded game too. -/
theorem stepExpectation_padded_dead (σ : paddedGame.BehaviorProfile) {t : ℕ}
    (h : paddedGame.Hist t) (hs : h.2 = Site.dead) :
    paddedGame.stepExpectation aliveVal σ h = 0 := by
  have hinner : (fun a : Bool → Label => expect (paddedGame.transition h.2 a) aliveVal) =
      fun _ => (0 : ℝ) := by
    funext a
    rw [hs]
    change expect (sepTransition Site.dead
      (sepGame.normalizeAct SepLegal sepLegal_nonempty Site.dead a)) aliveVal = 0
    simp
  unfold stepExpectation
  rw [hinner]
  exact expect_const _ _

/-- One-step alive values never exceed the current state's alive value, in the
original game. -/
theorem stepExpectation_sep_le (σ : sepGame.BehaviorProfile) {t : ℕ}
    (h : sepGame.Hist t) : sepGame.stepExpectation aliveVal σ h ≤ aliveVal h.2 := by
  rcases hd : h.2 with _ | _ | _
  · rw [stepExpectation_sep_lottery σ h hd]; simp
  · rw [stepExpectation_sep_decision σ h hd]
    have h0 := expect_unitInterval (σ false t h) keepVal keepVal_mem_unitInterval
    have h1 := expect_unitInterval (σ true t h) keepVal keepVal_mem_unitInterval
    simpa using mul_le_one₀ h0.2 h1.1 h1.2
  · rw [stepExpectation_sep_dead σ h hd]; simp

/-- One-step alive values never exceed the current state's alive value, in the
padded game. -/
theorem stepExpectation_padded_le (σ : paddedGame.BehaviorProfile) {t : ℕ}
    (h : paddedGame.Hist t) :
    paddedGame.stepExpectation aliveVal σ h ≤ aliveVal h.2 := by
  rcases hd : h.2 with _ | _ | _
  · rw [stepExpectation_padded_lottery σ h hd]; simp
  · rw [stepExpectation_padded_decision σ h hd]
    have h0 := expect_unitInterval (σ false t h) (padKeep false)
      (padKeep_mem_unitInterval false)
    have h1 := expect_unitInterval (σ true t h) (padKeep true)
      (padKeep_mem_unitInterval true)
    simpa using mul_le_one₀ h0.2 h1.1 h1.2
  · rw [stepExpectation_padded_dead σ h hd]; simp

-- ============================================================================
-- The impossibility half: no legal profile attains `(1/2, 1/2)`
-- ============================================================================

/-- `aliveVal` is an indicator, hence between `0` and `1`. -/
theorem aliveVal_mem_unitInterval (s : Site) : 0 ≤ aliveVal s ∧ aliveVal s ≤ 1 := by
  cases s <;> simp

/-- Alive probabilities lie in `[0, 1]`. -/
theorem stateExpectation_sep_mem (σ : sepGame.BehaviorProfile) (t : ℕ) :
    0 ≤ sepGame.stateExpectation aliveVal σ Site.lottery t ∧
      sepGame.stateExpectation aliveVal σ Site.lottery t ≤ 1 := by
  unfold stateExpectation
  refine ⟨expect_nonneg _ _ fun h => (aliveVal_mem_unitInterval h.2).1, ?_⟩
  calc expect (sepGame.histDist σ Site.lottery t) (fun h => aliveVal h.2)
      ≤ expect (sepGame.histDist σ Site.lottery t) (fun _ => (1 : ℝ)) :=
        expect_mono _ _ _ fun h => (aliveVal_mem_unitInterval h.2).2
    _ = 1 := expect_const _ _

/-- The alive probability is nonincreasing: `dead` absorbs. -/
theorem stateExpectation_sep_antitone (σ : sepGame.BehaviorProfile) {m n : ℕ}
    (hmn : m ≤ n) :
    sepGame.stateExpectation aliveVal σ Site.lottery n ≤
      sepGame.stateExpectation aliveVal σ Site.lottery m :=
  sepGame.stateExpectation_antitone aliveVal σ Site.lottery
    (fun _ h => stepExpectation_sep_le σ h) hmn

/-- The average payoff is the average alive probability. -/
theorem finiteAveragePayoff_sep (σ : sepGame.BehaviorProfile) (who : Bool) (T : ℕ) :
    sepGame.finiteAveragePayoff Site.lottery T σ who =
      (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        sepGame.stateExpectation aliveVal σ Site.lottery t :=
  sepGame.finiteAveragePayoff_eq_sum_stateExpectation aliveVal
    (fun _ _ _ => rfl) σ Site.lottery who T

/-- The unique history at epoch `t` on which a legal profile can still be
alive: `stay` at every stage, `lottery` once and `decision` thereafter. -/
def forcedHist : (t : ℕ) → sepGame.Hist t
  | 0 => sepGame.emptyHist Site.lottery
  | t + 1 =>
      (Fin.snoc (forcedHist t).1 ((forcedHist t).2, fun _ => Label.stay), Site.decision)

/-- **Forcing.**  Under a legal profile the live path carries no information:
every history that has not been absorbed is the forced one.  This is what a
legal profile cannot buy back, and what raw duplicate labels supply. -/
theorem forced_of_mem_support_histDist {σ : sepGame.BehaviorProfile}
    (hσ : sepGame.IsLegalBehaviorProfile SepLegal σ) :
    ∀ (t : ℕ) (h : sepGame.Hist t),
      h ∈ (sepGame.histDist σ Site.lottery t).support → h.2 ≠ Site.dead →
        h = forcedHist t := by
  intro t
  induction t with
  | zero =>
    intro h hh _
    have : h = sepGame.emptyHist Site.lottery := by
      simpa using hh
    simpa [forcedHist] using this
  | succ t ih =>
    intro h' hh' hne
    obtain ⟨h, hh, a, ha, s', hs', rfl⟩ :=
      (sepGame.mem_support_histDist_succ σ Site.lottery t h').mp hh'
    have hjoint : ∀ i, SepLegal h.2 i (a i) :=
      sepGame.jointlyLegal_of_mem_support_stageActionDist SepLegal hσ ha
    have hs'ne : s' ≠ Site.dead := hne
    rcases hd : h.2 with _ | _ | _
    · -- `lottery`: only `stay` is legal, and the successor is `decision`
      rw [hd] at hs' hjoint
      have hstay : a = fun _ => Label.stay := by
        funext i; exact hjoint i
      have hs'eq : s' = Site.decision := by
        have : s' ∈ (PMF.pure Site.decision).support := hs'
        simpa using this
      have hht : h = forcedHist t := ih h hh (by rw [hd]; exact fun hc => Site.noConfusion hc)
      rw [hstay, hs'eq, forcedHist, ← hht, hd]
    · -- `decision`: legality excludes `dupe`, survival excludes `quit`
      rw [hd] at hs' hjoint
      have hnotquit : ∀ i, a i ≠ Label.quit := by
        intro i hqi
        apply hs'ne
        have : s' ∈ (sepTransition Site.decision a).support := hs'
        rw [sepTransition_decision, if_pos (by cases i <;> simp [hqi])] at this
        simpa using this
      have hstay : a = fun _ => Label.stay := by
        funext i
        have h1 : a i ≠ Label.dupe := hjoint i
        have h2 : a i ≠ Label.quit := hnotquit i
        cases hai : a i
        · rfl
        · exact absurd hai h1
        · exact absurd hai h2
      have hs'eq : s' = Site.decision := by
        have : s' ∈ (sepTransition Site.decision a).support := hs'
        rw [sepTransition_decision, if_neg (by rw [hstay]; simp)] at this
        simpa using this
      have hht : h = forcedHist t := ih h hh (by rw [hd]; exact fun hc => Site.noConfusion hc)
      rw [hstay, hs'eq, forcedHist, ← hht, hd]
    · -- `dead` absorbs, so the successor cannot be alive
      exact absurd (by
        have : s' ∈ (sepGame.transition h.2 a).support := hs'
        rw [hd] at this
        simpa using this) hs'ne

/-- The strategy that always plays the reduced continuation label. -/
def alwaysStay (i : Bool) : sepGame.BehaviorStrategy i := fun _ _ => PMF.pure Label.stay

/-- Always continuing is legal. -/
theorem isLegal_alwaysStay (i : Bool) :
    sepGame.IsLegalBehaviorStrategy SepLegal i (alwaysStay i) := by
  intro t h l hl
  have : l = Label.stay := by simpa [alwaysStay] using hl
  rw [this]
  exact sepLegal_stay h.2 i

/-- The profile obtained by switching player `i` to always continuing. -/
def devProfile (σ : sepGame.BehaviorProfile) (i : Bool) : sepGame.BehaviorProfile :=
  Function.update σ i (alwaysStay i)

/-- Switching one player to always continuing keeps the profile legal. -/
theorem isLegal_devProfile {σ : sepGame.BehaviorProfile}
    (hσ : sepGame.IsLegalBehaviorProfile SepLegal σ) (i : Bool) :
    sepGame.IsLegalBehaviorProfile SepLegal (devProfile σ i) :=
  sepGame.isLegalBehaviorProfile_update SepLegal hσ (isLegal_alwaysStay i)

/-- **The product structure.**  One stage's survival probability under any
profile is the product of the two always-continue deviations' survival
probabilities: the players randomize independently and the state survives
only if both continue. -/
theorem stepExpectation_eq_mul_dev (σ : sepGame.BehaviorProfile) {t : ℕ}
    (h : sepGame.Hist t) :
    sepGame.stepExpectation aliveVal σ h =
      sepGame.stepExpectation aliveVal (devProfile σ false) h *
        sepGame.stepExpectation aliveVal (devProfile σ true) h := by
  rcases hd : h.2 with _ | _ | _
  · rw [stepExpectation_sep_lottery σ h hd, stepExpectation_sep_lottery _ h hd,
      stepExpectation_sep_lottery _ h hd]
    norm_num
  · rw [stepExpectation_sep_decision σ h hd, stepExpectation_sep_decision _ h hd,
      stepExpectation_sep_decision _ h hd]
    have e0 : devProfile σ false false t h = PMF.pure Label.stay := by
      simp [devProfile, alwaysStay]
    have e1 : devProfile σ false true t h = σ true t h := by
      simp [devProfile]
    have e2 : devProfile σ true false t h = σ false t h := by
      simp [devProfile]
    have e3 : devProfile σ true true t h = PMF.pure Label.stay := by
      simp [devProfile, alwaysStay]
    rw [e0, e1, e2, e3]
    simp only [expect_pure, keepVal_stay]
    ring
  · rw [stepExpectation_sep_dead σ h hd, stepExpectation_sep_dead _ h hd,
      stepExpectation_sep_dead _ h hd]
    norm_num

/-- The alive probability recursion along the forced live path. -/
theorem stateExpectation_succ_forced {σ : sepGame.BehaviorProfile}
    (hσ : sepGame.IsLegalBehaviorProfile SepLegal σ) (t : ℕ) :
    sepGame.stateExpectation aliveVal σ Site.lottery (t + 1) =
      sepGame.stateExpectation aliveVal σ Site.lottery t *
        sepGame.stepExpectation aliveVal σ (forcedHist t) := by
  rw [stateExpectation_succ]
  unfold stateExpectation
  rw [expect_congr_on_support _ _
    (fun h : sepGame.Hist t =>
      sepGame.stepExpectation aliveVal σ (forcedHist t) * aliveVal h.2) ?_,
    expect_const_mul, mul_comm]
  intro h hh
  by_cases hdead : h.2 = Site.dead
  · rw [stepExpectation_sep_dead σ h hdead, hdead]
    simp
  · have h1 : aliveVal h.2 = 1 := by
      cases hc : h.2 with
      | lottery => simp
      | decision => simp
      | dead => exact absurd hc hdead
    rw [h1, mul_one, forced_of_mem_support_histDist hσ t h hh hdead]

/-- **The global product identity.**  Along the forced path the survival
probability factorizes across the two players, at every horizon. -/
theorem stateExpectation_eq_mul_dev {σ : sepGame.BehaviorProfile}
    (hσ : sepGame.IsLegalBehaviorProfile SepLegal σ) (t : ℕ) :
    sepGame.stateExpectation aliveVal σ Site.lottery t =
      sepGame.stateExpectation aliveVal (devProfile σ false) Site.lottery t *
        sepGame.stateExpectation aliveVal (devProfile σ true) Site.lottery t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [stateExpectation_succ_forced hσ t,
      stateExpectation_succ_forced (isLegal_devProfile hσ false) t,
      stateExpectation_succ_forced (isLegal_devProfile hσ true) t, ih,
      stepExpectation_eq_mul_dev σ (forcedHist t)]
    ring

/-- **The impossibility half.**  `(1/2, 1/2)` is not a legal uniform
equilibrium payoff of the original game.

The route is finite-horizon throughout: no limits of the attainability
clauses are taken.  Two horizons suffice — `T₁ = max T₀ 1` bounds each
player's own survival factor by `3/5` (the repository's deviation clause is
relative to the profile's own payoff, hence `1/2 + 2ε` rather than the hand
proof's `1/2 + ε`), and `T₂ = 100 * T₁` turns the resulting `9/25` bound on
their product into an average of at most `1/100 + 9/25 = 37/100`, below the
`9/20` the payoff clause forces. -/
theorem not_isLegalUniformEquilibriumPayoff_half :
    ¬ sepGame.IsLegalUniformEquilibriumPayoff SepLegal Site.lottery (fun _ => 1 / 2) := by
  intro hW
  obtain ⟨σ, T₀, hσ⟩ := hW (1 / 20) (by norm_num)
  set T₁ : ℕ := max T₀ 1 with hT₁def
  have hT₁ge : T₀ ≤ T₁ := le_max_left _ _
  have hT₁pos : 0 < T₁ := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hT₁R : (0 : ℝ) < (T₁ : ℝ) := by exact_mod_cast hT₁pos
  obtain ⟨⟨hlegal, hcap⟩, happ⟩ := hσ T₁ hT₁ge
  have hdev : ∀ i : Bool,
      sepGame.stateExpectation aliveVal (devProfile σ i) Site.lottery T₁ ≤ 3 / 5 := by
    intro i
    have hcapi := hcap i (alwaysStay i) (isLegal_alwaysStay i)
    have happi := (abs_le.mp (happ i)).2
    have hle : sepGame.finiteAveragePayoff Site.lottery T₁ (devProfile σ i) i ≤ 3 / 5 := by
      have hupd : sepGame.finiteAveragePayoff Site.lottery T₁ (devProfile σ i) i =
          sepGame.finiteAveragePayoff Site.lottery T₁
            (Function.update σ i (alwaysStay i)) i := rfl
      rw [hupd]
      linarith
    rw [finiteAveragePayoff_sep] at hle
    have hsum : (T₁ : ℝ) * sepGame.stateExpectation aliveVal (devProfile σ i) Site.lottery T₁ ≤
        ∑ t ∈ Finset.range T₁,
          sepGame.stateExpectation aliveVal (devProfile σ i) Site.lottery t := by
      have hle' := Finset.sum_le_sum (s := Finset.range T₁)
        (f := fun _ : ℕ =>
          sepGame.stateExpectation aliveVal (devProfile σ i) Site.lottery T₁)
        (g := fun t => sepGame.stateExpectation aliveVal (devProfile σ i) Site.lottery t)
        (fun t ht => stateExpectation_sep_antitone _ (le_of_lt (Finset.mem_range.mp ht)))
      simpa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hle'
    have hinv := mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hT₁R))
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hT₁R), one_mul] at hinv
    linarith
  have hAT₁ : sepGame.stateExpectation aliveVal σ Site.lottery T₁ ≤ 9 / 25 := by
    rw [stateExpectation_eq_mul_dev hlegal T₁]
    have hb := hdev false
    have hc := hdev true
    have hbn := (stateExpectation_sep_mem (devProfile σ false) T₁).1
    have hcn := (stateExpectation_sep_mem (devProfile σ true) T₁).1
    nlinarith
  have hmul : T₁ ≤ 100 * T₁ := Nat.le_mul_of_pos_left T₁ (by norm_num)
  obtain ⟨-, happ2⟩ := hσ (100 * T₁) (le_trans hT₁ge hmul)
  have hcast : (((100 * T₁ : ℕ)) : ℝ) = 100 * (T₁ : ℝ) := by push_cast; ring
  have hlow : (9 : ℝ) / 20 ≤ (100 * (T₁ : ℝ))⁻¹ *
      ∑ t ∈ Finset.range (100 * T₁),
        sepGame.stateExpectation aliveVal σ Site.lottery t := by
    have h := (abs_le.mp (happ2 false)).1
    rw [finiteAveragePayoff_sep, hcast] at h
    linarith
  have hsplit : ∑ t ∈ Finset.range (100 * T₁),
      sepGame.stateExpectation aliveVal σ Site.lottery t ≤
        (T₁ : ℝ) + 100 * (T₁ : ℝ) * (9 / 25) := by
    rw [Finset.range_eq_Ico,
      ← Finset.sum_Ico_consecutive _ (Nat.zero_le T₁) hmul]
    have h1 : ∑ t ∈ Finset.Ico 0 T₁,
        sepGame.stateExpectation aliveVal σ Site.lottery t ≤ (T₁ : ℝ) := by
      calc ∑ t ∈ Finset.Ico 0 T₁, sepGame.stateExpectation aliveVal σ Site.lottery t
          ≤ ∑ _t ∈ Finset.Ico 0 T₁, (1 : ℝ) :=
            Finset.sum_le_sum fun t _ => (stateExpectation_sep_mem σ t).2
        _ = (T₁ : ℝ) := by simp
    have h2 : ∑ t ∈ Finset.Ico T₁ (100 * T₁),
        sepGame.stateExpectation aliveVal σ Site.lottery t ≤
          100 * (T₁ : ℝ) * (9 / 25) := by
      calc ∑ t ∈ Finset.Ico T₁ (100 * T₁),
              sepGame.stateExpectation aliveVal σ Site.lottery t
          ≤ ∑ _t ∈ Finset.Ico T₁ (100 * T₁), (9 / 25 : ℝ) :=
            Finset.sum_le_sum fun t ht =>
              le_trans (stateExpectation_sep_antitone σ (Finset.mem_Ico.mp ht).1) hAT₁
        _ = ((100 * T₁ - T₁ : ℕ) : ℝ) * (9 / 25) := by
            simp [Nat.card_Ico, mul_comm]
        _ ≤ 100 * (T₁ : ℝ) * (9 / 25) := by
            refine mul_le_mul_of_nonneg_right ?_ (by norm_num)
            rw [← hcast]
            exact_mod_cast Nat.sub_le (100 * T₁) T₁
    linarith
  have hpos : (0 : ℝ) < 100 * (T₁ : ℝ) := by linarith
  have hup := mul_le_mul_of_nonneg_left hsplit (le_of_lt (inv_pos.mpr hpos))
  have heq : (100 * (T₁ : ℝ))⁻¹ * ((T₁ : ℝ) + 100 * (T₁ : ℝ) * (9 / 25)) = 37 / 100 := by
    field_simp
    ring
  rw [heq] at hup
  linarith

-- ============================================================================
-- The jointly controlled lottery in the padded game
-- ============================================================================

/-- A fair Boolean draw. -/
def fairBool : PMF Bool :=
  PMF.ofFintype (fun _ : Bool => 1 / 2)
    (by rw [Fintype.sum_bool, one_div]; exact ENNReal.inv_two_add_inv_two)

/-- The fair coin over the two labels that share a normalization: the private
bit each player publishes at `lottery`, at no cost to the transition. -/
def coinFlip : PMF Label :=
  PMF.map (fun b => if b then Label.dupe else Label.stay) fairBool

/-- Expectations under the fair coin. -/
theorem expect_coinFlip (u : Label → ℝ) :
    expect coinFlip u = 1 / 2 * u Label.dupe + 1 / 2 * u Label.stay := by
  unfold coinFlip
  rw [expect_map, expect_eq_sum, Fintype.sum_bool]
  simp [fairBool, PMF.ofFintype_apply]

/-- The published bit: whether the label is the duplicate. -/
def isDupe : Label → Bool
  | Label.dupe => true
  | _ => false

/-- Real-valued form of the published bit. -/
def bitVal (l : Label) : ℝ := if isDupe l then 1 else 0

/-- The reduced continuation label publishes bit `false`. -/
@[simp] theorem isDupe_stay : isDupe Label.stay = false := rfl

/-- The duplicate label publishes bit `true`. -/
@[simp] theorem isDupe_dupe : isDupe Label.dupe = true := rfl

/-- The quitting label publishes bit `false`. -/
@[simp] theorem isDupe_quit : isDupe Label.quit = false := rfl

/-- Real-valued published bit of the reduced continuation label. -/
@[simp] theorem bitVal_stay : bitVal Label.stay = 0 := rfl

/-- Real-valued published bit of the duplicate label. -/
@[simp] theorem bitVal_dupe : bitVal Label.dupe = 1 := rfl

/-- Real-valued published bit of the quitting label. -/
@[simp] theorem bitVal_quit : bitVal Label.quit = 0 := rfl

/-- The fair coin publishes a fair bit. -/
@[simp] theorem expect_coinFlip_bitVal : expect coinFlip bitVal = 1 / 2 := by
  rw [expect_coinFlip]
  simp

/-- Indicator that the two published bits agree, written as a sum of two
products so that it factorizes over independent coordinates. -/
def agreeVal (a : Bool → Label) : ℝ :=
  bitVal (a false) * bitVal (a true) + (1 - bitVal (a false)) * (1 - bitVal (a true))

/-- `agreeVal` is the indicator of "both bits agree". -/
theorem agreeVal_eq_ite (a : Bool → Label) :
    agreeVal a = if isDupe (a false) = isDupe (a true) then 1 else 0 := by
  unfold agreeVal
  cases a false <;> cases a true <;> norm_num

/-- `agreeVal` is an indicator. -/
theorem agreeVal_mem_unitInterval (a : Bool → Label) :
    0 ≤ agreeVal a ∧ agreeVal a ≤ 1 := by
  rw [agreeVal_eq_ite]; split_ifs <;> norm_num

/-- `agreeVal` is idempotent under multiplication. -/
theorem agreeVal_mul_self (a : Bool → Label) : agreeVal a * agreeVal a = agreeVal a := by
  rw [agreeVal_eq_ite]; split_ifs <;> norm_num

/-- The agreement indicator's expectation under an independent product depends
only on the two coordinates' bit means. -/
theorem expect_pmfPi_agreeVal (m : Bool → PMF Label) :
    expect (pmfPi (A := fun _ : Bool => Label) m) agreeVal =
      expect (m false) bitVal * expect (m true) bitVal +
        (1 - expect (m false) bitVal) * (1 - expect (m true) bitVal) := by
  have hsplit : agreeVal = fun a : Bool → Label =>
      (fun (_ : Bool) (l : Label) => bitVal l) false (a false) *
        (fun (_ : Bool) (l : Label) => bitVal l) true (a true) +
      (fun (_ : Bool) (l : Label) => 1 - bitVal l) false (a false) *
        (fun (_ : Bool) (l : Label) => 1 - bitVal l) true (a true) := rfl
  rw [hsplit, expect_add, expect_pmfPi_mul m (fun _ l => bitVal l),
    expect_pmfPi_mul m (fun _ l => 1 - bitVal l)]
  have hsub : ∀ c : Bool, expect (m c) (fun l => 1 - bitVal l) = 1 - expect (m c) bitVal := by
    intro c
    rw [expect_sub, expect_const]
  rw [hsub false, hsub true]

/-- **Unbiasability.**  As long as one coordinate is a fresh fair coin, the
agreement indicator is fair whatever the other coordinate does. -/
theorem expect_pmfPi_agreeVal_of_coin (m : Bool → PMF Label) (j : Bool)
    (hj : m j = coinFlip) :
    expect (pmfPi (A := fun _ : Bool => Label) m) agreeVal = 1 / 2 := by
  rw [expect_pmfPi_agreeVal]
  cases j with
  | false => rw [hj, expect_coinFlip_bitVal]; ring
  | true => rw [hj, expect_coinFlip_bitVal]; ring

/-- **The jointly controlled lottery.**  Publish a fair private bit at
`lottery`, then continue forever if the two bits agree and quit at the next
stage if they differ. -/
def xorStrategy (_i : Bool) : (t : ℕ) → paddedGame.Hist t → PMF Label
  | 0, _ => coinFlip
  | 1, h =>
      if isDupe ((h.1 0).2 false) = isDupe ((h.1 0).2 true) then PMF.pure Label.stay
      else PMF.pure Label.quit
  | _ + 2, _ => PMF.pure Label.stay

/-- Both players run the same lottery strategy. -/
def xorProfile : paddedGame.BehaviorProfile := xorStrategy

/-- The epoch-one history reached after the joint first-stage labels `a`. -/
def firstHist (a : Bool → Label) : paddedGame.Hist 1 :=
  (Fin.snoc (paddedGame.emptyHist Site.lottery).1 (Site.lottery, a), Site.decision)

/-- The epoch-one history records exactly the first-stage joint labels. -/
@[simp] theorem firstHist_stage (a : Bool → Label) :
    ((firstHist a).1 0).2 = a := by
  change ((Fin.snoc Fin.elim0 (Site.lottery, a) : Fin 1 → Site × (Bool → Label)) 0).2 = a
  rw [show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]

/-- Epoch one is always reached at `decision`. -/
@[simp] theorem firstHist_snd (a : Bool → Label) : (firstHist a).2 = Site.decision := rfl

/-- `lottery` moves on unconditionally, in the padded game as well. -/
theorem paddedTransition_lottery (a : Bool → Label) :
    paddedGame.transition Site.lottery a = PMF.pure Site.decision := rfl

/-- Nobody can be absorbed before epoch two: the first stage's transition
ignores the actions. -/
theorem stateExpectation_one (σ : paddedGame.BehaviorProfile) :
    paddedGame.stateExpectation aliveVal σ Site.lottery 1 = 1 := by
  rw [stateExpectation_succ, histDist_zero, expect_pure,
    stepExpectation_padded_lottery σ (paddedGame.emptyHist Site.lottery) rfl]

/-- The epoch-two alive probability under any profile that runs the lottery at
epoch zero. -/
theorem stateExpectation_two (σ : paddedGame.BehaviorProfile) :
    paddedGame.stateExpectation aliveVal σ Site.lottery 2 =
      expect (pmfPi (A := fun _ : Bool => Label) (fun i => σ i 0
        (paddedGame.emptyHist Site.lottery)))
        (fun a => paddedGame.stepExpectation aliveVal σ (firstHist a)) := by
  rw [stateExpectation_succ, expect_histDist_one]
  refine congrArg (expect (pmfPi (fun i => σ i 0 (paddedGame.emptyHist Site.lottery))))
    (funext fun a => ?_)
  rw [paddedTransition_lottery, expect_pure]
  rfl

/-- At epoch one the lottery strategy's continuation mass is exactly the
agreement indicator of the two published labels. -/
theorem expect_xorStrategy_padKeep (i : Bool) (a : Bool → Label) :
    expect (xorProfile i 1 (firstHist a)) (padKeep i) = agreeVal a := by
  change expect (xorStrategy i 1 (firstHist a)) (padKeep i) = agreeVal a
  rw [agreeVal_eq_ite]
  change expect (if isDupe (((firstHist a).1 0).2 false) = isDupe (((firstHist a).1 0).2 true)
      then PMF.pure Label.stay else PMF.pure Label.quit) (padKeep i) = _
  rw [firstHist_stage]
  split_ifs <;> simp

/-- After epoch one the lottery profile never quits again, so a stage costs
nothing on the surviving branch. -/
theorem stepExpectation_xor_late {t : ℕ} (h : paddedGame.Hist (t + 2)) :
    paddedGame.stepExpectation aliveVal xorProfile h = aliveVal h.2 := by
  rcases hd : h.2 with _ | _ | _
  · rw [stepExpectation_padded_lottery xorProfile h hd]; simp
  · rw [stepExpectation_padded_decision xorProfile h hd]
    have hx : ∀ i : Bool, xorProfile i (t + 2) h = PMF.pure Label.stay := fun _ => rfl
    rw [hx false, hx true, expect_pure, expect_pure, padKeep_stay, padKeep_stay]
    norm_num
  · rw [stepExpectation_padded_dead xorProfile h hd]; simp

/-- The lottery's alive probability: certain for two stages, then one half. -/
theorem stateExpectation_xor (t : ℕ) :
    paddedGame.stateExpectation aliveVal xorProfile Site.lottery (t + 2) = 1 / 2 := by
  have hbase : paddedGame.stateExpectation aliveVal xorProfile Site.lottery 2 = 1 / 2 := by
    rw [stateExpectation_two]
    have hstep : ∀ a : Bool → Label,
        paddedGame.stepExpectation aliveVal xorProfile (firstHist a) = agreeVal a := by
      intro a
      rw [stepExpectation_padded_decision xorProfile (firstHist a) (firstHist_snd a),
        expect_xorStrategy_padKeep false a, expect_xorStrategy_padKeep true a,
        agreeVal_mul_self]
    rw [funext hstep]
    exact expect_pmfPi_agreeVal_of_coin _ false rfl
  induction t with
  | zero => exact hbase
  | succ t ih =>
    rw [stateExpectation_succ,
      expect_congr_on_support _ _ (fun h : paddedGame.Hist (t + 2) => aliveVal h.2)
        (fun h _ => stepExpectation_xor_late h)]
    exact ih

/-- The lottery's own finite-horizon payoff is `1/2 + 1/T`. -/
theorem finiteAveragePayoff_xor (who : Bool) {T : ℕ} (hT : 2 ≤ T) :
    paddedGame.finiteAveragePayoff Site.lottery T xorProfile who = 1 / 2 + (T : ℝ)⁻¹ := by
  have hTR : (0 : ℝ) < (T : ℝ) := by
    have : (0 : ℕ) < T := lt_of_lt_of_le (by norm_num) hT
    exact_mod_cast this
  rw [paddedGame.finiteAveragePayoff_eq_sum_stateExpectation aliveVal
    (fun _ _ _ => rfl) xorProfile Site.lottery who T]
  have hsum : ∑ t ∈ Finset.range T,
      paddedGame.stateExpectation aliveVal xorProfile Site.lottery t =
        2 + ((T : ℝ) - 2) * (1 / 2) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 2) hT,
      ← Finset.range_eq_Ico]
    have h1 : ∑ t ∈ Finset.range 2,
        paddedGame.stateExpectation aliveVal xorProfile Site.lottery t = 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one, stateExpectation_zero,
        stateExpectation_one]
      norm_num
    have h2 : ∑ t ∈ Finset.Ico 2 T,
        paddedGame.stateExpectation aliveVal xorProfile Site.lottery t =
          ((T - 2 : ℕ) : ℝ) * (1 / 2) := by
      rw [Finset.sum_congr rfl (fun t ht => ?_), Finset.sum_const, Nat.card_Ico,
        nsmul_eq_mul]
      obtain ⟨k, rfl⟩ : ∃ k, t = k + 2 :=
        ⟨t - 2, (Nat.sub_add_cancel (Finset.mem_Ico.mp ht).1).symm⟩
      exact stateExpectation_xor k
    rw [h1, h2, Nat.cast_sub hT]
    norm_num
  rw [hsum]
  field_simp
  ring

-- ============================================================================
-- Every unilateral deviation is capped by the lottery's own payoff
-- ============================================================================

/-- **Unbiasability, one stage.**  Whatever the deviator publishes at
`lottery`, the opponent's fresh fair bit still decides the XOR, so the
deviator's epoch-one survival weight is at most the agreement indicator. -/
theorem stepExpectation_dev_le (who : Bool) (dev : paddedGame.BehaviorStrategy who)
    (a : Bool → Label) :
    paddedGame.stepExpectation aliveVal (Function.update xorProfile who dev)
      (firstHist a) ≤ agreeVal a := by
  rw [stepExpectation_padded_decision _ (firstHist a) (firstHist_snd a)]
  have hag := agreeVal_mem_unitInterval a
  cases who with
  | false =>
    have hopp : Function.update xorProfile false dev true = xorProfile true := by simp
    rw [hopp, expect_xorStrategy_padKeep true a]
    have hd := expect_unitInterval
      (Function.update xorProfile false dev false 1 (firstHist a)) (padKeep false)
      (padKeep_mem_unitInterval false)
    nlinarith [hd.1, hd.2, hag.1]
  | true =>
    have hopp : Function.update xorProfile true dev false = xorProfile false := by simp
    rw [hopp, expect_xorStrategy_padKeep false a]
    have hd := expect_unitInterval
      (Function.update xorProfile true dev true 1 (firstHist a)) (padKeep true)
      (padKeep_mem_unitInterval true)
    nlinarith [hd.1, hd.2, hag.1]

/-- The deviator's epoch-two survival probability is at most one half. -/
theorem stateExpectation_dev_two_le (who : Bool) (dev : paddedGame.BehaviorStrategy who) :
    paddedGame.stateExpectation aliveVal (Function.update xorProfile who dev)
      Site.lottery 2 ≤ 1 / 2 := by
  rw [stateExpectation_two]
  have hcoin : (fun i => (Function.update xorProfile who dev) i 0
      (paddedGame.emptyHist Site.lottery)) (!who) = coinFlip := by
    cases who <;> simp [xorProfile, xorStrategy]
  calc expect (pmfPi (A := fun _ : Bool => Label)
        (fun i => (Function.update xorProfile who dev) i 0
          (paddedGame.emptyHist Site.lottery)))
        (fun a => paddedGame.stepExpectation aliveVal
          (Function.update xorProfile who dev) (firstHist a))
      ≤ expect (pmfPi (A := fun _ : Bool => Label)
          (fun i => (Function.update xorProfile who dev) i 0
            (paddedGame.emptyHist Site.lottery))) agreeVal :=
        expect_mono _ _ _ fun a => stepExpectation_dev_le who dev a
    _ = 1 / 2 := expect_pmfPi_agreeVal_of_coin _ (!who) hcoin

/-- **The deviation cap.**  Every unilateral deviation from the lottery earns
at most the lottery's own finite-horizon payoff. -/
theorem finiteAveragePayoff_dev_le (who : Bool) (dev : paddedGame.BehaviorStrategy who)
    {T : ℕ} (hT : 2 ≤ T) :
    paddedGame.finiteAveragePayoff Site.lottery T
      (Function.update xorProfile who dev) who ≤ 1 / 2 + (T : ℝ)⁻¹ := by
  have hTR : (0 : ℝ) < (T : ℝ) := by
    have : (0 : ℕ) < T := lt_of_lt_of_le (by norm_num) hT
    exact_mod_cast this
  rw [paddedGame.finiteAveragePayoff_eq_sum_stateExpectation aliveVal
    (fun _ _ _ => rfl) _ Site.lottery who T]
  have hlate : ∀ t : ℕ, 2 ≤ t →
      paddedGame.stateExpectation aliveVal (Function.update xorProfile who dev)
        Site.lottery t ≤ 1 / 2 := fun t ht =>
    le_trans (paddedGame.stateExpectation_antitone aliveVal _ Site.lottery
      (fun _ h => stepExpectation_padded_le _ h) ht) (stateExpectation_dev_two_le who dev)
  have hsum : ∑ t ∈ Finset.range T,
      paddedGame.stateExpectation aliveVal (Function.update xorProfile who dev)
        Site.lottery t ≤ 2 + ((T : ℝ) - 2) * (1 / 2) := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 2) hT,
      ← Finset.range_eq_Ico]
    have h1 : ∑ t ∈ Finset.range 2,
        paddedGame.stateExpectation aliveVal (Function.update xorProfile who dev)
          Site.lottery t = 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_one, stateExpectation_zero,
        stateExpectation_one]
      norm_num
    have h2 : ∑ t ∈ Finset.Ico 2 T,
        paddedGame.stateExpectation aliveVal (Function.update xorProfile who dev)
          Site.lottery t ≤ ((T - 2 : ℕ) : ℝ) * (1 / 2) := by
      calc ∑ t ∈ Finset.Ico 2 T,
              paddedGame.stateExpectation aliveVal (Function.update xorProfile who dev)
                Site.lottery t
          ≤ ∑ _t ∈ Finset.Ico 2 T, (1 / 2 : ℝ) :=
            Finset.sum_le_sum fun t ht => hlate t (Finset.mem_Ico.mp ht).1
        _ = ((T - 2 : ℕ) : ℝ) * (1 / 2) := by
            rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    rw [h1, Nat.cast_sub hT] at *
    linarith
  have hval : (T : ℝ)⁻¹ * (2 + ((T : ℝ) - 2) * (1 / 2)) = 1 / 2 + (T : ℝ)⁻¹ := by
    field_simp
    ring
  calc (T : ℝ)⁻¹ * ∑ t ∈ Finset.range T,
        paddedGame.stateExpectation aliveVal (Function.update xorProfile who dev)
          Site.lottery t
      ≤ (T : ℝ)⁻¹ * (2 + ((T : ℝ) - 2) * (1 / 2)) :=
        mul_le_mul_of_nonneg_left hsum (le_of_lt (inv_pos.mpr hTR))
    _ = 1 / 2 + (T : ℝ)⁻¹ := hval

/-- **The attainability half.**  `(1/2, 1/2)` is a uniform equilibrium payoff
of the padded game — indeed the lottery is an exact equilibrium of every
horizon `T ≥ 2`, with payoff `1/2 + 1/T`. -/
theorem isUniformEquilibriumPayoff_paddedGame_half :
    paddedGame.IsUniformEquilibriumPayoff Site.lottery (fun _ => 1 / 2) := by
  intro ε hε
  refine ⟨xorProfile, max 2 ⌈ε⁻¹⌉₊, fun T hT => ?_⟩
  have hT2 : 2 ≤ T := le_trans (le_max_left _ _) hT
  have hTceil : ⌈ε⁻¹⌉₊ ≤ T := le_trans (le_max_right _ _) hT
  have hTR : (0 : ℝ) < (T : ℝ) := by
    have : (0 : ℕ) < T := lt_of_lt_of_le (by norm_num) hT2
    exact_mod_cast this
  have hinv : (T : ℝ)⁻¹ ≤ ε := by
    have h1 : ε⁻¹ ≤ (T : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hTceil)
    have h2 : ε * ε⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hε)
    have h3 : (T : ℝ) * (T : ℝ)⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hTR)
    have h4 : (0 : ℝ) < (T : ℝ)⁻¹ := inv_pos.mpr hTR
    nlinarith [h1, h2, h3, h4]
  refine ⟨fun who dev => ?_, fun who => ?_⟩
  · rw [finiteAveragePayoff_xor who hT2]
    have hdev := finiteAveragePayoff_dev_le who dev hT2
    linarith
  · rw [finiteAveragePayoff_xor who hT2]
    have hz : (1 : ℝ) / 2 + (T : ℝ)⁻¹ - (fun _ : Bool => (1 : ℝ) / 2) who = (T : ℝ)⁻¹ := by
      norm_num
    rw [hz, abs_of_nonneg (le_of_lt (inv_pos.mpr hTR))]
    exact hinv

/-- **The refutation.**  The unconditional padding transfer is false: a
uniform equilibrium payoff of `G.normalizedGame Legal hLegal` need not be a
legal uniform equilibrium payoff of `G`.  This is exactly the direction that
`isLegalUniformEquilibriumPayoff_of_witness` has to condition on a
normalized-history-invariant legal witness. -/
theorem not_forall_isLegalUniformEquilibriumPayoff_of_padded :
    ¬ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : StochasticGame ι)
        (Legal : G.State → ∀ i, G.Act i → Prop) (hLegal : ∀ s i, ∃ a, Legal s i a)
        (s₀ : G.State) (v : Payoff ι),
        (G.normalizedGame Legal hLegal).IsUniformEquilibriumPayoff s₀ v →
          G.IsLegalUniformEquilibriumPayoff Legal s₀ v := by
  intro htransfer
  exact not_isLegalUniformEquilibriumPayoff_half
    (htransfer Bool sepGame SepLegal sepLegal_nonempty Site.lottery (fun _ => 1 / 2)
      isUniformEquilibriumPayoff_paddedGame_half)

end PaddedLotterySeparation

end GameTheory
