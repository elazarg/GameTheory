import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Math.Probability
import GameTheory.Concepts.SolutionConcepts

/-!
# Infinite Repeated Games

An infinite repeated game plays the same stage game at every natural-numbered
period.  Players observe the public history of past action profiles and choose
the next stage-game action.

This file is intentionally lightweight: it provides a public-action
infinite-horizon repeated-game API.  Finite protocol syntax lives in
`MultiRoundGame`, whose `rounds : List Round` is a separate compiled-language
representation.

## Main definitions

* `RepeatedGame` — an infinite repeated game with observable stage actions
* `RepeatedGame.play` — the generated stream of action profiles
* `RepeatedGame.discountedPayoff` — normalized discounted payoff
* `RepeatedGame.discountedKernelGame` — strategic-form kernel game induced by a
  fixed discount factor

## Main results

* `RepeatedGame.discountedPayoff_constStrategy` — constant play has the stage
  payoff for `0 ≤ δ < 1`
* `RepeatedGame.constStrategy_isDiscountedNash` — repeating a stage Nash action
  profile is Nash in the discounted repeated game, under bounded stage payoffs
-/

noncomputable section

open scoped BigOperators

namespace GameTheory

open Math.Probability

/-- An infinite repeated game with public observation of past action profiles. -/
structure RepeatedGame (ι : Type) where
  /-- Per-player action set in the stage game. -/
  Act : ι → Type
  /-- Stage-game utility given a joint action profile. -/
  stageUtil : (∀ i, Act i) → ι → ℝ

namespace RepeatedGame

variable {ι : Type}

/-- History before period `t`: the public sequence of past action profiles. -/
abbrev History (R : RepeatedGame ι) (t : ℕ) : Type :=
  Fin t → (∀ i, R.Act i)

/-- A strategy chooses an action after every finite public action history. -/
abbrev Strategy (R : RepeatedGame ι) (i : ι) : Type :=
  (t : ℕ) → R.History t → R.Act i

/-- A repeated-game strategy profile. -/
abbrev RProfile (R : RepeatedGame ι) : Type :=
  ∀ i, R.Strategy i

/-- Payoff of a single round given a joint action. -/
def roundPayoff (R : RepeatedGame ι) (a : ∀ i, R.Act i) (who : ι) : ℝ :=
  R.stageUtil a who

/-- Generate the action profile at period `t` by running strategies on the
history built from earlier periods. -/
def play (R : RepeatedGame ι) (σ : R.RProfile) : (t : ℕ) → (∀ i, R.Act i)
  | t => fun i => σ i t (fun k => R.play σ k)
termination_by t => t
decreasing_by exact k.isLt

/-- Constant repeated play of a fixed stage action profile. -/
def constStrategy (R : RepeatedGame ι) (a : ∀ i, R.Act i) : R.RProfile :=
  fun i _ _ => a i

/-- Normalized discounted payoff in the infinite repeated game.

The definition is total for all real `δ`; the payoff interpretation and lemmas
below use the explicit side conditions `0 ≤ δ` and `δ < 1`. -/
def discountedPayoff (R : RepeatedGame ι) (δ : ℝ)
    (σ : R.RProfile) (who : ι) : ℝ :=
  (1 - δ) * ∑' t : ℕ, δ ^ t * R.stageUtil (R.play σ t) who

/-- The strategic-form kernel game induced by a fixed discounted repeated game. -/
def discountedKernelGame (R : RepeatedGame ι) (δ : ℝ) : KernelGame ι :=
  KernelGame.ofEU R.Strategy (fun σ i => R.discountedPayoff δ σ i)

@[simp] theorem play_constStrategy
    (R : RepeatedGame ι) (a : ∀ i, R.Act i) (t : ℕ) :
    R.play (R.constStrategy a) t = a := by
  funext i
  simp [play, constStrategy]

/-- If one player deviates from constant play, every realized period profile is
the constant action profile with only that player's current action updated. -/
theorem play_update_constStrategy
    (R : RepeatedGame ι) [DecidableEq ι] (a : ∀ i, R.Act i)
    (who : ι) (dev : R.Strategy who) (t : ℕ) :
    R.play (Function.update (R.constStrategy a) who dev) t =
      Function.update a who
        (dev t (fun k => R.play (Function.update (R.constStrategy a) who dev) k)) := by
  funext i
  by_cases hi : i = who
  · subst hi
    rw [play]
    simp [Function.update]
  · simp [play, constStrategy, Function.update, hi]

/-- Discounted stage utilities are summable when stage utilities are uniformly
bounded and `δ ∈ [0,1)`. -/
theorem summable_discounted_stageUtil_of_abs_bound
    (R : RepeatedGame ι) {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ : R.RProfile} (who : ι)
    (hbd : ∀ a : ∀ i, R.Act i, |R.stageUtil a who| ≤ C) :
    Summable fun t : ℕ => δ ^ t * R.stageUtil (R.play σ t) who := by
  have hgeom : Summable fun t : ℕ => C * δ ^ t :=
    (summable_geometric_of_lt_one hδ0 hδ1).mul_left C
  refine Summable.of_norm_bounded hgeom ?_
  intro t
  rw [Real.norm_eq_abs]
  calc
    |δ ^ t * R.stageUtil (R.play σ t) who| =
        δ ^ t * |R.stageUtil (R.play σ t) who| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg hδ0 t)]
    _ ≤ δ ^ t * C :=
        mul_le_mul_of_nonneg_left (hbd (R.play σ t)) (pow_nonneg hδ0 t)
    _ = C * δ ^ t := by ring

/-- Pointwise dominance of all stage payoffs implies dominance of normalized
discounted payoffs. -/
theorem discountedPayoff_le_of_forall_stageUtil_le
    (R : RepeatedGame ι) {δ C : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    {σ τ : R.RProfile} (who : ι)
    (hbd : ∀ a : ∀ i, R.Act i, |R.stageUtil a who| ≤ C)
    (hle : ∀ t : ℕ,
      R.stageUtil (R.play σ t) who ≤ R.stageUtil (R.play τ t) who) :
    R.discountedPayoff δ σ who ≤ R.discountedPayoff δ τ who := by
  have hsσ := R.summable_discounted_stageUtil_of_abs_bound
    hδ0 hδ1 who hbd (σ := σ)
  have hsτ := R.summable_discounted_stageUtil_of_abs_bound
    hδ0 hδ1 who hbd (σ := τ)
  have hsum :
      (∑' t : ℕ, δ ^ t * R.stageUtil (R.play σ t) who) ≤
        ∑' t : ℕ, δ ^ t * R.stageUtil (R.play τ t) who := by
    exact hsσ.tsum_le_tsum
      (fun t => mul_le_mul_of_nonneg_left (hle t) (pow_nonneg hδ0 t)) hsτ
  exact mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hδ1.le)

/-- Normalized discounted payoff of constant repeated play is the stage payoff,
for discount factors in `[0, 1)`. -/
theorem discountedPayoff_constStrategy
    (R : RepeatedGame ι) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (a : ∀ i, R.Act i) (who : ι) :
    R.discountedPayoff δ (R.constStrategy a) who = R.stageUtil a who := by
  have hne : 1 - δ ≠ 0 := by linarith
  simp [discountedPayoff, tsum_mul_right, tsum_geometric_of_lt_one hδ0 hδ1, hne]

/-- If `a` is a stage-game Nash action profile, then constant repetition of `a`
is Nash in the discounted repeated game induced by any `δ ∈ [0,1)`, assuming
bounded stage payoffs for each player. -/
theorem constStrategy_isDiscountedNash
    (R : RepeatedGame ι) [DecidableEq ι]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (a : ∀ i, R.Act i)
    (hstage : ∀ (who : ι) (a' : R.Act who),
      R.stageUtil a who ≥ R.stageUtil (Function.update a who a') who)
    (hbd : ∀ who, ∃ C : ℝ,
      ∀ a : ∀ i, R.Act i, |R.stageUtil a who| ≤ C) :
    (R.discountedKernelGame δ).IsNash (R.constStrategy a) := by
  intro who dev
  obtain ⟨C, hC⟩ := hbd who
  simp only [discountedKernelGame, KernelGame.eu_ofEU, KernelGame.ofEU_Strategy]
  rw [ge_iff_le]
  exact R.discountedPayoff_le_of_forall_stageUtil_le
    (σ := Function.update (R.constStrategy a) who dev)
    (τ := R.constStrategy a) hδ0 hδ1 who hC (fun t => by
      rw [R.play_update_constStrategy a who dev t]
      rw [R.play_constStrategy a t]
      exact hstage who _)

end RepeatedGame

end GameTheory
