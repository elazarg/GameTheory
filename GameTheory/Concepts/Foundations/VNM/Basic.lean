/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Fintype
import Math.Probability
import Math.ProbabilityMassFunction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Lottery Expected Utility

This file records expected-utility facts for lotteries, relation-level vNM
preference axioms, and axiom-independence examples. It proves that preferences
represented by expected utility satisfy the vNM axioms. It also proves the
finite-outcome converse: the vNM axioms imply an expected-utility
representation.
-/

namespace GameTheory

open Math.Probability

namespace VNM

universe u v

/-- A lottery over outcomes is a probability mass function over outcomes. -/
abbrev Lottery (Ω : Type*) := PMF Ω

/-- Expected utility of a lottery. -/
noncomputable def expectedValue {Ω : Type*} (u : Ω → ℝ) (L : Lottery Ω) : ℝ :=
  expect L u

@[simp] theorem expectedValue_pure {Ω : Type*} (u : Ω → ℝ) (ω : Ω) :
    expectedValue u (PMF.pure ω) = u ω := by
  simp [expectedValue]

/-- Expected utility as a finite sum over outcomes. -/
theorem expectedValue_eq_sum {Ω : Type*} [Fintype Ω] (u : Ω → ℝ) (L : Lottery Ω) :
    expectedValue u L = ∑ ω : Ω, (L ω).toReal * u ω := by
  simp [expectedValue, expect_eq_sum]

/-- Expected utility is monotone in the outcome utility function. -/
theorem expectedValue_mono {Ω : Type*} [Finite Ω] (L : Lottery Ω) {u v : Ω → ℝ}
    (h : ∀ ω, u ω ≤ v ω) :
    expectedValue u L ≤ expectedValue v L := by
  exact expect_mono L u v h

/-- Expected utility is additive in the outcome utility function. -/
theorem expectedValue_add {Ω : Type*} [Finite Ω] (L : Lottery Ω) (u v : Ω → ℝ) :
    expectedValue (fun ω => u ω + v ω) L =
      expectedValue u L + expectedValue v L := by
  exact expect_add L u v

/-- Expected utility pulls out scalar multiplication of the utility function. -/
theorem expectedValue_const_mul {Ω : Type*} (L : Lottery Ω) (c : ℝ) (u : Ω → ℝ) :
    expectedValue (fun ω => c * u ω) L = c * expectedValue u L := by
  exact expect_const_mul L c u

/-- Expected utility of a constant utility function. -/
@[simp] theorem expectedValue_const {Ω : Type*} (L : Lottery Ω) (c : ℝ) :
    expectedValue (fun _ : Ω => c) L = c := by
  simp [expectedValue]

/-- Expected utility is invariantly affine in the utility scale. -/
theorem expectedValue_affine {Ω : Type*} [Finite Ω] (L : Lottery Ω)
    (u : Ω → ℝ) (a b : ℝ) :
    expectedValue (fun ω => a * u ω + b) L =
      a * expectedValue u L + b := by
  rw [expectedValue_add, expectedValue_const_mul, expectedValue_const]

/-- Expected utility commutes with subtraction of utility functions. -/
theorem expectedValue_sub {Ω : Type*} [Finite Ω] (L : Lottery Ω) (u v : Ω → ℝ) :
    expectedValue (fun ω => u ω - v ω) L =
      expectedValue u L - expectedValue v L := by
  exact expect_sub L u v

/-- Expected utility of `1 - u`. -/
theorem expectedValue_one_sub {Ω : Type*} [Finite Ω] (L : Lottery Ω) (u : Ω → ℝ) :
    expectedValue (fun ω => 1 - u ω) L = 1 - expectedValue u L := by
  rw [expectedValue_sub, expectedValue_const]

/-- Expected utility of a compound lottery is the outer expectation of inner
expected utilities. -/
theorem expectedValue_bind {ι Ω : Type*} [Finite Ω] (w : PMF ι)
    (L : ι → Lottery Ω) (u : Ω → ℝ) :
    expectedValue u (PMF.bind w L) = expect w (fun i => expectedValue u (L i)) := by
  exact expect_bind w L u

/-- Binary convex combination of two lotteries. -/
noncomputable def mix {Ω : Type*} (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (Ltrue Lfalse : Lottery Ω) : Lottery Ω :=
  PMF.bind
    (PMF.ofFintype (fun b : Bool =>
      if b then ENNReal.ofReal t else ENNReal.ofReal (1 - t)) (by
        rw [Fintype.sum_bool]
        calc
          ENNReal.ofReal t + ENNReal.ofReal (1 - t)
              = ENNReal.ofReal (t + (1 - t)) :=
                (ENNReal.ofReal_add ht0 (sub_nonneg.mpr ht1)).symm
          _ = 1 := by ring_nf; simp))
    (fun b => if b then Ltrue else Lfalse)

/-- Binary mixtures are a special case of compound lotteries. -/
theorem expectedValue_binaryMix {Ω : Type*} [Finite Ω] (coin : PMF Bool)
    (Ltrue Lfalse : Lottery Ω) (u : Ω → ℝ) :
    expectedValue u (PMF.bind coin fun b => if b then Ltrue else Lfalse) =
      (coin true).toReal * expectedValue u Ltrue +
        (coin false).toReal * expectedValue u Lfalse := by
  rw [expectedValue_bind]
  rw [show expect coin (fun b => expectedValue u (if b then Ltrue else Lfalse)) =
      ∑ b : Bool, (coin b).toReal * expectedValue u (if b then Ltrue else Lfalse) by
        exact expect_eq_sum coin _]
  simp

/-- Expected utility is linear in binary convex combinations of lotteries. -/
theorem expectedValue_mix {Ω : Type*} [Finite Ω] (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (Ltrue Lfalse : Lottery Ω) (u : Ω → ℝ) :
    expectedValue u (mix t ht0 ht1 Ltrue Lfalse) =
      t * expectedValue u Ltrue + (1 - t) * expectedValue u Lfalse := by
  rw [mix, expectedValue_binaryMix]
  simp [ht0, sub_nonneg.mpr ht1]

/-- A functional on lotteries is linear when it evaluates compound lotteries by
outer expected value of the component lottery values. -/
def IsLinearLotteryFunctional {Ω : Type u} (U : Lottery Ω → ℝ) : Prop :=
  ∀ {ι : Type v} [Finite ι] (w : PMF ι) (L : ι → Lottery Ω),
    U (PMF.bind w L) = expect w (fun i => U (L i))

/-- Expected utility is a linear functional on finite-outcome lotteries. -/
theorem expectedValue_isLinearLotteryFunctional {Ω : Type u} [Finite Ω] (u : Ω → ℝ) :
    IsLinearLotteryFunctional.{u, v} (expectedValue u) := by
  intro ι _ w L
  exact expectedValue_bind w L u

/-- Sure-thing principle for any linear lottery functional: if every contingent
lottery is weakly improved, then any lottery over contingencies is weakly
improved. -/
theorem sureThingPrinciple {Ω : Type u} {ι : Type v} [Finite ι]
    {U : Lottery Ω → ℝ} (hU : IsLinearLotteryFunctional.{u, v} U)
    (w : PMF ι) {L L' : ι → Lottery Ω}
    (h : ∀ i, U (L i) ≤ U (L' i)) :
    U (PMF.bind w L) ≤ U (PMF.bind w L') := by
  calc
    U (PMF.bind w L) = expect w (fun i => U (L i)) := hU w L
    _ ≤ expect w (fun i => U (L' i)) :=
      expect_mono w (fun i => U (L i)) (fun i => U (L' i)) h
    _ = U (PMF.bind w L') := (hU w L').symm

/-! ## Preference Axioms -/

/-- Strict preference induced by a weak preference relation. -/
def strict {Ω : Type*} (pref : Lottery Ω → Lottery Ω → Prop)
    (L M : Lottery Ω) : Prop :=
  pref L M ∧ ¬ pref M L

/-- Indifference induced by a weak preference relation. -/
def indiff {Ω : Type*} (pref : Lottery Ω → Lottery Ω → Prop)
    (L M : Lottery Ω) : Prop :=
  pref L M ∧ pref M L

/-- Completeness of a weak preference relation. -/
def Completeness {Ω : Type*} (pref : Lottery Ω → Lottery Ω → Prop) : Prop :=
  ∀ L M, pref L M ∨ pref M L

/-- Transitivity of a weak preference relation. -/
def Transitivity {Ω : Type*} (pref : Lottery Ω → Lottery Ω → Prop) : Prop :=
  ∀ L M N, pref L M → pref M N → pref L N

/-- Independence: mixing both sides with the same lottery and positive weight
preserves weak preference. -/
def Independence {Ω : Type*} (pref : Lottery Ω → Lottery Ω → Prop) : Prop :=
  ∀ (L M N : Lottery Ω) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1),
    pref L M ↔ pref (mix t (le_of_lt ht0) ht1 L N)
                    (mix t (le_of_lt ht0) ht1 M N)

/-- Continuity: if `L ≿ M ≿ N`, then `M` is indifferent to some binary
mixture of `L` and `N`. -/
def Continuity {Ω : Type*} (pref : Lottery Ω → Lottery Ω → Prop) : Prop :=
  ∀ L M N, pref L M → pref M N →
    ∃ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
      indiff pref M (mix t ht0 ht1 L N)

/-! ## Expected-Utility Preferences -/

/-- A weak preference relation is represented by expected utility when it ranks
lotteries exactly by the expectation of a utility index. -/
def RepresentsExpectedUtility {Ω : Type*}
    (pref : Lottery Ω → Lottery Ω → Prop) (u : Ω → ℝ) : Prop :=
  ∀ L M, pref L M ↔ expectedValue u L ≥ expectedValue u M

/-- Expected-utility representation gives completeness. -/
theorem RepresentsExpectedUtility.completeness {Ω : Type*}
    {pref : Lottery Ω → Lottery Ω → Prop} {u : Ω → ℝ}
    (hrep : RepresentsExpectedUtility pref u) :
    Completeness pref := by
  intro L M
  rcases le_total (expectedValue u M) (expectedValue u L) with hLM | hML
  · exact Or.inl ((hrep L M).2 hLM)
  · exact Or.inr ((hrep M L).2 hML)

/-- Expected-utility representation gives transitivity. -/
theorem RepresentsExpectedUtility.transitivity {Ω : Type*}
    {pref : Lottery Ω → Lottery Ω → Prop} {u : Ω → ℝ}
    (hrep : RepresentsExpectedUtility pref u) :
    Transitivity pref := by
  intro L M N hLM hMN
  exact (hrep L N).2 (le_trans ((hrep M N).1 hMN) ((hrep L M).1 hLM))

/-- Expected-utility representation gives independence. -/
theorem RepresentsExpectedUtility.independence {Ω : Type*} [Finite Ω]
    {pref : Lottery Ω → Lottery Ω → Prop} {u : Ω → ℝ}
    (hrep : RepresentsExpectedUtility pref u) :
    Independence pref := by
  intro L M N t ht0 ht1
  constructor
  · intro hLM
    apply (hrep (mix t (le_of_lt ht0) ht1 L N) (mix t (le_of_lt ht0) ht1 M N)).2
    rw [expectedValue_mix, expectedValue_mix]
    nlinarith [(hrep L M).1 hLM]
  · intro hmix
    apply (hrep L M).2
    have hval := (hrep (mix t (le_of_lt ht0) ht1 L N) (mix t (le_of_lt ht0) ht1 M N)).1 hmix
    rw [expectedValue_mix, expectedValue_mix] at hval
    nlinarith [ht0]

/-- Expected-utility representation gives continuity. -/
theorem RepresentsExpectedUtility.continuity {Ω : Type*} [Finite Ω]
    {pref : Lottery Ω → Lottery Ω → Prop} {u : Ω → ℝ}
    (hrep : RepresentsExpectedUtility pref u) :
    Continuity pref := by
  intro L M N hLM hMN
  let a := expectedValue u L
  let b := expectedValue u M
  let c := expectedValue u N
  have hb_a : b ≤ a := (hrep L M).1 hLM
  have hc_b : c ≤ b := (hrep M N).1 hMN
  by_cases hac : a = c
  · refine ⟨0, by norm_num, by norm_num, ?_⟩
    have hba : b = a := by
      apply le_antisymm hb_a
      linarith
    have hmix : expectedValue u (mix 0 (by norm_num) (by norm_num) L N) = b := by
      rw [expectedValue_mix]
      dsimp [a, b, c] at hac hba
      nlinarith
    constructor
    · exact (hrep M (mix 0 (by norm_num) (by norm_num) L N)).2 (by rw [hmix])
    · exact (hrep (mix 0 (by norm_num) (by norm_num) L N) M).2 (by rw [hmix])
  · have hc_a : c ≤ a := le_trans hc_b hb_a
    have hc_lt_a : c < a := lt_of_le_of_ne hc_a (fun hca => hac hca.symm)
    have hden_pos : 0 < a - c := sub_pos.mpr hc_lt_a
    let t := (b - c) / (a - c)
    have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hc_b) (le_of_lt hden_pos)
    have ht1 : t ≤ 1 := by
      rw [div_le_one (by positivity : 0 < a - c)]
      linarith
    refine ⟨t, ht0, ht1, ?_⟩
    have hcalc : t * a + (1 - t) * c = b := by
      dsimp [t]
      field_simp [ne_of_gt hden_pos]
      ring
    have hmix : expectedValue u (mix t ht0 ht1 L N) = b := by
      rw [expectedValue_mix]
      simpa [a, c] using hcalc
    constructor
    · exact (hrep M (mix t ht0 ht1 L N)).2 (by rw [hmix])
    · exact (hrep (mix t ht0 ht1 L N) M).2 (by rw [hmix])

/-- Preferences represented by expected utility satisfy the vNM axioms. -/
theorem RepresentsExpectedUtility.vnmAxioms {Ω : Type*} [Finite Ω]
    {pref : Lottery Ω → Lottery Ω → Prop} {u : Ω → ℝ}
    (hrep : RepresentsExpectedUtility pref u) :
    Completeness pref ∧ Transitivity pref ∧ Independence pref ∧ Continuity pref :=
  ⟨hrep.completeness, hrep.transitivity, hrep.independence, hrep.continuity⟩

/-- Coordinate probability of an outcome in a lottery, as a real number. -/
noncomputable def probOf {Ω : Type*} (ω : Ω) (L : Lottery Ω) : ℝ :=
  (L ω).toReal

@[simp] theorem probOf_pure_self {Ω : Type*} (ω : Ω) :
    probOf ω (PMF.pure ω : Lottery Ω) = 1 := by
  classical
  simp [probOf]

@[simp] theorem probOf_pure_ne {Ω : Type*} {ω ω' : Ω}
    (h : ω' ≠ ω) :
    probOf ω (PMF.pure ω' : Lottery Ω) = 0 := by
  classical
  simp [probOf, PMF.pure_apply, h.symm]

/-- Expected value of an indicator is the corresponding coordinate
probability. -/
theorem expectedValue_indicator {Ω : Type*} [Finite Ω] [DecidableEq Ω]
    (ω : Ω) (L : Lottery Ω) :
    expectedValue (fun ω' => if ω' = ω then 1 else 0) L = probOf ω L := by
  classical
  letI : Fintype Ω := Fintype.ofFinite Ω
  rw [expectedValue_eq_sum]
  rw [Finset.sum_eq_single ω]
  · simp [probOf]
  · intro b _ hb
    simp [hb]
  · intro h
    exact (h (Finset.mem_univ ω)).elim

@[simp] theorem probOf_mix {Ω : Type*} [Finite Ω]
    (ω : Ω) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (L M : Lottery Ω) :
    probOf ω (mix t ht0 ht1 L M) =
      t * probOf ω L + (1 - t) * probOf ω M := by
  classical
  have h := expectedValue_mix t ht0 ht1 L M
    (fun ω' => if ω' = ω then 1 else 0)
  simpa [expectedValue_indicator] using h

/-- Coordinate probability after binding a finite-target lottery kernel. -/
theorem probOf_bind {ι Ω : Type*} [Finite Ω]
    (w : PMF ι) (K : ι → Lottery Ω) (ω : Ω) :
    probOf ω (w.bind K) = expect w (fun i => probOf ω (K i)) := by
  classical
  have h := expectedValue_bind w K (fun ω' => if ω' = ω then 1 else 0)
  simpa [expectedValue_indicator] using h

/-- The lottery that gives probability `t` to the best outcome and `1 - t` to
the worst outcome. -/
noncomputable def standardLottery {Ω : Type*} (best worst : Ω)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : Lottery Ω :=
  mix t ht0 ht1 (PMF.pure best) (PMF.pure worst)

@[simp] theorem standardLottery_apply_best {Ω : Type*} [Finite Ω]
    {best worst : Ω} (hneq : best ≠ worst)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    probOf best (standardLottery best worst t ht0 ht1) = t := by
  rw [standardLottery, probOf_mix, probOf_pure_self, probOf_pure_ne (Ne.symm hneq)]
  ring

@[simp] theorem standardLottery_apply_worst {Ω : Type*} [Finite Ω]
    {best worst : Ω} (hneq : best ≠ worst)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    probOf worst (standardLottery best worst t ht0 ht1) = 1 - t := by
  rw [standardLottery, probOf_mix, probOf_pure_ne hneq, probOf_pure_self]
  ring

@[simp] theorem standardLottery_apply_ne {Ω : Type*} [Finite Ω]
    {best worst ω : Ω}
    (hbest : ω ≠ best) (hworst : ω ≠ worst)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    probOf ω (standardLottery best worst t ht0 ht1) = 0 := by
  rw [standardLottery, probOf_mix, probOf_pure_ne (Ne.symm hbest), probOf_pure_ne (Ne.symm hworst)]
  ring

/-- Mixing a lottery with itself gives the same lottery. -/
theorem mix_self {Ω : Type*} [Finite Ω]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (L : Lottery Ω) :
    mix t ht0 ht1 L L = L := by
  classical
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro ω
  change probOf ω (mix t ht0 ht1 L L) = probOf ω L
  rw [probOf_mix]
  ring

/-- A zero-weight mixture is its second branch. -/
theorem mix_zero {Ω : Type*} [Finite Ω] (L M : Lottery Ω) :
    mix 0 le_rfl (by norm_num) L M = M := by
  classical
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro ω
  change probOf ω (mix 0 le_rfl (by norm_num) L M) = probOf ω M
  rw [probOf_mix]
  ring

/-- A one-weight mixture is its first branch. -/
theorem mix_one {Ω : Type*} [Finite Ω] (L M : Lottery Ω) :
    mix 1 (by norm_num) le_rfl L M = L := by
  classical
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro ω
  change probOf ω (mix 1 (by norm_num) le_rfl L M) = probOf ω L
  rw [probOf_mix]
  ring

/-- Swapping mixture branches replaces the weight by its complement. -/
theorem mix_swap {Ω : Type*} [Finite Ω]
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (L M : Lottery Ω) :
    mix t ht0 ht1 L M =
      mix (1 - t) (sub_nonneg.mpr ht1) (by linarith) M L := by
  classical
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro ω
  change probOf ω (mix t ht0 ht1 L M) =
    probOf ω (mix (1 - t) (sub_nonneg.mpr ht1) (by linarith) M L)
  rw [probOf_mix, probOf_mix]
  ring

/-- The standard lottery with best probability `1` is the best point mass. -/
theorem standardLottery_one {Ω : Type*} [Finite Ω]
    {best worst : Ω} (hneq : best ≠ worst) :
    standardLottery best worst 1 (by norm_num) le_rfl = PMF.pure best := by
  classical
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro ω
  by_cases hbest : ω = best
  · subst ω
    change probOf best (standardLottery best worst 1 (by norm_num) le_rfl) =
      probOf best (PMF.pure best)
    simp [hneq]
  · change probOf ω (standardLottery best worst 1 (by norm_num) le_rfl) =
      probOf ω (PMF.pure best)
    by_cases hworst : ω = worst
    · subst ω
      simp [standardLottery_apply_worst hneq, probOf_pure_ne hneq]
    · rw [standardLottery_apply_ne hbest hworst, probOf_pure_ne (Ne.symm hbest)]

/-- The standard lottery with best probability `0` is the worst point mass. -/
theorem standardLottery_zero {Ω : Type*} [Finite Ω]
    {best worst : Ω} (hneq : best ≠ worst) :
    standardLottery best worst 0 le_rfl (by norm_num) = PMF.pure worst := by
  classical
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro ω
  by_cases hbest : ω = best
  · subst ω
    change probOf best (standardLottery best worst 0 le_rfl (by norm_num)) =
      probOf best (PMF.pure worst)
    simp [standardLottery_apply_best hneq, probOf_pure_ne (Ne.symm hneq)]
  · change probOf ω (standardLottery best worst 0 le_rfl (by norm_num)) =
      probOf ω (PMF.pure worst)
    by_cases hworst : ω = worst
    · subst ω
      simp [hneq]
    · rw [standardLottery_apply_ne hbest hworst, probOf_pure_ne (Ne.symm hworst)]

/-- If `t < 1` and `t ≤ s`, the standard lottery with best probability `s`
is a mixture of `best` with the standard lottery at `t`. -/
theorem standardLottery_eq_mix_best_standard {Ω : Type*} [Finite Ω]
    {best worst : Ω} (hneq : best ≠ worst)
    {s t : ℝ} (ht0 : 0 ≤ t) (hst : t ≤ s) (hs1 : s ≤ 1) (ht1lt : t < 1) :
    standardLottery best worst s (le_trans ht0 hst) hs1 =
      mix ((s - t) / (1 - t))
        (div_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr (le_of_lt ht1lt)))
        (by
          rw [div_le_one (sub_pos.mpr ht1lt)]
          linarith)
        (PMF.pure best)
        (standardLottery best worst t ht0 (le_of_lt ht1lt)) := by
  classical
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro ω
  set a : ℝ := (s - t) / (1 - t)
  have hden : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht1lt)
  have ha_best : a + (1 - a) * t = s := by
    dsimp [a]
    field_simp [hden]
    ring
  have ha_worst : (1 - a) * (1 - t) = 1 - s := by
    dsimp [a]
    field_simp [hden]
    ring
  by_cases hbest : ω = best
  · subst ω
    change probOf best (standardLottery best worst s (le_trans ht0 hst) hs1) =
      probOf best (mix a _ _ (PMF.pure best)
        (standardLottery best worst t ht0 (le_of_lt ht1lt)))
    rw [standardLottery_apply_best hneq, probOf_mix, probOf_pure_self,
      standardLottery_apply_best hneq]
    nlinarith [ha_best]
  · by_cases hworst : ω = worst
    · subst ω
      change probOf worst (standardLottery best worst s (le_trans ht0 hst) hs1) =
        probOf worst (mix a _ _ (PMF.pure best)
          (standardLottery best worst t ht0 (le_of_lt ht1lt)))
      rw [standardLottery_apply_worst hneq, probOf_mix, probOf_pure_ne hneq,
        standardLottery_apply_worst hneq]
      nlinarith [ha_worst]
    · change probOf ω (standardLottery best worst s (le_trans ht0 hst) hs1) =
        probOf ω (mix a _ _ (PMF.pure best)
          (standardLottery best worst t ht0 (le_of_lt ht1lt)))
      rw [standardLottery_apply_ne hbest hworst, probOf_mix, probOf_pure_ne (Ne.symm hbest),
        standardLottery_apply_ne hbest hworst]
      ring

/-- If `s < 1` and `s ≤ t`, the standard lottery with best probability `t`
is a mixture of `best` with the standard lottery at `s`. -/
theorem standardLottery_eq_mix_best_standard_of_le {Ω : Type*} [Finite Ω]
    {best worst : Ω} (hneq : best ≠ worst)
    {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht1 : t ≤ 1) (hs1lt : s < 1) :
    standardLottery best worst t (le_trans hs0 hst) ht1 =
      mix ((t - s) / (1 - s))
        (div_nonneg (sub_nonneg.mpr hst) (sub_nonneg.mpr (le_of_lt hs1lt)))
        (by
          rw [div_le_one (sub_pos.mpr hs1lt)]
          linarith)
        (PMF.pure best)
        (standardLottery best worst s hs0 (le_of_lt hs1lt)) := by
  exact standardLottery_eq_mix_best_standard hneq hs0 hst ht1 hs1lt

/-- Binary independence orders nondegenerate standard best/worst lotteries by
their probability on the best outcome. -/
theorem standardLottery_order_of_independence {Ω : Type*} [Finite Ω]
    {pref : Lottery Ω → Lottery Ω → Prop}
    (hcomplete : Completeness pref) (hind : Independence pref)
    {best worst : Ω} (hbest_worst : pref (PMF.pure best) (PMF.pure worst))
    (hnot_worst_best : ¬ pref (PMF.pure worst) (PMF.pure best))
    (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    pref (standardLottery best worst s hs0 hs1)
      (standardLottery best worst t ht0 ht1) ↔ s ≥ t := by
  have hneq : best ≠ worst := by
    intro h
    subst h
    exact hnot_worst_best hbest_worst
  have hrefl : ∀ L : Lottery Ω, pref L L := fun L => (hcomplete L L).elim id id
  have hbest_pref_standard : ∀ (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1),
      pref (PMF.pure best) (standardLottery best worst q hq0 hq1) := by
    intro q hq0 hq1
    rcases eq_or_lt_of_le hq1 with hqeq | hqlt
    · subst q
      rw [standardLottery_one hneq]
      exact hrefl (PMF.pure best)
    · rcases eq_or_lt_of_le hq0 with hqzero | hqpos
      · subst q
        rw [standardLottery_zero hneq]
        exact hbest_worst
      · have hmix_best :
            mix (1 - q) (sub_nonneg.mpr hq1) (by linarith)
                (PMF.pure best) (PMF.pure best) = PMF.pure best :=
          mix_self (1 - q) (sub_nonneg.mpr hq1) (by linarith) (PMF.pure best)
        have hmix_std :
            mix (1 - q) (sub_nonneg.mpr hq1) (by linarith)
                (PMF.pure worst) (PMF.pure best) =
              standardLottery best worst q hq0 hq1 := by
          classical
          apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
          intro ω
          by_cases hωbest : ω = best
          · subst ω
            change probOf best (mix (1 - q) _ _ (PMF.pure worst) (PMF.pure best)) =
              probOf best (standardLottery best worst q hq0 hq1)
            rw [probOf_mix, probOf_pure_ne (Ne.symm hneq), probOf_pure_self,
              standardLottery_apply_best hneq]
            ring
          · by_cases hωworst : ω = worst
            · subst ω
              change probOf worst (mix (1 - q) _ _ (PMF.pure worst) (PMF.pure best)) =
                probOf worst (standardLottery best worst q hq0 hq1)
              rw [probOf_mix, probOf_pure_self, probOf_pure_ne hneq,
                standardLottery_apply_worst hneq]
              ring
            · change probOf ω (mix (1 - q) _ _ (PMF.pure worst) (PMF.pure best)) =
                probOf ω (standardLottery best worst q hq0 hq1)
              rw [probOf_mix, probOf_pure_ne (Ne.symm hωworst), probOf_pure_ne (Ne.symm hωbest),
                standardLottery_apply_ne hωbest hωworst]
              ring
        have h := (hind (PMF.pure best) (PMF.pure worst) (PMF.pure best)
          (1 - q) (sub_pos.mpr hqlt) (by linarith)).mp hbest_worst
        simpa [hmix_best, hmix_std] using h
  constructor
  · intro hpref
    by_contra hnot
    have hlt : s < t := lt_of_not_ge hnot
    have hs1lt : s < 1 := lt_of_lt_of_le hlt ht1
    let a : ℝ := (t - s) / (1 - s)
    have ha0 : 0 ≤ a := div_nonneg (sub_nonneg.mpr (le_of_lt hlt))
      (sub_nonneg.mpr (le_of_lt hs1lt))
    have ha1 : a ≤ 1 := by
      dsimp [a]
      rw [div_le_one (sub_pos.mpr hs1lt)]
      linarith
    have hmix_std :
        standardLottery best worst t (le_trans hs0 (le_of_lt hlt)) ht1 =
          mix a ha0 ha1 (PMF.pure best)
            (standardLottery best worst s hs0 (le_of_lt hs1lt)) := by
      exact standardLottery_eq_mix_best_standard_of_le hneq hs0 (le_of_lt hlt) ht1 hs1lt
    have hmix_self :
        mix a ha0 ha1
            (standardLottery best worst s hs0 (le_of_lt hs1lt))
            (standardLottery best worst s hs0 (le_of_lt hs1lt)) =
          standardLottery best worst s hs0 (le_of_lt hs1lt) :=
      mix_self a ha0 ha1 (standardLottery best worst s hs0 (le_of_lt hs1lt))
    have hbase : pref (standardLottery best worst s hs0 (le_of_lt hs1lt)) (PMF.pure best) := by
      have h := (hind
        (standardLottery best worst s hs0 (le_of_lt hs1lt))
        (PMF.pure best)
        (standardLottery best worst s hs0 (le_of_lt hs1lt))
        a (by
          dsimp [a]
          exact div_pos (sub_pos.mpr hlt) (sub_pos.mpr hs1lt))
        ha1).mpr ?_
      · exact h
      · simpa [hmix_self, hmix_std] using hpref
    rcases eq_or_lt_of_le hs0 with hs_eq | hs_pos
    · subst s
      rw [standardLottery_zero hneq] at hbase
      exact hnot_worst_best hbase
    · have hmix_worst :
          mix (1 - s) (sub_nonneg.mpr hs1) (by linarith)
              (PMF.pure worst) (PMF.pure best) =
            standardLottery best worst s hs0 hs1 := by
        classical
        apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
        intro ω
        by_cases hωbest : ω = best
        · subst ω
          change probOf best (mix (1 - s) _ _ (PMF.pure worst) (PMF.pure best)) =
            probOf best (standardLottery best worst s hs0 hs1)
          rw [probOf_mix, probOf_pure_ne (Ne.symm hneq), probOf_pure_self,
            standardLottery_apply_best hneq]
          ring
        · by_cases hωworst : ω = worst
          · subst ω
            change probOf worst (mix (1 - s) _ _ (PMF.pure worst) (PMF.pure best)) =
              probOf worst (standardLottery best worst s hs0 hs1)
            rw [probOf_mix, probOf_pure_self, probOf_pure_ne hneq,
              standardLottery_apply_worst hneq]
            ring
          · change probOf ω (mix (1 - s) _ _ (PMF.pure worst) (PMF.pure best)) =
              probOf ω (standardLottery best worst s hs0 hs1)
            rw [probOf_mix, probOf_pure_ne (Ne.symm hωworst), probOf_pure_ne (Ne.symm hωbest),
              standardLottery_apply_ne hωbest hωworst]
            ring
      have hmix_best :
          mix (1 - s) (sub_nonneg.mpr hs1) (by linarith)
              (PMF.pure best) (PMF.pure best) =
            PMF.pure best :=
        mix_self (1 - s) (sub_nonneg.mpr hs1) (by linarith) (PMF.pure best)
      have hworst_best := (hind (PMF.pure worst) (PMF.pure best) (PMF.pure best)
        (1 - s) (sub_pos.mpr hs1lt) (by linarith)).mpr (by
          simpa [hmix_worst, hmix_best] using hbase)
      exact hnot_worst_best hworst_best
  · intro hst
    rcases eq_or_lt_of_le hst with hst_eq | hlt_ts
    · subst s
      exact hrefl (standardLottery best worst t ht0 ht1)
    · rcases eq_or_lt_of_le ht1 with ht_eq | ht_lt_one
      · subst t
        have hs_eq : s = 1 := le_antisymm hs1 hst
        subst s
        exact hrefl (standardLottery best worst 1 (by norm_num) le_rfl)
      · let a : ℝ := (s - t) / (1 - t)
        have ha0 : 0 ≤ a := div_nonneg (sub_nonneg.mpr hst)
          (sub_nonneg.mpr (le_of_lt ht_lt_one))
        have ha1 : a ≤ 1 := by
          dsimp [a]
          rw [div_le_one (sub_pos.mpr ht_lt_one)]
          linarith
        have hmix_s :
            standardLottery best worst s (le_trans ht0 hst) hs1 =
              mix a ha0 ha1 (PMF.pure best)
                (standardLottery best worst t ht0 (le_of_lt ht_lt_one)) := by
          exact standardLottery_eq_mix_best_standard hneq ht0 hst hs1 ht_lt_one
        have hmix_t :
            mix a ha0 ha1
                (standardLottery best worst t ht0 (le_of_lt ht_lt_one))
                (standardLottery best worst t ht0 (le_of_lt ht_lt_one)) =
              standardLottery best worst t ht0 (le_of_lt ht_lt_one) :=
          mix_self a ha0 ha1 (standardLottery best worst t ht0 (le_of_lt ht_lt_one))
        have hbest_std := hbest_pref_standard t ht0 (le_of_lt ht_lt_one)
        have h := (hind (PMF.pure best)
          (standardLottery best worst t ht0 (le_of_lt ht_lt_one))
          (standardLottery best worst t ht0 (le_of_lt ht_lt_one))
          a (by
            dsimp [a]
            exact div_pos (sub_pos.mpr hlt_ts) (sub_pos.mpr ht_lt_one))
          ha1).mp hbest_std
        simpa [hmix_s, hmix_t] using h

/-- A two-branch compound lottery is the corresponding binary mixture, with
the probability of `true` as the mixture weight. -/
theorem bind_bool_eq_mix {Ω : Type*} [Finite Ω]
    (coin : PMF Bool) (Ltrue Lfalse : Lottery Ω) :
    coin.bind (fun b => if b then Ltrue else Lfalse) =
      mix (coin true).toReal ENNReal.toReal_nonneg
        ((ENNReal.toReal_le_toReal (PMF.apply_ne_top coin true) (by norm_num)).mpr
          (PMF.coe_le_one coin true))
        Ltrue Lfalse := by
  classical
  let ht1 : (coin true).toReal ≤ 1 :=
    (ENNReal.toReal_le_toReal (PMF.apply_ne_top coin true) (by norm_num)).mpr
      (PMF.coe_le_one coin true)
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro ω
  change probOf ω (coin.bind (fun b => if b then Ltrue else Lfalse)) =
    probOf ω (mix (coin true).toReal ENNReal.toReal_nonneg ht1 Ltrue Lfalse)
  rw [probOf_bind, probOf_mix]
  rw [show expect coin (fun b => probOf ω (if b then Ltrue else Lfalse)) =
      ∑ b : Bool, (coin b).toReal * probOf ω (if b then Ltrue else Lfalse) by
        exact expect_eq_sum coin _]
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_true, if_false]
  have hsum := Math.Probability.pmf_toReal_sum_one coin
  rw [Fintype.sum_bool] at hsum
  have hfalse : (coin false).toReal = 1 - (coin true).toReal := by
    nlinarith [hsum]
  rw [hfalse]

/-- Binary independence gives compound substitution for two-branch lotteries. -/
theorem bool_compoundIndifference_of_independence {Ω : Type*} [Finite Ω]
    {pref : Lottery Ω → Lottery Ω → Prop}
    (htrans : Transitivity pref) (hind : Independence pref)
    (coin : PMF Bool) (L M : Bool → Lottery Ω)
    (h : ∀ b, indiff pref (L b) (M b)) :
    indiff pref (coin.bind L) (coin.bind M) := by
  classical
  let t : ℝ := (coin true).toReal
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have ht1 : t ≤ 1 :=
    (ENNReal.toReal_le_toReal (PMF.apply_ne_top coin true) (by norm_num)).mpr
      (PMF.coe_le_one coin true)
  have hL : coin.bind L = mix t ht0 ht1 (L true) (L false) := by
    rw [show L = (fun b => if b then L true else L false) by
      funext b
      cases b <;> simp]
    simpa [t] using bind_bool_eq_mix coin (L true) (L false)
  have hM : coin.bind M = mix t ht0 ht1 (M true) (M false) := by
    rw [show M = (fun b => if b then M true else M false) by
      funext b
      cases b <;> simp]
    simpa [t] using bind_bool_eq_mix coin (M true) (M false)
  by_cases htpos : 0 < t
  · constructor
    · rw [hL, hM]
      by_cases htlt1 : t < 1
      · have htrue :
            pref (mix t ht0 ht1 (L true) (L false))
              (mix t ht0 ht1 (M true) (L false)) :=
          (hind (L true) (M true) (L false) t htpos ht1).mp (h true).1
        have hfalse' :
            pref (mix (1 - t) (sub_nonneg.mpr ht1) (by linarith) (L false) (M true))
              (mix (1 - t) (sub_nonneg.mpr ht1) (by linarith) (M false) (M true)) :=
          (hind (L false) (M false) (M true) (1 - t)
            (sub_pos.mpr htlt1) (by linarith)).mp (h false).1
        have hfalse :
            pref (mix t ht0 ht1 (M true) (L false))
              (mix t ht0 ht1 (M true) (M false)) := by
          simpa [(mix_swap t ht0 ht1 (M true) (L false)).symm,
            (mix_swap t ht0 ht1 (M true) (M false)).symm] using hfalse'
        exact htrans _ _ _ htrue hfalse
      · have htone : t = 1 := le_antisymm ht1 (le_of_not_gt htlt1)
        simpa [htone, mix_one] using (h true).1
    · rw [hL, hM]
      by_cases htlt1 : t < 1
      · have htrue :
            pref (mix t ht0 ht1 (M true) (M false))
              (mix t ht0 ht1 (L true) (M false)) :=
          (hind (M true) (L true) (M false) t htpos ht1).mp (h true).2
        have hfalse' :
            pref (mix (1 - t) (sub_nonneg.mpr ht1) (by linarith) (M false) (L true))
              (mix (1 - t) (sub_nonneg.mpr ht1) (by linarith) (L false) (L true)) :=
          (hind (M false) (L false) (L true) (1 - t)
            (sub_pos.mpr htlt1) (by linarith)).mp (h false).2
        have hfalse :
            pref (mix t ht0 ht1 (L true) (M false))
              (mix t ht0 ht1 (L true) (L false)) := by
          simpa [(mix_swap t ht0 ht1 (L true) (M false)).symm,
            (mix_swap t ht0 ht1 (L true) (L false)).symm] using hfalse'
        exact htrans _ _ _ htrue hfalse
      · have htone : t = 1 := le_antisymm ht1 (le_of_not_gt htlt1)
        simpa [htone, mix_one] using (h true).2
  · have htzero : t = 0 := le_antisymm (le_of_not_gt htpos) ht0
    have hLzero : coin.bind L = L false := by
      refine hL.trans ?_
      apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
      intro ω
      change probOf ω (mix t ht0 ht1 (L true) (L false)) = probOf ω (L false)
      rw [probOf_mix, htzero]
      ring
    have hMzero : coin.bind M = M false := by
      refine hM.trans ?_
      apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
      intro ω
      change probOf ω (mix t ht0 ht1 (M true) (M false)) = probOf ω (M false)
      rw [probOf_mix, htzero]
      ring
    simpa [hLzero, hMzero] using h false

/-- Expected utility is nonnegative when the utility index is pointwise
nonnegative. -/
theorem expectedValue_nonneg_of_nonneg {Ω : Type*} [Finite Ω]
    (L : Lottery Ω) {u : Ω → ℝ} (hu : ∀ ω, 0 ≤ u ω) :
    0 ≤ expectedValue u L := by
  have h := expectedValue_mono L (u := fun _ : Ω => 0) (v := u) hu
  simpa using h

/-- Expected utility is at most one when the utility index is pointwise at most
one. -/
theorem expectedValue_le_one_of_le_one {Ω : Type*} [Finite Ω]
    (L : Lottery Ω) {u : Ω → ℝ} (hu : ∀ ω, u ω ≤ 1) :
    expectedValue u L ≤ 1 := by
  have h := expectedValue_mono L (u := u) (v := fun _ : Ω => 1) hu
  simpa using h

/-- A compound lottery over standard best/worst lotteries is the standard
lottery whose best-outcome probability is the expected inner probability. -/
theorem bind_standardLottery_eq_standard_expectedValue {Ω : Type*}
    [Finite Ω] {best worst : Ω} (hneq : best ≠ worst)
    (L : Lottery Ω) (u : Ω → ℝ)
    (hu0 : ∀ ω, 0 ≤ u ω) (hu1 : ∀ ω, u ω ≤ 1) :
    L.bind (fun ω => standardLottery best worst (u ω) (hu0 ω) (hu1 ω)) =
      standardLottery best worst (expectedValue u L)
        (expectedValue_nonneg_of_nonneg L hu0)
        (expectedValue_le_one_of_le_one L hu1) := by
  classical
  apply Math.ProbabilityMassFunction.eq_of_forall_toReal_eq
  intro ω
  change probOf ω (L.bind fun x => standardLottery best worst (u x) (hu0 x) (hu1 x)) =
    probOf ω (standardLottery best worst (expectedValue u L)
      (expectedValue_nonneg_of_nonneg L hu0)
      (expectedValue_le_one_of_le_one L hu1))
  rw [probOf_bind]
  by_cases hbest : ω = best
  · subst ω
    rw [standardLottery_apply_best hneq]
    have hinner :
        (fun x => probOf best (standardLottery best worst (u x) (hu0 x) (hu1 x))) = u := by
      funext x
      rw [standardLottery_apply_best hneq]
    rw [hinner]
    rfl
  · by_cases hworst : ω = worst
    · subst ω
      rw [standardLottery_apply_worst hneq]
      have hinner :
          (fun x => probOf worst (standardLottery best worst (u x) (hu0 x) (hu1 x))) =
            fun x => 1 - u x := by
        funext x
        rw [standardLottery_apply_worst hneq]
      rw [hinner]
      change expectedValue (fun x => 1 - u x) L = 1 - expectedValue u L
      rw [expectedValue_one_sub]
    · simp [hbest, hworst]

/-- Finite compound-lottery substitution for indifference. This is the
relation-level finite sure-thing principle needed by the representation proof. -/
def CompoundIndifference {Ω : Type u}
    (pref : Lottery Ω → Lottery Ω → Prop) : Prop :=
  ∀ {ι : Type u} [Finite ι] (w : PMF ι) (L M : ι → Lottery Ω),
    (∀ i, indiff pref (L i) (M i)) →
      indiff pref (w.bind L) (w.bind M)

/-- Binary independence implies finite compound-lottery substitution. -/
theorem compoundIndifference_of_independence {Ω : Type u} [Finite Ω]
    {pref : Lottery Ω → Lottery Ω → Prop}
    (htrans : Transitivity pref) (hind : Independence pref) :
    CompoundIndifference pref := by
  classical
  let P : Type u → Prop := fun ι =>
    ∀ [Finite ι] (w : PMF ι) (L M : ι → Lottery Ω),
      (∀ i, indiff pref (L i) (M i)) →
        indiff pref (w.bind L) (w.bind M)
  have hP : ∀ (ι : Type u) [Finite ι], P ι := by
    intro ι _
    refine Finite.induction_empty_option (P := P) ?equiv ?empty ?option ι
    · intro α β e hα _ w L M h
      let wα : PMF α := w.map e.symm
      haveI : Finite α := Finite.of_equiv β e.symm
      have hα' := hα (w := wα) (L := fun a => L (e a)) (M := fun a => M (e a))
        (fun a => h (e a))
      have hL : wα.bind (fun a => L (e a)) = w.bind L := by
        unfold wα
        rw [PMF.bind_map]
        congr 1
        funext b
        simp
      have hM : wα.bind (fun a => M (e a)) = w.bind M := by
        unfold wα
        rw [PMF.bind_map]
        congr 1
        funext b
        simp
      simpa [hL, hM] using hα'
    · intro _ w L M _h
      obtain ⟨i, _hi⟩ := w.support_nonempty
      cases i
    · intro α _ hα _ w L M h
      by_cases hempty : IsEmpty α
      · haveI : Subsingleton (Option α) := by
          refine ⟨?_⟩
          intro x y
          cases x with
          | none =>
              cases y with
              | none => rfl
              | some a => exact (hempty.false a).elim
          | some a => exact (hempty.false a).elim
        have hL : w.bind L = L none := by
          rw [show L = fun _ : Option α => L none by
            funext x
            exact congrArg L (Subsingleton.elim x none)]
          exact PMF.bind_const w (L none)
        have hM : w.bind M = M none := by
          rw [show M = fun _ : Option α => M none by
            funext x
            exact congrArg M (Subsingleton.elim x none)]
          exact PMF.bind_const w (M none)
        simpa [hL, hM] using h none
      · haveI : Nonempty α := not_isEmpty_iff.mp hempty
        let proj : Option α → Bool := fun x => x.isNone
        let coin : PMF Bool := Math.ProbabilityMassFunction.pushforward w proj
        let tail : PMF α :=
          (Math.ProbabilityMassFunction.condOn w proj false).map
            (fun x => x.getD (Classical.choice ‹Nonempty α›))
        let Lbranch : Bool → Lottery Ω := fun b =>
          if b then L none else tail.bind (fun a => L (some a))
        let Mbranch : Bool → Lottery Ω := fun b =>
          if b then M none else tail.bind (fun a => M (some a))
        have htrueL (hb : coin true ≠ 0) :
            (Math.ProbabilityMassFunction.condOn w proj true).bind L = L none := by
          rw [show (Math.ProbabilityMassFunction.condOn w proj true).bind L =
              (Math.ProbabilityMassFunction.condOn w proj true).bind
                (fun _ : Option α => L none) by
            apply Math.ProbabilityMassFunction.bind_congr_on_support
            intro x hx
            have hproj := Math.ProbabilityMassFunction.condOn_support_project
              (μ := w) (proj := proj) (b := true) (hb := hb) hx
            cases x with
            | none => rfl
            | some a =>
                simp [proj] at hproj]
          exact PMF.bind_const _ _
        have htrueM (hb : coin true ≠ 0) :
            (Math.ProbabilityMassFunction.condOn w proj true).bind M = M none := by
          rw [show (Math.ProbabilityMassFunction.condOn w proj true).bind M =
              (Math.ProbabilityMassFunction.condOn w proj true).bind
                (fun _ : Option α => M none) by
            apply Math.ProbabilityMassFunction.bind_congr_on_support
            intro x hx
            have hproj := Math.ProbabilityMassFunction.condOn_support_project
              (μ := w) (proj := proj) (b := true) (hb := hb) hx
            cases x with
            | none => rfl
            | some a =>
                simp [proj] at hproj]
          exact PMF.bind_const _ _
        have hfalseL (hb : coin false ≠ 0) :
            (Math.ProbabilityMassFunction.condOn w proj false).bind L =
              tail.bind (fun a => L (some a)) := by
          symm
          unfold tail
          rw [PMF.bind_map]
          apply Math.ProbabilityMassFunction.bind_congr_on_support
          intro x hx
          have hproj := Math.ProbabilityMassFunction.condOn_support_project
            (μ := w) (proj := proj) (b := false) (hb := hb) hx
          cases x with
          | none =>
              simp [proj] at hproj
          | some a =>
              rfl
        have hfalseM (hb : coin false ≠ 0) :
            (Math.ProbabilityMassFunction.condOn w proj false).bind M =
              tail.bind (fun a => M (some a)) := by
          symm
          unfold tail
          rw [PMF.bind_map]
          apply Math.ProbabilityMassFunction.bind_congr_on_support
          intro x hx
          have hproj := Math.ProbabilityMassFunction.condOn_support_project
            (μ := w) (proj := proj) (b := false) (hb := hb) hx
          cases x with
          | none =>
              simp [proj] at hproj
          | some a =>
              rfl
        have hLdecomp : w.bind L = coin.bind Lbranch := by
          calc
            w.bind L =
                ((Math.ProbabilityMassFunction.pushforward w proj).bind
                  (fun b => Math.ProbabilityMassFunction.condOn w proj b)).bind L := by
                    rw [← Math.ProbabilityMassFunction.bind_pushforward_condOn_pure
                      (μ := w) (proj := proj)]
            _ = coin.bind (fun b =>
                  (Math.ProbabilityMassFunction.condOn w proj b).bind L) := by
                    rw [PMF.bind_bind]
            _ = coin.bind Lbranch := by
                    apply Math.ProbabilityMassFunction.bind_congr_of_ne_zero
                    intro b hb
                    cases b
                    · simpa [Lbranch] using hfalseL hb
                    · simpa [Lbranch] using htrueL hb
        have hMdecomp : w.bind M = coin.bind Mbranch := by
          calc
            w.bind M =
                ((Math.ProbabilityMassFunction.pushforward w proj).bind
                  (fun b => Math.ProbabilityMassFunction.condOn w proj b)).bind M := by
                    rw [← Math.ProbabilityMassFunction.bind_pushforward_condOn_pure
                      (μ := w) (proj := proj)]
            _ = coin.bind (fun b =>
                  (Math.ProbabilityMassFunction.condOn w proj b).bind M) := by
                    rw [PMF.bind_bind]
            _ = coin.bind Mbranch := by
                    apply Math.ProbabilityMassFunction.bind_congr_of_ne_zero
                    intro b hb
                    cases b
                    · simpa [Mbranch] using hfalseM hb
                    · simpa [Mbranch] using htrueM hb
        have htail :
            indiff pref (tail.bind (fun a => L (some a)))
              (tail.bind (fun a => M (some a))) :=
          hα (w := tail) (L := fun a => L (some a)) (M := fun a => M (some a))
            (fun a => h (some a))
        have hbranches : ∀ b, indiff pref (Lbranch b) (Mbranch b) := by
          intro b
          cases b <;> simp [Lbranch, Mbranch, h, htail]
        have hbool := bool_compoundIndifference_of_independence htrans hind
          coin Lbranch Mbranch hbranches
        simpa [hLdecomp, hMdecomp] using hbool
  intro ι _ w L M h
  exact hP ι w L M h

/-- If every pure prize has a best/worst certainty equivalent, finite compound
substitution preserves indifference, and standard best/worst lotteries are
ordered by the probability of the best prize, then the preference is represented
by expected utility. -/
theorem representsExpectedUtility_of_standardLottery_certaintyEquivalents {Ω : Type*}
    [Finite Ω] {pref : Lottery Ω → Lottery Ω → Prop}
    {best worst : Ω} (hneq : best ≠ worst) (u : Ω → ℝ)
    (hu0 : ∀ ω, 0 ≤ u ω) (hu1 : ∀ ω, u ω ≤ 1)
    (htrans : Transitivity pref)
    (hcompound : CompoundIndifference pref)
    (hpure : ∀ ω,
      indiff pref (PMF.pure ω) (standardLottery best worst (u ω) (hu0 ω) (hu1 ω)))
    (hstandard : ∀ (s t : ℝ)
      (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
        pref (standardLottery best worst s hs0 hs1)
          (standardLottery best worst t ht0 ht1) ↔ s ≥ t) :
    RepresentsExpectedUtility pref u := by
  intro L M
  let std (K : Lottery Ω) : Lottery Ω :=
    standardLottery best worst (expectedValue u K)
      (expectedValue_nonneg_of_nonneg K hu0)
      (expectedValue_le_one_of_le_one K hu1)
  have hstd_indiff : ∀ K : Lottery Ω, indiff pref K (std K) := by
    intro K
    have h := hcompound (ι := Ω) K (fun ω : Ω => PMF.pure ω)
      (fun ω => standardLottery best worst (u ω) (hu0 ω) (hu1 ω)) hpure
    simpa [std, bind_standardLottery_eq_standard_expectedValue hneq K u hu0 hu1]
      using h
  constructor
  · intro hLM
    have hL := hstd_indiff L
    have hM := hstd_indiff M
    have h_std_L_M : pref (std L) M := htrans (std L) L M hL.2 hLM
    have h_std : pref (std L) (std M) := htrans (std L) M (std M) h_std_L_M hM.1
    exact (hstandard (expectedValue u L) (expectedValue u M)
      (expectedValue_nonneg_of_nonneg L hu0)
      (expectedValue_le_one_of_le_one L hu1)
      (expectedValue_nonneg_of_nonneg M hu0)
      (expectedValue_le_one_of_le_one M hu1)).1 h_std
  · intro hEU
    have hL := hstd_indiff L
    have hM := hstd_indiff M
    have h_std : pref (std L) (std M) :=
      (hstandard (expectedValue u L) (expectedValue u M)
        (expectedValue_nonneg_of_nonneg L hu0)
        (expectedValue_le_one_of_le_one L hu1)
        (expectedValue_nonneg_of_nonneg M hu0)
        (expectedValue_le_one_of_le_one M hu1)).2 hEU
    have h_L_stdM : pref L (std M) := htrans L (std L) (std M) hL.1 h_std
    exact htrans L (std M) M h_L_stdM hM.2

/-- A converse representation theorem once the finite-compound substitution
and standard-lottery ordering steps are available. The binary vNM axioms provide
best and worst pure outcomes and the certainty equivalents; the two remaining
hypotheses are the finite-mixture consequences normally derived from
independence in the textbook proof. -/
theorem exists_representsExpectedUtility_of_compoundIndifference_and_standardLottery_order
    {Ω : Type*} [Finite Ω] [Nonempty Ω]
    {pref : Lottery Ω → Lottery Ω → Prop}
    (hcomplete : Completeness pref)
    (htrans : Transitivity pref)
    (hcont : Continuity pref)
    (hcompound : CompoundIndifference pref)
    (hstandard : ∀ {best worst : Ω},
      pref (PMF.pure best) (PMF.pure worst) →
      ¬ pref (PMF.pure worst) (PMF.pure best) →
      ∀ (s t : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
        pref (standardLottery best worst s hs0 hs1)
          (standardLottery best worst t ht0 ht1) ↔ s ≥ t) :
    ∃ u : Ω → ℝ, RepresentsExpectedUtility pref u := by
  classical
  obtain ⟨best, hbest⟩ :=
    Math.exists_greatest_of_complete_transitive (α := Ω)
      (fun a b : Ω => pref (PMF.pure a) (PMF.pure b))
      (fun a b => hcomplete (PMF.pure a) (PMF.pure b))
      (fun a b c hab hbc => htrans (PMF.pure a) (PMF.pure b) (PMF.pure c) hab hbc)
  obtain ⟨worst, hworst⟩ :=
    Math.exists_least_of_complete_transitive (α := Ω)
      (fun a b : Ω => pref (PMF.pure a) (PMF.pure b))
      (fun a b => hcomplete (PMF.pure a) (PMF.pure b))
      (fun a b c hab hbc => htrans (PMF.pure a) (PMF.pure b) (PMF.pure c) hab hbc)
  by_cases hdeg : pref (PMF.pure worst) (PMF.pure best)
  · refine ⟨fun _ => 0, ?_⟩
    have hpure_best : ∀ ω, indiff pref (PMF.pure ω) (PMF.pure best) := by
      intro ω
      constructor
      · exact htrans (PMF.pure ω) (PMF.pure worst) (PMF.pure best) (hworst ω) hdeg
      · exact hbest ω
    have hlot_best : ∀ L : Lottery Ω, indiff pref L (PMF.pure best) := by
      intro L
      have h := hcompound (ι := Ω) L (fun ω : Ω => PMF.pure ω)
        (fun _ : Ω => PMF.pure best) hpure_best
      simpa using h
    intro L M
    constructor
    · intro _
      simp [expectedValue]
    · intro _
      exact htrans L (PMF.pure best) M (hlot_best L).1 (hlot_best M).2
  · have hbest_worst : pref (PMF.pure best) (PMF.pure worst) := hbest worst
    have hneq : best ≠ worst := by
      intro heq
      have hsame : pref (PMF.pure best) (PMF.pure best) :=
        (hcomplete (PMF.pure best) (PMF.pure best)).elim id id
      exact hdeg (by simpa [heq] using hsame)
    have hce : ∀ ω : Ω,
        ∃ (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1),
          indiff pref (PMF.pure ω) (standardLottery best worst t ht0 ht1) := by
      intro ω
      exact hcont (PMF.pure best) (PMF.pure ω) (PMF.pure worst)
        (hbest ω) (hworst ω)
    let u : Ω → ℝ := fun ω => (hce ω).choose
    have hu0 : ∀ ω, 0 ≤ u ω := by
      intro ω
      exact (hce ω).choose_spec.choose
    have hu1 : ∀ ω, u ω ≤ 1 := by
      intro ω
      exact (hce ω).choose_spec.choose_spec.choose
    have hpure : ∀ ω,
        indiff pref (PMF.pure ω) (standardLottery best worst (u ω) (hu0 ω) (hu1 ω)) := by
      intro ω
      exact (hce ω).choose_spec.choose_spec.choose_spec
    exact ⟨u,
      representsExpectedUtility_of_standardLottery_certaintyEquivalents
        hneq u hu0 hu1 htrans hcompound hpure
        (hstandard hbest_worst hdeg)⟩

/-- A converse representation theorem once finite compound-lottery substitution
is available. Binary independence supplies the required ordering of standard
best/worst lotteries. -/
theorem exists_representsExpectedUtility_of_vnmAxioms_of_compoundIndifference
    {Ω : Type*} [Finite Ω] [Nonempty Ω]
    {pref : Lottery Ω → Lottery Ω → Prop}
    (hcomplete : Completeness pref)
    (htrans : Transitivity pref)
    (hind : Independence pref)
    (hcont : Continuity pref)
    (hcompound : CompoundIndifference pref) :
    ∃ u : Ω → ℝ, RepresentsExpectedUtility pref u :=
  exists_representsExpectedUtility_of_compoundIndifference_and_standardLottery_order
    hcomplete htrans hcont hcompound
    (fun hbest_worst hnot_worst_best =>
      standardLottery_order_of_independence hcomplete hind hbest_worst hnot_worst_best)

/-- Finite-outcome von Neumann-Morgenstern converse theorem. If a preference
relation on finite lotteries is complete, transitive, independent, and
continuous, then it has an expected-utility representation. -/
theorem exists_representsExpectedUtility_of_vnmAxioms
    {Ω : Type*} [Finite Ω] [Nonempty Ω]
    {pref : Lottery Ω → Lottery Ω → Prop}
    (hcomplete : Completeness pref)
    (htrans : Transitivity pref)
    (hind : Independence pref)
    (hcont : Continuity pref) :
    ∃ u : Ω → ℝ, RepresentsExpectedUtility pref u :=
  exists_representsExpectedUtility_of_vnmAxioms_of_compoundIndifference
    hcomplete htrans hind hcont
    (compoundIndifference_of_independence htrans hind)

/-- Finite-outcome vNM characterization: a preference relation satisfies the
four vNM axioms exactly when it has an expected-utility representation. -/
theorem vnmAxioms_iff_exists_representsExpectedUtility
    {Ω : Type*} [Finite Ω] [Nonempty Ω]
    {pref : Lottery Ω → Lottery Ω → Prop} :
    (Completeness pref ∧ Transitivity pref ∧ Independence pref ∧ Continuity pref) ↔
      ∃ u : Ω → ℝ, RepresentsExpectedUtility pref u := by
  constructor
  · rintro ⟨hcomplete, htrans, hind, hcont⟩
    exact exists_representsExpectedUtility_of_vnmAxioms hcomplete htrans hind hcont
  · rintro ⟨u, hrep⟩
    exact hrep.vnmAxioms

/-- Sure-thing principle for relation-level vNM independence. -/
theorem strict_mix_common_iff_of_independence {Ω : Type*}
    {pref : Lottery Ω → Lottery Ω → Prop} (hind : Independence pref)
    (L M N N' : Lottery Ω) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    strict pref (mix t (le_of_lt ht0) ht1 L N) (mix t (le_of_lt ht0) ht1 M N) ↔
      strict pref (mix t (le_of_lt ht0) ht1 L N') (mix t (le_of_lt ht0) ht1 M N') := by
  constructor
  · intro h
    exact ⟨(hind L M N' t ht0 ht1).mp ((hind L M N t ht0 ht1).mpr h.1),
      fun hrev => h.2 ((hind M L N t ht0 ht1).mp
        ((hind M L N' t ht0 ht1).mpr hrev))⟩
  · intro h
    exact ⟨(hind L M N t ht0 ht1).mp ((hind L M N' t ht0 ht1).mpr h.1),
      fun hrev => h.2 ((hind M L N' t ht0 ht1).mp
        ((hind M L N t ht0 ht1).mpr hrev))⟩

/-! ## Risk Neutrality -/

/-- A real utility index is affine when it has the form `x ↦ a * x + b`. -/
def IsAffineUtility (u : ℝ → ℝ) : Prop :=
  ∃ a b : ℝ, ∀ x, u x = a * x + b

/-- Risk neutrality for real monetary outcomes: utility commutes with every
binary convex combination. -/
def IsRiskNeutral (u : ℝ → ℝ) : Prop :=
  ∀ (t : ℝ), 0 ≤ t → t ≤ 1 → ∀ x y,
    u (t * x + (1 - t) * y) = t * u x + (1 - t) * u y

/-- Affine utility indices are risk neutral. -/
theorem IsAffineUtility.isRiskNeutral {u : ℝ → ℝ}
    (h : IsAffineUtility u) : IsRiskNeutral u := by
  obtain ⟨a, b, hu⟩ := h
  intro t _ _ x y
  simp [hu]
  ring

/-- Risk-neutral utility indices are affine. -/
theorem IsRiskNeutral.isAffine {u : ℝ → ℝ}
    (h : IsRiskNeutral u) : IsAffineUtility u := by
  refine ⟨u 1 - u 0, u 0, fun x => ?_⟩
  suffices hnonneg : ∀ y : ℝ, 0 ≤ y → u y = (u 1 - u 0) * y + u 0 by
    by_cases hx : 0 ≤ x
    · exact hnonneg x hx
    · have hxlt : x < 0 := lt_of_not_ge hx
      have hmx := hnonneg (-x) (le_of_lt (neg_pos.mpr hxlt))
      have hmid := h (1 / 2) (by norm_num) (by norm_num) x (-x)
      have harg : (1 : ℝ) / 2 * x + (1 - 1 / 2) * -x = 0 := by ring
      rw [harg] at hmid
      linarith
  intro y hy
  rcases eq_or_lt_of_le hy with rfl | hy_pos
  · ring
  rcases le_or_gt y 1 with hy1 | hy1
  · have hy_formula := h y hy hy1 1 0
    simp at hy_formula
    linarith
  · have h_inv := h (1 / y) (le_of_lt (div_pos one_pos hy_pos))
      ((div_le_one hy_pos).mpr (le_of_lt hy1)) y 0
    simp at h_inv
    have hyne : y ≠ 0 := ne_of_gt hy_pos
    field_simp [hyne] at h_inv ⊢
    linarith

/-! ## Axiom Independence -/

namespace AxiomIndependence

private noncomputable def lottery3 (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h1 : 0 ≤ p1) (h2 : 0 ≤ p2)
    (hsum : p0 + p1 + p2 = 1) : Lottery (Fin 3) :=
  PMF.ofFintype
    (fun i : Fin 3 => ![ENNReal.ofReal p0, ENNReal.ofReal p1, ENNReal.ofReal p2] i)
    (by
      rw [Fin.sum_univ_three]
      calc
        ENNReal.ofReal p0 + ENNReal.ofReal p1 + ENNReal.ofReal p2
            = ENNReal.ofReal (p0 + p1) + ENNReal.ofReal p2 := by
              rw [ENNReal.ofReal_add h0 h1]
        _ = ENNReal.ofReal ((p0 + p1) + p2) := by
              rw [ENNReal.ofReal_add (add_nonneg h0 h1) h2]
        _ = 1 := by
              rw [show (p0 + p1) + p2 = 1 by linarith]
              simp)

@[simp] private theorem probOf_lottery3_zero (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h1 : 0 ≤ p1) (h2 : 0 ≤ p2)
    (hsum : p0 + p1 + p2 = 1) :
    probOf (0 : Fin 3) (lottery3 p0 p1 p2 h0 h1 h2 hsum) = p0 := by
  simp [probOf, lottery3, h0]

@[simp] private theorem probOf_lottery3_one (p0 p1 p2 : ℝ)
    (h0 : 0 ≤ p0) (h1 : 0 ≤ p1) (h2 : 0 ≤ p2)
    (hsum : p0 + p1 + p2 = 1) :
    probOf (1 : Fin 3) (lottery3 p0 p1 p2 h0 h1 h2 hsum) = p1 := by
  simp [probOf, lottery3, h1]

namespace NotComplete

private def pref (L M : Lottery (Fin 3)) : Prop :=
  probOf (0 : Fin 3) L = probOf (0 : Fin 3) M ∧
    probOf (1 : Fin 3) L ≥ probOf (1 : Fin 3) M

private theorem not_complete : ¬ Completeness pref := by
  intro h
  have hc := h (PMF.pure (0 : Fin 3)) (PMF.pure (1 : Fin 3))
  unfold pref at hc
  norm_num [probOf] at hc

private theorem transitive : Transitivity pref := by
  intro L M N hLM hMN
  exact ⟨hLM.1.trans hMN.1, le_trans hMN.2 hLM.2⟩

private theorem independent : Independence pref := by
  intro L M N t ht0 ht1
  unfold pref
  simp only [probOf_mix]
  constructor
  · intro h
    constructor <;> nlinarith [h.1, h.2, ht0]
  · intro h
    constructor <;> nlinarith [h.1, h.2, ht0]

private theorem continuous : Continuity pref := by
  intro L M N hLM hMN
  unfold pref at hLM hMN
  by_cases heq : probOf (1 : Fin 3) L = probOf (1 : Fin 3) N
  · refine ⟨0, by norm_num, by norm_num, ?_⟩
    have hM_eq_N : probOf (1 : Fin 3) M = probOf (1 : Fin 3) N := by
      exact le_antisymm (by linarith) hMN.2
    have h0_eq : probOf (0 : Fin 3) M =
        probOf (0 : Fin 3) (mix 0 (by norm_num) (by norm_num) L N) := by
      rw [probOf_mix]
      nlinarith [hMN.1]
    have h1_eq : probOf (1 : Fin 3) M =
        probOf (1 : Fin 3) (mix 0 (by norm_num) (by norm_num) L N) := by
      rw [probOf_mix]
      nlinarith [hM_eq_N]
    unfold indiff pref
    constructor <;> constructor <;> linarith
  · have hNL : probOf (1 : Fin 3) N < probOf (1 : Fin 3) L := by
      exact lt_of_le_of_ne (le_trans hMN.2 hLM.2) (Ne.symm heq)
    let t := (probOf (1 : Fin 3) M - probOf (1 : Fin 3) N) /
      (probOf (1 : Fin 3) L - probOf (1 : Fin 3) N)
    have hden_pos : 0 < probOf (1 : Fin 3) L - probOf (1 : Fin 3) N :=
      sub_pos.mpr hNL
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact div_nonneg (sub_nonneg.mpr hMN.2) (le_of_lt hden_pos)
    have ht1 : t ≤ 1 := by
      dsimp [t]
      rw [div_le_one hden_pos]
      linarith
    refine ⟨t, ht0, ht1, ?_⟩
    have h0_eq : probOf (0 : Fin 3) M =
        probOf (0 : Fin 3) (mix t ht0 ht1 L N) := by
      rw [probOf_mix]
      nlinarith [hLM.1, hMN.1]
    have h1_eq : probOf (1 : Fin 3) M =
        probOf (1 : Fin 3) (mix t ht0 ht1 L N) := by
      rw [probOf_mix]
      dsimp [t]
      field_simp [ne_of_gt hden_pos]
      ring
    unfold indiff pref
    constructor <;> constructor <;> linarith

theorem completeness_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Completeness pref ∧ Transitivity pref ∧
      Independence pref ∧ Continuity pref :=
  ⟨pref, not_complete, transitive, independent, continuous⟩

end NotComplete

namespace NotContinuous

private def pref (L M : Lottery (Fin 3)) : Prop :=
  probOf (0 : Fin 3) L > probOf (0 : Fin 3) M ∨
    (probOf (0 : Fin 3) L = probOf (0 : Fin 3) M ∧
      probOf (1 : Fin 3) L ≥ probOf (1 : Fin 3) M)

private theorem complete : Completeness pref := by
  intro L M
  unfold pref
  rcases lt_trichotomy (probOf (0 : Fin 3) L) (probOf (0 : Fin 3) M) with h | h | h
  · right; left; exact h
  · rcases le_total (probOf (1 : Fin 3) M) (probOf (1 : Fin 3) L) with h1 | h1
    · left; right; exact ⟨h, h1⟩
    · right; right; exact ⟨h.symm, h1⟩
  · left; left; exact h

private theorem transitive : Transitivity pref := by
  intro L M N hLM hMN
  unfold pref at *
  rcases hLM with hLM | ⟨hLM0, hLM1⟩ <;>
    rcases hMN with hMN | ⟨hMN0, hMN1⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨by linarith, by linarith⟩

private theorem independent : Independence pref := by
  intro L M N t ht0 ht1
  unfold pref
  simp only [probOf_mix]
  constructor
  · intro h
    rcases h with h | ⟨h0, h1⟩
    · left; nlinarith
    · right; constructor <;> nlinarith
  · intro h
    rcases h with h | ⟨h0, h1⟩
    · left; nlinarith
    · right; constructor <;> nlinarith

private theorem not_continuous : ¬ Continuity pref := by
  intro h
  let L0 : Lottery (Fin 3) := PMF.pure 0
  let L1 : Lottery (Fin 3) := PMF.pure 1
  let L2 : Lottery (Fin 3) := PMF.pure 2
  have h01 : pref L0 L1 := by
    unfold pref L0 L1
    left
    norm_num
  have h12 : pref L1 L2 := by
    unfold pref L1 L2
    right
    constructor <;> simp [probOf]
  obtain ⟨t, ht0, ht1, hindiff⟩ := h L0 L1 L2 h01 h12
  rcases hindiff with ⟨hleft, hright⟩
  unfold pref at hleft hright
  simp only [probOf_mix] at hleft hright
  unfold L0 L1 L2 at hleft hright
  have hleft' : 0 > t ∨ (0 = t ∧ 1 ≥ (0 : ℝ)) := by
    simpa [probOf] using hleft
  have hright' : t > 0 ∨ (t = 0 ∧ (0 : ℝ) ≥ 1) := by
    simpa [probOf] using hright
  rcases hright' with htpos | ⟨htzero, hbad⟩
  · rcases hleft' with hneg | ⟨hzero, _⟩ <;> linarith
  · linarith

theorem continuity_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Continuity pref ∧ Completeness pref ∧
      Transitivity pref ∧ Independence pref :=
  ⟨pref, not_continuous, complete, transitive, independent⟩

end NotContinuous

namespace NotIndependent

private def pref (L M : Lottery (Fin 3)) : Prop :=
  probOf (0 : Fin 3) L ≥ 1 / 2 ∨ probOf (0 : Fin 3) M < 1 / 2

private theorem complete : Completeness pref := by
  intro L M
  unfold pref
  rcases le_or_gt (1 / 2 : ℝ) (probOf (0 : Fin 3) L) with h | h
  · left; left; exact h
  · right; right; exact h

private theorem transitive : Transitivity pref := by
  intro L M N hLM hMN
  unfold pref at *
  rcases hLM with hL | hM
  · left; exact hL
  · rcases hMN with hM' | hN
    · linarith
    · right; exact hN

private theorem not_independent : ¬ Independence pref := by
  intro h
  let L : Lottery (Fin 3) := lottery3 (2 / 5) (3 / 5) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let M : Lottery (Fin 3) := lottery3 (3 / 5) (2 / 5) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let N : Lottery (Fin 3) := lottery3 (4 / 5) (1 / 5) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hnot : ¬ pref L M := by
    unfold pref L M
    simp
    constructor <;> norm_num
  have hmix : pref (mix (1 / 2) (by norm_num) (by norm_num) L N)
      (mix (1 / 2) (by norm_num) (by norm_num) M N) := by
    unfold pref L M N
    simp only [probOf_mix]
    left
    norm_num
  exact hnot ((h L M N (1 / 2) (by norm_num) (by norm_num)).mpr hmix)

private theorem continuous : Continuity pref := by
  intro L M N hLM hMN
  rcases le_or_gt (1 / 2 : ℝ) (probOf (0 : Fin 3) M) with hMhigh | hMlow
  · have hLhigh : probOf (0 : Fin 3) L ≥ 1 / 2 := by
      unfold pref at hLM
      rcases hLM with h | h <;> linarith
    refine ⟨1, by norm_num, le_rfl, ?_⟩
    unfold indiff pref
    simp only [probOf_mix]
    constructor
    · left; nlinarith
    · left; nlinarith
  · have hNlow : probOf (0 : Fin 3) N < 1 / 2 := by
      unfold pref at hMN
      rcases hMN with h | h <;> linarith
    refine ⟨0, le_rfl, by norm_num, ?_⟩
    unfold indiff pref
    simp only [probOf_mix]
    constructor
    · right; nlinarith
    · right; nlinarith

theorem independence_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Independence pref ∧ Completeness pref ∧
      Transitivity pref ∧ Continuity pref :=
  ⟨pref, not_independent, complete, transitive, continuous⟩

end NotIndependent

namespace NotTransitive

private def pref (L M : Lottery (Fin 3)) : Prop :=
  probOf (0 : Fin 3) L ≥ probOf (0 : Fin 3) M ∨
    probOf (1 : Fin 3) L ≥ probOf (1 : Fin 3) M

private theorem complete : Completeness pref := by
  intro L M
  unfold pref
  rcases le_total (probOf (0 : Fin 3) M) (probOf (0 : Fin 3) L) with h | h
  · left; left; exact h
  · right; left; exact h

private theorem not_transitive : ¬ Transitivity pref := by
  intro h
  let L : Lottery (Fin 3) := lottery3 (2 / 5) (1 / 10) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let M : Lottery (Fin 3) := lottery3 (3 / 10) (3 / 10) (2 / 5)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  let N : Lottery (Fin 3) := lottery3 (1 / 2) (1 / 5) (3 / 10)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hLM : pref L M := by
    unfold pref L M
    left
    norm_num
  have hMN : pref M N := by
    unfold pref M N
    right
    norm_num
  have hLN := h L M N hLM hMN
  unfold pref at hLN
  dsimp only [L, M, N] at hLN
  rcases hLN with h0 | h1
  · norm_num at h0
  · norm_num at h1

private theorem independent : Independence pref := by
  intro L M N t ht0 ht1
  unfold pref
  simp only [probOf_mix]
  constructor
  · intro h
    rcases h with h | h
    · left; nlinarith
    · right; nlinarith
  · intro h
    rcases h with h | h
    · left; nlinarith
    · right; nlinarith

private theorem continuous : Continuity pref := by
  intro L M N hLM hMN
  by_cases hNM : pref N M
  · refine ⟨0, le_rfl, by norm_num, ?_⟩
    unfold indiff
    unfold pref
    simp only [probOf_mix]
    constructor
    · rcases hMN with h | h
      · left; nlinarith
      · right; nlinarith
    · rcases hNM with h | h
      · left; nlinarith
      · right; nlinarith
  · by_cases hML : pref M L
    · refine ⟨1, by norm_num, le_rfl, ?_⟩
      unfold indiff
      unfold pref
      simp only [probOf_mix]
      constructor
      · rcases hML with h | h
        · left; nlinarith
        · right; nlinarith
      · rcases hLM with h | h
        · left; nlinarith
        · right; nlinarith
    · unfold pref at hNM hML hLM hMN
      push Not at hNM hML
      obtain ⟨hNM0, hNM1⟩ := hNM
      obtain ⟨hML0, hML1⟩ := hML
      have hden_pos : 0 < probOf (0 : Fin 3) L - probOf (0 : Fin 3) N := by
        linarith
      have hnum_pos : 0 < probOf (0 : Fin 3) M - probOf (0 : Fin 3) N := by
        linarith
      have hnum_lt : probOf (0 : Fin 3) M - probOf (0 : Fin 3) N <
          probOf (0 : Fin 3) L - probOf (0 : Fin 3) N := by
        linarith
      set t := (probOf (0 : Fin 3) M - probOf (0 : Fin 3) N) /
        (probOf (0 : Fin 3) L - probOf (0 : Fin 3) N)
      have ht0 : 0 ≤ t := le_of_lt (div_pos hnum_pos hden_pos)
      have ht1 : t ≤ 1 := le_of_lt (by
        rw [div_lt_one hden_pos]
        exact hnum_lt)
      refine ⟨t, ht0, ht1, ?_⟩
      have ht_eq : t * probOf (0 : Fin 3) L + (1 - t) * probOf (0 : Fin 3) N =
          probOf (0 : Fin 3) M := by
        have hne : probOf (0 : Fin 3) L - probOf (0 : Fin 3) N ≠ 0 :=
          ne_of_gt hden_pos
        simp only [t]
        field_simp [hne]
        ring
      unfold indiff pref
      simp only [probOf_mix]
      constructor
      · left; linarith
      · left; linarith

theorem transitivity_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Transitivity pref ∧ Completeness pref ∧
      Independence pref ∧ Continuity pref :=
  ⟨pref, not_transitive, complete, independent, continuous⟩

end NotTransitive

end AxiomIndependence

/-- Completeness is independent from transitivity, independence, and continuity
for preferences over three-outcome lotteries. -/
theorem completeness_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Completeness pref ∧ Transitivity pref ∧
      Independence pref ∧ Continuity pref :=
  AxiomIndependence.NotComplete.completeness_independent

/-- Continuity is independent from completeness, transitivity, and independence
for preferences over three-outcome lotteries. -/
theorem continuity_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Continuity pref ∧ Completeness pref ∧
      Transitivity pref ∧ Independence pref :=
  AxiomIndependence.NotContinuous.continuity_independent

/-- Independence is independent from completeness, transitivity, and continuity
for preferences over three-outcome lotteries. -/
theorem independence_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Independence pref ∧ Completeness pref ∧
      Transitivity pref ∧ Continuity pref :=
  AxiomIndependence.NotIndependent.independence_independent

/-- Transitivity is independent from completeness, independence, and continuity
for preferences over three-outcome lotteries. -/
theorem transitivity_independent :
    ∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Transitivity pref ∧ Completeness pref ∧
      Independence pref ∧ Continuity pref :=
  AxiomIndependence.NotTransitive.transitivity_independent

/-- The four vNM preference axioms are independent: each can fail while the
other three hold for a preference relation over three-outcome lotteries. -/
theorem axioms_independent :
    (∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Completeness pref ∧ Transitivity pref ∧ Independence pref ∧ Continuity pref) ∧
    (∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Transitivity pref ∧ Completeness pref ∧ Independence pref ∧ Continuity pref) ∧
    (∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Independence pref ∧ Completeness pref ∧ Transitivity pref ∧ Continuity pref) ∧
    (∃ pref : Lottery (Fin 3) → Lottery (Fin 3) → Prop,
      ¬ Continuity pref ∧ Completeness pref ∧ Transitivity pref ∧ Independence pref) :=
  ⟨completeness_independent, transitivity_independent,
    independence_independent, continuity_independent⟩

end VNM

end GameTheory
