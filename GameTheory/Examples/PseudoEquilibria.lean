/-
# Pseudo-equilibrium examples

*Dominance against expectation.* Let `X` pay `0` or `2` with equal
probability, and let `Y` pay `4 ^ κ` with probability `2 ^ (-κ)` and `0`
otherwise. Then `E Y = 2 ^ κ` exceeds `E X = 1` at every positive size, yet `X`
computationally mean-dominates `Y`. Polynomially many draws of `Y` are all zero
except with negligible probability, while polynomially many draws of `X` are
all zero only with negligible probability. So in parameterized games pseudo-Nash
separates from Nash: a deviation paying `Y` refutes Nash but not pseudo-Nash.

*The ideal guessing game.* A committer picks a `κ`-bit string, a guesser picks
another, and the guesser wins `2 ^ ℓ` from the committer when `ℓ` bits agree.
When both pick uniformly, every unilateral deviation leaves each player's
utility law unchanged, so the uniform profile is a pseudo-Nash equilibrium,
although utilities grow exponentially in `κ`.

Primary reference: A. Psomas, A. Terzoglou, Y. Wei, and V. Zikas,
“Pseudo-Equilibria, or: How to Stop Worrying About Crypto and Just Analyze the
Game,” arXiv:2506.22089 (2025).
-/
import GameTheory.Core.ExpectedUtility
import GameTheory.Core.PseudoNash
import GameTheory.Math.Probability.MeanComparisonExpectation
import GameTheory.Math.Probability.Uniform
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

namespace GameTheory.Examples.PseudoEquilibria

open Filter GameTheory.Math.Probability

/-! ## Probability tools for nonnegative draws -/

section Nonnegative

/-- The probability of an event, as the expectation of its indicator. -/
private abbrev probOf (μ : PMF ℝ) (event : ℝ → Prop) [DecidablePred event] : ℝ :=
  expect μ fun x => if event x then 1 else 0

private theorem abs_indicator_le (p : Prop) [Decidable p] :
    |(if p then (1 : ℝ) else 0)| ≤ 1 := by
  split_ifs <;> simp

private theorem indicator_nonneg (p : Prop) [Decidable p] : 0 ≤ (if p then (1 : ℝ) else 0) := by
  split_ifs <;> norm_num

private theorem expect_pair (A B : PMF ℝ) (m : ℕ) (f : ℝ × ℝ → ℝ) (hf : ∀ p, |f p| ≤ 1) :
    expect (sampleSumPair A B m) f =
      expect (sampleSum A m) fun s => expect (sampleSum B m) fun t => f (s, t) := by
  rw [sampleSumPair, expect_bind_tower _ _ _ (payoffIntegrable_of_bounded _ _ hf)]
  apply expect_congr_on_support
  intro s _
  rw [expect_map]
  rfl

/-- The sum of `m` draws is nonzero only if some draw is: a union bound. -/
private theorem probOf_sampleSum_ne_zero_le (μ : PMF ℝ) (m : ℕ) :
    probOf (sampleSum μ m) (· ≠ 0) ≤ m * probOf μ (· ≠ 0) := by
  induction m with
  | zero => simp [expect_pure]
  | succ m ih =>
    rw [sampleSum_succ, probOf, expect_addLaw _ _ _
      (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)]
    have hpoint : ∀ s, expect μ (fun y => if s + y ≠ 0 then (1 : ℝ) else 0) ≤
        (if s ≠ 0 then 1 else 0) + probOf μ (· ≠ 0) := by
      intro s
      rw [← expect_constant μ (if s ≠ 0 then (1 : ℝ) else 0),
        ← expect_add (payoffIntegrable_constant _ _)
          (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)]
      refine expect_mono (fun y _ => ?_)
        (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)
        (payoffIntegrable_add (payoffIntegrable_constant _ _)
          (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _))
      by_cases hs : s = 0
      · subst hs
        simp only [zero_add, ne_eq, not_true_eq_false, ite_false]
        rfl
      · have := indicator_nonneg (y ≠ 0)
        split_ifs <;> simp_all
    calc
      _ ≤ expect (sampleSum μ m) (fun s => (if s ≠ 0 then (1 : ℝ) else 0) + probOf μ (· ≠ 0)) :=
        expect_mono (fun s _ => hpoint s)
          (payoffIntegrable_of_bounded _ _ (C := 1) fun _ =>
            expect_abs_le_of_bounded zero_le_one fun _ => abs_indicator_le _)
          (payoffIntegrable_add (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)
            (payoffIntegrable_constant _ _))
      _ = probOf (sampleSum μ m) (· ≠ 0) + probOf μ (· ≠ 0) := by
        rw [expect_add (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)
          (payoffIntegrable_constant _ _), expect_constant]
      _ ≤ m * probOf μ (· ≠ 0) + probOf μ (· ≠ 0) := by linarith
      _ = ((m + 1 : ℕ) : ℝ) * probOf μ (· ≠ 0) := by push_cast; ring

/-- A sum of nonnegative draws vanishes only if every draw does. -/
private theorem probOf_sampleSum_eq_zero_le {μ : PMF ℝ} (hμ : ∀ x ∈ μ.support, 0 ≤ x)
    (m : ℕ) : probOf (sampleSum μ m) (· = 0) ≤ probOf μ (· = 0) ^ m := by
  induction m with
  | zero => simp [expect_pure]
  | succ m ih =>
    have hnonneg := fun s hs => nonneg_of_mem_support_sampleSum hμ m s hs
    rw [sampleSum_succ, probOf, expect_addLaw _ _ _
      (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)]
    have hpoint : ∀ s ∈ (sampleSum μ m).support,
        expect μ (fun y => if s + y = 0 then (1 : ℝ) else 0) ≤
          (if s = 0 then 1 else 0) * probOf μ (· = 0) := by
      intro s hs
      rw [← expect_const_mul]
      refine expect_mono (fun y hy => ?_)
        (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)
        (payoffIntegrable_const_mul (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _))
      have h0 := hnonneg s hs
      have h1 := hμ y hy
      by_cases hsy : s + y = 0
      · have hs0 : s = 0 := by linarith
        have hy0 : y = 0 := by linarith
        simp [hs0, hy0]
      · simp only [hsy, ite_false]
        exact mul_nonneg (indicator_nonneg _) (indicator_nonneg _)
    have hprob0 : 0 ≤ probOf μ (· = 0) := expect_nonneg _ _ fun _ _ => indicator_nonneg _
    calc
      _ ≤ expect (sampleSum μ m) (fun s => (if s = 0 then (1 : ℝ) else 0) * probOf μ (· = 0)) :=
        expect_mono hpoint
          (payoffIntegrable_of_bounded _ _ (C := 1) fun _ =>
            expect_abs_le_of_bounded zero_le_one fun _ => abs_indicator_le _)
          (payoffIntegrable_of_bounded _ _ (C := |probOf μ (· = 0)|) fun _ => by
            rw [abs_mul]
            exact mul_le_of_le_one_left (abs_nonneg _) (abs_indicator_le _))
      _ = probOf (sampleSum μ m) (· = 0) * probOf μ (· = 0) := by
        simp only [mul_comm _ (probOf μ (· = 0))]
        rw [expect_const_mul, mul_comm]
      _ ≤ probOf μ (· = 0) ^ m * probOf μ (· = 0) := mul_le_mul_of_nonneg_right ih hprob0
      _ = probOf μ (· = 0) ^ (m + 1) := (pow_succ _ _).symm

end Nonnegative

/-! ## Ahead probabilities of nonnegative draws -/

section Ahead

private theorem aheadProb_eq_expect (A B : PMF ℝ) (m : ℕ) :
    aheadProb A B m =
      expect (sampleSum A m) fun s => expect (sampleSum B m) fun t => if t < s then 1 else 0 := by
  classical
  rw [aheadProb, ← expect_indicator, expect_pair _ _ _ _ fun _ => abs_indicator_le _]
  rfl

/-- A nonnegative sum beats `ΣY` only when `ΣY` is nonzero. -/
private theorem aheadProb_le {X Y : PMF ℝ} (hX : ∀ x ∈ X.support, 0 ≤ x) (m : ℕ) :
    aheadProb Y X m ≤ probOf (sampleSum Y m) (· ≠ 0) := by
  rw [aheadProb_eq_expect]
  refine expect_mono (fun s _ => ?_)
    (payoffIntegrable_of_bounded _ _ (C := 1) fun _ =>
      expect_abs_le_of_bounded zero_le_one fun _ => abs_indicator_le _)
    (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)
  refine expect_le_const _ _ (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _) _
    fun t ht => ?_
  have := nonneg_of_mem_support_sampleSum hX m t ht
  by_cases hts : t < s
  · have hs : s ≠ 0 := by intro hs; linarith
    simp [hts, hs]
  · simp only [hts, ite_false]
    exact indicator_nonneg _

/-- A nonnegative sum beats a nonnegative `ΣY` whenever `ΣY` vanishes and it
does not. -/
private theorem one_sub_le_aheadProb {X Y : PMF ℝ} (hX : ∀ x ∈ X.support, 0 ≤ x)
    (hY : ∀ y ∈ Y.support, 0 ≤ y) (m : ℕ) :
    1 - probOf (sampleSum Y m) (· ≠ 0) - probOf (sampleSum X m) (· = 0) ≤ aheadProb X Y m := by
  rw [aheadProb_eq_expect]
  set pY := probOf (sampleSum Y m) (· ≠ 0)
  have hinner : ∀ s ∈ (sampleSum X m).support,
      (1 - (if s = 0 then (1 : ℝ) else 0)) - pY ≤
        expect (sampleSum Y m) fun t => if t < s then 1 else 0 := by
    intro s hs
    have hs0 := nonneg_of_mem_support_sampleSum hX m s hs
    have hsub : expect (sampleSum Y m)
        (fun t => (1 - (if s = 0 then (1 : ℝ) else 0)) - if t ≠ 0 then 1 else 0) =
          (1 - (if s = 0 then (1 : ℝ) else 0)) - pY := by
      rw [expect_sub (payoffIntegrable_constant _ _)
        (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _), expect_constant]
    rw [← hsub]
    refine expect_mono (fun t ht => ?_)
      (payoffIntegrable_sub (payoffIntegrable_constant _ _)
        (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _))
      (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)
    have ht0 := nonneg_of_mem_support_sampleSum hY m t ht
    by_cases hs : s = 0
    · simp only [hs, ite_true, sub_self, zero_sub]
      have := indicator_nonneg (t ≠ 0)
      have := indicator_nonneg (t < 0)
      linarith
    · by_cases ht : t = 0
      · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
        simp [hs, ht, hspos]
      · simp only [hs, ht, ite_false, ne_eq, not_false_eq_true, ite_true, sub_zero, sub_self]
        exact indicator_nonneg _
  have hmono := expect_mono hinner
    (payoffIntegrable_sub (payoffIntegrable_sub (payoffIntegrable_constant _ _)
      (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)) (payoffIntegrable_constant _ _))
    (payoffIntegrable_of_bounded _ _ (C := 1) fun _ =>
      expect_abs_le_of_bounded zero_le_one fun _ => abs_indicator_le _)
  rw [expect_sub (payoffIntegrable_sub (payoffIntegrable_constant _ _)
      (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _)) (payoffIntegrable_constant _ _),
    expect_sub (payoffIntegrable_constant _ _)
      (payoffIntegrable_of_bounded _ _ fun _ => abs_indicator_le _),
    expect_constant, expect_constant] at hmono
  linarith

end Ahead

/-! ## Dominance against expectation -/

/-- Pays `0` or `2` with equal probability. -/
def coinPayoff : PMF ℝ :=
  (PMF.uniformOfFintype Bool).map fun b => if b then 2 else 0

/-- Pays `4 ^ κ` with probability `2 ^ (-κ)`, and `0` otherwise. -/
def jackpot (κ : ℕ) : PMF ℝ :=
  (PMF.uniformOfFintype (Fin (2 ^ κ))).map fun i => if i = 0 then 4 ^ κ else 0

theorem lawMean_coinPayoff : lawMean coinPayoff = 1 := by
  rw [lawMean, coinPayoff, expect_map, expect_uniformOfFintype]
  norm_num

theorem lawMean_jackpot (κ : ℕ) : lawMean (jackpot κ) = 2 ^ κ := by
  rw [lawMean, jackpot, expect_map, expect_uniformOfFintype]
  simp only [Function.comp_apply, id, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Fintype.card_fin]
  push_cast
  rw [show (4 : ℝ) ^ κ = 2 ^ κ * 2 ^ κ by rw [← mul_pow]; norm_num]
  field_simp

/-- The expectation of the jackpot exceeds that of the coin at every positive size. -/
theorem lawMean_coinPayoff_lt_lawMean_jackpot {κ : ℕ} (hκ : 1 ≤ κ) :
    lawMean coinPayoff < lawMean (jackpot κ) := by
  rw [lawMean_coinPayoff, lawMean_jackpot]
  exact one_lt_pow₀ (by norm_num) (by omega)

private theorem coinPayoff_nonneg : ∀ x ∈ coinPayoff.support, 0 ≤ x := by
  intro x hx
  rw [coinPayoff, PMF.mem_support_map_iff] at hx
  obtain ⟨b, _, rfl⟩ := hx
  cases b <;> norm_num

private theorem jackpot_nonneg (κ : ℕ) : ∀ x ∈ (jackpot κ).support, 0 ≤ x := by
  intro x hx
  rw [jackpot, PMF.mem_support_map_iff] at hx
  obtain ⟨i, _, rfl⟩ := hx
  split_ifs <;> positivity

private theorem probOf_coinPayoff_eq_zero : probOf coinPayoff (· = 0) = 1 / 2 := by
  rw [probOf, coinPayoff, expect_map, expect_uniformOfFintype]
  norm_num

private theorem probOf_jackpot_ne_zero (κ : ℕ) : probOf (jackpot κ) (· ≠ 0) = 1 / 2 ^ κ := by
  rw [probOf, jackpot, expect_map, expect_uniformOfFintype]
  have hne : ∀ i : Fin (2 ^ κ), ((if i = 0 then (4 : ℝ) ^ κ else 0) ≠ 0) ↔ i = 0 := by
    intro i
    by_cases hi : i = 0 <;> simp [hi]
  simp only [Function.comp_apply, hne, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Fintype.card_fin]
  push_cast
  rfl

/-- **The coin dominates the jackpot**, although the jackpot's expectation is
exponentially larger. -/
theorem coinPayoff_computationallyMeanDominates_jackpot :
    ComputationallyMeanDominates (fun _ => coinPayoff) jackpot := by
  intro c _
  refine ⟨c + 1, by omega, ?_⟩
  have hlim : Tendsto (fun κ : ℕ => (κ : ℝ) ^ (c + 1) / 2 ^ κ) atTop (nhds 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt (c + 1) (by norm_num)
  filter_upwards [(tendsto_order.1 hlim).2 (1 / 4) (by norm_num), eventually_ge_atTop 1]
    with κ hsmall hκ
  set m := κ ^ (c + 1)
  have hm : 1 ≤ m := Nat.one_le_pow _ _ (by omega)
  have hbeaten := aheadProb_le coinPayoff_nonneg (Y := jackpot κ) m
  have hbeat := one_sub_le_aheadProb coinPayoff_nonneg (jackpot_nonneg κ) m
  have hjack : probOf (sampleSum (jackpot κ) m) (· ≠ 0) ≤ m * (1 / 2 ^ κ) := by
    rw [← probOf_jackpot_ne_zero]
    exact probOf_sampleSum_ne_zero_le _ m
  have hcoin : probOf (sampleSum coinPayoff m) (· = 0) ≤ 1 / 2 := by
    refine (probOf_sampleSum_eq_zero_le coinPayoff_nonneg m).trans ?_
    rw [probOf_coinPayoff_eq_zero]
    exact pow_le_of_le_one (by norm_num) (by norm_num) (by omega)
  have hmκ : (m : ℝ) * (1 / 2 ^ κ) < 1 / 4 := by
    simp only [m]
    push_cast
    rw [mul_one_div]
    exact hsmall
  have hpos : (0 : ℝ) < ((κ : ℝ) ^ c)⁻¹ := by
    have : (0 : ℝ) < κ := by exact_mod_cast hκ
    positivity
  rw [meanComparisonGap_eq_aheadProb_sub]
  linarith

/-! ## A lottery game -/

/-- One player chooses between the coin (`true`) and the jackpot (`false`); the
outcome is the payoff. -/
@[reducible]
def lottery : ParameterizedGame Unit where
  sig := { Strategy := fun _ => Bool, Outcome := ℝ }
  play κ profile := if profile () then coinPayoff else jackpot κ
  utility _ payoff _ := payoff

/-- Choosing the coin. -/
def takeCoin : Profile lottery.sig := fun _ => true

private theorem lottery_utilityLaw (profile : Profile lottery.sig) :
    lottery.utilityLaw () profile = fun κ => lottery.play κ profile := by
  funext κ
  exact PMF.map_id _

private theorem lottery_play_takeCoin (κ : ℕ) : lottery.play κ takeCoin = coinPayoff := rfl

private theorem lottery_play_coin (κ : ℕ) :
    lottery.play κ (Profile.update takeCoin () true) = coinPayoff := by
  change (if Profile.update takeCoin () true () then coinPayoff else jackpot κ) = _
  rw [Profile.update_same]
  rfl

private theorem lottery_play_jackpot (κ : ℕ) :
    lottery.play κ (Profile.update takeCoin () false) = jackpot κ := by
  change (if Profile.update takeCoin () false () then coinPayoff else jackpot κ) = _
  rw [Profile.update_same]
  rfl

/-- Taking the coin is a pseudo-Nash equilibrium. -/
theorem lottery_isPseudoNash_takeCoin : lottery.IsPseudoNash takeCoin := by
  intro who replacement
  cases who
  rw [lottery_utilityLaw, lottery_utilityLaw,
    show (fun κ => lottery.play κ takeCoin) = fun _ => coinPayoff from
      funext lottery_play_takeCoin]
  cases replacement
  · rw [show (fun κ => lottery.play κ (Profile.update takeCoin () false)) = jackpot from
      funext lottery_play_jackpot]
    exact coinPayoff_computationallyMeanDominates_jackpot
  · rw [show (fun κ => lottery.play κ (Profile.update takeCoin () true)) = fun _ => coinPayoff
      from funext lottery_play_coin]
    exact computationallyMeanDominates_refl _

/-- Taking the coin is not a Nash equilibrium of the game at any positive size. -/
theorem lottery_not_isNash_takeCoin {κ : ℕ} (hκ : 1 ≤ κ) :
    ¬ IsNash (lottery.formAt κ) (euPreference (lottery.utility κ)) takeCoin := by
  rw [isNash_iff]
  intro h
  have hdev := h () false
  have hint : ∀ law : PMF ℝ, (∀ x ∈ law.support, |x| ≤ 4 ^ κ) →
      UtilityIntegrable (lottery.utility κ) () law := fun law hlaw =>
    payoffIntegrable_of_bounded_on_support law _ hlaw
  have hcoinBound : ∀ x ∈ coinPayoff.support, |x| ≤ 4 ^ κ := by
    intro x hx
    rw [coinPayoff, PMF.mem_support_map_iff] at hx
    obtain ⟨b, _, rfl⟩ := hx
    have : (2 : ℝ) ≤ 4 ^ κ := le_trans (by norm_num) (le_self_pow₀ (by norm_num) (by omega))
    cases b
    · simp
    · simpa using this
  have hjackBound : ∀ x ∈ (jackpot κ).support, |x| ≤ 4 ^ κ := by
    intro x hx
    rw [jackpot, PMF.mem_support_map_iff] at hx
    obtain ⟨i, _, rfl⟩ := hx
    split_ifs <;> simp
  change euPreference (lottery.utility κ) () (lottery.play κ takeCoin)
    (lottery.play κ (Profile.update takeCoin () false)) at hdev
  rw [lottery_play_takeCoin, lottery_play_jackpot] at hdev
  rw [euPreference_iff _ _ _ _ (hint _ hcoinBound) (hint _ hjackBound)] at hdev
  have hlt := lawMean_coinPayoff_lt_lawMean_jackpot hκ
  exact absurd hdev (not_le.mpr hlt)

/-! ## The ideal guessing game -/

/-- The two roles of the guessing game. -/
inductive GuessRole
  | committer
  | guesser
  deriving DecidableEq

/-- The number of positions where two bit strings agree. -/
def agreements {κ : ℕ} (x y : Fin κ → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i = y i).card

theorem agreements_comm {κ : ℕ} (x y : Fin κ → Bool) : agreements x y = agreements y x := by
  simp only [agreements, eq_comm]

/-- The law of agreements when the two strings are drawn independently. -/
def agreementPlay {κ : ℕ} (committer guesser : PMF (Fin κ → Bool)) : PMF ℕ :=
  committer.bind fun x => guesser.map fun y => agreements x y

/-- Each role picks, at every size, a law on `κ`-bit strings; the outcome is
the number of agreeing bits, and the guesser wins `2 ^ ℓ` from the committer
for `ℓ` agreements. -/
@[reducible]
def guessingGame : ParameterizedGame GuessRole where
  sig := { Strategy := fun _ => (κ : ℕ) → PMF (Fin κ → Bool), Outcome := ℕ }
  play κ profile := agreementPlay (profile .committer κ) (profile .guesser κ)
  utility _ agreed who := match who with
    | .committer => -(2 : ℝ) ^ agreed
    | .guesser => 2 ^ agreed

/-- Both roles pick uniformly at every size. -/
def uniformGuess : Profile guessingGame.sig :=
  fun _ κ => PMF.uniformOfFintype (Fin κ → Bool)

/-- The number of agreements with a uniform string does not depend on the other
string. -/
private theorem uniform_map_agreements {κ : ℕ} (y : Fin κ → Bool) :
    (PMF.uniformOfFintype (Fin κ → Bool)).map (fun x => agreements x y) =
      (PMF.uniformOfFintype (Fin κ → Bool)).map (fun x => agreements x fun _ => true) := by
  let flip : Equiv.Perm (Fin κ → Bool) :=
    Function.Involutive.toPerm (fun x i => x i == y i) fun x => by
      funext i
      change ((x i == y i) == y i) = x i
      cases x i <;> cases y i <;> rfl
  have hcount : (fun x => agreements x y) = (fun x => agreements x fun _ => true) ∘ flip := by
    funext x
    change (Finset.univ.filter fun i => x i = y i).card =
      (Finset.univ.filter fun i => (x i == y i) = true).card
    simp only [beq_iff_eq]
  have hflip : (PMF.uniformOfFintype (Fin κ → Bool)).map flip =
      PMF.uniformOfFintype (Fin κ → Bool) := by
    ext z
    classical
    rw [uniformOfFintype_map_apply, PMF.uniformOfFintype_apply]
    have hfiber : (Finset.univ.filter fun x => flip x = z) = {flip.symm z} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro rfl
        rw [Equiv.symm_apply_apply]
      · rintro rfl
        rw [Equiv.apply_symm_apply]
    rw [hfiber, Finset.card_singleton, Nat.cast_one, one_div]
  rw [hcount, ← PMF.map_comp, hflip]

/-- The law of agreements with an independent uniform string. -/
private abbrev agreementLaw (κ : ℕ) : PMF ℕ :=
  (PMF.uniformOfFintype (Fin κ → Bool)).map fun x => agreements x fun _ => true

private theorem bind_uniform_right {κ : ℕ} (law : PMF (Fin κ → Bool)) :
    agreementPlay law (PMF.uniformOfFintype (Fin κ → Bool)) = agreementLaw κ := by
  have hpoint : ∀ x : Fin κ → Bool,
      (PMF.uniformOfFintype (Fin κ → Bool)).map (fun y => agreements x y) = agreementLaw κ := by
    intro x
    simp_rw [agreements_comm x]
    exact uniform_map_agreements x
  simp only [agreementPlay, hpoint]
  exact PMF.bind_const _ _

private theorem bind_uniform_left {κ : ℕ} (law : PMF (Fin κ → Bool)) :
    agreementPlay (PMF.uniformOfFintype (Fin κ → Bool)) law = agreementLaw κ := by
  have hswap : ((PMF.uniformOfFintype (Fin κ → Bool)).bind fun x =>
      law.map fun y => agreements x y) =
        law.bind fun y => (PMF.uniformOfFintype (Fin κ → Bool)).map fun x => agreements x y := by
    simp only [PMF.map, Function.comp_def]
    exact PMF.bind_comm _ _ _
  rw [agreementPlay, hswap]
  simp only [uniform_map_agreements]
  exact PMF.bind_const _ _

/-- Against a uniform opponent, every unilateral choice yields the same law of
agreements as uniform play. -/
private theorem guessingGame_play_update (who : GuessRole)
    (replacement : guessingGame.sig.Strategy who) (κ : ℕ) :
    guessingGame.play κ (Profile.update uniformGuess who replacement) =
      guessingGame.play κ uniformGuess := by
  cases who
  · have hother : Profile.update uniformGuess GuessRole.committer replacement GuessRole.guesser =
        uniformGuess GuessRole.guesser :=
      Profile.update_of_ne _ _ (by decide)
    change agreementPlay (Profile.update uniformGuess GuessRole.committer replacement
        GuessRole.committer κ) (Profile.update uniformGuess GuessRole.committer replacement
        GuessRole.guesser κ) = agreementPlay (uniformGuess GuessRole.committer κ)
        (uniformGuess GuessRole.guesser κ)
    rw [Profile.update_same, hother]
    exact (bind_uniform_right _).trans (bind_uniform_right _).symm
  · have hother : Profile.update uniformGuess GuessRole.guesser replacement GuessRole.committer =
        uniformGuess GuessRole.committer :=
      Profile.update_of_ne _ _ (by decide)
    change agreementPlay (Profile.update uniformGuess GuessRole.guesser replacement
        GuessRole.committer κ) (Profile.update uniformGuess GuessRole.guesser replacement
        GuessRole.guesser κ) = agreementPlay (uniformGuess GuessRole.committer κ)
        (uniformGuess GuessRole.guesser κ)
    rw [Profile.update_same, hother]
    exact (bind_uniform_left _).trans (bind_uniform_left _).symm

/-- **Uniform guessing is a pseudo-Nash equilibrium** of the ideal guessing
game, although utilities are exponential in the size. -/
theorem guessingGame_isPseudoNash_uniformGuess : guessingGame.IsPseudoNash uniformGuess := by
  intro who replacement
  have hsame : guessingGame.utilityLaw who (Profile.update uniformGuess who replacement) =
      guessingGame.utilityLaw who uniformGuess := by
    funext κ
    exact congrArg (PMF.map _) (guessingGame_play_update who replacement κ)
  rw [hsame]
  exact computationallyMeanDominates_refl _

end GameTheory.Examples.PseudoEquilibria
