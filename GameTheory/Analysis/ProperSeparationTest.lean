module

/-
# A perfect equilibrium that is not proper

In the symmetric three-action game, mutual middle play survives equal trembles
to the upper and lower actions. Properness instead forces the worse lower
mistake to become negligible relative to the upper mistake. The upper action
then beats the middle action, ruling out that limit.

The example is discussed in Alexander Wolitzky's MIT 14.126 lecture on
equilibrium refinements (2024), following Myerson's properness distinction.
-/

public import GameTheory.Analysis.Proper
public import GameTheory.Math.Probability.ExpectationMap
public import GameTheory.Math.Probability.ExpectationMixture
public import GameTheory.Math.Probability.FiniteUniform
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

namespace GameTheory.Analysis.ProperSeparationTest

open Filter GameTheory.Math.Probability
open scoped BigOperators

@[reducible]
def form : GameForm Bool where
  sig := { Strategy := fun _ => Fin 3, Outcome := Bool → Fin 3 }
  play profile := PMF.pure profile

def payoff (own other : Fin 3) : ℝ :=
  (![![1, 0, -9], ![0, 0, -7], ![-9, -7, -7]] : Fin 3 → Fin 3 → ℝ) own other

def utility (outcome : form.sig.Outcome) (who : Bool) : ℝ :=
  payoff (outcome who) (outcome (!who))

def middle : Profile form.sig.mixed := fun _ => PMF.pure 1

theorem utility_integrable : form.HasIntegrableUtility utility :=
  fun _ _ => payoffIntegrable_pure _ _

def score (profile : Profile form.sig.mixed) (who : Bool) (action : Fin 3) : ℝ :=
  expectedUtility utility who
    (form.mixed.play (Profile.update profile who (PMF.pure action)))

theorem score_eq_expect (profile : Profile form.sig.mixed) (who : Bool) (action : Fin 3) :
    score profile who action = expect (profile (!who)) (payoff action) := by
  let updated := Profile.update (sig := form.sig.mixed) profile who (PMF.pure action)
  have play : form.mixed.play updated = independentProduct updated := by
    rw [GameForm.mixed_play]
    simp [form]
  have self (outcome : form.sig.Outcome)
      (supported : outcome ∈ (independentProduct updated).support) : outcome who = action := by
    have coordinate := (independentProduct_support_iff updated outcome).mp supported who
    simpa only [updated, Profile.update_same, PMF.mem_support_pure_iff] using coordinate
  have other : (!who) ≠ who := by cases who <;> decide
  calc
    score profile who action = expect (independentProduct updated)
        (fun outcome => payoff (outcome who) (outcome (!who))) := by
      rw [score, play]
      rfl
    _ = expect (independentProduct updated) (fun outcome => payoff action (outcome (!who))) :=
      expect_congr_on_support fun outcome supported => by rw [self outcome supported]
    _ = expect ((independentProduct updated).map (fun outcome => outcome (!who)))
        (payoff action) := (expect_map _ _ _).symm
    _ = expect (profile (!who)) (payoff action) := by
      rw [independentProduct_map_eval]
      exact congrArg (fun law => expect law (payoff action))
        (Profile.update_of_ne profile (PMF.pure action) other)

theorem score_upper (profile : Profile form.sig.mixed) (who : Bool) :
    score profile who 0 = (profile (!who) 0).toReal - 9 * (profile (!who) 2).toReal := by
  rw [score_eq_expect, expect_eq_sum]
  change (∑ action : Fin 3, (profile (!who) action).toReal * payoff 0 action) = _
  norm_num [Fin.sum_univ_succ, payoff]
  ring

theorem score_middle (profile : Profile form.sig.mixed) (who : Bool) :
    score profile who 1 = -7 * (profile (!who) 2).toReal := by
  rw [score_eq_expect, expect_eq_sum]
  change (∑ action : Fin 3, (profile (!who) action).toReal * payoff 1 action) = _
  norm_num [Fin.sum_univ_succ, payoff]
  ring

theorem score_lower (profile : Profile form.sig.mixed) (who : Bool) :
    score profile who 2 = -9 * (profile (!who) 0).toReal -
      7 * (profile (!who) 1).toReal - 7 * (profile (!who) 2).toReal := by
  rw [score_eq_expect, expect_eq_sum]
  change (∑ action : Fin 3, (profile (!who) action).toReal * payoff 2 action) = _
  norm_num [Fin.sum_univ_succ, payoff]
  ring

def tremble (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1) : PMF (Fin 3) :=
  mix weight nonnegative small (uniformLaw (Fin 3)) (PMF.pure 1)

def trembleProfile (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1) :
    Profile form.sig.mixed := fun _ => tremble weight nonnegative small

theorem tremble_mass (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1)
    (action : Fin 3) :
    (tremble weight nonnegative small action).toReal =
      if action = 1 then 1 - 2 * weight / 3 else weight / 3 := by
  rw [tremble, mix_apply_toReal]
  fin_cases action <;> norm_num [uniformLaw_apply, PMF.pure_apply] <;> ring

theorem tremble_scores (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1)
    (who : Bool) :
    score (trembleProfile weight nonnegative small) who 0 = -8 * weight / 3 ∧
      score (trembleProfile weight nonnegative small) who 1 = -7 * weight / 3 ∧
      score (trembleProfile weight nonnegative small) who 2 = -7 - 2 * weight / 3 := by
  rw [score_upper, score_middle, score_lower]
  dsimp only [trembleProfile]
  rw [tremble_mass, tremble_mass, tremble_mass]
  norm_num
  constructor
  · ring
  · constructor <;> ring

theorem value_eq_expect (profile : Profile form.sig.mixed) (who : Bool) :
    expectedUtility utility who (form.mixed.play profile) =
      expect (profile who) (score profile who) :=
  expectedUtility_mixed_eq_expect form utility profile who (payoffIntegrable_of_finite _ _)

theorem tremble_middle_best (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1)
    (who : Bool) (action : Fin 3) :
    score (trembleProfile weight nonnegative small) who action ≤
      score (trembleProfile weight nonnegative small) who 1 := by
  obtain ⟨upper, middle, lower⟩ := tremble_scores weight nonnegative small who
  fin_cases action
  · change score (trembleProfile weight nonnegative small) who 0 ≤ _
    rw [upper, middle]
    linarith
  · exact le_rfl
  · change score (trembleProfile weight nonnegative small) who 2 ≤ _
    rw [lower, middle]
    linarith

/-- Equal trembles lock both inferior actions at the common positive floor;
every free unit remains on the score-maximizing middle action. -/
theorem tremble_isPerturbedEq (weight : ℝ) (nonnegative : 0 ≤ weight) (small : weight ≤ 1) :
    form.IsPerturbedEq (euPreference utility) (fun _ _ => weight / 3)
      (trembleProfile weight nonnegative small) := by
  rw [form.isPerturbedEq_iff]
  refine ⟨?_, ?_⟩
  · intro who action
    change weight / 3 ≤ (tremble weight nonnegative small action).toReal
    rw [tremble_mass]
    split
    · linarith
    · exact le_rfl
  · intro who replacement respects
    apply (euPreference_iff utility who _ _ (payoffIntegrable_of_finite _ _)
      (payoffIntegrable_of_finite _ _)).mpr
    rw [value_eq_expect, value_eq_expect]
    have erase (action : Fin 3) :
        score (Profile.update (trembleProfile weight nonnegative small) who replacement)
          who action =
          score (trembleProfile weight nonnegative small) who action := by
      simp only [score, Profile.update_idem]
    simp only [Profile.update_same, funext erase]
    apply expect_le_of_suboptimal_mass_le
    intro action inferior
    fin_cases action
    · change (tremble weight nonnegative small 0).toReal ≤ (replacement 0).toReal
      rw [tremble_mass]
      norm_num
      exact respects 0
    · obtain ⟨better, improves⟩ := inferior
      exact False.elim (not_lt_of_ge
        (tremble_middle_best weight nonnegative small who better) improves)
    · change (tremble weight nonnegative small 2).toReal ≤ (replacement 2).toReal
      rw [tremble_mass]
      norm_num
      exact respects 2

/-- Mutual middle play is perfect, with explicit vanishing equal trembles to
the two inferior actions. -/
theorem middle_isTremblingHandPerfect :
    form.IsTremblingHandPerfect (euPreference utility) middle := by
  let weight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have positive (n : ℕ) : 0 < weight n :=
    one_div_pos.mpr (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))
  have small (n : ℕ) : weight n ≤ 1 := by
    apply (div_le_one (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))).mpr
    have nonnegative : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have vanishes : Tendsto weight atTop (nhds 0) := by
    have limit := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    convert limit using 1
    funext n
    simp only [weight, Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  refine ⟨fun n _ _ => weight n / 3,
    fun n => trembleProfile (weight n) (positive n).le (small n),
    fun n => ⟨fun _ _ => div_pos (positive n) (by norm_num),
      tremble_isPerturbedEq (weight n) (positive n).le (small n)⟩, ?_, ?_⟩
  · intro who action
    simpa only [zero_div] using vanishes.div_const 3
  · intro who
    exact pmfConvergesPointwise_mix_zero weight (fun n => (positive n).le) small vanishes
      (uniformLaw (Fin 3)) (PMF.pure 1)

/-- Proper error ratios force the upper mistake to dominate the lower mistake.
The middle action then becomes inferior, contradicting its unit limiting mass. -/
theorem middle_not_isProper : ¬ form.IsProper utility middle := by
  rintro ⟨epsilon, approximating, proper, vanishes, converges⟩
  have scoreConverges (who : Bool) (action : Fin 3) :
      Tendsto (fun n => score (approximating n) who action) atTop
        (nhds (score middle who action)) :=
    UtilityGame.expectedUtility_update_pure_tendsto
      (G := ⟨form, utility⟩) converges utility_integrable who action
  have lowerLimit : Tendsto (fun n => score (approximating n) true 2)
      atTop (nhds (-7)) := by
    have target : score middle true 2 = -7 := by
      rw [score_lower]
      dsimp only [middle]
      norm_num [PMF.pure_apply]
    simpa only [target] using scoreConverges true 2
  have upperLimit : Tendsto (fun n => score (approximating n) true 0)
      atTop (nhds 0) := by
    have target : score middle true 0 = 0 := by
      rw [score_upper]
      dsimp only [middle]
      norm_num [PMF.pure_apply]
    simpa only [target] using scoreConverges true 0
  have inferiorEventually : ∀ᶠ n in atTop,
      score (approximating n) true 2 < score (approximating n) true 0 :=
    lowerLimit.eventually_lt upperLimit (by norm_num)
  have smallEventually : ∀ᶠ n in atTop, epsilon n < 1 / 2 :=
    Filter.Tendsto.eventually_lt_const (by norm_num) vanishes
  have boundedEventually : ∀ᶠ n in atTop,
      (approximating n false 1).toReal ≤ epsilon n := by
    filter_upwards [inferiorEventually, smallEventually] with n inferior small
    have ratio := (proper n).2.2.2 true 2 0 inferior
    have positive : 0 < (approximating n true 0).toReal :=
      pmf_toReal_pos_iff.mpr ((proper n).2.1 true 0)
    have strictRatio : 0 < (1 - 2 * epsilon n) * (approximating n true 0).toReal :=
      mul_pos (by linarith) positive
    have improves : score (approximating n) false 1 < score (approximating n) false 0 := by
      rw [score_middle, score_upper]
      change -7 * (approximating n true 2).toReal <
        (approximating n true 0).toReal - 9 * (approximating n true 2).toReal
      nlinarith
    have bound := (proper n).2.2.2 false 1 0 improves
    exact bound.trans
      (mul_le_of_le_one_right (proper n).1.le (pmf_toReal_apply_le_one _ _))
  have zeroLimit : Tendsto (fun n => (approximating n false 1).toReal) atTop (nhds 0) :=
    squeeze_zero' (Eventually.of_forall fun _ => ENNReal.toReal_nonneg) boundedEventually vanishes
  have oneLimit : Tendsto (fun n => (approximating n false 1).toReal) atTop (nhds 1) := by
    simpa [middle, PMF.pure_apply] using (converges false).toReal 1
  have impossible : (0 : ℝ) = 1 := tendsto_nhds_unique zeroLimit oneLimit
  norm_num at impossible

theorem perfect_not_proper :
    form.IsTremblingHandPerfect (euPreference utility) middle ∧
      ¬ form.IsProper utility middle :=
  ⟨middle_isTremblingHandPerfect, middle_not_isProper⟩

end GameTheory.Analysis.ProperSeparationTest
