/-
# Trembling-hand perfection is not a comparison family

The row player chooses `T`, `M`, or a copy of `T`; the column player chooses
`L`, `R₁`, or `R₂` and is indifferent. `M` earns the row player `gain column`
and the other rows earn nothing, so at `L` every row ties. Under the first gain
`(0, 1, -1)` and the second gain `(0, -1, 2)` a suitable tremble of the column
player makes `M` tie with `T`, so `(T, L)` is trembling-hand perfect. Under
their sum `(0, 0, 1)` every tremble makes `M` strictly better, a perturbed
equilibrium gives `T` only its lower bound, and `(T, L)` is not a limit of
perturbed equilibria. The supporting utilities are not closed under addition,
so trembling-hand perfection is the concept of no comparison family and its
preservation is not decided by a cone criterion.
-/

import GameTheory.Analysis.IncentiveHierarchy
import GameTheory.Analysis.TremblingHand

noncomputable section

namespace GameTheory.Tests.TremblingHandBoundary

open GameTheory GameTheory.Math.Probability Filter Topology

@[reducible]
def form : GameForm Bool where
  sig := { Strategy := fun _ => Fin 3, Outcome := Fin 3 × Fin 3 }
  play profile := PMF.pure (profile false, profile true)

/-- The row player earns `gain column` from its second action; the column
player is indifferent. -/
def rowUtility (gain : Fin 3 → ℝ) : Fin 3 × Fin 3 → Bool → ℝ
  | (row, column), false => if row = 1 then gain column else 0
  | _, true => 0

def firstGain : Fin 3 → ℝ := ![0, 1, -1]

def secondGain : Fin 3 → ℝ := ![0, -1, 2]

def sumGain : Fin 3 → ℝ := ![0, 0, 1]

theorem rowUtility_add :
    rowUtility firstGain + rowUtility secondGain = rowUtility sumGain := by
  funext outcome who
  rcases outcome with ⟨row, column⟩
  cases who <;> fin_cases row <;> fin_cases column <;>
    simp [rowUtility, firstGain, secondGain, sumGain]
  norm_num

/-- The row player plays `T` and the column player `L`. -/
def incumbent : Profile form.sig.mixed := fun _ => PMF.pure 0

def IsPerfect (utility : Fin 3 × Fin 3 → Bool → ℝ) : Prop :=
  form.IsTremblingHandPerfect (euPreference fun outcome who => utility outcome who) incumbent

/-! ## Expected utility under independent mixing -/

theorem expect_mixed_play (profile : Profile form.sig.mixed) (payoff : Fin 3 × Fin 3 → ℝ) :
    expect (form.mixed.play profile) payoff =
      ∑ row, ∑ column, (profile false row).toReal * (profile true column).toReal *
        payoff (row, column) := by
  have hmap : form.mixed.play profile =
      (independentProduct profile).map fun choices => (choices false, choices true) := by
    rw [GameForm.mixed_play]
    exact PMF.bind_pure_comp _ _
  rw [hmap, expect_map, expect_eq_sum]
  simp only [independentProduct_apply, Fintype.prod_bool, ENNReal.toReal_mul,
    Function.comp_apply]
  rw [← (Equiv.boolArrowEquivProd (Fin 3)).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.boolArrowEquivProd_symm_apply, Bool.false_eq_true, ↓reduceIte]
  exact Finset.sum_congr rfl fun row _ => Finset.sum_congr rfl fun column _ => by ring

theorem expect_row (profile : Profile form.sig.mixed) (gain : Fin 3 → ℝ) :
    expect (form.mixed.play profile) (fun outcome => rowUtility gain outcome false) =
      (profile false 1).toReal * ∑ column, (profile true column).toReal * gain column := by
  rw [expect_mixed_play]
  simp only [rowUtility, Fin.sum_univ_three, Fin.isValue]
  norm_num
  ring

theorem expect_column (profile : Profile form.sig.mixed) (gain : Fin 3 → ℝ) :
    expect (form.mixed.play profile) (fun outcome => rowUtility gain outcome true) = 0 := by
  rw [expect_mixed_play]
  simp [rowUtility]

theorem prefers_iff (utility : Fin 3 × Fin 3 → Bool → ℝ) (who : Bool)
    (first second : PMF (Fin 3 × Fin 3)) :
    euPreference (fun outcome who => utility outcome who) who first second ↔
      expect second (fun outcome => utility outcome who) ≤
        expect first (fun outcome => utility outcome who) :=
  euPreference_iff _ who first second (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)

/-! ## Mixed strategies with prescribed weights -/

/-- The mixed strategy with weights `first`, `second`, `third`. -/
def weights (first second third : ℝ) (hfirst : 0 ≤ first) (hsecond : 0 ≤ second)
    (hthird : 0 ≤ third) (hsum : first + second + third = 1) : PMF (Fin 3) :=
  PMF.ofFintype (fun action => ENNReal.ofReal (![first, second, third] action)) (by
    rw [Fin.sum_univ_three]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [← ENNReal.ofReal_add hfirst hsecond, ← ENNReal.ofReal_add (by positivity) hthird,
      hsum, ENNReal.ofReal_one])

theorem weights_toReal {first second third : ℝ} (hfirst : 0 ≤ first) (hsecond : 0 ≤ second)
    (hthird : 0 ≤ third) (hsum : first + second + third = 1) (action : Fin 3) :
    (weights first second third hfirst hsecond hthird hsum action).toReal =
      ![first, second, third] action := by
  simp only [weights, PMF.ofFintype_apply]
  refine ENNReal.toReal_ofReal ?_
  fin_cases action <;> simpa

theorem sum_toReal (law : PMF (Fin 3)) : ∑ action, (law action).toReal = 1 := by
  rw [← ENNReal.toReal_sum fun action _ => PMF.apply_ne_top law action]
  have := PMF.tsum_coe law
  rw [tsum_fintype] at this
  rw [this, ENNReal.toReal_one]

/-! ## Perfection under each gain -/

/-- The vanishing tremble. -/
def tremble (n : ℕ) : ℝ := (1 / 4) * (1 / ((n : ℝ) + 1))

theorem tremble_pos (n : ℕ) : 0 < tremble n := by
  unfold tremble
  positivity

theorem tremble_le (n : ℕ) : tremble n ≤ 1 / 4 := by
  unfold tremble
  have : 1 / ((n : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  nlinarith

theorem tremble_tendsto : Tendsto tremble atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 4)
  rw [mul_zero] at h
  exact h

/-- Row trembles: `T` keeps the rest, `M` and the copy each get the tremble. -/
def rowTremble (n : ℕ) : PMF (Fin 3) :=
  weights (1 - 2 * tremble n) (tremble n) (tremble n)
    (by linarith [tremble_le n]) (tremble_pos n).le (tremble_pos n).le (by ring)

/-- A column tremble whose weights on `R₁` and `R₂` are `first * ε` and
`second * ε`. -/
def columnTremble (first second : ℝ) (hfirst : 0 ≤ first) (hsecond : 0 ≤ second)
    (hsmall : first + second ≤ 3) (n : ℕ) : PMF (Fin 3) :=
  weights (1 - (first + second) * tremble n) (first * tremble n) (second * tremble n)
    (by nlinarith [tremble_le n, tremble_pos n])
    (mul_nonneg hfirst (tremble_pos n).le) (mul_nonneg hsecond (tremble_pos n).le) (by ring)

theorem isPerfect_of_balanced (gain : Fin 3 → ℝ) (first second : ℝ) (hfirst : 0 ≤ first)
    (hsecond : 0 ≤ second) (hlarge : 1 ≤ first) (hlarge' : 1 ≤ second)
    (hsmall : first + second ≤ 3) (hgain : gain 0 = 0)
    (hbalanced : first * gain 1 + second * gain 2 = 0) :
    IsPerfect (rowUtility gain) := by
  let approximating : ℕ → Profile form.sig.mixed := fun n who =>
    cond who (columnTremble first second hfirst hsecond hsmall n) (rowTremble n)
  have hrow (n : ℕ) (action : Fin 3) : (approximating n false action).toReal =
      ![1 - 2 * tremble n, tremble n, tremble n] action := by
    change (rowTremble n action).toReal = _
    exact weights_toReal _ _ _ _ action
  have hcolumn (n : ℕ) (action : Fin 3) : (approximating n true action).toReal =
      ![1 - (first + second) * tremble n, first * tremble n, second * tremble n] action := by
    change (columnTremble first second hfirst hsecond hsmall n action).toReal = _
    exact weights_toReal _ _ _ _ action
  have hdelta (n : ℕ) :
      ∑ column, (approximating n true column).toReal * gain column = 0 := by
    simp only [Fin.sum_univ_three, hcolumn, hgain]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    linear_combination tremble n * hbalanced
  refine ⟨fun n _ _ => tremble n, approximating, fun n => ⟨fun _ _ => tremble_pos n, ?_⟩,
    fun _ _ => tremble_tendsto, fun who action => ?_⟩
  · refine (form.isPerturbedEq_iff _ _ _).2 ⟨fun who action => ?_, fun who replacement _ => ?_⟩
    · cases who
      · rw [hrow]
        fin_cases action
        all_goals simp
        all_goals linarith [tremble_le n]
      · rw [hcolumn]
        fin_cases action <;> simp <;> nlinarith [tremble_le n, tremble_pos n]
    · rw [prefers_iff]
      cases who
      · rw [expect_row, expect_row, hdelta,
          show (Profile.update (approximating n) false replacement : Profile form.sig.mixed) true =
            approximating n true from Profile.update_of_ne _ _ (by decide), hdelta]
        simp
      · rw [expect_column, expect_column]
  · have hlimit : ∀ (weight : ℕ → ℝ) (limit : ℝ), Tendsto weight atTop (𝓝 limit) →
        Tendsto (fun n => ENNReal.ofReal (weight n)) atTop (𝓝 (ENNReal.ofReal limit)) :=
      fun _ _ h => ENNReal.tendsto_ofReal h
    have hsmallLimit (scale : ℝ) : Tendsto (fun n => scale * tremble n) atTop (𝓝 0) := by
      simpa using tremble_tendsto.const_mul scale
    have hlargeLimit (scale : ℝ) : Tendsto (fun n => 1 - scale * tremble n) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (hsmallLimit scale)
    cases who
    · change Tendsto (fun n => rowTremble n action) atTop (𝓝 (PMF.pure (0 : Fin 3) action))
      simp only [rowTremble, weights, PMF.ofFintype_apply, PMF.pure_apply]
      fin_cases action
      · simpa using hlimit _ _ (hlargeLimit 2)
      · simpa using hlimit _ _ tremble_tendsto
      · simpa using hlimit _ _ tremble_tendsto
    · change Tendsto (fun n => columnTremble first second hfirst hsecond hsmall n action) atTop
        (𝓝 (PMF.pure (0 : Fin 3) action))
      simp only [columnTremble, weights, PMF.ofFintype_apply, PMF.pure_apply]
      fin_cases action
      · simpa using hlimit _ _ (hlargeLimit (first + second))
      · simpa using hlimit _ _ (hsmallLimit first)
      · simpa using hlimit _ _ (hsmallLimit second)

theorem first_isPerfect : IsPerfect (rowUtility firstGain) :=
  isPerfect_of_balanced firstGain 1 1 (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num)
    (by simp [firstGain]) (by simp [firstGain])

theorem second_isPerfect : IsPerfect (rowUtility secondGain) :=
  isPerfect_of_balanced secondGain 2 1 (by norm_num) (by norm_num) (by norm_num) le_rfl
    (by norm_num) (by simp [secondGain]) (by norm_num [secondGain])

/-! ## No perfection under the sum -/

/-- In a perturbed equilibrium under the summed gain, the row player gives `T`
no more than its lower bound. -/
theorem incumbent_mass_le {lower : form.Perturbation} (hpositive : lower.Positive)
    {profile : Profile form.sig.mixed}
    (hequilibrium : form.IsPerturbedEq
      (euPreference fun outcome who => rowUtility sumGain outcome who) lower profile) :
    (profile false 0).toReal ≤ lower false 0 := by
  obtain ⟨hrespects, hstable⟩ := (form.isPerturbedEq_iff _ _ _).1 hequilibrium
  by_contra hgt
  push Not at hgt
  have hsum := sum_toReal (profile false)
  simp only [Fin.sum_univ_three] at hsum
  have hmiddle := hrespects false 1
  have hthird := hrespects false 2
  let replacement : PMF (Fin 3) :=
    weights (lower false 0) ((profile false 1).toReal + (profile false 0).toReal - lower false 0)
      (profile false 2).toReal (hpositive false 0).le
      (by linarith [ENNReal.toReal_nonneg (a := profile false 1)])
      ENNReal.toReal_nonneg (by linarith)
  have hreplacement (action : Fin 3) : (replacement action).toReal =
      ![lower false 0, (profile false 1).toReal + (profile false 0).toReal - lower false 0,
        (profile false 2).toReal] action :=
    weights_toReal _ _ _ _ action
  have hrespectsReplacement : form.StrategyRespectsPerturbation (lower false) replacement := by
    intro action
    rw [hreplacement]
    fin_cases action <;> simp <;> linarith
  have hprefers := hstable false replacement hrespectsReplacement
  rw [prefers_iff, expect_row, expect_row,
    show (Profile.update profile false replacement : Profile form.sig.mixed) true =
      profile true from Profile.update_of_ne _ _ (by decide),
    show (Profile.update profile false replacement : Profile form.sig.mixed) false =
      replacement from Profile.update_same _ _ _, hreplacement] at hprefers
  simp only [Fin.sum_univ_three, sumGain, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hprefers
  have hdelta : 0 < (profile true 2).toReal := lt_of_lt_of_le (hpositive true 2) (hrespects true 2)
  nlinarith

theorem sum_not_isPerfect : ¬ IsPerfect (rowUtility sumGain) := by
  rintro ⟨lower, approximating, hperturbed, hzero, hconverges⟩
  have hbound (n : ℕ) : (approximating n false 0).toReal ≤ lower n false 0 :=
    incumbent_mass_le (hperturbed n).1 (hperturbed n).2
  have hmass : Tendsto (fun n => (approximating n false 0).toReal) atTop (𝓝 1) := by
    have hone : incumbent false 0 = 1 := by simp [incumbent]
    have h := hconverges false 0
    rw [hone] at h
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp h
  have hle := le_of_tendsto_of_tendsto' hmass (hzero false 0) hbound
  norm_num at hle

/-- **Trembling-hand perfection is the concept of no comparison family.** -/
theorem perfect_not_family :
    ¬ ∃ (Index : Bool → Type) (family : (who : Bool) → Index who →
        IncentiveComparison (Fin 3 × Fin 3)),
      ∀ utility, (∀ who deviation, (family who deviation).Holds (utility · who)) ↔
        IsPerfect utility :=
  IncentiveComparison.not_exists_family_of_not_add IsPerfect first_isPerfect second_isPerfect
    (by rw [rowUtility_add]; exact sum_not_isPerfect)

end GameTheory.Tests.TremblingHandBoundary
