/-
# Indistinguishability by sample tests

A sample test sees a prescribed number of independent draws from a real law at
each size `κ` and accepts with some probability. Two ensembles are
indistinguishable by a class of tests when every test in the class has
negligible advantage between them.

The class is a parameter. The class of all tests gives statistical
indistinguishability; restricting it to the tests a probabilistic
polynomial-time machine can run gives computational indistinguishability once a
machine model fixes that class. What follows needs no machine model:
computational mean dominance performs one kind of test only, comparing the
empirical mean of the draws with that of fresh draws from a reference
ensemble. Any class containing those comparisons makes indistinguishable
ensembles interchangeable in every dominance statement against that reference.
For computational indistinguishability this is the requirement that the
reference be efficiently samplable.
-/
import GameTheory.Math.Probability.MeanComparison
import GameTheory.Math.Probability.Product
import GameTheory.Math.Probability.Support

noncomputable section

namespace GameTheory.Math.Probability

open GameTheory.Math

/-! ## Independent samples -/

/-- The law of `n` independent draws from `μ`. -/
abbrev iidLaw (μ : PMF ℝ) (n : ℕ) : PMF (Fin n → ℝ) :=
  independentProduct fun _ => μ

/-- One more independent draw is prepended to the tuple. -/
theorem iidLaw_succ (μ : PMF ℝ) (n : ℕ) :
    iidLaw μ (n + 1) = (iidLaw μ n).bind fun z => μ.map fun x => Fin.cons x z := by
  ext t
  rw [PMF.bind_apply, tsum_eq_single (Fin.tail t)]
  · have hhead := pmf_map_apply_of_injective μ (Fin.cons_left_injective (Fin.tail t)) (t 0)
    rw [Fin.cons_self_tail] at hhead
    rw [hhead, independentProduct_apply, independentProduct_apply, Fin.prod_univ_succ, mul_comm]
    rfl
  · intro z hz
    have hzero : (μ.map fun x => (Fin.cons x z : Fin (n + 1) → ℝ)) t = 0 := by
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.mpr fun x => ?_
      split_ifs with ht
      · exact absurd (by rw [ht, Fin.tail_cons]) hz
      · rfl
    rw [hzero, mul_zero]

/-- The sum of `n` independent draws has the law `sampleSum μ n`. -/
theorem iidLaw_map_sum (μ : PMF ℝ) (n : ℕ) :
    (iidLaw μ n).map (fun z => ∑ i, z i) = sampleSum μ n := by
  induction n with
  | zero =>
    rw [eq_pure_of_subsingleton (iidLaw μ 0) (fun _ => 0)]
    simp [PMF.pure_map]
  | succ n ih =>
    rw [iidLaw_succ, PMF.map_bind, sampleSum_succ, ← ih, addLaw, PMF.bind_map]
    congr 1
    funext z
    rw [Function.comp_apply, PMF.map_comp]
    congr 1
    funext x
    simp [Fin.sum_cons, add_comm]

/-! ## Tests and indistinguishability -/

/-- A randomized test seeing `samples κ` independent draws at size `κ`. -/
structure SampleTest where
  /-- How many independent draws the test sees at each size. -/
  samples : ℕ → ℕ
  /-- The acceptance law given the draws. -/
  accept : (κ : ℕ) → (Fin (samples κ) → ℝ) → PMF Bool

/-- The probability that the test accepts draws from the ensemble at size `κ`. -/
def SampleTest.acceptProb (T : SampleTest) (X : ℕ → PMF ℝ) (κ : ℕ) : ℝ :=
  ((iidLaw (X κ) (T.samples κ)).bind (T.accept κ) true).toReal

/-- Every test in the class has negligible advantage between the ensembles. -/
def IndistinguishableBy (tests : Set SampleTest) (X X' : ℕ → PMF ℝ) : Prop :=
  ∀ T ∈ tests, Negligible fun κ => T.acceptProb X κ - T.acceptProb X' κ

theorem IndistinguishableBy.refl (tests : Set SampleTest) (X : ℕ → PMF ℝ) :
    IndistinguishableBy tests X X := fun _ _ => by
  simpa using negligible_zero

theorem IndistinguishableBy.symm {tests : Set SampleTest} {X X' : ℕ → PMF ℝ}
    (h : IndistinguishableBy tests X X') : IndistinguishableBy tests X' X := fun T hT => by
  simpa using (h T hT).neg

theorem IndistinguishableBy.trans {tests : Set SampleTest} {X X' X'' : ℕ → PMF ℝ}
    (h : IndistinguishableBy tests X X') (h' : IndistinguishableBy tests X' X'') :
    IndistinguishableBy tests X X'' := fun T hT => by
  simpa using (h T hT).add (h' T hT)

/-! ## Comparing empirical means with a reference -/

/-- Accept when the sum of the `κ ^ d` draws exceeds the sum of `κ ^ d` fresh
draws from the reference. -/
def beatsMeanTest (Y : ℕ → PMF ℝ) (d : ℕ) : SampleTest where
  samples κ := κ ^ d
  accept κ z := (sampleSum (Y κ) (κ ^ d)).map fun t => decide (t < ∑ i, z i)

/-- Accept when the sum of `κ ^ d` fresh draws from the reference exceeds the
sum of the `κ ^ d` draws. -/
def beatenByMeanTest (Y : ℕ → PMF ℝ) (d : ℕ) : SampleTest where
  samples κ := κ ^ d
  accept κ z := (sampleSum (Y κ) (κ ^ d)).map fun t => decide (∑ i, z i < t)

/-- The class contains every comparison of empirical means with the reference
`Y`. -/
def ContainsMeanTests (tests : Set SampleTest) (Y : ℕ → PMF ℝ) : Prop :=
  ∀ d, beatsMeanTest Y d ∈ tests ∧ beatenByMeanTest Y d ∈ tests

theorem containsMeanTests_univ (Y : ℕ → PMF ℝ) : ContainsMeanTests Set.univ Y :=
  fun _ => ⟨Set.mem_univ _, Set.mem_univ _⟩

private theorem aheadProb_eq_bind (X Y : PMF ℝ) (m : ℕ) :
    aheadProb X Y m =
      (((sampleSum X m).bind fun s => (sampleSum Y m).map fun t => decide (t < s))
        true).toReal := by
  have hlaw : ((sampleSum X m).bind fun s => (sampleSum Y m).map fun t => decide (t < s)) =
      (sampleSumPair X Y m).map fun p => decide (p.2 < p.1) := by
    rw [sampleSumPair, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
  rw [hlaw, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply, aheadProb]
  congr 2
  ext p
  simp

theorem acceptProb_beatsMeanTest (Y X : ℕ → PMF ℝ) (d κ : ℕ) :
    (beatsMeanTest Y d).acceptProb X κ = aheadProb (X κ) (Y κ) (κ ^ d) := by
  rw [aheadProb_eq_bind, ← iidLaw_map_sum, PMF.bind_map]
  rfl

theorem acceptProb_beatenByMeanTest (Y X : ℕ → PMF ℝ) (d κ : ℕ) :
    (beatenByMeanTest Y d).acceptProb X κ = aheadProb (Y κ) (X κ) (κ ^ d) := by
  rw [aheadProb_eq_bind, ← iidLaw_map_sum (X κ)]
  have hlaw : ((iidLaw (X κ) (κ ^ d)).bind fun z =>
      (sampleSum (Y κ) (κ ^ d)).map fun t => decide (∑ i, z i < t)) =
        (sampleSum (Y κ) (κ ^ d)).bind fun t =>
          ((iidLaw (X κ) (κ ^ d)).map fun z => ∑ i, z i).map fun s => decide (s < t) := by
    simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
    exact PMF.bind_comm _ _ _
  change ((iidLaw (X κ) (κ ^ d)).bind (fun z =>
      (sampleSum (Y κ) (κ ^ d)).map fun t => decide (∑ i, z i < t)) true).toReal = _
  rw [hlaw]

/-- Indistinguishability by a class containing the mean comparisons against `Y`
is indistinguishability by those comparisons. -/
theorem IndistinguishableBy.meanTestIndistinguishable {tests : Set SampleTest}
    {X X' Y : ℕ → PMF ℝ} (hY : ContainsMeanTests tests Y) (h : IndistinguishableBy tests X X') :
    MeanTestIndistinguishable Y X X' := by
  intro d
  constructor
  · simpa only [acceptProb_beatsMeanTest] using h _ (hY d).1
  · simpa only [acceptProb_beatenByMeanTest] using h _ (hY d).2

end GameTheory.Math.Probability
