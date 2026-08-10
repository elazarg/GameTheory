/-
# Feasible and opponent-rational payoff vectors

This is the analytic side of repeated play. Feasibility is the convex hull of
stage payoff vectors; opponent minmax is an order-theoretic punishment value.
The finite-cycle approximation uses the independent denominator-clearing lemma
from `GameTheoryMath`. The construction needs neither ambient/interior geometry
nor a separate general security hierarchy.
-/

import Mathlib.Analysis.Convex.Combination
import GameTheory.Repeated.Periodic
import GameTheoryMath.SimplexApproximation

noncomputable section

open scoped BigOperators

namespace GameTheory

universe uι

variable {ι : Type uι}

open Probability

/-- A real payoff coordinate for every player. -/
abbrev PayoffVector (ι : Type uι) := ι → ℝ

namespace UtilityGame

/-- Finite players and outcomes give one nonnegative absolute payoff bound for
every stage profile and player. Strategy carriers need not be finite. -/
theorem exists_uniform_stagePayoff_abs_bound
    (G : UtilityGame ι) [Fintype ι] [Fintype G.form.sig.Outcome] :
    ∃ bound : ℝ, 0 ≤ bound ∧
      ∀ (profile : Profile G.form.sig) (who : ι),
        |G.stagePayoff profile who| ≤ bound := by
  let bound : ℝ :=
    ∑ who : ι, ∑ outcome : G.form.sig.Outcome,
      |G.utility outcome who|
  have hbound0 : 0 ≤ bound := by
    exact Finset.sum_nonneg fun _ _ =>
      Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨bound, hbound0, ?_⟩
  intro profile who
  have hcoordinate : ∀ outcome : G.form.sig.Outcome,
      |G.utility outcome who| ≤ bound := by
    intro outcome
    calc
      |G.utility outcome who| ≤
          ∑ result : G.form.sig.Outcome,
            |G.utility result who| := by
        exact Finset.single_le_sum
          (fun result _ => abs_nonneg (G.utility result who))
          (Finset.mem_univ outcome)
      _ ≤ bound := by
        exact Finset.single_le_sum
          (fun player _ =>
            Finset.sum_nonneg fun result _ =>
              abs_nonneg (G.utility result player))
          (Finset.mem_univ who)
  have hupper :
      expectedUtility G.utility who (G.form.play profile) ≤ bound := by
    calc
      expectedUtility G.utility who (G.form.play profile) ≤
          (G.form.play profile).expect
            (fun outcome => |G.utility outcome who|) := by
        apply FinDist.expect_mono
        intro outcome _
        exact le_abs_self _
      _ ≤ (G.form.play profile).expect (fun _ => bound) := by
        exact FinDist.expect_mono fun outcome _ => hcoordinate outcome
      _ = bound := FinDist.expect_const ..
  have hlower :
      -bound ≤ expectedUtility G.utility who (G.form.play profile) := by
    calc
      -bound = (G.form.play profile).expect (fun _ => -bound) := by
        rw [FinDist.expect_const]
      _ ≤ expectedUtility G.utility who (G.form.play profile) := by
        apply FinDist.expect_mono
        intro outcome _
        exact (neg_le_neg (hcoordinate outcome)).trans (neg_abs_le _)
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- The expected stage-payoff vector induced by a strategy profile. -/
def payoffVector (G : UtilityGame ι) (profile : Profile G.form.sig) :
    PayoffVector ι :=
  fun who => G.stagePayoff profile who

@[simp]
theorem payoffVector_apply (G : UtilityGame ι)
    (profile : Profile G.form.sig) (who : ι) :
    G.payoffVector profile who = G.stagePayoff profile who :=
  rfl

/-- Stage-payoff vectors attainable by pure profiles of the given form. -/
def purePayoffSet (G : UtilityGame ι) : Set (PayoffVector ι) :=
  Set.range G.payoffVector

theorem mem_purePayoffSet (G : UtilityGame ι) (value : PayoffVector ι) :
    value ∈ G.purePayoffSet ↔
      ∃ profile : Profile G.form.sig, G.payoffVector profile = value := by
  simp [purePayoffSet]

/-- Feasible payoffs are finite convex combinations of stage-payoff vectors. -/
def feasibleSet (G : UtilityGame ι) : Set (PayoffVector ι) :=
  convexHull ℝ G.purePayoffSet

theorem payoffVector_mem_feasibleSet (G : UtilityGame ι)
    (profile : Profile G.form.sig) :
    G.payoffVector profile ∈ G.feasibleSet :=
  subset_convexHull ℝ G.purePayoffSet ⟨profile, rfl⟩

theorem exists_fintype_weighted_profiles_of_mem_feasibleSet
    (G : UtilityGame ι) {value : PayoffVector ι}
    (hvalue : value ∈ G.feasibleSet) :
    ∃ (κ : Type) (_ : Fintype κ) (weight : κ → ℝ)
        (profile : κ → Profile G.form.sig),
      (∀ k, 0 ≤ weight k) ∧
        (∑ k, weight k = 1) ∧
          (∑ k, weight k • G.payoffVector (profile k) = value) := by
  rw [feasibleSet] at hvalue
  rcases (mem_convexHull_iff_exists_fintype (R := ℝ)
      (s := G.purePayoffSet) (x := value)).1 hvalue with
    ⟨κ, hκ, weight, point, hnonneg, hsum, hpoint, hweighted⟩
  letI : Fintype κ := hκ
  choose profile hprofile using
    fun k => (G.mem_purePayoffSet (point k)).1 (hpoint k)
  refine ⟨κ, hκ, weight, profile, hnonneg, hsum, ?_⟩
  calc
    ∑ k, weight k • G.payoffVector (profile k) =
        ∑ k, weight k • point k := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hprofile k]
    _ = value := hweighted

theorem exists_fintype_weighted_profiles_apply_of_mem_feasibleSet
    (G : UtilityGame ι) {value : PayoffVector ι}
    (hvalue : value ∈ G.feasibleSet) :
    ∃ (κ : Type) (_ : Fintype κ) (weight : κ → ℝ)
        (profile : κ → Profile G.form.sig),
      (∀ k, 0 ≤ weight k) ∧
        (∑ k, weight k = 1) ∧
          ∀ who, ∑ k, weight k * G.stagePayoff (profile k) who =
            value who := by
  rcases G.exists_fintype_weighted_profiles_of_mem_feasibleSet hvalue with
    ⟨κ, hκ, weight, profile, hnonneg, hsum, hweighted⟩
  letI : Fintype κ := hκ
  refine ⟨κ, hκ, weight, profile, hnonneg, hsum, ?_⟩
  intro who
  have happly := congrArg (fun payoff : PayoffVector ι => payoff who)
    hweighted
  simpa [payoffVector, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
    using happly

/-- Payoff vectors strictly above a reservation vector. -/
def strictReservationSet (reservation : PayoffVector ι) :
    Set (PayoffVector ι) :=
  { value | ∀ who, reservation who < value who }

/-- Feasible payoffs strictly above the opponent punishment vector. -/
def strictIndividuallyRationalPayoffSet (G : UtilityGame ι)
    (reservation : PayoffVector ι) : Set (PayoffVector ι) :=
  G.feasibleSet ∩ strictReservationSet reservation

/-- Best payoff against a fixed full punishment profile; the punished player's
stored coordinate is ignored and replaced.  On an empty strategy carrier this
inherits `iSup`'s empty-index convention; operational punishment theorems below
therefore request the relevant nonemptiness explicitly. -/
def bestResponseValueAgainstPunishment (G : UtilityGame ι)
    [DecidableEq ι] (who : ι) (punishment : Profile G.form.sig) : ℝ :=
  ⨆ own : G.form.sig.Strategy who,
    G.stagePayoff (Profile.update punishment who own) who

/-- The lowest best-response value the other players can impose.  On an empty
profile carrier this inherits `iInf`'s empty-index convention; no minmax claim
is made there. -/
def opponentMinmaxLevel (G : UtilityGame ι) [DecidableEq ι]
    (who : ι) : ℝ :=
  ⨅ punishment : Profile G.form.sig,
    G.bestResponseValueAgainstPunishment who punishment

/-- Opponent-enforced punishment levels for all players. -/
def opponentMinmaxVector (G : UtilityGame ι) [DecidableEq ι] :
    PayoffVector ι :=
  fun who => G.opponentMinmaxLevel who

theorem exists_punishment_bestResponseValue_lt_add
    (G : UtilityGame ι) [DecidableEq ι]
    (who : ι) [Nonempty (Profile G.form.sig)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ punishment : Profile G.form.sig,
      G.bestResponseValueAgainstPunishment who punishment <
        G.opponentMinmaxLevel who + ε := by
  have hlt :
      G.opponentMinmaxLevel who < G.opponentMinmaxLevel who + ε :=
    lt_add_of_pos_right _ hε
  simpa [opponentMinmaxLevel] using
    (exists_lt_of_ciInf_lt
      (f := fun punishment : Profile G.form.sig =>
        G.bestResponseValueAgainstPunishment who punishment)
      hlt)

theorem stagePayoff_update_le_bestResponseValue
    (G : UtilityGame ι) [DecidableEq ι]
    (who : ι) (punishment : Profile G.form.sig)
    (hbounded : BddAbove (Set.range fun own : G.form.sig.Strategy who =>
      G.stagePayoff (Profile.update punishment who own) who))
    (own : G.form.sig.Strategy who) :
    G.stagePayoff (Profile.update punishment who own) who ≤
      G.bestResponseValueAgainstPunishment who punishment :=
  le_ciSup hbounded own

theorem exists_approx_punishmentProfiles
    (G : UtilityGame ι) [DecidableEq ι]
    [Nonempty (Profile G.form.sig)]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ punishment : ι → Profile G.form.sig,
      ∀ who,
        G.bestResponseValueAgainstPunishment who (punishment who) <
          G.opponentMinmaxLevel who + ε := by
  choose punishment hpunishment using
    fun who => G.exists_punishment_bestResponseValue_lt_add who hε
  exact ⟨punishment, hpunishment⟩

/-- Strict coordinatewise domination over finitely many players has a common
positive slack. -/
theorem exists_pos_margin_of_mem_strictReservationSet
    [Fintype ι] {reservation value : PayoffVector ι}
    (hvalue : value ∈ strictReservationSet reservation) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ who, reservation who + margin ≤ value who := by
  by_cases hplayers : Nonempty ι
  · letI : Nonempty ι := hplayers
    let minimum : ℝ :=
      Finset.univ.inf' Finset.univ_nonempty
        (fun who : ι => value who - reservation who)
    have hminimum : 0 < minimum := by
      rw [Finset.lt_inf'_iff]
      intro who _
      exact sub_pos.mpr (hvalue who)
    refine ⟨minimum / 2, half_pos hminimum, ?_⟩
    intro who
    have hle :
        minimum ≤ value who - reservation who :=
      Finset.inf'_le _ (Finset.mem_univ who)
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro who
    exact False.elim (hplayers ⟨who⟩)

theorem exists_pos_margin_of_mem_strictIndividuallyRationalPayoffSet
    (G : UtilityGame ι) [Fintype ι]
    {reservation value : PayoffVector ι}
    (hvalue : value ∈ G.strictIndividuallyRationalPayoffSet reservation) :
    ∃ margin : ℝ, 0 < margin ∧
      ∀ who, reservation who + margin ≤ value who :=
  exists_pos_margin_of_mem_strictReservationSet hvalue.2

/-- Turn integer multiplicities into one finite cycle. -/
def cycleOfCounts (G : UtilityGame ι)
    {κ : Type} [Fintype κ]
    (count : κ → ℕ) (profile : κ → Profile G.form.sig) :
    Fin (Fintype.card (Sigma fun k => Fin (count k))) →
      Profile G.form.sig :=
  fun t =>
    profile (((Fintype.equivFin (Sigma fun k => Fin (count k))).symm t).1)

theorem sum_stagePayoff_cycleOfCounts
    (G : UtilityGame ι) {κ : Type} [Fintype κ]
    (count : κ → ℕ) (profile : κ → Profile G.form.sig) (who : ι) :
    (∑ t : Fin (Fintype.card (Sigma fun k => Fin (count k))),
        G.stagePayoff (G.cycleOfCounts count profile t) who) =
      ∑ k, (count k : ℝ) * G.stagePayoff (profile k) who := by
  rw [show
      (∑ t : Fin (Fintype.card (Sigma fun k => Fin (count k))),
          G.stagePayoff (G.cycleOfCounts count profile t) who) =
        ∑ a : Sigma fun k => Fin (count k),
          G.stagePayoff (profile a.1) who from ?_]
  · rw [Fintype.sum_sigma]
    simp [Finset.sum_const, nsmul_eq_mul]
  · exact
      (Fintype.sum_equiv
        (Fintype.equivFin (Sigma fun k => Fin (count k)))
        (fun a : Sigma fun k => Fin (count k) =>
          G.stagePayoff (profile a.1) who)
        (fun t : Fin (Fintype.card (Sigma fun k => Fin (count k))) =>
          G.stagePayoff (G.cycleOfCounts count profile t) who)
        (fun a => by simp [cycleOfCounts])).symm

/-- Every feasible vector is approximated by the uniform average of a finite
stage-profile cycle. -/
theorem exists_cycleAveragePayoff_close_of_mem_feasibleSet
    (G : UtilityGame ι) [Fintype ι]
    {value : PayoffVector ι} (hvalue : value ∈ G.feasibleSet)
    {bound ε : ℝ}
    (hbound : ∀ (profile : Profile G.form.sig) (who : ι),
      |G.stagePayoff profile who| ≤ bound)
    (hbound0 : 0 ≤ bound) (hε : 0 < ε) :
    ∃ (n : ℕ) (_ : NeZero n) (cycle : Fin n → Profile G.form.sig),
      ∀ who, |G.cycleAveragePayoff cycle who - value who| < ε := by
  classical
  rcases G.exists_fintype_weighted_profiles_apply_of_mem_feasibleSet
      hvalue with
    ⟨κ, hκ, weight, profile, hnonneg, hsum, hvalueSum⟩
  letI : Fintype κ := hκ
  have hκ : Nonempty κ := by
    by_contra hempty
    haveI : IsEmpty κ := not_nonempty_iff.mp hempty
    simp at hsum
  letI : Nonempty κ := hκ
  let errorBound : ℝ :=
    (Fintype.card κ : ℝ) * ((Fintype.card κ : ℝ) * bound)
  have herrorBound : 0 ≤ errorBound :=
    mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) hbound0)
  obtain ⟨denominator, hdenominator⟩ :=
    exists_nat_gt (errorBound / ε)
  have hdenominatorPos : 0 < denominator := by
    by_contra hnot
    have hzero : denominator = 0 := Nat.eq_zero_of_not_pos hnot
    have hdiv : 0 ≤ errorBound / ε := div_nonneg herrorBound hε.le
    have : errorBound / ε < 0 := by
      simpa [hzero] using hdenominator
    linarith
  have herrorLt : errorBound < (denominator : ℝ) * ε :=
    (div_lt_iff₀ hε).1 hdenominator
  let base : κ := Classical.choice hκ
  let count : κ → ℕ :=
    GameTheoryMath.SimplexApproximation.residualFloorCounts
      base weight denominator
  let n : ℕ := Fintype.card (Sigma fun k => Fin (count k))
  have hn : n = denominator := by
    dsimp [n, count]
    rw [Fintype.card_sigma]
    simp [GameTheoryMath.SimplexApproximation.sum_residualFloorCounts
      base hnonneg hsum denominator]
  have hn0 : n ≠ 0 := by
    rw [hn]
    exact Nat.ne_of_gt hdenominatorPos
  letI : NeZero n := ⟨hn0⟩
  let cycle : Fin n → Profile G.form.sig := by
    dsimp [n]
    exact G.cycleOfCounts count profile
  refine ⟨n, inferInstance, cycle, ?_⟩
  intro who
  let payoff : κ → ℝ :=
    fun k => G.stagePayoff (profile k) who
  have hdenominatorReal : (denominator : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hdenominatorPos
  have hcycle :
      G.cycleAveragePayoff cycle who =
        (n : ℝ)⁻¹ * ∑ k, (count k : ℝ) * payoff k := by
    have hcycleSum :
        (∑ t : Fin n, G.stagePayoff (cycle t) who) =
          ∑ k, (count k : ℝ) * payoff k := by
      dsimp [cycle, n]
      simpa [payoff] using
        G.sum_stagePayoff_cycleOfCounts count profile who
    rw [cycleAveragePayoff, hcycleSum]
  have herror :
      (denominator : ℝ)⁻¹ *
          (∑ k, (count k : ℝ) * payoff k) -
        ∑ k, weight k * payoff k =
      (denominator : ℝ)⁻¹ *
        ∑ k, (((count k : ℝ) -
          (denominator : ℝ) * weight k) * payoff k) := by
    field_simp [hdenominatorReal]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have habs :
      |∑ k, (((count k : ℝ) -
          (denominator : ℝ) * weight k) * payoff k)| ≤
        errorBound := by
    calc
      |∑ k, (((count k : ℝ) -
          (denominator : ℝ) * weight k) * payoff k)| ≤
          ∑ k, |(((count k : ℝ) -
            (denominator : ℝ) * weight k) * payoff k)| := by
        simpa using Finset.abs_sum_le_sum_abs
          (fun k => (((count k : ℝ) -
            (denominator : ℝ) * weight k) * payoff k))
          Finset.univ
      _ ≤ ∑ _k : κ, (Fintype.card κ : ℝ) * bound := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul
          (GameTheoryMath.SimplexApproximation.residualFloorCounts_abs_error_le_card
            base hnonneg hsum denominator k)
          (hbound (profile k) who)
          (abs_nonneg (payoff k))
          (Nat.cast_nonneg _)
      _ = errorBound := by
        simp [errorBound, Finset.sum_const, nsmul_eq_mul]
  have hscaled :
      |(denominator : ℝ)⁻¹ *
        ∑ k, (((count k : ℝ) -
          (denominator : ℝ) * weight k) * payoff k)| < ε := by
    rw [abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg denominator))]
    have hle :
        (denominator : ℝ)⁻¹ *
            |∑ k, (((count k : ℝ) -
              (denominator : ℝ) * weight k) * payoff k)| ≤
          (denominator : ℝ)⁻¹ * errorBound :=
      mul_le_mul_of_nonneg_left habs
        (inv_nonneg.mpr (Nat.cast_nonneg denominator))
    have hlt : (denominator : ℝ)⁻¹ * errorBound < ε := by
      have hpositive : 0 < (denominator : ℝ) := by
        exact_mod_cast hdenominatorPos
      have hmul := mul_lt_mul_of_pos_left herrorLt
        (inv_pos.mpr hpositive)
      have hright :
          (denominator : ℝ)⁻¹ *
            ((denominator : ℝ) * ε) = ε := by
        field_simp [ne_of_gt hpositive]
      simpa [hright] using hmul
    exact hle.trans_lt hlt
  calc
    |G.cycleAveragePayoff cycle who - value who| =
        |(denominator : ℝ)⁻¹ *
            (∑ k, (count k : ℝ) * payoff k) -
          ∑ k, weight k * payoff k| := by
      rw [hcycle, hvalueSum who, hn]
    _ = |(denominator : ℝ)⁻¹ *
        ∑ k, (((count k : ℝ) -
          (denominator : ℝ) * weight k) * payoff k)| := by
      rw [herror]
    _ < ε := hscaled

end UtilityGame

end GameTheory
