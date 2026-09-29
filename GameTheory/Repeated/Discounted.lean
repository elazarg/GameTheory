/-
# Discounted repeated games

Normalized discounted payoff evaluates the deterministic stage-profile path
from `Basic`. The only infinite object is an ordinary real series; there is no
PMF over infinite histories. The induced strategic form is
`UtilityGame.repeatedForm`, so discounted equilibrium is ordinary `IsNash`.
-/

import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import GameTheory.Math.Discounted
import GameTheory.Repeated.Basic

noncomputable section

open scoped BigOperators

namespace GameTheory

open GameTheory.Math.Probability

universe uι

variable {ι : Type uι}

namespace UtilityGame

/-- Normalized discounted expected payoff of a repeated profile. -/
def discountedPayoff (G : UtilityGame ι) (discount : ℝ)
    (profile : G.RepeatedProfile) (who : ι)
    (_hsum : Summable fun t : ℕ =>
      discount ^ t * G.stagePayoff (G.repeatedPlay profile t) who) : ℝ :=
  GameTheory.Math.normalizedDiscountedSum discount fun t =>
    G.stagePayoff (G.repeatedPlay profile t) who

/-- Discounted utility on the existing repeated form. -/
def discountedUtility (G : UtilityGame ι) (discount : ℝ)
    (hsum : ∀ profile : G.RepeatedProfile, ∀ who,
      Summable fun t : ℕ => discount ^ t *
        G.stagePayoff (G.repeatedPlay profile t) who) :
    Utility G.repeatedSignature :=
  fun profile who => G.discountedPayoff discount profile who
     (hsum profile who)

/-- Normalized discounted continuation payoff of an explicit stage-profile
path, starting at `start`. -/
def discountedContinuationPayoff (G : UtilityGame ι) (discount : ℝ)
    (path : ℕ → Profile G.form.sig) (start : ℕ) (who : ι)
    (_hsum : Summable fun k : ℕ =>
      discount ^ k * G.stagePayoff (path (start + k)) who) : ℝ :=
  GameTheory.Math.normalizedDiscountedSum discount fun k =>
    G.stagePayoff (path (start + k)) who

/-- A repeated profile's discounted payoff is its zero-start continuation. -/
theorem discountedPayoff_eq_discountedContinuationPayoff_zero
    (G : UtilityGame ι) (discount : ℝ) (profile : G.RepeatedProfile)
    (who : ι)
    (hsum : Summable fun t : ℕ =>
      discount ^ t * G.stagePayoff (G.repeatedPlay profile t) who) :
    G.discountedPayoff discount profile who hsum =
      G.discountedContinuationPayoff discount
        (fun t => G.repeatedPlay profile t) 0 who
         (by simpa using hsum) := by
  simp [discountedPayoff, discountedContinuationPayoff,
    GameTheory.Math.normalizedDiscountedSum]

/-- Bounded stage payoffs give a summable discounted series whenever the
discount factor lies in `[0, 1)`. -/
theorem summable_discounted_stagePayoff_of_abs_bound
    (G : UtilityGame ι) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    {profile : G.RepeatedProfile} (who : ι)
    (hbound : ∀ t,
      |G.stagePayoff (G.repeatedPlay profile t) who| ≤ bound) :
    Summable fun t : ℕ =>
      discount ^ t * G.stagePayoff (G.repeatedPlay profile t) who := by
  have hgeom : Summable fun t : ℕ => bound * discount ^ t :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound
  refine Summable.of_norm_bounded hgeom ?_
  intro t
  rw [Real.norm_eq_abs]
  calc
    |discount ^ t * G.stagePayoff (G.repeatedPlay profile t) who| =
        discount ^ t *
          |G.stagePayoff (G.repeatedPlay profile t) who| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hdiscount0 t)]
    _ ≤ discount ^ t * bound :=
      mul_le_mul_of_nonneg_left
        (hbound t) (pow_nonneg hdiscount0 t)
    _ = bound * discount ^ t := by ring

/-- Bounded stage payoffs make every explicit continuation summable. -/
theorem summable_discounted_continuation_of_abs_bound
    (G : UtilityGame ι) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (path : ℕ → Profile G.form.sig) (start : ℕ) (who : ι)
    (hbound : ∀ k,
      |G.stagePayoff (path (start + k)) who| ≤ bound) :
    Summable fun k : ℕ =>
      discount ^ k * G.stagePayoff (path (start + k)) who := by
  have hgeom : Summable fun k : ℕ => bound * discount ^ k :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_left bound
  refine Summable.of_norm_bounded hgeom ?_
  intro k
  rw [Real.norm_eq_abs]
  calc
    |discount ^ k * G.stagePayoff (path (start + k)) who| =
        discount ^ k * |G.stagePayoff (path (start + k)) who| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hdiscount0 k)]
    _ ≤ discount ^ k * bound :=
      mul_le_mul_of_nonneg_left
        (hbound k) (pow_nonneg hdiscount0 k)
    _ = bound * discount ^ k := by ring

/-- The bounded specialization supplies the actual summability certificate to
the canonical repeated-profile evaluator. -/
abbrev discountedPayoffOfBounded (G : UtilityGame ι)
    {discount bound : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) (profile : G.RepeatedProfile) (who : ι)
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound) : ℝ :=
  G.discountedPayoff discount profile who
    (G.summable_discounted_stagePayoff_of_abs_bound
      hdiscount0 hdiscount1 who
      (fun t => hbound (G.repeatedPlay profile t)))

/-- The bounded specialization supplies the actual summability certificate to
the canonical path continuation evaluator. -/
abbrev discountedContinuationPayoffOfBounded (G : UtilityGame ι)
    {discount bound : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) (path : ℕ → Profile G.form.sig)
    (start : ℕ) (who : ι)
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound) : ℝ :=
  G.discountedContinuationPayoff discount path start who
    (G.summable_discounted_continuation_of_abs_bound
      hdiscount0 hdiscount1 path start who
      (fun k => hbound (path (start + k))))

/-- A bounded stage game supplies the per-profile certificates required by
the canonical total repeated utility constructor. -/
abbrev discountedUtilityOfBounded (G : UtilityGame ι)
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ stage : Profile G.form.sig,
        |G.stagePayoff stage who| ≤ bound) :
    Utility G.repeatedSignature :=
  G.discountedUtility discount
      (fun profile who =>
      G.summable_discounted_stagePayoff_of_abs_bound
        hdiscount0 hdiscount1 who
        (fun t => (hbound who).choose_spec (G.repeatedPlay profile t)))

/-- With finite outcomes, each player's stage expected payoff has a finite
absolute bound, even when there are infinitely many players or strategies. -/
theorem exists_stagePayoff_abs_bound_of_finiteOutcome
    (G : UtilityGame ι) [Finite G.form.sig.Outcome] (who : ι) :
    ∃ bound : ℝ, ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound := by
  have hfinite :
      (Set.range fun outcome : G.form.sig.Outcome =>
        |G.utility outcome who|).Finite := Set.finite_range _
  obtain ⟨C, hC⟩ := hfinite.bddAbove
  refine ⟨max C 0, fun stage => ?_⟩
  have hcoordinate (outcome : G.form.sig.Outcome) :
      |G.utility outcome who| ≤ max C 0 :=
    (hC ⟨outcome, rfl⟩).trans (le_max_left C 0)
  exact expect_abs_le_of_bounded (le_max_right C 0) hcoordinate

/-- Finite outcomes transparently supply the guards for the canonical total
discounted utility. No player or strategy finiteness is required. -/
abbrev discountedUtilityOfFiniteOutcome (G : UtilityGame ι)
    [Finite G.form.sig.Outcome]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) : Utility G.repeatedSignature :=
  G.discountedUtilityOfBounded hdiscount0 hdiscount1
    (G.exists_stagePayoff_abs_bound_of_finiteOutcome)

/-- Finite outcomes transparently supply the guards for one canonical
discounted path payoff. -/
abbrev discountedPayoffOfFiniteOutcome (G : UtilityGame ι)
    [Finite G.form.sig.Outcome]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1)
    (profile : G.RepeatedProfile) (who : ι) : ℝ :=
  G.discountedPayoffOfBounded hdiscount0 hdiscount1 profile who
    (G.exists_stagePayoff_abs_bound_of_finiteOutcome who).choose_spec

/-- If every future stage payoff is at most `cap`, so is the normalized
continuation. -/
theorem discountedContinuationPayoff_le_const
    (G : UtilityGame ι) {discount cap : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (path : ℕ → Profile G.form.sig) (start : ℕ) (who : ι)
    (hsum : Summable fun k : ℕ =>
      discount ^ k * G.stagePayoff (path (start + k)) who)
    (hle : ∀ k : ℕ,
      G.stagePayoff (path (start + k)) who ≤ cap) :
    G.discountedContinuationPayoff discount path start who hsum ≤ cap := by
  have hconst : Summable fun k : ℕ => discount ^ k * cap :=
    (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_right cap
  have hsumLe :
      (∑' k : ℕ,
        discount ^ k * G.stagePayoff (path (start + k)) who) ≤
      ∑' k : ℕ, discount ^ k * cap := by
    exact hsum.tsum_le_tsum
      (fun k => mul_le_mul_of_nonneg_left (hle k)
        (pow_nonneg hdiscount0 k))
      hconst
  have hone : 1 - discount ≠ 0 := by linarith
  calc
    G.discountedContinuationPayoff discount path start who hsum ≤
        (1 - discount) * ∑' k : ℕ, discount ^ k * cap :=
      mul_le_mul_of_nonneg_left hsumLe (sub_nonneg.mpr hdiscount1.le)
    _ = cap := by
      rw [tsum_mul_right, tsum_geometric_of_lt_one hdiscount0 hdiscount1]
      field_simp [hone]

/-- Bellman split for normalized discounted continuations. -/
theorem discountedContinuationPayoff_eq_head_add
    (G : UtilityGame ι) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (path : ℕ → Profile G.form.sig) (start : ℕ) (who : ι)
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound) :
    G.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
        path start who hbound =
      (1 - discount) * G.stagePayoff (path start) who +
        discount *
          G.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
            path (start + 1) who hbound := by
  let term : ℕ → ℝ :=
    fun k => discount ^ k * G.stagePayoff (path (start + k)) who
  have hs : Summable term := by
    simpa [term] using G.summable_discounted_continuation_of_abs_bound
      hdiscount0 hdiscount1 path start who
      (fun k => hbound (path (start + k)))
  have hsplit : term 0 + (∑' k : ℕ, term (k + 1)) = ∑' k : ℕ, term k := by
    simpa using hs.sum_add_tsum_nat_add 1
  have htail :
      (∑' k : ℕ, term (k + 1)) =
        discount *
          ∑' k : ℕ,
            discount ^ k * G.stagePayoff (path (start + 1 + k)) who := by
    calc
      (∑' k : ℕ, term (k + 1)) =
          ∑' k : ℕ, discount *
            (discount ^ k *
              G.stagePayoff (path (start + 1 + k)) who) := by
        apply tsum_congr
        intro k
        have hindex : start + (k + 1) = start + 1 + k := by omega
        dsimp [term]
        rw [pow_succ, hindex]
        ring
      _ = discount *
          ∑' k : ℕ,
            discount ^ k * G.stagePayoff (path (start + 1 + k)) who := by
        rw [tsum_mul_left]
  calc
    G.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
        path start who hbound =
        (1 - discount) * ∑' k : ℕ, term k := by rfl
    _ = (1 - discount) * (term 0 + ∑' k : ℕ, term (k + 1)) := by
      rw [hsplit]
    _ = (1 - discount) * G.stagePayoff (path start) who +
        discount *
          G.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
            path (start + 1) who hbound := by
      rw [htail]
      simp [discountedContinuationPayoffOfBounded,
        discountedContinuationPayoff, term]
      ring

/-- Equal finite prefixes and an ordered tail give ordered continuations. -/
theorem discountedContinuationPayoff_le_of_prefix_eq_of_tail_le
    (G : UtilityGame ι) {discount bound : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (first second : ℕ → Profile G.form.sig) (start count : ℕ) (who : ι)
    (hbound : ∀ stage : Profile G.form.sig,
      |G.stagePayoff stage who| ≤ bound)
    (hprefix : ∀ k < count, first (start + k) = second (start + k))
    (htail :
      G.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
          first (start + count) who hbound ≤
        G.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
          second (start + count) who hbound) :
    G.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
        first start who hbound ≤
      G.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1
        second start who hbound := by
  revert start
  induction count with
  | zero =>
      intro start _ htail
      simpa using htail
  | succ count ih =>
      intro start hprefix htail
      have hhead : first start = second start := by
        simpa using hprefix 0 (Nat.succ_pos count)
      have htail' :
          G.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1 first
              (start + 1 + count) who hbound ≤
            G.discountedContinuationPayoffOfBounded hdiscount0 hdiscount1 second
              (start + 1 + count) who hbound := by
        simpa only [show start + (count + 1) = start + 1 + count by omega]
          using htail
      have hprefix' :
          ∀ k < count,
            first (start + 1 + k) = second (start + 1 + k) := by
        intro k hk
        have hk' : k + 1 < count + 1 := Nat.succ_lt_succ hk
        simpa only [show start + (k + 1) = start + 1 + k by omega]
          using hprefix (k + 1) hk'
      have hnext := ih (start + 1) hprefix' htail'
      rw [G.discountedContinuationPayoff_eq_head_add
        hdiscount0 hdiscount1 first start who hbound]
      rw [G.discountedContinuationPayoff_eq_head_add
        hdiscount0 hdiscount1 second start who hbound]
      rw [hhead]
      exact add_le_add_right
        (mul_le_mul_of_nonneg_left hnext hdiscount0) _

/-- Pointwise dominance of generated stage payoffs implies dominance of
normalized discounted payoffs. -/
theorem discountedPayoff_le_of_forall_stagePayoff_le
    (G : UtilityGame ι) {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    {first second : G.RepeatedProfile} (who : ι)
    (hfirstSum : Summable fun t : ℕ =>
      discount ^ t * G.stagePayoff (G.repeatedPlay first t) who)
    (hsecondSum : Summable fun t : ℕ =>
      discount ^ t * G.stagePayoff (G.repeatedPlay second t) who)
    (hle : ∀ t : ℕ,
      G.stagePayoff (G.repeatedPlay first t) who ≤
        G.stagePayoff (G.repeatedPlay second t) who) :
    G.discountedPayoff discount first who hfirstSum ≤
      G.discountedPayoff discount second who hsecondSum := by
  exact GameTheory.Math.normalizedDiscountedSum_le hdiscount0 hdiscount1
    hfirstSum hsecondSum hle

/-- Stationary repetition has the same normalized discounted payoff as its
stage profile. -/
theorem discountedPayoff_stationaryRepeatedProfile
    (G : UtilityGame ι) {discount : ℝ}
    (hdiscount0 : 0 ≤ discount) (hdiscount1 : discount < 1)
    (profile : Profile G.form.sig) (who : ι) :
    let hsum : Summable fun t : ℕ => discount ^ t *
        G.stagePayoff (G.repeatedPlay (G.stationaryRepeatedProfile profile) t)
          who := by
      simpa [G.repeatedPlay_stationaryRepeatedProfile] using
        (summable_geometric_of_lt_one hdiscount0 hdiscount1).mul_right
          (G.stagePayoff profile who)
    G.discountedPayoff discount (G.stationaryRepeatedProfile profile) who
         hsum = G.stagePayoff profile who := by
  dsimp only
  have hne : 1 - discount ≠ 0 := by linarith
  have hterm : ∀ t : ℕ,
      G.stagePayoff (G.repeatedPlay (G.stationaryRepeatedProfile profile) t)
        who = G.stagePayoff profile who := by
    intro t
    simp [stagePayoff]
  simp only [discountedPayoff, GameTheory.Math.normalizedDiscountedSum]
  simp_rw [hterm]
  rw [tsum_mul_right, tsum_geometric_of_lt_one hdiscount0 hdiscount1]
  field_simp [hne]

/-- Stationary repetition of a bounded stage Nash profile is ordinary Nash in
the repeated form under discounted utility. A deviation replaces the player's
whole history-dependent strategy; no repeated-specific equilibrium predicate
is introduced. -/
theorem stationaryRepeatedProfile_isNash_of_isNash_of_bounded
    (G : UtilityGame ι) [DecidableEq ι]
    {discount : ℝ} (hdiscount0 : 0 ≤ discount)
    (hdiscount1 : discount < 1) {profile : Profile G.form.sig}
    (hnash : IsNash G.form (euPreference G.utility) profile)
    (hstage : G.form.HasIntegrableUtility G.utility)
    (hbound : ∀ who : ι, ∃ bound : ℝ,
      ∀ stage : Profile G.form.sig,
        |G.stagePayoff stage who| ≤ bound) :
    IsNash G.repeatedForm
      (euPreference
        (G.discountedUtilityOfBounded hdiscount0 hdiscount1 hbound))
      (G.stationaryRepeatedProfile profile) := by
  rw [isNash_iff]
  intro who deviation
  obtain ⟨bound, hboundWho⟩ := hbound who
  let deviated := Profile.update (G.stationaryRepeatedProfile profile) who deviation
  have hleStage (t : ℕ) :
      G.stagePayoff (G.repeatedPlay deviated t) who ≤
        G.stagePayoff (G.repeatedPlay (G.stationaryRepeatedProfile profile) t)
          who := by
    rw [G.repeatedPlay_update_stationaryRepeatedProfile profile who deviation t]
    rw [G.repeatedPlay_stationaryRepeatedProfile profile t]
    have hstageNash := (isNash_iff profile).mp hnash who
      (deviation (List.ofFn fun k : Fin t => G.repeatedPlay deviated k))
    have hle := (euPreference_iff G.utility who
      (G.form.play profile)
      (G.form.play (Profile.update profile who
        (deviation (List.ofFn fun k : Fin t => G.repeatedPlay deviated k))))
      (hstage who profile) (hstage who _)).mp hstageNash
    exact hle
  have hdevSum := G.summable_discounted_stagePayoff_of_abs_bound
    hdiscount0 hdiscount1 who
    (fun t => hboundWho (G.repeatedPlay deviated t))
  have hbaseSum := G.summable_discounted_stagePayoff_of_abs_bound
    hdiscount0 hdiscount1 who
    (fun t => hboundWho
      (G.repeatedPlay (G.stationaryRepeatedProfile profile) t))
  have hleDiscount := G.discountedPayoff_le_of_forall_stagePayoff_le
    hdiscount0 hdiscount1 who
    hdevSum hbaseSum hleStage
  apply (euPreference_iff
    (G.discountedUtilityOfBounded hdiscount0 hdiscount1 hbound)
    who (G.repeatedForm.play (G.stationaryRepeatedProfile profile))
    (G.repeatedForm.play deviated)
    (by simpa [repeatedForm] using
      payoffIntegrable_pure (G.stationaryRepeatedProfile profile) _)
    (by simpa [repeatedForm] using payoffIntegrable_pure deviated _)).mpr
  simpa [repeatedForm, discountedUtilityOfBounded, discountedUtility,
    discountedPayoff, deviated] using hleDiscount

end UtilityGame

end GameTheory
