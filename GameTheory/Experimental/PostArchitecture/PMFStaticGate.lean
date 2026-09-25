/-
EXP-122 consumer: an infinite correlated law is tested against the canonical
static game, preference, and equilibrium definitions.
-/

import GameTheory.Core.Utility
import GameTheory.Core.CorrelatedDominance
import GameTheory.Languages.NFG
import GameTheory.Experimental.PostArchitecture.PMFRestorationProbe
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

namespace GameTheory.Experimental.PMFStaticGate

open GameTheory GameTheory.Math.Probability
open GameTheory.Languages.NFG
open GameTheory.Experimental.PMFRestoration

abbrev Player := Fin 2

abbrev boolCoordinationGame : Game Player where
  Action _ := Bool
  Outcome := Bool × Bool
  outcome profile := (profile 0, profile 1)

abbrev boolCoordinationForm : GameForm Player := boolCoordinationGame.toGameForm

def boolCoordinationUtility (outcome : boolCoordinationForm.sig.Outcome)
    (_player : Player) : ℝ :=
  if outcome.1 = outcome.2 then 1 else 0

abbrev coordinationSignature : GameSignature Player where
  Strategy _ := ℕ
  Outcome := ℕ × ℕ

abbrev coordinationForm : GameForm Player :=
  { sig := coordinationSignature
    play profile := PMF.pure (profile 0, profile 1) }

def coordinationUtility (outcome : ℕ × ℕ) (_player : Player) : ℝ :=
  if Even outcome.1 ↔ Even outcome.2 then 1 else 0

def diagonalProfile (n : ℕ) : Profile coordinationSignature := fun _ => n

def diagonalLaw : PMF (Profile coordinationSignature) :=
  geometric.map diagonalProfile

def evenGeometric : PMF ℕ :=
  geometric.filter {n | Even n} ⟨0, by decide, (geometric_positive 0).ne'⟩

theorem evenGeometric_support : evenGeometric.support = {n | Even n} := by
  rw [evenGeometric, PMF.support_filter, geometric_support, Set.inter_univ]

def evenMixedProfile : Profile coordinationForm.mixed.sig :=
  fun _ => evenGeometric

theorem diagonalProfile_injective : Function.Injective diagonalProfile := by
  intro n m h
  have hfirst := congrFun h 0
  simpa [diagonalProfile] using hfirst

theorem diagonalLaw_mem_support (n : ℕ) :
    diagonalProfile n ∈ diagonalLaw.support := by
  rw [diagonalLaw, PMF.mem_support_map_iff]
  exact ⟨n, (geometric_positive n).ne', rfl⟩

theorem diagonalLaw_infinite_support : diagonalLaw.support.Infinite := by
  apply (Set.infinite_range_of_injective diagonalProfile_injective).mono
  rintro _ ⟨n, rfl⟩
  exact diagonalLaw_mem_support n

theorem diagonal_outcomeLaw :
    coordinationForm.outcomeLaw diagonalLaw =
      geometric.map fun n => (n, n) := by
  calc
    coordinationForm.outcomeLaw diagonalLaw =
        geometric.bind (fun n => coordinationForm.play (diagonalProfile n)) := by
          rw [GameForm.outcomeLaw, diagonalLaw, PMF.bind_map]
          rfl
    _ = geometric.bind (PMF.pure ∘ fun n : ℕ => (n, n)) := by
      congr 1
    _ = geometric.map (fun n : ℕ => (n, n)) :=
      PMF.bind_pure_comp (fun n : ℕ => (n, n)) geometric

theorem diagonal_outcomeLaw_infinite_support :
    (coordinationForm.outcomeLaw diagonalLaw).support.Infinite := by
  rw [diagonal_outcomeLaw]
  have hinj : Function.Injective (fun n : ℕ => (n, n)) := by
    intro n m h
    exact congrArg Prod.fst h
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  rw [PMF.mem_support_map_iff]
  exact ⟨n, (geometric_positive n).ne', rfl⟩

theorem evenMixedProfile_play_supported :
    ∀ outcome : ℕ × ℕ,
      outcome ∈ (coordinationForm.mixed.play evenMixedProfile).support →
      (Even outcome.1 ↔ Even outcome.2) := by
  intro outcome hout
  rw [PMF.mem_support_bind_iff] at hout
  obtain ⟨profile, hprofile, hout⟩ := hout
  have hcoord := (independentProduct_support_iff
    (fun _ : Player => evenGeometric) profile).mp hprofile
  have hout' : outcome ∈ (PMF.pure (profile 0, profile 1)).support := by
    simpa only [coordinationForm] using hout
  rw [PMF.mem_support_pure_iff] at hout'
  subst outcome
  simp only [evenGeometric_support] at hcoord
  exact iff_of_true (hcoord 0) (hcoord 1)

theorem evenMixedProfile_play_infinite_support :
    (coordinationForm.mixed.play evenMixedProfile).support.Infinite := by
  rw [GameForm.mixed_play]
  have hinj : Function.Injective (fun n : ℕ => (2 * n, 0)) := by
    intro n m h
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (congrArg Prod.fst h)
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n, rfl⟩
  rw [PMF.mem_support_bind_iff]
  let profile : Profile coordinationSignature := fun i => if i = 0 then 2 * n else 0
  refine ⟨profile, ?_, ?_⟩
  · rw [independentProduct_support_iff]
    intro i
    show profile i ∈ evenGeometric.support
    rw [evenGeometric_support]
    by_cases hi : i = 0
    · subst i
      exact even_two_mul n
    · simp [profile, hi]
  · simp [profile]

theorem bounded_coordination_utility (outcome : ℕ × ℕ) (player : Player) :
    |coordinationUtility outcome player| ≤ 1 := by
  unfold coordinationUtility
  split_ifs <;> norm_num

def explodingUtility (n : ℕ) (_player : Player) : ℝ := exploding n

theorem explodingUtility_not_integrable :
    ¬ UtilityIntegrable explodingUtility 0 geometric := by
  intro h
  have hsum : Summable (fun n => (geometric n).toReal * exploding n) := by
    have hterm (n : ℕ) : |exploding n| = exploding n :=
      abs_of_nonneg (by rw [exploding]; positivity)
    simpa only [UtilityIntegrable, PayoffIntegrable, explodingUtility, hterm]
      using h
  exact exploding_not_summable hsum

abbrev singletonSignature : GameSignature Player where
  Strategy _ := Unit
  Outcome := ℕ

abbrev singletonForm : GameForm Player where
  sig := singletonSignature
  play _ := geometric

def singletonProfile : Profile singletonForm.sig := fun _ => ()

theorem singleton_action_is_strictlyDominant :
    ∀ who : Player,
      IsStrictDominant singletonForm (euPreference explodingUtility) who () := by
  intro who alternative halternative
  exact (halternative (Subsingleton.elim _ _)).elim

theorem singleton_profile_not_nash :
    ¬ IsNash singletonForm (euPreference explodingUtility) singletonProfile := by
  intro hnash
  obtain ⟨hincumbent, _, _⟩ :=
    (isNash_iff (F := singletonForm)
      (weaklyPrefers := euPreference explodingUtility) singletonProfile).mp hnash 0 ()
  exact explodingUtility_not_integrable (by
    simpa [singletonForm] using hincumbent)

theorem singleton_profile_not_coarse_correlated_eq :
    ¬ IsCoarseCorrelatedEq singletonForm (euPreference explodingUtility)
      (PMF.pure singletonProfile) := by
  intro hcce
  obtain ⟨hincumbent, _, _⟩ :=
    (isCoarseCorrelatedEq_iff (F := singletonForm)
      (weaklyPrefers := euPreference explodingUtility)
      (PMF.pure singletonProfile)).mp hcce 0 ()
  exact explodingUtility_not_integrable (by
    simpa [singletonForm, GameForm.outcomeLaw] using hincumbent)

theorem euPreference_rejects_undefined_incumbent :
    ¬ euPreference explodingUtility 0 geometric (PMF.pure 0) := by
  rintro ⟨hbase, _, _⟩
  exact explodingUtility_not_integrable hbase

theorem euPreference_rejects_undefined_alternative :
    ¬ euPreference explodingUtility 0 (PMF.pure 0) geometric := by
  rintro ⟨_, halt, _⟩
  exact explodingUtility_not_integrable halt

def linearUtility (n : ℕ) (_player : Player) : ℝ := n + 1

theorem linearUtility_unbounded :
    ¬ ∃ C, ∀ n : ℕ, |linearUtility n 0| ≤ C := by
  rintro ⟨C, hC⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hle := hC n
  have hn0 : 0 ≤ (n : ℝ) + 1 := by positivity
  have hle' : (n : ℝ) + 1 ≤ C := by
    simpa [linearUtility, abs_of_nonneg hn0] using hle
  linarith

theorem linearUtility_integrable_geometric :
    UtilityIntegrable linearUtility 0 geometric := by
  have hpow : Summable (fun n : ℕ =>
      ‖(n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n‖) :=
    summable_norm_pow_mul_geometric_of_norm_lt_one 1 (by norm_num)
  have hscaled := hpow.mul_left (1 / 2 : ℝ)
  have hn : Summable (fun n : ℕ =>
      (geometric n).toReal * |(n : ℝ)|) := by
    apply hscaled.congr
    intro n
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hp0 : 0 ≤ (1 / 2 : ℝ) ^ n := pow_nonneg (by norm_num) _
    rw [geometric_real, Real.norm_eq_abs, pow_one,
      abs_of_nonneg hn0, abs_of_nonneg (mul_nonneg hn0 hp0)]
    have hpowInv : (1 / 2 : ℝ) ^ n = ((2 : ℝ) ^ n)⁻¹ := by
      simp only [one_div, inv_pow]
    rw [hpowInv, div_eq_mul_inv]
    field_simp
  have hone : Summable (fun n : ℕ => (geometric n).toReal * |(1 : ℝ)|) := by
    simpa only [abs_of_nonneg (by norm_num : 0 ≤ (1 : ℝ)), mul_one] using
      (pmf_weight_summable geometric)
  have hlinear : PayoffIntegrable geometric (fun n => linearUtility n 0) := by
    have hadd := hn.add hone
    apply hadd.congr
    intro n
    simp only [linearUtility]
    rw [abs_of_nonneg (by positivity : 0 ≤ (n : ℝ)),
      abs_of_nonneg (by norm_num : 0 ≤ (1 : ℝ)),
      abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
    ring
  exact hlinear

theorem unbounded_integrable_utility_has_positive_eu :
    ∃ h : UtilityIntegrable linearUtility 0 geometric,
      0 < expectedUtility linearUtility 0 geometric h := by
  have hcert := linearUtility_integrable_geometric
  refine ⟨hcert, ?_⟩
  have hconst : PayoffIntegrable geometric (fun _ : ℕ => (1 : ℝ)) :=
    payoffIntegrable_of_bounded geometric _ (C := 1) (by intro _; norm_num)
  have hle := expect_mono (μ := geometric)
    (f := fun _ => (1 : ℝ)) (g := fun n => linearUtility n 0)
    (fun n _ => by simp [linearUtility]) hconst hcert
  rw [expect_constant geometric 1 hconst] at hle
  calc
    0 < 1 := by norm_num
    _ ≤ expectedUtility linearUtility 0 geometric hcert := by
      simpa only [expectedUtility] using hle

theorem finite_bool_expect_eq_sum (μ : PMF Bool) (f : Bool → ℝ)
    (h : PayoffIntegrable μ f) :
    expect μ f h = (μ false).toReal * f false + (μ true).toReal * f true := by
  rw [expect_eq_sum]
  simp only [Fintype.sum_bool]
  ring

theorem bool_nfg_pure_payoff (profile : Profile boolCoordinationGame.signature)
    (player : Player) :
    expectedUtility boolCoordinationUtility player
        (boolCoordinationForm.play profile)
        (payoffIntegrable_pure (boolCoordinationGame.outcome profile)
          (fun outcome => boolCoordinationUtility outcome player)) =
      boolCoordinationUtility (boolCoordinationGame.outcome profile) player := by
  simp [boolCoordinationForm]

theorem bool_nfg_coordinated_is_nash
    (profile : Profile boolCoordinationGame.signature)
    (hcoord : profile 0 = profile 1) :
    IsNash boolCoordinationForm (euPreference boolCoordinationUtility) profile := by
  rw [isNash_iff]
  simp only [boolCoordinationForm]
  intro player replacement
  rw [euPreference_pure_iff]
  fin_cases player
  · simp [boolCoordinationUtility, hcoord, Profile.update_of_ne]
    split_ifs <;> norm_num
  · simp [boolCoordinationUtility, hcoord, Profile.update_of_ne]
    split_ifs <;> norm_num

theorem bool_nfg_not_coordinated_not_nash
    (profile : Profile boolCoordinationGame.signature)
    (hcoord : profile 0 ≠ profile 1) :
    ¬ IsNash boolCoordinationForm (euPreference boolCoordinationUtility) profile := by
  intro hnash
  rw [isNash_iff] at hnash
  simp only [boolCoordinationForm] at hnash
  have hdev := hnash 0 (profile 1)
  rw [euPreference_pure_iff] at hdev
  simp [boolCoordinationUtility, hcoord, Profile.update_of_ne] at hdev
  norm_num at hdev

theorem coordination_optimal_of_always_coordinated (player : Player)
    (preferred : PMF (ℕ × ℕ))
    (hpreferred : ∀ outcome ∈ preferred.support,
      (Even outcome.1 ↔ Even outcome.2))
    (alternative : PMF (ℕ × ℕ)) :
    euPreference coordinationUtility player preferred alternative := by
  let payoff (outcome : ℕ × ℕ) := coordinationUtility outcome player
  let hpref : UtilityIntegrable coordinationUtility player preferred :=
    payoffIntegrable_of_bounded preferred payoff (C := 1) (by
      intro outcome
      exact bounded_coordination_utility outcome player)
  let halt : UtilityIntegrable coordinationUtility player alternative :=
    payoffIntegrable_of_bounded alternative payoff (C := 1) (by
      intro outcome
      exact bounded_coordination_utility outcome player)
  let hconstPref : PayoffIntegrable preferred (fun _ : ℕ × ℕ => (1 : ℝ)) :=
    payoffIntegrable_of_bounded preferred _ (C := 1) (by intro _; norm_num)
  let hconstAlt : PayoffIntegrable alternative (fun _ : ℕ × ℕ => (1 : ℝ)) :=
    payoffIntegrable_of_bounded alternative _ (C := 1) (by intro _; norm_num)
  have heq : expect preferred payoff hpref =
      expect preferred (fun _ => (1 : ℝ)) hconstPref := by
    apply expect_congr_on_support
    · intro outcome ho
      simp [payoff, coordinationUtility, hpreferred outcome ho]
  have hval : expect preferred payoff hpref = 1 := by
    rw [heq, expect_constant]
  have hle : expect alternative payoff halt ≤ 1 := by
    calc
      expect alternative payoff halt ≤
          expect alternative (fun _ => (1 : ℝ)) hconstAlt := by
        apply expect_mono
        · intro outcome _
          unfold payoff coordinationUtility
          split_ifs <;> norm_num
      _ = 1 := expect_constant alternative 1 hconstAlt
  have hlePref : expect alternative payoff halt ≤ expect preferred payoff hpref := by
    rw [hval]
    exact hle
  exact ⟨hpref, halt, by simpa [expectedUtility, payoff] using hlePref⟩

theorem diagonal_is_coarse_correlated_equilibrium :
    IsCoarseCorrelatedEq coordinationForm (euPreference coordinationUtility)
      diagonalLaw := by
  rw [isCoarseCorrelatedEq_iff]
  intro player replacement
  apply coordination_optimal_of_always_coordinated
  intro outcome hout
  rw [diagonal_outcomeLaw, PMF.mem_support_map_iff] at hout
  obtain ⟨n, hn, rfl⟩ := hout
  exact Iff.rfl

theorem diagonal_is_correlated_equilibrium :
    IsCorrelatedEq coordinationForm (euPreference coordinationUtility)
      diagonalLaw := by
  rw [isCorrelatedEq_iff]
  intro player respond
  apply coordination_optimal_of_always_coordinated
  intro outcome hout
  rw [diagonal_outcomeLaw, PMF.mem_support_map_iff] at hout
  obtain ⟨n, hn, rfl⟩ := hout
  exact Iff.rfl

theorem diagonal_is_randomized_equilibrium :
    IsEquilibrium coordinationForm (euPreference coordinationUtility) diagonalLaw
      (DeviationScheme.unilateralRandomized coordinationSignature) := by
  apply isCoarseCorrelatedEq_randomized diagonal_is_coarse_correlated_equilibrium
  intro player replacement
  exact payoffIntegrable_of_bounded
    (coordinationForm.outcomeLaw
      ((DeviationScheme.unilateralRandomized coordinationSignature).apply
        diagonalLaw player replacement))
    (fun outcome => coordinationUtility outcome player) (C := 1)
    (fun outcome => bounded_coordination_utility outcome player)

theorem even_mixed_profile_is_nash :
    IsNash coordinationForm.mixed (euPreference coordinationUtility)
      evenMixedProfile := by
  have hdev : ∀ player (replacement : PMF (ℕ)),
      UtilityIntegrable coordinationUtility player
        (coordinationForm.mixed.play
          (Profile.update evenMixedProfile player replacement)) := by
    intro player replacement
    exact payoffIntegrable_of_bounded
      (coordinationForm.mixed.play
        (Profile.update evenMixedProfile player replacement))
      (fun outcome => coordinationUtility outcome player) (C := 1)
      (fun outcome => bounded_coordination_utility outcome player)
  apply (isNash_mixed_iff evenMixedProfile hdev).2
  intro player strategy
  apply coordination_optimal_of_always_coordinated
    player (coordinationForm.mixed.play evenMixedProfile)
    evenMixedProfile_play_supported

end GameTheory.Experimental.PMFStaticGate
