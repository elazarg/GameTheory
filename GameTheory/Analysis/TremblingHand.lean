/-
# Trembling-hand perfection

Core owns finite mixed perturbations and their restricted deviation scheme.
This one-way analytic leaf adds pointwise convergence and the resulting limit
refinement.  It never introduces another mixed extension or Nash predicate.

Primary reference: R. Selten, “Reexamination of the Perfectness Concept for
Equilibrium Points in Extensive Games,” *International Journal of Game
Theory* 4 (1975).
-/

import GameTheory.Analysis.ExpectedUtility
import GameTheory.Core.TremblingHand

noncomputable section

namespace GameTheory

open Filter GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

namespace Analysis

variable {F : GameForm ι}

/-- Pointwise convergence of every player's finite mixed strategy. -/
def MixedProfileConvergesPointwise
    (sequence : ℕ → Profile F.sig.mixed)
    (target : Profile F.sig.mixed) : Prop :=
  ∀ i, PMFConvergesPointwise (fun n => sequence n i) (target i)

omit [Fintype ι] [DecidableEq ι] in
theorem mixedProfileConvergesPointwise_const
    (profile : Profile F.sig.mixed) :
    MixedProfileConvergesPointwise (fun _ => profile) profile :=
  fun i => pmfConvergesPointwise_const (profile i)

/-- Pointwise convergence of every lower bound to zero. -/
def PerturbationConvergesToZero (F : GameForm ι)
    (sequence : ℕ → F.Perturbation) : Prop :=
  ∀ i action,
    Tendsto (fun n => sequence n i action) atTop (nhds 0)

end Analysis

namespace GameForm

variable (F : GameForm ι)

/-- A mixed profile is trembling-hand perfect when it is the pointwise limit
of equilibria of strictly positive perturbations whose lower bounds vanish. -/
def IsTremblingHandPerfect
    (weaklyPrefers : WeakPreference ι F.sig.Outcome)
    (profile : Profile F.sig.mixed) : Prop :=
  ∃ (lower : ℕ → F.Perturbation)
      (approximating : ℕ → Profile F.sig.mixed),
    (∀ n, (lower n).Positive ∧
      F.IsPerturbedEq weaklyPrefers (lower n) (approximating n)) ∧
      Analysis.PerturbationConvergesToZero F lower ∧
        Analysis.MixedProfileConvergesPointwise approximating profile

theorem isTremblingHandPerfect_iff
    (weaklyPrefers : WeakPreference ι F.sig.Outcome)
    (profile : Profile F.sig.mixed) :
    F.IsTremblingHandPerfect weaklyPrefers profile ↔
      ∃ (lower : ℕ → F.Perturbation)
          (approximating : ℕ → Profile F.sig.mixed),
        (∀ n, (lower n).Positive ∧
          F.IsPerturbedEq weaklyPrefers (lower n) (approximating n)) ∧
          Analysis.PerturbationConvergesToZero F lower ∧
            Analysis.MixedProfileConvergesPointwise approximating profile :=
  Iff.rfl

private def vanishingWeight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 2)

private theorem vanishingWeight_pos (n : ℕ) :
    0 < vanishingWeight n := by
  dsimp [vanishingWeight]
  exact one_div_pos.mpr
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))

private theorem vanishingWeight_le_one (n : ℕ) :
    vanishingWeight n ≤ 1 := by
  apply (div_le_one
    (add_pos_of_nonneg_of_pos (Nat.cast_nonneg n) (by norm_num))).2
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

private theorem vanishingWeight_tendsto_zero :
    Tendsto vanishingWeight atTop (nhds 0) := by
  have h :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
  convert h using 1
  funext n
  simp [vanishingWeight, Function.comp_apply, Nat.cast_add]
  ring

private def scaledPerturbation (profile : Profile F.sig.mixed)
    (n : ℕ) : F.Perturbation :=
  fun i action => vanishingWeight n * (profile i action).toReal

private def perturbationMass [∀ i, Fintype (F.sig.Strategy i)]
    (lower : F.Perturbation) (who : ι) : ℝ :=
  ∑ action, lower who action

/-- Every full-support mixed Nash equilibrium is trembling-hand perfect.  Its
own profile is feasible and remains optimal in each restricted game; scaling
its positive masses supplies a vanishing perturbation certificate. -/
theorem _root_.GameTheory.IsNash.isTremblingHandPerfect_of_fullSupport
    {weaklyPrefers : WeakPreference ι F.sig.Outcome}
    {profile : Profile F.sig.mixed}
    (hnash : IsNash F.mixed weaklyPrefers profile)
    (hfull : ∀ i action, action ∈ (profile i).support) :
    F.IsTremblingHandPerfect weaklyPrefers profile := by
  refine ⟨scaledPerturbation F profile, fun _ => profile, ?_, ?_, ?_⟩
  · intro n
    constructor
    · intro i action
      exact mul_pos (vanishingWeight_pos n)
        (ENNReal.toReal_pos_iff.mpr ⟨
          (PMF.apply_pos_iff (profile i) action).2 (hfull i action),
          lt_top_iff_ne_top.mpr (PMF.apply_ne_top (profile i) action)⟩)
    · apply hnash.isPerturbedEq
      intro i action
      exact mul_le_of_le_one_left ENNReal.toReal_nonneg
        (vanishingWeight_le_one n)
  · intro i action
    simpa [scaledPerturbation] using
      vanishingWeight_tendsto_zero.mul_const ((profile i action).toReal)
  · exact Analysis.mixedProfileConvergesPointwise_const profile

/-- A trembling-hand perfect profile is mixed Nash.  Finite action carriers
let an arbitrary mixed deviation be repaired to satisfy each positive lower
bound; those repairs converge back to the original deviation as the bounds
vanish. Expected-utility continuity then passes the perturbed equilibrium
inequalities to the limit. -/
theorem IsTremblingHandPerfect.isNash
    [∀ i, Fintype (F.sig.Strategy i)]
    {utility : F.sig.Outcome → ι → ℝ}
    {profile : Profile F.sig.mixed}
    (hperfect : F.IsTremblingHandPerfect (euPreference utility) profile) :
    IsNash F.mixed (euPreference utility) profile := by
  rw [isNash_iff]
  intro who replacement
  rw [euPreference_apply]
  rcases hperfect with ⟨lower, approximating, hequilibria, hzero, hconverges⟩
  have hprobSum (n : ℕ) :
      ∑ action, (approximating n who action).toReal = 1 := by
    simpa only [tsum_fintype] using pmf_weight_tsum_one (approximating n who)
  have hreplacementSum : ∑ action, (replacement action).toReal = 1 := by
    simpa only [tsum_fintype] using pmf_weight_tsum_one replacement
  have hlowerNonneg (n : ℕ) (action : F.sig.Strategy who) :
      0 ≤ lower n who action :=
    (hequilibria n).1 who action |>.le
  have hmassLe (n : ℕ) :
      perturbationMass F (lower n) who ≤ 1 := by
    calc
      ∑ action, lower n who action ≤
          ∑ action, (approximating n who action).toReal := by
        apply Finset.sum_le_sum
        intro action _
        exact (hequilibria n).2.1 who action
      _ = 1 := hprobSum n
  let weight : ℕ → F.sig.Strategy who → ℝ := fun n action =>
    lower n who action +
      (1 - perturbationMass F (lower n) who) * (replacement action).toReal
  have hweightNonneg (n : ℕ) (action : F.sig.Strategy who) :
      0 ≤ weight n action := by
    apply add_nonneg (hlowerNonneg n action)
    exact mul_nonneg (sub_nonneg.mpr (hmassLe n))
      ENNReal.toReal_nonneg
  have hweightSum (n : ℕ) : ∑ action, weight n action = 1 := by
    simp only [weight, Finset.sum_add_distrib, ← Finset.mul_sum,
      perturbationMass, hreplacementSum]
    ring
  let repaired : ℕ → PMF (F.sig.Strategy who) := fun n =>
    PMF.ofFintype (fun action => ENNReal.ofReal (weight n action)) (by
      rw [← ENNReal.ofReal_sum_of_nonneg
        (fun action _ => hweightNonneg n action), hweightSum]
      norm_num)
  have hrepairedRespects (n : ℕ) :
      F.StrategyRespectsPerturbation (lower n who) (repaired n) := by
    intro action
    rw [show (repaired n action).toReal = weight n action by
      simp [repaired, PMF.ofFintype_apply, ENNReal.toReal_ofReal,
        hweightNonneg]]
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr (hmassLe n))
        ENNReal.toReal_nonneg)
  have hmassZero :
      Tendsto (fun n => perturbationMass F (lower n) who) atTop (nhds 0) := by
    unfold perturbationMass
    simpa using tendsto_finsetSum Finset.univ fun action _ => hzero who action
  have hrepairedConverges :
      PMFConvergesPointwise repaired replacement := by
    intro action
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hlimit := (hzero who action).add
      ((hone.sub hmassZero).mul_const ((replacement action).toReal))
    have hweight : Tendsto (fun n => weight n action) atTop
        (nhds ((replacement action).toReal)) := by
      simpa [weight] using hlimit
    have htarget : ENNReal.ofReal ((replacement action).toReal) =
        replacement action :=
      ENNReal.ofReal_toReal (PMF.apply_ne_top replacement action)
    rw [← htarget]
    simpa only [repaired, PMF.ofFintype_apply] using
      ENNReal.tendsto_ofReal hweight
  have hupdatedConverges (other : ι) :
      PMFConvergesPointwise
        (fun n => Profile.update (approximating n) who (repaired n) other)
        (Profile.update profile who replacement other) := by
    by_cases hother : other = who
    · subst hother
      simpa only [Profile.update_same] using hrepairedConverges
    · simpa only [Profile.update_of_ne _ _ hother] using hconverges other
  have hintegrable : F.HasIntegrableUtility utility := by
    intro player pureProfile
    have hprofileSupport :
        pureProfile ∈ (independentProduct (approximating 0)).support := by
      apply (independentProduct_support_iff (approximating 0) pureProfile).2
      intro other
      exact GameForm.Perturbation.Positive.fullSupport_of_respects F
        (hequilibria 0).1 (hequilibria 0).2.1 other (pureProfile other)
    have hbase : UtilityIntegrable utility player
        (F.mixed.play (approximating 0)) := by
      have hrelation :=
        ((F.isPerturbedEq_iff (euPreference utility) (lower 0)
          (approximating 0)).mp (hequilibria 0).2).2 player
          (approximating 0 player) ((hequilibria 0).2.1 player)
      rw [Profile.update_eq_self] at hrelation
      rcases (euPreference_apply utility player
        (F.mixed.play (approximating 0))
        (F.mixed.play (approximating 0))).mp hrelation with
        ⟨hpreferred, _⟩
      exact hpreferred
    have hconditional := payoffIntegrable_bind_conditional_on_support
      (independentProduct (approximating 0)) F.play
      (fun outcome => utility outcome player)
      (by simpa only [GameForm.mixed_play, UtilityIntegrable] using hbase)
      pureProfile hprofileSupport
    simpa only [GameForm.mixed_play, UtilityIntegrable] using hconditional
  let G : UtilityGame ι := ⟨F, utility⟩
  have hstatusTendsto :
      Tendsto
        (fun n => expectedUtility utility who (F.mixed.play (approximating n))
          (hintegrable.mixed_of_finite who (approximating n)))
        atTop
        (nhds (expectedUtility utility who (F.mixed.play profile)
          (hintegrable.mixed_of_finite who profile))) := by
    simpa only [G] using
      (UtilityGame.expectedUtility_mixed_tendsto (G := G)
        hconverges hintegrable who)
  have hdeviationTendsto :
      Tendsto
        (fun n => expectedUtility utility who
          (F.mixed.play (Profile.update (approximating n) who (repaired n)))
          (hintegrable.mixed_of_finite who
            (Profile.update (approximating n) who (repaired n))))
        atTop
      (nhds (expectedUtility utility who
        (F.mixed.play (Profile.update profile who replacement))
        (hintegrable.mixed_of_finite who
          (Profile.update profile who replacement)))) := by
    simpa only [G] using
      (UtilityGame.expectedUtility_mixed_tendsto (G := G)
        hupdatedConverges hintegrable who)
  refine ⟨hintegrable.mixed_of_finite who profile,
    hintegrable.mixed_of_finite who (Profile.update profile who replacement), ?_⟩
  apply le_of_tendsto_of_tendsto hdeviationTendsto hstatusTendsto
  exact Eventually.of_forall fun n => by
    have hpref :=
      ((F.isPerturbedEq_iff (euPreference utility) (lower n) (approximating n)).mp
        (hequilibria n).2).2 who (repaired n) (hrepairedRespects n)
    rcases (euPreference_apply utility who
      (F.mixed.play (approximating n))
      (F.mixed.play (Profile.update (approximating n) who (repaired n)))).mp
      hpref with ⟨_, _, hle⟩
    exact hle

end GameForm

namespace UtilityGame

/-- Expected-utility specialization of trembling-hand perfection. -/
def IsTremblingHandPerfect (G : UtilityGame ι)
    (profile : Profile G.form.sig.mixed) : Prop :=
  G.form.IsTremblingHandPerfect (euPreference G.utility) profile

theorem isTremblingHandPerfect_iff (G : UtilityGame ι)
    (profile : Profile G.form.sig.mixed) :
    G.IsTremblingHandPerfect profile ↔
      G.form.IsTremblingHandPerfect (euPreference G.utility) profile :=
  Iff.rfl

/-- Expected-utility trembling-hand perfection refines ordinary mixed Nash. -/
theorem IsTremblingHandPerfect.isNash
    (G : UtilityGame ι)
    [∀ i, Fintype (G.form.sig.Strategy i)]
    {profile : Profile G.form.sig.mixed}
    (hperfect : G.IsTremblingHandPerfect profile) :
    IsNash G.form.mixed (euPreference G.utility) profile :=
  GameForm.IsTremblingHandPerfect.isNash G.form hperfect

end UtilityGame

end GameTheory
