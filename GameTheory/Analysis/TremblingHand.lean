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

open Filter Probability
open Analysis

universe uι us uo

variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

namespace Analysis

variable {F : GameForm ι}

/-- Pointwise convergence of every player's finite mixed strategy. -/
def MixedProfileConvergesPointwise
    (sequence : ℕ → Profile F.sig.mixed)
    (target : Profile F.sig.mixed) : Prop :=
  ∀ i, FinDistConvergesPointwise (fun n => sequence n i) (target i)

omit [Fintype ι] [DecidableEq ι] in
theorem mixedProfileConvergesPointwise_const
    (profile : Profile F.sig.mixed) :
    MixedProfileConvergesPointwise (fun _ => profile) profile :=
  fun i => finDistConvergesPointwise_const (profile i)

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
  fun i action => vanishingWeight n * (profile i).prob action

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
    (hfull : ∀ i, (profile i).FullSupport) :
    F.IsTremblingHandPerfect weaklyPrefers profile := by
  refine ⟨scaledPerturbation F profile, fun _ => profile, ?_, ?_, ?_⟩
  · intro n
    constructor
    · intro i action
      exact mul_pos (vanishingWeight_pos n)
        (FinDist.prob_pos_iff.mpr (hfull i action))
    · apply hnash.isPerturbedEq
      intro i action
      exact mul_le_of_le_one_left (FinDist.prob_nonneg (profile i) action)
        (vanishingWeight_le_one n)
  · intro i action
    simpa [scaledPerturbation] using
      vanishingWeight_tendsto_zero.mul_const ((profile i).prob action)
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
  have hlowerNonneg (n : ℕ) (action : F.sig.Strategy who) :
      0 ≤ lower n who action :=
    (hequilibria n).1 who action |>.le
  have hmassLe (n : ℕ) :
      perturbationMass F (lower n) who ≤ 1 := by
    calc
      ∑ action, lower n who action ≤
          ∑ action, (approximating n who).prob action := by
        apply Finset.sum_le_sum
        intro action _
        exact (hequilibria n).2.1 who action
      _ = 1 := FinDist.sum_prob (approximating n who)
  let weight : ℕ → F.sig.Strategy who → ℝ := fun n action =>
    lower n who action +
      (1 - perturbationMass F (lower n) who) * replacement.prob action
  have hweightNonneg (n : ℕ) (action : F.sig.Strategy who) :
      0 ≤ weight n action := by
    apply add_nonneg (hlowerNonneg n action)
    exact mul_nonneg (sub_nonneg.mpr (hmassLe n))
      (FinDist.prob_nonneg replacement action)
  have hweightSum (n : ℕ) : ∑ action, weight n action = 1 := by
    simp only [weight, Finset.sum_add_distrib, ← Finset.mul_sum,
      FinDist.sum_prob, perturbationMass]
    ring
  let repaired : ℕ → FinDist (F.sig.Strategy who) := fun n =>
    FinDist.ofWeights (weight n) (hweightNonneg n) (hweightSum n)
  have hrepairedRespects (n : ℕ) :
      F.StrategyRespectsPerturbation (lower n who) (repaired n) := by
    intro action
    rw [show (repaired n).prob action = weight n action by
      exact FinDist.prob_ofWeights ..]
    exact le_add_of_nonneg_right
      (mul_nonneg (sub_nonneg.mpr (hmassLe n))
        (FinDist.prob_nonneg replacement action))
  have hmassZero :
      Tendsto (fun n => perturbationMass F (lower n) who) atTop (nhds 0) := by
    unfold perturbationMass
    simpa using tendsto_finsetSum Finset.univ fun action _ => hzero who action
  have hrepairedConverges :
      Analysis.FinDistConvergesPointwise repaired replacement := by
    intro action
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hlimit := (hzero who action).add
      ((hone.sub hmassZero).mul_const (replacement.prob action))
    simpa [repaired, weight, FinDist.prob_ofWeights] using hlimit
  have hupdatedConverges (other : ι) :
      Analysis.FinDistConvergesPointwise
        (fun n => Profile.update (approximating n) who (repaired n) other)
        (Profile.update profile who replacement other) := by
    by_cases hother : other = who
    · subst hother
      simpa only [Profile.update_same] using hrepairedConverges
    · simpa only [Profile.update_of_ne _ _ hother] using hconverges other
  let G : UtilityGame ι := ⟨F, utility⟩
  have hstatusTendsto :
      Tendsto
        (fun n => expectedUtility utility who (F.mixed.play (approximating n)))
        atTop
        (nhds (expectedUtility utility who (F.mixed.play profile))) := by
    simpa only [G] using
      (UtilityGame.expectedUtility_mixed_tendsto (G := G) hconverges who)
  have hdeviationTendsto :
      Tendsto
        (fun n => expectedUtility utility who
          (F.mixed.play (Profile.update (approximating n) who (repaired n))))
        atTop
        (nhds (expectedUtility utility who
          (F.mixed.play (Profile.update profile who replacement)))) := by
    simpa only [G] using
      (UtilityGame.expectedUtility_mixed_tendsto (G := G)
        hupdatedConverges who)
  apply le_of_tendsto_of_tendsto hdeviationTendsto hstatusTendsto
  exact Eventually.of_forall fun n => by
    have hpref :=
      ((F.isPerturbedEq_iff (euPreference utility) (lower n) (approximating n)).mp
        (hequilibria n).2).2 who (repaired n) (hrepairedRespects n)
    simpa only [euPreference_apply] using hpref

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
