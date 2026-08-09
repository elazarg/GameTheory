/-
# Trembling-hand perfection

Core owns finite mixed perturbations and their restricted deviation scheme.
This one-way analytic leaf adds pointwise convergence and the resulting limit
refinement.  It never introduces another mixed extension or Nash predicate.
-/

import GameTheory.Analysis.FiniteLaw
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

end UtilityGame

end GameTheory
