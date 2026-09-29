/-
# Dominance and Nash as preservation targets

A dominant profile compares each player's prescribed strategy with every
alternative at every opponent profile. Nash makes the same comparisons at the
prescribed opponents only, so dominance refines Nash. The extra comparisons sit
at opponent behaviour the deviator cannot condition on: a Nash deviation never
reaches another opponent profile, so no localization links the two families
and preserving Nash says nothing about dominance at other opponent profiles.
-/

import GameTheory.Analysis.IncentiveHierarchy
import GameTheory.Core.Response

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo uv

variable {ι : Type uι} [DecidableEq ι] {Observation : Type uv}

namespace GameForm

variable (F : GameForm.{uι, us, uo} ι)

/-- The comparison behind dominance of a prescribed strategy over one
alternative at one opponent profile. -/
def dominanceComparison (profile : Profile F.sig) (observe : F.sig.Outcome → Observation)
    (who : ι) (deviation : Profile F.sig × F.sig.Strategy who) :
    IncentiveComparison Observation where
  prescribed := (F.play (Profile.update deviation.1 who (profile who))).map observe
  alternative := (F.play (Profile.update deviation.1 who deviation.2)).map observe

/-- A dominant profile of observed payoffs is its comparison family. -/
theorem isDominantProfile_iff_holds (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) (utility : Observation → ι → ℝ) :
    IsDominantProfile F (euPreference fun outcome who => utility (observe outcome) who)
        profile ↔
      ∀ who deviation,
        (F.dominanceComparison profile observe who deviation).Holds (utility · who) := by
  simp only [IsDominantProfile, IsDominant, VeryWeaklyDominates, dominanceComparison,
    IncentiveComparison.holds_map_iff, Prod.forall]
  exact ⟨fun dominant who opponents alternative => dominant who alternative opponents,
    fun holds who alternative opponents => holds who opponents alternative⟩

/-- A Nash comparison is the dominance comparison at the prescribed
opponents. -/
theorem equilibriumComparison_eq_dominanceComparison (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) (who : ι) (alternative : F.sig.Strategy who) :
    equilibriumComparison F (PMF.pure profile) (DeviationScheme.unilateralConstant F.sig)
        observe who alternative =
      F.dominanceComparison profile observe who (profile, alternative) := by
  simp [equilibriumComparison, dominanceComparison, GameForm.outcomeLaw, PMF.pure_map]

/-- Dominance refines Nash for every utility. -/
theorem implies_equilibriumComparison (profile : Profile F.sig)
    (observe : F.sig.Outcome → Observation) :
    IncentiveComparison.Implies (F.dominanceComparison profile observe)
      (equilibriumComparison F (PMF.pure profile) (DeviationScheme.unilateralConstant F.sig)
        observe) :=
  fun _ holds who alternative =>
    (IncentiveComparison.holds_iff_of_eq
      (F.equilibriumComparison_eq_dominanceComparison profile observe who alternative) _).2
        (holds who _)

end GameForm

end GameTheory
