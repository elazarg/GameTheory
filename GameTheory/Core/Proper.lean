module

/-
# Relative error probabilities in proper equilibrium

An epsilon-proper profile has full support and assigns an inferior pure action
at most epsilon times the probability of a strictly better pure action against
the same opponents. Comparisons use the canonical mixed play law, with actual
pure-action deviation integrability required before comparing real values.
The limiting proper-equilibrium concept belongs to Analysis.

Primary reference: R. B. Myerson, "Refinements of the Nash Equilibrium Concept,"
International Journal of Game Theory 7 (1978), 73–80.
-/

public import GameTheory.Core.Mixed
public import GameTheory.Math.Probability.Support

@[expose] public section

noncomputable section

namespace GameTheory.GameForm

open GameTheory.Math.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (F : GameForm ι)

/-- Full support with relative error bounds for every strictly inferior action.
All real payoff comparisons are guarded by integrability of their actual laws.
The approximating profile need not be a Nash equilibrium. -/
def IsεProper (utility : F.sig.Outcome → ι → ℝ) (epsilon : ℝ)
    (profile : Profile F.sig.mixed) : Prop :=
  0 < epsilon ∧
    (∀ who, FullSupport (profile who)) ∧
    (∀ who (action : F.sig.Strategy who), UtilityIntegrable utility who
      (F.mixed.play (Profile.update profile who (PMF.pure action)))) ∧
    ∀ who (worse better : F.sig.Strategy who),
      expectedUtility utility who
          (F.mixed.play (Profile.update profile who (PMF.pure worse))) <
        expectedUtility utility who
          (F.mixed.play (Profile.update profile who (PMF.pure better))) →
      (profile who worse).toReal ≤ epsilon * (profile who better).toReal

end GameTheory.GameForm
