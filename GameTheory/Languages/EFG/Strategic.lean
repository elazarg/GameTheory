/-
# EFG strategic-form transfer

An EFG's pure strategy is an information-local contingent plan, already owned
by its `InformationModel`. The strategic form therefore applies the accepted
Protocol compiler directly; there is no EFG-specific evaluator and no
intermediate normal-form game.

The two central equivalences expose ordinary pure and mixed `IsNash` in the
native `run` and `runMixed` vocabulary. They define no language-specific
equilibrium predicate.
-/

import GameTheory.Languages.EFG
import GameTheory.Protocol.Strategic
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory.Languages.EFG

open GameTheory.Protocol Probability

universe uι us ua up uq uk

namespace Game

variable {ι : Type uι} (G : Game.{uι, us, ua, up, uq, uk} ι)

/-- A pure EFG contingent plan is exactly an information-local policy. -/
abbrev ContingentPlan (who : ι) :=
  G.information.Policy who

/-- Finite local information and menu carriers make the extracted contingent
plan carrier finite. The capabilities are supplied here rather than stored in
the EFG. -/
@[reducible]
noncomputable def contingentPlanFintype (who : ι)
    [Fintype (G.information.InfoState who)]
    [DecidableEq (G.information.InfoState who)]
    [∀ info, Fintype (G.information.Choice who info)]
    [∀ info, DecidableEq (G.information.Choice who info)] :
    Fintype (G.ContingentPlan who) := by
  show
    Fintype
      ((info : G.information.InfoState who) →
        G.information.Choice who info)
  infer_instance

/-- The EFG strategic signature retains information-local contingent plans and
full realized histories. -/
abbrev strategicSignature : GameSignature ι :=
  G.information.strategicSignature

/-- Compile an EFG to the accepted finite-horizon strategic `GameForm`. -/
@[reducible]
def toGameForm (horizon : ℕ) : GameForm ι :=
  G.information.toGameForm horizon

/-- The EFG compiler reuses the information model's named evaluation law. -/
@[simp]
theorem toGameForm_play (horizon : ℕ)
    (profile : Profile G.strategicSignature) :
    (G.toGameForm horizon).play profile =
      G.information.run profile horizon :=
  InformationModel.toGameForm_play G.information horizon profile

variable [DecidableEq ι]

/-- Ordinary Nash of the extracted EFG strategic form is
exactly the native contingent-plan deviation inequality. -/
theorem isNash_toGameForm_iff
    (utility : G.History → ι → ℝ)
    (profile : Profile G.strategicSignature) (horizon : ℕ) :
    IsNash (G.toGameForm horizon) (euPreference utility) profile ↔
      ∀ who replacement,
        expectedUtility utility who
            (G.information.run
              (Profile.update profile who replacement) horizon) ≤
          expectedUtility utility who
            (G.information.run profile horizon) := by
  rw [isNash_iff]
  rfl

variable [Fintype ι]

omit [DecidableEq ι] in
/-- Static mixing of extracted contingent plans is the native mixed-policy
runner. -/
@[simp]
theorem toGameForm_mixed_play
    (mixed : Profile G.strategicSignature.mixed) (horizon : ℕ) :
    ((G.toGameForm horizon).mixed).play mixed =
      G.information.runMixed mixed horizon :=
  InformationModel.toGameForm_mixed_play G.information horizon mixed

/-- Mixed Nash of the extracted EFG strategic form is
exactly the native mixed-policy deviation inequality. -/
theorem isNash_mixed_toGameForm_iff
    (utility : G.History → ι → ℝ)
    (mixed : Profile G.strategicSignature.mixed) (horizon : ℕ) :
    IsNash (G.toGameForm horizon).mixed (euPreference utility) mixed ↔
      ∀ who replacement,
        expectedUtility utility who
            (G.information.runMixed
              (Profile.update mixed who replacement) horizon) ≤
          expectedUtility utility who
            (G.information.runMixed mixed horizon) := by
  rw [isNash_iff]
  rfl

end Game

end GameTheory.Languages.EFG
