/-
# Topology-free mixed perturbations

Lower bounds on finite mixed strategies and equilibrium under the resulting
restricted unilateral deviations are algebraic data.  They live in Core and
reuse the sole `IsEquilibrium` predicate through a constrained deviation
scheme.  Only limits of perturbations belong in Analysis.
-/

import GameTheory.Core.Mixed

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι}

namespace GameForm

variable (F : GameForm ι)

/-- A player- and strategy-specific real lower bound on mixed-strategy mass.
Feasibility is deliberately not stored in the raw data. -/
abbrev Perturbation : Type _ :=
  (i : ι) → F.sig.Strategy i → ℝ

/-- One mixed strategy respects its coordinatewise lower bounds. -/
def StrategyRespectsPerturbation {i : ι}
    (lower : F.sig.Strategy i → ℝ)
    (strategy : FinDist (F.sig.Strategy i)) : Prop :=
  ∀ action, lower action ≤ strategy.prob action

/-- Every coordinate of a mixed profile respects the supplied perturbation. -/
def RespectsPerturbation (lower : F.Perturbation)
    (profile : Profile F.sig.mixed) : Prop :=
  ∀ i, F.StrategyRespectsPerturbation (lower i) (profile i)

/-- Strictly positive lower bounds force every respecting mixed strategy to
have full support. -/
def Perturbation.Positive (lower : F.Perturbation) : Prop :=
  ∀ i action, 0 < lower i action

theorem RespectsPerturbation.apply {lower : F.Perturbation}
    {profile : Profile F.sig.mixed} (h : F.RespectsPerturbation lower profile)
    (i : ι) (action : F.sig.Strategy i) :
    lower i action ≤ (profile i).prob action :=
  h i action

theorem Perturbation.Positive.fullSupport_of_respects
    {lower : F.Perturbation} (hpositive : lower.Positive)
    {profile : Profile F.sig.mixed}
    (hrespects : F.RespectsPerturbation lower profile) (i : ι) :
    (profile i).FullSupport := by
  intro action
  rw [← FinDist.prob_pos_iff]
  exact lt_of_lt_of_le (hpositive i action) (hrespects i action)

end GameForm

namespace DeviationScheme

variable [Fintype ι] [DecidableEq ι]

/-- Constant unilateral mixed replacements restricted by one perturbation. -/
def perturbedMixed (F : GameForm ι) (lower : F.Perturbation) :
    DeviationScheme F.sig.mixed ι where
  members who := {who}
  Dev who :=
    { replacement : FinDist (F.sig.Strategy who) //
      F.StrategyRespectsPerturbation (lower who) replacement }
  actLocal who replacement _ :=
    FinDist.pure (Subprofile.single who replacement.1)

/-- Forgetting the lower-bound certificate embeds every perturbed deviation
into the ordinary Nash deviation scheme. -/
def perturbedMixedToUnilateral (F : GameForm ι) (lower : F.Perturbation) :
    Hom id (perturbedMixed F lower) (unilateralConstant F.sig.mixed) where
  map _ replacement := replacement.1
  apply_eq _ _ _ := rfl

end DeviationScheme

namespace GameForm

variable [Fintype ι] [DecidableEq ι] (F : GameForm ι)

/-- Equilibrium of the mixed extension when unilateral replacements must obey
the same lower bounds.  This is a specialization of `IsEquilibrium`, not a
parallel Nash predicate. -/
def IsPerturbedEq (weaklyPrefers : WeakPreference ι F.sig.Outcome)
    (lower : F.Perturbation) (profile : Profile F.sig.mixed) : Prop :=
  F.RespectsPerturbation lower profile ∧
    IsEquilibrium F.mixed weaklyPrefers (FinDist.pure profile)
      (DeviationScheme.perturbedMixed F lower)

theorem isPerturbedEq_iff (weaklyPrefers : WeakPreference ι F.sig.Outcome)
    (lower : F.Perturbation) (profile : Profile F.sig.mixed) :
    F.IsPerturbedEq weaklyPrefers lower profile ↔
      F.RespectsPerturbation lower profile ∧
        ∀ (who : ι) (replacement : FinDist (F.sig.Strategy who)),
          F.StrategyRespectsPerturbation (lower who) replacement →
            weaklyPrefers who (F.mixed.play profile)
              (F.mixed.play (Profile.update profile who replacement)) := by
  simp [IsPerturbedEq, IsEquilibrium, GameForm.outcomeLaw,
    DeviationScheme.perturbedMixed]

/-- An ordinary mixed Nash equilibrium is an equilibrium of every feasible
perturbation that its own profile respects. -/
theorem _root_.GameTheory.IsNash.isPerturbedEq
    {weaklyPrefers : WeakPreference ι F.sig.Outcome}
    {lower : F.Perturbation} {profile : Profile F.sig.mixed}
    (hnash : IsNash F.mixed weaklyPrefers profile)
    (hrespects : F.RespectsPerturbation lower profile) :
    F.IsPerturbedEq weaklyPrefers lower profile := by
  refine ⟨hrespects, ?_⟩
  exact IsEquilibrium.ofHom
    (DeviationScheme.perturbedMixedToUnilateral F lower) hnash

end GameForm

end GameTheory
