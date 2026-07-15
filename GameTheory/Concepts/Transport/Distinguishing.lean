/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.ProbabilityMassFunction.Distinguishing
import GameTheory.Concepts.Transport.Approximate

/-!
# Contextual Distinguishing Advantage

An observer represented by a `ViewFamily` first maps a game's correlated outcome
law to the observer's visible law. Its distinguishing advantage between two
profile distributions is the total variation distance between those visible
laws. This keeps contexts at the observation boundary rather than adding an
adversary field to `GameForm` or `KernelGame`.

Finite Boolean and unit-bounded real tests characterize this advantage exactly.
Deterministic garbling cannot increase it.

## Main definitions

* `ViewFamily.distinguishingAdvantageAgainst` — observer-relative total
  variation across two game forms
* `ViewFamily.distinguishingAdvantage` — same-game specialization
* `ViewFamily.testAdvantageAgainst` — advantage of one real-valued observer test
* `ViewFamily.booleanAdvantageAgainst` — advantage of one Boolean observer test

## Main results

* `ViewFamily.distinguishingAdvantage_garble_le` — data processing
* `ViewFamily.exists_booleanAdvantage_eq_distinguishingAdvantage` — Boolean
  tests attain contextual advantage
* `ViewFamily.distinguishingAdvantage_le_iff_booleanAdvantage_le` — Boolean-test
  characterization
-/

namespace GameTheory

open Math.Probability

namespace GameForm
namespace ViewFamily

variable {ι : Type} {F G H : GameForm ι} {U : Type} {Ω : U → Type}
variable [∀ u, Fintype (Ω u)]

/-- Total variation between the laws visible through two possibly different
game-form views. -/
noncomputable def distinguishingAdvantageAgainst
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (u : U)
    (μG : PMF G.Profile) (μH : PMF H.Profile) : ℝ :=
  pmfTV (VG.claw u μG) (VH.claw u μH)

/-- Total variation between the laws visible to unit `u` under two correlated
profile distributions. -/
noncomputable def distinguishingAdvantage (V : ViewFamily F U Ω) (u : U)
    (μ ν : PMF F.Profile) : ℝ :=
  V.distinguishingAdvantageAgainst V u μ ν

/-- Advantage achieved by one real-valued test shared by two possibly different
game-form views. -/
noncomputable def testAdvantageAgainst
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (u : U)
    (μG : PMF G.Profile) (μH : PMF H.Profile) (test : Ω u → ℝ) : ℝ :=
  pmfTestAdvantage (VG.claw u μG) (VH.claw u μH) test

/-- Advantage achieved by one real-valued test of unit `u`'s observation. -/
noncomputable def testAdvantage (V : ViewFamily F U Ω) (u : U)
    (μ ν : PMF F.Profile) (test : Ω u → ℝ) : ℝ :=
  V.testAdvantageAgainst V u μ ν test

/-- Boolean acceptance-probability gap shared by two possibly different
game-form views. -/
noncomputable def booleanAdvantageAgainst
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (u : U)
    (μG : PMF G.Profile) (μH : PMF H.Profile) (test : Ω u → Bool) : ℝ :=
  pmfBooleanAdvantage (VG.claw u μG) (VH.claw u μH) test

/-- Acceptance-probability gap achieved by one Boolean test of unit `u`'s
observation. -/
noncomputable def booleanAdvantage (V : ViewFamily F U Ω) (u : U)
    (μ ν : PMF F.Profile) (test : Ω u → Bool) : ℝ :=
  V.booleanAdvantageAgainst V u μ ν test

theorem booleanAdvantageAgainst_le_distinguishingAdvantageAgainst
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (u : U)
    (μG : PMF G.Profile) (μH : PMF H.Profile) (test : Ω u → Bool) :
    VG.booleanAdvantageAgainst VH u μG μH test ≤
      VG.distinguishingAdvantageAgainst VH u μG μH :=
  pmfBooleanAdvantage_le_pmfTV _ _ test

theorem exists_booleanAdvantageAgainst_eq_distinguishingAdvantageAgainst
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (u : U)
    (μG : PMF G.Profile) (μH : PMF H.Profile) :
    ∃ test : Ω u → Bool,
      VG.booleanAdvantageAgainst VH u μG μH test =
        VG.distinguishingAdvantageAgainst VH u μG μH :=
  exists_booleanTest_advantage_eq_pmfTV _ _

theorem distinguishingAdvantageAgainst_le_iff_booleanAdvantageAgainst_le
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (u : U)
    (μG : PMF G.Profile) (μH : PMF H.Profile) (ε : ℝ) :
    VG.distinguishingAdvantageAgainst VH u μG μH ≤ ε ↔
      ∀ test : Ω u → Bool,
        VG.booleanAdvantageAgainst VH u μG μH test ≤ ε :=
  pmfTV_le_iff_booleanTest_advantage_le _ _ ε

theorem testAdvantageAgainst_le_distinguishingAdvantageAgainst
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (u : U)
    (μG : PMF G.Profile) (μH : PMF H.Profile)
    (test : Ω u → ℝ) (htest : IsUnitBoundedTest test) :
    VG.testAdvantageAgainst VH u μG μH test ≤
      VG.distinguishingAdvantageAgainst VH u μG μH :=
  pmfTestAdvantage_le_pmfTV _ _ test htest

theorem exists_testAdvantageAgainst_eq_distinguishingAdvantageAgainst
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (u : U)
    (μG : PMF G.Profile) (μH : PMF H.Profile) :
    ∃ test : Ω u → ℝ,
      IsUnitBoundedTest test ∧
        VG.testAdvantageAgainst VH u μG μH test =
          VG.distinguishingAdvantageAgainst VH u μG μH :=
  exists_unitBoundedTest_advantage_eq_pmfTV _ _

theorem distinguishingAdvantageAgainst_le_iff_testAdvantageAgainst_le
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (u : U)
    (μG : PMF G.Profile) (μH : PMF H.Profile) (ε : ℝ) :
    VG.distinguishingAdvantageAgainst VH u μG μH ≤ ε ↔
      ∀ test : Ω u → ℝ, IsUnitBoundedTest test →
        VG.testAdvantageAgainst VH u μG μH test ≤ ε :=
  pmfTV_le_iff_unitBoundedTest_advantage_le _ _ ε

theorem distinguishingAdvantage_nonneg (V : ViewFamily F U Ω) (u : U)
    (μ ν : PMF F.Profile) :
    0 ≤ V.distinguishingAdvantage u μ ν :=
  pmfTV_nonneg _ _

@[simp] theorem distinguishingAdvantage_self (V : ViewFamily F U Ω) (u : U)
    (μ : PMF F.Profile) :
    V.distinguishingAdvantage u μ μ = 0 :=
  pmfTV_self _

theorem distinguishingAdvantage_symm (V : ViewFamily F U Ω) (u : U)
    (μ ν : PMF F.Profile) :
    V.distinguishingAdvantage u μ ν = V.distinguishingAdvantage u ν μ :=
  pmfTV_symm _ _

theorem distinguishingAdvantage_triangle (V : ViewFamily F U Ω) (u : U)
    (μ ν ρ : PMF F.Profile) :
    V.distinguishingAdvantage u μ ρ ≤
      V.distinguishingAdvantage u μ ν + V.distinguishingAdvantage u ν ρ :=
  pmfTV_triangle _ _ _

theorem testAdvantage_le_distinguishingAdvantage
    (V : ViewFamily F U Ω) (u : U) (μ ν : PMF F.Profile)
    (test : Ω u → ℝ) (htest : IsUnitBoundedTest test) :
    V.testAdvantage u μ ν test ≤ V.distinguishingAdvantage u μ ν :=
  testAdvantageAgainst_le_distinguishingAdvantageAgainst V V u μ ν test htest

theorem exists_testAdvantage_eq_distinguishingAdvantage
    (V : ViewFamily F U Ω) (u : U) (μ ν : PMF F.Profile) :
    ∃ test : Ω u → ℝ,
      IsUnitBoundedTest test ∧
        V.testAdvantage u μ ν test = V.distinguishingAdvantage u μ ν :=
  exists_testAdvantageAgainst_eq_distinguishingAdvantageAgainst V V u μ ν

theorem distinguishingAdvantage_le_iff_testAdvantage_le
    (V : ViewFamily F U Ω) (u : U) (μ ν : PMF F.Profile) (ε : ℝ) :
    V.distinguishingAdvantage u μ ν ≤ ε ↔
      ∀ test : Ω u → ℝ, IsUnitBoundedTest test →
        V.testAdvantage u μ ν test ≤ ε :=
  distinguishingAdvantageAgainst_le_iff_testAdvantageAgainst_le V V u μ ν ε

theorem booleanAdvantage_le_distinguishingAdvantage
    (V : ViewFamily F U Ω) (u : U) (μ ν : PMF F.Profile)
    (test : Ω u → Bool) :
    V.booleanAdvantage u μ ν test ≤ V.distinguishingAdvantage u μ ν :=
  booleanAdvantageAgainst_le_distinguishingAdvantageAgainst V V u μ ν test

theorem exists_booleanAdvantage_eq_distinguishingAdvantage
    (V : ViewFamily F U Ω) (u : U) (μ ν : PMF F.Profile) :
    ∃ test : Ω u → Bool,
      V.booleanAdvantage u μ ν test = V.distinguishingAdvantage u μ ν :=
  exists_booleanAdvantageAgainst_eq_distinguishingAdvantageAgainst V V u μ ν

theorem distinguishingAdvantage_le_iff_booleanAdvantage_le
    (V : ViewFamily F U Ω) (u : U) (μ ν : PMF F.Profile) (ε : ℝ) :
    V.distinguishingAdvantage u μ ν ≤ ε ↔
      ∀ test : Ω u → Bool, V.booleanAdvantage u μ ν test ≤ ε :=
  distinguishingAdvantageAgainst_le_iff_booleanAdvantageAgainst_le V V u μ ν ε

theorem distinguishingAdvantageAgainst_garble_le {Ω' : U → Type}
    [∀ u, Fintype (Ω' u)]
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω)
    (g : ∀ u, Ω u → Ω' u) (u : U)
    (μG : PMF G.Profile) (μH : PMF H.Profile) :
    (VG.garble g).distinguishingAdvantageAgainst (VH.garble g) u μG μH ≤
      VG.distinguishingAdvantageAgainst VH u μG μH := by
  unfold distinguishingAdvantageAgainst
  rw [claw_garble, claw_garble]
  exact pmfTV_map_le (g u) (VG.claw u μG) (VH.claw u μH)

theorem distinguishingAdvantage_garble_le {Ω' : U → Type}
    [∀ u, Fintype (Ω' u)] (V : ViewFamily F U Ω)
    (g : ∀ u, Ω u → Ω' u) (u : U) (μ ν : PMF F.Profile) :
    (V.garble g).distinguishingAdvantage u μ ν ≤
      V.distinguishingAdvantage u μ ν :=
  distinguishingAdvantageAgainst_garble_le V V g u μ ν

omit [∀ u, Fintype (Ω u)] in
theorem testAdvantage_garble {Ω' : U → Type}
    (V : ViewFamily F U Ω) (g : ∀ u, Ω u → Ω' u)
    (u : U) (μ ν : PMF F.Profile) (test : Ω' u → ℝ) :
    (V.garble g).testAdvantage u μ ν test =
      V.testAdvantage u μ ν (test ∘ g u) := by
  unfold testAdvantage testAdvantageAgainst pmfTestAdvantage
  rw [claw_garble, claw_garble, expect_map, expect_map]
  rfl

omit [∀ u, Fintype (Ω u)] in
theorem booleanAdvantage_garble {Ω' : U → Type}
    (V : ViewFamily F U Ω) (g : ∀ u, Ω u → Ω' u)
    (u : U) (μ ν : PMF F.Profile) (test : Ω' u → Bool) :
    (V.garble g).booleanAdvantage u μ ν test =
      V.booleanAdvantage u μ ν (test ∘ g u) := by
  unfold booleanAdvantage booleanAdvantageAgainst pmfBooleanAdvantage
  rw [claw_garble, claw_garble, PMF.map_comp, PMF.map_comp]

end ViewFamily

namespace Realization

variable {G H : GameForm ι} {U : Type} {Ω : U → Type}
variable [∀ u, Fintype (Ω u)]
variable {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}

/-- Exact realization means zero contextual distinguishing advantage. -/
theorem distinguishingAdvantageAgainst_eq_zero
    (R : Realization G H VG VH)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : R.rel μG μH) (u : U) :
    VG.distinguishingAdvantageAgainst VH u μG μH = 0 := by
  unfold ViewFamily.distinguishingAdvantageAgainst
  rw [R.law_eq hrel u]
  exact pmfTV_self _

end Realization

namespace ApproxRealization

variable {G H : GameForm ι} {U : Type} {Ω : U → Type}
variable [∀ u, Fintype (Ω u)]
variable {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}

/-- The error field of an approximate realization is exactly a contextual
distinguishing-advantage bound. -/
theorem distinguishingAdvantageAgainst_le {ε : ℝ}
    (R : ApproxRealization G H VG VH ε)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : R.rel μG μH) (u : U) :
    VG.distinguishingAdvantageAgainst VH u μG μH ≤ ε :=
  R.law_le hrel u

/-- Every Boolean observer context has advantage bounded by an approximate
realization's error. -/
theorem booleanAdvantageAgainst_le {ε : ℝ}
    (R : ApproxRealization G H VG VH ε)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : R.rel μG μH)
    (u : U) (test : Ω u → Bool) :
    VG.booleanAdvantageAgainst VH u μG μH test ≤ ε :=
  le_trans
    (ViewFamily.booleanAdvantageAgainst_le_distinguishingAdvantageAgainst
      VG VH u μG μH test)
    (R.distinguishingAdvantageAgainst_le hrel u)

/-- Every unit-bounded real observer context has advantage bounded by an
approximate realization's error. -/
theorem testAdvantageAgainst_le {ε : ℝ}
    (R : ApproxRealization G H VG VH ε)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : R.rel μG μH)
    (u : U) (test : Ω u → ℝ) (htest : IsUnitBoundedTest test) :
    VG.testAdvantageAgainst VH u μG μH test ≤ ε :=
  le_trans
    (ViewFamily.testAdvantageAgainst_le_distinguishingAdvantageAgainst
      VG VH u μG μH test htest)
    (R.distinguishingAdvantageAgainst_le hrel u)

end ApproxRealization

end GameForm
end GameTheory
