/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Public.TerminalChildAdaptivePotential

/-!
# Finite families of child adaptive potential systems

Childwise adaptive-potential certificates contain existentially quantified
profiles and witness data.  For a finite child type, this file chooses those
witnesses and records one common horizon threshold obtained from their finite
maximum.  No child profiles, potentials, or charge sequences are combined or
modified.

The terminal-base specialization merely assigns a child through a public
observation map and applies canonical off-path behavior dispatch.  It does
not construct the preceding selector, preserve a parent target, or prove a
strategic splice.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι Child : Type} {G : StochasticGame ι}

/-- Explicit adaptive-potential witnesses for a finite family of children,
together with one horizon threshold dominating every child threshold. -/
structure FiniteChildAdaptivePotentialFamily
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [Fintype Child]
    (entry : Child → G.State) (target : Child → Payoff ι)
    (error : ℝ) where
  profile : Child → G.BehaviorProfile
  system : ∀ child,
    G.AdaptivePotentialSystemAt
      (profile child) (entry child) (target child) error
  commonHorizon : ℕ
  commonHorizon_ge_two : 2 ≤ commonHorizon
  horizon_le_common : ∀ child,
    (system child).horizon ≤ commonHorizon

namespace FiniteChildAdaptivePotentialFamily

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)] [Fintype Child]
  {entry : Child → G.State} {target : Child → Payoff ι}
  {error : ℝ}

private theorem horizon_cast_entry
    {profile : G.BehaviorProfile} {leftEntry rightEntry : G.State}
    {childTarget : Payoff ι} (hentry : leftEntry = rightEntry)
    (system :
      G.AdaptivePotentialSystemAt
        profile leftEntry childTarget error) :
    (hentry ▸ system).horizon = system.horizon := by
  subst rightEntry
  rfl

/-- Choose one explicit system for every childwise existential certificate
and synchronize only their horizon thresholds. -/
def ofCertificates
    (certificates : ∀ child,
      G.IsAdaptivePotentialCertificateAt
        (entry child) (target child) error) :
    G.FiniteChildAdaptivePotentialFamily entry target error := by
  classical
  have systems_exist : ∀ child,
      ∃ profile : G.BehaviorProfile,
        Nonempty
          (G.AdaptivePotentialSystemAt
            profile (entry child) (target child) error) := by
    intro child
    exact
      (G.isAdaptivePotentialCertificateAt_iff_exists_system
        (entry child) (target child) error).mp
        (certificates child)
  choose profile systems_nonempty using systems_exist
  let system : ∀ child,
      G.AdaptivePotentialSystemAt
        (profile child) (entry child) (target child) error :=
    fun child => Classical.choice (systems_nonempty child)
  let finiteMaximum : ℕ :=
    Finset.univ.sup fun child => (system child).horizon
  refine {
    profile := profile
    system := system
    commonHorizon := max 2 finiteMaximum
    commonHorizon_ge_two := Nat.le_max_left 2 finiteMaximum
    horizon_le_common := ?_
  }
  intro child
  exact
    (Finset.le_sup (s := Finset.univ)
      (f := fun candidate => (system candidate).horizon)
      (Finset.mem_univ child)).trans
      (Nat.le_max_right 2 finiteMaximum)

/-- The chosen common threshold may replace each child's threshold in any
monotone eventual statement. -/
theorem horizon_le_total
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    (child : Child) {total : ℕ}
    (htotal : family.commonHorizon ≤ total) :
    (family.system child).horizon ≤ total :=
  (family.horizon_le_common child).trans htotal

/-- The raw child profile selected from a terminal public base through a
finite observation map. -/
def observedTerminalProfile
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    {fuel : ℕ} (observe : G.Hist fuel → Child) :
    G.Hist fuel → G.BehaviorProfile :=
  fun base => family.profile (observe base)

/-- Canonically dispatch the observed child system after one terminal base.

The entry-state equality is explicit because observation alone does not show
that the selected child's certificate starts at the terminal state. -/
def canonicalSystemAtTerminalBase
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    {fuel : ℕ} (selection : G.BehaviorProfile)
    (observe : G.Hist fuel → Child) (base : G.Hist fuel)
    (hentry : base.2 = entry (observe base)) :
    G.AdaptivePotentialSystemAt
      (G.canonicalTerminalChildProfile fuel selection
        (family.observedTerminalProfile observe) base)
      base.2 (target (observe base)) error := by
  let rawSystem :
      G.AdaptivePotentialSystemAt
        (family.profile (observe base)) base.2
        (target (observe base)) error :=
    hentry.symm ▸ family.system (observe base)
  exact rawSystem.canonicalTerminalChildProfile
    fuel selection (family.observedTerminalProfile observe) base

/-- The common family horizon also dominates every canonically dispatched
terminal child system. -/
theorem canonicalSystemAtTerminalBase_horizon_le_common
    (family :
      G.FiniteChildAdaptivePotentialFamily entry target error)
    {fuel : ℕ} (selection : G.BehaviorProfile)
    (observe : G.Hist fuel → Child) (base : G.Hist fuel)
    (hentry : base.2 = entry (observe base)) :
    (family.canonicalSystemAtTerminalBase
      selection observe base hentry).horizon ≤
        family.commonHorizon := by
  calc
    (family.canonicalSystemAtTerminalBase
        selection observe base hentry).horizon =
        (hentry.symm ▸ family.system (observe base)).horizon := rfl
    _ = (family.system (observe base)).horizon :=
      horizon_cast_entry hentry.symm (family.system (observe base))
    _ ≤ family.commonHorizon :=
      family.horizon_le_common (observe base)

end FiniteChildAdaptivePotentialFamily

end StochasticGame
end GameTheory
