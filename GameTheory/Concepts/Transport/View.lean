/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.GameForm

/-!
# View families and observed outcome laws

A **view family** records, for each deviating unit `u : U`, a deterministic
observation `observe u : F.Outcome → Ω u` of the game's outcome. It is the datum
that says *what each unit sees* of the realized play. Pushing a profile
distribution through the observation gives the unit's **observed correlated law**
`claw u μ : PMF (Ω u)`, the finest description of what unit `u` can distinguish
about the outcome under `μ`.

The carrier family `Ω : U → Type` is a parameter shared between the two sides of
a transport; per-side carriers equated only propositionally would force casts
through `PMF`.

Degenerate corners:

* the **global view** `ViewFamily.const obs`, one carrier for every unit — the
  view under which observation does not depend on the deviating unit;
* the **utility-law view**, `Ω u := ℝ` observed through a game's utility, which
  lives at the `KernelGame` level because a `GameForm` carries no utility.

Coarsening a view by a deterministic map `g : ∀ u, Ω u → Ω' u`
(`ViewFamily.garble`) is the deterministic-garbling fragment of the Blackwell
informativeness order on observations: `garble` produces a view that sees no more
than the original, and `claw` commutes with the coarsening. The stochastic
informativeness order and Blackwell's theorem proper are not developed here.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type}

/-- A **view family** over a type `U` of deviating units: for each unit `u`, a
deterministic observation of the game's outcome into the carrier `Ω u`. -/
structure ViewFamily (F : GameForm ι) (U : Type) (Ω : U → Type) where
  /-- What unit `u` observes of a realized outcome. -/
  observe : ∀ u, F.Outcome → Ω u

namespace ViewFamily

variable {F : GameForm ι} {U : Type} {Ω : U → Type}

/-- The **observed correlated law** at unit `u`: the distribution of what `u`
observes when the profile is drawn from `μ`. -/
noncomputable def claw (V : ViewFamily F U Ω) (u : U) (μ : PMF F.Profile) : PMF (Ω u) :=
  PMF.map (V.observe u) (F.correlatedOutcome μ)

/-- The observed law at a pure profile: what unit `u` observes when the profile
is `σ`. -/
noncomputable def plaw (V : ViewFamily F U Ω) (u : U) (σ : F.Profile) : PMF (Ω u) :=
  PMF.map (V.observe u) (F.outcomeKernel σ)

@[simp] theorem plaw_eq_claw_pure (V : ViewFamily F U Ω) (u : U) (σ : F.Profile) :
    V.plaw u σ = V.claw u (PMF.pure σ) := by
  simp [plaw, claw]

/-- The **global view**: a single carrier `Ω` observed identically by every
deviating unit. -/
def const {Ω : Type} (observe : F.Outcome → Ω) : ViewFamily F U (fun _ => Ω) where
  observe := fun _ => observe

@[simp] theorem const_observe {Ω : Type} (observe : F.Outcome → Ω) (u : U) :
    (const (F := F) (U := U) observe).observe u = observe := rfl

/-- **Deterministic garbling** of a view along `g : ∀ u, Ω u → Ω' u`: the coarser
view that first observes and then applies `g`. This is the deterministic fragment
of the Blackwell informativeness order — the garbled view sees no more than the
original. -/
def garble {Ω' : U → Type} (V : ViewFamily F U Ω) (g : ∀ u, Ω u → Ω' u) :
    ViewFamily F U Ω' where
  observe := fun u => g u ∘ V.observe u

/-- Garbling commutes with the observed correlated law. -/
@[simp] theorem claw_garble {Ω' : U → Type} (V : ViewFamily F U Ω)
    (g : ∀ u, Ω u → Ω' u) (u : U) (μ : PMF F.Profile) :
    (V.garble g).claw u μ = PMF.map (g u) (V.claw u μ) := by
  simp [claw, garble, PMF.map_comp]

/-- Pointwise observed-law equality lifts through a common recommendation
distribution mapped independently on each side. -/
theorem claw_map_eq_map_of_plaw {G H : GameForm ι} {U : Type} {Ω : U → Type}
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (u : U)
    {α : Type} (μ : PMF α) (source : α → G.Profile) (target : α → H.Profile)
    (law_eq : ∀ a, VG.plaw u (source a) = VH.plaw u (target a)) :
    VG.claw u (PMF.map source μ) = VH.claw u (PMF.map target μ) := by
  simpa [claw, plaw, GameForm.correlatedOutcome, Math.Probability.Kernel.pushforward,
    PMF.map_bind, PMF.bind_map] using
    Math.ProbabilityMassFunction.bind_congr_on_support μ
      (fun a => PMF.map (VG.observe u) (G.outcomeKernel (source a)))
      (fun a => PMF.map (VH.observe u) (H.outcomeKernel (target a)))
      (fun a _ => law_eq a)

/-- A pointwise profile realization induces the same observed correlated law at
each unit. -/
theorem claw_map_of_plaw {G H : GameForm ι} {U : Type} {Ω : U → Type}
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (u : U)
    (realize : G.Profile → H.Profile)
    (law_eq : ∀ σ, VG.plaw u σ = VH.plaw u (realize σ))
    (μ : PMF G.Profile) :
    VG.claw u μ = VH.claw u (PMF.map realize μ) := by
  have h := claw_map_eq_map_of_plaw VG VH u μ id realize (fun σ => law_eq σ)
  rwa [PMF.map_id] at h

/-- Pointwise observed-law equality after profile transforms lifts to observed
correlated laws through a common recommendation distribution. -/
theorem claw_bind_profile_map_of_plaw {G H : GameForm ι} {U : Type} {Ω : U → Type}
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) (u : U)
    (realize : G.Profile → H.Profile)
    (source : G.Profile → G.Profile) (target : H.Profile → H.Profile)
    (law_eq : ∀ σ, VG.plaw u (source σ) = VH.plaw u (target (realize σ)))
    (μ : PMF G.Profile) :
    VG.claw u (μ.bind (fun σ => PMF.pure (source σ))) =
      VH.claw u ((PMF.map realize μ).bind (fun τ => PMF.pure (target τ))) := by
  have hsource : μ.bind (fun σ => PMF.pure (source σ)) = PMF.map source μ :=
    PMF.bind_pure_comp source μ
  have htarget :
      ((PMF.map realize μ).bind fun τ => PMF.pure (target τ)) =
        PMF.map (target ∘ realize) μ :=
    calc
      ((PMF.map realize μ).bind fun τ => PMF.pure (target τ))
          = PMF.map target (PMF.map realize μ) :=
            PMF.bind_pure_comp target (PMF.map realize μ)
      _ = PMF.map (target ∘ realize) μ := PMF.map_comp realize μ target
  rw [hsource, htarget]
  exact claw_map_eq_map_of_plaw VG VH u μ source (target ∘ realize) law_eq

end ViewFamily

/-- Lift per-unit preferences on observed laws to preferences on a game form's
native outcome laws, by mapping each unit's observation over both sides. -/
def observedPref {F : GameForm ι} {U : Type} {Ω : U → Type}
    (V : ViewFamily F U Ω) (prefΩ : ∀ u, PMF (Ω u) → PMF (Ω u) → Prop) :
    U → PMF F.Outcome → PMF F.Outcome → Prop :=
  fun u d e => prefΩ u (PMF.map (V.observe u) d) (PMF.map (V.observe u) e)

end GameForm

end GameTheory
