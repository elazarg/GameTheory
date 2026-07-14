/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.Transport.View
import GameTheory.Concepts.Foundations.Transport.Deviation

/-!
# Realizations, simulation, and transports

A **realization** `Realization G H VG VH` is a law-preserving correspondence
between profile distributions of two game forms: a relation `rel` whose related
pairs share the same observed correlated law at every deviating unit. It is the
data a compiler or bridge exposes about how honest play in `G` corresponds to
honest play in `H`.

Backtranslation is a *separate* assertion about that same realization:
`R.Simulates ΔG ΔH` says every target-side deviation in the family `ΔH` is
matched by a source-side deviation in `ΔG` inducing the same observed law. Because
backtranslation is existential there is no canonical produced witness to inspect,
so which family pairs a realization simulates cannot be read off `rel` — it must
be asserted. A single realization typically simulates several family pairs; the
factoring records each such fact independently. A `Transport` bundles a
realization with one chosen simulated pair.

The two componentwise variance lemmas (`Simulates.mono_target`,
`Simulates.mono_source`) and view garbling (`Realization.garble`,
`Simulates.garble`) are the order structure on this data: restricting the target
family, enlarging the source family, or coarsening the view all preserve
simulation, and none of them relates the two families along a common morphism.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type}

/-- A **law-preserving realization**: a relation on profile distributions whose
related pairs induce the same observed correlated law at every deviating unit. -/
structure Realization (G H : GameForm ι) {U : Type} {Ω : U → Type}
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω) where
  /-- Which source distributions the realization matches to which target ones. -/
  rel : PMF G.Profile → PMF H.Profile → Prop
  /-- Related distributions share the observed correlated law at each unit. -/
  law_eq : ∀ {μG : PMF G.Profile} {μH : PMF H.Profile}, rel μG μH →
    ∀ u, VG.claw u μG = VH.claw u μH

/-- `R` **simulates** the family pair `(ΔG, ΔH)`: for every related pair and every
target-side deviation, a source-side deviation induces the same per-unit observed
law. This is the backtranslation obligation, asserted separately from `rel`. -/
def Realization.Simulates {G H : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    (R : Realization G H VG VH)
    (ΔG : DeviationFamily G U) (ΔH : DeviationFamily H U) : Prop :=
  ∀ {μG : PMF G.Profile} {μH : PMF H.Profile}, R.rel μG μH →
    ∀ u (dH : ΔH.Dev u),
      ∃ dG : ΔG.Dev u,
        VG.claw u (ΔG.deviate μG u dG) = VH.claw u (ΔH.deviate μH u dH)

/-- A **transport**: a realization together with one chosen family pair it
simulates. -/
structure Transport (G H : GameForm ι) {U : Type} {Ω : U → Type}
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω)
    (ΔG : DeviationFamily G U) (ΔH : DeviationFamily H U)
    extends Realization G H VG VH where
  /-- The chosen backtranslation obligation this transport discharges. -/
  simulate : toRealization.Simulates ΔG ΔH

namespace Realization

variable {G H : GameForm ι} {U : Type} {Ω : U → Type}

/-- The identity realization on a single game and view family. -/
def refl (V : ViewFamily G U Ω) : Realization G G V V where
  rel := Eq
  law_eq := by intro μG μH h _; rw [h]

/-- Swap the two sides of a realization. -/
def flip {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    (R : Realization G H VG VH) : Realization H G VH VG where
  rel := fun μH μG => R.rel μG μH
  law_eq := by intro μH μG h u; exact (R.law_eq h u).symm

/-- Build a realization from a functional realization map on profile
distributions. -/
def ofFunctionalRealization (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω)
    (realize : PMF G.Profile → PMF H.Profile)
    (law_eq : ∀ u μ, VG.claw u μ = VH.claw u (realize μ)) :
    Realization G H VG VH where
  rel := fun μG μH => μH = realize μG
  law_eq := by intro μG μH h u; subst h; exact law_eq u μG

/-- Coarsen the observed carrier of a realization along a deterministic garbling
`g`. The correspondence is unchanged; only what each unit observes is coarser. -/
def garble {Ω' : U → Type} {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    (R : Realization G H VG VH) (g : ∀ u, Ω u → Ω' u) :
    Realization G H (VG.garble g) (VH.garble g) where
  rel := R.rel
  law_eq := by
    intro μG μH h u
    rw [ViewFamily.claw_garble, ViewFamily.claw_garble, R.law_eq h u]

end Realization

namespace Realization.Simulates

variable {G H : GameForm ι} {U : Type} {Ω : U → Type}
variable {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}

/-- Restrict the target family: if `ΔH'` embeds into `ΔH`, matching every `ΔH`
deviation matches every `ΔH'` deviation. -/
theorem mono_target {R : Realization G H VG VH}
    {ΔG : DeviationFamily G U} {ΔH ΔH' : DeviationFamily H U}
    (φ : DeviationFamily.Hom id ΔH' ΔH)
    (h : R.Simulates ΔG ΔH) : R.Simulates ΔG ΔH' := by
  intro μG μH hrel u dH'
  obtain ⟨dG, hdG⟩ := h hrel u (φ.map u dH')
  refine ⟨dG, ?_⟩
  have hφ : ΔH.deviate μH u (φ.map u dH') = ΔH'.deviate μH u dH' :=
    φ.deviate_eq μH u dH'
  rw [hdG, hφ]

/-- Enlarge the source family: if `ΔG` embeds into `ΔG'`, a match from `ΔG`
supplies a match from `ΔG'`. -/
theorem mono_source {R : Realization G H VG VH}
    {ΔG ΔG' : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (φ : DeviationFamily.Hom id ΔG ΔG')
    (h : R.Simulates ΔG ΔH) : R.Simulates ΔG' ΔH := by
  intro μG μH hrel u dH
  obtain ⟨dG, hdG⟩ := h hrel u dH
  refine ⟨φ.map u dG, ?_⟩
  have hφ : ΔG'.deviate μG u (φ.map u dG) = ΔG.deviate μG u dG :=
    φ.deviate_eq μG u dG
  rw [hφ]
  exact hdG

/-- A simulation fact survives coarsening the observed carrier. -/
theorem garble {Ω' : U → Type} {R : Realization G H VG VH}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (g : ∀ u, Ω u → Ω' u) (h : R.Simulates ΔG ΔH) :
    (R.garble g).Simulates ΔG ΔH := by
  intro μG μH hrel u dH
  obtain ⟨dG, hdG⟩ := h hrel u dH
  refine ⟨dG, ?_⟩
  rw [ViewFamily.claw_garble, ViewFamily.claw_garble, hdG]

/-- The identity realization simulates every family pair against itself: related
distributions are equal, so each target deviation is matched by itself. -/
theorem refl (V : ViewFamily G U Ω) (Δ : DeviationFamily G U) :
    (Realization.refl V).Simulates Δ Δ := by
  intro μG μH hrel u dH
  cases hrel
  exact ⟨dH, rfl⟩

end Realization.Simulates

/-- Coarsen the observed carrier of a whole transport. -/
def Transport.garble {G H : GameForm ι} {U : Type} {Ω Ω' : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (T : Transport G H VG VH ΔG ΔH) (g : ∀ u, Ω u → Ω' u) :
    Transport G H (VG.garble g) (VH.garble g) ΔG ΔH where
  toRealization := T.toRealization.garble g
  simulate := Realization.Simulates.garble g T.simulate

/-- The identity transport on a game, view family, and deviation family. -/
def Transport.refl {G : GameForm ι} {U : Type} {Ω : U → Type}
    (V : ViewFamily G U Ω) (Δ : DeviationFamily G U) :
    Transport G G V V Δ Δ where
  toRealization := Realization.refl V
  simulate := Realization.Simulates.refl V Δ

/-- A **transport bisimulation**: a realization that simulates a family pair in
both directions. It bundles the two transfers that make an equilibrium notion
*invariant* rather than merely preserved. -/
structure TransportBisimulation (G H : GameForm ι) {U : Type} {Ω : U → Type}
    (VG : ViewFamily G U Ω) (VH : ViewFamily H U Ω)
    (ΔG : DeviationFamily G U) (ΔH : DeviationFamily H U)
    extends Realization G H VG VH where
  /-- Forward backtranslation: target `ΔH` deviations by source `ΔG` ones. -/
  simulate : toRealization.Simulates ΔG ΔH
  /-- Backward backtranslation: source `ΔG` deviations by target `ΔH` ones. -/
  simulate_flip : toRealization.flip.Simulates ΔH ΔG

namespace TransportBisimulation

variable {G H : GameForm ι} {U : Type} {Ω : U → Type}
variable {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
variable {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}

/-- The forward transport of a bisimulation. -/
def toTransport (B : TransportBisimulation G H VG VH ΔG ΔH) :
    Transport G H VG VH ΔG ΔH where
  toRealization := B.toRealization
  simulate := B.simulate

/-- The backward transport of a bisimulation. -/
def toFlipTransport (B : TransportBisimulation G H VG VH ΔG ΔH) :
    Transport H G VH VG ΔH ΔG where
  toRealization := B.toRealization.flip
  simulate := B.simulate_flip

/-- The identity bisimulation on a game, view family, and deviation family. -/
def refl {G : GameForm ι} {U : Type} {Ω : U → Type}
    (V : ViewFamily G U Ω) (Δ : DeviationFamily G U) :
    TransportBisimulation G G V V Δ Δ where
  toRealization := Realization.refl V
  simulate := Realization.Simulates.refl V Δ
  simulate_flip := by
    intro μG μH hrel u dH
    cases hrel
    exact ⟨dH, rfl⟩

/-- Reverse a bisimulation: swap the forward and backward directions. The flipped
realization's two simulation obligations are exactly the original's, exchanged. -/
def symm (B : TransportBisimulation G H VG VH ΔG ΔH) :
    TransportBisimulation H G VH VG ΔH ΔG where
  toRealization := B.toRealization.flip
  simulate := B.simulate_flip
  simulate_flip := by
    intro μG μH hrel u dH
    exact B.simulate hrel u dH

end TransportBisimulation

end GameForm

end GameTheory
