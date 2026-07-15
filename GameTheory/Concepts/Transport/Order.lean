/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Transport.Transfer

/-!
# Composition of realizations and transports

Realizations compose relationally: `Realization.comp` chains two law-preserving
correspondences through a shared middle game and middle view family, its own
`law_eq` following by transitivity. Middle views are made comparable by garbling
both sides to a common carrier (`Realization.garble`), so composition asks only
that the two realizations already meet at one middle `ViewFamily`.

Composition of *transports* is the substance: given `T₁ : Transport G H … ΔG ΔH₁`
and `T₂ : Transport H K … ΔH₂ ΔK`, the composite backtranslation needs the middle
game's `ΔH₁` deviations — the ones `T₁` knows how to backtranslate — to be
matchable by `T₂` against the target family `ΔK`. That interface condition
`T₂.Simulates ΔH₁ ΔK` is supplied as data at each pipeline joint (`Transport.comp`);
`T₂`'s own chosen obligation `T₂.simulate : Simulates ΔH₂ ΔK` is *not* what the
composite consumes. An intersection or meet of the middle families does not
suffice: `T₂`'s witnesses need not land in it. When the middle families are
related by a morphism `ΔH₂ ⟶ ΔH₁`, `Transport.compOfHom` derives the interface
condition from `T₂.simulate` by `Simulates.mono_source`.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type}

/-- **Relational composition of realizations** through a shared middle game `H`
and middle view family `VH`: relate `μG` to `μK` when some middle `μH` is related
to both. The composite preserves the observed law by transitivity. -/
def Realization.comp {G H K : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {VK : ViewFamily K U Ω}
    (R₁ : Realization G H VG VH) (R₂ : Realization H K VH VK) :
    Realization G K VG VK where
  rel := fun μG μK => ∃ μH, R₁.rel μG μH ∧ R₂.rel μH μK
  law_eq := by
    rintro μG μK ⟨μH, h₁, h₂⟩ u
    rw [R₁.law_eq h₁ u, R₂.law_eq h₂ u]

namespace Realization

@[simp] theorem comp_rel {G H K : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {VK : ViewFamily K U Ω}
    (R₁ : Realization G H VG VH) (R₂ : Realization H K VH VK)
    (μG : PMF G.Profile) (μK : PMF K.Profile) :
    (R₁.comp R₂).rel μG μK ↔ ∃ μH, R₁.rel μG μH ∧ R₂.rel μH μK :=
  Iff.rfl

theorem refl_comp {G H : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    (R : Realization G H VG VH) :
    (refl VG).comp R |>.RelEquivalent R := by
  funext μG μH
  apply propext
  constructor
  · rintro ⟨μG', rfl, h⟩
    exact h
  · intro h
    exact ⟨μG, rfl, h⟩

theorem comp_refl {G H : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    (R : Realization G H VG VH) :
    R.comp (refl VH) |>.RelEquivalent R := by
  funext μG μH
  apply propext
  constructor
  · rintro ⟨μH', h, rfl⟩
    exact h
  · intro h
    exact ⟨μH, h, rfl⟩

theorem comp_assoc {G H K L : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {VK : ViewFamily K U Ω} {VL : ViewFamily L U Ω}
    (R₁ : Realization G H VG VH) (R₂ : Realization H K VH VK)
    (R₃ : Realization K L VK VL) :
    (R₁.comp R₂).comp R₃ |>.RelEquivalent (R₁.comp (R₂.comp R₃)) := by
  funext μG μL
  apply propext
  constructor
  · rintro ⟨μK, ⟨μH, h₁, h₂⟩, h₃⟩
    exact ⟨μH, h₁, μK, h₂, h₃⟩
  · rintro ⟨μH, h₁, μK, h₂, h₃⟩
    exact ⟨μK, ⟨μH, h₁, h₂⟩, h₃⟩

theorem comp_flip {G H K : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {VK : ViewFamily K U Ω}
    (R₁ : Realization G H VG VH) (R₂ : Realization H K VH VK) :
    (R₁.comp R₂).flip.RelEquivalent (R₂.flip.comp R₁.flip) := by
  funext μK μG
  apply propext
  constructor
  · rintro ⟨μH, h₁, h₂⟩
    exact ⟨μH, h₂, h₁⟩
  · rintro ⟨μH, h₂, h₁⟩
    exact ⟨μH, h₁, h₂⟩

theorem comp_garble {G H K : GameForm ι} {U : Type}
    {Ω Ω' : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {VK : ViewFamily K U Ω}
    (R₁ : Realization G H VG VH) (R₂ : Realization H K VH VK)
    (g : ∀ u, Ω u → Ω' u) :
    ((R₁.comp R₂).garble g).RelEquivalent
      ((R₁.garble g).comp (R₂.garble g)) :=
  rfl

end Realization

/-- **Composition of transports at the interface.** The composite realization
chains `T₁` and `T₂`; its backtranslation obligation is discharged by routing a
target `ΔK` deviation through the interface condition `hMid : T₂.Simulates ΔH₁ ΔK`
(matching it by a middle `ΔH₁` deviation with equal observed law) and then through
`T₁.simulate` (matching that middle deviation by a source `ΔG` one).

The interface condition is the point of the theorem, and it is data at each joint:
`T₂`'s own obligation `T₂.simulate : Simulates ΔH₂ ΔK` is never used, because
`T₁` backtranslates `ΔH₁` deviations, not `ΔH₂` ones, and an intersection of the
two middle families does not suffice — `T₂`'s witnesses need not land in it. -/
def Transport.comp {G H K : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {VK : ViewFamily K U Ω}
    {ΔG : DeviationFamily G U} {ΔH₁ ΔH₂ : DeviationFamily H U} {ΔK : DeviationFamily K U}
    (T₁ : Transport G H VG VH ΔG ΔH₁) (T₂ : Transport H K VH VK ΔH₂ ΔK)
    (hMid : T₂.toRealization.Simulates ΔH₁ ΔK) :
    Transport G K VG VK ΔG ΔK where
  toRealization := T₁.toRealization.comp T₂.toRealization
  simulate := by
    rintro μG μK ⟨μH, h₁, h₂⟩ u dK
    obtain ⟨dH₁, hdH₁⟩ := hMid h₂ u dK
    obtain ⟨dG, hdG⟩ := T₁.simulate h₁ u dH₁
    exact ⟨dG, hdG.trans hdH₁⟩

/-- **Composition of transports along a middle-family morphism.** When the middle
family `ΔH₂` that `T₂` backtranslates embeds into the middle family `ΔH₁` that
`T₁` consumes, the interface condition of `Transport.comp` is derived from
`T₂.simulate` by enlarging its source family (`Simulates.mono_source`). -/
def Transport.compOfHom {G H K : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {VK : ViewFamily K U Ω}
    {ΔG : DeviationFamily G U} {ΔH₁ ΔH₂ : DeviationFamily H U} {ΔK : DeviationFamily K U}
    (T₁ : Transport G H VG VH ΔG ΔH₁) (T₂ : Transport H K VH VK ΔH₂ ΔK)
    (φ : DeviationFamily.Hom id ΔH₂ ΔH₁) :
    Transport G K VG VK ΔG ΔK :=
  T₁.comp T₂ (Realization.Simulates.mono_source φ T₂.simulate)

/-- Composition of transports sharing the same middle deviation family. -/
def Transport.compSameMiddle {G H K : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {VK : ViewFamily K U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U} {ΔK : DeviationFamily K U}
    (T₁ : Transport G H VG VH ΔG ΔH) (T₂ : Transport H K VH VK ΔH ΔK) :
    Transport G K VG VK ΔG ΔK :=
  T₁.comp T₂ T₂.simulate

namespace Transport

@[simp] theorem comp_rel {G H K : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {VK : ViewFamily K U Ω}
    {ΔG : DeviationFamily G U} {ΔH₁ ΔH₂ : DeviationFamily H U}
    {ΔK : DeviationFamily K U}
    (T₁ : Transport G H VG VH ΔG ΔH₁) (T₂ : Transport H K VH VK ΔH₂ ΔK)
    (hMid : T₂.toRealization.Simulates ΔH₁ ΔK)
    (μG : PMF G.Profile) (μK : PMF K.Profile) :
    (T₁.comp T₂ hMid).rel μG μK ↔ ∃ μH, T₁.rel μG μH ∧ T₂.rel μH μK :=
  Iff.rfl

theorem refl_comp {G H : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (T : Transport G H VG VH ΔG ΔH) :
    (Transport.refl VG ΔG).compSameMiddle T |>.RelEquivalent T :=
  Realization.refl_comp T.toRealization

theorem comp_refl {G H : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (T : Transport G H VG VH ΔG ΔH) :
    T.compSameMiddle (Transport.refl VH ΔH) |>.RelEquivalent T :=
  Realization.comp_refl T.toRealization

theorem comp_assoc {G H K L : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {VK : ViewFamily K U Ω} {VL : ViewFamily L U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    {ΔK : DeviationFamily K U} {ΔL : DeviationFamily L U}
    (T₁ : Transport G H VG VH ΔG ΔH) (T₂ : Transport H K VH VK ΔH ΔK)
    (T₃ : Transport K L VK VL ΔK ΔL) :
    (T₁.compSameMiddle T₂).compSameMiddle T₃ |>.RelEquivalent
      (T₁.compSameMiddle (T₂.compSameMiddle T₃)) :=
  Realization.comp_assoc T₁.toRealization T₂.toRealization T₃.toRealization

theorem comp_garble {G H K : GameForm ι} {U : Type}
    {Ω Ω' : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {VK : ViewFamily K U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    {ΔK : DeviationFamily K U}
    (T₁ : Transport G H VG VH ΔG ΔH) (T₂ : Transport H K VH VK ΔH ΔK)
    (g : ∀ u, Ω u → Ω' u) :
    (T₁.compSameMiddle T₂).garble g |>.RelEquivalent
      ((T₁.garble g).compSameMiddle (T₂.garble g)) :=
  Realization.comp_garble T₁.toRealization T₂.toRealization g

end Transport

/-- **Composition of transport bisimulations at the interface.** The composite
realization chains `B₁` and `B₂` through the middle game `H`, and both backtranslation
obligations are supplied as data at the joint. The forward composite routes a target
`ΔK` deviation through `hFwd : B₂.Simulates ΔH₁ ΔK` (matching it by a middle `ΔH₁`
deviation, the family `B₁` backtranslates forward) and then through `B₁.simulate`. The
backward composite routes a source `ΔG` deviation through `hBwd : B₁.flip.Simulates ΔH₂
ΔG` (matching it by a middle `ΔH₂` deviation, the family `B₂` backtranslates backward)
and then through `B₂.simulate_flip`.

The two middle families enter asymmetrically: the forward joint consumes `ΔH₁`-facts
about `B₂` while the backward joint consumes `ΔH₂`-facts about `B₁`, because each
direction's *second* leg is the other bisimulation's own chosen obligation (`ΔH₁` for
`B₁.simulate`, `ΔH₂` for `B₂.simulate_flip`), so its *first* leg must produce that same
family. Neither bisimulation's own obligation alone suffices; an intersection of the two
middle families need not contain the required witnesses. -/
def TransportBisimulation.comp {G H K : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {VK : ViewFamily K U Ω}
    {ΔG : DeviationFamily G U} {ΔH₁ ΔH₂ : DeviationFamily H U} {ΔK : DeviationFamily K U}
    (B₁ : TransportBisimulation G H VG VH ΔG ΔH₁)
    (B₂ : TransportBisimulation H K VH VK ΔH₂ ΔK)
    (hFwd : B₂.toRealization.Simulates ΔH₁ ΔK)
    (hBwd : B₁.toRealization.flip.Simulates ΔH₂ ΔG) :
    TransportBisimulation G K VG VK ΔG ΔK where
  toRealization := B₁.toRealization.comp B₂.toRealization
  simulate := by
    rintro μG μK ⟨μH, h₁, h₂⟩ u dK
    obtain ⟨dH₁, hdH₁⟩ := hFwd h₂ u dK
    obtain ⟨dG, hdG⟩ := B₁.simulate h₁ u dH₁
    exact ⟨dG, hdG.trans hdH₁⟩
  simulate_flip := by
    rintro μK μG ⟨μH, h₁, h₂⟩ u dG
    obtain ⟨dH₂, hdH₂⟩ := hBwd h₁ u dG
    obtain ⟨dK, hdK⟩ := B₂.simulate_flip h₂ u dH₂
    exact ⟨dK, hdK.trans hdH₂⟩

/-- **Composition of bisimulations sharing a middle family.** When `B₁` and `B₂` meet
at the same middle deviation family `ΔH`, the two interface conditions of
`TransportBisimulation.comp` are exactly the bisimulations' own obligations
(`B₂.simulate` and `B₁.simulate_flip`), so the composite needs no extra data. -/
def TransportBisimulation.compSameMiddle {G H K : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {VK : ViewFamily K U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U} {ΔK : DeviationFamily K U}
    (B₁ : TransportBisimulation G H VG VH ΔG ΔH)
    (B₂ : TransportBisimulation H K VH VK ΔH ΔK) :
    TransportBisimulation G K VG VK ΔG ΔK :=
  B₁.comp B₂ B₂.simulate B₁.simulate_flip

namespace TransportBisimulation

theorem refl_comp {G H : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (B : TransportBisimulation G H VG VH ΔG ΔH) :
    (refl VG ΔG).compSameMiddle B |>.RelEquivalent B :=
  Realization.refl_comp B.toRealization

theorem comp_refl {G H : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (B : TransportBisimulation G H VG VH ΔG ΔH) :
    B.compSameMiddle (refl VH ΔH) |>.RelEquivalent B :=
  Realization.comp_refl B.toRealization

theorem comp_assoc {G H K L : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {VK : ViewFamily K U Ω} {VL : ViewFamily L U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    {ΔK : DeviationFamily K U} {ΔL : DeviationFamily L U}
    (B₁ : TransportBisimulation G H VG VH ΔG ΔH)
    (B₂ : TransportBisimulation H K VH VK ΔH ΔK)
    (B₃ : TransportBisimulation K L VK VL ΔK ΔL) :
    (B₁.compSameMiddle B₂).compSameMiddle B₃ |>.RelEquivalent
      (B₁.compSameMiddle (B₂.compSameMiddle B₃)) :=
  Realization.comp_assoc B₁.toRealization B₂.toRealization B₃.toRealization

theorem comp_symm {G H K : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω} {VK : ViewFamily K U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    {ΔK : DeviationFamily K U}
    (B₁ : TransportBisimulation G H VG VH ΔG ΔH)
    (B₂ : TransportBisimulation H K VH VK ΔH ΔK) :
    (B₁.compSameMiddle B₂).symm.RelEquivalent
      (B₂.symm.compSameMiddle B₁.symm) :=
  Realization.comp_flip B₁.toRealization B₂.toRealization

end TransportBisimulation

end GameForm

end GameTheory
