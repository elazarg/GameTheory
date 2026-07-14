/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Transport.Deviation

/-!
# Preference-level backtranslation

`PrefSimulates` is the backtranslation obligation of a transport read one level
below observed laws: instead of asking that a source deviation reproduce the
target's *observed law*, it asks only that the source deviation's
*non-profitability verdict* carry over to the target. Concretely, every
target-side deviation is matched by a source-side deviation whose "the status quo
is not strictly worse" fact, under the source preference, implies the same fact
for the target preference.

This is strictly weaker than `Realization.Simulates`, which forces the two
observed laws to be equal. Equal laws give equal verdicts for any
observation-shaped preference, so a law-based simulation is a `PrefSimulates`; but
a `PrefSimulates` can hold when the two games' outcome laws differ, as long as the
preference verdicts along matched deviations agree. This is exactly the level at
which utility-difference ("flow") invariance lives (Candogan–Menache–Ozdaglar–
Parrilo, *Flows and Decompositions of Games*, Math. Oper. Res. 2011): a
nonstrategic utility component moves the outcome law but cancels in every
unilateral incentive comparison, so it preserves verdicts without preserving laws.

The obligation is a plain implication, the minimal hypothesis for one-directional
transfer. The invariance ("both games satisfy the equilibrium notion or neither")
is two `PrefSimulates` facts in opposite directions, packaged by
`PrefSimulates.transfer_iff`.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type}

/-- `PrefSimulates rel prefG prefH ΔG ΔH`: preference-level backtranslation. For
every `rel`-related pair `(μG, μH)` and every target deviation `dH`, some source
deviation `dG` carries its verdict across — if `prefG` finds the source status quo
not strictly improved by `dG`, then `prefH` finds the target status quo not
strictly improved by `dH`. Weaker than `Realization.Simulates`, which demands
equal observed laws rather than merely matched verdicts. -/
def PrefSimulates {G H : GameForm ι} {U : Type}
    (rel : PMF G.Profile → PMF H.Profile → Prop)
    (prefG : U → PMF G.Outcome → PMF G.Outcome → Prop)
    (prefH : U → PMF H.Outcome → PMF H.Outcome → Prop)
    (ΔG : DeviationFamily G U) (ΔH : DeviationFamily H U) : Prop :=
  ∀ {μG μH}, rel μG μH → ∀ u (dH : ΔH.Dev u),
    ∃ dG : ΔG.Dev u,
      (prefG u (G.correlatedOutcome μG) (G.correlatedOutcome (ΔG.deviate μG u dG)) →
       prefH u (H.correlatedOutcome μH) (H.correlatedOutcome (ΔH.deviate μH u dH)))

/-- **Preference-level transfer.** A source deviation-family equilibrium transports
to the target along a `PrefSimulates`: each target deviation's verdict is supplied
by the matched source deviation. This is the single transfer argument that every
law-based transfer specialises to (see `Transport.target_eq_of_source_eq`). -/
theorem PrefSimulates.transfer {G H : GameForm ι} {U : Type}
    {rel : PMF G.Profile → PMF H.Profile → Prop}
    {prefG : U → PMF G.Outcome → PMF G.Outcome → Prop}
    {prefH : U → PMF H.Outcome → PMF H.Outcome → Prop}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (h : PrefSimulates rel prefG prefH ΔG ΔH)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : rel μG μH)
    (hEq : G.IsDeviationEqFor prefG μG ΔG) :
    H.IsDeviationEqFor prefH μH ΔH := by
  intro u dH
  obtain ⟨dG, himpl⟩ := h hrel u dH
  exact himpl (hEq u dG)

/-- The identity backtranslation: with `rel := Eq` and a single preference, each
target deviation is matched by itself and the verdict implication is reflexivity. -/
theorem PrefSimulates.refl {G : GameForm ι} {U : Type}
    (pref : U → PMF G.Outcome → PMF G.Outcome → Prop) (Δ : DeviationFamily G U) :
    PrefSimulates (G := G) (H := G) Eq pref pref Δ Δ := by
  intro μG μH hrel u dH
  cases hrel
  exact ⟨dH, fun h => h⟩

/-- Backtranslations compose through a middle game: chaining the two verdict
implications matches each target deviation with a source deviation, over the
relational composition of the two correspondences. -/
theorem PrefSimulates.comp {G H K : GameForm ι} {U : Type}
    {relGH : PMF G.Profile → PMF H.Profile → Prop}
    {relHK : PMF H.Profile → PMF K.Profile → Prop}
    {prefG : U → PMF G.Outcome → PMF G.Outcome → Prop}
    {prefH : U → PMF H.Outcome → PMF H.Outcome → Prop}
    {prefK : U → PMF K.Outcome → PMF K.Outcome → Prop}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U} {ΔK : DeviationFamily K U}
    (hGH : PrefSimulates relGH prefG prefH ΔG ΔH)
    (hHK : PrefSimulates relHK prefH prefK ΔH ΔK) :
    PrefSimulates (fun μG μK => ∃ μH, relGH μG μH ∧ relHK μH μK)
      prefG prefK ΔG ΔK := by
  rintro μG μK ⟨μH, hGH', hHK'⟩ u dK
  obtain ⟨dH, himplHK⟩ := hHK hHK' u dK
  obtain ⟨dG, himplGH⟩ := hGH hGH' u dH
  exact ⟨dG, fun h => himplHK (himplGH h)⟩

/-- Restrict the target family along a reindexing `DeviationFamily.Hom id`: since
the restricted deviations act identically, their verdicts are matched by the same
source deviations. -/
theorem PrefSimulates.mono_target {G H : GameForm ι} {U : Type}
    {rel : PMF G.Profile → PMF H.Profile → Prop}
    {prefG : U → PMF G.Outcome → PMF G.Outcome → Prop}
    {prefH : U → PMF H.Outcome → PMF H.Outcome → Prop}
    {ΔG : DeviationFamily G U} {ΔH ΔH' : DeviationFamily H U}
    (φ : DeviationFamily.Hom id ΔH' ΔH)
    (h : PrefSimulates rel prefG prefH ΔG ΔH) :
    PrefSimulates rel prefG prefH ΔG ΔH' := by
  intro μG μH hrel u dH'
  obtain ⟨dG, himpl⟩ := h hrel u (φ.map u dH')
  refine ⟨dG, ?_⟩
  have hφ : ΔH.deviate μH u (φ.map u dH') = ΔH'.deviate μH u dH' :=
    φ.deviate_eq μH u dH'
  rw [hφ] at himpl
  exact himpl

/-- **Preference-level invariance.** Two opposite backtranslations make the
equilibrium notion invariant: a `rel`-related pair satisfies the source concept
iff it satisfies the target concept. This is the `PrefSimulates` analogue of a
transport bisimulation, assembled from the two one-directional facts rather than a
bundled structure. -/
theorem PrefSimulates.transfer_iff {G H : GameForm ι} {U : Type}
    {rel : PMF G.Profile → PMF H.Profile → Prop}
    {prefG : U → PMF G.Outcome → PMF G.Outcome → Prop}
    {prefH : U → PMF H.Outcome → PMF H.Outcome → Prop}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (fwd : PrefSimulates rel prefG prefH ΔG ΔH)
    (bwd : PrefSimulates (fun μH μG => rel μG μH) prefH prefG ΔH ΔG)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : rel μG μH) :
    G.IsDeviationEqFor prefG μG ΔG ↔ H.IsDeviationEqFor prefH μH ΔH :=
  ⟨fun hEq => fwd.transfer hrel hEq, fun hEq => bwd.transfer hrel hEq⟩

end GameForm

end GameTheory
