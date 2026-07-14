/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Foundations.Transport.Simulation

/-!
# Generic transfer of deviation-family equilibrium

The single transfer theorem: along a `Transport`, a deviation-family equilibrium
for the source under observed preferences is a deviation-family equilibrium for
the target under the corresponding observed preferences. Every named
solution-concept transport is an instantiation of this theorem — no solution
concept keeps a bespoke transfer proof.

The unilateral instantiations (Nash, correlated, coarse-correlated) live with the
`DeviationSimulation` corollaries. The coalition instantiation is here:
`Transport.target_strongNashEq_of_source_strongNashEq` transports strong-Nash-style
`noParetoBlock` equilibria, using `observedPref_noParetoBlock_const` to factor the
coalition Pareto aggregator through a global view.

The argument is per unit: the target-side deviation is backtranslated (`simulate`)
to a source-side one with the same observed law, and the source equilibrium's
inequality is carried across by rewriting along the base `law_eq` and the
backtranslation equality.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type}

/-- **Generic transfer.** A source deviation-family equilibrium under observed
preferences transports to a target one along a transport that simulates the
family pair. -/
theorem Transport.target_eq_of_source_eq {G H : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (T : Transport G H VG VH ΔG ΔH)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : T.rel μG μH)
    {prefΩ : ∀ u, PMF (Ω u) → PMF (Ω u) → Prop}
    (hEq : G.IsDeviationEqFor (observedPref VG prefΩ) μG ΔG) :
    H.IsDeviationEqFor (observedPref VH prefΩ) μH ΔH := by
  intro u dH
  obtain ⟨dG, hdev⟩ := T.simulate hrel u dH
  have hsrc : prefΩ u (VG.claw u μG) (VG.claw u (ΔG.deviate μG u dG)) := hEq u dG
  rw [T.law_eq hrel u, hdev] at hsrc
  exact hsrc

/-- **Generic invariance.** A deviation-family equilibrium is preserved in both
directions along a bisimulation. -/
theorem TransportBisimulation.eq_iff {G H : GameForm ι} {U : Type} {Ω : U → Type}
    {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
    {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
    (B : TransportBisimulation G H VG VH ΔG ΔH)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : B.rel μG μH)
    {prefΩ : ∀ u, PMF (Ω u) → PMF (Ω u) → Prop} :
    G.IsDeviationEqFor (observedPref VG prefΩ) μG ΔG ↔
      H.IsDeviationEqFor (observedPref VH prefΩ) μH ΔH := by
  constructor
  · intro hEq
    exact B.toTransport.target_eq_of_source_eq hrel hEq
  · intro hEq
    exact B.toFlipTransport.target_eq_of_source_eq hrel hEq

/-- **Coalition aggregator commutes with a constant view.** At a global (constant)
view, observing the coalition Pareto-block aggregator of per-player preferences is
the same as aggregating the observed per-player preferences: the aggregators only
ever apply the player relations to the two observed laws, so pushing the
observation inside is definitional. This is the factoring that lets the generic
transfer read in strong-Nash vocabulary. -/
theorem observedPref_noParetoBlock_const {F : GameForm ι} {Ω₀ : Type}
    (obs : F.Outcome → Ω₀) (prefΩ sprefΩ : ι → PMF Ω₀ → PMF Ω₀ → Prop) :
    observedPref (ViewFamily.const (U := Coalition ι) obs) (noParetoBlock prefΩ sprefΩ) =
      noParetoBlock (observedPref (ViewFamily.const (U := ι) obs) prefΩ)
        (observedPref (ViewFamily.const (U := ι) obs) sprefΩ) :=
  rfl

/-- **Strong-Nash-style equilibrium transports.** A source no-Pareto-block
(strong-Nash) coalition equilibrium under observed per-player preferences
transports to the target along a coalition transport with global views. This is
the coalition instantiation of `Transport.target_eq_of_source_eq`, factored so the
statement is phrased in the strong-Nash `noParetoBlock` vocabulary. -/
theorem Transport.target_strongNashEq_of_source_strongNashEq {G H : GameForm ι} {Ω₀ : Type}
    {obsG : G.Outcome → Ω₀} {obsH : H.Outcome → Ω₀}
    {ΔG : DeviationFamily G (Coalition ι)} {ΔH : DeviationFamily H (Coalition ι)}
    (T : Transport G H (ViewFamily.const obsG) (ViewFamily.const obsH) ΔG ΔH)
    {μG : PMF G.Profile} {μH : PMF H.Profile} (hrel : T.rel μG μH)
    {prefΩ sprefΩ : ι → PMF Ω₀ → PMF Ω₀ → Prop}
    (hEq : G.IsDeviationEqFor
      (noParetoBlock (observedPref (ViewFamily.const (U := ι) obsG) prefΩ)
        (observedPref (ViewFamily.const (U := ι) obsG) sprefΩ)) μG ΔG) :
    H.IsDeviationEqFor
      (noParetoBlock (observedPref (ViewFamily.const (U := ι) obsH) prefΩ)
        (observedPref (ViewFamily.const (U := ι) obsH) sprefΩ)) μH ΔH := by
  rw [← observedPref_noParetoBlock_const] at hEq
  rw [← observedPref_noParetoBlock_const]
  exact T.target_eq_of_source_eq hrel hEq

end GameForm

end GameTheory
