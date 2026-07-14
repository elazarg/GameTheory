/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Transport.Simulation

/-!
# Characterization: simulation as preservation of a class of observation properties

This is the completeness layer of the transport theory. `Realization.Simulates`
was defined as an existential backtranslation obligation; here it is proved
*equivalent* to preserving exactly the right class of properties of what the
deviating units observe — so simulation is characterized, not merely shown
sufficient for transfer.

Fix a realization `R`, a related pair `(μG, μH)`, deviation families `ΔG`, `ΔH`,
and a unit `u`. Each side has a **deviation-law map**
`DeviationFamily.deviationLaw`, `d ↦ V.claw u (Δ.deviate μ u d)`, sending a
deviation to the observed correlated law it induces. Its image — the
**achievable-law set** `Set.range (Δ.deviationLaw V μ u)` — is the collection of
observed laws that unit `u` can force. Writing `S` for the source achievable-law
set and `T` for the target one, the pointwise backtranslation body of
`Simulates` at `(μG, μH, u)` sits in a characterization triangle:

* **backtranslation** `∀ dH, ∃ dG, lawG dG = lawH dH`
  (`simulates_iff_range_subset`, `simulates_iff_forall_fragment`) ⟺
* **range inclusion** `T ⊆ S` — every target-forceable law is source-forceable ⟺
* **∀-fragment preservation**: every property of the form `∀ d, L d ∈ P` (a
  subset-closed predicate on the achievable-law set) transfers from source to
  target.

The ∀-fragment — properties of the *laws*, quantified universally over
deviations — is exactly the class `Simulates` preserves. Strengthening to
preserve **arbitrary** predicates of the achievable-law *set* is strictly more:
`forall_predicate_iff_range_eq` shows it characterizes range **equality** `S = T`,
and `bisim_bodies_iff_range_eq` identifies that with two-sided backtranslation
(the `TransportBisimulation` bodies at the pair). This ∀-fragment /
arbitrary-predicate split is where the Clarkson–Schneider distinction between
properties of laws and properties of law-*sets* — trace properties versus
hyperproperties — becomes formal.

The refined interpolation between these two classes — safety-like/closure
subclasses of law-set predicates and the correspondingly weaker
backtranslations, the game-theoretic analogue of the interior nodes of the
Abate et al. secure-compilation grid — is deferred; it awaits the relational
form settling.
-/

namespace GameTheory

open Math.Probability

namespace GameForm

variable {ι : Type}

/-- The **deviation-law map** at unit `u`: send each deviation `d` available to
`u` to the observed correlated law `V.claw u (Δ.deviate μ u d)` it induces from
the status-quo distribution `μ`. Its range is the set of observed laws `u` can
force. -/
noncomputable def DeviationFamily.deviationLaw {F : GameForm ι} {U : Type} {Ω : U → Type}
    (Δ : DeviationFamily F U) (V : ViewFamily F U Ω) (μ : PMF F.Profile) (u : U) :
    Δ.Dev u → PMF (Ω u) :=
  fun d => V.claw u (Δ.deviate μ u d)

section Pointwise

variable {G H : GameForm ι} {U : Type} {Ω : U → Type}
  {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}
  {ΔG : DeviationFamily G U} {ΔH : DeviationFamily H U}
  {μG : PMF G.Profile} {μH : PMF H.Profile} {u : U}

/-- **Backtranslation ⟺ range inclusion**, at a fixed related pair and unit. The
`Simulates` body — every target deviation matched by a source deviation of equal
observed law — says exactly that the target achievable-law set is contained in
the source one. Near-definitional; the content is naming it. -/
theorem simulates_iff_range_subset :
    (∀ dH : ΔH.Dev u, ∃ dG : ΔG.Dev u,
        ΔG.deviationLaw VG μG u dG = ΔH.deviationLaw VH μH u dH) ↔
      Set.range (ΔH.deviationLaw VH μH u) ⊆ Set.range (ΔG.deviationLaw VG μG u) := by
  simp only [Set.range_subset_iff, Set.mem_range]

/-- **Backtranslation ⟺ ∀-fragment preservation**, at a fixed related pair and
unit. A ∀-fragment property is one of the form `∀ d, L d ∈ P` for a set of laws
`P` — equivalently a subset-closed predicate on the achievable-law set. Every
such property transfers from source to target iff the backtranslation body holds.
The interesting direction is preservation ⇒ backtranslation: instantiate
`P := Set.range (source law map)`, on which the source-side hypothesis is
trivially true, forcing every target law into the source range. -/
theorem simulates_iff_forall_fragment :
    (∀ dH : ΔH.Dev u, ∃ dG : ΔG.Dev u,
        ΔG.deviationLaw VG μG u dG = ΔH.deviationLaw VH μH u dH) ↔
      (∀ P : Set (PMF (Ω u)),
        (∀ dG, ΔG.deviationLaw VG μG u dG ∈ P) → ∀ dH, ΔH.deviationLaw VH μH u dH ∈ P) := by
  constructor
  · intro h P hP dH
    obtain ⟨dG, hdG⟩ := h dH
    rw [← hdG]
    exact hP dG
  · intro h dH
    have hmem := h (Set.range (ΔG.deviationLaw VG μG u)) (fun dG => Set.mem_range_self dG) dH
    rwa [Set.mem_range] at hmem

/-- **Arbitrary-predicate preservation ⟺ range equality**, at a fixed related
pair and unit. Preserving *every* predicate `Q` on the achievable-law set from
the source set to the target set is strictly stronger than the ∀-fragment: it
forces the two achievable-law sets to be equal. Forward is Leibniz —
instantiate `Q := (· = S)`; the converse is rewriting along the equality. -/
theorem forall_predicate_iff_range_eq :
    (∀ Q : Set (PMF (Ω u)) → Prop,
        Q (Set.range (ΔG.deviationLaw VG μG u)) → Q (Set.range (ΔH.deviationLaw VH μH u))) ↔
      Set.range (ΔG.deviationLaw VG μG u) = Set.range (ΔH.deviationLaw VH μH u) := by
  constructor
  · intro h
    exact (h (fun X => X = Set.range (ΔG.deviationLaw VG μG u)) rfl).symm
  · intro h Q hQ
    rwa [← h]

/-- **Two-sided backtranslation ⟺ range equality**, at a fixed related pair and
unit. The two `TransportBisimulation` bodies — target deviations matched in the
source and source deviations matched in the target — together say the two
achievable-law sets coincide. Combined with `forall_predicate_iff_range_eq`, a
transport bisimulation at the pair is what preserves arbitrary predicates of the
achievable-law set. -/
theorem bisim_bodies_iff_range_eq :
    ((∀ dH : ΔH.Dev u, ∃ dG : ΔG.Dev u,
        ΔG.deviationLaw VG μG u dG = ΔH.deviationLaw VH μH u dH) ∧
     (∀ dG : ΔG.Dev u, ∃ dH : ΔH.Dev u,
        ΔH.deviationLaw VH μH u dH = ΔG.deviationLaw VG μG u dG)) ↔
      Set.range (ΔG.deviationLaw VG μG u) = Set.range (ΔH.deviationLaw VH μH u) := by
  rw [Set.Subset.antisymm_iff]
  exact (and_congr simulates_iff_range_subset simulates_iff_range_subset).trans and_comm

end Pointwise

section Global

variable {G H : GameForm ι} {U : Type} {Ω : U → Type}
  {VG : ViewFamily G U Ω} {VH : ViewFamily H U Ω}

/-- **Global backtranslation ⟺ range inclusion.** `R.Simulates ΔG ΔH` holds iff,
at every related pair and unit, the target achievable-law set is contained in the
source one. The per-pair form of `simulates_iff_range_subset`, quantified over
`rel`. -/
theorem simulates_iff_forall_rel_range_subset (R : Realization G H VG VH)
    (ΔG : DeviationFamily G U) (ΔH : DeviationFamily H U) :
    R.Simulates ΔG ΔH ↔
      ∀ {μG : PMF G.Profile} {μH : PMF H.Profile}, R.rel μG μH →
        ∀ u, Set.range (ΔH.deviationLaw VH μH u) ⊆ Set.range (ΔG.deviationLaw VG μG u) := by
  constructor
  · intro h μG μH hrel u
    exact simulates_iff_range_subset.mp (h hrel u)
  · intro h μG μH hrel u dH
    exact simulates_iff_range_subset.mpr (h hrel u) dH

/-- **Global backtranslation ⟺ ∀-fragment preservation.** `R.Simulates ΔG ΔH`
holds iff, at every related pair and unit, every ∀-fragment property of the
achievable-law set transfers from source to target. The per-pair form of
`simulates_iff_forall_fragment`, quantified over `rel`; this states that the
∀-fragment is exactly the class of observation properties `Simulates` preserves. -/
theorem simulates_iff_forall_rel_fragment (R : Realization G H VG VH)
    (ΔG : DeviationFamily G U) (ΔH : DeviationFamily H U) :
    R.Simulates ΔG ΔH ↔
      ∀ {μG : PMF G.Profile} {μH : PMF H.Profile}, R.rel μG μH →
        ∀ u, ∀ P : Set (PMF (Ω u)),
          (∀ dG, ΔG.deviationLaw VG μG u dG ∈ P) → ∀ dH, ΔH.deviationLaw VH μH u dH ∈ P := by
  constructor
  · intro h μG μH hrel u
    exact simulates_iff_forall_fragment.mp (h hrel u)
  · intro h μG μH hrel u dH
    exact simulates_iff_forall_fragment.mpr (h hrel u) dH

/-- **Global two-sided backtranslation ⟺ range equality.** A realization
simulates the pair in both directions — the two `TransportBisimulation`
obligations, `R.Simulates ΔG ΔH` and `R.flip.Simulates ΔH ΔG` — iff, at every
related pair and unit, the two achievable-law sets coincide. The per-pair form of
`bisim_bodies_iff_range_eq`; with `forall_predicate_iff_range_eq` it says a
transport bisimulation is what preserves arbitrary predicates of the
achievable-law set. -/
theorem bisimulates_iff_forall_rel_range_eq (R : Realization G H VG VH)
    (ΔG : DeviationFamily G U) (ΔH : DeviationFamily H U) :
    (R.Simulates ΔG ΔH ∧ R.flip.Simulates ΔH ΔG) ↔
      ∀ {μG : PMF G.Profile} {μH : PMF H.Profile}, R.rel μG μH →
        ∀ u, Set.range (ΔG.deviationLaw VG μG u) = Set.range (ΔH.deviationLaw VH μH u) := by
  constructor
  · rintro ⟨h₁, h₂⟩ μG μH hrel u
    exact bisim_bodies_iff_range_eq.mp ⟨h₁ hrel u, h₂ hrel u⟩
  · intro h
    refine ⟨?_, ?_⟩
    · intro μG μH hrel u dH
      exact (bisim_bodies_iff_range_eq.mpr (h hrel u)).1 dH
    · intro μH μG hrel u dG
      exact (bisim_bodies_iff_range_eq.mpr (h hrel u)).2 dG

end Global

end GameForm

end GameTheory
