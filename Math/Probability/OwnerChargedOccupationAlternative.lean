/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.ChargedOccupationAlternative

/-!
# Owner-preserving charged occupation alternatives

This file assembles the finite charged-occupation alternative independently
for every owner. The circulation branch never cancels transitions belonging
to different owners. In the potential branch, the scalar potentials are
assembled into one owner-indexed vector potential.
-/

noncomputable section

namespace Math
namespace Probability

variable {S Owner : Type*} {Index : Owner → Type*}

/-- Either one owner has a normalized positive charged circulation using only
that owner's transition family, or one owner-indexed potential controls every
transition in every family.

This is an exact exclusive alternative. It does not assert that an owner can
force entry into the support of the circulation. -/
theorem exists_ownerCirculation_xor_driftPotentialFamily
    [Fintype S] [DecidableEq S]
    [∀ owner, Fintype (Index owner)]
    (kernel : ∀ owner, Index owner → PMF S)
    (source : ∀ owner, Index owner → S)
    (charge : ∀ owner, Index owner → ℝ) :
    Xor
      (∃ owner,
        HasNormalizedPositiveChargedCirculation
          (actualOccupationColumn (kernel owner) (source owner))
          (charge owner))
      (∃ potential : Owner → S → ℝ,
        ∀ owner index,
          charge owner index ≤
            expect (kernel owner index) (potential owner) -
              potential owner (source owner index)) := by
  classical
  rw [xor_def]
  by_cases hcirculation :
      ∃ owner,
        HasNormalizedPositiveChargedCirculation
          (actualOccupationColumn (kernel owner) (source owner))
          (charge owner)
  · refine Or.inl ⟨hcirculation, ?_⟩
    rintro ⟨potential, hpotential⟩
    obtain ⟨owner, howner⟩ := hcirculation
    have halt :=
      normalizedPositiveChargedCirculation_xor_driftPotential
        (kernel owner) (source owner) (charge owner)
    rw [xor_def] at halt
    rcases halt with halt | halt
    · exact halt.2 ⟨potential owner, hpotential owner⟩
    · exact halt.2 howner
  · refine Or.inr ⟨?_, hcirculation⟩
    have hpotential :
        ∀ owner,
          ∃ potential : S → ℝ,
            ∀ index,
              charge owner index ≤
                expect (kernel owner index) potential -
                  potential (source owner index) := by
      intro owner
      have halt :=
        normalizedPositiveChargedCirculation_xor_driftPotential
          (kernel owner) (source owner) (charge owner)
      rw [xor_def] at halt
      rcases halt with halt | halt
      · exact False.elim (hcirculation ⟨owner, halt.1⟩)
      · exact halt.1
    choose potential hpotentialSpec using hpotential
    exact ⟨potential, hpotentialSpec⟩

end Probability
end Math
