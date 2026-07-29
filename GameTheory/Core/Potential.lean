/-
# Potential games

A potential is a single real function on profiles that every player's incentives
follow. It buys the one thing a general game does not have: a reason for a pure
equilibrium to exist at all, with no fixed-point theorem and no topology —
maximize the potential and nobody can gain by moving alone.

Two strengths are recorded, because the existence argument needs only the weaker
one. An *exact* potential moves by exactly as much as the deviator's expected
utility; an *ordinal* potential only has to move in the same direction. The
first implies the second and the theorems are proved for the second.
-/

import GameTheory.Core.Equilibrium
import GameTheory.Core.Utility

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

variable {ι : Type uι} [DecidableEq ι] {F : GameForm ι}
variable {utility : F.sig.Outcome → ι → ℝ} {potential : Profile F.sig → ℝ}

variable (F utility potential) in
/-- Every unilateral change moves the deviator's expected utility by exactly as
much as it moves the potential. -/
def IsExactPotential : Prop :=
  ∀ (who : ι) (profile : Profile F.sig) (replacement : F.sig.Strategy who),
    expectedUtility utility who (F.play (Profile.update profile who replacement)) -
        expectedUtility utility who (F.play profile) =
      potential (Profile.update profile who replacement) - potential profile

variable (F utility potential) in
/-- Every unilateral change moves the deviator's expected utility *up* exactly
when it moves the potential up. This is all the existence argument uses. -/
def IsOrdinalPotential : Prop :=
  ∀ (who : ι) (profile : Profile F.sig) (replacement : F.sig.Strategy who),
    expectedUtility utility who (F.play profile) <
        expectedUtility utility who (F.play (Profile.update profile who replacement)) ↔
      potential profile < potential (Profile.update profile who replacement)

/-- An exact potential is an ordinal one: equal differences have equal signs. -/
theorem IsExactPotential.isOrdinalPotential (hpotential : IsExactPotential F utility potential) :
    IsOrdinalPotential F utility potential := by
  intro who profile replacement
  have hdiff := hpotential who profile replacement
  constructor <;> intro hlt <;> linarith

/-- **A maximizer of the potential is a pure equilibrium.** No player can gain
alone, because gaining alone would raise the potential. -/
theorem IsOrdinalPotential.isNash_of_maximal
    (hpotential : IsOrdinalPotential F utility potential) {profile : Profile F.sig}
    (hmax : ∀ other, potential other ≤ potential profile) :
    IsNash F (euPreference utility) profile := by
  rw [isNash_iff]
  intro who replacement
  show expectedUtility utility who (F.play (Profile.update profile who replacement)) ≤
    expectedUtility utility who (F.play profile)
  by_contra hgain
  exact absurd ((hpotential who profile replacement).1 (not_le.1 hgain))
    (not_lt.2 (hmax (Profile.update profile who replacement)))

theorem IsExactPotential.isNash_of_maximal (hpotential : IsExactPotential F utility potential)
    {profile : Profile F.sig} (hmax : ∀ other, potential other ≤ potential profile) :
    IsNash F (euPreference utility) profile :=
  hpotential.isOrdinalPotential.isNash_of_maximal hmax

/-- **A finite potential game has a pure equilibrium.** The potential attains a
maximum on a finite nonempty profile space, and that maximizer is one. No
fixed-point theorem is used, and none is available at this layer. -/
theorem IsOrdinalPotential.exists_isNash [Fintype (Profile F.sig)] [Nonempty (Profile F.sig)]
    (hpotential : IsOrdinalPotential F utility potential) :
    ∃ profile : Profile F.sig, IsNash F (euPreference utility) profile := by
  obtain ⟨best, -, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Profile F.sig)) potential
      ⟨Classical.arbitrary _, Finset.mem_univ _⟩
  exact ⟨best, hpotential.isNash_of_maximal fun other => hmax other (Finset.mem_univ other)⟩

theorem IsExactPotential.exists_isNash [Fintype (Profile F.sig)] [Nonempty (Profile F.sig)]
    (hpotential : IsExactPotential F utility potential) :
    ∃ profile : Profile F.sig, IsNash F (euPreference utility) profile :=
  hpotential.isOrdinalPotential.exists_isNash

/-! ## A family that always has one

A potential constrains only *unilateral* changes, so it says nothing about
coalitions and nothing about efficiency: the maximizer is an equilibrium, not
necessarily the profile the players would agree on. What it does supply is
existence, and one natural family supplies the potential for free. -/

/-- **Identical interests are a potential game**, with the common payoff as the
potential. Nothing is computed: when every player values an outcome the same, the
deviator's change *is* the potential's change. -/
theorem isExactPotential_of_identicalInterests (common : F.sig.Outcome → ℝ) :
    IsExactPotential F (fun outcome _ => common outcome)
      (fun profile => (F.play profile).expect common) :=
  fun _ _ _ => rfl

/-- Hence a finite game of identical interests has a pure equilibrium. -/
theorem exists_isNash_of_identicalInterests [Fintype (Profile F.sig)] [Nonempty (Profile F.sig)]
    (common : F.sig.Outcome → ℝ) :
    ∃ profile : Profile F.sig,
      IsNash F (euPreference fun outcome _ => common outcome) profile :=
  (isExactPotential_of_identicalInterests common).exists_isNash

end GameTheory
