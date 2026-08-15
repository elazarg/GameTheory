/-
# Exact and ordinal potentials are genuinely different

This one-player fixture scales a strictly increasing utility by two.  The
scaled function preserves every improvement direction, so it is an ordinal
potential, but its nonzero difference cannot be an exact potential.
-/

import GameTheory.Core.Potential

noncomputable section

namespace GameTheory.Tests.Potential

open GameTheory.Math.Probability

@[reducible]
def signature : GameSignature Unit where
  Strategy _ := Bool
  Outcome := Bool

@[reducible]
def form : GameForm Unit :=
  GameForm.deterministic signature fun profile => profile ()

def utility (outcome : Bool) (_who : Unit) : ℝ :=
  if outcome then 1 else 0

def scaledPotential (profile : Profile signature) : ℝ :=
  if profile () then 2 else 0

def falseProfile : Profile signature := fun _ => false

def trueProfile : Profile signature := fun _ => true

/-- Multiplying all nonzero utility differences by two preserves their sign. -/
theorem scaledPotential_isOrdinal :
    IsOrdinalPotential form utility scaledPotential := by
  intro who profile replacement
  rcases who with ⟨⟩
  cases hcurrent : profile () <;> cases replacement <;>
    norm_num [form, utility, scaledPotential, hcurrent, Profile.update_same]

/-- The same scaling does not preserve the magnitude of the false-to-true
deviation, so the ordinal potential is not exact. -/
theorem scaledPotential_not_isExact :
    ¬ IsExactPotential form utility scaledPotential := by
  intro hexact
  have h := hexact () falseProfile true
  norm_num [form, utility, scaledPotential, falseProfile,
    Profile.update_same] at h

/-- The ordinal-only theorem family is load-bearing: maximizing the scaled
potential proves that the true action is Nash without an exact certificate. -/
theorem trueProfile_isNash :
    IsNash form (euPreference utility) trueProfile := by
  apply scaledPotential_isOrdinal.isNash_of_maximal
  intro other
  simp only [scaledPotential, trueProfile]
  split <;> norm_num

end GameTheory.Tests.Potential
