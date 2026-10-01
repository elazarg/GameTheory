/-
# Exact and ordinal potentials are genuinely different

This one-player fixture scales a strictly increasing utility by two.  The
scaled function preserves every improvement direction, so it is an ordinal
potential, but its nonzero difference cannot be an exact potential.  A second
one-player game chooses among the natural numbers; its two-valued payoff gives
a potential with finitely many values on infinitely many profiles.
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

theorem play_integrable (profile : Profile signature) (who : Unit) :
    UtilityIntegrable utility who (form.play profile) := by
  rw [GameForm.deterministic_play]
  exact payoffIntegrable_pure (profile ()) (fun outcome => utility outcome who)

/-- Multiplying all nonzero utility differences by two preserves their sign. -/
theorem scaledPotential_isOrdinal :
    IsOrdinalPotential form utility scaledPotential := by
  refine ⟨play_integrable, ?_⟩
  intro who profile replacement
  rcases who with ⟨⟩
  cases hcurrent : profile () <;> cases replacement <;>
    norm_num [form, utility, scaledPotential, hcurrent, Profile.update_same,
      expectedUtility_pure]

/-- The same scaling does not preserve the magnitude of the false-to-true
deviation, so the ordinal potential is not exact. -/
theorem scaledPotential_not_isExact :
    ¬ IsExactPotential form utility scaledPotential := by
  intro hexact
  have h := hexact.difference () falseProfile true
  norm_num [form, utility, scaledPotential, falseProfile,
    Profile.update_same, expectedUtility_pure] at h

/-- The ordinal-only theorem family is load-bearing: maximizing the scaled
potential proves that the true action is Nash without an exact certificate. -/
theorem trueProfile_isNash :
    IsNash form (euPreference utility) trueProfile := by
  apply scaledPotential_isOrdinal.isNash_of_maximal
  intro other
  simp only [scaledPotential, trueProfile]
  split <;> norm_num

/-- One player chooses a natural number. -/
@[reducible]
def countableSignature : GameSignature Unit where
  Strategy _ := ℕ
  Outcome := ℕ

@[reducible]
def countableForm : GameForm Unit :=
  GameForm.deterministic countableSignature fun profile => profile ()

/-- Even choices pay one, odd choices nothing. -/
def parityPayoff (outcome : ℕ) : ℝ := if Even outcome then 1 else 0

/-- Infinitely many profiles, a two-valued potential, and so a pure
equilibrium without finitely many profiles. -/
theorem countable_exists_isNash :
    ∃ profile : Profile countableSignature,
      IsNash countableForm (euPreference fun outcome _ => parityPayoff outcome) profile := by
  have hintegrable (profile : Profile countableSignature) :
      PayoffIntegrable (countableForm.play profile) parityPayoff := by
    rw [GameForm.deterministic_play]
    exact payoffIntegrable_pure _ _
  apply (isExactPotential_of_identicalInterests (F := countableForm) parityPayoff
    hintegrable).isOrdinalPotential.exists_isNash_of_finite_range
  apply (Set.toFinite ({0, 1} : Set ℝ)).subset
  rintro _ ⟨profile, rfl⟩
  simp only [expect_pure, parityPayoff]
  split_ifs <;> simp

end GameTheory.Tests.Potential
