module

/-
# Exact and ordinal potentials are genuinely different

This one-player fixture scales a strictly increasing utility by two.  The
scaled function preserves every improvement direction, so it is an ordinal
potential, but its nonzero difference cannot be an exact potential.  A second
one-player game chooses among the natural numbers; its two-valued payoff gives
a potential with finitely many values on infinitely many profiles.
-/

public import GameTheory.Core.Potential

@[expose] public section

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


/-! ## Preferences on laws without utility representations -/

/-- Only the possibility of outcome `true` matters. This preference compares
support membership directly and contains no utility or expectation operation. -/
def supportPreference : WeakPreference Unit Bool :=
  fun _ preferred alternative => true ∈ preferred.support ∨ true ∉ alternative.support

/-- A fair lottery still makes `true` possible. -/
def supportFairLaw : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure true) (PMF.pure false)

theorem true_mem_supportFairLaw : true ∈ supportFairLaw.support :=
  mem_support_mix_left (1 / 2) (by norm_num) (by norm_num) (by norm_num)
    (by simp)

/-- Possibility alone cannot be represented by real expected utility: the fair
lottery is as good as sure `true`, but sure `false` is strictly worse. -/
theorem supportPreference_not_expectedUtility :
    ¬ ∃ candidate : Bool → Unit → ℝ, supportPreference = euPreference candidate := by
  rintro ⟨candidate, hrepresentation⟩
  have hnot : ¬ euPreference candidate () (PMF.pure false) (PMF.pure true) := by
    rw [← hrepresentation]
    simp [supportPreference]
  have hnotBound := (euPreference_iff candidate () (PMF.pure false) (PMF.pure true)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).not.mp hnot
  have hfair : euPreference candidate () supportFairLaw (PMF.pure true) := by
    rw [← hrepresentation]
    exact Or.inl true_mem_supportFairLaw
  have hfairBound := (euPreference_iff candidate () supportFairLaw (PMF.pure true)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).mp hfair
  have hmix := expectedUtility_mix candidate () (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure true) (PMF.pure false)
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
  dsimp only [supportFairLaw] at hfairBound
  rw [hmix] at hfairBound
  simp only [expectedUtility_pure] at hnotBound hfairBound
  linarith

/-- The preferred deterministic outcome is a strict equilibrium for a
law-valued, nonnumeric comparison. -/
theorem trueProfile_support_strictNash :
    IsStrictNash form supportPreference trueProfile := by
  intro who
  cases who
  constructor
  · simp [supportPreference, trueProfile]
  · intro replacement hne
    cases replacement with
    | false =>
      simp [Preference.strict, Rank.strict, supportPreference, form,
        trueProfile, Profile.update_same]
    | true => exact (hne rfl).elim

/-- The response graph has the expected false-to-true edge. -/
theorem false_to_true_support_improvingStep :
    ImprovingStep form supportPreference falseProfile trueProfile := by
  refine ⟨(), true, ?_, ?_⟩
  · funext who
    cases who
    simp [trueProfile, Profile.update_same]
  · simp [Preference.strict, Rank.strict, supportPreference,
      trueProfile, falseProfile]

/-- A two-valued natural rank certifies termination independently of payoff. -/
def supportRank (profile : Profile signature) : ℕ :=
  if profile () then 1 else 0

theorem support_comparable (profile : Profile signature) (who : Unit)
    (replacement : signature.Strategy who) :
    supportPreference who (form.play profile)
        (form.play (Profile.update profile who replacement)) ∨
      supportPreference who (form.play (Profile.update profile who replacement))
        (form.play profile) := by
  cases who
  cases hcurrent : profile () <;> cases replacement <;>
    simp [supportPreference, form, hcurrent, Profile.update_same]

theorem supportRank_increases {source target : Profile signature}
    (hstep : ImprovingStep form supportPreference source target) :
    supportRank source < supportRank target := by
  obtain ⟨who, replacement, rfl, hstrict⟩ := hstep
  cases who
  cases hcurrent : source () <;> cases replacement <;>
    simp_all [Preference.strict, Rank.strict, supportPreference, form,
      supportRank, Profile.update_same]

/-- The generic finite-range rank theorem reaches equilibrium with no numeric
payoff interpretation of the preference. -/
theorem support_weaklyAcyclic : WeaklyAcyclic form supportPreference :=
  weaklyAcyclic_of_improvement_rank support_comparable supportRank
    (Set.finite_range supportRank) (fun hstep => supportRank_increases hstep)

/-- Comparability cannot be dropped: equality is a partial preference with no
strict gains, while a distinct outcome still violates weak-form Nash. -/
def equalityPreference : WeakPreference Unit Bool := fun _ preferred alternative =>
  preferred = alternative

theorem falseProfile_equality_not_isNash :
    ¬ IsNash form equalityPreference falseProfile := by
  intro hnash
  have h := (isNash_iff (F := form) (weaklyPrefers := equalityPreference)
    falseProfile).1 hnash () true
  have hlaw : (PMF.pure false : PMF Bool) = PMF.pure true := by
    simpa [equalityPreference, form, falseProfile, Profile.update_same] using h
  simpa using congrArg (fun law : PMF Bool => law false) hlaw

theorem equality_no_improvingStep (source target : Profile signature) :
    ¬ ImprovingStep form equalityPreference source target := by
  rintro ⟨_, _, _, hstrict⟩
  exact hstrict.2 hstrict.1.symm

/-- A singleton strategy leaves the genuine-alternative clause vacuous. -/
@[reducible]
def singletonSignature : GameSignature Unit where
  Strategy _ := Unit
  Outcome := Unit

@[reducible]
def singletonForm : GameForm Unit :=
  GameForm.deterministic singletonSignature fun _ => ()

def singletonProfile : Profile singletonSignature := fun _ => ()

def rejectsEveryLaw : WeakPreference Unit Unit := fun _ _ _ => False

theorem singleton_genuine_alternatives_vacuous :
    ∀ who (replacement : singletonSignature.Strategy who),
      replacement ≠ singletonProfile who →
        Preference.strict rejectsEveryLaw who (singletonForm.play singletonProfile)
          (singletonForm.play (Profile.update singletonProfile who replacement)) := by
  intro who replacement hne
  exact (hne (Subsingleton.elim _ _)).elim

/-- The self-comparison guard rules out a false strict-equilibrium verdict even
when there are no genuine alternatives. -/
theorem singleton_rejects_not_strictNash :
    ¬ IsStrictNash singletonForm rejectsEveryLaw singletonProfile := by
  intro hstrict
  exact (hstrict ()).1

end GameTheory.Tests.Potential
