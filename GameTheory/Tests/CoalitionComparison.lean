module

/-
# Coalition comparisons on the actual deviation laws

The preference is a partial order on laws. Its deterministic game only visits
the two point masses, which are comparable; a fair lottery remains incomparable
with a pure law. Strong Nash therefore has its strict-gain characterization
without requiring total preferences on unrelated lotteries.
-/

public import GameTheory.Core.Equilibrium
public import GameTheory.Math.Probability.FiniteUniform

@[expose] public section

noncomputable section

namespace GameTheory.Tests.CoalitionComparison

open GameTheory.Math.Probability

@[reducible]
def signature : GameSignature Unit where
  Strategy _ := Bool
  Outcome := Bool

@[reducible]
def form : GameForm Unit :=
  GameForm.deterministic signature fun profile => profile ()

def trueProfile : Profile signature := fun _ => true

def falseProfile : Profile signature := fun _ => false

/-- Distinct laws are comparable only along the pure-false to pure-true edge. -/
def partialPreference : WeakPreference Unit Bool :=
  fun _ preferred alternative => preferred = alternative ∨
    (preferred = PMF.pure true ∧ alternative = PMF.pure false)

theorem pure_false_ne_true : (PMF.pure false : PMF Bool) ≠ PMF.pure true := by
  intro heq
  have hmass := congrArg (fun law : PMF Bool => law true) heq
  norm_num at hmass

theorem partialPreference_reflexive : Preference.Reflexive partialPreference :=
  fun _ _ => Or.inl rfl

theorem partialPreference_transitive : Preference.Transitive partialPreference := by
  intro _ preferred middle alternative hfirst hsecond
  rcases hfirst with heq | ⟨hpreferred, hmiddle⟩
  · subst preferred
    exact hsecond
  · rcases hsecond with heq | ⟨hmiddle', _⟩
    · exact Or.inr ⟨hpreferred, heq.symm.trans hmiddle⟩
    · exact (pure_false_ne_true (hmiddle.symm.trans hmiddle')).elim

theorem partialPreference_antisymmetric : Preference.Antisymmetric partialPreference := by
  intro _ preferred alternative hforward hreverse
  rcases hforward with heq | ⟨_, halternative⟩
  · exact heq
  · rcases hreverse with heq | ⟨halternative', _⟩
    · exact heq.symm
    · exact (pure_false_ne_true (halternative.symm.trans halternative')).elim

def fairLaw : PMF Bool := uniformLaw Bool

theorem fairLaw_ne_pure_true : fairLaw ≠ PMF.pure true := by
  intro heq
  have hmass := congrArg (fun law : PMF Bool => law true) heq
  norm_num [fairLaw, uniformLaw_apply] at hmass

theorem fairLaw_ne_pure_false : fairLaw ≠ PMF.pure false := by
  intro heq
  have hmass := congrArg (fun law : PMF Bool => law true) heq
  norm_num [fairLaw, uniformLaw_apply] at hmass

/-- The global-totality characterization genuinely does not apply. -/
theorem partialPreference_not_total : ¬ Preference.Total partialPreference := by
  intro htotal
  rcases htotal () fairLaw (PMF.pure true) with hforward | hreverse
  · rcases hforward with heq | ⟨heq, _⟩ <;> exact fairLaw_ne_pure_true heq
  · rcases hreverse with heq | ⟨_, heq⟩
    · exact fairLaw_ne_pure_true heq.symm
    · exact fairLaw_ne_pure_false heq

theorem true_above_pure (who : Unit) (bit : Bool) :
    partialPreference who (PMF.pure true) (PMF.pure bit) := by
  cases bit
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl rfl

/-- Only the actual incumbent and replacement laws need to be comparable. -/
theorem true_profile_comparable :
    ∀ coalition : Finset Unit, coalition.Nonempty →
      ∀ replacement : Subprofile signature coalition, ∀ member ∈ coalition,
        partialPreference member (form.play trueProfile)
            (form.play (Profile.override coalition replacement trueProfile)) ∨
          partialPreference member (form.play (Profile.override coalition replacement trueProfile))
            (form.play trueProfile) := by
  intro coalition _ replacement member _
  exact Or.inl (true_above_pure member
    ((Profile.override coalition replacement trueProfile) ()))

/-- The local theorem establishes the canonical positive verdict despite
global incomparability of laws. -/
theorem trueProfile_isStrongNash : IsStrongNash form partialPreference trueProfile := by
  apply (isStrongNash_iff_not_all_gain_of_comparable (F := form)
    (weaklyPrefers := partialPreference) trueProfile true_profile_comparable).2
  intro coalition hnonempty replacement hall
  obtain ⟨member, hmember⟩ := hnonempty
  exact (hall member hmember).2
    (true_above_pure member ((Profile.override coalition replacement trueProfile) ()))

/-- A genuine singleton-coalition replacement rejects the false profile. -/
theorem falseProfile_not_isStrongNash : ¬ IsStrongNash form partialPreference falseProfile := by
  intro hstrong
  obtain ⟨member, _, hcomparison⟩ :=
    (isStrongNash_iff (F := form) (weaklyPrefers := partialPreference)
      falseProfile).1 hstrong {()} (by simp)
      (Subprofile.single (sig := signature) () true)
  cases member
  have hwrong : partialPreference () (PMF.pure false) (PMF.pure true) := by
    simpa [form, falseProfile, Profile.override_single, Profile.update_same] using hcomparison
  rcases hwrong with heq | ⟨heq, _⟩ <;> exact pure_false_ne_true heq

namespace Coordination

@[reducible]
def signature : GameSignature Bool where
  Strategy _ := Bool
  Outcome := Bool

@[reducible]
def form : GameForm Bool :=
  GameForm.deterministic signature fun profile => profile false && profile true

def preference : WeakPreference Bool Bool := fun _ => partialPreference ()

def trueProfile : Profile signature := fun _ => true

def falseProfile : Profile signature := fun _ => false

theorem preference_reflexive : Preference.Reflexive preference :=
  fun _ => partialPreference_reflexive ()

theorem preference_transitive : Preference.Transitive preference :=
  fun _ => partialPreference_transitive ()

theorem preference_antisymmetric : Preference.Antisymmetric preference :=
  fun _ => partialPreference_antisymmetric ()

theorem preference_not_total : ¬ Preference.Total preference := by
  intro htotal
  apply partialPreference_not_total
  intro _ preferred alternative
  exact htotal false preferred alternative

/-- Unilateral replacements cannot repair failed coordination. -/
theorem falseProfile_isNash : IsNash form preference falseProfile := by
  rw [isNash_iff]
  intro who replacement
  apply Or.inl
  cases who <;> cases replacement <;>
    simp [form, falseProfile, Profile.update_same, Profile.update_of_ne]

theorem true_profile_comparable :
    ∀ coalition : Finset Bool, coalition.Nonempty →
      ∀ replacement : Subprofile signature coalition, ∀ member ∈ coalition,
        preference member (form.play trueProfile)
            (form.play (Profile.override coalition replacement trueProfile)) ∨
          preference member (form.play (Profile.override coalition replacement trueProfile))
            (form.play trueProfile) := by
  intro coalition _ replacement _ _
  exact Or.inl (true_above_pure ()
    (((Profile.override coalition replacement trueProfile) false) &&
      ((Profile.override coalition replacement trueProfile) true)))

/-- Every member compares the actual coalition deviation laws, which suffices
for the strong-equilibrium verdict despite global partiality. -/
theorem trueProfile_isStrongNash : IsStrongNash form preference trueProfile := by
  apply (isStrongNash_iff_not_all_gain_of_comparable (F := form)
    (weaklyPrefers := preference) trueProfile true_profile_comparable).2
  intro coalition hnonempty replacement hall
  obtain ⟨member, hmember⟩ := hnonempty
  exact (hall member hmember).2 (true_above_pure ()
    (((Profile.override coalition replacement trueProfile) false) &&
      ((Profile.override coalition replacement trueProfile) true)))

/-- Both players must replace their actions together to obtain a strict gain.
Unilateral Nash therefore does not settle the coalition comparison. -/
theorem falseProfile_not_isStrongNash : ¬ IsStrongNash form preference falseProfile := by
  intro hstrong
  obtain ⟨_, _, hcomparison⟩ :=
    (isStrongNash_iff (F := form) (weaklyPrefers := preference)
      falseProfile).1 hstrong Finset.univ Finset.univ_nonempty
      (fun _ => true)
  have hwrong : partialPreference () (PMF.pure false) (PMF.pure true) := by
    simpa [preference, form, falseProfile, Profile.override] using hcomparison
  rcases hwrong with heq | ⟨heq, _⟩ <;> exact pure_false_ne_true heq

end Coordination

end GameTheory.Tests.CoalitionComparison
