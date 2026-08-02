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

import GameTheory.Core.Response

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
theorem IsOrdinalPotential.exists_isNash [Finite (Profile F.sig)] [Nonempty (Profile F.sig)]
    (hpotential : IsOrdinalPotential F utility potential) :
    ∃ profile : Profile F.sig, IsNash F (euPreference utility) profile := by
  obtain ⟨best, hmax⟩ := Finite.exists_max potential
  exact ⟨best, hpotential.isNash_of_maximal hmax⟩

theorem IsExactPotential.exists_isNash [Finite (Profile F.sig)] [Nonempty (Profile F.sig)]
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
theorem exists_isNash_of_identicalInterests [Finite (Profile F.sig)] [Nonempty (Profile F.sig)]
    (common : F.sig.Outcome → ℝ) :
    ∃ profile : Profile F.sig,
      IsNash F (euPreference fun outcome _ => common outcome) profile :=
  (isExactPotential_of_identicalInterests common).exists_isNash

/-! ## Local optima and improvement dynamics

The potential argument has two useful dynamic readings.  First, Nash profiles
are precisely the local potential maxima.  Second, a unilateral strict utility
improvement is a directed edge on profiles; finiteness turns an ordinal
potential into a well-founded ranking of those edges.  These are semantic
relations, rather than an executable better-response scheduler. -/

/-- In an ordinal potential game, Nash is exactly local maximality of the
potential under unilateral replacements. -/
theorem IsOrdinalPotential.isNash_iff_local_maximal
    (hpotential : IsOrdinalPotential F utility potential) {profile : Profile F.sig} :
    IsNash F (euPreference utility) profile ↔
      ∀ who replacement,
        potential (Profile.update profile who replacement) ≤ potential profile := by
  constructor
  · intro hnash who replacement
    by_contra hnot
    have hgain : expectedUtility utility who (F.play profile) <
        expectedUtility utility who (F.play (Profile.update profile who replacement)) :=
      (hpotential who profile replacement).2 (lt_of_not_ge hnot)
    exact (not_lt_of_ge ((isNash_iff profile).1 hnash who replacement)) hgain
  · intro hmax
    rw [isNash_iff]
    intro who replacement
    by_contra hgain
    have hpotentialGain : potential profile < potential (Profile.update profile who replacement) :=
      (hpotential who profile replacement).1 (lt_of_not_ge hgain)
    exact (not_lt_of_ge (hmax who replacement)) hpotentialGain

/-- The exact-potential specialization of local maximality. -/
theorem IsExactPotential.isNash_iff_local_maximal
    (hpotential : IsExactPotential F utility potential) {profile : Profile F.sig} :
    IsNash F (euPreference utility) profile ↔
      ∀ who replacement,
        potential (Profile.update profile who replacement) ≤ potential profile :=
  hpotential.isOrdinalPotential.isNash_iff_local_maximal

/-- The exact-potential difference identity, exposed under the canonical
expected-utility and profile-update vocabulary. -/
theorem IsExactPotential.expectedUtility_diff_eq_potential_diff
    (hpotential : IsExactPotential F utility potential) (profile : Profile F.sig)
    (who : ι) (replacement : F.sig.Strategy who) :
    expectedUtility utility who (F.play (Profile.update profile who replacement)) -
        expectedUtility utility who (F.play profile) =
      potential (Profile.update profile who replacement) - potential profile :=
  hpotential who profile replacement

/-- A strict expected-utility improvement strictly raises an exact potential. -/
theorem IsExactPotential.improving_deviation_increases_potential
    (hpotential : IsExactPotential F utility potential) {profile : Profile F.sig}
    {who : ι} {replacement : F.sig.Strategy who}
    (himprove : expectedUtility utility who (F.play profile) <
      expectedUtility utility who (F.play (Profile.update profile who replacement))) :
    potential profile < potential (Profile.update profile who replacement) := by
  have hdiff := hpotential who profile replacement
  linarith

/-- A global potential maximum admits no strictly improving unilateral move. -/
theorem IsExactPotential.no_improving_at_maximal
    (hpotential : IsExactPotential F utility potential) {profile : Profile F.sig}
    (hmax : ∀ other, potential other ≤ potential profile)
    (who : ι) (replacement : F.sig.Strategy who) :
    expectedUtility utility who (F.play (Profile.update profile who replacement)) ≤
      expectedUtility utility who (F.play profile) := by
  have hdiff := hpotential who profile replacement
  have hle := hmax (Profile.update profile who replacement)
  linarith

/-- A strict global maximum of an exact potential is a strict Nash profile. -/
theorem IsExactPotential.isStrictNash_of_strict_maximal
    (hpotential : IsExactPotential F utility potential) {profile : Profile F.sig}
    (hmax : ∀ other : Profile F.sig, other ≠ profile → potential other < potential profile) :
    IsStrictNash F utility profile := by
  intro who replacement hreplacement
  have hupdate_ne : Profile.update profile who replacement ≠ profile := by
    intro hupdate
    apply hreplacement
    have hcoordinate := congr_fun hupdate who
    simpa using hcoordinate
  have hlt := hmax (Profile.update profile who replacement) hupdate_ne
  have hdiff := hpotential who profile replacement
  linarith

/-- Every improving step strictly raises an exact potential. -/
theorem IsExactPotential.improvingStep_increases_potential
    (hpotential : IsExactPotential F utility potential) {source target : Profile F.sig}
    (hstep : ImprovingStep F utility source target) : potential source < potential target := by
  obtain ⟨who, replacement, htarget, himprove⟩ := hstep
  subst target
  exact hpotential.improving_deviation_increases_potential himprove

/-- A finite exact-potential game admits no infinite path of strict unilateral
expected-utility improvements. -/
theorem IsExactPotential.no_infinite_improving_path [Finite (Profile F.sig)]
    (hpotential : IsExactPotential F utility potential) :
    ¬ ∃ path : ℕ → Profile F.sig,
        ∀ n, ImprovingStep F utility (path n) (path (n + 1)) := by
  rintro ⟨path, hstep⟩
  have hincrease : ∀ n, potential (path n) < potential (path (n + 1)) :=
    fun n => hpotential.improvingStep_increases_potential (hstep n)
  have hmono : StrictMono (potential ∘ path) := strictMono_nat_of_lt_succ hincrease
  have hinjective : Function.Injective path := by
    intro left right heq
    have hpotentialEq : potential (path left) = potential (path right) := by rw [heq]
    exact hmono.injective hpotentialEq
  exact not_injective_infinite_finite path hinjective

/-- From every profile, some finite improving path reaches a Nash profile. -/
def WeaklyAcyclic (F : GameForm ι) (utility : F.sig.Outcome → ι → ℝ) : Prop :=
  ∀ source, ∃ target,
    Relation.ReflTransGen (ImprovingStep F utility) source target ∧
      IsNash F (euPreference utility) target

/-- Every improving step strictly raises an ordinal potential. -/
theorem IsOrdinalPotential.improvingStep_increases_potential
    (hpotential : IsOrdinalPotential F utility potential) {source target : Profile F.sig}
    (hstep : ImprovingStep F utility source target) : potential source < potential target := by
  obtain ⟨who, replacement, htarget, himprove⟩ := hstep
  subst target
  exact (hpotential who source replacement).1 himprove

/-- An ordinal-potential improving step strictly reduces the number of profiles
whose potential is higher. -/
theorem IsOrdinalPotential.improvingStep_filter_card_lt [Fintype (Profile F.sig)]
    (hpotential : IsOrdinalPotential F utility potential) {source target : Profile F.sig}
    (hstep : ImprovingStep F utility source target) :
    (Finset.univ.filter (fun profile => potential target < potential profile)).card <
      (Finset.univ.filter (fun profile => potential source < potential profile)).card := by
  have hpotentialIncrease := hpotential.improvingStep_increases_potential hstep
  have hsubset : (Finset.univ.filter (fun profile => potential target < potential profile)) ⊆
      Finset.univ.filter (fun profile => potential source < potential profile) := by
    intro profile hprofile
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hprofile ⊢
    exact lt_trans hpotentialIncrease hprofile
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset hsubset]
  exact ⟨target, by simp [hpotentialIncrease], by simp⟩

/-- Well-founded strict improvement is sufficient for weak acyclicity. -/
theorem weaklyAcyclic_of_wellFounded
    (hwellFounded : WellFounded (fun target source : Profile F.sig =>
      ImprovingStep F utility source target)) :
    WeaklyAcyclic F utility := by
  intro source
  induction source using hwellFounded.induction with
  | h source ih =>
    by_cases hnash : IsNash F (euPreference utility) source
    · exact ⟨source, Relation.ReflTransGen.refl, hnash⟩
    · obtain ⟨next, hstep⟩ := not_isNash_iff_exists_improvingStep.mp hnash
      obtain ⟨target, hreach, htarget⟩ := ih next hstep
      exact ⟨target, Relation.ReflTransGen.head hstep hreach, htarget⟩

/-- In a finite ordinal-potential game, strict improvement is well-founded. -/
theorem IsOrdinalPotential.improvement_wellFounded [Finite (Profile F.sig)]
    (hpotential : IsOrdinalPotential F utility potential) :
    WellFounded (fun target source : Profile F.sig => ImprovingStep F utility source target) := by
  have hsubrelation : Subrelation
      (fun target source : Profile F.sig => ImprovingStep F utility source target)
      (fun target source => potential source < potential target) := by
    intro target source hstep
    exact hpotential.improvingStep_increases_potential hstep
  exact hsubrelation.wf (Finite.wellFounded_of_trans_of_irrefl _)

/-- Every finite ordinal-potential game is weakly acyclic. -/
theorem IsOrdinalPotential.weaklyAcyclic [Finite (Profile F.sig)]
    (hpotential : IsOrdinalPotential F utility potential) : WeaklyAcyclic F utility :=
  weaklyAcyclic_of_wellFounded hpotential.improvement_wellFounded

/-- The exact-potential special case of ordinal-potential weak acyclicity. -/
theorem IsExactPotential.weaklyAcyclic [Finite (Profile F.sig)]
    (hpotential : IsExactPotential F utility potential) : WeaklyAcyclic F utility :=
  hpotential.isOrdinalPotential.weaklyAcyclic

/-! ## Team games

Identical outcome utilities imply identical expected utilities at every law.
That gives a potential for free and records the one degenerate overlap with
zero-sum games. -/

/-- Every team game is an exact potential game, using any player's expected
utility as the common potential. -/
theorem IsTeamGame.isExactPotential (hteam : IsTeamGame utility) (anchor : ι) :
    IsExactPotential F utility
      (fun profile => expectedUtility utility anchor (F.play profile)) := by
  intro who profile replacement
  have hbefore := hteam.expectedUtility_eq (F.play profile) who anchor
  have hafter := hteam.expectedUtility_eq
    (F.play (Profile.update profile who replacement)) who anchor
  linarith

/-- In a team game, Nash is exactly local maximality of any anchor player's
expected utility. -/
theorem IsTeamGame.isNash_iff_local_potential_maximal
    (hteam : IsTeamGame utility) (anchor : ι) (profile : Profile F.sig) :
    IsNash F (euPreference utility) profile ↔
      ∀ who replacement,
        expectedUtility utility anchor (F.play (Profile.update profile who replacement)) ≤
          expectedUtility utility anchor (F.play profile) :=
  (hteam.isExactPotential anchor).isNash_iff_local_maximal

end GameTheory
