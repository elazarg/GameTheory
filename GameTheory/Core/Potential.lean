module

/-
# Potential games

A finite-range improvement rank takes values in a preorder and strictly rises
along every improving move. Local comparability then makes improvement paths
reach a Nash profile, without fixed-point theorems, topology, or numerical
preferences. The profile carrier itself may be infinite.

For expected utility, two numerical potential certificates are recorded. An
*exact* potential moves by exactly as much as the deviator's expected
utility; an *ordinal* potential only has to move in the same direction. The
first implies the second, and the equilibrium-existence family is proved at
the ordinal level.

Primary reference: D. Monderer and L. S. Shapley, “Potential Games,” *Games
and Economic Behavior* 14 (1996).
-/

public import GameTheory.Core.Response

@[expose] public section

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι} [DecidableEq ι] {F : GameForm ι}
variable {utility : F.sig.Outcome → ι → ℝ} {potential : Profile F.sig → ℝ}

/-- A rank with finite range makes strict improvement well-founded. Only a
preorder on rank values is needed; profiles may form an infinite type. -/
theorem improvement_wellFounded_of_improvement_rank
    {prefers : WeakPreference ι F.sig.Outcome} {V : Type*} [Preorder V]
    (rank : Profile F.sig → V) (hrange : (Set.range rank).Finite)
    (hincrease : ∀ {source target}, ImprovingStep F prefers source target →
      rank source < rank target) :
    WellFounded (fun target source : Profile F.sig => ImprovingStep F prefers source target) := by
  have := hrange.to_subtype
  have hvalues : WellFounded (fun later earlier : Set.range rank => earlier.1 < later.1) :=
    Finite.wellFounded_of_trans_of_irrefl _
  have hsubrelation : Subrelation
      (fun target source : Profile F.sig => ImprovingStep F prefers source target)
      (InvImage (fun later earlier : Set.range rank => earlier.1 < later.1)
        fun profile => ⟨rank profile, profile, rfl⟩) := by
    intro target source hstep
    exact hincrease hstep
  exact hsubrelation.wf (InvImage.wf _ hvalues)

/-- Local comparability and a finite-range improvement rank suffice for weak
acyclicity, without numerical preferences or a finite profile carrier. -/
theorem weaklyAcyclic_of_improvement_rank
    {prefers : WeakPreference ι F.sig.Outcome} {V : Type*} [Preorder V]
    (hcompare : ∀ (profile : Profile F.sig) who replacement,
      prefers who (F.play profile) (F.play (Profile.update profile who replacement)) ∨
        prefers who (F.play (Profile.update profile who replacement)) (F.play profile))
    (rank : Profile F.sig → V) (hrange : (Set.range rank).Finite)
    (hincrease : ∀ {source target}, ImprovingStep F prefers source target →
      rank source < rank target) : WeaklyAcyclic F prefers :=
  weaklyAcyclic_of_wellFounded hcompare
    (improvement_wellFounded_of_improvement_rank rank hrange hincrease)

/-- A nonempty game with locally comparable preferences has a Nash profile
when strict improvement raises a finite-range rank. -/
theorem exists_isNash_of_improvement_rank [Nonempty (Profile F.sig)]
    {prefers : WeakPreference ι F.sig.Outcome} {V : Type*} [Preorder V]
    (hcompare : ∀ (profile : Profile F.sig) who replacement,
      prefers who (F.play profile) (F.play (Profile.update profile who replacement)) ∨
        prefers who (F.play (Profile.update profile who replacement)) (F.play profile))
    (rank : Profile F.sig → V) (hrange : (Set.range rank).Finite)
    (hincrease : ∀ {source target}, ImprovingStep F prefers source target →
      rank source < rank target) : ∃ profile, IsNash F prefers profile := by
  obtain ⟨profile, _, hnash⟩ := weaklyAcyclic_of_improvement_rank hcompare rank hrange hincrease
    (Classical.choice ‹Nonempty (Profile F.sig)›)
  exact ⟨profile, hnash⟩

variable (F utility potential) in
/-- Every unilateral change moves the deviator's expected utility by exactly as
much as it moves the potential. -/
structure IsExactPotential : Prop where
  integrable : ∀ (profile : Profile F.sig) (who : ι),
    UtilityIntegrable utility who (F.play profile)
  difference : ∀ (who : ι) (profile : Profile F.sig)
      (replacement : F.sig.Strategy who),
    expectedUtility utility who (F.play (Profile.update profile who replacement)) -
      expectedUtility utility who (F.play profile) =
        potential (Profile.update profile who replacement) - potential profile

variable (F utility potential) in
/-- Every unilateral change moves the deviator's expected utility *up* exactly
when it moves the potential up. This is all the existence argument uses. -/
structure IsOrdinalPotential : Prop where
  integrable : ∀ (profile : Profile F.sig) (who : ι),
    UtilityIntegrable utility who (F.play profile)
  comparison : ∀ (who : ι) (profile : Profile F.sig)
      (replacement : F.sig.Strategy who),
    expectedUtility utility who (F.play profile) <
        expectedUtility utility who (F.play (Profile.update profile who replacement))
           ↔
      potential profile < potential (Profile.update profile who replacement)

/-- An exact potential is an ordinal one: equal differences have equal signs. -/
theorem IsExactPotential.isOrdinalPotential (hpotential : IsExactPotential F utility potential) :
    IsOrdinalPotential F utility potential := by
  refine ⟨hpotential.integrable, ?_⟩
  intro who profile replacement
  have hdiff := hpotential.difference who profile replacement
  constructor <;> intro hlt <;> linarith

/-- Integrability in an ordinal-potential certificate supplies both directions
of every local expected-utility comparison. -/
theorem IsOrdinalPotential.deviation_comparable
    (hpotential : IsOrdinalPotential F utility potential)
    (profile : Profile F.sig) (who : ι) (replacement : F.sig.Strategy who) :
    euPreference utility who (F.play profile)
        (F.play (Profile.update profile who replacement)) ∨
      euPreference utility who (F.play (Profile.update profile who replacement))
        (F.play profile) := by
  rcases le_total
      (expectedUtility utility who (F.play (Profile.update profile who replacement)))
      (expectedUtility utility who (F.play profile)) with hle | hle
  · exact Or.inl ((euPreference_iff utility who _ _
      (hpotential.integrable profile who)
      (hpotential.integrable (Profile.update profile who replacement) who)).2 hle)
  · exact Or.inr ((euPreference_iff utility who _ _
      (hpotential.integrable (Profile.update profile who replacement) who)
      (hpotential.integrable profile who)).2 hle)

/-- **A maximizer of the potential is a pure equilibrium.** No player can gain
alone, because gaining alone would raise the potential. -/
theorem IsOrdinalPotential.isNash_of_maximal
    (hpotential : IsOrdinalPotential F utility potential) {profile : Profile F.sig}
    (hmax : ∀ other, potential other ≤ potential profile) :
    IsNash F (euPreference utility) profile := by
  rw [isNash_iff]
  intro who replacement
  apply (euPreference_iff utility who (F.play profile)
    (F.play (Profile.update profile who replacement))
    (hpotential.integrable profile who)
    (hpotential.integrable (Profile.update profile who replacement) who)).2
  by_contra hgain
  exact absurd ((hpotential.comparison who profile replacement).1 (not_le.1 hgain))
    (not_lt.2 (hmax (Profile.update profile who replacement)))

theorem IsExactPotential.isNash_of_maximal (hpotential : IsExactPotential F utility potential)
    {profile : Profile F.sig} (hmax : ∀ other, potential other ≤ potential profile) :
    IsNash F (euPreference utility) profile :=
  hpotential.isOrdinalPotential.isNash_of_maximal hmax

/-- **A potential with finitely many values has a pure equilibrium.** The
potential attains its largest value, and a profile attaining it is one. Strategy
and profile carriers may be infinite. No fixed-point theorem is used, and none
is available at this layer. -/
theorem IsOrdinalPotential.exists_isNash_of_finite_range [Nonempty (Profile F.sig)]
    (hpotential : IsOrdinalPotential F utility potential)
    (hrange : (Set.range potential).Finite) :
    ∃ profile : Profile F.sig, IsNash F (euPreference utility) profile := by
  apply exists_isNash_of_improvement_rank hpotential.deviation_comparable potential hrange
  rintro source target ⟨who, replacement, htarget, hstrict⟩
  subst target
  exact (hpotential.comparison who source replacement).1
    ((euPreference_strict_iff utility who _ _
      (hpotential.integrable (Profile.update source who replacement) who)
      (hpotential.integrable source who)).1 hstrict)

/-- **A finite potential game has a pure equilibrium.** -/
theorem IsOrdinalPotential.exists_isNash [Finite (Profile F.sig)] [Nonempty (Profile F.sig)]
    (hpotential : IsOrdinalPotential F utility potential) :
    ∃ profile : Profile F.sig, IsNash F (euPreference utility) profile :=
  hpotential.exists_isNash_of_finite_range (Set.finite_range potential)

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
theorem isExactPotential_of_identicalInterests (common : F.sig.Outcome → ℝ)
    (hintegrable : ∀ profile : Profile F.sig,
      PayoffIntegrable (F.play profile) common) :
    IsExactPotential F (fun outcome _ => common outcome)
      (fun profile => expect (F.play profile) common) := by
  refine ⟨?_, ?_⟩
  · intro profile who
    exact hintegrable profile
  · intro who profile replacement
    rfl

/-- Hence a finite game of identical interests has a pure equilibrium. -/
theorem exists_isNash_of_identicalInterests [Finite (Profile F.sig)] [Nonempty (Profile F.sig)]
    (common : F.sig.Outcome → ℝ)
    (hintegrable : ∀ profile : Profile F.sig,
      PayoffIntegrable (F.play profile) common) :
    ∃ profile : Profile F.sig,
      IsNash F (euPreference fun outcome _ => common outcome) profile :=
  (isExactPotential_of_identicalInterests common hintegrable).exists_isNash

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
      (hpotential.comparison who profile replacement).2 (lt_of_not_ge hnot)
    have hpref := (euPreference_iff utility who (F.play profile)
      (F.play (Profile.update profile who replacement))
      (hpotential.integrable profile who)
      (hpotential.integrable (Profile.update profile who replacement) who)).mp
        ((isNash_iff profile).1 hnash who replacement)
    exact (not_lt_of_ge hpref) hgain
  · intro hmax
    rw [isNash_iff]
    intro who replacement
    apply (euPreference_iff utility who (F.play profile)
      (F.play (Profile.update profile who replacement))
      (hpotential.integrable profile who)
      (hpotential.integrable (Profile.update profile who replacement) who)).2
    by_contra hgain
    have hpotentialGain := (hpotential.comparison who profile replacement).1
      (not_le.1 hgain)
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
  hpotential.difference who profile replacement

/-- A strict expected-utility improvement strictly raises an exact potential. -/
theorem IsExactPotential.improving_deviation_increases_potential
    (hpotential : IsExactPotential F utility potential) {profile : Profile F.sig}
    {who : ι} {replacement : F.sig.Strategy who}
    (himprove : expectedUtility utility who (F.play profile) <
      expectedUtility utility who (F.play (Profile.update profile who replacement))) :
    potential profile < potential (Profile.update profile who replacement) := by
  have hdiff := hpotential.difference who profile replacement
  linarith

/-- A global potential maximum admits no strictly improving unilateral move. -/
theorem IsExactPotential.no_improving_at_maximal
    (hpotential : IsExactPotential F utility potential) {profile : Profile F.sig}
    (hmax : ∀ other, potential other ≤ potential profile)
    (who : ι) (replacement : F.sig.Strategy who) :
    expectedUtility utility who (F.play (Profile.update profile who replacement)) ≤
      expectedUtility utility who (F.play profile) := by
  have hdiff := hpotential.difference who profile replacement
  have hle := hmax (Profile.update profile who replacement)
  linarith

/-- A strict global maximum of an exact potential is a strict Nash profile. -/
theorem IsExactPotential.isStrictNash_of_strict_maximal
    (hpotential : IsExactPotential F utility potential) {profile : Profile F.sig}
    (hmax : ∀ other : Profile F.sig, other ≠ profile → potential other < potential profile) :
    IsStrictNash F (euPreference utility) profile := by
  intro who
  refine ⟨⟨(hpotential.integrable profile who).hasExpectation,
    (hpotential.integrable profile who).hasExpectation, le_rfl⟩, ?_⟩
  intro replacement hreplacement
  have hupdate_ne : Profile.update profile who replacement ≠ profile := by
    intro hupdate
    apply hreplacement
    have hcoordinate := congr_fun hupdate who
    simpa using hcoordinate
  have hlt := hmax (Profile.update profile who replacement) hupdate_ne
  have hdiff := hpotential.difference who profile replacement
  apply (euPreference_strict_iff utility who _ _
    (hpotential.integrable profile who)
    (hpotential.integrable (Profile.update profile who replacement) who)).2
  linarith

/-- Every improving step strictly raises an exact potential. -/
theorem IsExactPotential.improvingStep_increases_potential
    (hpotential : IsExactPotential F utility potential) {source target : Profile F.sig}
    (hstep : ImprovingStep F (euPreference utility) source target) :
    potential source < potential target := by
  obtain ⟨who, replacement, htarget, himprove⟩ := hstep
  subst target
  exact hpotential.improving_deviation_increases_potential
    ((euPreference_strict_iff utility who _ _ (hpotential.integrable _ who)
      (hpotential.integrable _ who)).1 himprove)

/-- A finite exact-potential game admits no infinite path of strict unilateral
expected-utility improvements. -/
theorem IsExactPotential.no_infinite_improving_path [Finite (Profile F.sig)]
    (hpotential : IsExactPotential F utility potential) :
    ¬ ∃ path : ℕ → Profile F.sig,
        ∀ n, ImprovingStep F (euPreference utility) (path n) (path (n + 1)) := by
  rintro ⟨path, hstep⟩
  have hincrease : ∀ n, potential (path n) < potential (path (n + 1)) :=
    fun n => hpotential.improvingStep_increases_potential (hstep n)
  have hmono : StrictMono (potential ∘ path) := strictMono_nat_of_lt_succ hincrease
  have hinjective : Function.Injective path := by
    intro left right heq
    have hpotentialEq : potential (path left) = potential (path right) := by rw [heq]
    exact hmono.injective hpotentialEq
  exact not_injective_infinite_finite path hinjective

/-- Every improving step strictly raises an ordinal potential. -/
theorem IsOrdinalPotential.improvingStep_increases_potential
    (hpotential : IsOrdinalPotential F utility potential) {source target : Profile F.sig}
    (hstep : ImprovingStep F (euPreference utility) source target) :
    potential source < potential target := by
  obtain ⟨who, replacement, htarget, himprove⟩ := hstep
  subst target
  exact (hpotential.comparison who source replacement).1
    ((euPreference_strict_iff utility who _ _ (hpotential.integrable _ who)
      (hpotential.integrable _ who)).1 himprove)

/-- An ordinal-potential improving step strictly reduces the number of profiles
whose potential is higher. -/
theorem IsOrdinalPotential.improvingStep_filter_card_lt [Fintype (Profile F.sig)]
    (hpotential : IsOrdinalPotential F utility potential) {source target : Profile F.sig}
    (hstep : ImprovingStep F (euPreference utility) source target) :
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

/-- Strict improvement is well-founded when an ordinal potential takes finitely
many values: each step raises the potential. -/
theorem IsOrdinalPotential.improvement_wellFounded_of_finite_range
    (hpotential : IsOrdinalPotential F utility potential)
    (hrange : (Set.range potential).Finite) :
    WellFounded (fun target source : Profile F.sig =>
      ImprovingStep F (euPreference utility) source target) :=
  improvement_wellFounded_of_improvement_rank potential hrange
    hpotential.improvingStep_increases_potential

/-- In a finite ordinal-potential game, strict improvement is well-founded. -/
theorem IsOrdinalPotential.improvement_wellFounded [Finite (Profile F.sig)]
    (hpotential : IsOrdinalPotential F utility potential) :
    WellFounded (fun target source : Profile F.sig =>
      ImprovingStep F (euPreference utility) source target) :=
  hpotential.improvement_wellFounded_of_finite_range (Set.finite_range potential)

/-- An ordinal-potential game whose potential takes finitely many values is
weakly acyclic. -/
theorem IsOrdinalPotential.weaklyAcyclic_of_finite_range
    (hpotential : IsOrdinalPotential F utility potential)
    (hrange : (Set.range potential).Finite) : WeaklyAcyclic F (euPreference utility) :=
  weaklyAcyclic_of_improvement_rank hpotential.deviation_comparable potential hrange
    hpotential.improvingStep_increases_potential

/-- Every finite ordinal-potential game is weakly acyclic. -/
theorem IsOrdinalPotential.weaklyAcyclic [Finite (Profile F.sig)]
    (hpotential : IsOrdinalPotential F utility potential) :
    WeaklyAcyclic F (euPreference utility) :=
  hpotential.weaklyAcyclic_of_finite_range (Set.finite_range potential)

/-- The exact-potential special case of ordinal-potential weak acyclicity. -/
theorem IsExactPotential.weaklyAcyclic [Finite (Profile F.sig)]
    (hpotential : IsExactPotential F utility potential) : WeaklyAcyclic F (euPreference utility) :=
  hpotential.isOrdinalPotential.weaklyAcyclic

/-! ## Team games

Identical outcome utilities imply identical expected utilities at every law.
That gives a potential for free and records the one degenerate overlap with
zero-sum games. -/

/-- Every team game is an exact potential game, using any player's expected
utility as the common potential. -/
theorem IsTeamGame.isExactPotential (hteam : IsTeamGame utility) (anchor : ι)
    (hintegrable : ∀ profile : Profile F.sig,
      UtilityIntegrable utility anchor (F.play profile)) :
    IsExactPotential F utility
      (fun profile =>
        expectedUtility utility anchor (F.play profile)) := by
  refine ⟨?_, ?_⟩
  · intro profile who
    exact payoffIntegrable_congr_on_support
      (fun outcome _ => (hteam outcome who anchor).symm) (hintegrable profile)
  intro who profile replacement
  rw [hteam.expectedUtility_eq (F.play profile) who anchor,
    hteam.expectedUtility_eq (F.play (Profile.update profile who replacement)) who anchor]

/-- In a team game, Nash is exactly local maximality of any anchor player's
expected utility. -/
theorem IsTeamGame.isNash_iff_local_potential_maximal
    (hteam : IsTeamGame utility) (anchor : ι)
    (hintegrable : ∀ profile : Profile F.sig,
      UtilityIntegrable utility anchor (F.play profile))
    (profile : Profile F.sig) :
    IsNash F (euPreference utility) profile ↔
      ∀ who replacement,
        expectedUtility utility anchor
          (F.play (Profile.update profile who replacement)) ≤
        expectedUtility utility anchor (F.play profile) :=
  (hteam.isExactPotential anchor hintegrable).isNash_iff_local_maximal

end GameTheory
