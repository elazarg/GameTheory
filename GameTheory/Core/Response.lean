/-
# Best response, dominance, and pure rationalizability

Equilibrium of a law is one logical shape; these are another. Best response
fixes an opponents' profile, dominance quantifies over *all* profiles, and
pure rationalizability iterates dominance over shrinking strategy sets. None of them
is an instance of `IsEquilibrium`, and forcing them through it would hide the
quantifier that distinguishes them.

They share `GameForm.play`, the preference, and `Profile.update` with the
equilibrium family, which is what makes the cross-family theorems below short.

Pareto dominance and efficiency close the file: they compare whole profiles
across all players rather than deviations of one unit.  Profile individual
rationality compares those same canonical expected utilities with an explicit
reservation vector.
-/

import GameTheory.Core.Utility

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι}

section Definitions

variable [DecidableEq ι] (F : GameForm ι) (weaklyPrefers : WeakPreference ι F.sig.Outcome)

/-- `candidate` is a best response for `who` while `opponents` stays fixed. -/
def IsBestResponse (who : ι) (opponents : Profile F.sig)
    (candidate : F.sig.Strategy who) : Prop :=
  ∀ alternative,
    weaklyPrefers who (F.play (Profile.update opponents who candidate))
      (F.play (Profile.update opponents who alternative))

/-- `preferred` very weakly dominates `alternative` for `who`: it is at least
as good at every profile. This reflexive comparison is the one used to define
a dominant strategy. -/
def VeryWeaklyDominates (who : ι)
    (preferred alternative : F.sig.Strategy who) : Prop :=
  ∀ profile : Profile F.sig,
    weaklyPrefers who (F.play (Profile.update profile who preferred))
      (F.play (Profile.update profile who alternative))

/-- Textbook weak dominance: `preferred` is at least as good everywhere and
strictly better at some profile. Unlike `VeryWeaklyDominates`, this relation is
irreflexive for reflexive preferences. -/
def WeaklyDominates (who : ι)
    (preferred alternative : F.sig.Strategy who) : Prop :=
  VeryWeaklyDominates F weaklyPrefers who preferred alternative ∧
    ∃ profile : Profile F.sig,
      Preference.strict weaklyPrefers who
        (F.play (Profile.update profile who preferred))
        (F.play (Profile.update profile who alternative))

/-- A strategy is weakly undominated when no alternative weakly dominates it
in the textbook sense of being weakly better everywhere and strictly better
somewhere. -/
def IsWeaklyUndominated (who : ι) (strategy : F.sig.Strategy who) : Prop :=
  ∀ alternative, ¬ WeaklyDominates F weaklyPrefers who alternative strategy

/-- Every coordinate of a profile is weakly undominated. -/
def IsWeaklyUndominatedProfile (profile : Profile F.sig) : Prop :=
  ∀ who, IsWeaklyUndominated F weaklyPrefers who (profile who)

/-- `preferred` strictly dominates `alternative` for `who` at every profile
whose coordinates lie in `allowed`.

The constraint covers *every* coordinate, including the deviator's own, even
though `Profile.update` overwrites that coordinate on both sides. This is the
standard presentation of iterated strict dominance and is exactly what the
executable `eliminatePureRound` computes, so `mem_pureSurvivors_iff` is an equality
rather than an approximation. The only observable difference would be a
degenerate round in which some player's allowed set becomes empty while the
strategy carrier is infinite. -/
def StrictlyDominatesOn (who : ι) (allowed : ∀ j, Set (F.sig.Strategy j))
    (preferred alternative : F.sig.Strategy who) : Prop :=
  ∀ profile : Profile F.sig, (∀ j, profile j ∈ allowed j) →
    Preference.strict weaklyPrefers who
      (F.play (Profile.update profile who preferred))
      (F.play (Profile.update profile who alternative))

/-- Unrestricted strict dominance is the `allowed = univ` specialization. -/
def StrictlyDominates (who : ι) (preferred alternative : F.sig.Strategy who) : Prop :=
  StrictlyDominatesOn F weaklyPrefers who (fun _ => Set.univ) preferred alternative

/-- `s` is dominant for `who`: it weakly dominates every alternative. -/
def IsDominant (who : ι) (s : F.sig.Strategy who) : Prop :=
  ∀ alternative, VeryWeaklyDominates F weaklyPrefers who s alternative

/-- `s` is strictly dominant for `who`: it strictly dominates every distinct
alternative.  Reflexivity of the weak preference is intentionally not stored;
it is requested only when strict dominance is weakened to ordinary
dominance. -/
def IsStrictDominant (who : ι) (s : F.sig.Strategy who) : Prop :=
  ∀ alternative, alternative ≠ s →
    StrictlyDominates F weaklyPrefers who s alternative

/-- Every player plays a dominant strategy. -/
def IsDominantProfile (profile : Profile F.sig) : Prop :=
  ∀ who, IsDominant F weaklyPrefers who (profile who)

/-- A game is dominant-strategy solvable when every player has a strictly
dominant strategy.  This is the strong, one-round notion; iterated dominance
solvability remains a separate property of the survivor sequence. -/
def IsDominantStrategySolvable : Prop :=
  ∀ who, ∃ strategy, IsStrictDominant F weaklyPrefers who strategy

/-- The strategy sets surviving `n` rounds of elimination by pure strictly
dominating strategies. Round zero allows everything. -/
def pureSurvivors : ℕ → ∀ j, Set (F.sig.Strategy j)
  | 0, _ => Set.univ
  | n + 1, j =>
    {s | s ∈ pureSurvivors n j ∧
      ∀ t ∈ pureSurvivors n j,
        ¬ StrictlyDominatesOn F weaklyPrefers j (pureSurvivors n) t s}

/-- Survival of every round of elimination by pure strict dominators.
This is named for the elimination procedure rather than “rationalizability”:
the standard epistemic notions use mixed dominators or best responses to
beliefs and are distinct. -/
def SurvivesAllPureEliminationRounds (who : ι)
    (s : F.sig.Strategy who) : Prop :=
  ∀ round, s ∈ pureSurvivors F weaklyPrefers round who

/-- A strict expected-utility Nash equilibrium: every genuine unilateral
replacement strictly lowers the deviator's expected utility. -/
def IsStrictNash (F : GameForm ι) (utility : F.sig.Outcome → ι → ℝ)
    (profile : Profile F.sig) : Prop :=
  ∀ who replacement, replacement ≠ profile who →
    expectedUtility utility who (F.play (Profile.update profile who replacement)) <
      expectedUtility utility who (F.play profile)

/-- A strict unilateral expected-utility improvement from `source` to `target`.
The target equation keeps the relation tied to the canonical profile operation. -/
def ImprovingStep (F : GameForm ι) (utility : F.sig.Outcome → ι → ℝ)
    (source target : Profile F.sig) : Prop :=
  ∃ who replacement,
    target = Profile.update source who replacement ∧
      expectedUtility utility who (F.play source) < expectedUtility utility who (F.play target)

/-- From every profile, some finite path of strict unilateral improvements
reaches a Nash profile. This is a response-graph property; potential functions
are one sufficient certificate, not its semantic owner. -/
def WeaklyAcyclic (F : GameForm ι) (utility : F.sig.Outcome → ι → ℝ) : Prop :=
  ∀ source, ∃ target,
    Relation.ReflTransGen (ImprovingStep F utility) source target ∧
      IsNash F (euPreference utility) target

end Definitions

section Theorems

variable [DecidableEq ι] {F : GameForm ι} {weaklyPrefers : WeakPreference ι F.sig.Outcome}

@[simp]
theorem pureSurvivors_zero (j : ι) :
    pureSurvivors F weaklyPrefers 0 j = Set.univ :=
  rfl

theorem mem_pureSurvivors_succ {round : ℕ} {j : ι} {s : F.sig.Strategy j} :
    s ∈ pureSurvivors F weaklyPrefers (round + 1) j ↔
      s ∈ pureSurvivors F weaklyPrefers round j ∧
        ∀ t ∈ pureSurvivors F weaklyPrefers round j,
          ¬ StrictlyDominatesOn F weaklyPrefers j
            (pureSurvivors F weaklyPrefers round) t s :=
  Iff.rfl

theorem pureSurvivors_antitone (round : ℕ) (j : ι) :
    pureSurvivors F weaklyPrefers (round + 1) j ⊆
      pureSurvivors F weaklyPrefers round j :=
  fun _ hs => hs.1

theorem mem_pureSurvivors_of_le {earlier later : ℕ} (hround : earlier ≤ later)
    {j : ι} {strategy : F.sig.Strategy j}
    (h : strategy ∈ pureSurvivors F weaklyPrefers later j) :
    strategy ∈ pureSurvivors F weaklyPrefers earlier j := by
  induction hround with
  | refl => exact h
  | step _ ih => exact ih h.1

/-- Failure of expected-utility Nash exhibits an improving step. -/
theorem not_isNash_iff_exists_improvingStep {F : GameForm ι}
    {utility : F.sig.Outcome → ι → ℝ} {profile : Profile F.sig} :
    ¬ IsNash F (euPreference utility) profile ↔
      ∃ target, ImprovingStep F utility profile target := by
  constructor
  · intro hnash
    rw [isNash_iff] at hnash
    push Not at hnash
    obtain ⟨who, replacement, hnot⟩ := hnash
    refine ⟨Profile.update profile who replacement, who, replacement, rfl, ?_⟩
    exact lt_of_not_ge hnot
  · rintro ⟨target, who, replacement, htarget, himprove⟩ hnash
    subst target
    exact (not_lt_of_ge ((isNash_iff profile).1 hnash who replacement)) himprove

/-- A Nash equilibrium is exactly a profile of mutual best responses. -/
theorem isNash_iff_isBestResponse (profile : Profile F.sig) :
    IsNash F weaklyPrefers profile ↔
      ∀ who, IsBestResponse F weaklyPrefers who profile (profile who) := by
  rw [isNash_iff]
  exact forall_congr' fun who => forall_congr' fun alternative => by
    simp

/-- A strategy that is never a best response cannot occur in a Nash
equilibrium. -/
theorem not_in_nash_of_not_isBestResponse {who : ι}
    (strategy : F.sig.Strategy who)
    (hnever : ∀ opponents : Profile F.sig,
      ¬ IsBestResponse F weaklyPrefers who opponents strategy)
    {profile : Profile F.sig} (hnash : IsNash F weaklyPrefers profile) :
    profile who ≠ strategy := by
  intro heq
  apply hnever profile
  simpa [heq] using (isNash_iff_isBestResponse profile).1 hnash who

/-- A strategy strictly dominating the current choice refutes Nash. -/
theorem StrictlyDominates.not_isNash {who : ι}
    {preferred : F.sig.Strategy who} {profile : Profile F.sig}
    (hdom : StrictlyDominates F weaklyPrefers who preferred (profile who)) :
    ¬ IsNash F weaklyPrefers profile := by
  intro hnash
  exact (hdom profile (fun _ => Set.mem_univ _)).2
    (by simpa using (isNash_iff profile).1 hnash who preferred)

/-- A strictly dominant strategy is the unique best response at every
opponents' profile. -/
theorem IsStrictDominant.eq_of_isBestResponse {who : ι}
    {strict : F.sig.Strategy who}
    (hstrict : IsStrictDominant F weaklyPrefers who strict)
    (opponents : Profile F.sig) {candidate : F.sig.Strategy who}
    (hbest : IsBestResponse F weaklyPrefers who opponents candidate) :
    candidate = strict := by
  by_contra hne
  exact (hstrict candidate hne opponents (fun _ => Set.mem_univ _)).2
    (hbest strict)

/-- With reflexive preferences, strict dominance implies weak dominance. -/
theorem IsStrictDominant.toDominant
    (hrefl : Preference.Reflexive weaklyPrefers) {who : ι}
    {strategy : F.sig.Strategy who}
    (hstrict : IsStrictDominant F weaklyPrefers who strategy) :
    IsDominant F weaklyPrefers who strategy := by
  intro alternative profile
  by_cases heq : alternative = strategy
  · subst alternative
    exact hrefl who _
  · exact (hstrict alternative heq profile (fun _ => Set.mem_univ _)).1

/-- Strict dominance implies textbook weak dominance whenever a profile is
available to witness strict improvement. -/
theorem StrictlyDominates.toWeaklyDominates {who : ι}
    {preferred alternative : F.sig.Strategy who}
    (hstrict : StrictlyDominates F weaklyPrefers who preferred alternative)
    (witness : Profile F.sig) :
    WeaklyDominates F weaklyPrefers who preferred alternative :=
  ⟨fun profile => (hstrict profile (fun _ => Set.mem_univ _)).1,
    ⟨witness, hstrict witness (fun _ => Set.mem_univ _)⟩⟩

/-- A very weakly dominating strategy inherits best-response status when the
preference is transitive. -/
theorem VeryWeaklyDominates.isBestResponse_of_isBestResponse
    (htrans : Preference.Transitive weaklyPrefers) {who : ι}
    {preferred alternative : F.sig.Strategy who}
    (hdom : VeryWeaklyDominates F weaklyPrefers who preferred alternative)
    (opponents : Profile F.sig)
    (hbest : IsBestResponse F weaklyPrefers who opponents alternative) :
    IsBestResponse F weaklyPrefers who opponents preferred := by
  intro candidate
  exact htrans who _ _ _ (hdom opponents) (hbest candidate)

/-- Textbook weak dominance has the same best-response inheritance through
its everywhere-weak projection. -/
theorem WeaklyDominates.isBestResponse_of_isBestResponse
    (htrans : Preference.Transitive weaklyPrefers) {who : ι}
    {preferred alternative : F.sig.Strategy who}
    (hdom : WeaklyDominates F weaklyPrefers who preferred alternative)
    (opponents : Profile F.sig)
    (hbest : IsBestResponse F weaklyPrefers who opponents alternative) :
    IsBestResponse F weaklyPrefers who opponents preferred :=
  hdom.1.isBestResponse_of_isBestResponse htrans opponents hbest

/-- A dominant strategy is a best response to every opponents' profile. -/
theorem IsDominant.isBestResponse {who : ι} {s : F.sig.Strategy who}
    (hdom : IsDominant F weaklyPrefers who s) (opponents : Profile F.sig) :
    IsBestResponse F weaklyPrefers who opponents s :=
  fun alternative => hdom alternative opponents

/-- A profile of dominant strategies is a Nash equilibrium. -/
theorem IsDominantProfile.isNash {profile : Profile F.sig}
    (hdom : IsDominantProfile F weaklyPrefers profile) : IsNash F weaklyPrefers profile := by
  rw [isNash_iff]
  intro who replacement
  simpa using hdom who replacement profile

/-- A profile of strictly dominant strategies is Nash. -/
theorem isNash_of_forall_isStrictDominant
    (hrefl : Preference.Reflexive weaklyPrefers) {profile : Profile F.sig}
    (hstrict : ∀ who,
      IsStrictDominant F weaklyPrefers who (profile who)) :
    IsNash F weaklyPrefers profile :=
  IsDominantProfile.isNash (fun who => (hstrict who).toDominant hrefl)

/-- Any Nash profile equals a supplied profile of strictly dominant
strategies. -/
theorem IsNash.eq_of_forall_isStrictDominant
    {profile strictProfile : Profile F.sig}
    (hnash : IsNash F weaklyPrefers profile)
    (hstrict : ∀ who,
      IsStrictDominant F weaklyPrefers who (strictProfile who)) :
    profile = strictProfile := by
  funext who
  exact (hstrict who).eq_of_isBestResponse profile
    ((isNash_iff_isBestResponse profile).1 hnash who)

/-- Select the strictly dominant strategy of every player.  The selector is
proof-only; executable finite search remains in `GameTheory.Finite`. -/
noncomputable def IsDominantStrategySolvable.dominantProfile
    (hsolvable : IsDominantStrategySolvable F weaklyPrefers) : Profile F.sig :=
  fun who => Classical.choose (hsolvable who)

theorem IsDominantStrategySolvable.dominantProfile_isStrictDominant
    (hsolvable : IsDominantStrategySolvable F weaklyPrefers) (who : ι) :
    IsStrictDominant F weaklyPrefers who
      (hsolvable.dominantProfile who) :=
  Classical.choose_spec (hsolvable who)

/-- The selected profile is pointwise dominant when preferences are
reflexive. -/
theorem IsDominantStrategySolvable.dominantProfile_isDominant
    (hsolvable : IsDominantStrategySolvable F weaklyPrefers)
    (hrefl : Preference.Reflexive weaklyPrefers) :
    IsDominantProfile F weaklyPrefers
      hsolvable.dominantProfile :=
  fun who => (hsolvable.dominantProfile_isStrictDominant who).toDominant hrefl

/-- A dominant-strategy-solvable game has the selected Nash profile. -/
theorem IsDominantStrategySolvable.isNash
    (hsolvable : IsDominantStrategySolvable F weaklyPrefers)
    (hrefl : Preference.Reflexive weaklyPrefers) :
    IsNash F weaklyPrefers hsolvable.dominantProfile :=
  (hsolvable.dominantProfile_isDominant hrefl).isNash

/-- Every Nash profile equals the selected strictly dominant profile. -/
theorem IsDominantStrategySolvable.nash_eq_dominantProfile
    (hsolvable : IsDominantStrategySolvable F weaklyPrefers)
    {profile : Profile F.sig} (hnash : IsNash F weaklyPrefers profile) :
    profile = hsolvable.dominantProfile := by
  funext who
  exact (hsolvable.dominantProfile_isStrictDominant who).eq_of_isBestResponse
    profile ((isNash_iff_isBestResponse profile).1 hnash who)

/-- Dominant-strategy solvability gives existence and uniqueness of Nash. -/
theorem IsDominantStrategySolvable.existsUniqueNash
    (hsolvable : IsDominantStrategySolvable F weaklyPrefers)
    (hrefl : Preference.Reflexive weaklyPrefers) :
    ∃! profile : Profile F.sig, IsNash F weaklyPrefers profile :=
  ⟨hsolvable.dominantProfile,
    hsolvable.isNash hrefl,
    fun _ hnash => hsolvable.nash_eq_dominantProfile hnash⟩

/-- Strict dominance is dominance against every profile, so it restricts to any
allowed set. -/
theorem StrictlyDominates.strictlyDominatesOn {who : ι}
    {preferred alternative : F.sig.Strategy who}
    (h : StrictlyDominates F weaklyPrefers who preferred alternative)
    (allowed : ∀ j, Set (F.sig.Strategy j)) :
    StrictlyDominatesOn F weaklyPrefers who allowed preferred alternative :=
  fun profile _ => h profile (fun _ => Set.mem_univ _)

/-- Every strategy in a Nash equilibrium survives every round of elimination
by pure strict dominance. -/
theorem IsNash.survivesPure {profile : Profile F.sig}
    (hnash : IsNash F weaklyPrefers profile) :
    ∀ round j, profile j ∈ pureSurvivors F weaklyPrefers round j := by
  intro round
  induction round with
  | zero => intro j; exact Set.mem_univ _
  | succ round ih =>
    intro j
    refine ⟨ih j, fun t _ hdom => ?_⟩
    have hstrict := hdom profile ih
    rw [Profile.update_eq_self] at hstrict
    exact hstrict.2 ((isNash_iff profile).1 hnash j t)

/-- Every strategy in a Nash equilibrium survives every pure-elimination
round. -/
theorem IsNash.survivesAllPureEliminationRounds {profile : Profile F.sig}
    (hnash : IsNash F weaklyPrefers profile) (who : ι) :
    SurvivesAllPureEliminationRounds F weaklyPrefers who (profile who) :=
  fun round => hnash.survivesPure round who

/-- Every action in a dominant profile survives pure elimination. -/
theorem dominantProfile_survivesPure (profile : Profile F.sig)
    (hdom : IsDominantProfile F weaklyPrefers profile) :
    ∀ round who, profile who ∈ pureSurvivors F weaklyPrefers round who :=
  hdom.isNash.survivesPure

/-- A dominant action survives every pure-elimination round when the other
players can be filled out by dominant actions. -/
theorem IsDominant.survivesAllPureEliminationRounds
    {who : ι} {strategy : F.sig.Strategy who}
    (hdom : IsDominant F weaklyPrefers who strategy)
    (base : Profile F.sig)
    (hother : ∀ player, player ≠ who →
      IsDominant F weaklyPrefers player (base player)) :
    SurvivesAllPureEliminationRounds F weaklyPrefers who strategy := by
  let profile := Profile.update base who strategy
  have hall : IsDominantProfile F weaklyPrefers profile := by
    intro player
    by_cases hplayer : player = who
    · subst player
      simpa [profile] using hdom
    · have hvalue : profile player = base player := by
        simp [profile, hplayer]
      rw [hvalue]
      exact hother player hplayer
  intro round
  have hsurvives := dominantProfile_survivesPure profile hall round who
  simpa [profile] using hsurvives

/-! ## Elimination eliminates

`pureSurvivors` is a definition; the facts below are what make it the *right* one.
A strategy that something available beats strictly is gone after one round,
an unconditionally dominated strategy cannot survive every round, and no
equilibrium ever plays one. -/

/-- **One round removes what it should.** If a strategy still available strictly
beats `alternative` across the survivors, `alternative` does not survive the
round. -/
theorem not_mem_pureSurvivors_succ_of_strictlyDominatesOn
    {round : ℕ} {who : ι}
    {preferred alternative : F.sig.Strategy who}
    (hpreferred : preferred ∈ pureSurvivors F weaklyPrefers round who)
    (hdom : StrictlyDominatesOn F weaklyPrefers who
      (pureSurvivors F weaklyPrefers round) preferred alternative) :
    alternative ∉ pureSurvivors F weaklyPrefers (round + 1) who :=
  fun hmem => hmem.2 preferred hpreferred hdom

/-- **A strictly dominated strategy cannot survive every pure-elimination
round**, and nothing is assumed about the strategy that beats it — the first
round already allows everything, so the elimination fires there. -/
theorem StrictlyDominates.not_survivesAllPureEliminationRounds {who : ι}
    {preferred alternative : F.sig.Strategy who}
    (hdom : StrictlyDominates F weaklyPrefers who preferred alternative) :
    ¬ SurvivesAllPureEliminationRounds F weaklyPrefers who alternative := fun hrat =>
  not_mem_pureSurvivors_succ_of_strictlyDominatesOn (round := 0)
    (Set.mem_univ preferred)
    (hdom.strictlyDominatesOn _) (hrat 1)

/-- **A strictly dominated strategy is never a best response.** Beating it at
every profile beats it at the one the responder faces. -/
theorem StrictlyDominates.not_isBestResponse {who : ι}
    {preferred alternative : F.sig.Strategy who}
    (hdom : StrictlyDominates F weaklyPrefers who preferred alternative)
    (opponents : Profile F.sig) :
    ¬ IsBestResponse F weaklyPrefers who opponents alternative := fun hbest =>
  (hdom opponents fun _ => Set.mem_univ _).2 (hbest preferred)

/-- **No equilibrium plays a strictly dominated strategy.** This is the two
previous families meeting: equilibrium survives elimination, and elimination
removes the dominated. -/
theorem IsNash.not_strictlyDominates {profile : Profile F.sig} {who : ι}
    {preferred : F.sig.Strategy who} (hnash : IsNash F weaklyPrefers profile) :
    ¬ StrictlyDominates F weaklyPrefers who preferred (profile who) := fun hdom =>
  hdom.not_survivesAllPureEliminationRounds
    (hnash.survivesAllPureEliminationRounds who)

/-! ## Dominance orders the strategies

Very weak dominance inherits the reflexive and transitive shape of the
preference it is built from. Textbook weak dominance is not reflexive, but is
transitive when the underlying preference is. -/

/-- Very weak dominance is reflexive whenever the preference is. -/
theorem veryWeaklyDominates_refl (hrefl : Preference.Reflexive weaklyPrefers)
    (who : ι) (s : F.sig.Strategy who) :
    VeryWeaklyDominates F weaklyPrefers who s s :=
  fun profile => hrefl who (F.play (Profile.update profile who s))

/-- Very weak dominance is transitive whenever the preference is. -/
theorem VeryWeaklyDominates.trans
    (htrans : Preference.Transitive weaklyPrefers) {who : ι}
    {first middle last : F.sig.Strategy who}
    (hfirst : VeryWeaklyDominates F weaklyPrefers who first middle)
    (hsecond : VeryWeaklyDominates F weaklyPrefers who middle last) :
    VeryWeaklyDominates F weaklyPrefers who first last :=
  fun profile => htrans who _ _ _ (hfirst profile) (hsecond profile)

/-- Textbook weak dominance is transitive for a transitive preference. -/
theorem WeaklyDominates.trans
    (htrans : Preference.Transitive weaklyPrefers) {who : ι}
    {first middle last : F.sig.Strategy who}
    (hfirst : WeaklyDominates F weaklyPrefers who first middle)
    (hsecond : WeaklyDominates F weaklyPrefers who middle last) :
    WeaklyDominates F weaklyPrefers who first last := by
  refine ⟨hfirst.1.trans htrans hsecond.1, ?_⟩
  obtain ⟨profile, hstrict⟩ := hfirst.2
  refine ⟨profile, htrans who _ _ _ hstrict.1 (hsecond.1 profile), ?_⟩
  intro hback
  exact hstrict.2 (htrans who _ _ _ (hsecond.1 profile) hback)

/-- Strict dominance on an allowed set is transitive whenever the preference is,
and the middle strategy need not be allowed. -/
theorem StrictlyDominatesOn.trans (htrans : Preference.Transitive weaklyPrefers) {who : ι}
    {allowed : ∀ j, Set (F.sig.Strategy j)} {first middle last : F.sig.Strategy who}
    (hfirst : StrictlyDominatesOn F weaklyPrefers who allowed first middle)
    (hsecond : StrictlyDominatesOn F weaklyPrefers who allowed middle last) :
    StrictlyDominatesOn F weaklyPrefers who allowed first last := by
  intro profile hprofile
  refine ⟨htrans who _ _ _ (hfirst profile hprofile).1 (hsecond profile hprofile).1, ?_⟩
  intro hback
  exact (hfirst profile hprofile).2
    (htrans who _ _ _ (hsecond profile hprofile).1 hback)

/-- A dominant strategy very weakly dominates every alternative. -/
theorem IsDominant.veryWeaklyDominates {who : ι} {s : F.sig.Strategy who}
    (hdom : IsDominant F weaklyPrefers who s) (alternative : F.sig.Strategy who) :
    VeryWeaklyDominates F weaklyPrefers who s alternative := hdom alternative

/-- **A dominant strategy is never strictly dominated.** A witness profile is
needed and not a technicality: with no profile at all, strict dominance is
vacuous and every strategy is dominated by every other. -/
theorem IsDominant.not_strictlyDominated {who : ι} {s preferred : F.sig.Strategy who}
    (hdom : IsDominant F weaklyPrefers who s) (witness : Profile F.sig) :
    ¬ StrictlyDominates F weaklyPrefers who preferred s := fun hstrict =>
  (hstrict witness fun _ => Set.mem_univ _).2 (hdom preferred witness)

/-! ## Pareto comparisons -/

variable (F) in
/-- A profile is individually rational relative to an explicit reservation
utility when every player's canonical expected utility reaches that player's
reservation level. -/
def IsIndividuallyRational (utility : F.sig.Outcome → ι → ℝ)
    (reservation : ι → ℝ) (profile : Profile F.sig) : Prop :=
  ∀ player, reservation player ≤ expectedUtility utility player (F.play profile)

variable (F weaklyPrefers) in
/-- `better` Pareto-dominates `worse`: nobody is worse off and somebody is
strictly better off. -/
def ParetoDominates (better worse : Profile F.sig) : Prop :=
  (∀ i, weaklyPrefers i (F.play better) (F.play worse)) ∧
    ∃ i, Preference.strict weaklyPrefers i (F.play better) (F.play worse)

variable (F weaklyPrefers) in
/-- No profile Pareto-dominates `profile`. -/
def IsParetoEfficient (profile : Profile F.sig) : Prop :=
  ¬ ∃ other, ParetoDominates F weaklyPrefers other profile

omit [DecidableEq ι] in
/-- Weakening every reservation level preserves individual rationality. -/
theorem IsIndividuallyRational.mono {utility : F.sig.Outcome → ι → ℝ}
    {reservation reservation' : ι → ℝ} {profile : Profile F.sig}
    (hir : IsIndividuallyRational F utility reservation profile)
    (hle : ∀ player, reservation' player ≤ reservation player) :
    IsIndividuallyRational F utility reservation' profile :=
  fun player => (hle player).trans (hir player)

omit [DecidableEq ι] in
/-- A Pareto improvement preserves individual rationality. -/
theorem IsIndividuallyRational.of_paretoDominates
    {utility : F.sig.Outcome → ι → ℝ} {reservation : ι → ℝ}
    {better worse : Profile F.sig}
    (hdom : ParetoDominates F (euPreference utility) better worse)
    (hir : IsIndividuallyRational F utility reservation worse) :
    IsIndividuallyRational F utility reservation better :=
  fun player => (hir player).trans (hdom.1 player)

omit [DecidableEq ι] in
/-- Meeting two reservation vectors implies meeting their pointwise maximum. -/
theorem IsIndividuallyRational.sup {utility : F.sig.Outcome → ι → ℝ}
    {first second : ι → ℝ} {profile : Profile F.sig}
    (hfirst : IsIndividuallyRational F utility first profile)
    (hsecond : IsIndividuallyRational F utility second profile) :
    IsIndividuallyRational F utility
      (fun player => max (first player) (second player)) profile :=
  fun player => max_le (hfirst player) (hsecond player)

omit [DecidableEq ι] in
theorem ParetoDominates.irrefl (profile : Profile F.sig) :
    ¬ ParetoDominates F weaklyPrefers profile profile := by
  rintro ⟨-, i, hi⟩
  exact Preference.strict_irrefl weaklyPrefers i _ hi

variable (F weaklyPrefers) in
/-- Everyone is strictly better off under `better`. This is the comparison a
coalition of *all* players can act on, which is why it is what an equilibrium
against coalitions rules out. Pareto domination proper permits some players to
be indifferent, so it is a weaker comparison and can hold even when this one
does not. -/
def StrictlyParetoDominates (better worse : Profile F.sig) : Prop :=
  ∀ i, Preference.strict weaklyPrefers i (F.play better) (F.play worse)

variable (F weaklyPrefers) in
/-- No profile makes everybody strictly better off. -/
def IsWeaklyParetoEfficient (profile : Profile F.sig) : Prop :=
  ¬ ∃ other, StrictlyParetoDominates F weaklyPrefers other profile

omit [DecidableEq ι] in
/-- Making everybody strictly better off is in particular Pareto-dominating,
provided there is somebody. -/
theorem StrictlyParetoDominates.paretoDominates [Nonempty ι] {better worse : Profile F.sig}
    (h : StrictlyParetoDominates F weaklyPrefers better worse) :
    ParetoDominates F weaklyPrefers better worse :=
  ⟨fun i => (h i).1, Classical.arbitrary ι, h _⟩

omit [DecidableEq ι] in
/-- Hence Pareto efficiency is the stronger notion. -/
theorem IsParetoEfficient.isWeaklyParetoEfficient [Nonempty ι] {profile : Profile F.sig}
    (h : IsParetoEfficient F weaklyPrefers profile) :
    IsWeaklyParetoEfficient F weaklyPrefers profile :=
  fun ⟨other, hstrict⟩ => h ⟨other, hstrict.paretoDominates⟩

omit [DecidableEq ι] in
/-- Pareto domination is transitive whenever the preference is. -/
theorem ParetoDominates.trans (htrans : Preference.Transitive weaklyPrefers)
    {first middle last : Profile F.sig}
    (hfirst : ParetoDominates F weaklyPrefers first middle)
    (hsecond : ParetoDominates F weaklyPrefers middle last) :
    ParetoDominates F weaklyPrefers first last := by
  obtain ⟨hweak, agent, hstrict⟩ := hfirst
  refine ⟨fun i => htrans i _ _ _ (hweak i) (hsecond.1 i), agent, ?_, ?_⟩
  · exact htrans agent _ _ _ hstrict.1 (hsecond.1 agent)
  · exact fun hback => hstrict.2 (htrans agent _ _ _ (hsecond.1 agent) hback)

omit [DecidableEq ι] in
/-- And asymmetric whenever the preference is transitive. -/
theorem ParetoDominates.asymm (htrans : Preference.Transitive weaklyPrefers)
    {better worse : Profile F.sig} (h : ParetoDominates F weaklyPrefers better worse) :
    ¬ ParetoDominates F weaklyPrefers worse better := fun hback =>
  ParetoDominates.irrefl better (h.trans htrans hback)

/-- **A strong equilibrium is weakly Pareto efficient.** If some profile made
everybody strictly better off, the coalition of all players could move there
together, and that is exactly the deviation a strong equilibrium forbids.

Only the *weak* form follows, and the reason is visible in the statement: an
equilibrium against coalitions objects when every member gains, while Pareto
domination allows some to be indifferent. -/
theorem IsStrongNash.isWeaklyParetoEfficient [Fintype ι] [Nonempty ι]
    (htotal : Preference.Total weaklyPrefers) {profile : Profile F.sig}
    (hstrong : IsStrongNash F weaklyPrefers profile) :
    IsWeaklyParetoEfficient F weaklyPrefers profile := by
  rintro ⟨other, hstrict⟩
  refine (isStrongNash_iff_not_all_gain htotal profile).1 hstrong Finset.univ
    Finset.univ_nonempty (Profile.restrict Finset.univ other) fun member _ => ?_
  have hall : Profile.override Finset.univ (Profile.restrict Finset.univ other) profile = other :=
    funext fun i => Profile.override_mem Finset.univ _ profile ⟨i, Finset.mem_univ i⟩
  rw [hall]
  exact hstrict member

end Theorems

end GameTheory
