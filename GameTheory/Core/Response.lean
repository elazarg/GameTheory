/-
# Best response, dominance, and rationalizability

Equilibrium of a law is one logical shape; these are another. Best response
fixes an opponents' profile, dominance quantifies over *all* profiles, and
rationalizability iterates dominance over shrinking strategy sets. None of them
is an instance of `IsEquilibrium`, and forcing them through it would hide the
quantifier that distinguishes them.

They share `GameForm.play`, the preference, and `Profile.update` with the
equilibrium family, which is what makes the cross-family theorems below short.

Pareto dominance and efficiency close the file: they compare whole profiles
across all players rather than deviations of one unit.
-/

import GameTheory.Core.Equilibrium

noncomputable section

namespace GameTheory

open Probability

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

/-- `preferred` weakly dominates `alternative` for `who`: it is at least as good
at *every* profile. -/
def WeaklyDominates (who : ι) (preferred alternative : F.sig.Strategy who) : Prop :=
  ∀ profile : Profile F.sig,
    weaklyPrefers who (F.play (Profile.update profile who preferred))
      (F.play (Profile.update profile who alternative))

/-- `preferred` strictly dominates `alternative` for `who` at every profile
whose coordinates lie in `allowed`.

The constraint covers *every* coordinate, including the deviator's own, even
though `Profile.update` overwrites that coordinate on both sides. This is the
standard presentation of iterated strict dominance and is exactly what the
executable `eliminateRound` computes, so `mem_survivors_iff` is an equality
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
  ∀ alternative, WeaklyDominates F weaklyPrefers who s alternative

/-- Every player plays a dominant strategy. -/
def IsDominantProfile (profile : Profile F.sig) : Prop :=
  ∀ who, IsDominant F weaklyPrefers who (profile who)

/-- The strategy sets surviving `n` rounds of elimination of strictly dominated
strategies. Round zero allows everything. -/
def survivors : ℕ → ∀ j, Set (F.sig.Strategy j)
  | 0, _ => Set.univ
  | n + 1, j =>
    {s | s ∈ survivors n j ∧
      ∀ t ∈ survivors n j, ¬ StrictlyDominatesOn F weaklyPrefers j (survivors n) t s}

/-- The selected rationalizability target: survival of every round of iterated
strict dominance. -/
def IsRationalizable (who : ι) (s : F.sig.Strategy who) : Prop :=
  ∀ round, s ∈ survivors F weaklyPrefers round who

end Definitions

section Theorems

variable [DecidableEq ι] {F : GameForm ι} {weaklyPrefers : WeakPreference ι F.sig.Outcome}

@[simp]
theorem survivors_zero (j : ι) : survivors F weaklyPrefers 0 j = Set.univ := rfl

theorem mem_survivors_succ {round : ℕ} {j : ι} {s : F.sig.Strategy j} :
    s ∈ survivors F weaklyPrefers (round + 1) j ↔
      s ∈ survivors F weaklyPrefers round j ∧
        ∀ t ∈ survivors F weaklyPrefers round j,
          ¬ StrictlyDominatesOn F weaklyPrefers j (survivors F weaklyPrefers round) t s :=
  Iff.rfl

theorem survivors_antitone (round : ℕ) (j : ι) :
    survivors F weaklyPrefers (round + 1) j ⊆ survivors F weaklyPrefers round j :=
  fun _ hs => hs.1

/-- A Nash equilibrium is exactly a profile of mutual best responses. -/
theorem isNash_iff_isBestResponse (profile : Profile F.sig) :
    IsNash F weaklyPrefers profile ↔
      ∀ who, IsBestResponse F weaklyPrefers who profile (profile who) := by
  rw [isNash_iff]
  exact forall_congr' fun who => forall_congr' fun alternative => by
    simp

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

/-- Strict dominance is dominance against every profile, so it restricts to any
allowed set. -/
theorem StrictlyDominates.strictlyDominatesOn {who : ι}
    {preferred alternative : F.sig.Strategy who}
    (h : StrictlyDominates F weaklyPrefers who preferred alternative)
    (allowed : ∀ j, Set (F.sig.Strategy j)) :
    StrictlyDominatesOn F weaklyPrefers who allowed preferred alternative :=
  fun profile _ => h profile (fun _ => Set.mem_univ _)

/-- Every strategy in a Nash equilibrium survives every round of iterated strict
dominance. This is the cross-family theorem that makes rationalizability a
genuine relaxation of Nash rather than an unrelated definition. -/
theorem IsNash.isRationalizable {profile : Profile F.sig}
    (hnash : IsNash F weaklyPrefers profile) (who : ι) :
    IsRationalizable F weaklyPrefers who (profile who) := by
  have key : ∀ round, ∀ j, profile j ∈ survivors F weaklyPrefers round j := by
    intro round
    induction round with
    | zero => intro j; exact Set.mem_univ _
    | succ round ih =>
      intro j
      refine ⟨ih j, fun t _ hdom => ?_⟩
      have hstrict := hdom profile ih
      rw [Profile.update_eq_self] at hstrict
      exact hstrict.2 ((isNash_iff profile).1 hnash j t)
  exact fun round => key round who

/-! ## Elimination eliminates

`survivors` is a definition; the facts below are what make it the *right* one.
A strategy that something available beats strictly is gone after one round, an
unconditionally dominated strategy is never rationalizable at all, and no
equilibrium ever plays one. -/

/-- **One round removes what it should.** If a strategy still available strictly
beats `alternative` across the survivors, `alternative` does not survive the
round. -/
theorem not_mem_survivors_succ_of_strictlyDominatesOn {round : ℕ} {who : ι}
    {preferred alternative : F.sig.Strategy who}
    (hpreferred : preferred ∈ survivors F weaklyPrefers round who)
    (hdom : StrictlyDominatesOn F weaklyPrefers who (survivors F weaklyPrefers round)
      preferred alternative) :
    alternative ∉ survivors F weaklyPrefers (round + 1) who :=
  fun hmem => hmem.2 preferred hpreferred hdom

/-- **A strictly dominated strategy is never rationalizable**, and nothing is
assumed about the strategy that beats it — the first round already allows
everything, so the elimination fires there. -/
theorem StrictlyDominates.not_isRationalizable {who : ι}
    {preferred alternative : F.sig.Strategy who}
    (hdom : StrictlyDominates F weaklyPrefers who preferred alternative) :
    ¬ IsRationalizable F weaklyPrefers who alternative := fun hrat =>
  not_mem_survivors_succ_of_strictlyDominatesOn (round := 0) (Set.mem_univ preferred)
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
  hdom.not_isRationalizable (hnash.isRationalizable who)

/-! ## Dominance orders the strategies

Weak dominance inherits the shape of the preference it is built from: reflexive
when the preference is, transitive when the preference is. Neither is assumed
of a `WeakPreference`, so both are stated as consequences. -/

/-- Weak dominance is reflexive whenever the preference is. -/
theorem weaklyDominates_refl (hrefl : Preference.Reflexive weaklyPrefers) (who : ι)
    (s : F.sig.Strategy who) : WeaklyDominates F weaklyPrefers who s s :=
  fun profile => hrefl who (F.play (Profile.update profile who s))

/-- Weak dominance is transitive whenever the preference is. -/
theorem WeaklyDominates.trans (htrans : Preference.Transitive weaklyPrefers) {who : ι}
    {first middle last : F.sig.Strategy who}
    (hfirst : WeaklyDominates F weaklyPrefers who first middle)
    (hsecond : WeaklyDominates F weaklyPrefers who middle last) :
    WeaklyDominates F weaklyPrefers who first last :=
  fun profile => htrans who _ _ _ (hfirst profile) (hsecond profile)

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

/-- A dominant strategy weakly dominates a dominated one, so dominance and
domination cannot disagree. -/
theorem IsDominant.weaklyDominates {who : ι} {s : F.sig.Strategy who}
    (hdom : IsDominant F weaklyPrefers who s) (alternative : F.sig.Strategy who) :
    WeaklyDominates F weaklyPrefers who s alternative := hdom alternative

/-- **A dominant strategy is never strictly dominated.** A witness profile is
needed and not a technicality: with no profile at all, strict dominance is
vacuous and every strategy is dominated by every other. -/
theorem IsDominant.not_strictlyDominated {who : ι} {s preferred : F.sig.Strategy who}
    (hdom : IsDominant F weaklyPrefers who s) (witness : Profile F.sig) :
    ¬ StrictlyDominates F weaklyPrefers who preferred s := fun hstrict =>
  (hstrict witness fun _ => Set.mem_univ _).2 (hdom preferred witness)

/-! ## Pareto comparisons -/

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
theorem ParetoDominates.irrefl (profile : Profile F.sig) :
    ¬ ParetoDominates F weaklyPrefers profile profile := by
  rintro ⟨-, i, hi⟩
  exact Preference.strict_irrefl weaklyPrefers i _ hi

variable (F weaklyPrefers) in
/-- Everyone is strictly better off under `better`. This is the comparison a
coalition of *all* players can act on, which is why it is what an equilibrium
against coalitions rules out — Pareto domination proper, which lets some players
be indifferent, is a strictly stronger demand and is not ruled out. -/
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
