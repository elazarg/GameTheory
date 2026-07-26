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

end Theorems

end GameTheory
