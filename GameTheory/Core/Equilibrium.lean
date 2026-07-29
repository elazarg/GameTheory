/-
# The standard equilibrium concepts

Every concept in this file is a choice of status quo and deviation scheme for
the single predicate `IsEquilibrium`. None of them is a new logical definition,
and none of them mentions expected utility: the preference stays an explicit
argument.

| Concept | Status quo | Units | Deviations |
|---|---|---|---|
| pure Nash | `pure σ` | players | constant unilateral replacements |
| mixed Nash | `pure σ` in `F.mixed` | players | replacement mixed strategies |
| CCE | arbitrary profile law | players | constant unilateral replacements |
| CE | arbitrary profile law | players | recommendation-dependent maps |
| strong Nash | `pure σ` | nonempty coalitions | joint member replacements |

Mixed Nash is `IsNash F.mixed`, not a separate predicate.
-/

import GameTheory.Core.Deviation

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

variable {ι : Type uι} {sig : GameSignature ι}

namespace DeviationScheme

/-- Constant unilateral replacements: the Nash and CCE family. -/
def unilateralConstant (sig : GameSignature ι) : DeviationScheme sig ι where
  members who := {who}
  Dev who := sig.Strategy who
  actLocal who replacement _ := FinDist.pure (Subprofile.single who replacement)

/-- Recommendation-dependent unilateral maps: Aumann's correlated family. The
deviation's only input is the deviator's own recommendation. -/
def recommendation (sig : GameSignature ι) : DeviationScheme sig ι where
  members who := {who}
  Dev who := sig.Strategy who → sig.Strategy who
  actLocal who respond own :=
    FinDist.pure (Subprofile.single who (respond (own ⟨who, Finset.mem_singleton_self who⟩)))

/-- Randomized unilateral replacements. -/
def unilateralRandomized (sig : GameSignature ι) : DeviationScheme sig ι where
  members who := {who}
  Dev who := FinDist (sig.Strategy who)
  actLocal who replacement _ := replacement.map (Subprofile.single who)

/-- Joint replacements available to a nonempty coalition. -/
def coalitionConstant (sig : GameSignature ι) :
    DeviationScheme sig { members : Finset ι // members.Nonempty } where
  members coalition := coalition.1
  Dev coalition := Subprofile sig coalition.1
  actLocal _ replacement _ := FinDist.pure replacement

section Projections

@[simp] theorem unilateralConstant_members (sig : GameSignature ι) (who : ι) :
    (unilateralConstant sig).members who = {who} := rfl

@[simp] theorem unilateralConstant_Dev (sig : GameSignature ι) (who : ι) :
    (unilateralConstant sig).Dev who = sig.Strategy who := rfl

@[simp] theorem unilateralConstant_actLocal (sig : GameSignature ι) (who : ι)
    (replacement : sig.Strategy who) (own : Subprofile sig {who}) :
    (unilateralConstant sig).actLocal who replacement own =
      FinDist.pure (Subprofile.single who replacement) := rfl

@[simp] theorem recommendation_members (sig : GameSignature ι) (who : ι) :
    (recommendation sig).members who = {who} := rfl

@[simp] theorem recommendation_Dev (sig : GameSignature ι) (who : ι) :
    (recommendation sig).Dev who = (sig.Strategy who → sig.Strategy who) := rfl

@[simp] theorem recommendation_actLocal (sig : GameSignature ι) (who : ι)
    (respond : sig.Strategy who → sig.Strategy who) (own : Subprofile sig {who}) :
    (recommendation sig).actLocal who respond own =
      FinDist.pure
        (Subprofile.single who (respond (own ⟨who, Finset.mem_singleton_self who⟩))) := rfl

@[simp] theorem unilateralRandomized_members (sig : GameSignature ι) (who : ι) :
    (unilateralRandomized sig).members who = {who} := rfl

@[simp] theorem unilateralRandomized_Dev (sig : GameSignature ι) (who : ι) :
    (unilateralRandomized sig).Dev who = FinDist (sig.Strategy who) := rfl

@[simp] theorem unilateralRandomized_actLocal (sig : GameSignature ι) (who : ι)
    (replacement : FinDist (sig.Strategy who)) (own : Subprofile sig {who}) :
    (unilateralRandomized sig).actLocal who replacement own =
      replacement.map (Subprofile.single who) := rfl

@[simp] theorem coalitionConstant_members (sig : GameSignature ι)
    (coalition : { members : Finset ι // members.Nonempty }) :
    (coalitionConstant sig).members coalition = coalition.1 := rfl

@[simp] theorem coalitionConstant_Dev (sig : GameSignature ι)
    (coalition : { members : Finset ι // members.Nonempty }) :
    (coalitionConstant sig).Dev coalition = Subprofile sig coalition.1 := rfl

@[simp] theorem coalitionConstant_actLocal (sig : GameSignature ι)
    (coalition : { members : Finset ι // members.Nonempty })
    (replacement : Subprofile sig coalition.1) (own : Subprofile sig coalition.1) :
    (coalitionConstant sig).actLocal coalition replacement own =
      FinDist.pure replacement := rfl

end Projections

section Apply

variable [DecidableEq ι]

@[simp]
theorem unilateralConstant_apply (sig : GameSignature ι) (statusQuo : FinDist (Profile sig))
    (who : ι) (replacement : sig.Strategy who) :
    (unilateralConstant sig).apply statusQuo who replacement =
      statusQuo.map fun profile => Profile.update profile who replacement := by
  simp [apply, FinDist.map_eq_bind]

@[simp]
theorem recommendation_apply (sig : GameSignature ι) (statusQuo : FinDist (Profile sig))
    (who : ι) (respond : sig.Strategy who → sig.Strategy who) :
    (recommendation sig).apply statusQuo who respond =
      statusQuo.map fun profile => Profile.update profile who (respond (profile who)) := by
  simp [apply, FinDist.map_eq_bind]

@[simp]
theorem unilateralRandomized_apply (sig : GameSignature ι) (statusQuo : FinDist (Profile sig))
    (who : ι) (replacement : FinDist (sig.Strategy who)) :
    (unilateralRandomized sig).apply statusQuo who replacement =
      statusQuo.bind fun profile =>
        replacement.map fun s => Profile.update profile who s := by
  simp only [apply, unilateralRandomized_members, unilateralRandomized_actLocal,
    FinDist.map_comp, Function.comp_def, Profile.override_single]

@[simp]
theorem coalitionConstant_apply (sig : GameSignature ι) (statusQuo : FinDist (Profile sig))
    (coalition : { members : Finset ι // members.Nonempty })
    (replacement : Subprofile sig coalition.1) :
    (coalitionConstant sig).apply statusQuo coalition replacement =
      statusQuo.map fun profile => Profile.override coalition.1 replacement profile := by
  simp [apply, FinDist.map_eq_bind]

/-- A constant replacement is the recommendation-independent rewrite. This
morphism is what makes "CE implies CCE" a theorem rather than a second proof. -/
def constantToRecommendation (sig : GameSignature ι) :
    Hom id (unilateralConstant sig) (recommendation sig) where
  map _ replacement := fun _ => replacement
  apply_eq statusQuo who replacement := by simp

/-- A player's constant replacement is the singleton coalition's joint
replacement. -/
def constantToCoalition (sig : GameSignature ι) :
    Hom (fun who => ⟨{who}, Finset.singleton_nonempty who⟩)
      (unilateralConstant sig) (coalitionConstant sig) where
  map who replacement := Subprofile.single who replacement
  apply_eq statusQuo who replacement := by simp

/-- A deterministic replacement is a point-mass randomized replacement. -/
def constantToRandomized (sig : GameSignature ι) :
    Hom id (unilateralConstant sig) (unilateralRandomized sig) where
  map _ replacement := FinDist.pure replacement
  apply_eq statusQuo who replacement := by simp [FinDist.map_eq_bind]

end Apply

end DeviationScheme

/-! ## The five concepts -/

section Concepts

variable [DecidableEq ι] (F : GameForm ι) (weaklyPrefers : WeakPreference ι F.sig.Outcome)

/-- A pure Nash equilibrium: no player prefers a unilateral constant
replacement. -/
def IsNash (profile : Profile F.sig) : Prop :=
  IsEquilibrium F weaklyPrefers (FinDist.pure profile)
    (DeviationScheme.unilateralConstant F.sig)

/-- A coarse correlated equilibrium: the same deviations, but the status quo is
an arbitrary law over profiles. -/
def IsCoarseCorrelatedEq (statusQuo : FinDist (Profile F.sig)) : Prop :=
  IsEquilibrium F weaklyPrefers statusQuo (DeviationScheme.unilateralConstant F.sig)

/-- A correlated equilibrium: deviations may depend on the deviator's own
recommendation. -/
def IsCorrelatedEq (statusQuo : FinDist (Profile F.sig)) : Prop :=
  IsEquilibrium F weaklyPrefers statusQuo (DeviationScheme.recommendation F.sig)

/-- A strong Nash equilibrium: no nonempty coalition has a joint replacement
that every member strictly prefers. -/
def IsStrongNash (profile : Profile F.sig) : Prop :=
  IsEquilibrium F (Preference.coalition weaklyPrefers) (FinDist.pure profile)
    (DeviationScheme.coalitionConstant F.sig)

end Concepts

/-! ## Unfolded characterizations

These say what each concept means in elementary terms. They are the statements
downstream users quote; the definitions above are what makes them one concept. -/

section Characterizations

variable [DecidableEq ι] {F : GameForm ι} {weaklyPrefers : WeakPreference ι F.sig.Outcome}

theorem isNash_iff (profile : Profile F.sig) :
    IsNash F weaklyPrefers profile ↔
      ∀ who replacement,
        weaklyPrefers who (F.play profile)
          (F.play (Profile.update profile who replacement)) := by
  simp [IsNash, IsEquilibrium, GameForm.outcomeLaw]

theorem isCoarseCorrelatedEq_iff (statusQuo : FinDist (Profile F.sig)) :
    IsCoarseCorrelatedEq F weaklyPrefers statusQuo ↔
      ∀ who replacement,
        weaklyPrefers who (F.outcomeLaw statusQuo)
          (statusQuo.bind fun profile =>
            F.play (Profile.update profile who replacement)) := by
  simp [IsCoarseCorrelatedEq, IsEquilibrium, GameForm.outcomeLaw]

theorem isCorrelatedEq_iff (statusQuo : FinDist (Profile F.sig)) :
    IsCorrelatedEq F weaklyPrefers statusQuo ↔
      ∀ who (respond : F.sig.Strategy who → F.sig.Strategy who),
        weaklyPrefers who (F.outcomeLaw statusQuo)
          (statusQuo.bind fun profile =>
            F.play (Profile.update profile who (respond (profile who)))) := by
  simp [IsCorrelatedEq, IsEquilibrium, GameForm.outcomeLaw]

theorem isStrongNash_iff (profile : Profile F.sig) :
    IsStrongNash F weaklyPrefers profile ↔
      ∀ coalition : Finset ι, coalition.Nonempty →
        ∀ replacement : Subprofile F.sig coalition,
          ∃ member ∈ coalition,
            weaklyPrefers member (F.play profile)
              (F.play (Profile.override coalition replacement profile)) := by
  constructor
  · intro h coalition hne replacement
    simpa [GameForm.outcomeLaw] using h ⟨coalition, hne⟩ replacement
  · rintro h ⟨coalition, hne⟩ replacement
    simpa [GameForm.outcomeLaw] using h coalition hne replacement

/-- Aumann's reading of strong Nash — "no nonempty coalition has a joint
replacement that *every* member strictly prefers" — is equivalent to
`IsStrongNash` exactly when the preference is total. `Preference.coalition`
documents why the two readings come apart for a partial preference; expected
utility (`euPreference_total`) is total, so the two agree there. -/
theorem isStrongNash_iff_not_all_gain (htotal : Preference.Total weaklyPrefers)
    (profile : Profile F.sig) :
    IsStrongNash F weaklyPrefers profile ↔
      ∀ coalition : Finset ι, coalition.Nonempty →
        ∀ replacement : Subprofile F.sig coalition,
          ¬ ∀ member ∈ coalition,
            Preference.strict weaklyPrefers member
              (F.play (Profile.override coalition replacement profile))
              (F.play profile) := by
  rw [isStrongNash_iff]
  refine forall_congr' fun coalition => forall_congr' fun hne => forall_congr' fun replacement => ?_
  exact Preference.coalition_iff_not_forall_strict weaklyPrefers htotal ⟨coalition, hne⟩ _ _

end Characterizations

/-! ## Relations between the concepts -/

section Relations

variable [DecidableEq ι] {F : GameForm ι} {weaklyPrefers : WeakPreference ι F.sig.Outcome}

/-- A pure Nash equilibrium is exactly the coarse correlated equilibrium of its
own point mass. The two concepts differ only in the status quo they accept, so
this is definitional rather than a transported proof. -/
theorem isNash_iff_isCoarseCorrelatedEq_pure (profile : Profile F.sig) :
    IsNash F weaklyPrefers profile ↔
      IsCoarseCorrelatedEq F weaklyPrefers (FinDist.pure profile) :=
  Iff.rfl

/-- Correlated equilibrium implies coarse correlated equilibrium, by the
constant-into-recommendation scheme morphism. -/
theorem IsCorrelatedEq.isCoarseCorrelatedEq {statusQuo : FinDist (Profile F.sig)}
    (h : IsCorrelatedEq F weaklyPrefers statusQuo) :
    IsCoarseCorrelatedEq F weaklyPrefers statusQuo :=
  IsEquilibrium.ofHom (DeviationScheme.constantToRecommendation F.sig) h

/-- A strong Nash equilibrium is a Nash equilibrium, by the singleton-coalition
scheme morphism followed by preference weakening. -/
theorem IsStrongNash.isNash {profile : Profile F.sig}
    (h : IsStrongNash F weaklyPrefers profile) : IsNash F weaklyPrefers profile := by
  refine IsEquilibrium.mono (weaker := weaklyPrefers) ?_
    (IsEquilibrium.ofHom (DeviationScheme.constantToCoalition F.sig) h)
  rintro who preferred alternative ⟨member, hmember, hpref⟩
  rwa [Finset.mem_singleton.mp hmember] at hpref

/-! ## Nash sits inside the correlated hierarchy

A pure equilibrium is a correlated equilibrium of its own point mass. Unlike the
coarse case this is not definitional — a correlated deviation may read the
recommendation — but at a point mass there is only one recommendation to read. -/

/-- A pure Nash equilibrium is a correlated equilibrium of its own point mass. -/
theorem IsNash.isCorrelatedEq {profile : Profile F.sig}
    (h : IsNash F weaklyPrefers profile) :
    IsCorrelatedEq F weaklyPrefers (FinDist.pure profile) := by
  rw [isCorrelatedEq_iff]
  intro who respond
  have := (isNash_iff profile).1 h who (respond (profile who))
  simpa [GameForm.outcomeLaw] using this

/-! ## The correlated concepts are convex

Nash equilibria are not closed under mixing — mixing two of them correlates the
players, which is exactly what a Nash profile may not do. The correlated
concepts are, and the reason is visible in their shape: both compare a `bind` of
the status quo against another `bind` of the same status quo, and composition is
affine in the law it composes with.

Convexity of the preference is a hypothesis rather than a fact about weak
preferences; expected utility satisfies it. -/

/-- **Coarse correlated equilibria are closed under mixing.** -/
theorem IsCoarseCorrelatedEq.mix (hconvex : Preference.Convex weaklyPrefers)
    {first second : FinDist (Profile F.sig)} (hfirst : IsCoarseCorrelatedEq F weaklyPrefers first)
    (hsecond : IsCoarseCorrelatedEq F weaklyPrefers second)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    IsCoarseCorrelatedEq F weaklyPrefers (FinDist.mix t h0 h1 first second) := by
  rw [isCoarseCorrelatedEq_iff] at hfirst hsecond ⊢
  intro who replacement
  rw [GameForm.outcomeLaw_mix, FinDist.mix_bind]
  exact hconvex who t h0 h1 _ _ _ _ (hfirst who replacement) (hsecond who replacement)

/-- **And so are correlated equilibria**, by the same argument with the
recommendation-reading deviations. -/
theorem IsCorrelatedEq.mix (hconvex : Preference.Convex weaklyPrefers)
    {first second : FinDist (Profile F.sig)} (hfirst : IsCorrelatedEq F weaklyPrefers first)
    (hsecond : IsCorrelatedEq F weaklyPrefers second)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    IsCorrelatedEq F weaklyPrefers (FinDist.mix t h0 h1 first second) := by
  rw [isCorrelatedEq_iff] at hfirst hsecond ⊢
  intro who respond
  rw [GameForm.outcomeLaw_mix, FinDist.mix_bind]
  exact hconvex who t h0 h1 _ _ _ _ (hfirst who respond) (hsecond who respond)

end Relations

end GameTheory
