/-
# Hostile locality and law-linearity tests

The equilibrium API is supposed to enforce law-linearity and recommendation
locality by construction. These are the tests that would catch it failing to.

Nothing here is a new definition; every statement exercises the public Core API.
-/

import GameTheory.Core

noncomputable section

namespace GameTheory.Tests

open GameTheory GameTheory.Probability

universe uι us uo

variable {ι : Type uι} {sig : GameSignature ι}

/-! ## A CE deviation cannot read another player's recommendation

The strongest form of this test is not "the malicious definition fails to
compile" but "the malicious definition cannot be written": the argument type of
a unilateral `actLocal` is equivalent to the deviator's own strategy. -/

example (who : ι) : Subprofile sig {who} ≃ sig.Strategy who :=
  Subprofile.singletonEquiv who

/-- Concretely: a would-be spy has no way to project a nonmember's coordinate
out of a singleton subprofile, because doing so needs a proof that the spy is
the deviator. -/
example (who spy : ι) (_own : Subprofile sig {who}) (hspy : spy ∈ ({who} : Finset ι)) :
    spy = who :=
  Finset.mem_singleton.mp hspy

/-- The same statement for a coalition: `actLocal` sees the coalition's own
recommendation and nothing else. -/
example (D : DeviationScheme sig ι) (who : ι) (d : D.Dev who) :
    Subprofile sig (D.members who) → FinDist (Subprofile sig (D.members who)) :=
  D.actLocal who d

/-! ## Locality is a congruence, not a side condition -/

/-- Two profiles that agree on the deviating group induce the same law of local
replacements. The proof is `rw`, because the scheme physically cannot depend on
anything else. -/
example (D : DeviationScheme sig ι) (who : ι) (d : D.Dev who)
    (first second : Profile sig)
    (hagree : Profile.restrict (D.members who) first =
      Profile.restrict (D.members who) second) :
    D.actLocal who d (Profile.restrict (D.members who) first) =
      D.actLocal who d (Profile.restrict (D.members who) second) :=
  D.actLocal_local who d hagree

/-- Nonmember coordinates survive into every profile the deviation can
produce. -/
example [DecidableEq ι] (D : DeviationScheme sig ι) (statusQuo : FinDist (Profile sig))
    (who : ι) (d : D.Dev who) (deviated : Profile sig)
    (hmem : deviated ∈ (D.apply statusQuo who d).support) :
    ∃ profile ∈ statusQuo.support, ∀ j ∉ D.members who, deviated j = profile j :=
  D.exists_agree_off_members statusQuo who d hmem

/-! ## Law-linearity

A deviation meets the status-quo law only through `bind`, so it commutes with
mixing the status quo. -/

example [DecidableEq ι] (D : DeviationScheme sig ι) {α : Type*} (μ : FinDist α)
    (f : α → FinDist (Profile sig)) (who : ι) (d : D.Dev who) :
    D.apply (μ.bind f) who d = μ.bind fun a => D.apply (f a) who d :=
  D.apply_bind μ f who d

/-! ## One equilibrium predicate, five concepts

Each of these type-checks against the single `IsEquilibrium` definition. -/

section Concepts

variable [DecidableEq ι] (F : GameForm ι) (weaklyPrefers : WeakPreference ι F.sig.Outcome)

example (profile : Profile F.sig) :
    IsNash F weaklyPrefers profile =
      IsEquilibrium F weaklyPrefers (FinDist.pure profile)
        (DeviationScheme.unilateralConstant F.sig) := rfl

example (statusQuo : FinDist (Profile F.sig)) :
    IsCoarseCorrelatedEq F weaklyPrefers statusQuo =
      IsEquilibrium F weaklyPrefers statusQuo
        (DeviationScheme.unilateralConstant F.sig) := rfl

example (statusQuo : FinDist (Profile F.sig)) :
    IsCorrelatedEq F weaklyPrefers statusQuo =
      IsEquilibrium F weaklyPrefers statusQuo
        (DeviationScheme.recommendation F.sig) := rfl

example (profile : Profile F.sig) :
    IsStrongNash F weaklyPrefers profile =
      IsEquilibrium F (Preference.coalition weaklyPrefers) (FinDist.pure profile)
        (DeviationScheme.coalitionConstant F.sig) := rfl

/-- Mixed Nash is `IsNash` of the mixed extension, not a sixth definition. -/
example [Fintype ι] (mixedProfile : Profile F.sig.mixed) :
    IsNash F.mixed weaklyPrefers mixedProfile =
      IsEquilibrium F.mixed weaklyPrefers (FinDist.pure mixedProfile)
        (DeviationScheme.unilateralConstant F.sig.mixed) := rfl

end Concepts

/-! ## Response concepts are *not* equilibrium instances

They quantify over opponent profiles, and the tests below record that their
statements keep that quantifier explicit. -/

section Response

variable [DecidableEq ι] (F : GameForm ι) (weaklyPrefers : WeakPreference ι F.sig.Outcome)

example (who : ι) (opponents : Profile F.sig) (candidate : F.sig.Strategy who) :
    IsBestResponse F weaklyPrefers who opponents candidate =
      ∀ alternative,
        weaklyPrefers who (F.play (Profile.update opponents who candidate))
          (F.play (Profile.update opponents who alternative)) := rfl

example (who : ι) (preferred alternative : F.sig.Strategy who) :
    WeaklyDominates F weaklyPrefers who preferred alternative =
      ∀ profile : Profile F.sig,
        weaklyPrefers who (F.play (Profile.update profile who preferred))
          (F.play (Profile.update profile who alternative)) := rfl

end Response

end GameTheory.Tests
