/-
# Local, law-linear deviations and the single equilibrium predicate

`DeviationScheme` enforces the two invariants of D5 in its type, not in prose:

* **law-linearity** — a deviation acts on one profile at a time and is lifted to
  profile laws by `bind` in `DeviationScheme.apply`; no field of the scheme sees
  the status-quo law;
* **information locality** — `actLocal` receives only the deviating group's own
  recommendation, of type `Subprofile sig (members who)`. A nonmember's
  recommendation is not in scope, so a deviation that inspects one does not
  typecheck.

`IsEquilibrium` is then the single logical shape "no allowed deviation is
preferred". Best response, dominance, and rationalizability quantify over
opponent profiles instead and live in `GameTheory.Core.Response`; they are
deliberately *not* instances of this predicate.
-/

import GameTheory.Core.Form
import GameTheory.Core.Preference

noncomputable section

namespace GameTheory

open Probability

universe uι us uo ud ud' udv

variable {ι : Type uι} {sig : GameSignature ι}

/-- A family of allowed deviations. Each deviating unit `who` owns a member set
and a type of deviations acting on that group's recommendation alone. -/
structure DeviationScheme (sig : GameSignature ι) (Deviator : Type ud) where
  /-- The coordinates a unit may rewrite. -/
  members : Deviator → Finset ι
  /-- The deviations available to a unit. -/
  Dev : Deviator → Type udv
  /-- How a deviation rewrites the group's own recommendation. The argument type
  contains no nonmember coordinate. -/
  actLocal : ∀ who, Dev who →
    Subprofile sig (members who) → FinDist (Subprofile sig (members who))

namespace DeviationScheme

variable {Deviator : Type ud} {Deviator' : Type ud'}

/-- Two profiles agreeing on the deviating group induce the same law of local
replacements. Locality holds by construction: the statement is a congruence, not
an extra hypothesis on the scheme. -/
theorem actLocal_local (D : DeviationScheme sig Deviator) (who : Deviator) (d : D.Dev who)
    {first second : Profile sig}
    (h : Profile.restrict (D.members who) first = Profile.restrict (D.members who) second) :
    D.actLocal who d (Profile.restrict (D.members who) first) =
      D.actLocal who d (Profile.restrict (D.members who) second) := by
  rw [h]

variable [DecidableEq ι]

/-- Lift a deviation to profile laws. This is the only place where a deviation
meets the status-quo law, and it does so linearly through `bind`. -/
def apply (D : DeviationScheme sig Deviator) (statusQuo : FinDist (Profile sig))
    (who : Deviator) (d : D.Dev who) : FinDist (Profile sig) :=
  statusQuo.bind fun profile =>
    (D.actLocal who d (Profile.restrict (D.members who) profile)).map fun replacement =>
      Profile.override (D.members who) replacement profile

@[simp]
theorem apply_pure (D : DeviationScheme sig Deviator) (profile : Profile sig)
    (who : Deviator) (d : D.Dev who) :
    D.apply (FinDist.pure profile) who d =
      (D.actLocal who d (Profile.restrict (D.members who) profile)).map fun replacement =>
        Profile.override (D.members who) replacement profile :=
  FinDist.pure_bind ..

theorem apply_bind (D : DeviationScheme sig Deviator) {α : Type*} (μ : FinDist α)
    (f : α → FinDist (Profile sig)) (who : Deviator) (d : D.Dev who) :
    D.apply (μ.bind f) who d = μ.bind fun a => D.apply (f a) who d :=
  FinDist.bind_bind ..

/-- Every profile a deviation can produce agrees with some status-quo profile
off the deviating group. Nonmember coordinates are therefore untouched in the
*result*, not merely in the deviation's argument. -/
theorem exists_agree_off_members (D : DeviationScheme sig Deviator)
    (statusQuo : FinDist (Profile sig)) (who : Deviator) (d : D.Dev who)
    {deviated : Profile sig} (hmem : deviated ∈ (D.apply statusQuo who d).support) :
    ∃ profile ∈ statusQuo.support,
      ∀ j ∉ D.members who, deviated j = profile j := by
  simp only [apply, FinDist.support_bind, FinDist.support_map, Set.mem_iUnion,
    Set.mem_image] at hmem
  obtain ⟨profile, hprofile, replacement, -, rfl⟩ := hmem
  exact ⟨profile, hprofile, fun j hj => Profile.override_of_not_mem _ _ _ hj⟩

/-- A map of allowed deviations. `apply_eq` says the target deviation has
exactly the effect of the source deviation, so equilibrium transports without
reopening either scheme. -/
structure Hom (agents : Deviator → Deviator')
    (source : DeviationScheme sig Deviator) (target : DeviationScheme sig Deviator') where
  /-- The corresponding target deviation. -/
  map : ∀ who, source.Dev who → target.Dev (agents who)
  /-- The two deviations act identically on every status-quo law. -/
  apply_eq : ∀ statusQuo who d,
    target.apply statusQuo (agents who) (map who d) = source.apply statusQuo who d

end DeviationScheme

/-- `statusQuo` is an equilibrium of `F` for `weaklyPrefers` against the
deviations of `D`: no unit prefers the law it can reach to the law it has.

This is the library's only equilibrium-of-a-law predicate. Nash, mixed Nash,
CCE, CE, and strong Nash are choices of `statusQuo` and `D`, not new logical
definitions. -/
def IsEquilibrium [DecidableEq ι] {Deviator : Type ud} (F : GameForm ι)
    (weaklyPrefers : WeakPreference Deviator F.sig.Outcome)
    (statusQuo : FinDist (Profile F.sig))
    (D : DeviationScheme F.sig Deviator) : Prop :=
  ∀ who d,
    weaklyPrefers who (F.outcomeLaw statusQuo) (F.outcomeLaw (D.apply statusQuo who d))

namespace IsEquilibrium

variable [DecidableEq ι] {Deviator : Type ud} {Deviator' : Type ud'} {F : GameForm ι}
variable {statusQuo : FinDist (Profile F.sig)}

/-- Equilibrium against a larger deviation scheme implies equilibrium against
any scheme mapping into it. -/
theorem ofHom {agents : Deviator → Deviator'}
    {source : DeviationScheme F.sig Deviator} {target : DeviationScheme F.sig Deviator'}
    (hom : DeviationScheme.Hom agents source target)
    {weaklyPrefers : WeakPreference Deviator' F.sig.Outcome}
    (h : IsEquilibrium F weaklyPrefers statusQuo target) :
    IsEquilibrium F (fun who => weaklyPrefers (agents who)) statusQuo source := by
  intro who d
  have hd := h (agents who) (hom.map who d)
  rwa [hom.apply_eq] at hd

/-- Weakening the preference preserves equilibrium. -/
theorem mono {weaker stronger : WeakPreference Deviator F.sig.Outcome}
    {D : DeviationScheme F.sig Deviator}
    (hpref : Preference.Weaker weaker stronger)
    (h : IsEquilibrium F stronger statusQuo D) :
    IsEquilibrium F weaker statusQuo D :=
  fun who d => hpref _ _ _ (h who d)

end IsEquilibrium

end GameTheory
