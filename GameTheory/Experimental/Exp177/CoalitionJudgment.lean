module

/-
EXP-177: strict unanimity and positive weak rejection remain distinct.
Fixed nonempty coalitions inherit strict transitivity, but their no-strict-gain
comparison need not be transitive. Totality connects it to the existing weak
coalition lift; partial preferences separate the resulting equilibrium verdicts.
-/

public import GameTheory.Core.Equilibrium

@[expose] public section

noncomputable section

namespace GameTheory.Experimental.CoalitionJudgment

open GameTheory.Math.Probability

universe ua uα uι us uo

/-- Fixed nonempty coalition members all strictly prefer the first outcome. -/
def allStrict {Agent : Type ua} {α : Type uα} (r : Ranking Agent α)
    (members : {s : Finset Agent // s.Nonempty}) (preferred alternative : α) : Prop :=
  ∀ agent ∈ members.1, Preference.strict r agent preferred alternative

theorem allStrict_irreflexive {Agent : Type ua} {α : Type uα} (r : Ranking Agent α)
    (members : {s : Finset Agent // s.Nonempty}) :
    ∀ outcome, ¬ allStrict r members outcome outcome := by
  intro outcome hall
  obtain ⟨agent, hmember⟩ := members.2
  exact Rank.strict_irrefl (r agent) outcome (hall agent hmember)

theorem allStrict_transitive {Agent : Type ua} {α : Type uα} {r : Ranking Agent α}
    (htrans : Preference.Transitive r) (members : {s : Finset Agent // s.Nonempty}) :
    Rank.Transitive (allStrict r members) := by
  intro preferred middle alternative hfirst hsecond agent hmember
  exact Rank.strict_trans (htrans agent) (hfirst agent hmember)
    (hsecond agent hmember).1

/-- This lawless coalition relation records the absence of strict unanimity.
Specializing `α` to outcome laws supplies an equilibrium preference. -/
def noStrictGainPreference {Agent : Type ua} {α : Type uα} (r : Ranking Agent α) :
    Ranking {s : Finset Agent // s.Nonempty} α :=
  fun members stay deviation => ¬ allStrict r members deviation stay

/-- Under totality the existing coalition aggregation has exactly this
meaning. Without totality, replacing it would change equilibrium semantics. -/
theorem noStrictGainPreference_eq_coalition
    {Agent : Type ua} {α : Type uα} (r : Ranking Agent α)
    (htotal : Preference.Total r) :
    noStrictGainPreference r = Preference.coalition r := by
  funext members preferred alternative
  exact propext (Preference.coalition_iff_not_forall_strict
    r htotal members preferred alternative).symm

theorem isEquilibrium_noStrictGain_iff_strongNash
    {ι : Type uι} [DecidableEq ι] (F : GameForm.{uι, us, uo} ι)
    (prefers : WeakPreference ι F.sig.Outcome) (htotal : Preference.Total prefers)
    (profile : Profile F.sig) :
    IsEquilibrium F (noStrictGainPreference prefers) (PMF.pure profile)
        (DeviationScheme.coalitionConstant F.sig) ↔ IsStrongNash F prefers profile := by
  rw [noStrictGainPreference_eq_coalition prefers htotal]
  rfl

/-- Both individuals rank these three outcomes numerically and hence totally. -/
def threeValue (agent : Bool) (outcome : Fin 3) : ℕ :=
  if agent then (if outcome = 0 then 2 else if outcome = 1 then 0 else 1)
  else (if outcome = 0 then 2 else if outcome = 1 then 3 else 1)

def numericalRanking : Ranking Bool (Fin 3) :=
  fun agent preferred alternative => threeValue agent alternative ≤ threeValue agent preferred

theorem numericalRanking_total : Preference.Total numericalRanking := by
  intro agent preferred alternative
  exact le_total (threeValue agent alternative) (threeValue agent preferred)

theorem numericalRanking_transitive : Preference.Transitive numericalRanking := by
  intro agent preferred middle alternative hfirst hsecond
  exact le_trans hsecond hfirst

def bothAgents : {s : Finset Bool // s.Nonempty} :=
  ⟨Finset.univ, Finset.univ_nonempty⟩

/-- Absence of a strict coalition gain is not transitive even when every
individual relation is a total preorder. The coalition remains fixed. -/
theorem noStrictGainPreference_not_transitive :
    ¬ Rank.Transitive (noStrictGainPreference numericalRanking bothAgents) := by
  intro htrans
  have first : noStrictGainPreference numericalRanking bothAgents (2 : Fin 3) 1 := by
    intro hall
    have hmember := (hall true (by simp [bothAgents])).1
    norm_num [numericalRanking, threeValue] at hmember
  have second : noStrictGainPreference numericalRanking bothAgents (1 : Fin 3) 0 := by
    intro hall
    have hmember := (hall false (by simp [bothAgents])).1
    norm_num [numericalRanking, threeValue] at hmember
  have hnone := htrans 2 1 0 first second
  apply hnone
  intro agent _
  cases agent <;> norm_num [Preference.strict, Rank.strict, numericalRanking, threeValue]

@[reducible]
def binarySignature : GameSignature Unit where
  Strategy _ := Bool
  Outcome := Bool

@[reducible]
def binaryForm : GameForm Unit :=
  GameForm.deterministic binarySignature fun profile => profile ()

def falseProfile : Profile binarySignature := fun _ => false

def equalityPreference : WeakPreference Unit Bool :=
  fun _ preferred alternative => preferred = alternative

/-- Equality admits no strict preference, so the single equilibrium engine
accepts every coalition replacement under the no-strict-gain relation. -/
theorem equality_noStrictGain_equilibrium :
    IsEquilibrium binaryForm (noStrictGainPreference equalityPreference)
      (PMF.pure falseProfile) (DeviationScheme.coalitionConstant binarySignature) := by
  intro members replacement hall
  obtain ⟨agent, hmember⟩ := members.2
  have hstrict := hall agent hmember
  exact hstrict.2 hstrict.1.symm

/-- The same profile fails the canonical weak-form strong Nash predicate:
the singleton coalition can change its outcome to a distinct incomparable law. -/
theorem equality_not_strongNash : ¬ IsStrongNash binaryForm equalityPreference falseProfile := by
  intro hstrong
  obtain ⟨agent, _, hcomparison⟩ :=
    (isStrongNash_iff (F := binaryForm) (weaklyPrefers := equalityPreference)
      falseProfile).1 hstrong {()} (by simp)
      (Subprofile.single (sig := binarySignature) () true)
  cases agent
  have hfalse : (PMF.pure false : PMF Bool) = PMF.pure true := by
    simpa [equalityPreference, binaryForm, falseProfile, Profile.override_single,
      Profile.update_same] using hcomparison
  have hmass := congrArg (fun law : PMF Bool => law true) hfalse
  norm_num at hmass

/-- Universal strict unanimity over an empty coalition is vacuous, including
when the two compared outcomes coincide. -/
theorem empty_coalition_all_strict {Agent : Type ua} {α : Type uα}
    (r : Ranking Agent α) (preferred alternative : α) :
    ∀ agent ∈ (∅ : Finset Agent), Preference.strict r agent preferred alternative := by
  simp

theorem nonempty_coalition_ne_empty {Agent : Type ua}
    (members : {s : Finset Agent // s.Nonempty}) : members.1 ≠ ∅ :=
  Finset.nonempty_iff_ne_empty.mp members.2

end GameTheory.Experimental.CoalitionJudgment
