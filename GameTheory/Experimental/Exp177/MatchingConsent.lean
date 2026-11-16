module

/-
EXP-177: responsive blocking separates consent from affected coordinates.
A hospital and newcomer gain by replacing an incumbent who loses his assignment.
In the explicit assignment-coordinate representation, rewriting only the
consenting coordinates cannot realize this valid blocking replacement.
-/

public import GameTheory.Cooperative.Matching.Capacitated
public import GameTheory.Core.Deviation

@[expose] public section

namespace GameTheory.Experimental.MatchingConsent

open MatchingMarket

/-- Optional partners are heterogeneous: doctors rank `Option Unit`, while
this hospital ranks `Option Bool`. -/
def doctorScore : Option Unit → ℕ
  | none => 0
  | some _ => 1

def hospitalScore : Option Bool → ℕ
  | none => 0
  | some false => 1
  | some true => 2

def rankings : MatchingMarket Bool Unit where
  prefersLeft _ preferred alternative := doctorScore alternative ≤ doctorScore preferred
  prefersRight _ preferred alternative := hospitalScore alternative ≤ hospitalScore preferred

def market : CapacitatedMarket Bool Unit := rankings.withCapacities fun _ => 1

/-- Doctor `false` initially occupies the only slot. -/
def source : Matching Bool Unit := fun doctor => if doctor then none else some ()

/-- The newcomer `true` displaces the incumbent `false`. -/
def target : Matching Bool Unit := fun doctor => if doctor then some () else none

theorem source_feasible : market.IsFeasible source := by
  apply (market.isFeasible_iff_isMatching_of_unitCapacity (fun _ => rfl) source).2
  intro first second right hfirst hsecond
  cases first <;> cases second <;> simp_all [source]

theorem target_feasible : market.IsFeasible target := by
  apply (market.isFeasible_iff_isMatching_of_unitCapacity (fun _ => rfl) target).2
  intro first second right hfirst hsecond
  cases first <;> cases second <;> simp_all [target]

theorem source_individuallyRational : rankings.IsIndividuallyRational source := by
  intro doctor hospital assigned
  cases doctor <;> cases hospital <;>
    simp [source, rankings, doctorScore, hospitalScore] at *

theorem target_individuallyRational : rankings.IsIndividuallyRational target := by
  intro doctor hospital assigned
  cases doctor <;> cases hospital <;>
    simp [target, rankings, doctorScore, hospitalScore] at *

/-- The existing responsive blocking definition witnesses the incumbent's
replacement, without requiring his consent. -/
theorem newcomer_blocks : market.IsBlockingPair source true () := by
  constructor
  · simp [Preference.strict, Rank.strict, market, MatchingMarket.withCapacities,
      rankings, doctorScore, source]
  · right
    refine ⟨false, ?_, ?_⟩
    · rfl
    · simp [Preference.strict, Rank.strict, market, MatchingMarket.withCapacities,
        rankings, hospitalScore]

theorem newcomer_strictly_improves :
    Preference.strict rankings.prefersLeft true (target true) (source true) := by
  simp [Preference.strict, Rank.strict, rankings, doctorScore, source, target]

theorem hospital_strictly_improves :
    Preference.strict rankings.prefersRight () (some true) (some false) := by
  simp [Preference.strict, Rank.strict, rankings, hospitalScore]

def consentingPair : Set (Bool ⊕ Unit) := {Sum.inl true, Sum.inr ()}

/-- A coordinate outside the consenting pair changes. Consent is not the set
of assignment coordinates affected by a responsive replacement. -/
theorem displaced_incumbent_outside_consent :
    Sum.inl false ∉ consentingPair ∧ target false ≠ source false := by
  simp [consentingPair, source, target]


/-- Displacement harms the nonconsenting incumbent. -/
theorem displaced_incumbent_strictly_worse :
    Preference.strict rankings.prefersLeft false (source false) (target false) := by
  simp [Preference.strict, Rank.strict, rankings, doctorScore, source, target]

/-- Direct assignment coordinates keep each side's own optional-partner type.
This is one concrete representation, not a restriction on all game encodings. -/
@[reducible]
def assignmentSignature : GameSignature (Bool ⊕ Unit) where
  Strategy
    | .inl _ => Option Unit
    | .inr _ => Option Bool
  Outcome := Unit

def sourceProfile : Profile assignmentSignature
  | .inl doctor => source doctor
  | .inr _ => some false

def targetProfile : Profile assignmentSignature
  | .inl doctor => target doctor
  | .inr _ => some true

/-- In this direct assignment-coordinate representation, a local rewrite
restricted to consenting agents cannot realize the blocking replacement. -/
theorem no_consent_local_rewrite {Deviator : Type*}
    (D : DeviationScheme assignmentSignature Deviator) (who : Deviator) (d : D.Dev who)
    (affected : (D.members who : Set (Bool ⊕ Unit)) ⊆ consentingPair) :
    targetProfile ∉ (D.apply (PMF.pure sourceProfile) who d).support := by
  intro htarget
  obtain ⟨original, horiginal, hagree⟩ :=
    D.exists_agree_off_members (PMF.pure sourceProfile) who d htarget
  have hsource : original = sourceProfile := (PMF.mem_support_pure_iff _ _).mp horiginal
  subst original
  have houtside : Sum.inl false ∉ D.members who := by
    intro member
    exact displaced_incumbent_outside_consent.1 (affected member)
  have hsame := hagree (Sum.inl false) houtside
  exact displaced_incumbent_outside_consent.2 hsame

/-! Equality rankings supply a separate incomparability control. -/

def equalityRankings : MatchingMarket Bool Unit where
  prefersLeft _ preferred alternative := preferred = alternative
  prefersRight _ preferred alternative := preferred = alternative

def equalityMarket : CapacitatedMarket Bool Unit :=
  equalityRankings.withCapacities fun _ => 1

def empty : Matching Bool Unit := fun _ => none

theorem empty_feasible : equalityMarket.IsFeasible empty := by
  apply (equalityMarket.isFeasible_iff_isMatching_of_unitCapacity (fun _ => rfl) empty).2
  exact MatchingMarket.empty_isMatching

theorem empty_individuallyRational : equalityRankings.IsIndividuallyRational empty := by
  intro doctor hospital assigned
  simp [empty] at assigned

/-- With partial comparisons, absence of strict blocking is strictly weaker
than requiring a positive weak rejection by one of the pair's members. -/
theorem empty_stable : equalityMarket.IsStable empty := by
  refine ⟨empty_feasible, empty_individuallyRational, ?_⟩
  rintro ⟨doctor, hospital, blocks⟩
  have himpossible := blocks.1.1
  simp [equalityMarket, MatchingMarket.withCapacities, equalityRankings, empty] at himpossible

theorem hypothetical_pair_neither_weakly_rejects :
    ¬ equalityRankings.prefersLeft true (empty true) (some ()) ∧
      ¬ equalityRankings.prefersRight () none (some true) := by
  simp [equalityRankings, empty]

end GameTheory.Experimental.MatchingConsent
