/-
# Classic examples

Four executable games plus the downstream usability tests. Nothing here
opens an implementation namespace or mentions a transport, certificate, or
representation: the public `TableGame`, `Profile`, and solution-concept API is
all a reader needs.

Every `#guard` is a regression test that fails the build if the algorithm and
the semantics drift apart.
-/

import GameTheory.Finite.Correctness
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring

namespace GameTheory.Examples

open GameTheory GameTheory.Finite GameTheory.Probability

/-! ## Prisoner's Dilemma -/

/-- Cooperate or defect. -/
inductive Choice
  | cooperate
  | defect
  deriving DecidableEq, Fintype, Repr

/-- The other player in a two-player game. -/
def opponent (i : Fin 2) : Fin 2 := 1 - i

/-- Standard Prisoner's Dilemma payoffs, own action first. -/
def dilemmaPayoff : Choice → Choice → ℚ
  | .cooperate, .cooperate => 3
  | .cooperate, .defect => 0
  | .defect, .cooperate => 5
  | .defect, .defect => 1

/-- The Prisoner's Dilemma. -/
def prisonersDilemma : TableGame (Fin 2) where
  Action _ := Choice
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile i := dilemmaPayoff (profile i) (profile (opponent i))

/-- Both defect. -/
def bothDefect : Profile prisonersDilemma.sig := fun _ => .defect

/-- Both cooperate. -/
def bothCooperate : Profile prisonersDilemma.sig := fun _ => .cooperate

#guard prisonersDilemma.isNash bothDefect
#guard !prisonersDilemma.isNash bothCooperate
#guard prisonersDilemma.enumerateNash.card = 1
#guard prisonersDilemma.isDominantProfile bothDefect
#guard !prisonersDilemma.isParetoEfficient bothDefect

/-- Mutual defection is the unique pure equilibrium, stated against the
semantic predicate rather than the checker. -/
theorem prisonersDilemma_isNash_iff (profile : Profile prisonersDilemma.sig) :
    IsNash prisonersDilemma.toForm (euPreference prisonersDilemma.utility) profile ↔
      profile = bothDefect := by
  rw [← TableGame.isNash_eq_true_iff]
  revert profile
  decide

/-- The enumerated profile really is Nash for the compiled real-valued
semantics; the executable and semantic sides agree. -/
theorem prisonersDilemma_bothDefect_isNash :
    IsNash prisonersDilemma.toForm (euPreference prisonersDilemma.utility) bothDefect := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- The deterministic frontend plays the mutual-defection profile as its point
mass outcome law. -/
theorem prisonersDilemma_bothDefect_play :
    prisonersDilemma.toForm.play bothDefect = FinDist.pure bothDefect :=
  TableGame.toForm_play prisonersDilemma bothDefect

/-- Mutual cooperation is not a Nash equilibrium: either player can profit by
defecting. -/
theorem prisonersDilemma_bothCooperate_not_isNash :
    ¬ IsNash prisonersDilemma.toForm (euPreference prisonersDilemma.utility)
      bothCooperate := by
  rw [prisonersDilemma_isNash_iff]
  decide

/-- Defection is dominant, hence Nash by the abstract theorem rather than a
second computation. -/
theorem prisonersDilemma_bothDefect_isNash_of_dominant :
    IsNash prisonersDilemma.toForm (euPreference prisonersDilemma.utility) bothDefect :=
  IsDominantProfile.isNash
    ((TableGame.isDominantProfile_eq_true_iff prisonersDilemma bothDefect).1 (by decide))

/-- Defection is dominant for either prisoner. -/
theorem prisonersDilemma_defect_isDominant (who : Fin 2) :
    IsDominant prisonersDilemma.toForm (euPreference prisonersDilemma.utility)
      who .defect :=
  ((TableGame.isDominantProfile_eq_true_iff prisonersDilemma bothDefect).1
    (by decide)) who

/-- Defection strictly dominates cooperation. -/
theorem prisonersDilemma_defect_strictlyDominates (who : Fin 2) :
    StrictlyDominates prisonersDilemma.toForm (euPreference prisonersDilemma.utility)
      who .defect .cooperate :=
  (TableGame.strictlyDominates_eq_true_iff prisonersDilemma who .defect .cooperate).1
    (by revert who; decide)

/-- Hence cooperation survives no round of elimination — from the abstract
theorem, not from a second computation. -/
theorem prisonersDilemma_cooperate_not_isRationalizable (who : Fin 2) :
    ¬ IsRationalizable prisonersDilemma.toForm (euPreference prisonersDilemma.utility)
      who .cooperate :=
  (prisonersDilemma_defect_strictlyDominates who).not_isRationalizable

/-- And no equilibrium plays it. The elimination and equilibrium families meet
here: nothing about this profile is computed, it follows from the two theorems
above. -/
theorem prisonersDilemma_isNash_ne_cooperate {profile : Profile prisonersDilemma.sig}
    (hnash : IsNash prisonersDilemma.toForm (euPreference prisonersDilemma.utility) profile)
    (who : Fin 2) : profile who ≠ .cooperate := by
  intro hcooperate
  refine hnash.not_strictlyDominates (who := who) (preferred := Choice.defect) ?_
  rw [hcooperate]
  exact prisonersDilemma_defect_strictlyDominates who

/-- Mutual defection is not Pareto efficient — both prisoners prefer mutual
cooperation — and the computed checker and the semantic predicate agree on
that. -/
theorem prisonersDilemma_bothDefect_not_isParetoEfficient :
    ¬ IsParetoEfficient prisonersDilemma.toForm (euPreference prisonersDilemma.utility)
      bothDefect := by
  rw [← TableGame.isParetoEfficient_eq_true_iff]
  decide

/-- It *is* weakly Pareto efficient all the same, and that is not an accident:
being a strong equilibrium forces it. The two notions come apart exactly where
Pareto domination allows indifference. -/
theorem prisonersDilemma_bothDefect_isWeaklyParetoEfficient
    (hstrong : IsStrongNash prisonersDilemma.toForm (euPreference prisonersDilemma.utility)
      bothDefect) :
    IsWeaklyParetoEfficient prisonersDilemma.toForm (euPreference prisonersDilemma.utility)
      bothDefect :=
  hstrong.isWeaklyParetoEfficient (euPreference_total _)

/-- Mutual defection stays an equilibrium once the players may randomize. Mixed
Nash is not a separate predicate here — it is `IsNash` of the mixed extension —
so this is the abstract embedding theorem instantiated, not a new computation. -/
theorem prisonersDilemma_bothDefect_isNash_mixed :
    IsNash prisonersDilemma.toForm.mixed (euPreference prisonersDilemma.utility)
      (prisonersDilemma.toForm.purify bothDefect) :=
  prisonersDilemma_bothDefect_isNash.purify

/-! ## Matching Pennies -/

/-- Heads or tails. -/
inductive Side
  | heads
  | tails
  deriving DecidableEq, Fintype, Repr

/-- Player `0` wins when the coins match. -/
def matchingPennies : TableGame (Fin 2) where
  Action _ := Side
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile i :=
    if profile 0 = profile 1 then (if i = 0 then 1 else -1) else (if i = 0 then -1 else 1)

@[simp]
theorem matchingPennies_payoff (profile : Fin 2 → Side) (i : Fin 2) :
    matchingPennies.payoff profile i =
      if profile 0 = profile 1 then (if i = 0 then 1 else -1)
      else (if i = 0 then -1 else 1) := rfl

/-- Boolean labels for the two descriptive penny sides. -/
def Side.boolEquiv : Bool ≃ Side where
  toFun
    | true => .heads
    | false => .tails
  invFun
    | .heads => true
    | .tails => false
  left_inv bit := by cases bit <;> rfl
  right_inv side := by cases side <;> rfl

/-- The same labels at the dependent action type of either player. -/
def matchingPenniesAction (who : Fin 2) : Bool ≃ matchingPennies.Action who :=
  Side.boolEquiv

/-- Matching Pennies satisfies the language-independent binary payoff
pattern. -/
def matchingPenniesLike :
    matchingPennies.toForm.MatchingPenniesLike matchingPennies.utility where
  action := matchingPenniesAction
  scale := 1
  scale_pos := by norm_num
  payoff_zero bits := by
    rw [TableGame.toForm_play, expectedUtility_pure]
    simp only [TableGame.utility_apply, matchingPennies_payoff]
    cases hzero : bits 0 <;> cases hone : bits 1 <;> split <;> norm_num
    all_goals
      rename_i hbad
      first
      | exact hbad rfl
      | exact Bool.noConfusion (Side.boolEquiv.injective hbad)
  payoff_one bits := by
    rw [TableGame.toForm_play, expectedUtility_pure]
    simp only [TableGame.utility_apply, matchingPennies_payoff]
    cases hzero : bits 0 <;> cases hone : bits 1 <;> split <;> norm_num
    all_goals
      rename_i hbad
      first
      | exact hbad rfl
      | exact Bool.noConfusion (Side.boolEquiv.injective hbad)

/-- An arbitrary semantic mixed profile is Nash in Matching Pennies exactly
when both players put probability one half on heads. -/
theorem matchingPennies_mixed_isNash_iff_half
    (mixedProfile : Profile matchingPennies.toForm.sig.mixed) :
    IsNash matchingPennies.toForm.mixed
        (euPreference matchingPennies.utility) mixedProfile ↔
      (mixedProfile 0).prob .heads = (1 / 2 : ℝ) ∧
        (mixedProfile 1).prob .heads = (1 / 2 : ℝ) := by
  have hzero : matchingPenniesLike.action 0 true = .heads := rfl
  have hone : matchingPenniesLike.action 1 true = .heads := rfl
  simpa only [GameForm.MatchingPenniesLike.probTrue, hzero, hone] using
    matchingPenniesLike.isNash_iff_half mixedProfile

#guard matchingPennies.enumerateNash.card = 0

/-- Matching Pennies has no pure Nash equilibrium. -/
theorem matchingPennies_noPureNash (profile : Profile matchingPennies.sig) :
    ¬ IsNash matchingPennies.toForm (euPreference matchingPennies.utility)
      profile := by
  rw [← TableGame.isNash_eq_true_iff]
  revert profile
  decide

/-- The standard uniform mixed equilibrium, supplied by the reader. -/
def uniformPennies : Profile matchingPennies.mixedSig := fun _ _ => 1 / 2

#guard matchingPennies.isMixed uniformPennies
#guard matchingPennies.verifyMixedNash uniformPennies

#guard matchingPennies.expectedPayoff uniformPennies 0 = 0

/-- One penny profile. -/
def pennyProfile (first second : Side) : Profile matchingPennies.sig := ![first, second]

@[simp] theorem pennyProfile_zero (first second : Side) : pennyProfile first second 0 = first := rfl
@[simp] theorem pennyProfile_one (first second : Side) : pennyProfile first second 1 = second := rfl

/-- Kernel `decide` cannot reduce `ℚ` addition, so the four penny profiles are
listed here and the exact rational arithmetic is discharged by `norm_num`. -/
theorem pennyProfiles :
    (Finset.univ : Finset (Profile matchingPennies.sig)) =
      {pennyProfile .heads .heads, pennyProfile .heads .tails,
       pennyProfile .tails .heads, pennyProfile .tails .tails} := by
  decide

theorem uniformPennies_isMixed : matchingPennies.isMixed uniformPennies = true := by
  rw [TableGame.isMixed_iff]
  refine fun i => ⟨fun a => by norm_num [uniformPennies], ?_⟩
  have hcard : Fintype.card (matchingPennies.Action i) = 2 := rfl
  simp only [uniformPennies, Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]
  norm_num

theorem sum_pennies (f : Profile matchingPennies.sig → ℚ) :
    ∑ p, f p = f (pennyProfile .heads .heads) + f (pennyProfile .heads .tails)
      + f (pennyProfile .tails .heads) + f (pennyProfile .tails .tails) := by
  rw [pennyProfiles, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

/-- The fair profile gives either player expected payoff zero. -/
theorem uniformPennies_expectedPayoff_zero (who : Fin 2) :
    matchingPennies.expectedPayoff uniformPennies who = 0 := by
  simp only [TableGame.expectedPayoff, sum_pennies, TableGame.mixedWeight,
    Fin.prod_univ_two, matchingPennies_payoff, pennyProfile_zero,
    pennyProfile_one]
  fin_cases who <;>
    norm_num +decide [uniformPennies]

/-- Every pure deviation against a fair opponent also gives payoff zero. This
is the concrete balanced-mixing fact behind the Nash verification. -/
theorem uniformPennies_pureDeviation_expectedPayoff_zero
    (who : Fin 2) (action : matchingPennies.Action who) :
    matchingPennies.expectedPayoff
        (Profile.update uniformPennies who
          (matchingPennies.pureMixed who action)) who = 0 := by
  simp only [TableGame.expectedPayoff, sum_pennies, TableGame.mixedWeight,
    Fin.prod_univ_two, matchingPennies_payoff, pennyProfile_zero,
    pennyProfile_one]
  fin_cases who <;> cases action <;>
    norm_num +decide [TableGame.pureMixed, uniformPennies]

theorem uniformPennies_verify : matchingPennies.verifyMixedNash uniformPennies = true := by
  rw [TableGame.verifyMixedNash, uniformPennies_isMixed, Bool.true_and]
  simp only [decide_eq_true_eq]
  intro who a
  rw [uniformPennies_pureDeviation_expectedPayoff_zero,
    uniformPennies_expectedPayoff_zero]

/-- The verified rational profile is a mixed Nash equilibrium of the compiled
game. There is no separate mixed-Nash predicate: this is `IsNash` of the mixed
extension. -/
theorem matchingPennies_uniform_isNash :
    IsNash matchingPennies.toForm.mixed (euPreference matchingPennies.utility)
      (matchingPennies.toMixed uniformPennies uniformPennies_isMixed) := by
  rw [← TableGame.verifyMixedNash_eq_true_iff]
  exact uniformPennies_verify

/-- The semantic fair profile, after validating and compiling the exact
rational weights. -/
abbrev fairPennies : Profile matchingPennies.toForm.sig.mixed :=
  matchingPennies.toMixed uniformPennies uniformPennies_isMixed

/-- The named fair profile is a mixed Nash equilibrium. -/
theorem fairPennies_isNash :
    IsNash matchingPennies.toForm.mixed
      (euPreference matchingPennies.utility) fairPennies :=
  matchingPennies_uniform_isNash

/-- Independent fair mixing induces a correlated equilibrium of Matching
Pennies. This is the concrete consumer of the general mixed-Nash-to-CE bridge.
-/
theorem matchingPennies_fair_isCorrelatedEq :
    IsCorrelatedEq matchingPennies.toForm
      (euPreference matchingPennies.utility) (Probability.FinDist.pi fairPennies) :=
  fairPennies_isNash.isCorrelatedEq_pi

private theorem matchingPenniesLike_fairProfile_eq_fairPennies :
    matchingPenniesLike.fairProfile = fairPennies := by
  funext who
  apply FinDist.ext_of_prob
  intro action
  rw [TableGame.toMixed_prob]
  cases action
  · have hheads : (Side.heads : matchingPennies.Action who) =
        matchingPenniesLike.action who true := rfl
    rw [hheads, matchingPenniesLike.fairProfile_prob_action]
    norm_num [uniformPennies]
  · have htails : (Side.tails : matchingPennies.Action who) =
        matchingPenniesLike.action who false := rfl
    rw [htails, matchingPenniesLike.fairProfile_prob_action]
    norm_num [uniformPennies]

/-- The independent fair law is the unique correlated equilibrium of Matching
Pennies. -/
theorem matchingPennies_correlatedEq_unique
    {law : FinDist (Profile matchingPennies.sig)}
    (hCE : IsCorrelatedEq matchingPennies.toForm
      (euPreference matchingPennies.utility) law) :
    law = FinDist.pi fairPennies := by
  rw [← matchingPenniesLike_fairProfile_eq_fairPennies]
  exact matchingPenniesLike.correlatedEq_unique hCE

/-- A profile law is a correlated equilibrium of Matching Pennies exactly when
it is the independent fair law. -/
theorem matchingPennies_isCorrelatedEq_iff
    (law : FinDist (Profile matchingPennies.sig)) :
    IsCorrelatedEq matchingPennies.toForm
        (euPreference matchingPennies.utility) law ↔
      law = FinDist.pi fairPennies := by
  constructor
  · exact matchingPennies_correlatedEq_unique
  · rintro rfl
    exact matchingPennies_fair_isCorrelatedEq

/-! ## Stag Hunt -/

/-- Hunt stag together or take the safe hare. -/
inductive Hunt
  | stag
  | hare
  deriving DecidableEq, Fintype, Repr

/-- The Stag Hunt coordination game, written as a symmetric payoff table. -/
def stagHunt : TableGame (Fin 2) where
  Action _ := Hunt
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile i :=
    match profile i, profile (opponent i) with
    | .stag, .stag => 3
    | .stag, .hare => 0
    | .hare, .stag => 1
    | .hare, .hare => 1

/-- The Pareto-dominant coordination profile. -/
def bothStag : Profile stagHunt.sig := fun _ => .stag

/-- The safer coordination profile. -/
def bothHare : Profile stagHunt.sig := fun _ => .hare

/-- A mismatched Stag Hunt profile. -/
def stagHare : Profile stagHunt.sig := ![.stag, .hare]

#guard stagHunt.enumerateNash.card = 2
#guard stagHunt.isNash bothStag
#guard stagHunt.isNash bothHare
#guard !stagHunt.isNash stagHare

/-- Mutual stag hunting is a Nash equilibrium. -/
theorem stagHunt_bothStag_isNash :
    IsNash stagHunt.toForm (euPreference stagHunt.utility) bothStag := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- Mutual hare hunting is also a Nash equilibrium. -/
theorem stagHunt_bothHare_isNash :
    IsNash stagHunt.toForm (euPreference stagHunt.utility) bothHare := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- A stag hunter facing a hare hunter profitably switches to hare. -/
theorem stagHunt_stagHare_not_isNash :
    ¬ IsNash stagHunt.toForm (euPreference stagHunt.utility) stagHare := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-! ## Hawk–Dove -/

/-- Escalate as a hawk or accommodate as a dove. -/
inductive Contest
  | hawk
  | dove
  deriving DecidableEq, Fintype, Repr

/-- The symmetric Hawk–Dove anti-coordination game. -/
def hawkDove : TableGame (Fin 2) where
  Action _ := Contest
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile i :=
    match profile i, profile (opponent i) with
    | .hawk, .hawk => -1
    | .hawk, .dove => 3
    | .dove, .hawk => 0
    | .dove, .dove => 1

/-- Player zero escalates and player one accommodates. -/
def hawkDoveProfile : Profile hawkDove.sig := ![.hawk, .dove]

/-- Player zero accommodates and player one escalates. -/
def doveHawkProfile : Profile hawkDove.sig := ![.dove, .hawk]

#guard hawkDove.enumerateNash.card = 2
#guard hawkDove.isNash hawkDoveProfile
#guard hawkDove.isNash doveHawkProfile

/-- Hawk against dove is a Nash equilibrium. -/
theorem hawkDoveProfile_isNash :
    IsNash hawkDove.toForm (euPreference hawkDove.utility)
      hawkDoveProfile := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- The role-reversed profile is the second pure Nash equilibrium. -/
theorem doveHawkProfile_isNash :
    IsNash hawkDove.toForm (euPreference hawkDove.utility)
      doveHawkProfile := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-! ## Battle of the Sexes -/

/-- Where to spend the evening. -/
inductive Venue
  | opera
  | football
  deriving DecidableEq, Fintype, Repr

/-- Both prefer agreeing, but disagree about where. -/
def battleOfTheSexes : TableGame (Fin 2) where
  Action _ := Venue
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile i :=
    if profile 0 ≠ profile 1 then 0
    else if profile i = .opera then (if i = 0 then 2 else 1)
    else (if i = 0 then 1 else 2)

/-- Both players attend the opera. -/
def bothOpera : Profile battleOfTheSexes.sig := fun _ => .opera

/-- Both players attend the football match. -/
def bothFootball : Profile battleOfTheSexes.sig := fun _ => .football

#guard battleOfTheSexes.enumerateNash.card = 2
#guard battleOfTheSexes.isNash bothOpera
#guard battleOfTheSexes.isNash bothFootball
#guard !battleOfTheSexes.isDominantProfile bothOpera

/-- Coordinating on opera is a Nash equilibrium. -/
theorem battleOfTheSexes_bothOpera_isNash :
    IsNash battleOfTheSexes.toForm (euPreference battleOfTheSexes.utility)
      bothOpera := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-- Coordinating on football is the other pure Nash equilibrium. -/
theorem battleOfTheSexes_bothFootball_isNash :
    IsNash battleOfTheSexes.toForm (euPreference battleOfTheSexes.utility)
      bothFootball := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-! ## A three-player game -/

/-- Three players are rewarded only for unanimity. -/
def unanimity : TableGame (Fin 3) where
  Action _ := Bool
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile _ := if profile 0 = profile 1 ∧ profile 1 = profile 2 then 1 else 0

#guard unanimity.enumerateNash.card = 2
#guard unanimity.isNash (fun _ => true)
#guard !unanimity.isNash (fun i => i == 0)

theorem unanimity_allTrue_isNash :
    IsNash unanimity.toForm (euPreference unanimity.utility) (fun _ => true) := by
  rw [← TableGame.isNash_eq_true_iff]
  decide

/-! ## Usability tests

Each is written against the public API only. -/

/-- A purely ordinal preference: judge a law by the best outcome it can
produce, with no expected utility anywhere. -/
def bestCasePreference {Agent Outcome : Type} (rank : Outcome → Agent → ℚ) :
    WeakPreference Agent Outcome :=
  fun agent preferred alternative =>
    ∀ bad ∈ alternative.support, ∃ good ∈ preferred.support,
      rank bad agent ≤ rank good agent

/-- The same form, switched from expected utility to an ordinal preference. The
form, the profile, and `IsNash` are unchanged; only the preference argument
differs. -/
theorem prisonersDilemma_bothDefect_isNash_ordinal :
    IsNash prisonersDilemma.toForm (bestCasePreference prisonersDilemma.payoff) bothDefect := by
  rw [isNash_iff]
  intro who replacement bad hbad
  refine ⟨bothDefect, by simp, ?_⟩
  rw [FinDist.mem_support_pure] at hbad
  subst hbad
  revert who replacement
  decide

/-- Bundling a form with its evaluation is an ergonomic option, not a second
semantic layer. -/
noncomputable def prisonersDilemmaGame : UtilityGame (Fin 2) where
  form := prisonersDilemma.toForm
  utility := prisonersDilemma.utility

/-- The bundled game proves nothing new: `IsNash` still takes the form and the
preference explicitly, so the unbundled theorem is accepted verbatim. -/
theorem prisonersDilemmaGame_bothDefect_isNash :
    IsNash prisonersDilemmaGame.form prisonersDilemmaGame.preference bothDefect :=
  prisonersDilemma_bothDefect_isNash

/-- A second play law over the *same* signature: with probability one half the
intended profile is played, otherwise both players defect. -/
noncomputable def noisyDilemma : GameForm (Fin 2) where
  sig := prisonersDilemma.sig
  play profile :=
    FinDist.mix (1 / 2) (by norm_num) (by norm_num)
      (FinDist.pure profile) (FinDist.pure bothDefect)

/-- One signature-bound profile, two different play laws, one shared profile
theorem. Nothing is restated or converted. -/
theorem update_eq_self_serves_both_laws
    (profile : Profile prisonersDilemma.sig) (who : Fin 2) :
    prisonersDilemma.toForm.play (Profile.update profile who (profile who)) =
        prisonersDilemma.toForm.play profile ∧
      noisyDilemma.play (Profile.update profile who (profile who)) =
        noisyDilemma.play profile := by
  refine ⟨?_, ?_⟩ <;> rw [Profile.update_eq_self]

end GameTheory.Examples
