/-
# May's theorem

For binary social choice with indifference, majority is the unique rule that
is anonymous, neutral, and positively responsive.  This is ranking-free
finite social-choice mathematics: it uses `SignType` ballots and no lottery,
probability, utility, mechanism, or equilibrium layer.

Primary reference: K. O. May, “A Set of Independent Necessary and Sufficient
Conditions for Simple Majority Decision,” *Econometrica* 20 (1952).
-/

import GameTheory.Core.Rank
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.Order

namespace GameTheory.May

open Finset

variable {Voter : Type*} [Fintype Voter]

/-- Signed support for the first alternative. -/
def tally (ballot : Voter → SignType) : ℤ :=
  ∑ voter, (ballot voter : ℤ)

/-- Binary majority rule, including a tied verdict. -/
noncomputable def majority (ballot : Voter → SignType) : SignType :=
  SignType.sign (tally ballot)

/-- Relabelling voters does not change the social verdict. -/
def IsAnonymous (rule : (Voter → SignType) → SignType) : Prop :=
  ∀ ballot (permutation : Equiv.Perm Voter),
    rule (ballot ∘ permutation) = rule ballot

/-- Swapping the alternatives negates the social verdict. -/
def IsNeutral (rule : (Voter → SignType) → SignType) : Prop :=
  ∀ ballot, rule (fun voter => -(ballot voter)) = -(rule ballot)

/-- A nontrivial weak shift toward the first alternative turns every
non-adverse verdict into strict support for it. -/
def IsPositivelyResponsive (rule : (Voter → SignType) → SignType) : Prop :=
  ∀ first second : Voter → SignType,
    (∀ voter, first voter ≤ second voter) → first ≠ second →
      0 ≤ rule first → rule second = 1

theorem majority_isAnonymous :
    IsAnonymous (majority : (Voter → SignType) → SignType) := by
  intro ballot permutation
  simp only [majority, tally, Function.comp_apply]
  rw [Equiv.sum_comp permutation (fun voter => (ballot voter : ℤ))]

theorem majority_isNeutral :
    IsNeutral (majority : (Voter → SignType) → SignType) := by
  intro ballot
  have htally : tally (fun voter => -(ballot voter)) = -tally ballot := by
    simp only [tally, SignType.coe_neg, Finset.sum_neg_distrib]
  simp only [majority, htally, Left.sign_neg]

theorem majority_isPositivelyResponsive :
    IsPositivelyResponsive (majority : (Voter → SignType) → SignType) := by
  intro first second hle hne hnonnegative
  have coe_le : ∀ {a b : SignType}, a ≤ b → (a : ℤ) ≤ (b : ℤ) := by decide
  have coe_lt : ∀ {a b : SignType}, a < b → (a : ℤ) < (b : ℤ) := by decide
  simp only [majority] at hnonnegative ⊢
  rw [sign_eq_one_iff]
  have hfirst : 0 ≤ tally first := by
    by_contra hnegative
    rw [sign_eq_neg_one_iff.mpr (not_le.mp hnegative)] at hnonnegative
    exact absurd hnonnegative (by decide)
  have htally : tally first < tally second := by
    unfold tally
    apply Finset.sum_lt_sum
    · intro voter _
      exact coe_le (hle voter)
    · obtain ⟨voter, hvoter⟩ := Function.ne_iff.mp hne
      exact ⟨voter, mem_univ voter,
        coe_lt (lt_of_le_of_ne (hle voter) hvoter)⟩
  exact lt_of_le_of_lt hfirst htally

/-- The signed tally is the number of positive ballots minus the number of
negative ballots. -/
theorem tally_eq_card_sub (ballot : Voter → SignType) :
    tally ballot =
      ((univ.filter fun voter => ballot voter = 1).card : ℤ) -
        (univ.filter fun voter => ballot voter = -1).card := by
  have key : ∀ value : SignType,
      (value : ℤ) = (if value = 1 then (1 : ℤ) else 0) -
        (if value = -1 then (1 : ℤ) else 0) := by
    decide
  simp only [tally]
  rw [Finset.sum_congr rfl (fun voter _ => key (ballot voter)),
    Finset.sum_sub_distrib, sum_boole, sum_boole]

theorem card_pos_eq_card_neg (ballot : Voter → SignType)
    (htally : tally ballot = 0) :
    Fintype.card {voter // ballot voter = 1} =
      Fintype.card {voter // ballot voter = -1} := by
  have hcards := tally_eq_card_sub ballot
  rw [htally] at hcards
  simp only [Fintype.card_subtype]
  omega

/-- At a tie, a voter permutation exchanges positive and negative ballots and
fixes indifferent ballots. -/
theorem exists_neg_perm (ballot : Voter → SignType)
    (htally : tally ballot = 0) :
    ∃ permutation : Equiv.Perm Voter,
      ∀ voter, ballot (permutation voter) = -(ballot voter) := by
  classical
  let exchange : {voter // ballot voter = 1} ≃
      {voter // ballot voter = -1} :=
    Fintype.equivOfCardEq (card_pos_eq_card_neg ballot htally)
  let swap : Voter → Voter := fun voter =>
    if hpos : ballot voter = 1 then (exchange ⟨voter, hpos⟩ : Voter)
    else if hneg : ballot voter = -1 then
      (exchange.symm ⟨voter, hneg⟩ : Voter)
    else voter
  have hvalue : ∀ voter, ballot (swap voter) = -(ballot voter) := by
    intro voter
    dsimp only [swap]
    by_cases hpos : ballot voter = 1
    · rw [dif_pos hpos, hpos, (exchange ⟨voter, hpos⟩).2]
    · rw [dif_neg hpos]
      by_cases hneg : ballot voter = -1
      · rw [dif_pos hneg, hneg, (exchange.symm ⟨voter, hneg⟩).2]
        decide
      · rw [dif_neg hneg]
        have hzero : ballot voter = 0 := by
          revert hpos hneg
          cases ballot voter <;> decide
        rw [hzero]
        decide
  have hdefinition : ∀ voter,
      swap voter =
        if hpos : ballot voter = 1 then (exchange ⟨voter, hpos⟩ : Voter)
        else if hneg : ballot voter = -1 then
          (exchange.symm ⟨voter, hneg⟩ : Voter)
        else voter := fun _ => rfl
  have hinvolutive : Function.Involutive swap := by
    intro voter
    by_cases hpos : ballot voter = 1
    · have hswap : swap voter = (exchange ⟨voter, hpos⟩ : Voter) := by
        rw [hdefinition]
        exact dif_pos hpos
      have hnegative : ballot (swap voter) = -1 := by
        rw [hswap]
        exact (exchange ⟨voter, hpos⟩).2
      have hnotpositive : ¬ballot (swap voter) = 1 := by
        rw [hnegative]
        decide
      have htwice :
          swap (swap voter) =
            (exchange.symm ⟨swap voter, hnegative⟩ : Voter) := by
        rw [hdefinition (swap voter), dif_neg hnotpositive,
          dif_pos hnegative]
      have hinverse : exchange.symm ⟨swap voter, hnegative⟩ =
          ⟨voter, hpos⟩ :=
        exchange.symm_apply_eq.mpr (Subtype.ext hswap)
      rw [htwice, hinverse]
    · by_cases hneg : ballot voter = -1
      · have hswap : swap voter =
            (exchange.symm ⟨voter, hneg⟩ : Voter) := by
          rw [hdefinition, dif_neg hpos, dif_pos hneg]
        have hpositive : ballot (swap voter) = 1 := by
          rw [hswap]
          exact (exchange.symm ⟨voter, hneg⟩).2
        have htwice : swap (swap voter) =
            (exchange ⟨swap voter, hpositive⟩ : Voter) := by
          rw [hdefinition (swap voter), dif_pos hpositive]
        have hsubtype : (⟨swap voter, hpositive⟩ :
            {voter // ballot voter = 1}) = exchange.symm ⟨voter, hneg⟩ :=
          Subtype.ext hswap
        have happly : exchange ⟨swap voter, hpositive⟩ =
            ⟨voter, hneg⟩ := by
          rw [hsubtype, Equiv.apply_symm_apply]
        rw [htwice, happly]
      · have hzero : ballot voter = 0 := by
          revert hpos hneg
          cases ballot voter <;> decide
        have hswap : swap voter = voter := by
          rw [hdefinition, dif_neg hpos, dif_neg hneg]
        rw [hswap, hswap]
  exact ⟨hinvolutive.toPerm swap, hvalue⟩

theorem eq_zero_of_tally_zero {rule : (Voter → SignType) → SignType}
    (hanonymous : IsAnonymous rule) (hneutral : IsNeutral rule)
    (ballot : Voter → SignType) (htally : tally ballot = 0) :
    rule ballot = 0 := by
  obtain ⟨permutation, hpermutation⟩ := exists_neg_perm ballot htally
  have hanon : rule (ballot ∘ permutation) = rule ballot :=
    hanonymous ballot permutation
  have hprofile : ballot ∘ permutation = fun voter => -(ballot voter) :=
    funext hpermutation
  rw [hprofile, hneutral ballot] at hanon
  revert hanon
  cases rule ballot <;> decide

theorem eq_one_of_tally_pos {rule : (Voter → SignType) → SignType}
    (hanonymous : IsAnonymous rule) (hneutral : IsNeutral rule)
    (hresponsive : IsPositivelyResponsive rule)
    (ballot : Voter → SignType) (htally : 0 < tally ballot) :
    rule ballot = 1 := by
  classical
  have hcards := tally_eq_card_sub ballot
  have hcard : (tally ballot).toNat ≤
      (univ.filter fun voter => ballot voter = 1).card := by
    omega
  obtain ⟨shifted, hsubset, hsize⟩ := Finset.exists_subset_card_eq hcard
  let tie : Voter → SignType := fun voter =>
    if voter ∈ shifted then 0 else ballot voter
  have hmonotone : ∀ voter, tie voter ≤ ballot voter := by
    intro voter
    simp only [tie]
    split
    · rename_i hmem
      rw [(Finset.mem_filter.mp (hsubset hmem)).2]
      decide
    · exact le_rfl
  have hnonempty : shifted.Nonempty := by
    rw [← Finset.card_pos, hsize]
    omega
  obtain ⟨witness, hwitness⟩ := hnonempty
  have hne : tie ≠ ballot := by
    intro heq
    have hpositive : ballot witness = 1 :=
      (Finset.mem_filter.mp (hsubset hwitness)).2
    have hvalue : tie witness = ballot witness := by rw [heq]
    simp only [tie, if_pos hwitness, hpositive] at hvalue
    exact absurd hvalue (by decide)
  have htie : tally tie = 0 := by
    have hdifference : ∀ voter,
        (ballot voter : ℤ) - (tie voter : ℤ) =
          if voter ∈ shifted then (1 : ℤ) else 0 := by
      intro voter
      by_cases hmem : voter ∈ shifted
      · have hpositive : ballot voter = 1 :=
          (Finset.mem_filter.mp (hsubset hmem)).2
        simp only [tie, if_pos hmem, hpositive]
        decide
      · simp only [tie, if_neg hmem, sub_self]
    have hsum : tally ballot - tally tie = (shifted.card : ℤ) := by
      simp only [tally]
      rw [← Finset.sum_sub_distrib,
        Finset.sum_congr rfl (fun voter _ => hdifference voter),
        sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
    omega
  have htieVerdict : rule tie = 0 :=
    eq_zero_of_tally_zero hanonymous hneutral tie htie
  exact hresponsive tie ballot hmonotone hne (le_of_eq htieVerdict.symm)

theorem eq_neg_one_of_tally_neg {rule : (Voter → SignType) → SignType}
    (hanonymous : IsAnonymous rule) (hneutral : IsNeutral rule)
    (hresponsive : IsPositivelyResponsive rule)
    (ballot : Voter → SignType) (htally : tally ballot < 0) :
    rule ballot = -1 := by
  have hnegated : tally (fun voter => -(ballot voter)) = -tally ballot := by
    simp only [tally, SignType.coe_neg, Finset.sum_neg_distrib]
  have hpositive : 0 < tally (fun voter => -(ballot voter)) := by
    rw [hnegated]
    omega
  have hone : rule (fun voter => -(ballot voter)) = 1 :=
    eq_one_of_tally_pos hanonymous hneutral hresponsive _ hpositive
  rw [hneutral ballot] at hone
  revert hone
  cases rule ballot <;> decide

/-- May's theorem: anonymity, neutrality, and positive responsiveness
characterize binary majority rule. -/
theorem characterization (rule : (Voter → SignType) → SignType) :
    (∀ ballot, rule ballot = majority ballot) ↔
      IsAnonymous rule ∧ IsNeutral rule ∧ IsPositivelyResponsive rule := by
  constructor
  · intro heq
    refine ⟨fun ballot permutation => ?_, fun ballot => ?_,
      fun first second hle hne hnonnegative => ?_⟩
    · rw [heq (ballot ∘ permutation), heq ballot]
      exact majority_isAnonymous ballot permutation
    · rw [heq (fun voter => -(ballot voter)), heq ballot]
      exact majority_isNeutral ballot
    · rw [heq second]
      rw [heq first] at hnonnegative
      exact majority_isPositivelyResponsive first second hle hne hnonnegative
  · rintro ⟨hanonymous, hneutral, hresponsive⟩ ballot
    rcases lt_trichotomy (tally ballot) 0 with hnegative | hzero | hpositive
    · rw [eq_neg_one_of_tally_neg hanonymous hneutral hresponsive ballot hnegative,
        majority, sign_eq_neg_one_iff.mpr hnegative]
    · rw [eq_zero_of_tally_zero hanonymous hneutral ballot hzero,
        majority, hzero, sign_zero]
    · rw [eq_one_of_tally_pos hanonymous hneutral hresponsive ballot hpositive,
        majority, sign_eq_one_iff.mpr hpositive]

end GameTheory.May
