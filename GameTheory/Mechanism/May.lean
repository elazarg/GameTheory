/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Math.Probability

/-!
# May's theorem

May's theorem (1952) characterizes **majority rule** as the unique way to decide
between two alternatives that treats voters and alternatives even-handedly and
responds positively to support.

Each voter casts a `SignType` ballot — `1` for the first alternative, `-1` for the
second, `0` for indifference — so voters are allowed to be indifferent (the general
form of the theorem). A social decision function `f` maps profiles of ballots to a
`SignType` verdict, and majority rule returns the sign of the tally (support in favor
minus support against).

`f` agrees with majority rule on every profile **iff** `f` is

* **anonymous** — invariant under relabelling the voters,
* **neutral** — swapping the two alternatives negates the verdict, and
* **positively responsive** — if some voters shift toward the first alternative and
  the verdict was not already against it, the verdict becomes strictly in favor.

The electorate `ι` is an arbitrary `Fintype` (no fixed `Fin n`, no nonemptiness
assumption), and voters may be indifferent.

## Main definitions

* `tally` — signed vote total of a profile
* `majority` — majority rule: the sign of the tally
* `IsAnonymous`, `IsNeutral`, `IsPositivelyResponsive` — May's three axioms

## Main results

* `majority_isAnonymous`, `majority_isNeutral`, `majority_isPositivelyResponsive` —
  majority rule satisfies the three axioms
* `may_theorem` — the three axioms characterize majority rule
-/

namespace GameTheory.May

open Finset

variable {ι : Type*} [Fintype ι]

/-- The signed tally of a profile: (support for the first alternative) minus
(support for the second), counting each ballot as `+1`, `0`, or `-1`. -/
def tally (v : ι → SignType) : ℤ := ∑ i, (v i : ℤ)

/-- **Majority rule**: decide for whichever alternative has more support, with a tie
(`0`) when support is equal. It is the sign of the `tally`. -/
noncomputable def majority (v : ι → SignType) : SignType := SignType.sign (tally v)

/-- **Anonymity**: the verdict is invariant under relabelling the voters. -/
def IsAnonymous (f : (ι → SignType) → SignType) : Prop :=
  ∀ (v : ι → SignType) (σ : Equiv.Perm ι), f (v ∘ σ) = f v

/-- **Neutrality**: swapping the two alternatives — negating every ballot — negates
the verdict. -/
def IsNeutral (f : (ι → SignType) → SignType) : Prop :=
  ∀ v : ι → SignType, f (fun i => -(v i)) = -(f v)

/-- **Positive responsiveness**: if every voter's ballot weakly shifts toward the
first alternative — with at least one change — and the verdict was not already against
the first alternative, then the verdict comes out strictly in favor. -/
def IsPositivelyResponsive (f : (ι → SignType) → SignType) : Prop :=
  ∀ v v' : ι → SignType, (∀ i, v i ≤ v' i) → v ≠ v' → 0 ≤ f v → f v' = 1

/-! ### Majority rule satisfies the axioms -/

/-- Majority rule is anonymous: the tally, hence its sign, is permutation-invariant. -/
theorem majority_isAnonymous : IsAnonymous (majority : (ι → SignType) → SignType) := by
  intro v σ
  simp only [majority, tally, Function.comp_apply]
  rw [Equiv.sum_comp σ (fun i => (v i : ℤ))]

/-- Majority rule is neutral: negating every ballot negates the tally, hence its sign. -/
theorem majority_isNeutral : IsNeutral (majority : (ι → SignType) → SignType) := by
  intro v
  have ht : tally (fun i => -(v i)) = - tally v := by
    simp only [tally, SignType.coe_neg, Finset.sum_neg_distrib]
  simp only [majority, ht, Left.sign_neg]

/-- Majority rule is positively responsive: a weak, non-trivial shift toward the first
alternative from a non-adverse verdict strictly increases the tally past zero. -/
theorem majority_isPositivelyResponsive :
    IsPositivelyResponsive (majority : (ι → SignType) → SignType) := by
  intro v v' hle hne hnonneg
  have cle : ∀ {a b : SignType}, a ≤ b → (a : ℤ) ≤ (b : ℤ) := by decide
  have clt : ∀ {a b : SignType}, a < b → (a : ℤ) < (b : ℤ) := by decide
  simp only [majority] at hnonneg ⊢
  rw [sign_eq_one_iff]
  have hv : 0 ≤ tally v := by
    by_contra h
    rw [sign_eq_neg_one_iff.mpr (not_le.mp h)] at hnonneg
    exact absurd hnonneg (by decide)
  have hlt : tally v < tally v' := by
    unfold tally
    apply Finset.sum_lt_sum
    · intro i _; exact cle (hle i)
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
      exact ⟨j, mem_univ j, clt (lt_of_le_of_ne (hle j) hj)⟩
  exact lt_of_le_of_lt hv hlt

/-! ### The axioms force majority rule -/

/-- The tally is the number of `+1` ballots minus the number of `-1` ballots. -/
theorem tally_eq_card_sub (v : ι → SignType) :
    tally v = ((univ.filter (fun i => v i = 1)).card : ℤ)
      - (univ.filter (fun i => v i = -1)).card := by
  have key : ∀ a : SignType,
      (a : ℤ) = (if a = 1 then (1 : ℤ) else 0) - (if a = -1 then (1 : ℤ) else 0) := by decide
  simp only [tally]
  rw [Finset.sum_congr rfl (fun i _ => key (v i)), Finset.sum_sub_distrib,
    Finset.sum_boole, Finset.sum_boole]

/-- A zero tally means the `+1` and `-1` blocks have equal size. -/
theorem card_pos_eq_card_neg (v : ι → SignType) (h : tally v = 0) :
    Fintype.card {i // v i = 1} = Fintype.card {i // v i = -1} := by
  have hts := tally_eq_card_sub v
  rw [h] at hts
  simp only [Fintype.card_subtype]
  omega

/-- **Swap lemma.** When the tally is zero, some relabelling of the voters turns every
ballot into its negation: the equally-sized blocks of `+1` and `-1` ballots are
exchanged and the indifferent voters are fixed. -/
theorem exists_neg_perm (v : ι → SignType) (h : tally v = 0) :
    ∃ σ : Equiv.Perm ι, ∀ i, v (σ i) = -(v i) := by
  classical
  let e : {i // v i = 1} ≃ {i // v i = -1} :=
    Fintype.equivOfCardEq (card_pos_eq_card_neg v h)
  let g : ι → ι := fun i =>
    if h1 : v i = 1 then (e ⟨i, h1⟩ : ι)
    else if h2 : v i = -1 then (e.symm ⟨i, h2⟩ : ι)
    else i
  have hval : ∀ i, v (g i) = -(v i) := by
    intro i
    change v (if h1 : v i = 1 then (e ⟨i, h1⟩ : ι)
        else if h2 : v i = -1 then (e.symm ⟨i, h2⟩ : ι) else i) = -(v i)
    by_cases h1 : v i = 1
    · rw [dif_pos h1, h1, (e ⟨i, h1⟩).2]
    · rw [dif_neg h1]
      by_cases h2 : v i = -1
      · rw [dif_pos h2, h2, (e.symm ⟨i, h2⟩).2]; decide
      · rw [dif_neg h2]
        have h0 : v i = 0 := by revert h1 h2; cases v i <;> decide
        rw [h0]; decide
  have gdite : ∀ j : ι, g j = if h1 : v j = 1 then (e ⟨j, h1⟩ : ι)
      else if h2 : v j = -1 then (e.symm ⟨j, h2⟩ : ι) else j := fun _ => rfl
  have hinv : Function.Involutive g := by
    intro i
    by_cases h1 : v i = 1
    · have hgi : g i = (e ⟨i, h1⟩ : ι) := by rw [gdite]; exact dif_pos h1
      have hv1 : v (g i) = -1 := by rw [hgi]; exact (e ⟨i, h1⟩).2
      have hne1 : ¬ v (g i) = 1 := by rw [hv1]; decide
      have hggi : g (g i) = (e.symm ⟨g i, hv1⟩ : ι) := by
        rw [gdite (g i), dif_neg hne1, dif_pos hv1]
      have hsymm : e.symm ⟨g i, hv1⟩ = ⟨i, h1⟩ :=
        e.symm_apply_eq.mpr (Subtype.ext hgi)
      rw [hggi, hsymm]
    · by_cases h2 : v i = -1
      · have hgi : g i = (e.symm ⟨i, h2⟩ : ι) := by rw [gdite, dif_neg h1, dif_pos h2]
        have hv1 : v (g i) = 1 := by rw [hgi]; exact (e.symm ⟨i, h2⟩).2
        have hggi : g (g i) = (e ⟨g i, hv1⟩ : ι) := by rw [gdite (g i), dif_pos hv1]
        have hsub : (⟨g i, hv1⟩ : {i // v i = 1}) = e.symm ⟨i, h2⟩ := Subtype.ext hgi
        have happ : e ⟨g i, hv1⟩ = ⟨i, h2⟩ := by rw [hsub, Equiv.apply_symm_apply]
        rw [hggi, happ]
      · have h0 : v i = 0 := by revert h1 h2; cases v i <;> decide
        have hgi : g i = i := by rw [gdite, dif_neg h1, dif_neg h2]
        rw [hgi, hgi]
  exact ⟨hinv.toPerm g, fun i => hval i⟩

/-- Under anonymity and neutrality, a tied electorate produces a tied verdict:
relabelling by the swap of `exists_neg_perm` turns `v` into `-v`, so anonymity and
neutrality force `f v = -(f v)`, hence `f v = 0`. -/
theorem eq_zero_of_tally_zero {f : (ι → SignType) → SignType}
    (hA : IsAnonymous f) (hN : IsNeutral f) (v : ι → SignType) (h : tally v = 0) :
    f v = 0 := by
  obtain ⟨σ, hσ⟩ := exists_neg_perm v h
  have h1 : f (v ∘ σ) = f v := hA v σ
  have h3 : (v ∘ σ) = fun i => -(v i) := funext hσ
  rw [h3, hN v] at h1
  revert h1
  cases f v <;> decide

/-- Under the three axioms, a positive tally produces a verdict for the first
alternative: lower just enough `+1` ballots to `0` to reach an exact tie, where the
verdict is `0` by `eq_zero_of_tally_zero`; then positive responsiveness carries the
restored ballots to a verdict of `1`. -/
theorem eq_one_of_tally_pos {f : (ι → SignType) → SignType}
    (hA : IsAnonymous f) (hN : IsNeutral f) (hP : IsPositivelyResponsive f)
    (v : ι → SignType) (h : 0 < tally v) : f v = 1 := by
  classical
  have hts := tally_eq_card_sub v
  have hcard : (tally v).toNat ≤ (univ.filter (fun i => v i = 1)).card := by omega
  obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hcard
  set v0 : ι → SignType := fun i => if i ∈ S then 0 else v i with hv0_def
  have hmono : ∀ i, v0 i ≤ v i := by
    intro i
    simp only [hv0_def]
    split
    · rename_i hi
      rw [(Finset.mem_filter.mp (hSsub hi)).2]; decide
    · exact le_rfl
  have hSne : S.Nonempty := by rw [← Finset.card_pos, hScard]; omega
  obtain ⟨i0, hi0⟩ := hSne
  have hne : v0 ≠ v := by
    intro hcon
    have hvi0 : v i0 = 1 := (Finset.mem_filter.mp (hSsub hi0)).2
    have hval0 : v0 i0 = v i0 := by rw [hcon]
    simp only [hv0_def, if_pos hi0, hvi0] at hval0
    exact absurd hval0 (by decide)
  have htie : tally v0 = 0 := by
    have hd : ∀ i, (v i : ℤ) - (v0 i : ℤ) = if i ∈ S then (1 : ℤ) else 0 := by
      intro i
      by_cases hi : i ∈ S
      · have hvi : v i = 1 := (Finset.mem_filter.mp (hSsub hi)).2
        simp only [hv0_def, if_pos hi, hvi]; decide
      · simp only [hv0_def, if_neg hi, sub_self]
    have hsum : tally v - tally v0 = (S.card : ℤ) := by
      simp only [tally]
      rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun i _ => hd i),
        Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
    omega
  have hf0 : f v0 = 0 := eq_zero_of_tally_zero hA hN v0 htie
  exact hP v0 v hmono hne (le_of_eq hf0.symm)

/-- The mirror image of `eq_one_of_tally_pos`: a negative tally produces a verdict for
the second alternative, obtained by applying the positive case to the negated profile
and undoing it with neutrality. -/
theorem eq_neg_one_of_tally_neg {f : (ι → SignType) → SignType}
    (hA : IsAnonymous f) (hN : IsNeutral f) (hP : IsPositivelyResponsive f)
    (v : ι → SignType) (h : tally v < 0) : f v = -1 := by
  have htneg : tally (fun i => -(v i)) = - tally v := by
    simp only [tally, SignType.coe_neg, Finset.sum_neg_distrib]
  have hpos : 0 < tally (fun i => -(v i)) := by rw [htneg]; omega
  have h1 : f (fun i => -(v i)) = 1 := eq_one_of_tally_pos hA hN hP _ hpos
  rw [hN v] at h1
  revert h1
  cases f v <;> decide

/-- **May's theorem** (May 1952). A social decision function `f` between two
alternatives agrees with majority rule on every profile of `SignType` ballots **iff**
it is anonymous, neutral, and positively responsive. -/
theorem may_theorem (f : (ι → SignType) → SignType) :
    (∀ v, f v = majority v) ↔
      IsAnonymous f ∧ IsNeutral f ∧ IsPositivelyResponsive f := by
  constructor
  · intro hf
    refine ⟨fun v σ => ?_, fun v => ?_, fun v v' hle hne hnn => ?_⟩
    · rw [hf (v ∘ σ), hf v]; exact majority_isAnonymous v σ
    · rw [hf (fun i => -(v i)), hf v]; exact majority_isNeutral v
    · rw [hf v']; rw [hf v] at hnn; exact majority_isPositivelyResponsive v v' hle hne hnn
  · rintro ⟨hA, hN, hP⟩ v
    rcases lt_trichotomy (tally v) 0 with ht | ht | ht
    · rw [eq_neg_one_of_tally_neg hA hN hP v ht, majority, sign_eq_neg_one_iff.mpr ht]
    · rw [eq_zero_of_tally_zero hA hN v ht, majority, ht, sign_zero]
    · rw [eq_one_of_tally_pos hA hN hP v ht, majority, sign_eq_one_iff.mpr ht]

end GameTheory.May
