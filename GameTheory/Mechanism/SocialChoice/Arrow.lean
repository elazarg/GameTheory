/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.SocialChoice.Basic

/-!
# Arrow's impossibility theorem

The social-choice layer (`SocialChoice/Basic.lean`) defines a social welfare function on an
*unconstrained* `PrefRel`. Arrow's theorem is not even statable there: it needs the
preferences to be **rankings** (strict linear orders) and the social welfare function to
return a ranking ("collective rationality"). This file adds that rationality layer and
proves Arrow's impossibility theorem via Geanakoplos's pivotal-voter argument.
The proof architecture is the strict-order construction also mechanized by Tobias Nipkow in
the AFP entry *Arrow and Gibbard-Satterthwaite*; this development is adapted to the library's
relation-valued `SWF` interface.

Throughout, a `PrefRel` is read as a **strict** preference: `r a b` means "`a` is
strictly preferred to `b`". Arrow's domain is the profiles of *rankings*, so the Pareto and
IIA axioms are taken on that domain (`SWF.IsParetoOnRankings`, `SWF.IsIIAOnRankings`). The
unconstrained `SWF.IsPareto` / `SWF.IsIIA` of `SocialChoice/Basic.lean` imply these restrictions
(`IsPareto.onRankings`, `IsIIA.onRankings`), so the theorem also applies under the global axioms.

## Main definitions

* `IsRanking` — a strict linear order (irreflexive, transitive, total on distinct pairs)
* `HasAtLeastThree` — an inhabited alternative type with an alternative outside every pair
* `SWF.IsSWO` — collective rationality: the SWF maps ranking profiles to a ranking
* `SWF.IsParetoOnRankings`, `SWF.IsIIAOnRankings` — weak Pareto and IIA on the domain of rankings
* `SWF.IsDictatorOnRankings` — a voter whose strict preference society always follows on rankings

## Main results

* `arrow_impossibility` — with ≥ 3 alternatives and a nonempty finite electorate, every
  collectively rational SWF that is weakly Paretian and IIA on ranking profiles is dictatorial;
  the alternative type may be infinite.
* `arrow_impossibility_exact` — the same conclusion, with the dictator's strict preference shown
  to coincide with society's on every ranking profile.
-/

namespace GameTheory

universe u v

variable {ι : Type u} {A : Type v}

/-- `r` is a **strict linear order** ("ranking") on `A`: irreflexive, transitive, and total
on distinct elements. Together these give asymmetry and trichotomy, so this is exactly a
strict total order. Read `r a b` as "`a` is strictly preferred to `b`". -/
structure IsRanking (r : PrefRel A) : Prop where
  irrefl : ∀ a, ¬ r a a
  trans : ∀ {a b c}, r a b → r b c → r a c
  total : ∀ a b, a ≠ b → r a b ∨ r b a

/-- The strict relation of any linear order is a ranking. -/
theorem isRanking_lt [LinearOrder A] : IsRanking ((· < ·) : PrefRel A) :=
  ⟨lt_irrefl, fun hab hbc => lt_trans hab hbc, fun _ _ hab => lt_or_gt_of_ne hab⟩

/-- Every type admits a ranking. This is classical and uses a well-order of the type. -/
theorem exists_ranking (A : Type v) : ∃ r : PrefRel A, IsRanking r := by
  letI : LinearOrder A := WellOrderingRel.isWellOrder.linearOrder
  exact ⟨(· < ·), isRanking_lt⟩

/-- `A` has at least three alternatives. The second conjunct is the form used by Arrow's
proof: outside every (possibly repeated) pair there is a third alternative. -/
def HasAtLeastThree (A : Type v) : Prop :=
  Nonempty A ∧ ∀ a b : A, ∃ c, c ≠ a ∧ c ≠ b

/-- The proof-oriented definition of `HasAtLeastThree` is equivalent to the usual existence of
three pairwise distinct alternatives. -/
theorem hasAtLeastThree_iff_exists : HasAtLeastThree A ↔
    ∃ a b c : A, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  classical
  constructor
  · rintro ⟨⟨a⟩, hthird⟩
    obtain ⟨b, hba, _⟩ := hthird a a
    obtain ⟨c, hca, hcb⟩ := hthird a b
    exact ⟨a, b, c, Ne.symm hba, Ne.symm hca, Ne.symm hcb⟩
  · rintro ⟨a, b, c, hab, hac, hbc⟩
    refine ⟨⟨a⟩, fun u v => ?_⟩
    by_contra h
    push Not at h
    have hsub : ({a, b, c} : Finset A) ⊆ {u, v} := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      rcases hw with hwa | hwb | hwc
      · subst w
        exact (eq_or_ne a u).elim Or.inl (fun hau => Or.inr (h a hau))
      · subst w
        exact (eq_or_ne b u).elim Or.inl (fun hbu => Or.inr (h b hbu))
      · subst w
        exact (eq_or_ne c u).elim Or.inl (fun hcu => Or.inr (h c hcu))
    have hle := Finset.card_le_card hsub
    have h3 : ({a, b, c} : Finset A).card = 3 := by
      simp [hab, hac, hbc]
    have h2 : ({u, v} : Finset A).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    omega

/-- A finite type of cardinality at least three has at least three alternatives. -/
theorem hasAtLeastThree_of_natCard [Finite A] (hcard : 2 < Nat.card A) :
    HasAtLeastThree A := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  have hcard' : 2 < Fintype.card A := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  constructor
  · exact Fintype.card_pos_iff.mp (by omega)
  · intro u v
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset A) ⊆ {u, v} := by
      intro w _
      rcases eq_or_ne w u with rfl | hwu
      · exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (h w hwu))
    have hle := Finset.card_le_card hsub
    rw [Finset.card_univ] at hle
    have h2 : ({u, v} : Finset A).card ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)
    omega

/-- On finite types, `HasAtLeastThree` is equivalent to the expected cardinal inequality. -/
theorem hasAtLeastThree_iff_natCard [Finite A] :
    HasAtLeastThree A ↔ 2 < Nat.card A := by
  constructor
  · intro hA
    classical
    letI : Fintype A := Fintype.ofFinite A
    obtain ⟨a, b, c, hab, hac, hbc⟩ := hasAtLeastThree_iff_exists.mp hA
    have hsub : ({a, b, c} : Finset A) ⊆ Finset.univ := fun _ _ => Finset.mem_univ _
    have hle := Finset.card_le_card hsub
    have h3 : ({a, b, c} : Finset A).card = 3 := by
      simp [hab, hac, hbc]
    rw [h3, Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
    omega
  · exact hasAtLeastThree_of_natCard

namespace IsRanking

variable {r : PrefRel A} {a b c : A}

/-- A strict linear order is asymmetric. -/
theorem asymm (h : IsRanking r) (hab : r a b) : ¬ r b a :=
  fun hba => h.irrefl a (h.trans hab hba)

/-- Related elements are distinct. -/
theorem ne_of_rel (h : IsRanking r) (hab : r a b) : a ≠ b := by
  rintro rfl; exact h.irrefl a hab

/-- Trichotomy: for distinct elements, `¬ r a b ↔ r b a`. -/
theorem not_iff (h : IsRanking r) (hab : a ≠ b) : ¬ r a b ↔ r b a := by
  constructor
  · intro hn
    rcases h.total a b hab with h1 | h1
    · exact absurd h1 hn
    · exact h1
  · exact fun h1 => h.asymm h1

/-- For distinct elements, the relation is decided one way or the other. -/
theorem rel_or (h : IsRanking r) (hab : a ≠ b) : r a b ∨ r b a := h.total a b hab

end IsRanking

/-! ### Repositioning an alternative

Geanakoplos's proof builds profiles by moving a fixed alternative `b` to the top or bottom
of a ranking while leaving the order among the other alternatives untouched. -/

/-- Move `b` to the **top** of `r`: `b` is strictly above every other element, and the order
among the remaining elements is unchanged. -/
def putTop (b : A) (r : PrefRel A) : PrefRel A :=
  fun x y => (x = b ∧ y ≠ b) ∨ (x ≠ b ∧ y ≠ b ∧ r x y)

/-- Move `b` to the **bottom** of `r`. -/
def putBot (b : A) (r : PrefRel A) : PrefRel A :=
  fun x y => (y = b ∧ x ≠ b) ∨ (x ≠ b ∧ y ≠ b ∧ r x y)

variable {r : PrefRel A} {b x y : A}

/-- After `putTop`, `b` is strictly above every other element. -/
theorem putTop_top (h : x ≠ b) : putTop b r b x := Or.inl ⟨rfl, h⟩

/-- After `putTop`, nothing is strictly above `b`. -/
theorem putTop_not_above : ¬ putTop b r x b := by
  rintro (⟨_, hb⟩ | ⟨_, hb, _⟩) <;> exact hb rfl

/-- `putTop` does not change the order among elements other than `b`. -/
theorem putTop_others (hx : x ≠ b) (hy : y ≠ b) : putTop b r x y ↔ r x y := by
  constructor
  · rintro (⟨hxb, _⟩ | ⟨_, _, h⟩)
    · exact absurd hxb hx
    · exact h
  · exact fun h => Or.inr ⟨hx, hy, h⟩

/-- After `putBot`, every other element is strictly above `b`. -/
theorem putBot_bot (h : x ≠ b) : putBot b r x b := Or.inl ⟨rfl, h⟩

/-- After `putBot`, `b` is strictly below every other element. -/
theorem putBot_not_below : ¬ putBot b r b y := by
  rintro (⟨_, hb⟩ | ⟨hb, _, _⟩) <;> exact hb rfl

/-- `putBot` does not change the order among elements other than `b`. -/
theorem putBot_others (hx : x ≠ b) (hy : y ≠ b) : putBot b r x y ↔ r x y := by
  constructor
  · rintro (⟨hyb, _⟩ | ⟨_, _, h⟩)
    · exact absurd hyb hy
    · exact h
  · exact fun h => Or.inr ⟨hx, hy, h⟩

/-- `putTop` of a ranking is a ranking. -/
theorem IsRanking.putTop (h : IsRanking r) (b : A) : IsRanking (GameTheory.putTop b r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rintro (⟨rfl, hb⟩ | ⟨_, _, hr⟩)
    · exact hb rfl
    · exact h.irrefl a hr
  · intro x y z hxy hyz
    rcases hxy with ⟨rfl, hyb⟩ | ⟨hxb, hyb, hrxy⟩
    · rcases hyz with ⟨hyb', _⟩ | ⟨_, hzb, _⟩
      · exact absurd hyb' hyb
      · exact Or.inl ⟨rfl, hzb⟩
    · rcases hyz with ⟨hyb', _⟩ | ⟨_, hzb, hryz⟩
      · exact absurd hyb' hyb
      · exact Or.inr ⟨hxb, hzb, h.trans hrxy hryz⟩
  · intro x y hxy
    by_cases hxb : x = b
    · subst hxb
      exact Or.inl (Or.inl ⟨rfl, fun h => hxy h.symm⟩)
    · by_cases hyb : y = b
      · subst hyb
        exact Or.inr (Or.inl ⟨rfl, hxb⟩)
      · rw [putTop_others hxb hyb, putTop_others hyb hxb]
        exact h.total x y hxy

/-- `putBot` of a ranking is a ranking. -/
theorem IsRanking.putBot (h : IsRanking r) (b : A) : IsRanking (GameTheory.putBot b r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rintro (⟨rfl, hb⟩ | ⟨_, _, hr⟩)
    · exact hb rfl
    · exact h.irrefl a hr
  · intro x y z hxy hyz
    rcases hyz with ⟨rfl, hyb⟩ | ⟨hyb, hzb, hryz⟩
    · rcases hxy with ⟨hxb', _⟩ | ⟨hxb, _, _⟩
      · exact absurd hxb' hyb
      · exact Or.inl ⟨rfl, hxb⟩
    · rcases hxy with ⟨hxb', _⟩ | ⟨hxb, _, hrxy⟩
      · exact absurd hxb' hyb
      · exact Or.inr ⟨hxb, hzb, h.trans hrxy hryz⟩
  · intro x y hxy
    by_cases hyb : y = b
    · subst hyb
      exact Or.inl (Or.inl ⟨rfl, hxy⟩)
    · by_cases hxb : x = b
      · subst hxb
        exact Or.inr (Or.inl ⟨rfl, fun h => hxy h.symm⟩)
      · rw [putBot_others hxb hyb, putBot_others hyb hxb]
        exact h.total x y hxy

/-! ### Extremal alternatives

`b` is *extremal* in `r` if it sits at the very top or the very bottom. The key fact is that
when `b` is extremal, its comparison with any other element is forced, so swapping two other
elements never disturbs the comparisons involving `b`. -/

/-- `b` is at an extreme (top or bottom) of `r`. -/
def IsExtremal (b : A) (r : PrefRel A) : Prop :=
  (∀ x, x ≠ b → r b x) ∨ (∀ x, x ≠ b → r x b)

/-- If `b` is extremal then its comparisons with `a` and with `c` move together: `r c b ↔ r a b`
and `r b c ↔ r b a`. (Both pairs are simultaneously true, at the bottom, or false, at the top.) -/
theorem IsExtremal.compare {r : PrefRel A} {a b c : A} (hext : IsExtremal b r) (h : IsRanking r)
    (hba : b ≠ a) (hbc : b ≠ c) : (r c b ↔ r a b) ∧ (r b c ↔ r b a) := by
  rcases hext with htop | hbot
  · exact ⟨iff_of_false (h.asymm (htop c (Ne.symm hbc))) (h.asymm (htop a (Ne.symm hba))),
      iff_of_true (htop c (Ne.symm hbc)) (htop a (Ne.symm hba))⟩
  · exact ⟨iff_of_true (hbot c (Ne.symm hbc)) (hbot a (Ne.symm hba)),
      iff_of_false (h.asymm (hbot c (Ne.symm hbc))) (h.asymm (hbot a (Ne.symm hba)))⟩

/-! ### Forcing one alternative above another

To prove the extremal lemma we modify a profile so that `c` is strictly above `a` for every
voter, *without* disturbing any comparison with the extremal alternative `b`. -/

/-- Pull back `r` along the transposition of `a` and `c`: `r` with the roles of `a` and `c`
exchanged. -/
def swapPref [DecidableEq A] (a c : A) (r : PrefRel A) : PrefRel A :=
  fun x y => r (Equiv.swap a c x) (Equiv.swap a c y)

/-- The transposition pullback of a ranking is a ranking. -/
theorem IsRanking.swapPref [DecidableEq A] {r : PrefRel A} (h : IsRanking r) (a c : A) :
    IsRanking (GameTheory.swapPref a c r) :=
  ⟨fun _ => h.irrefl _, fun hxy hyz => h.trans hxy hyz,
    fun _ _ hxy => h.total _ _ ((Equiv.swap a c).injective.ne hxy)⟩

open Classical in
/-- Make `c` strictly preferred to `a`, by swapping `a` and `c` exactly when `r` ranks `a`
above `c`. The result always has `c` above `a`; when `b ∉ {a, c}` is extremal in `r`, every
comparison with `b` is preserved. -/
noncomputable def forceAbove [DecidableEq A] (a c : A) (r : PrefRel A) : PrefRel A :=
  if r a c then swapPref a c r else r

/-- `forceAbove` of a ranking is a ranking. -/
theorem IsRanking.forceAbove [DecidableEq A] {r : PrefRel A} (h : IsRanking r) (a c : A) :
    IsRanking (GameTheory.forceAbove a c r) := by
  unfold GameTheory.forceAbove
  split
  · exact h.swapPref a c
  · exact h

/-- `forceAbove` puts `c` strictly above `a`. -/
theorem forceAbove_forces [DecidableEq A] {r : PrefRel A} {a c : A} (h : IsRanking r)
    (hac : a ≠ c) : forceAbove a c r c a := by
  unfold forceAbove
  split
  · rename_i hr
    simp only [swapPref, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact hr
  · rename_i hnr
    exact (h.total c a (Ne.symm hac)).resolve_right hnr

/-- `forceAbove` preserves all comparisons with an extremal `b ∉ {a, c}`. -/
theorem forceAbove_agree [DecidableEq A] {r : PrefRel A} {a b c : A} (h : IsRanking r)
    (hba : b ≠ a) (hbc : b ≠ c) (hext : IsExtremal b r) :
    (forceAbove a c r a b ↔ r a b) ∧ (forceAbove a c r b a ↔ r b a) ∧
    (forceAbove a c r b c ↔ r b c) ∧ (forceAbove a c r c b ↔ r c b) := by
  obtain ⟨hcb, hbc'⟩ := hext.compare h hba hbc
  unfold forceAbove
  split
  · have sab : swapPref a c r a b = r c b := by
      simp only [swapPref, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hba hbc]
    have sba : swapPref a c r b a = r b c := by
      simp only [swapPref, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hba hbc]
    have sbc : swapPref a c r b c = r b a := by
      simp only [swapPref, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hba hbc]
    have scb : swapPref a c r c b = r a b := by
      simp only [swapPref, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hba hbc]
    rw [sab, sba, sbc, scb]
    exact ⟨hcb, hbc', hbc'.symm, hcb.symm⟩
  · exact ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

/-! ### Collective rationality and the extremal lemma -/

namespace SWF

/-- A social welfare function is **collectively rational** (a social welfare *ordering*) if it
maps every profile of rankings to a ranking. This is the requirement absent from the bare
`SWF` type that makes Arrow's theorem statable. -/
def IsSWO (f : SWF ι A) : Prop :=
  ∀ R : PrefProfile ι A, (∀ i, IsRanking (R i)) → IsRanking (f R)

/-- **Weak Pareto on the domain of rankings.** If every voter — whose preference is a ranking —
strictly prefers `a` to `b`, then so does society. This is Arrow's Pareto axiom on its *proper*
domain: the unrestricted domain of *admissible* (ranked) preferences, not of arbitrary binary
relations. -/
def IsParetoOnRankings (f : SWF ι A) : Prop :=
  ∀ R : PrefProfile ι A, (∀ i, IsRanking (R i)) → ∀ a b, (∀ i, R i a b) → f R a b

/-- **Independence of irrelevant alternatives on the domain of rankings.** The social ranking of
`a` vs `b` depends only on the individual rankings of `a` vs `b`, across ranking profiles. -/
def IsIIAOnRankings (f : SWF ι A) : Prop :=
  ∀ R R' : PrefProfile ι A, (∀ i, IsRanking (R i)) → (∀ i, IsRanking (R' i)) →
    ∀ a b, (∀ i, (R i a b ↔ R' i a b) ∧ (R i b a ↔ R' i b a)) →
      (f R a b ↔ f R' a b) ∧ (f R b a ↔ f R' b a)

/-- The unrestricted weak-Pareto axiom implies its restriction to ranking profiles. -/
theorem IsPareto.onRankings {f : SWF ι A} (h : f.IsPareto) : f.IsParetoOnRankings :=
  fun R hR a b hab => (h R a b fun i => ⟨hab i, (hR i).asymm (hab i)⟩).1

/-- The unrestricted IIA axiom implies its restriction to ranking profiles. -/
theorem IsIIA.onRankings {f : SWF ι A} (h : f.IsIIA) : f.IsIIAOnRankings :=
  fun R R' _ _ a b hyp => h R R' a b hyp

end SWF

/-- **Extremal lemma.** For a collectively rational SWF satisfying weak Pareto and IIA: if every
voter ranks `b` at an extreme (top or bottom), then society ranks `b` at an extreme. -/
theorem extremal_lemma {f : SWF ι A} (hswo : f.IsSWO) (hp : f.IsParetoOnRankings)
    (hiia : f.IsIIAOnRankings) {b : A} {R : PrefProfile ι A} (hR : ∀ i, IsRanking (R i))
    (hb : ∀ i, IsExtremal b (R i)) : IsExtremal b (f R) := by
  classical
  by_contra hcon
  have hsR : IsRanking (f R) := hswo R hR
  unfold IsExtremal at hcon
  push Not at hcon
  obtain ⟨⟨a, hab, hnba⟩, ⟨c, hcb, hncb⟩⟩ := hcon
  have hsab : f R a b := (hsR.not_iff (Ne.symm hab)).mp hnba
  have hsbc : f R b c := (hsR.not_iff hcb).mp hncb
  have hac : a ≠ c := by rintro rfl; exact hsR.asymm hsab hsbc
  let R' : PrefProfile ι A := fun i => forceAbove a c (R i)
  have hR' : ∀ i, IsRanking (R' i) := fun i => (hR i).forceAbove a c
  have hca : f R' c a := hp R' hR' c a (fun i => forceAbove_forces (hR i) hac)
  have hnac : ¬ f R' a c := (hswo R' hR').asymm hca
  have hiiaAB := hiia R R' hR hR' a b (fun i => by
    obtain ⟨t1, t2, _, _⟩ := forceAbove_agree (hR i) (Ne.symm hab) (Ne.symm hcb) (hb i)
    exact ⟨t1.symm, t2.symm⟩)
  have hiiaBC := hiia R R' hR hR' b c (fun i => by
    obtain ⟨_, _, t3, t4⟩ := forceAbove_agree (hR i) (Ne.symm hab) (Ne.symm hcb) (hb i)
    exact ⟨t3.symm, t4.symm⟩)
  have hfab : f R' a b := hiiaAB.1.mp hsab
  have hfbc : f R' b c := hiiaBC.1.mp hsbc
  exact hnac ((hswo R' hR').trans hfab hfbc)

/-! ### The pivotal profiles and dictatorship -/

/-- `f` makes `d` **decisive** for the ordered pair `(x, y)` on rankings: whenever `d` ranks
`x` strictly above `y`, society does too — regardless of the other voters. -/
def Decides (f : SWF ι A) (d : ι) (x y : A) : Prop :=
  ∀ Q : PrefProfile ι A, (∀ i, IsRanking (Q i)) → Q d x y → f Q x y

/-- A voter `d` is a **dictator** on ranking profiles: decisive for every ordered pair. -/
def SWF.IsDictatorOnRankings (f : SWF ι A) (d : ι) : Prop :=
  ∀ x y : A, Decides f d x y

variable [DecidableEq ι]

/-- The pivotal profile for `b` over a coalition `S`: voters in `S` rank `b` at the top, the
rest rank `b` at the bottom; the background order `ρ` is shared. -/
def piv (b : A) (ρ : PrefRel A) (S : Finset ι) : PrefProfile ι A :=
  fun i => if i ∈ S then putTop b ρ else putBot b ρ

/-- A voter inside `S` ranks `b` at the top in `piv`. -/
theorem piv_mem {b : A} {ρ : PrefRel A} {S : Finset ι} {i : ι} (h : i ∈ S) :
    piv b ρ S i = putTop b ρ := if_pos h

/-- A voter outside `S` ranks `b` at the bottom in `piv`. -/
theorem piv_not_mem {b : A} {ρ : PrefRel A} {S : Finset ι} {i : ι} (h : i ∉ S) :
    piv b ρ S i = putBot b ρ := if_neg h

/-- Every voter's preference in `piv` is a ranking. -/
theorem piv_ranking {b : A} {ρ : PrefRel A} (hρ : IsRanking ρ) (S : Finset ι) (i : ι) :
    IsRanking (piv b ρ S i) := by
  unfold piv; split
  · exact hρ.putTop b
  · exact hρ.putBot b

/-- In `piv`, `b` is extremal for every voter. -/
theorem piv_extremal {b : A} {ρ : PrefRel A} (S : Finset ι) (i : ι) :
    IsExtremal b (piv b ρ S i) := by
  unfold piv; split
  · exact Or.inl fun _ hx => putTop_top hx
  · exact Or.inr fun _ hx => putBot_bot hx

/-- The witness profile for the pivotal voter `p` being decisive over `(x, y)`: `p` ranks
`x ≻ b ≻ y`, voters in `T0` rank `b` at the top of their `Q`-order, the rest at the bottom. -/
def starProfile (b x y : A) (ρ : PrefRel A) (Q : PrefProfile ι A) (p : ι) (T0 : Finset ι) :
    PrefProfile ι A :=
  fun i => if i = p then putBot y (putTop x ρ)
           else if i ∈ T0 then putTop b (Q i) else putBot b (Q i)

theorem starProfile_p {b x y : A} {ρ : PrefRel A} {Q : PrefProfile ι A} {p : ι} {T0 : Finset ι} :
    starProfile b x y ρ Q p T0 p = putBot y (putTop x ρ) := if_pos rfl

theorem starProfile_mem {b x y : A} {ρ : PrefRel A} {Q : PrefProfile ι A} {p i : ι}
    {T0 : Finset ι} (hip : i ≠ p) (hiT : i ∈ T0) :
    starProfile b x y ρ Q p T0 i = putTop b (Q i) := by
  rw [starProfile, if_neg hip, if_pos hiT]

theorem starProfile_not_mem {b x y : A} {ρ : PrefRel A} {Q : PrefProfile ι A} {p i : ι}
    {T0 : Finset ι} (hip : i ≠ p) (hiT : i ∉ T0) :
    starProfile b x y ρ Q p T0 i = putBot b (Q i) := by
  rw [starProfile, if_neg hip, if_neg hiT]

/-- **Dictator extraction.** If, over the pivotal coalition `T0` (which excludes the pivotal
voter `p`), society puts `b` at the bottom and putting `p` in too lifts `b` to the top, then `p`
is decisive over every ordered pair `(x, y)` of alternatives different from `b`. -/
theorem dictator_pair {f : SWF ι A} (hswo : f.IsSWO) (hiia : f.IsIIAOnRankings)
    {b : A} {ρ : PrefRel A} (hρ : IsRanking ρ) {p : ι} {T0 : Finset ι} (hp0 : p ∉ T0)
    (hbot : ∀ z, z ≠ b → f (piv b ρ T0) z b)
    (htop : ∀ z, z ≠ b → f (piv b ρ (insert p T0)) b z)
    {x y : A} (hxb : x ≠ b) (hyb : y ≠ b) (hxy : x ≠ y) : Decides f p x y := by
  intro Q hQ hQp
  set R := starProfile b x y ρ Q p T0 with hRdef
  have hRp : R p = putBot y (putTop x ρ) := by rw [hRdef]; exact starProfile_p
  -- relations of the pivotal voter's special ranking `x ≻ b ≻ y`
  have e1 : putBot y (putTop x ρ) x b :=
    (putBot_others hxy (Ne.symm hyb)).mpr (putTop_top (Ne.symm hxb))
  have e2 : ¬ putBot y (putTop x ρ) b x :=
    fun h => putTop_not_above ((putBot_others (Ne.symm hyb) hxy).mp h)
  have e3 : putBot y (putTop x ρ) b y := putBot_bot (Ne.symm hyb)
  have e4 : ¬ putBot y (putTop x ρ) y b := putBot_not_below
  have e5 : putBot y (putTop x ρ) x y := putBot_bot hxy
  have e6 : ¬ putBot y (putTop x ρ) y x := putBot_not_below
  -- `R` is a profile of rankings
  have hRprof : ∀ i, IsRanking (R i) := by
    intro i
    by_cases hip : i = p
    · rw [hip, hRp]; exact (hρ.putTop x).putBot y
    · by_cases hiT : i ∈ T0
      · rw [hRdef, starProfile_mem hip hiT]; exact (hQ i).putTop b
      · rw [hRdef, starProfile_not_mem hip hiT]; exact (hQ i).putBot b
  -- agreement with `piv T0` on the pair `{x, b}`
  have hAxb : ∀ i, (R i x b ↔ piv b ρ T0 i x b) ∧ (R i b x ↔ piv b ρ T0 i b x) := by
    intro i
    by_cases hip : i = p
    · rw [hip, hRp, piv_not_mem hp0]
      exact ⟨iff_of_true e1 (putBot_bot hxb), iff_of_false e2 putBot_not_below⟩
    · by_cases hiT : i ∈ T0
      · rw [hRdef, starProfile_mem hip hiT, piv_mem hiT]
        exact ⟨iff_of_false putTop_not_above putTop_not_above,
          iff_of_true (putTop_top hxb) (putTop_top hxb)⟩
      · rw [hRdef, starProfile_not_mem hip hiT, piv_not_mem hiT]
        exact ⟨iff_of_true (putBot_bot hxb) (putBot_bot hxb),
          iff_of_false putBot_not_below putBot_not_below⟩
  -- agreement with `piv (insert p T0)` on the pair `{b, y}`
  have hAby : ∀ i, (R i b y ↔ piv b ρ (insert p T0) i b y) ∧
      (R i y b ↔ piv b ρ (insert p T0) i y b) := by
    intro i
    by_cases hip : i = p
    · rw [hip, hRp, piv_mem (Finset.mem_insert_self p T0)]
      exact ⟨iff_of_true e3 (putTop_top hyb), iff_of_false e4 putTop_not_above⟩
    · by_cases hiT : i ∈ T0
      · rw [hRdef, starProfile_mem hip hiT, piv_mem (Finset.mem_insert_of_mem hiT)]
        exact ⟨iff_of_true (putTop_top hyb) (putTop_top hyb),
          iff_of_false putTop_not_above putTop_not_above⟩
      · have hni : i ∉ insert p T0 := fun h => (Finset.mem_insert.mp h).elim hip hiT
        rw [hRdef, starProfile_not_mem hip hiT, piv_not_mem hni]
        exact ⟨iff_of_false putBot_not_below putBot_not_below,
          iff_of_true (putBot_bot hyb) (putBot_bot hyb)⟩
  -- agreement with `Q` on the pair `{x, y}`
  have hAxy : ∀ i, (R i x y ↔ Q i x y) ∧ (R i y x ↔ Q i y x) := by
    intro i
    by_cases hip : i = p
    · rw [hip, hRp]
      exact ⟨iff_of_true e5 hQp, iff_of_false e6 ((hQ p).asymm hQp)⟩
    · by_cases hiT : i ∈ T0
      · rw [hRdef, starProfile_mem hip hiT]
        exact ⟨putTop_others hxb hyb, putTop_others hyb hxb⟩
      · rw [hRdef, starProfile_not_mem hip hiT]
        exact ⟨putBot_others hxb hyb, putBot_others hyb hxb⟩
  -- assemble: x ≻ b and b ≻ y socially, hence x ≻ y, transferred back to `Q`
  have hfxb : f R x b :=
    ((hiia R (piv b ρ T0) hRprof (piv_ranking hρ T0) x b hAxb).1).mpr (hbot x hxb)
  have hfby : f R b y :=
    ((hiia R (piv b ρ (insert p T0)) hRprof (piv_ranking hρ (insert p T0)) b y hAby).1).mpr
      (htop y hyb)
  have hfxy : f R x y := (hswo R hRprof).trans hfxb hfby
  exact ((hiia R Q hRprof hQ x y hAxy).1).mp hfxy

/-! ### Field expansion to pairs involving `b`

A voter decisive over every pair avoiding `b` is in fact decisive over the pairs `(x, b)` and
`(b, x)` too, and hence is a full dictator. -/

/-- Witness profile for extending decisiveness to `(x, b)`: `p` ranks `x ≻ y ≻ b`, every other
voter ranks `y` at the top (so all have `y ≻ b`). -/
def xbProfile (b x y : A) (Q : PrefProfile ι A) (p : ι) : PrefProfile ι A :=
  fun i => if i = p then putBot b (putTop x (Q p)) else putTop y (Q i)

/-- Witness profile for extending decisiveness to `(b, x)`: `p` ranks `b ≻ y ≻ x`, every other
voter ranks `y` at the bottom (so all have `b ≻ y`). -/
def bxProfile (b x y : A) (Q : PrefProfile ι A) (p : ι) : PrefProfile ι A :=
  fun i => if i = p then putTop b (putBot x (Q p)) else putBot y (Q i)

theorem xbProfile_p {b x y : A} {Q : PrefProfile ι A} {p : ι} :
    xbProfile b x y Q p p = putBot b (putTop x (Q p)) := if_pos rfl

theorem xbProfile_ne {b x y : A} {Q : PrefProfile ι A} {p i : ι} (hip : i ≠ p) :
    xbProfile b x y Q p i = putTop y (Q i) := if_neg hip

theorem bxProfile_p {b x y : A} {Q : PrefProfile ι A} {p : ι} :
    bxProfile b x y Q p p = putTop b (putBot x (Q p)) := if_pos rfl

theorem bxProfile_ne {b x y : A} {Q : PrefProfile ι A} {p i : ι} (hip : i ≠ p) :
    bxProfile b x y Q p i = putBot y (Q i) := if_neg hip

omit [DecidableEq ι] in
/-- A voter decisive over all `b`-avoiding pairs is decisive over `(x, b)` as well. -/
theorem dictator_xb {f : SWF ι A} (hswo : f.IsSWO) (hp : f.IsParetoOnRankings)
    (hiia : f.IsIIAOnRankings)
    {b : A} {p : ι} (hdict : ∀ u v, u ≠ b → v ≠ b → u ≠ v → Decides f p u v)
    {x y : A} (hxb : x ≠ b) (hyb : y ≠ b) (hyx : y ≠ x) : Decides f p x b := by
  classical
  intro Q hQ hQp
  set S := xbProfile b x y Q p with hSdef
  have hSp : S p = putBot b (putTop x (Q p)) := by rw [hSdef]; exact xbProfile_p
  have hSprof : ∀ i, IsRanking (S i) := by
    intro i
    by_cases hip : i = p
    · rw [hip, hSp]; exact ((hQ p).putTop x).putBot b
    · rw [hSdef, xbProfile_ne hip]; exact (hQ i).putTop y
  have hyb_all : ∀ i, S i y b := by
    intro i
    by_cases hip : i = p
    · rw [hip, hSp]; exact putBot_bot hyb
    · rw [hSdef, xbProfile_ne hip]; exact putTop_top (Ne.symm hyb)
  have hxy_p : S p x y := by
    rw [hSp]; exact (putBot_others hxb hyb).mpr (putTop_top hyx)
  have hSyb : f S y b := hp S hSprof y b hyb_all
  have hSxy : f S x y := hdict x y hxb hyb (Ne.symm hyx) S hSprof hxy_p
  have hSxb : f S x b := (hswo S hSprof).trans hSxy hSyb
  have hAgree : ∀ i, (S i x b ↔ Q i x b) ∧ (S i b x ↔ Q i b x) := by
    intro i
    by_cases hip : i = p
    · rw [hip, hSp]
      exact ⟨iff_of_true (putBot_bot hxb) hQp,
        iff_of_false putBot_not_below ((hQ p).asymm hQp)⟩
    · rw [hSdef, xbProfile_ne hip]
      exact ⟨putTop_others (Ne.symm hyx) (Ne.symm hyb),
        putTop_others (Ne.symm hyb) (Ne.symm hyx)⟩
  exact ((hiia S Q hSprof hQ x b hAgree).1).mp hSxb

omit [DecidableEq ι] in
/-- A voter decisive over all `b`-avoiding pairs is decisive over `(b, x)` as well. -/
theorem dictator_bx {f : SWF ι A} (hswo : f.IsSWO) (hp : f.IsParetoOnRankings)
    (hiia : f.IsIIAOnRankings)
    {b : A} {p : ι} (hdict : ∀ u v, u ≠ b → v ≠ b → u ≠ v → Decides f p u v)
    {x y : A} (hxb : x ≠ b) (hyb : y ≠ b) (hyx : y ≠ x) : Decides f p b x := by
  classical
  intro Q hQ hQp
  set S := bxProfile b x y Q p with hSdef
  have hSp : S p = putTop b (putBot x (Q p)) := by rw [hSdef]; exact bxProfile_p
  have hSprof : ∀ i, IsRanking (S i) := by
    intro i
    by_cases hip : i = p
    · rw [hip, hSp]; exact ((hQ p).putBot x).putTop b
    · rw [hSdef, bxProfile_ne hip]; exact (hQ i).putBot y
  have hby_all : ∀ i, S i b y := by
    intro i
    by_cases hip : i = p
    · rw [hip, hSp]; exact putTop_top hyb
    · rw [hSdef, bxProfile_ne hip]; exact putBot_bot (Ne.symm hyb)
  have hyx_p : S p y x := by
    rw [hSp]; exact (putTop_others hyb hxb).mpr (putBot_bot hyx)
  have hSby : f S b y := hp S hSprof b y hby_all
  have hSyx : f S y x := hdict y x hyb hxb hyx S hSprof hyx_p
  have hSbx : f S b x := (hswo S hSprof).trans hSby hSyx
  have hAgree : ∀ i, (S i b x ↔ Q i b x) ∧ (S i x b ↔ Q i x b) := by
    intro i
    by_cases hip : i = p
    · rw [hip, hSp]
      exact ⟨iff_of_true (putTop_top hxb) hQp,
        iff_of_false putTop_not_above ((hQ p).asymm hQp)⟩
    · rw [hSdef, bxProfile_ne hip]
      exact ⟨putBot_others (Ne.symm hyb) (Ne.symm hyx),
        putBot_others (Ne.symm hyx) (Ne.symm hyb)⟩
  exact ((hiia S Q hSprof hQ b x hAgree).1).mp hSbx

/-! ### Arrow's impossibility theorem -/

omit [DecidableEq ι] in
/-- **Arrow's impossibility theorem.** With at least three alternatives and a nonempty finite
electorate, every collectively rational social welfare function satisfying weak Pareto and
independence of irrelevant alternatives (both on the domain of rankings) is dictatorial.

The alternative type need not be finite. `HasAtLeastThree` is exactly the cardinality property
used by the proof, while finiteness is essential only for the pivotal-coalition argument over
the electorate.

`[Nonempty ι]` fixes the meaningful regime. With no voters the conclusion `∃ d` is
unsatisfiable, and indeed `IsSWO` together with `IsParetoOnRankings` is then jointly
inconsistent (Pareto vacuously forces `f R a a`, contradicting irreflexivity), so the statement
would otherwise hold only vacuously. -/
theorem arrow_impossibility [Nonempty ι] [Finite ι] {f : SWF ι A} (hswo : f.IsSWO)
    (hp : f.IsParetoOnRankings) (hiia : f.IsIIAOnRankings) (hA : HasAtLeastThree A) :
    ∃ d, f.IsDictatorOnRankings d := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨hAne, hthird⟩ := hA
  -- a reference alternative `b` and a background ranking `ρ`
  obtain ⟨b⟩ := hAne
  obtain ⟨ρ, hρ⟩ := exists_ranking A
  -- "society puts `b` at the top / bottom" as a predicate on coalitions
  let atTop : Finset ι → Prop := fun S => ∀ x, x ≠ b → f (piv b ρ S) b x
  let atBot : Finset ι → Prop := fun S => ∀ x, x ≠ b → f (piv b ρ S) x b
  have atTop_univ : atTop Finset.univ := fun x hx =>
    hp (piv b ρ Finset.univ) (piv_ranking hρ Finset.univ) b x (fun i => by
      rw [piv_mem (Finset.mem_univ i)]; exact putTop_top hx)
  have atBot_empty : atBot ∅ := fun x hx =>
    hp (piv b ρ ∅) (piv_ranking hρ ∅) x b (fun i => by
      rw [piv_not_mem (by simp)]; exact putBot_bot hx)
  -- a minimal-cardinality coalition that lifts `b` to the top
  have hne : (Finset.univ.filter atTop).Nonempty :=
    ⟨Finset.univ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, atTop_univ⟩⟩
  obtain ⟨T, hTmem, hTmin⟩ := Finset.exists_min_image _ Finset.card hne
  have hTtop : atTop T := (Finset.mem_filter.mp hTmem).2
  have hTne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hTe
    obtain ⟨x, hxb, _⟩ := hthird b b
    exact (hswo _ (piv_ranking hρ ∅)).asymm (hTe ▸ hTtop x hxb) (atBot_empty x hxb)
  obtain ⟨p, hpT⟩ := hTne
  set T0 := T.erase p with hT0
  have hp0 : p ∉ T0 := by rw [hT0]; simp
  have hinsert : insert p T0 = T := by rw [hT0]; exact Finset.insert_erase hpT
  have hT0_lt : T0.card < T.card := by rw [hT0]; exact Finset.card_erase_lt_of_mem hpT
  -- below the pivot `b` is no longer on top, hence (being extremal) it is on the bottom
  have hT0_notTop : ¬ atTop T0 := fun hcon => by
    have := hTmin T0 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcon⟩); omega
  have hT0_bot : atBot T0 := by
    rcases extremal_lemma hswo hp hiia (piv_ranking hρ T0) (piv_extremal T0) with htop | hbot
    · exact absurd htop hT0_notTop
    · exact hbot
  -- the pivot dictates every pair of alternatives different from `b`
  have hdict : ∀ u v, u ≠ b → v ≠ b → u ≠ v → Decides f p u v := fun u v hub hvb huv =>
    dictator_pair hswo hiia hρ hp0 hT0_bot
      (fun z hz => by rw [hinsert]; exact hTtop z hz) hub hvb huv
  -- extend to all pairs and conclude `p` is a dictator
  refine ⟨p, ?_⟩
  intro x y
  by_cases hxb : x = b
  · by_cases hyb : y = b
    · rw [hxb, hyb]; exact fun Q hQ hQbb => absurd hQbb ((hQ p).irrefl _)
    · rw [hxb]
      obtain ⟨w, hwy, hwb⟩ := hthird y b
      exact dictator_bx hswo hp hiia hdict hyb hwb hwy
  · by_cases hyb : y = b
    · rw [hyb]
      obtain ⟨w, hwx, hwb⟩ := hthird x b
      exact dictator_xb hswo hp hiia hdict hxb hwb hwx
    · by_cases hxy : x = y
      · rw [hxy]; exact fun Q hQ hQyy => absurd hQyy ((hQ p).irrefl _)
      · exact hdict x y hxb hyb hxy

omit [DecidableEq ι] in
/-- Finite-cardinality convenience form of Arrow's theorem. The canonical theorem
`arrow_impossibility` also applies to infinite alternative types. -/
theorem arrow_impossibility_of_natCard [Nonempty ι] [Finite ι] [Finite A] {f : SWF ι A}
    (hswo : f.IsSWO) (hp : f.IsParetoOnRankings) (hiia : f.IsIIAOnRankings)
    (hcard : 2 < Nat.card A) : ∃ d, f.IsDictatorOnRankings d :=
  arrow_impossibility hswo hp hiia (hasAtLeastThree_of_natCard hcard)

omit [DecidableEq ι] in
/-- A dictator on rankings determines society's strict preference **exactly**: on every ranking
profile the social ranking coincides with the dictator's. Given collective rationality, the
one-directional `IsDictatorOnRankings` already carries this full biconditional strength — the
reverse direction is the standard argument (if society has `x ≻ y` but the dictator does not,
then the dictator has `y ≻ x`, decisiveness forces society to `y ≻ x`, contradicting asymmetry). -/
theorem SWF.IsDictatorOnRankings.exact {f : SWF ι A} (hswo : f.IsSWO) {d : ι}
    (hd : f.IsDictatorOnRankings d) {Q : PrefProfile ι A} (hQ : ∀ i, IsRanking (Q i))
    (x y : A) : f Q x y ↔ Q d x y := by
  refine ⟨fun hf => ?_, hd x y Q hQ⟩
  by_contra hQd
  rcases eq_or_ne x y with rfl | hxy
  · exact (hswo Q hQ).irrefl x hf
  · exact (hswo Q hQ).asymm hf (hd y x Q hQ (((hQ d).not_iff hxy).mp hQd))

omit [DecidableEq ι] in
/-- **Arrow's impossibility theorem (exact form).** Under the same hypotheses there is a voter
whose strict preference *coincides* with society's on every ranking profile. -/
theorem arrow_impossibility_exact [Nonempty ι] [Finite ι] {f : SWF ι A}
    (hswo : f.IsSWO) (hp : f.IsParetoOnRankings) (hiia : f.IsIIAOnRankings)
    (hA : HasAtLeastThree A) :
    ∃ d, ∀ Q : PrefProfile ι A, (∀ i, IsRanking (Q i)) → ∀ x y, f Q x y ↔ Q d x y := by
  obtain ⟨d, hd⟩ := arrow_impossibility hswo hp hiia hA
  exact ⟨d, fun Q hQ x y => hd.exact hswo hQ x y⟩

omit [DecidableEq ι] in
/-- Finite-cardinality convenience form of exact Arrow dictatorship. -/
theorem arrow_impossibility_exact_of_natCard [Nonempty ι] [Finite ι] [Finite A]
    {f : SWF ι A} (hswo : f.IsSWO) (hp : f.IsParetoOnRankings)
    (hiia : f.IsIIAOnRankings) (hcard : 2 < Nat.card A) :
    ∃ d, ∀ Q : PrefProfile ι A, (∀ i, IsRanking (Q i)) → ∀ x y, f Q x y ↔ Q d x y :=
  arrow_impossibility_exact hswo hp hiia (hasAtLeastThree_of_natCard hcard)

end GameTheory
