/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Voting.Delegation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Fintype.EquivFin

/-!
# Liquid democracy: weights, conservation, and rule composition

Over a finite electorate, a delegation profile accumulates each caster's
*weight* — the number of voters whose delegation chains end at that caster —
and induces the multiset of *effective ballots*, one per non-abstaining voter.
Liquid democracy is then the composition of any anonymous voting rule (a
function of the ballot multiset) with delegation resolution.

## Main definitions

* `DelegationProfile.weight` — voters accumulated by a caster (0 for delegators)
* `DelegationProfile.casters` / `participants` / `guruFiber` / `resolversTo` /
  `castersOf` — the standard electorate subdivisions
* `DelegationProfile.resolvedBallots` — the multiset of effective ballots
* `Voting.liquidExtension` — the liquid-democracy extension of an anonymous rule
* `Voting.directProfile` — the all-cast (direct democracy) profile

## Main results

* `sum_weight_eq_card_participants` — **weight conservation**: total caster
  weight equals the number of non-abstaining voters
* `card_resolversTo_eq_sum_weight` — the supporters of a ballot are counted by
  the weights of its casters
* `resolvedBallots_eq_sum_casters` — **liquid = weighted direct democracy**:
  the effective ballots are each caster's ballot with multiplicity its weight
* `liquidExtension_directProfile` — direct democracy embeds: on all-cast
  profiles the liquid extension is the underlying rule
* `liquidExtension_update_cast` — **copy-robustness**: replacing a delegative
  ballot by a direct cast of its resolved ballot never changes the outcome
-/

namespace GameTheory.Voting

namespace DelegationProfile

variable {ι β : Type*} [Fintype ι] {d : DelegationProfile ι β} {i j k : ι} {b : β}

/-! ### Electorate subdivisions and weights -/

open Classical in
/-- The casters: voters who cast a direct ballot. -/
noncomputable def casters (d : DelegationProfile ι β) : Finset ι :=
  Finset.univ.filter fun j => d.IsCaster j

open Classical in
@[simp] theorem mem_casters : j ∈ d.casters ↔ d.IsCaster j := by
  simp [casters]

open Classical in
/-- The participants: voters whose delegation chain resolves (non-abstainers). -/
noncomputable def participants (d : DelegationProfile ι β) : Finset ι :=
  Finset.univ.filter fun i => ∃ b, d.Resolves i b

open Classical in
@[simp] theorem mem_participants : i ∈ d.participants ↔ ∃ b, d.Resolves i b := by
  simp [participants]

open Classical in
/-- The delegation fiber of `j`: voters whose delegation chain ends at `j`. -/
noncomputable def guruFiber (d : DelegationProfile ι β) (j : ι) : Finset ι :=
  Finset.univ.filter fun i => d.IsGuruOf j i

open Classical in
@[simp] theorem mem_guruFiber : i ∈ d.guruFiber j ↔ d.IsGuruOf j i := by
  simp [guruFiber]

open Classical in
/-- The voters whose chain resolves to ballot `b` (the support of `b`). -/
noncomputable def resolversTo (d : DelegationProfile ι β) (b : β) : Finset ι :=
  Finset.univ.filter fun i => d.Resolves i b

open Classical in
@[simp] theorem mem_resolversTo : i ∈ d.resolversTo b ↔ d.Resolves i b := by
  simp [resolversTo]

open Classical in
/-- The casters of ballot `b`. -/
noncomputable def castersOf (d : DelegationProfile ι β) (b : β) : Finset ι :=
  Finset.univ.filter fun j => d.Casts j b

open Classical in
@[simp] theorem mem_castersOf : j ∈ d.castersOf b ↔ d.Casts j b := by
  simp [castersOf]

/-- The voting weight accumulated by `j`: the number of voters whose delegation
chains end at `j` (including `j` itself when `j` casts). -/
noncomputable def weight (d : DelegationProfile ι β) (j : ι) : ℕ :=
  (d.guruFiber j).card

theorem weight_eq_zero_of_not_isCaster (h : ¬ d.IsCaster j) : d.weight j = 0 := by
  rw [weight, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
  intro i hi
  exact h (mem_guruFiber.mp hi).isCaster

/-- Casters carry at least their own vote. -/
theorem IsCaster.one_le_weight (h : d.IsCaster j) : 1 ≤ d.weight j :=
  Finset.card_pos.mpr ⟨j, mem_guruFiber.mpr h.isGuruOf_self⟩

theorem disjoint_guruFiber (hjk : j ≠ k) :
    Disjoint (d.guruFiber j) (d.guruFiber k) := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  exact hjk ((mem_guruFiber.mp hi).unique (mem_guruFiber.mp hi'))

/-- Grouping voters by guru: the voters resolving into any set `S` of casters
number exactly the total weight of `S`. -/
theorem card_biUnion_guruFiber [DecidableEq ι] (S : Finset ι) :
    (S.biUnion d.guruFiber).card = ∑ j ∈ S, d.weight j :=
  Finset.card_biUnion fun _ _ _ _ hjk => disjoint_guruFiber hjk

theorem participants_eq_biUnion [DecidableEq ι] :
    d.participants = d.casters.biUnion d.guruFiber := by
  ext i
  simp only [mem_participants, Finset.mem_biUnion, mem_casters, mem_guruFiber]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨j, hguru, -⟩ := resolves_iff_exists_guru.mp hb
    exact ⟨j, hguru.isCaster, hguru⟩
  · rintro ⟨j, -, hguru⟩
    obtain ⟨b, hcast⟩ := hguru.isCaster
    exact ⟨b, hguru.resolves hcast⟩

/-- **Weight conservation**: the total weight of the casters equals the number
of non-abstaining voters. -/
theorem sum_weight_eq_card_participants :
    ∑ j ∈ d.casters, d.weight j = d.participants.card := by
  classical
  rw [participants_eq_biUnion, card_biUnion_guruFiber]

theorem resolversTo_eq_biUnion [DecidableEq ι] (b : β) :
    d.resolversTo b = (d.castersOf b).biUnion d.guruFiber := by
  ext i
  simp only [mem_resolversTo, Finset.mem_biUnion, mem_castersOf, mem_guruFiber]
  constructor
  · intro hb
    obtain ⟨j, hguru, hcast⟩ := resolves_iff_exists_guru.mp hb
    exact ⟨j, hcast, hguru⟩
  · rintro ⟨j, hcast, hguru⟩
    exact hguru.resolves hcast

/-- The supporters of ballot `b` are counted, with multiplicity, by the weights
of its casters. -/
theorem card_resolversTo_eq_sum_weight (b : β) :
    (d.resolversTo b).card = ∑ j ∈ d.castersOf b, d.weight j := by
  classical
  rw [resolversTo_eq_biUnion, card_biUnion_guruFiber]

/-- Under an acyclic delegation graph no vote is lost: total weight is the full
electorate. -/
theorem sum_weight_eq_card_of_acyclic
    (h : ∀ i, ¬ Relation.TransGen d.DelegatesTo i i) :
    ∑ j ∈ d.casters, d.weight j = Fintype.card ι := by
  have hall := resolves_total_iff_acyclic (d := d) |>.mpr h
  rw [sum_weight_eq_card_participants, ← Finset.card_univ]
  congr 1
  rw [Finset.eq_univ_iff_forall]
  intro i
  exact mem_participants.mpr (hall i)

/-! ### The multiset of effective ballots -/

/-- The multiset of effective ballots: each non-abstaining voter contributes
the ballot their delegation chain resolves to. -/
noncomputable def resolvedBallots (d : DelegationProfile ι β) : Multiset β :=
  ∑ i : ι, ((d.resolve i).toList : Multiset β)

/-- One effective ballot per participant. -/
theorem card_resolvedBallots :
    Multiset.card d.resolvedBallots = d.participants.card := by
  classical
  rw [resolvedBallots, Multiset.card_sum]
  unfold participants
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases hr : d.resolve i with
  | none =>
    have hnone := resolve_eq_none_iff.mp hr
    rw [if_neg fun ⟨b, hb⟩ => hnone b hb]
    simp
  | some b =>
    rw [if_pos ⟨b, resolve_eq_some_iff.mp hr⟩]
    simp

/-- The multiplicity of a ballot among the effective ballots is the number of
its supporters. -/
theorem count_resolvedBallots [DecidableEq β] (b : β) :
    d.resolvedBallots.count b = (d.resolversTo b).card := by
  classical
  rw [resolvedBallots, Multiset.count_sum']
  unfold resolversTo
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases hr : d.resolve i with
  | none =>
    have hnone := resolve_eq_none_iff.mp hr
    rw [if_neg (hnone b)]
    simp
  | some b' =>
    have hsome := resolve_eq_some_iff.mp hr
    by_cases hbb : b' = b
    · subst hbb
      rw [if_pos hsome]
      simp
    · rw [if_neg fun hres => hbb (hsome.unique hres)]
      simp [Ne.symm hbb]

/-- **Liquid democracy is weighted direct democracy**: the effective ballots are
exactly each caster's direct ballot, taken with multiplicity its weight. -/
theorem resolvedBallots_eq_sum_casters :
    d.resolvedBallots
      = ∑ j ∈ d.casters, d.weight j • ((d.directBallot j).toList : Multiset β) := by
  classical
  refine Multiset.ext.mpr fun b => ?_
  rw [count_resolvedBallots, card_resolversTo_eq_sum_weight, Multiset.count_sum']
  have hsub : d.castersOf b ⊆ d.casters :=
    fun j hj => mem_casters.mpr (mem_castersOf.mp hj).isCaster
  refine (Finset.sum_congr rfl fun j hj => ?_).trans
    (Finset.sum_subset hsub fun j hj hnj => ?_)
  · have hcast := mem_castersOf.mp hj
    rw [directBallot_eq_some_iff.mpr hcast]
    simp
  · obtain ⟨bj, hbj⟩ := mem_casters.mp hj
    rw [directBallot_eq_some_iff.mpr hbj]
    have hne : bj ≠ b := fun hbb => hnj (mem_castersOf.mpr (hbb ▸ hbj))
    simp [Ne.symm hne]

end DelegationProfile

/-! ### Composing anonymous rules with delegation -/

variable {ι β α : Type*}

open DelegationProfile

/-- The direct-democracy profile in which every voter casts their own ballot. -/
def directProfile (p : ι → β) : DelegationProfile ι β := fun i => Sum.inr (p i)

@[simp] theorem directProfile_resolve (p : ι → β) (i : ι) :
    (directProfile p).resolve i = some (p i) := by
  have h : (directProfile p).Casts i (p i) := rfl
  exact h.resolves.resolve_eq

/-- A cast deviation from an all-cast profile is again an all-cast profile. -/
theorem update_directProfile [DecidableEq ι] (p : ι → β) (i : ι) (b : β) :
    Function.update (directProfile p) i (Sum.inr b)
      = directProfile (Function.update p i b) := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [directProfile]
  · simp [directProfile, Function.update_of_ne hk]

/-- In an all-cast profile every voter is their own guru. -/
theorem isGuruOf_directProfile_iff {p : ι → β} {i j : ι} :
    (directProfile p).IsGuruOf j i ↔ i = j := by
  constructor
  · rintro ⟨hchain, -⟩
    rcases hchain.cases_head with rfl | ⟨k, hstep, -⟩
    · rfl
    · exact absurd hstep (by simp [DelegationProfile.DelegatesTo, directProfile])
  · rintro rfl
    exact IsCaster.isGuruOf_self ⟨p i, rfl⟩

variable [Fintype ι]

/-- In an all-cast profile every voter carries exactly their own vote. -/
theorem weight_directProfile (p : ι → β) (j : ι) :
    (directProfile p).weight j = 1 := by
  rw [DelegationProfile.weight, Finset.card_eq_one]
  refine ⟨j, ?_⟩
  ext i
  simp only [mem_guruFiber, Finset.mem_singleton]
  exact isGuruOf_directProfile_iff

/-- The liquid-democracy extension of an anonymous voting rule: resolve all
delegations, then apply the rule to the multiset of effective ballots. -/
noncomputable def liquidExtension (R : Multiset β → α) (d : DelegationProfile ι β) : α :=
  R d.resolvedBallots

@[simp] theorem resolvedBallots_directProfile (p : ι → β) :
    (directProfile p).resolvedBallots = Finset.univ.val.map p := by
  have hmap : (Multiset.mapAddMonoidHom p) (∑ a : ι, ({a} : Multiset ι))
      = ∑ a : ι, ({p a} : Multiset β) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp [Multiset.mapAddMonoidHom]
  rw [resolvedBallots]
  simp only [directProfile_resolve, Option.toList_some, Multiset.coe_singleton]
  rw [← hmap, Finset.sum_multiset_singleton]
  simp [Multiset.mapAddMonoidHom]

/-- **Direct democracy embeds**: on an all-cast profile the liquid extension is
the underlying rule applied to the cast ballots. -/
theorem liquidExtension_directProfile (R : Multiset β → α) (p : ι → β) :
    liquidExtension R (directProfile p) = R (Finset.univ.val.map p) := by
  rw [liquidExtension, resolvedBallots_directProfile]

/-- **Copy-robustness**: a voter switching from their delegative ballot to a
direct cast of the ballot it resolves to never changes the outcome — under any
anonymous rule. -/
theorem liquidExtension_update_cast [DecidableEq ι] (R : Multiset β → α)
    {d : DelegationProfile ι β} {i : ι} {b : β} (hib : d.Resolves i b) :
    liquidExtension R (Function.update d i (Sum.inr b)) = liquidExtension R d := by
  rw [liquidExtension, liquidExtension, resolvedBallots, resolvedBallots,
    resolve_update_cast hib]

end GameTheory.Voting
