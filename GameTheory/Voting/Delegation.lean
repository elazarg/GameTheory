/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Logic.Relation
import Mathlib.Data.Fintype.Card

/-!
# Delegative voting: delegation profiles and resolution

In fluid (liquid) democracy every voter either casts a direct ballot or delegates
their vote to another voter. Delegations are transitive: a vote entrusted to a
delegate follows the delegate's own delegative choice, so each vote travels along
a delegation chain until it reaches a voter who casts directly (that voter is the
chain's *guru*). A chain that never reaches a caster — because it enters a
delegation cycle, or descends forever in an infinite electorate — leaves the
originating vote unresolved (an abstention).

This file provides the delegation layer independently of any voting rule:
profiles, chain resolution, gurus, and the termination theory. Weights and the
composition with anonymous voting rules live in
`GameTheory.Voting.LiquidDemocracy`.

## Main definitions

* `Voting.DelegationProfile` — per-voter delegative ballots `ι → ι ⊕ β`
  (`Sum.inl j` delegates to voter `j`, `Sum.inr b` casts the direct ballot `b`)
* `DelegationProfile.Resolves` — voter `i`'s chain terminates in ballot `b`
* `DelegationProfile.IsGuruOf` — caster `j` ends voter `i`'s delegation chain
* `DelegationProfile.resolve` / `DelegationProfile.guru` — the resolved ballot /
  guru as `Option`-valued functions (`none` = abstention)
* `DelegationProfile.resolveFuel` — computable resolution with bounded lookahead

## Main results

* `Resolves.unique`, `IsGuruOf.unique` — delegation chains are deterministic
* `resolves_congr` — resolution is local: profiles that agree away from `i` and
  resolve `i` alike resolve every voter alike
* `resolves_update_cast_iff` (copy lemma) — replacing a voter's delegative ballot
  by a direct cast of its resolved ballot changes no voter's resolution
* `resolves_total_of_wellFounded` — if delegation chains are well-founded, every
  voter resolves (no finiteness needed)
* `not_resolves_of_cycle`, `not_resolves_of_reflTransGen_cycle` — voters on, or
  whose chains reach, a delegation cycle abstain
* `resolves_total_iff_acyclic` — over a finite electorate, full participation is
  exactly acyclicity of the delegation graph
-/

namespace GameTheory.Voting

/-- A delegation profile: each voter either delegates to another voter
(`Sum.inl j`) or casts a direct ballot (`Sum.inr b`). This is simultaneously the
input to fluid-democracy vote resolution and the strategy of a voter in the
induced delegation game. -/
abbrev DelegationProfile (ι β : Type*) := ι → ι ⊕ β

namespace DelegationProfile

variable {ι β : Type*} {d d' : DelegationProfile ι β} {i j k : ι} {b b' : β}

/-- Voter `i` delegates directly to voter `j`. -/
def DelegatesTo (d : DelegationProfile ι β) (i j : ι) : Prop := d i = Sum.inl j

/-- Voter `i` casts the direct ballot `b`. -/
def Casts (d : DelegationProfile ι β) (i : ι) (b : β) : Prop := d i = Sum.inr b

/-- A caster: a voter who casts some direct ballot. -/
def IsCaster (d : DelegationProfile ι β) (i : ι) : Prop := ∃ b, d.Casts i b

@[simp] theorem delegatesTo_iff : d.DelegatesTo i j ↔ d i = Sum.inl j := Iff.rfl

@[simp] theorem casts_iff : d.Casts i b ↔ d i = Sum.inr b := Iff.rfl

theorem DelegatesTo.eq (h : d.DelegatesTo i j) (h' : d.DelegatesTo i k) : j = k := by
  rw [delegatesTo_iff] at h h'
  exact Sum.inl.inj (h.symm.trans h')

theorem Casts.eq (h : d.Casts i b) (h' : d.Casts i b') : b = b' := by
  rw [casts_iff] at h h'
  exact Sum.inr.inj (h.symm.trans h')

theorem Casts.isCaster (h : d.Casts i b) : d.IsCaster i := ⟨b, h⟩

theorem DelegatesTo.not_casts (h : d.DelegatesTo i j) (h' : d.Casts i b) : False := by
  rw [delegatesTo_iff] at h
  rw [casts_iff, h] at h'
  exact Sum.inl_ne_inr h'

theorem DelegatesTo.not_isCaster (h : d.DelegatesTo i j) : ¬ d.IsCaster i :=
  fun ⟨_, hb⟩ => h.not_casts hb

/-- Voter `i`'s delegation chain terminates in a voter who casts ballot `b`. -/
def Resolves (d : DelegationProfile ι β) (i : ι) (b : β) : Prop :=
  ∃ j, Relation.ReflTransGen d.DelegatesTo i j ∧ d.Casts j b

theorem Casts.resolves (h : d.Casts i b) : d.Resolves i b :=
  ⟨i, .refl, h⟩

theorem Resolves.delegate (h : d.DelegatesTo i j) (h' : d.Resolves j b) :
    d.Resolves i b := by
  obtain ⟨k, hchain, hcast⟩ := h'
  exact ⟨k, .head h hchain, hcast⟩

/-- One-step unfolding of resolution. -/
theorem resolves_iff :
    d.Resolves i b ↔ d.Casts i b ∨ ∃ j, d.DelegatesTo i j ∧ d.Resolves j b := by
  constructor
  · rintro ⟨j, hchain, hcast⟩
    rcases hchain.cases_head with rfl | ⟨k, hstep, hchain'⟩
    · exact Or.inl hcast
    · exact Or.inr ⟨k, hstep, j, hchain', hcast⟩
  · rintro (h | ⟨j, hstep, hres⟩)
    · exact h.resolves
    · exact hres.delegate hstep

/-- Resolution transports down the delegation chain: every voter a resolving
voter's chain passes through resolves to the same ballot. -/
theorem Resolves.of_reflTransGen (hic : Relation.ReflTransGen d.DelegatesTo i k)
    (h : d.Resolves i b) : d.Resolves k b := by
  induction hic with
  | refl => exact h
  | tail _ hstep ih =>
    rcases resolves_iff.mp ih with hcast | ⟨j', hj', hres⟩
    · exact (hstep.not_casts hcast).elim
    · obtain rfl := hstep.eq hj'
      exact hres

/-- Delegation chains are deterministic: from a fixed voter, any two chains ending
at casters end at the same caster. -/
theorem reflTransGen_caster_unique
    (hj : Relation.ReflTransGen d.DelegatesTo i j)
    (hcj : d.IsCaster j) :
    ∀ {j'}, Relation.ReflTransGen d.DelegatesTo i j' → d.IsCaster j' → j = j' := by
  induction hj using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro j' hj' hcj'
    rcases hj'.cases_head with rfl | ⟨k, hstep, _⟩
    · rfl
    · exact absurd hcj hstep.not_isCaster
  | head hstep _ ih =>
    intro j' hj' hcj'
    rcases hj'.cases_head with rfl | ⟨k, hstep', hchain'⟩
    · exact absurd hcj' hstep.not_isCaster
    · exact ih ((hstep.eq hstep').symm ▸ hchain') hcj'

/-- Resolution is unique: a voter's chain determines at most one ballot. -/
theorem Resolves.unique (h : d.Resolves i b) (h' : d.Resolves i b') : b = b' := by
  obtain ⟨j, hchain, hcast⟩ := h
  obtain ⟨j', hchain', hcast'⟩ := h'
  obtain rfl := reflTransGen_caster_unique hchain hcast.isCaster hchain' hcast'.isCaster
  exact hcast.eq hcast'

/-- Caster `j` ends voter `i`'s delegation chain: `j` is the guru of `i`.
Casters are their own gurus. -/
def IsGuruOf (d : DelegationProfile ι β) (j i : ι) : Prop :=
  Relation.ReflTransGen d.DelegatesTo i j ∧ d.IsCaster j

theorem IsCaster.isGuruOf_self (h : d.IsCaster j) : d.IsGuruOf j j := ⟨.refl, h⟩

theorem IsGuruOf.delegate (h : d.DelegatesTo i k) (h' : d.IsGuruOf j k) :
    d.IsGuruOf j i :=
  ⟨.head h h'.1, h'.2⟩

theorem IsGuruOf.isCaster (h : d.IsGuruOf j i) : d.IsCaster j := h.2

/-- Each voter has at most one guru. -/
theorem IsGuruOf.unique (h : d.IsGuruOf j i) (h' : d.IsGuruOf k i) : j = k :=
  reflTransGen_caster_unique h.1 h.2 h'.1 h'.2

/-- A caster is their own guru and no one else's guru-client relationship
assigns them a different guru. -/
theorem IsGuruOf.eq_self_of_isCaster (h : d.IsGuruOf j i) (hc : d.IsCaster i) :
    j = i :=
  h.unique hc.isGuruOf_self

theorem resolves_iff_exists_guru :
    d.Resolves i b ↔ ∃ j, d.IsGuruOf j i ∧ d.Casts j b := by
  constructor
  · rintro ⟨j, hchain, hcast⟩
    exact ⟨j, ⟨hchain, hcast.isCaster⟩, hcast⟩
  · rintro ⟨j, hguru, hcast⟩
    exact ⟨j, hguru.1, hcast⟩

theorem IsGuruOf.resolves (h : d.IsGuruOf j i) (hb : d.Casts j b) :
    d.Resolves i b :=
  resolves_iff_exists_guru.mpr ⟨j, h, hb⟩

/-! ### Resolution as an `Option`-valued function

`none` records abstention: the voter's chain never reaches a caster. -/

/-- The ballot voter `i` casts directly, if any. -/
def directBallot (d : DelegationProfile ι β) (i : ι) : Option β := (d i).getRight?

@[simp] theorem directBallot_eq_some_iff :
    d.directBallot i = some b ↔ d.Casts i b := by
  simp [directBallot, Casts, Sum.getRight?_eq_some_iff]

open Classical in
/-- The ballot voter `i`'s delegation chain resolves to; `none` for abstention. -/
noncomputable def resolve (d : DelegationProfile ι β) (i : ι) : Option β :=
  if h : ∃ b, d.Resolves i b then some h.choose else none

theorem resolve_eq_some_iff : d.resolve i = some b ↔ d.Resolves i b := by
  unfold resolve
  split_ifs with h
  · rw [Option.some_inj]
    exact ⟨fun hb => hb ▸ h.choose_spec, fun hb => h.choose_spec.unique hb⟩
  · constructor
    · intro hb
      exact absurd hb (by simp)
    · intro hb
      exact absurd ⟨b, hb⟩ h

theorem resolve_eq_none_iff : d.resolve i = none ↔ ∀ b, ¬ d.Resolves i b := by
  rw [← Option.not_isSome_iff_eq_none]
  simp only [Option.isSome_iff_exists, resolve_eq_some_iff, not_exists]

theorem Resolves.resolve_eq (h : d.Resolves i b) : d.resolve i = some b :=
  resolve_eq_some_iff.mpr h

open Classical in
/-- The guru of voter `i` — the caster ending `i`'s delegation chain, if any. -/
noncomputable def guru (d : DelegationProfile ι β) (i : ι) : Option ι :=
  if h : ∃ j, d.IsGuruOf j i then some h.choose else none

theorem guru_eq_some_iff : d.guru i = some j ↔ d.IsGuruOf j i := by
  unfold guru
  split_ifs with h
  · rw [Option.some_inj]
    exact ⟨fun hj => hj ▸ h.choose_spec, fun hj => h.choose_spec.unique hj⟩
  · constructor
    · intro hj
      exact absurd hj (by simp)
    · intro hj
      exact absurd ⟨j, hj⟩ h

theorem guru_eq_none_iff : d.guru i = none ↔ ∀ j, ¬ d.IsGuruOf j i := by
  rw [← Option.not_isSome_iff_eq_none]
  simp only [Option.isSome_iff_exists, guru_eq_some_iff, not_exists]

/-- A voter's resolved ballot is the direct ballot of their guru. -/
theorem resolve_eq_guru_bind :
    d.resolve i = (d.guru i).bind d.directBallot := by
  cases hg : d.guru i with
  | none =>
    change d.resolve i = none
    rw [resolve_eq_none_iff]
    intro b hb
    obtain ⟨j, hguru, -⟩ := resolves_iff_exists_guru.mp hb
    exact guru_eq_none_iff.mp hg j hguru
  | some j =>
    change d.resolve i = d.directBallot j
    have hguru := guru_eq_some_iff.mp hg
    cases hb : d.directBallot j with
    | none =>
      obtain ⟨b, hcast⟩ := hguru.isCaster
      have := directBallot_eq_some_iff.mpr hcast
      rw [hb] at this
      simp at this
    | some b =>
      exact (hguru.resolves (directBallot_eq_some_iff.mp hb)).resolve_eq

/-! ### Locality of resolution -/

/-- One-directional congruence: if `d` and `d'` agree away from `i`, and every
resolution of `i` under `d` transfers to `d'`, then every resolution transfers. -/
theorem Resolves.mono_of_agree (h : ∀ m, m ≠ i → d m = d' m)
    (hi : ∀ b, d.Resolves i b → d'.Resolves i b) (hk : d.Resolves k b) :
    d'.Resolves k b := by
  obtain ⟨j, hchain, hcast⟩ := hk
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    by_cases hji : j = i
    · subst hji; exact hi b hcast.resolves
    · refine Casts.resolves ?_
      rw [casts_iff, ← h j hji]
      exact hcast
  | @head a c hstep hchain ih =>
    by_cases hai : a = i
    · subst hai
      exact hi b ⟨j, .head hstep hchain, hcast⟩
    · refine Resolves.delegate ?_ ih
      rw [delegatesTo_iff, ← h a hai]
      exact hstep

/-- Resolution is local: profiles agreeing away from `i` that resolve `i` alike
resolve every voter alike. -/
theorem resolves_congr (h : ∀ m, m ≠ i → d m = d' m)
    (hi : ∀ b, d.Resolves i b ↔ d'.Resolves i b) :
    d.Resolves k b ↔ d'.Resolves k b :=
  ⟨Resolves.mono_of_agree h fun b => (hi b).mp,
   Resolves.mono_of_agree (fun m hm => (h m hm).symm) fun b => (hi b).mpr⟩

/-- **Copy lemma.** Replacing voter `i`'s delegative ballot by a direct cast of
the ballot their chain already resolves to leaves every voter's resolution
unchanged. In particular delegating to a voter whose chain casts `b` is
indistinguishable, for everyone, from casting `b` oneself. -/
theorem resolves_update_cast_iff [DecidableEq ι] (hib : d.Resolves i b) :
    Resolves (Function.update d i (Sum.inr b)) k b' ↔ d.Resolves k b' := by
  have hcast : Casts (Function.update d i (Sum.inr b)) i b := by
    simp [Casts]
  refine resolves_congr (i := i) (fun m hm => Function.update_of_ne hm _ _) ?_
  intro b''
  constructor
  · intro hb''
    obtain rfl := hcast.resolves.unique hb''
    exact hib
  · intro hb''
    obtain rfl := hib.unique hb''
    exact hcast.resolves

/-- Copy lemma, functional form: casting one's resolved ballot leaves the whole
resolution function unchanged. -/
theorem resolve_update_cast [DecidableEq ι] (hib : d.Resolves i b) :
    resolve (Function.update d i (Sum.inr b)) = d.resolve := by
  funext k
  cases hr : d.resolve k with
  | some b' =>
    exact ((resolves_update_cast_iff hib).mpr (resolve_eq_some_iff.mp hr)).resolve_eq
  | none =>
    rw [resolve_eq_none_iff] at hr ⊢
    intro b' hb'
    exact hr b' ((resolves_update_cast_iff hib).mp hb')

/-! ### Termination: well-founded delegation, cycles, and finite electorates -/

/-- If following delegations is well-founded — every delegation chain descends —
then every voter resolves. No finiteness of the electorate is needed. -/
theorem resolves_total_of_wellFounded
    (hwf : WellFounded fun j i => d.DelegatesTo i j) (i : ι) :
    ∃ b, d.Resolves i b := by
  refine hwf.induction (C := fun i => ∃ b, d.Resolves i b) i ?_
  intro i IH
  cases hd : d i with
  | inl j =>
    obtain ⟨b, hb⟩ := IH j hd
    exact ⟨b, hb.delegate hd⟩
  | inr b => exact ⟨b, Casts.resolves hd⟩

/-- A delegation chain that reaches a caster passes through no cycle at its
origin. -/
theorem not_cycle_of_reachable_caster
    (hchain : Relation.ReflTransGen d.DelegatesTo i j) (hcast : d.IsCaster j) :
    ¬ Relation.TransGen d.DelegatesTo i i := by
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro hcyc
    obtain ⟨k, hstep, -⟩ := Relation.TransGen.head'_iff.mp hcyc
    exact hstep.not_isCaster hcast
  | @head a c hstep hchain ih =>
    intro hcyc
    obtain ⟨k, hstep', hrest⟩ := Relation.TransGen.head'_iff.mp hcyc
    obtain rfl := hstep.eq hstep'
    exact ih (Relation.TransGen.tail' hrest hstep)

/-- Voters on delegation cycles abstain. -/
theorem not_resolves_of_cycle (hcyc : Relation.TransGen d.DelegatesTo i i) :
    ¬ d.Resolves i b :=
  fun ⟨_, hchain, hcast⟩ =>
    not_cycle_of_reachable_caster hchain hcast.isCaster hcyc

/-- Voters whose delegation chain reaches a cycle abstain. -/
theorem not_resolves_of_reflTransGen_cycle
    (hik : Relation.ReflTransGen d.DelegatesTo i k)
    (hcyc : Relation.TransGen d.DelegatesTo k k) : ¬ d.Resolves i b :=
  fun h => not_resolves_of_cycle hcyc (h.of_reflTransGen hik)

/-- Over a finite electorate, every voter resolves iff the delegation graph is
acyclic. -/
theorem resolves_total_iff_acyclic [Finite ι] :
    (∀ i, ∃ b, d.Resolves i b) ↔ ∀ i, ¬ Relation.TransGen d.DelegatesTo i i := by
  constructor
  · intro h i hcyc
    obtain ⟨b, hb⟩ := h i
    exact not_resolves_of_cycle hcyc hb
  · intro h
    have htrans : WellFounded (Relation.TransGen fun j i => d.DelegatesTo i j) := by
      haveI : Std.Irrefl (Relation.TransGen fun j i => d.DelegatesTo i j) :=
        ⟨fun a hcyc => h a (Relation.transGen_swap.mp hcyc)⟩
      exact Finite.wellFounded_of_trans_of_irrefl _
    exact resolves_total_of_wellFounded
      (Subrelation.wf (r := Relation.TransGen fun j i => d.DelegatesTo i j)
        (fun {_ _} hji => Relation.TransGen.single hji) htrans)

/-! ### Computable resolution with fuel -/

/-- Resolution with at most `n` delegation steps of lookahead: `resolveFuel d 0`
is `directBallot d`, and each unit of fuel follows one delegation edge. -/
def resolveFuel (d : DelegationProfile ι β) : ℕ → ι → Option β
  | 0, i => d.directBallot i
  | n + 1, i =>
    match d i with
    | .inr b => some b
    | .inl j => d.resolveFuel n j

@[simp] theorem resolveFuel_zero (i : ι) :
    d.resolveFuel 0 i = d.directBallot i := rfl

theorem resolveFuel_succ_delegate (h : d.DelegatesTo i j) (n : ℕ) :
    d.resolveFuel (n + 1) i = d.resolveFuel n j := by
  have h' : d i = Sum.inl j := h
  simp only [resolveFuel, h']

theorem resolveFuel_succ_cast (h : d.Casts i b) (n : ℕ) :
    d.resolveFuel (n + 1) i = some b := by
  have h' : d i = Sum.inr b := h
  simp only [resolveFuel, h']

theorem resolves_of_resolveFuel_eq_some {n : ℕ}
    (h : d.resolveFuel n i = some b) : d.Resolves i b := by
  induction n generalizing i with
  | zero => exact (directBallot_eq_some_iff.mp h).resolves
  | succ n ih =>
    cases hd : d i with
    | inl j =>
      rw [resolveFuel_succ_delegate hd] at h
      exact (ih h).delegate hd
    | inr b' =>
      rw [resolveFuel_succ_cast hd] at h
      obtain rfl := Option.some_inj.mp h
      exact Casts.resolves hd

theorem exists_resolveFuel_of_resolves (h : d.Resolves i b) :
    ∃ n, d.resolveFuel n i = some b := by
  obtain ⟨j, hchain, hcast⟩ := h
  induction hchain using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, directBallot_eq_some_iff.mpr hcast⟩
  | @head a c hstep hchain ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by rw [resolveFuel_succ_delegate hstep]; exact hn⟩

/-- Fuel monotonicity: extra lookahead never loses a resolution. -/
theorem resolveFuel_mono {n m : ℕ} (hnm : n ≤ m)
    (h : d.resolveFuel n i = some b) : d.resolveFuel m i = some b := by
  induction m generalizing n i with
  | zero => obtain rfl := Nat.le_zero.mp hnm; exact h
  | succ m ih =>
    cases n with
    | zero =>
      rw [resolveFuel_zero] at h
      exact resolveFuel_succ_cast (directBallot_eq_some_iff.mp h) m
    | succ n =>
      cases hd : d i with
      | inl j =>
        rw [resolveFuel_succ_delegate hd] at h
        rw [resolveFuel_succ_delegate hd]
        exact ih (Nat.succ_le_succ_iff.mp hnm) h
      | inr b' =>
        rw [resolveFuel_succ_cast hd] at h
        rw [resolveFuel_succ_cast hd]
        exact h

/-- `resolveFuel` computes `resolve`: any successful fuel-bounded resolution is
the (unique) resolution. -/
theorem resolve_eq_of_resolveFuel {n : ℕ} (h : d.resolveFuel n i = some b) :
    d.resolve i = some b :=
  (resolves_of_resolveFuel_eq_some h).resolve_eq

end DelegationProfile

end GameTheory.Voting
