/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.SocialChoice.Arrow

/-!
# The Gibbard–Satterthwaite theorem

A **social choice function** (SCF) selects a single alternative from each profile of rankings.
The Gibbard–Satterthwaite theorem says that, with at least three alternatives in its range, a
strategy-proof SCF over the full domain of rankings must be dictatorial.

The proof is the classical reduction to Arrow's impossibility theorem
(`Mechanism/SocialChoice/Arrow.lean`):
from a strategy-proof, onto SCF `g` we build an *induced social welfare function* — society
prefers `a` to `b` exactly when `g` chooses `a` from the profile that lifts `a, b` to the top —
show it is collectively rational, Paretian, and IIA, and transfer Arrow's dictator back to `g`.
This is the reduction used in Tobias Nipkow's AFP entry *Arrow and Gibbard-Satterthwaite*,
adapted here to the library's full-domain function types.

The workhorse is **monotonicity**: strategy-proofness implies that if `g` chooses `a` and every
voter (weakly) raises `a`, then `g` still chooses `a`.

## Main definitions

* `SCF` — a social choice function `PrefProfile ι A → A`
* `SCF.IsStrategyProof`, `SCF.IsOnto`, `SCF.IsDictator`

## Main results

* `gibbard_satterthwaite` — a strategy-proof, onto SCF with ≥ 3 alternatives and a nonempty
  finite electorate is dictatorial.
-/

namespace GameTheory

universe u v

variable {ι : Type u} {A : Type v}

/-- `a` is the top alternative of the ranking `r`: strictly above every other alternative. -/
def IsTop (r : PrefRel A) (a : A) : Prop := ∀ b, b ≠ a → r a b

/-- A ranking has at most one top alternative. -/
theorem IsTop.unique {r : PrefRel A} {a b : A} (hr : IsRanking r)
    (ha : IsTop r a) (hb : IsTop r b) : a = b := by
  by_contra hab
  exact hr.asymm (ha b (Ne.symm hab)) (hb a hab)

/-! ### Raising a set of alternatives to the top

`raiseTop p r` moves every alternative satisfying `p` above every alternative that does not,
keeping `r`'s order within each block. With `p = {a, b}` this is the pairwise lift used to define
the induced order; with `p = {a, b, c}` it is the triple lift used to prove transitivity. -/

/-- Move the alternatives satisfying `p` to the top, preserving `r`'s order within and outside. -/
def raiseTop (p : A → Prop) (r : PrefRel A) : PrefRel A :=
  fun x y => (p x ∧ ¬ p y) ∨ ((p x ↔ p y) ∧ r x y)

/-- An alternative in `p` is strictly above any alternative outside `p`. -/
theorem raiseTop_above {p : A → Prop} {r : PrefRel A} {x y : A} (hx : p x) (hy : ¬ p y) :
    raiseTop p r x y := Or.inl ⟨hx, hy⟩

/-- Nothing outside `p` is above something in `p`. -/
theorem raiseTop_not_above {p : A → Prop} {r : PrefRel A} {x y : A} (hx : ¬ p x) (hy : p y) :
    ¬ raiseTop p r x y := by
  rintro (⟨hx', _⟩ | ⟨hiff, _⟩)
  · exact hx hx'
  · exact hx (hiff.mpr hy)

/-- Within the same block, `raiseTop` keeps `r`'s order. -/
theorem raiseTop_same {p : A → Prop} {r : PrefRel A} {x y : A} (h : p x ↔ p y) :
    raiseTop p r x y ↔ r x y := by
  constructor
  · rintro (⟨hx, hy⟩ | ⟨_, hr⟩)
    · exact absurd (h.mp hx) hy
    · exact hr
  · exact fun hr => Or.inr ⟨h, hr⟩

/-- `raiseTop` of a ranking is a ranking. -/
theorem raiseTop_ranking {p : A → Prop} {r : PrefRel A} (hr : IsRanking r) :
    IsRanking (raiseTop p r) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro x
    rintro (⟨hx, hnx⟩ | ⟨_, hrxx⟩)
    · exact hnx hx
    · exact hr.irrefl x hrxx
  · intro x y z hxy hyz
    rcases hxy with ⟨hpx, hnpy⟩ | ⟨hxyi, hrxy⟩
    · rcases hyz with ⟨hpy, _⟩ | ⟨hyzi, _⟩
      · exact absurd hpy hnpy
      · exact Or.inl ⟨hpx, fun hpz => hnpy (hyzi.mpr hpz)⟩
    · rcases hyz with ⟨hpy, hnpz⟩ | ⟨hyzi, hryz⟩
      · exact Or.inl ⟨hxyi.mpr hpy, hnpz⟩
      · exact Or.inr ⟨hxyi.trans hyzi, hr.trans hrxy hryz⟩
  · intro x y hxy
    by_cases hpx : p x <;> by_cases hpy : p y
    · rcases hr.total x y hxy with h | h
      · exact Or.inl (Or.inr ⟨iff_of_true hpx hpy, h⟩)
      · exact Or.inr (Or.inr ⟨iff_of_true hpy hpx, h⟩)
    · exact Or.inl (Or.inl ⟨hpx, hpy⟩)
    · exact Or.inr (Or.inl ⟨hpy, hpx⟩)
    · rcases hr.total x y hxy with h | h
      · exact Or.inl (Or.inr ⟨iff_of_false hpx hpy, h⟩)
      · exact Or.inr (Or.inr ⟨iff_of_false hpy hpx, h⟩)

/-- `raiseTop` depends on the block predicate only up to logical equivalence. -/
theorem raiseTop_congr {p p' : A → Prop} (h : ∀ z, p z ↔ p' z) (r : PrefRel A) :
    raiseTop p r = raiseTop p' r := by
  funext x y; simp only [raiseTop, h x, h y]

/-- A **social choice function** picks a single alternative for each preference profile. -/
abbrev SCF (ι : Type u) (A : Type v) := PrefProfile ι A → A

section Mix
variable [DecidableEq ι]

/-- The profile in which the voters in `T` switch from `R` to `R'`, the rest keeping `R`. -/
def mixProfile (R R' : PrefProfile ι A) (T : Finset ι) : PrefProfile ι A :=
  fun j => if j ∈ T then R' j else R j

theorem mixProfile_mem {R R' : PrefProfile ι A} {T : Finset ι} {j : ι} (h : j ∈ T) :
    mixProfile R R' T j = R' j := if_pos h

theorem mixProfile_not_mem {R R' : PrefProfile ι A} {T : Finset ι} {j : ι} (h : j ∉ T) :
    mixProfile R R' T j = R j := if_neg h

theorem mixProfile_empty (R R' : PrefProfile ι A) : mixProfile R R' ∅ = R := by
  funext j; simp [mixProfile]

theorem mixProfile_univ [Fintype ι] (R R' : PrefProfile ι A) :
    mixProfile R R' Finset.univ = R' := by
  funext j; simp [mixProfile]

theorem mixProfile_insert {R R' : PrefProfile ι A} {T : Finset ι} {i : ι} (hiT : i ∉ T) :
    mixProfile R R' (insert i T) = Function.update (mixProfile R R' T) i (R' i) := by
  funext j
  by_cases hj : j = i
  · subst hj; rw [mixProfile_mem (Finset.mem_insert_self j T), Function.update_self]
  · rw [Function.update_of_ne hj]
    by_cases hjT : j ∈ T
    · rw [mixProfile_mem (Finset.mem_insert_of_mem hjT), mixProfile_mem hjT]
    · rw [mixProfile_not_mem fun h => (Finset.mem_insert.mp h).elim hj hjT,
        mixProfile_not_mem hjT]

end Mix

namespace SCF

variable [DecidableEq ι]

/-- `g` is **strategy-proof**: under their true ranking, no voter strictly prefers the outcome
obtained by misreporting some ranking `S` to the truthful outcome. -/
def IsStrategyProof (g : SCF ι A) : Prop :=
  ∀ R : PrefProfile ι A, (∀ i, IsRanking (R i)) →
    ∀ (i : ι) (S : PrefRel A), IsRanking S →
      ¬ R i (g (Function.update R i S)) (g R)

/-- `g` has **full range** on rankings: every alternative is selected at some ranking profile. -/
def IsOnto (g : SCF ι A) : Prop :=
  ∀ a : A, ∃ R : PrefProfile ι A, (∀ i, IsRanking (R i)) ∧ g R = a

/-- Voter `d` is a **dictator** for `g`: at every ranking profile, the selected alternative
is top-ranked by `d`. This formulation remains substantive for infinite rankings, which need
not have a top alternative a priori. -/
def IsDictator (g : SCF ι A) (d : ι) : Prop :=
  ∀ R : PrefProfile ι A, (∀ i, IsRanking (R i)) → IsTop (R d) (g R)

omit [DecidableEq ι] in
/-- A dictator's selected alternative equals any top alternative in the dictator's ranking. -/
theorem IsDictator.eq_of_isTop {g : SCF ι A} {d : ι} (hd : g.IsDictator d)
    {R : PrefProfile ι A} (hR : ∀ i, IsRanking (R i)) {a : A} (ha : IsTop (R d) a) :
    g R = a :=
  (hd R hR).unique (hR d) ha

/-! ### Monotonicity

The single workhorse: under strategy-proofness, if `g` chooses `a` and one voter changes their
ranking so that `a` does not fall below anything it was above, then `g` still chooses `a`. -/

/-- **Single-voter monotonicity.** If `g R = a` and voter `i` switches to a ranking `S` in which
`a` is weakly higher (above everything it was above in `R i`), the outcome is unchanged. -/
theorem monotone_step {g : SCF ι A} (hsp : g.IsStrategyProof) {R : PrefProfile ι A}
    (hR : ∀ j, IsRanking (R j)) {i : ι} {S : PrefRel A} (hS : IsRanking S)
    (hmono : ∀ b, R i (g R) b → S (g R) b) :
    g (Function.update R i S) = g R := by
  have hR'rank : ∀ j, IsRanking (Function.update R i S j) := by
    intro j
    by_cases hj : j = i
    · subst hj; rw [Function.update_self]; exact hS
    · rw [Function.update_of_ne hj]; exact hR j
  have hupd : Function.update (Function.update R i S) i (R i) = R := by
    rw [Function.update_idem, Function.update_eq_self]
  have hstar : ¬ S (g R) (g (Function.update R i S)) := by
    have h := hsp (Function.update R i S) hR'rank i (R i) (hR i)
    rw [Function.update_self, hupd] at h
    exact h
  have hstarstar : ¬ R i (g (Function.update R i S)) (g R) := hsp R hR i S hS
  by_contra hne
  have hS_ba : S (g (Function.update R i S)) (g R) := (hS.not_iff (Ne.symm hne)).mp hstar
  have hR_ab : R i (g R) (g (Function.update R i S)) := ((hR i).not_iff hne).mp hstarstar
  exact hS.asymm (hmono _ hR_ab) hS_ba

/-- **Monotonicity.** If `g R = a` and every voter raises `a` weakly (keeps it above everything
it was above), then `g` still chooses `a`. Proved by switching voters one at a time. -/
theorem monotone {g : SCF ι A} [Finite ι] (hsp : g.IsStrategyProof) {R R' : PrefProfile ι A}
    (hR : ∀ j, IsRanking (R j)) (hR' : ∀ j, IsRanking (R' j))
    (hmono : ∀ i b, R i (g R) b → R' i (g R) b) :
    g R' = g R := by
  have : Fintype ι := Fintype.ofFinite ι
  have hmix_rank : ∀ (T : Finset ι) j, IsRanking (mixProfile R R' T j) := by
    intro T j
    by_cases hj : j ∈ T
    · rw [mixProfile_mem hj]; exact hR' j
    · rw [mixProfile_not_mem hj]; exact hR j
  have key : ∀ T : Finset ι, g (mixProfile R R' T) = g R := by
    intro T
    induction T using Finset.induction with
    | empty => rw [mixProfile_empty]
    | insert i T hiT ih =>
      rw [mixProfile_insert hiT]
      have hcond : ∀ b, mixProfile R R' T i (g (mixProfile R R' T)) b →
          R' i (g (mixProfile R R' T)) b := by
        rw [ih, mixProfile_not_mem hiT]; exact hmono i
      rw [monotone_step hsp (hmix_rank T) (hR' i) hcond, ih]
  rw [← mixProfile_univ R R']
  exact key Finset.univ

/-! ### Unanimity and Pareto -/

/-- **Unanimity.** If every voter ranks `a` at the top, `g` chooses `a`. -/
theorem unanimous {g : SCF ι A} [Finite ι] (hsp : g.IsStrategyProof) (honto : g.IsOnto)
    {R : PrefProfile ι A} (hR : ∀ i, IsRanking (R i)) {a : A} (htop : ∀ i, IsTop (R i) a) :
    g R = a := by
  obtain ⟨R₀, hR₀, hg₀⟩ := honto a
  have hmono : ∀ i b, R₀ i (g R₀) b → R i (g R₀) b := by
    intro i b hb
    rw [hg₀] at hb ⊢
    exact htop i b ((hR₀ i).ne_of_rel hb).symm
  rw [monotone hsp hR₀ hR hmono, hg₀]

/-- **Weak Pareto.** If every voter strictly prefers `a` to `b`, then `g` does not choose `b`. -/
theorem pareto {g : SCF ι A} [Finite ι] (hsp : g.IsStrategyProof) (honto : g.IsOnto)
    {R : PrefProfile ι A} (hR : ∀ i, IsRanking (R i)) {a b : A} (hab : a ≠ b)
    (hdom : ∀ i, R i a b) : g R ≠ b := by
  intro hgb
  have hR' : ∀ i, IsRanking (putTop a (R i)) := fun i => (hR i).putTop a
  have htop : ∀ i, IsTop (putTop a (R i)) a := fun i c hc => putTop_top hc
  have hga : g (fun i => putTop a (R i)) = a := unanimous hsp honto hR' htop
  have hmono : ∀ i c, R i (g R) c → (fun i => putTop a (R i)) i (g R) c := by
    intro i c hc
    rw [hgb] at hc ⊢
    by_cases hca : c = a
    · subst hca; exact absurd hc ((hR i).asymm (hdom i))
    · exact (putTop_others (Ne.symm hab) hca).mpr hc
  have hmix := monotone hsp hR hR' hmono
  rw [hga, hgb] at hmix
  exact hab hmix

/-! ### The induced social welfare function -/

/-- If `g` chooses `x` from the lift of a block `p`, then `x` also wins the pairwise lift of
`{x, y}` for any `y ∈ p`: the winner of a lift beats everyone in it pairwise. -/
theorem lift_winner_beats {g : SCF ι A} [Finite ι] (hsp : g.IsStrategyProof)
    {R : PrefProfile ι A} (hR : ∀ i, IsRanking (R i)) {p : A → Prop} {x y : A}
    (hpx : p x) (hpy : p y)
    (hwin : g (fun i => raiseTop p (R i)) = x) :
    g (fun i => raiseTop (fun z => z = x ∨ z = y) (R i)) = x := by
  have hLp : ∀ i, IsRanking (raiseTop p (R i)) := fun i => raiseTop_ranking (hR i)
  have hLxy : ∀ i, IsRanking (raiseTop (fun z => z = x ∨ z = y) (R i)) :=
    fun i => raiseTop_ranking (hR i)
  have hmono : ∀ i w, raiseTop p (R i) x w →
      raiseTop (fun z => z = x ∨ z = y) (R i) x w := by
    intro i w hw
    by_cases hwx : w = x
    · rw [hwx] at hw; exact absurd hw ((hLp i).irrefl x)
    · by_cases hwy : w = y
      · rw [hwy] at hw ⊢
        have hr_xy : (R i) x y := (raiseTop_same (iff_of_true hpx hpy)).mp hw
        exact (raiseTop_same (p := fun z => z = x ∨ z = y)
          (iff_of_true (Or.inl rfl) (Or.inr rfl))).mpr hr_xy
      · exact raiseTop_above (Or.inl rfl) (fun h => h.elim hwx hwy)
  rw [monotone hsp hLp hLxy (by rw [hwin]; exact hmono), hwin]

/-- The social welfare function induced by an SCF: society strictly prefers `a` to `b` exactly
when `g` chooses `a` from the profile lifting `{a, b}` to the top. The `a ≠ b` guard makes it
irreflexive. -/
def inducedSWF (g : SCF ι A) : SWF ι A :=
  fun R a b => a ≠ b ∧ g (fun i => raiseTop (fun z => z = a ∨ z = b) (R i)) = a

/-- The pairwise lift selects one of the two lifted alternatives. -/
theorem induced_choice {g : SCF ι A} [Finite ι] (hsp : g.IsStrategyProof) (honto : g.IsOnto)
    {R : PrefProfile ι A} (hR : ∀ i, IsRanking (R i)) {a b : A} :
    g (fun i => raiseTop (fun z => z = a ∨ z = b) (R i)) = a ∨
    g (fun i => raiseTop (fun z => z = a ∨ z = b) (R i)) = b := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hna, hnb⟩ := hcon
  have hLrank : ∀ i, IsRanking (raiseTop (fun z => z = a ∨ z = b) (R i)) :=
    fun i => raiseTop_ranking (hR i)
  have hdom : ∀ i, raiseTop (fun z => z = a ∨ z = b) (R i) a
      (g (fun i => raiseTop (fun z => z = a ∨ z = b) (R i))) :=
    fun i => raiseTop_above (Or.inl rfl) (fun h => h.elim hna hnb)
  exact pareto hsp honto hLrank (Ne.symm hna) hdom rfl

omit [DecidableEq ι] in
/-- The pairwise lift of `{a, b}` and of `{b, a}` give the same outcome. -/
theorem induced_lift_swap (g : SCF ι A) (R : PrefProfile ι A) (a b : A) :
    g (fun i => raiseTop (fun z => z = a ∨ z = b) (R i)) =
    g (fun i => raiseTop (fun z => z = b ∨ z = a) (R i)) := by
  congr 1; funext i; exact raiseTop_congr (fun z => or_comm) (R i)

/-- The triple lift selects one of the three lifted alternatives. -/
theorem triple_choice {g : SCF ι A} [Finite ι] (hsp : g.IsStrategyProof) (honto : g.IsOnto)
    {R : PrefProfile ι A} (hR : ∀ i, IsRanking (R i)) {a b c : A} :
    g (fun i => raiseTop (fun z => z = a ∨ z = b ∨ z = c) (R i)) = a ∨
    g (fun i => raiseTop (fun z => z = a ∨ z = b ∨ z = c) (R i)) = b ∨
    g (fun i => raiseTop (fun z => z = a ∨ z = b ∨ z = c) (R i)) = c := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hna, hnb, hnc⟩ := hcon
  have hLrank : ∀ i, IsRanking (raiseTop (fun z => z = a ∨ z = b ∨ z = c) (R i)) :=
    fun i => raiseTop_ranking (hR i)
  have hdom : ∀ i, raiseTop (fun z => z = a ∨ z = b ∨ z = c) (R i) a
      (g (fun i => raiseTop (fun z => z = a ∨ z = b ∨ z = c) (R i))) :=
    fun i => raiseTop_above (Or.inl rfl) (fun h => by
      rcases h with h | h | h
      · exact hna h
      · exact hnb h
      · exact hnc h)
  exact pareto hsp honto hLrank (Ne.symm hna) hdom rfl

/-- **Collective rationality.** The induced SWF maps ranking profiles to rankings. Transitivity
is the crux: the winner of the triple lift beats each of the three pairwise, which pins it down. -/
theorem induced_isSWO {g : SCF ι A} [Finite ι] (hsp : g.IsStrategyProof) (honto : g.IsOnto) :
    (inducedSWF g).IsSWO := by
  intro R hR
  refine ⟨fun a hcon => hcon.1 rfl, ?_, ?_⟩
  · -- transitivity
    intro a b c hab hbc
    obtain ⟨hab_ne, hgab⟩ := hab
    obtain ⟨hbc_ne, hgbc⟩ := hbc
    have hac : a ≠ c := by
      intro h
      have Pba : g (fun i => raiseTop (fun z => z = b ∨ z = a) (R i)) = a :=
        (induced_lift_swap g R a b).symm.trans hgab
      simp only [h] at Pba
      exact hbc_ne (Pba.symm.trans hgbc).symm
    have h3 : g (fun i => raiseTop (fun z => z = a ∨ z = b ∨ z = c) (R i)) = a := by
      rcases triple_choice hsp honto hR with h | h | h
      · exact h
      · exfalso
        have hb := lift_winner_beats hsp hR (p := fun z => z = a ∨ z = b ∨ z = c)
          (x := b) (y := a) (Or.inr (Or.inl rfl)) (Or.inl rfl) h
        exact hab_ne (hgab.symm.trans ((induced_lift_swap g R a b).trans hb))
      · exfalso
        have hc := lift_winner_beats hsp hR (p := fun z => z = a ∨ z = b ∨ z = c)
          (x := c) (y := b) (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl)) h
        exact hbc_ne (hgbc.symm.trans ((induced_lift_swap g R b c).trans hc))
    exact ⟨hac, lift_winner_beats hsp hR (p := fun z => z = a ∨ z = b ∨ z = c)
      (x := a) (y := c) (Or.inl rfl) (Or.inr (Or.inr rfl)) h3⟩
  · -- totality
    intro a b hab
    rcases induced_choice hsp honto hR (a := a) (b := b) with h | h
    · exact Or.inl ⟨hab, h⟩
    · refine Or.inr ⟨hab.symm, ?_⟩
      rw [induced_lift_swap g R a b] at h
      exact h

/-- **Weak Pareto for the induced SWF.** -/
theorem induced_isParetoOnRankings {g : SCF ι A} [Finite ι] [Nonempty ι]
    (hsp : g.IsStrategyProof) (honto : g.IsOnto) : (inducedSWF g).IsParetoOnRankings := by
  intro R hR a b hdom
  have hab : a ≠ b := (hR (Classical.arbitrary ι)).ne_of_rel (hdom (Classical.arbitrary ι))
  refine ⟨hab, ?_⟩
  have hLrank : ∀ i, IsRanking (raiseTop (fun z => z = a ∨ z = b) (R i)) :=
    fun i => raiseTop_ranking (hR i)
  have hdom' : ∀ i, raiseTop (fun z => z = a ∨ z = b) (R i) a b := fun i =>
    (raiseTop_same (p := fun z => z = a ∨ z = b) (iff_of_true (Or.inl rfl) (Or.inr rfl))).mpr
      (hdom i)
  have hne := pareto hsp honto hLrank hab hdom'
  rcases induced_choice hsp honto hR (a := a) (b := b) with h | h
  · exact h
  · exact absurd h hne

/-- The pairwise-lift outcome depends only on each voter's `a`-vs-`b` ordering. -/
theorem induced_lift_eq {g : SCF ι A} [Finite ι] (hsp : g.IsStrategyProof) (honto : g.IsOnto)
    {R R' : PrefProfile ι A} (hR : ∀ i, IsRanking (R i)) (hR' : ∀ i, IsRanking (R' i))
    {a b : A} (hagree : ∀ i, (R i a b ↔ R' i a b) ∧ (R i b a ↔ R' i b a)) :
    g (fun i => raiseTop (fun z => z = a ∨ z = b) (R i)) =
    g (fun i => raiseTop (fun z => z = a ∨ z = b) (R' i)) := by
  have hLR : ∀ i, IsRanking (raiseTop (fun z => z = a ∨ z = b) (R i)) :=
    fun i => raiseTop_ranking (hR i)
  have hLR' : ∀ i, IsRanking (raiseTop (fun z => z = a ∨ z = b) (R' i)) :=
    fun i => raiseTop_ranking (hR' i)
  rcases induced_choice hsp honto hR (a := a) (b := b) with hw | hw
  · symm
    refine monotone hsp hLR hLR' ?_
    intro i v hv
    rw [hw] at hv ⊢
    by_cases hva : v = a
    · rw [hva] at hv; exact absurd hv ((hLR i).irrefl a)
    · by_cases hvb : v = b
      · rw [hvb] at hv ⊢
        exact (raiseTop_same (p := fun z => z = a ∨ z = b)
          (iff_of_true (Or.inl rfl) (Or.inr rfl))).mpr ((hagree i).1.mp
          ((raiseTop_same (p := fun z => z = a ∨ z = b)
            (iff_of_true (Or.inl rfl) (Or.inr rfl))).mp hv))
      · exact raiseTop_above (Or.inl rfl) (fun h => h.elim hva hvb)
  · symm
    refine monotone hsp hLR hLR' ?_
    intro i v hv
    rw [hw] at hv ⊢
    by_cases hvb : v = b
    · rw [hvb] at hv; exact absurd hv ((hLR i).irrefl b)
    · by_cases hva : v = a
      · rw [hva] at hv ⊢
        exact (raiseTop_same (p := fun z => z = a ∨ z = b)
          (iff_of_true (Or.inr rfl) (Or.inl rfl))).mpr ((hagree i).2.mp
          ((raiseTop_same (p := fun z => z = a ∨ z = b)
            (iff_of_true (Or.inr rfl) (Or.inl rfl))).mp hv))
      · exact raiseTop_above (Or.inr rfl) (fun h => h.elim hva hvb)

/-- **IIA for the induced SWF.** -/
theorem induced_isIIAOnRankings {g : SCF ι A} [Finite ι] (hsp : g.IsStrategyProof)
    (honto : g.IsOnto) : (inducedSWF g).IsIIAOnRankings := by
  intro R R' hR hR' a b hagree
  have hab_eq := induced_lift_eq hsp honto hR hR' hagree
  have hba_eq := induced_lift_eq hsp honto hR hR' (fun i => ⟨(hagree i).2, (hagree i).1⟩)
  refine ⟨?_, ?_⟩
  · unfold inducedSWF; rw [hab_eq]
  · unfold inducedSWF; rw [hba_eq]

/-! ### Reduction to Arrow -/

/-- A dictator of the induced SWF is a dictator of the SCF: if `d`'s pairwise preference always
governs society, then `g` always returns `d`'s top alternative. -/
theorem dictator_transfer {g : SCF ι A} [Finite ι] (hsp : g.IsStrategyProof)
    {d : ι} (hd : (inducedSWF g).IsDictatorOnRankings d) : g.IsDictator d := by
  intro R hR a hca
  rcases (hR d).total (g R) a hca.symm with hca' | hac
  · exact hca'
  obtain ⟨_, hgac⟩ := hd a (g R) R hR hac
  have hLac : ∀ i, IsRanking (raiseTop (fun z => z = a ∨ z = g R) (R i)) :=
    fun i => raiseTop_ranking (hR i)
  have hmono : ∀ i v, R i (g R) v → raiseTop (fun z => z = a ∨ z = g R) (R i) (g R) v := by
    intro i v hv
    by_cases hva : v = a
    · rw [hva] at hv ⊢
      exact (raiseTop_same (p := fun z => z = a ∨ z = g R)
        (iff_of_true (Or.inr rfl) (Or.inl rfl))).mpr hv
    · by_cases hvc : v = g R
      · rw [hvc] at hv; exact absurd hv ((hR i).irrefl (g R))
      · exact raiseTop_above (Or.inr rfl) (fun h => h.elim hva hvc)
  have hgR := monotone hsp hR hLac hmono
  rw [hgac] at hgR
  exact absurd hgR hca

/-- **Gibbard–Satterthwaite theorem.** A strategy-proof social choice function with at least
three alternatives in its range and a nonempty finite electorate is dictatorial. The
alternative type itself need not be finite. -/
theorem gibbard_satterthwaite {g : SCF ι A} [Nonempty ι] [Finite ι]
    (hsp : g.IsStrategyProof) (honto : g.IsOnto) (hA : HasAtLeastThree A) :
    ∃ d, g.IsDictator d := by
  obtain ⟨d, hd⟩ := arrow_impossibility (induced_isSWO hsp honto)
    (induced_isParetoOnRankings hsp honto) (induced_isIIAOnRankings hsp honto) hA
  exact ⟨d, dictator_transfer hsp hd⟩

/-- Finite-cardinality convenience form of Gibbard–Satterthwaite. -/
theorem gibbard_satterthwaite_of_natCard {g : SCF ι A} [Nonempty ι] [Finite ι] [Finite A]
    (hsp : g.IsStrategyProof) (honto : g.IsOnto) (hcard : 2 < Nat.card A) :
    ∃ d, g.IsDictator d :=
  gibbard_satterthwaite hsp honto (hasAtLeastThree_of_natCard hcard)

end SCF

end GameTheory
