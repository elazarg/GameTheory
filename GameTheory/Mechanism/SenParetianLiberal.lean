/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Mechanism.Arrow

/-!
# Sen's impossibility of a Paretian liberal

Sen's theorem (1970) sits beside Arrow's but trades hypotheses on both sides. It
*weakens* collective rationality all the way to **acyclicity** of the social
strict preference — the minimal condition guaranteeing a nonempty choice set on
every finite agenda — and it *replaces* non-dictatorship with **minimal
liberalism**: at least two individuals are each decisive over a personal pair of
alternatives (a protected sphere over which society defers to them). Even this
combination is inconsistent with the weak Pareto principle.

Two voters `p` and `q`, decisive over the distinct pairs `{a, b}` and `{c, d}`,
together with weak Pareto, force a social preference cycle, contradicting
acyclicity. The argument splits on whether the two protected pairs are disjoint or
share a single alternative:

* disjoint (four alternatives): `p` ranks `d ≻ a ≻ b ≻ c`, everyone else
  `b ≻ c ≻ d ≻ a`, so all agree on `b ≻ c` and `d ≻ a` (Pareto) while `p` supplies
  `a ≻ b` and `q` supplies `c ≻ d`, giving `a ≻ b ≻ c ≻ d ≻ a`;
* shared (three alternatives `x, y, z`, with `x` common): `p` ranks `x ≻ y ≻ z`,
  everyone else `y ≻ z ≻ x`, so all agree on `y ≻ z` (Pareto) while `p` supplies
  `x ≻ y` and `q` supplies `z ≻ x`, giving `x ≻ y ≻ z ≻ x`.

The development reuses the strict-ranking layer of `Arrow.lean` (`IsRanking`,
`putTop`, `Decides`, `SWF.IsParetoOnRankings`). Like Arrow it takes the
alternative set finite (a shared background ranking is read off an enumeration),
but it needs no finiteness of the electorate.

## Main definitions

* `IsAcyclic` — the transitive closure of a relation is irreflexive
* `SWF.IsSocialDecisionFunction` — society's strict preference is acyclic on every ranking profile
* `SWF.DecisiveOverPair` — a voter is decisive over an unordered pair (both directions)

## Main results

* `sen_paretian_liberal_disjoint` — the four-alternative case (disjoint protected pairs)
* `sen_paretian_liberal_shared` — the three-alternative case (pairs sharing one alternative)
* `sen_paretian_liberal` — no social decision function on rankings can satisfy weak Pareto
  together with two voters decisive over two distinct pairs
-/

namespace GameTheory

variable {ι A : Type}

/-- A strict preference relation is **acyclic** when its transitive closure is
irreflexive: no alternative is strictly preferred to itself through any chain of
strict preferences. This is exactly the condition that every finite set of
alternatives has a maximal element, so a choice function exists — the rationality
requirement Sen's theorem places on society. -/
def IsAcyclic (r : PrefRel A) : Prop := ∀ a, ¬ Relation.TransGen r a a

namespace SWF

/-- A **social decision function** maps every profile of rankings to an acyclic
social strict preference. This is Sen's weakening of Arrow's collective
rationality (`IsSWO`): only acyclicity — enough to guarantee a choice set — is
demanded of society, not a full transitive ranking. -/
def IsSocialDecisionFunction (f : SWF ι A) : Prop :=
  ∀ R : PrefProfile ι A, (∀ i, IsRanking (R i)) → IsAcyclic (f R)

/-- A voter `i` is **decisive over the pair `{x, y}`** if society follows `i`'s
strict preference between `x` and `y` in both directions, whatever the others
prefer. Minimal liberalism asserts that at least two voters have such a protected
pair. -/
def DecisiveOverPair (f : SWF ι A) (i : ι) (x y : A) : Prop :=
  Decides f i x y ∧ Decides f i y x

/-- Decisiveness over a pair is symmetric in the pair. -/
theorem DecisiveOverPair.symm {f : SWF ι A} {i : ι} {x y : A}
    (h : f.DecisiveOverPair i x y) : f.DecisiveOverPair i y x :=
  ⟨h.2, h.1⟩

end SWF

/-- **Sen's impossibility of a Paretian liberal**, disjoint-pairs case. There is no
social decision function on ranking profiles satisfying weak Pareto while granting
two distinct voters decisiveness over two *disjoint* pairs of alternatives: `p`
over `{a, b}` and `q` over `{c, d}`, with `a, b, c, d` pairwise distinct. -/
theorem sen_paretian_liberal_disjoint [Finite A] {f : SWF ι A}
    (hsdf : f.IsSocialDecisionFunction) (hpar : f.IsParetoOnRankings)
    {p q : ι} (hpq : p ≠ q) {a b c d : A}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hp : f.DecisiveOverPair p a b) (hq : f.DecisiveOverPair q c d) : False := by
  classical
  have : Fintype A := Fintype.ofFinite A
  -- a background ranking of the alternatives, read off an enumeration (as in Arrow)
  let e := Fintype.equivFin A
  let ρ : PrefRel A := fun s t => e s < e t
  have hρ : IsRanking ρ := by
    refine ⟨fun _ => lt_irrefl _, fun hxy hyz => lt_trans hxy hyz, fun x y hxy => ?_⟩
    rcases lt_or_gt_of_ne (e.injective.ne hxy) with h | h
    · exact Or.inl h
    · exact Or.inr h
  -- the two witness rankings, built by stacking the four alternatives on top of `ρ`
  set Rp : PrefRel A := putTop d (putTop a (putTop b (putTop c ρ))) with hRp -- d ≻ a ≻ b ≻ c
  set Rq : PrefRel A := putTop b (putTop c (putTop d (putTop a ρ))) with hRq -- b ≻ c ≻ d ≻ a
  have hRpr : IsRanking Rp := by rw [hRp]; exact (((hρ.putTop c).putTop b).putTop a).putTop d
  have hRqr : IsRanking Rq := by rw [hRq]; exact (((hρ.putTop a).putTop d).putTop c).putTop b
  -- the strict comparisons each witness contributes
  have Rp_ab : Rp a b := by
    rw [hRp]; exact (putTop_others had hbd).mpr (putTop_top (Ne.symm hab))
  have Rp_bc : Rp b c := by
    rw [hRp]
    exact (putTop_others hbd hcd).mpr
      ((putTop_others (Ne.symm hab) (Ne.symm hac)).mpr (putTop_top (Ne.symm hbc)))
  have Rp_da : Rp d a := by rw [hRp]; exact putTop_top had
  have Rq_cd : Rq c d := by
    rw [hRq]; exact (putTop_others (Ne.symm hbc) (Ne.symm hbd)).mpr (putTop_top (Ne.symm hcd))
  have Rq_bc : Rq b c := by rw [hRq]; exact putTop_top (Ne.symm hbc)
  have Rq_da : Rq d a := by
    rw [hRq]
    exact (putTop_others (Ne.symm hbd) hab).mpr
      ((putTop_others (Ne.symm hcd) hac).mpr (putTop_top had))
  -- the profile: `p` ranks `d ≻ a ≻ b ≻ c`, everyone else `b ≻ c ≻ d ≻ a`
  set R : PrefProfile ι A := fun i => if i = p then Rp else Rq with hR
  have hRp_eq : R p = Rp := by rw [hR]; exact if_pos rfl
  have hRq_eq : R q = Rq := by rw [hR]; exact if_neg (Ne.symm hpq)
  have hRprof : ∀ i, IsRanking (R i) := by
    intro i; simp only [hR]; split
    · exact hRpr
    · exact hRqr
  have hall_bc : ∀ i, R i b c := by
    intro i; simp only [hR]; split
    · exact Rp_bc
    · exact Rq_bc
  have hall_da : ∀ i, R i d a := by
    intro i; simp only [hR]; split
    · exact Rp_da
    · exact Rq_da
  -- the four social strict preferences forming the cycle
  have hab_soc : f R a b := hp.1 R hRprof (by rw [hRp_eq]; exact Rp_ab)
  have hcd_soc : f R c d := hq.1 R hRprof (by rw [hRq_eq]; exact Rq_cd)
  have hbc_soc : f R b c := hpar R hRprof b c hall_bc
  have hda_soc : f R d a := hpar R hRprof d a hall_da
  -- `a ≻ b ≻ c ≻ d ≻ a` is a cycle, contradicting acyclicity
  exact hsdf R hRprof a
    ((((Relation.TransGen.single hab_soc).tail hbc_soc).tail hcd_soc).tail hda_soc)

/-- **Sen's impossibility of a Paretian liberal**, shared-pair case. Two distinct
voters decisive over two pairs that share one alternative — `p` over `{x, y}` and
`q` over `{x, z}`, with `x, y, z` pairwise distinct — are inconsistent with weak
Pareto and acyclicity. -/
theorem sen_paretian_liberal_shared [Finite A] {f : SWF ι A}
    (hsdf : f.IsSocialDecisionFunction) (hpar : f.IsParetoOnRankings)
    {p q : ι} (hpq : p ≠ q) {x y z : A}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hp : f.DecisiveOverPair p x y) (hq : f.DecisiveOverPair q x z) : False := by
  classical
  have : Fintype A := Fintype.ofFinite A
  let e := Fintype.equivFin A
  let ρ : PrefRel A := fun s t => e s < e t
  have hρ : IsRanking ρ := by
    refine ⟨fun _ => lt_irrefl _, fun hst htu => lt_trans hst htu, fun s t hst => ?_⟩
    rcases lt_or_gt_of_ne (e.injective.ne hst) with h | h
    · exact Or.inl h
    · exact Or.inr h
  set Rp : PrefRel A := putTop x (putTop y (putTop z ρ)) with hRp -- x ≻ y ≻ z
  set Rq : PrefRel A := putTop y (putTop z (putTop x ρ)) with hRq -- y ≻ z ≻ x
  have hRpr : IsRanking Rp := by rw [hRp]; exact ((hρ.putTop z).putTop y).putTop x
  have hRqr : IsRanking Rq := by rw [hRq]; exact ((hρ.putTop x).putTop z).putTop y
  have Rp_xy : Rp x y := by rw [hRp]; exact putTop_top (Ne.symm hxy)
  have Rp_yz : Rp y z := by
    rw [hRp]
    exact (putTop_others (Ne.symm hxy) (Ne.symm hxz)).mpr (putTop_top (Ne.symm hyz))
  have Rq_yz : Rq y z := by rw [hRq]; exact putTop_top (Ne.symm hyz)
  have Rq_zx : Rq z x := by
    rw [hRq]
    exact (putTop_others (Ne.symm hyz) hxy).mpr (putTop_top hxz)
  set R : PrefProfile ι A := fun i => if i = p then Rp else Rq with hR
  have hRp_eq : R p = Rp := by rw [hR]; exact if_pos rfl
  have hRq_eq : R q = Rq := by rw [hR]; exact if_neg (Ne.symm hpq)
  have hRprof : ∀ i, IsRanking (R i) := by
    intro i; simp only [hR]; split
    · exact hRpr
    · exact hRqr
  have hall_yz : ∀ i, R i y z := by
    intro i; simp only [hR]; split
    · exact Rp_yz
    · exact Rq_yz
  have hxy_soc : f R x y := hp.1 R hRprof (by rw [hRp_eq]; exact Rp_xy)
  have hzx_soc : f R z x := hq.2 R hRprof (by rw [hRq_eq]; exact Rq_zx)
  have hyz_soc : f R y z := hpar R hRprof y z hall_yz
  -- `x ≻ y ≻ z ≻ x` is a cycle, contradicting acyclicity
  exact hsdf R hRprof x
    (((Relation.TransGen.single hxy_soc).tail hyz_soc).tail hzx_soc)

/-- **Sen's impossibility of a Paretian liberal.** No social decision function on
ranking profiles can satisfy weak Pareto together with minimal liberalism: two
distinct voters `p` and `q`, each decisive over a personal pair (`{a, b}` and
`{c, d}` respectively), where the two pairs are distinct. The pairs are either
disjoint or share a single alternative; both configurations force a social cycle. -/
theorem sen_paretian_liberal [Finite A] {f : SWF ι A}
    (hsdf : f.IsSocialDecisionFunction) (hpar : f.IsParetoOnRankings)
    {p q : ι} (hpq : p ≠ q) {a b c d : A} (hab : a ≠ b) (hcd : c ≠ d)
    (hpairs : ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)))
    (hp : f.DecisiveOverPair p a b) (hq : f.DecisiveOverPair q c d) : False := by
  by_cases hac : a = c
  · -- pairs share `a = c`: shared case over `{a, b}`, `{a, d}`
    have had : a ≠ d := by rw [hac]; exact hcd
    have hbd : b ≠ d := fun h => hpairs (Or.inl ⟨hac, h⟩)
    have hq' : f.DecisiveOverPair q a d := by rw [hac]; exact hq
    exact sen_paretian_liberal_shared hsdf hpar hpq hab had hbd hp hq'
  · by_cases had : a = d
    · -- pairs share `a = d`: shared case over `{a, b}`, `{a, c}`
      have hbc : b ≠ c := fun h => hpairs (Or.inr ⟨had, h⟩)
      have hq' : f.DecisiveOverPair q a c := by rw [had]; exact hq.symm
      exact sen_paretian_liberal_shared hsdf hpar hpq hab hac hbc hp hq'
    · by_cases hbc : b = c
      · -- pairs share `b = c`: shared case over `{b, a}`, `{b, d}`
        have hbd : b ≠ d := by rw [hbc]; exact hcd
        have hq' : f.DecisiveOverPair q b d := by rw [hbc]; exact hq
        exact sen_paretian_liberal_shared hsdf hpar hpq (Ne.symm hab) hbd had hp.symm hq'
      · by_cases hbd : b = d
        · -- pairs share `b = d`: shared case over `{b, a}`, `{b, c}`
          have hq' : f.DecisiveOverPair q b c := by rw [hbd]; exact hq.symm
          exact sen_paretian_liberal_shared hsdf hpar hpq (Ne.symm hab) hbc hac hp.symm hq'
        · -- all four alternatives distinct: disjoint case
          exact sen_paretian_liberal_disjoint hsdf hpar hpq hab hac had hbc hbd hcd hp hq

end GameTheory
