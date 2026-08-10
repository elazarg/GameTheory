/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Mechanism.FairDivision.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Indivisible Fair Division: Round-Robin

Choice round-robin for finite additive indivisible-goods instances with agents
ordered as `Fin n`. Agent `0` picks first, then turns cycle modulo `n`; each
agent chooses a remaining good maximizing their own item value.

For the EF1 guarantee, see R. J. Lipton, E. Markakis, E. Mossel, and
A. Saberi, “On Approximately Fair Allocations of Indivisible Goods,” EC 2004.
-/

open Finset BigOperators

namespace GameTheory.Mechanism.FairDivision

variable {n : ℕ} {G : Type}

/-- Private function-valued state used only by the recursive algorithm. -/
private abbrev RawAllocation (ι G : Type) := ι → Bundle G

/-- Replace one bundle in private recursive state without exposing a raw
function-update primitive. -/
private def updateBundle [DecidableEq ι] (A : RawAllocation ι G)
    (i : ι) (B : Bundle G) : RawAllocation ι G :=
  fun j => if j = i then B else A j

@[simp]
private theorem updateBundle_apply [DecidableEq ι]
    (A : RawAllocation ι G) (i : ι) (B : Bundle G) (j : ι) :
    updateBundle A i B j = if j = i then B else A j := rfl

@[simp]
private theorem updateBundle_same [DecidableEq ι]
    (i : ι) (B : Bundle G) (A : RawAllocation ι G) :
    updateBundle A i B i = B := by simp [updateBundle]

@[simp]
private theorem updateBundle_of_ne [DecidableEq ι] {i j : ι}
    (hji : j ≠ i) (B : Bundle G) (A : RawAllocation ι G) :
    updateBundle A i B j = A j := by simp [updateBundle, hji]

/-- A complete allocation over an explicit finite goods set. This is only used
inside the round-robin proof; public theorems specialize it to `Finset.univ` and
return the standard `IsAllocation`. -/
private def IsAllocationOn [Fintype ι] [DecidableEq G]
    (allGoods : Finset G) (A : RawAllocation ι G) : Prop :=
  (∀ i j : ι, i ≠ j → Disjoint (A i) (A j)) ∧
    allGoods = Finset.univ.biUnion A

/-- EF1 restricted to distinct agents with a nonempty envied bundle. For
nonnegative additive valuations it implies the public `IsEF1`. -/
private def IsEF1OnNonempty [DecidableEq G]
    (v : AdditiveValuation ι G) (A : RawAllocation ι G) : Prop :=
  ∀ i j : ι, i ≠ j → (A j).Nonempty →
    ∃ g ∈ A j, value v i (A j \ {g}) ≤ value v i (A i)

/-! ### Best-item selection -/

/-- `rawBestGood w i s hs` is a good in `s` that maximises `w i` over `s`.

    Defined noncomputably via `Classical.choose` on `Finset.exists_max_image`. Its
    key properties are `rawBestGood_mem` (membership) and `rawBestGood_le` (maximality). -/
private noncomputable def rawBestGood
    (w : AdditiveValuation (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) : G :=
  Classical.choose (Finset.exists_max_image s (w i) hs)

/-- `rawBestGood` lies in the candidate set `s`. -/
private lemma rawBestGood_mem
    (w : AdditiveValuation (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) :
    rawBestGood w i s hs ∈ s :=
  (Classical.choose_spec (Finset.exists_max_image s (w i) hs)).1

/-- Every element of `s` is no more valuable (to agent `i`) than `rawBestGood`. -/
private lemma rawBestGood_le
    (w : AdditiveValuation (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) {g : G} (hg : g ∈ s) :
    w i g ≤ w i (rawBestGood w i s hs) :=
  (Classical.choose_spec (Finset.exists_max_image s (w i) hs)).2 g hg

variable [NeZero n]

/-! ### Round-robin algorithm -/

/-- Recursive core of the choice round-robin.

    `rawRoundRobinAux w turn remaining A` distributes `remaining` one good at a time:
    `turn` picks the `rawBestGood` from `remaining`, it is added to `A turn`, and
    control passes to agent `(turn + 1) % n`. Terminates when `remaining = ∅`.

    Use `rawRoundRobinAlloc` (which starts with `turn = 0` and `A = fun _ => ∅`)
    rather than calling this directly. -/
private noncomputable def rawRoundRobinAux [DecidableEq G]
    (w : AdditiveValuation (Fin n) G)
    (turn : Fin n) (remaining : Finset G) (A : RawAllocation (Fin n) G) :
    RawAllocation (Fin n) G :=
  if h : remaining.Nonempty then
    let g := rawBestGood w turn remaining h
    rawRoundRobinAux w
      ⟨(turn.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
      (remaining.erase g)
      (updateBundle A turn (insert g (A turn)))
  else A
  termination_by remaining.card
  decreasing_by exact Finset.card_erase_lt_of_mem (rawBestGood_mem w turn remaining h)

/-- The complete choice round-robin allocation of `allGoods` among `n` agents.

    Agent 0 picks first. The `r`-th agent to pick is agent `r % n`. -/
private noncomputable def rawRoundRobinAlloc [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (allGoods : Finset G) : RawAllocation (Fin n) G :=
  rawRoundRobinAux w ⟨0, NeZero.pos n⟩ allGoods (fun _ => ∅)

/-! ### Unfolding lemmas -/

/-- `rawRoundRobinAux` with no remaining goods is the identity on the accumulator. -/
@[simp]
private lemma roundRobinAux_empty [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (turn : Fin n) (A : RawAllocation (Fin n) G) :
    rawRoundRobinAux w turn ∅ A = A := by
  rw [rawRoundRobinAux.eq_1]; simp [Finset.not_nonempty_empty]

/-- One unfolding step of `rawRoundRobinAux` when `remaining` is nonempty. -/
private lemma roundRobinAux_step [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (turn : Fin n)
    (remaining : Finset G) (A : RawAllocation (Fin n) G) (h : remaining.Nonempty) :
    rawRoundRobinAux w turn remaining A =
      rawRoundRobinAux w
        ⟨(turn.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
        (remaining.erase (rawBestGood w turn remaining h))
        (updateBundle A turn (insert (rawBestGood w turn remaining h) (A turn))) := by
  rw [rawRoundRobinAux.eq_1]; exact dif_pos h

/-! ### Partition properties -/

/-- Goods in the accumulator are never removed: `A i ⊆ (rawRoundRobinAux ... A) i`. -/
private lemma roundRobinAux_mono [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (turn : Fin n)
    (remaining : Finset G) (A : RawAllocation (Fin n) G) (i : Fin n) :
    A i ⊆ (rawRoundRobinAux w turn remaining A) i := by
  induction remaining using Finset.strongInductionOn generalizing turn A
  rename_i s ih
  by_cases hne : s.Nonempty
  · rw [roundRobinAux_step w turn s A hne]
    apply Finset.Subset.trans _ (ih _ (Finset.erase_ssubset (rawBestGood_mem w turn s hne)) _ _)
    simp only [updateBundle_apply]
    split_ifs with h
    · subst h; exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, roundRobinAux_empty]

/-- `rawRoundRobinAux` preserves bundle disjointness, provided `remaining` and `A` are disjoint. -/
private lemma roundRobinAux_disjoint [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (turn : Fin n)
    (remaining : Finset G) (A : RawAllocation (Fin n) G)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (A i) (A j))
    (hrem : ∀ g ∈ remaining, ∀ i : Fin n, g ∉ A i) :
    ∀ i j : Fin n, i ≠ j →
      Disjoint ((rawRoundRobinAux w turn remaining A) i)
               ((rawRoundRobinAux w turn remaining A) j) := by
  induction remaining using Finset.strongInductionOn generalizing turn A
  rename_i s ih
  by_cases hne : s.Nonempty
  · rw [roundRobinAux_step w turn s A hne]
    apply ih _ (Finset.erase_ssubset (rawBestGood_mem w turn s hne))
    · intro p q hpq
      simp only [updateBundle_apply]
      by_cases hp : p = turn <;> by_cases hq : q = turn
      · exact absurd (hp.trans hq.symm) hpq
      · rw [if_pos hp, if_neg hq]
        rw [Finset.disjoint_left]
        intro x hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact fun hxq => hrem _ (rawBestGood_mem w turn s hne) q hxq
        · exact Finset.disjoint_left.mp (hdisj turn q (by simpa [hp] using hpq)) hx
      · rw [if_neg hp, if_pos hq]
        rw [Finset.disjoint_left]
        intro x hx
        simp only [Finset.mem_insert]
        rintro (rfl | hxins)
        · exact hrem _ (rawBestGood_mem w turn s hne) p hx
        · exact Finset.disjoint_left.mp (hdisj p turn (by simpa [hq] using hpq)) hx hxins
      · rw [if_neg hp, if_neg hq]
        exact hdisj p q hpq
    · intro g' hg' i
      simp only [updateBundle_apply]
      by_cases hi : i = turn
      · rw [if_pos hi]
        simp only [Finset.mem_insert]
        rintro (rfl | hins)
        · exact (Finset.mem_erase.mp hg').1 rfl
        · exact hrem g' (Finset.erase_subset _ _ hg') turn (by simpa [hi] using hins)
      · rw [if_neg hi]
        exact hrem g' (Finset.erase_subset _ _ hg') i
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, roundRobinAux_empty]
    exact hdisj

/-- After `rawRoundRobinAux`, the union of all bundles equals `remaining ∪ ⋃_i A i`. -/
private lemma roundRobinAux_biUnion [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (turn : Fin n)
    (remaining : Finset G) (A : RawAllocation (Fin n) G)
    (hdisj : ∀ i j : Fin n, i ≠ j → Disjoint (A i) (A j))
    (hrem : ∀ g ∈ remaining, ∀ i : Fin n, g ∉ A i) :
    Finset.univ.biUnion (rawRoundRobinAux w turn remaining A) =
      remaining ∪ Finset.univ.biUnion A := by
  induction remaining using Finset.strongInductionOn generalizing turn A
  rename_i s ih
  by_cases hne : s.Nonempty
  · rw [roundRobinAux_step w turn s A hne]
    set g := rawBestGood w turn s hne with hg_def
    have hgmem : g ∈ s := rawBestGood_mem w turn s hne
    have hdisj' : ∀ p q : Fin n, p ≠ q →
        Disjoint (updateBundle A turn (insert g (A turn)) p)
                 (updateBundle A turn (insert g (A turn)) q) := by
      intro p q hpq; simp only [updateBundle_apply]
      by_cases hp : p = turn <;> by_cases hq : q = turn
      · exact absurd (hp.trans hq.symm) hpq
      · rw [if_pos hp, if_neg hq]; rw [Finset.disjoint_left]; intro x hx
        simp only [Finset.mem_insert] at hx; rcases hx with rfl | hx
        · exact fun hxq => hrem _ hgmem q hxq
        · exact Finset.disjoint_left.mp (hdisj turn q (by simpa [hp] using hpq)) hx
      · rw [if_neg hp, if_pos hq]; rw [Finset.disjoint_left]; intro x hx
        simp only [Finset.mem_insert]; rintro (rfl | hxins)
        · exact hrem _ hgmem p hx
        · exact Finset.disjoint_left.mp (hdisj p turn (by simpa [hq] using hpq)) hx hxins
      · rw [if_neg hp, if_neg hq]; exact hdisj p q hpq
    have hrem' : ∀ g' ∈ s.erase g, ∀ i : Fin n,
        g' ∉ updateBundle A turn (insert g (A turn)) i := by
      intro g' hg' i; simp only [updateBundle_apply]
      by_cases hi : i = turn
      · rw [if_pos hi]; simp only [Finset.mem_insert]; rintro (rfl | hins)
        · exact (Finset.mem_erase.mp hg').1 rfl
        · exact hrem g' (Finset.erase_subset _ _ hg') turn (by simpa [hi] using hins)
      · rw [if_neg hi]; exact hrem g' (Finset.erase_subset _ _ hg') i
    rw [ih _ (Finset.erase_ssubset hgmem) _ _ hdisj' hrem']
    have hbij : Finset.univ.biUnion (updateBundle A turn (insert g (A turn))) =
        {g} ∪ Finset.univ.biUnion A := by
      ext x
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union,
                 Finset.mem_singleton, updateBundle_apply]
      constructor
      · rintro ⟨i, hi⟩
        by_cases h : i = turn
        · simp only [h, if_true] at hi; simp only [Finset.mem_insert] at hi
          rcases hi with rfl | hmem
          · exact Or.inl rfl
          · exact Or.inr ⟨turn, by simpa [h] using hmem⟩
        · simp only [h, if_false] at hi; exact Or.inr ⟨i, hi⟩
      · rintro (rfl | ⟨i, hi⟩)
        · exact ⟨turn, by simp [Finset.mem_insert]⟩
        · by_cases h : i = turn
          · exact ⟨turn, by
              have hi' : x ∈ A turn := by simpa [h] using hi
              simp [Finset.mem_insert, hi']⟩
          · exact ⟨i, by simp [h, hi]⟩
    rw [hbij, ← Finset.union_assoc]
    congr 1
    rw [Finset.union_comm, ← Finset.insert_eq, Finset.insert_erase hgmem]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne, roundRobinAux_empty, Finset.empty_union]

/-- `rawRoundRobinAlloc` produces a complete partition of `allGoods`. -/
private theorem rawRoundRobinAlloc_isAllocation [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (allGoods : Finset G) :
    IsAllocationOn allGoods (rawRoundRobinAlloc w allGoods) := by
  constructor
  · intro i j hij
    exact roundRobinAux_disjoint w ⟨0, NeZero.pos n⟩ allGoods (fun _ => ∅)
      (fun i j _ => Finset.disjoint_empty_left _)
      (fun g _hg i hi => absurd hi (Finset.notMem_empty g))
      i j hij
  · have hb := roundRobinAux_biUnion w ⟨0, NeZero.pos n⟩ allGoods (fun _ => ∅)
      (fun i j _ => Finset.disjoint_empty_left _)
      (fun g _hg i hi => absurd hi (Finset.notMem_empty g))
    show allGoods =
      Finset.univ.biUnion (rawRoundRobinAux w ⟨0, NeZero.pos n⟩ allGoods (fun _ => ∅))
    rw [hb]
    simp

/-! ### EF1 correctness -/

/-- **Key lemma — no envy when picking earlier** (`i.val < j.val`).

    Since agent `i` picks before `j` in every round, when `i` picks `i_r` in round `r`,
    agent `j`'s round-`r` good `j_r` is still available. By `rawBestGood_le`:
    `w i i_r ≥ w i j_r`. Summing over all rounds:
    `v_i(A_i) ≥ v_i(A_j)` — agent `i` never envies agent `j` at all. -/
private lemma roundRobin_noEnvy_of_earlier
    [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (allGoods : Finset G)
    (hnn : ∀ (i : Fin n) (g : G), 0 ≤ w i g)
    (i j : Fin n) (hij : i.val < j.val) :
    value w i ((rawRoundRobinAlloc w allGoods) j) ≤
    value w i ((rawRoundRobinAlloc w allGoods) i) := by
  -- Strengthen to an invariant on `rawRoundRobinAux`:
  --   hinvI:  v_i(A_j) ≤ v_i(A_i)
  --   hinvII: when i already picked this round but j hasn't yet,
  --           every remaining good g satisfies v_i(A_j) + w_i(g) ≤ v_i(A_i)
  suffices h : ∀ (turn : Fin n) (remaining : Finset G) (A : RawAllocation (Fin n) G),
      (∀ p q : Fin n, p ≠ q → Disjoint (A p) (A q)) →
      (∀ g ∈ remaining, ∀ k : Fin n, g ∉ A k) →
      value w i (A j) ≤ value w i (A i) →
      (i.val < turn.val ∧ turn.val ≤ j.val →
        ∀ g ∈ remaining, value w i (A j) + w i g ≤
            value w i (A i)) →
      value w i ((rawRoundRobinAux w turn remaining A) j) ≤
      value w i ((rawRoundRobinAux w turn remaining A) i) by
    unfold rawRoundRobinAlloc; apply h
    · intro p q _; exact Finset.disjoint_empty_left _
    · intro g _ k hk; exact absurd hk (Finset.notMem_empty g)
    · simp [value]
    · intro ⟨h1, _⟩; exact absurd h1 (Nat.not_lt_zero i.val)
  intro turn remaining
  induction remaining using Finset.strongInductionOn generalizing turn
  rename_i s ih
  intro A hdisj hrem hinvI hinvII
  by_cases hne : s.Nonempty
  swap
  · -- Base: s = ∅
    simp only [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, roundRobinAux_empty]; exact hinvI
  · -- Step: s nonempty
    rw [roundRobinAux_step w turn s A hne]
    set g := rawBestGood w turn s hne with hg_def
    have hgmem : g ∈ s := rawBestGood_mem w turn s hne
    have hg_not : ∀ k : Fin n, g ∉ A k := hrem g hgmem
    have hij_ne : (i : Fin n) ≠ j := Fin.ne_of_val_ne (Nat.ne_of_lt hij)
    apply ih (s.erase g) (Finset.erase_ssubset hgmem)
      ⟨(turn.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
      (updateBundle A turn (insert g (A turn)))
    -- Disjointness preserved
    · intro p q hpq; simp only [updateBundle_apply]
      by_cases hp : p = turn <;> by_cases hq : q = turn
      · exact absurd (hp.trans hq.symm) hpq
      · rw [if_pos hp, if_neg hq, Finset.disjoint_left]
        intro x hx; simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact fun hxq => (hg_not q) hxq
        · exact Finset.disjoint_left.mp (hdisj turn q (by simpa [hp] using hpq)) hx
      · rw [if_neg hp, if_pos hq, Finset.disjoint_left]
        intro x hx; simp only [Finset.mem_insert]
        rintro (rfl | hxins)
        · exact (hg_not p) hx
        · exact Finset.disjoint_left.mp (hdisj p turn (by simpa [hq] using hpq)) hx hxins
      · rw [if_neg hp, if_neg hq]; exact hdisj p q hpq
    -- Remaining goods not in bundles
    · intro g' hg' k; simp only [updateBundle_apply]
      by_cases hk : k = turn
      · rw [if_pos hk]; simp only [Finset.mem_insert]
        rintro (rfl | hins)
        · exact (Finset.mem_erase.mp hg').1 rfl
        · exact hrem g' (Finset.erase_subset _ _ hg') turn (by simpa [hk] using hins)
      · rw [if_neg hk]; exact hrem g' (Finset.erase_subset _ _ hg') k
    -- hinvI': no-envy invariant maintained
    · by_cases hi : i = turn <;> by_cases hj : j = turn
      · exact absurd (hi.trans hj.symm) hij_ne
      · -- turn = i: i picks g; A'[j] = A j, A'[i] = insert g (A i)
        have h1 := updateBundle_of_ne hj (insert g (A turn)) A
        have h2 : updateBundle A turn (insert g (A turn)) i = insert g (A i) := by
          rw [hi]; exact updateBundle_same turn _ A
        rw [h1, h2]; simp only [value]
        have hg_not_i : g ∉ A i := by simpa [hi] using hg_not turn
        rw [Finset.sum_insert hg_not_i]
        exact le_trans hinvI (le_add_of_nonneg_left (hnn i g))
      · -- turn = j: j picks g; A'[j] = insert g (A j), A'[i] = A i
        have h1 : updateBundle A turn (insert g (A turn)) j = insert g (A j) := by
          rw [hj]; exact updateBundle_same turn _ A
        have h2 := updateBundle_of_ne hi (insert g (A turn)) A
        rw [h1, h2]; simp only [value]
        have hg_not_j : g ∉ A j := by simpa [hj] using hg_not turn
        rw [Finset.sum_insert hg_not_j]
        have := hinvII ⟨by rw [← hj]; exact hij, by rw [← hj]⟩ g hgmem
        simp only [value] at this; rw [add_comm]; exact this
      · -- turn ≠ i, turn ≠ j: bundles unchanged
        have h1 := updateBundle_of_ne hj (insert g (A turn)) A
        have h2 := updateBundle_of_ne hi (insert g (A turn)) A
        rw [h1, h2]; exact hinvI
    -- hinvII': headroom invariant maintained
    · intro ⟨hlt_turn', hle_turn'⟩ g' hg'
      simp only at hlt_turn' hle_turn'
      by_cases hi : i = turn <;> by_cases hj : j = turn
      · exact absurd (hi.trans hj.symm) hij_ne
      · -- turn = i: i picks g = rawBestGood w i s (since turn = i)
        have h1 := updateBundle_of_ne hj (insert g (A turn)) A
        have h2 : updateBundle A turn (insert g (A turn)) i = insert g (A i) := by
          rw [hi]; exact updateBundle_same turn _ A
        rw [h1, h2]; simp only [value]
        have hg_not_i : g ∉ A i := by simpa [hi] using hg_not turn
        rw [Finset.sum_insert hg_not_i]
        have hle : w i g' ≤ w i g := by
          rw [hg_def, ← hi]; exact rawBestGood_le w i s hne (Finset.erase_subset _ _ hg')
        have hab := add_le_add hinvI hle
        simp only [value] at hab
        rw [add_comm (w i g)]; exact hab
      · -- turn = j: vacuous (turn' > j or wraps to 0)
        exfalso
        have hteq : turn.val = j.val := congrArg Fin.val hj.symm
        have hjn : j.val + 1 ≤ n := Nat.succ_le_of_lt j.isLt
        rcases Nat.eq_or_lt_of_le hjn with h | h
        · -- j.val + 1 = n, so (turn.val+1) % n = 0
          have : (turn.val + 1) % n = 0 := by rw [hteq, h, Nat.mod_self]
          omega
        · -- j.val + 1 < n, so (turn.val+1) % n = j.val + 1 > j.val
          have : (turn.val + 1) % n = j.val + 1 := by
            rw [hteq, Nat.mod_eq_of_lt h]
          omega
      · -- turn ≠ i, turn ≠ j: bundles unchanged, deduce old condition
        have h1 := updateBundle_of_ne hj (insert g (A turn)) A
        have h2 := updateBundle_of_ne hi (insert g (A turn)) A
        rw [h1, h2]
        have : turn.val + 1 ≤ n := Nat.succ_le_of_lt turn.isLt
        rcases Nat.eq_or_lt_of_le this with h | h
        · rw [h, Nat.mod_self] at hlt_turn'; omega
        · rw [Nat.mod_eq_of_lt h] at hlt_turn' hle_turn'
          have hi_lt : i.val < turn.val := by
            rcases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hlt_turn') with heq | hlt
            · exact absurd (Fin.ext_iff.mpr heq : i = turn) hi
            · exact hlt
          exact hinvII ⟨hi_lt, by omega⟩ g' (Finset.erase_subset _ _ hg')

/-- **Key lemma — EF1 witness when picking later** (`j.val < i.val`).

    Since agent `j` picks before `i` in every round, when `i` picks `i_r` in round `r`,
    agent `j`'s *next* good `j_{r+1}` (to be picked in round `r+1`) is still available.
    By `rawBestGood_le`: `w i i_r ≥ w i j_{r+1}`. Telescoping:
    `v_i(A_i) ≥ Σ_r v_i(j_{r+1}) = v_i(A_j) − v_i(j_0)`,
    where `j_0` is `j`'s first picked good. So `j_0` is the EF1 witness. -/
private lemma roundRobin_ef1_of_later
    [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (allGoods : Finset G)
    (hnn : ∀ (i : Fin n) (g : G), 0 ≤ w i g)
    (i j : Fin n) (hij : j.val < i.val)
    (hne : ((rawRoundRobinAlloc w allGoods) j).Nonempty) :
    ∃ g ∈ (rawRoundRobinAlloc w allGoods) j,
      value w i ((rawRoundRobinAlloc w allGoods) j \ {g}) ≤
      value w i ((rawRoundRobinAlloc w allGoods) i) := by
  -- Strengthen to a two-phase invariant on `rawRoundRobinAux`:
  --   Phase 1 (A j = ∅, turn ≤ j): j hasn't picked yet.
  --   Phase 2 (∃ g0 ∈ A j): j already picked g0; v_i(A_j \ {g0}) ≤ v_i(A_i),
  --     with headroom ∀ g ∈ remaining, v_i(A_j\{g0}) + w_i(g) ≤ v_i(A_i)
  --     available when i has already picked this cycle (guard: i < turn ∨ turn ≤ j).
  --   Guard analysis:
  --     turn = j: guard is true (j ≤ j), headroom available for j's pick.
  --     turn = i: guard is false, headroom vacuous input; i establishes headroom.
  --     turn between j+1..i-1: guard false, headroom vacuous (pass-through).
  --     turn between i+1..n-1 or 0..j-1: guard true, headroom maintained.
  suffices h : ∀ (turn : Fin n) (remaining : Finset G) (A : RawAllocation (Fin n) G),
      (∀ p q : Fin n, p ≠ q → Disjoint (A p) (A q)) →
      (∀ g ∈ remaining, ∀ k : Fin n, g ∉ A k) →
      ((A j = ∅ ∧ turn.val ≤ j.val) ∨
       (∃ g0 ∈ A j,
         value w i (A j \ {g0}) ≤ value w i (A i) ∧
         (i.val < turn.val ∨ turn.val ≤ j.val →
           ∀ g ∈ remaining,
             value w i (A j \ {g0}) + w i g ≤
               value w i (A i)))) →
      (∃ g0 ∈ (rawRoundRobinAux w turn remaining A) j,
        value w i ((rawRoundRobinAux w turn remaining A) j \ {g0}) ≤
        value w i ((rawRoundRobinAux w turn remaining A) i)) ∨
      (rawRoundRobinAux w turn remaining A) j = ∅ by
    unfold rawRoundRobinAlloc
    rcases h ⟨0, NeZero.pos n⟩ allGoods (fun _ => ∅)
        (fun p q _ => Finset.disjoint_empty_left _)
        (fun g _ k hk => absurd hk (Finset.notMem_empty g))
        (Or.inl ⟨rfl, Nat.zero_le _⟩) with ⟨g0, hg0, hef1⟩ | hempty
    · exact ⟨g0, hg0, hef1⟩
    · exact absurd hempty (Finset.Nonempty.ne_empty hne)
  intro turn remaining
  induction remaining using Finset.strongInductionOn generalizing turn
  rename_i s ih
  intro A hdisj hrem hphase
  by_cases hne_s : s.Nonempty
  swap
  · -- Base: s = ∅
    simp only [Finset.not_nonempty_iff_eq_empty] at hne_s
    rw [hne_s, roundRobinAux_empty]
    rcases hphase with ⟨hempty, _⟩ | ⟨g0, hg0, hef1, _⟩
    · right; exact hempty
    · left; exact ⟨g0, hg0, hef1⟩
  · -- Step: s nonempty
    rw [roundRobinAux_step w turn s A hne_s]
    set g := rawBestGood w turn s hne_s with hg_def
    have hgmem : g ∈ s := rawBestGood_mem w turn s hne_s
    have hg_not : ∀ k : Fin n, g ∉ A k := hrem g hgmem
    have hij_ne : j ≠ i := Fin.ne_of_val_ne (Nat.ne_of_lt hij)
    -- Helper: compute (turn.val + 1) % n
    have htn : turn.val + 1 ≤ n := Nat.succ_le_of_lt turn.isLt
    apply ih (s.erase g) (Finset.erase_ssubset hgmem)
      ⟨(turn.val + 1) % n, Nat.mod_lt _ (NeZero.pos n)⟩
      (updateBundle A turn (insert g (A turn)))
    -- Disjointness preserved
    · intro p q hpq; simp only [updateBundle_apply]
      by_cases hp : p = turn <;> by_cases hq : q = turn
      · exact absurd (hp.trans hq.symm) hpq
      · rw [if_pos hp, if_neg hq, Finset.disjoint_left]
        intro x hx; simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact fun hxq => (hg_not q) hxq
        · exact Finset.disjoint_left.mp (hdisj turn q (by simpa [hp] using hpq)) hx
      · rw [if_neg hp, if_pos hq, Finset.disjoint_left]
        intro x hx; simp only [Finset.mem_insert]
        rintro (rfl | hxins)
        · exact (hg_not p) hx
        · exact Finset.disjoint_left.mp (hdisj p turn (by simpa [hq] using hpq)) hx hxins
      · rw [if_neg hp, if_neg hq]; exact hdisj p q hpq
    -- Remaining goods not in bundles
    · intro g' hg' k; simp only [updateBundle_apply]
      by_cases hk : k = turn
      · rw [if_pos hk]; simp only [Finset.mem_insert]
        rintro (rfl | hins)
        · exact (Finset.mem_erase.mp hg').1 rfl
        · exact hrem g' (Finset.erase_subset _ _ hg') turn (by simpa [hk] using hins)
      · rw [if_neg hk]; exact hrem g' (Finset.erase_subset _ _ hg') k
    -- Phase invariant maintained
    · rcases hphase with ⟨hempty, hturn_le⟩ | ⟨g0, hg0mem, hef1, hhead⟩
      · -- Phase 1: A[j] = ∅, turn.val ≤ j.val
        by_cases hj : j = turn
        · -- j = turn: j picks g, transitioning to Phase 2
          have h_Aj : updateBundle A turn (insert g (A turn)) j = insert g (A j) := by
            rw [hj]; exact updateBundle_same turn _ A
          have h_Ai : updateBundle A turn (insert g (A turn)) i = A i :=
            updateBundle_of_ne (fun h => hij_ne (hj.trans h.symm)) _ _
          right; refine ⟨g, ?_, ?_, ?_⟩
          · rw [h_Aj]; exact Finset.mem_insert_self g (A j)
          · -- v_i(insert g (A j) \ {g}) = v_i(∅) = 0 ≤ v_i(A i)
            rw [h_Aj, Finset.sdiff_singleton_eq_erase, Finset.erase_insert (by
              rw [hempty]; exact Finset.notMem_empty g)]
            rw [h_Ai, hempty]; simp only [value, Finset.sum_empty]
            exact Finset.sum_nonneg (fun x _ => hnn i x)
          · -- Headroom guard: i < turn' ∨ turn' ≤ j → ...
            -- turn' = (j+1) % n. Since j < i < n, j+1 ≤ i < n, so turn' = j+1.
            -- Guard: i < j+1 ∨ j+1 ≤ j. First: j+1 > i ↔ j ≥ i, contradicts j < i.
            -- Second: j+1 ≤ j is false. So guard is false. Headroom vacuous.
            intro hguard; exfalso
            have hjlt : j.val + 1 < n := Nat.lt_of_lt_of_le (Nat.succ_lt_succ hij) i.isLt
            have htv : (turn.val + 1) % n = j.val + 1 := by
              rw [congrArg Fin.val hj.symm, Nat.mod_eq_of_lt hjlt]
            simp only at hguard; rcases hguard with h | h <;> omega
        · -- turn ≠ j (turn.val < j.val): other agent picks, stay in Phase 1
          have hi : i ≠ turn := by
            intro h; rw [h] at hij; exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le hij hturn_le)
          left; constructor
          · rw [updateBundle_of_ne hj]; exact hempty
          · have hturn_lt_j : turn.val < j.val :=
              Nat.lt_of_le_of_ne hturn_le (fun h => hj (Fin.ext_iff.mpr h.symm))
            rcases Nat.eq_or_lt_of_le htn with h | h
            · have : (turn.val + 1) % n = 0 := by rw [h, Nat.mod_self]
              simp only [this]; exact Nat.zero_le _
            · have : (turn.val + 1) % n = turn.val + 1 := Nat.mod_eq_of_lt h
              simp only [this]; omega
      · -- Phase 2: ∃ g0 ∈ A j, EF1 + conditional headroom
        by_cases hi : i = turn <;> by_cases hj : j = turn
        · exact absurd (hj.trans hi.symm) hij_ne
        · -- turn = i: i picks g = rawBestGood w i s; establish headroom
          have h_Aj : updateBundle A turn (insert g (A turn)) j = A j :=
            updateBundle_of_ne hj _ _
          have h_Ai : updateBundle A turn (insert g (A turn)) i = insert g (A i) := by
            rw [hi]; exact updateBundle_same turn _ A
          right; refine ⟨g0, ?_, ?_, ?_⟩
          · rw [h_Aj]; exact hg0mem
          · -- EF1: v_i(A j \ {g0}) ≤ v_i(insert g (A i))
            rw [h_Aj, h_Ai]; simp only [value]
            have hg_not_i : g ∉ A i := by simpa [hi] using hg_not turn
            rw [Finset.sum_insert hg_not_i]
            exact le_trans hef1 (le_add_of_nonneg_left (hnn i g))
          · -- Headroom: i < turn' ∨ turn' ≤ j → ∀ g' ∈ s.erase g, ...
            -- turn' = (i+1) % n. Guard: i < (i+1)%n ∨ (i+1)%n ≤ j.
            -- If i+1 < n: turn' = i+1, first disjunct true.
            -- If i+1 = n: turn' = 0, second disjunct: 0 ≤ j, true (j : Fin n).
            -- Either way, guard is true, so we need to ESTABLISH headroom.
            intro _hguard g' hg'
            rw [h_Aj, h_Ai]; simp only [value]
            have hg_not_i : g ∉ A i := by simpa [hi] using hg_not turn
            rw [Finset.sum_insert hg_not_i]
            -- g = rawBestGood w i s (since turn = i), so w_i(g') ≤ w_i(g)
            have hle : w i g' ≤ w i g := by
              rw [hg_def, ← hi]; exact rawBestGood_le w i s hne_s (Finset.erase_subset _ _ hg')
            have hab := add_le_add hef1 hle
            simp only [value] at hab
            rw [add_comm (w i g)]; exact hab
        · -- turn = j: j picks g; use headroom to prove EF1
          have h_Aj : updateBundle A turn (insert g (A turn)) j = insert g (A j) := by
            rw [hj]; exact updateBundle_same turn _ A
          have h_Ai : updateBundle A turn (insert g (A turn)) i = A i :=
            updateBundle_of_ne hi _ _
          -- Guard for current turn is true: i < turn ∨ turn ≤ j.
          -- turn = j, so turn ≤ j (second disjunct). Guard is true.
          have hguard : i.val < turn.val ∨ turn.val ≤ j.val :=
            Or.inr (le_of_eq (congrArg Fin.val hj.symm))
          right; refine ⟨g0, ?_, ?_, ?_⟩
          · rw [h_Aj]; exact Finset.mem_insert_of_mem hg0mem
          · -- v_i(insert g (A j) \ {g0}) ≤ v_i(A i)
            have hg_ne_g0 : g ≠ g0 := fun h =>
              hg_not j (by simpa [h] using hg0mem)
            rw [h_Aj, h_Ai]
            have hsdiff : insert g (A j) \ {g0} = insert g (A j \ {g0}) := by
              ext x; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
              constructor
              · rintro ⟨hx | hx, hne⟩
                · exact Or.inl hx
                · exact Or.inr ⟨hx, hne⟩
              · rintro (rfl | ⟨hx, hne⟩)
                · exact ⟨Or.inl rfl, hg_ne_g0⟩
                · exact ⟨Or.inr hx, hne⟩
            rw [hsdiff]; simp only [value]
            have hg_not_sdiff : g ∉ A j \ {g0} :=
              fun h => hg_not j (Finset.mem_sdiff.mp h).1
            rw [Finset.sum_insert hg_not_sdiff]
            have := hhead hguard g hgmem
            simp only [value] at this
            rw [add_comm]; exact this
          · -- New headroom guard: i < turn' ∨ turn' ≤ j → ...
            -- turn' = (j+1)%n. Since j < i < n, j+1 ≤ i, j+1 < n, turn' = j+1.
            -- Guard: i < j+1 (false since j < i) or j+1 ≤ j (false). Guard false, vacuous.
            intro hguard'; exfalso
            have hjlt : j.val + 1 < n := Nat.lt_of_lt_of_le (Nat.succ_lt_succ hij) i.isLt
            have htv : (turn.val + 1) % n = j.val + 1 := by
              rw [congrArg Fin.val hj.symm, Nat.mod_eq_of_lt hjlt]
            simp only at hguard'; rcases hguard' with h | h <;> omega
        · -- turn ≠ i, turn ≠ j: bundles unchanged, pass through
          have h_Aj : updateBundle A turn (insert g (A turn)) j = A j :=
            updateBundle_of_ne hj _ _
          have h_Ai : updateBundle A turn (insert g (A turn)) i = A i :=
            updateBundle_of_ne hi _ _
          right; refine ⟨g0, ?_, ?_, ?_⟩
          · rw [h_Aj]; exact hg0mem
          · rw [h_Aj, h_Ai]; exact hef1
          · -- Headroom: if guard was true for turn, it stays true for turn'
            -- (or was false and stays false)
            intro hguard' g' hg'
            rw [h_Aj, h_Ai]
            -- Deduce guard was true for turn from guard being true for turn'
            simp only at hguard'
            have hguard_old : i.val < turn.val ∨ turn.val ≤ j.val := by
              rcases Nat.eq_or_lt_of_le htn with h | h
              · -- turn+1 = n, turn' = 0
                rw [h, Nat.mod_self] at hguard'
                rcases hguard' with h' | h'
                · omega
                · left; omega
              · -- turn+1 < n, turn' = turn+1
                rw [Nat.mod_eq_of_lt h] at hguard'
                rcases hguard' with h' | h'
                · left; omega
                · right; omega
            exact hhead hguard_old g' (Finset.erase_subset _ _ hg')

/-- **Round-robin gives EF1** for additive valuations with nonneg weights.

    For `i.val < j.val`: `roundRobin_noEnvy_of_earlier` gives no envy; monotonicity
    (`toValuation_mono`) then makes any good from `A j` a valid EF1 witness.
    For `j.val < i.val`: `roundRobin_ef1_of_later` provides `j`'s first good as witness.

    [Lipton et al. 2004; AGT Ch.11] -/
private theorem rawRoundRobinAlloc_isEF1
    [DecidableEq G]
    (w : AdditiveValuation (Fin n) G) (allGoods : Finset G)
    (hnn : ∀ (i : Fin n) (g : G), 0 ≤ w i g) :
    IsEF1OnNonempty w (rawRoundRobinAlloc w allGoods) := by
  intro i j hij hne
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · -- Case i.val < j.val: agent i never envies j; any good from A j is a witness
    obtain ⟨g, hg⟩ := hne
    exact ⟨g, hg, le_trans
      (value_mono hnn i Finset.sdiff_subset)
      (roundRobin_noEnvy_of_earlier w allGoods hnn i j hlt)⟩
  · -- Case j.val < i.val: j's first good is the EF1 witness
    exact roundRobin_ef1_of_later w allGoods hnn i j hgt hne


/-! ### Public API -/

/-- `bestGood v i s hs` is a good in `s` maximizing agent `i`'s item value. -/
noncomputable def bestGood [DecidableEq G]
    (v : AdditiveValuation (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) : G :=
  rawBestGood v i s hs

omit [NeZero n] in
/-- `bestGood` lies in the candidate set. -/
lemma bestGood_mem [DecidableEq G]
    (v : AdditiveValuation (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) :
    bestGood v i s hs ∈ s :=
  rawBestGood_mem v i s hs

omit [NeZero n] in
/-- Every candidate good has no larger value than `bestGood`. -/
lemma bestGood_le [DecidableEq G]
    (v : AdditiveValuation (Fin n) G) (i : Fin n)
    (s : Finset G) (hs : s.Nonempty) {g : G} (hg : g ∈ s) :
    v i g ≤ v i (bestGood v i s hs) :=
  rawBestGood_le v i s hs hg

omit [NeZero n] in
private theorem isComplete_of_isAllocationOn_univ [Fintype G] [DecidableEq G]
    {A : RawAllocation (Fin n) G}
    (hA : IsAllocationOn (Finset.univ : Finset G) A) :
    ∀ g : G, ∃ i : Fin n, g ∈ A i := by
  intro g
  have hg : g ∈ Finset.univ.biUnion A := by
    rw [← hA.2]
    exact Finset.mem_univ g
  simpa [Finset.mem_biUnion] using hg

omit [NeZero n] in
private theorem raw_isEF1_of_isEF1OnNonempty [DecidableEq G]
    {v : AdditiveValuation (Fin n) G} {A : RawAllocation (Fin n) G}
    (hnn : Nonnegative v) (hcore : IsEF1OnNonempty v A) :
    ∀ i j, value v i (A i) ≥ value v i (A j) ∨
      ∃ g ∈ A j, value v i (A i) ≥ value v i ((A j).erase g) := by
  intro i j
  by_cases hij : i = j
  · subst j
    exact Or.inl le_rfl
  · by_cases hAj : (A j).Nonempty
    · rcases hcore i j hij hAj with ⟨g, hg, hle⟩
      exact Or.inr ⟨g, hg, by simpa [Finset.sdiff_singleton_eq_erase] using hle⟩
    · have hempty : A j = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAj
      rw [hempty]
      exact Or.inl (by simpa using value_nonneg hnn i (A i))

/-- The canonical disjoint allocation produced by complete choice
round-robin.  The function-valued recursion remains private. -/
noncomputable def roundRobinAllocation [Fintype G] [DecidableEq G]
    (v : AdditiveValuation (Fin n) G) : Allocation (Fin n) G where
  bundle := rawRoundRobinAlloc v Finset.univ
  pairwise_disjoint :=
    (rawRoundRobinAlloc_isAllocation v (Finset.univ : Finset G)).1

/-- `roundRobinAllocation` assigns every good exactly once: disjointness is in
the canonical carrier and this theorem supplies completeness. -/
theorem roundRobinAllocation_isComplete [Fintype G] [DecidableEq G]
    (v : AdditiveValuation (Fin n) G) :
    IsComplete (roundRobinAllocation v) := by
  exact isComplete_of_isAllocationOn_univ
    (rawRoundRobinAlloc_isAllocation v (Finset.univ : Finset G))

/-- Round-robin gives EF1 for additive instances with nonnegative item values. -/
theorem roundRobinAllocation_isEF1 [Fintype G] [DecidableEq G]
    (v : AdditiveValuation (Fin n) G) (hnn : Nonnegative v) :
    IsEF1 v (roundRobinAllocation v) := by
  exact raw_isEF1_of_isEF1OnNonempty hnn
    (rawRoundRobinAlloc_isEF1 v (Finset.univ : Finset G) hnn)

/-- Round-robin bundled with its completeness certificate. -/
noncomputable def roundRobinRule [Fintype G] [DecidableEq G]
    (v : AdditiveValuation (Fin n) G) :
    {A : Allocation (Fin n) G // IsComplete A} :=
  ⟨roundRobinAllocation v, roundRobinAllocation_isComplete v⟩

/-- The bundled round-robin rule is EF1 under nonnegative item values. -/
theorem roundRobinRule_isEF1 [Fintype G] [DecidableEq G]
    (v : AdditiveValuation (Fin n) G) (hnn : Nonnegative v) :
    IsEF1 v (roundRobinRule v).1 :=
  roundRobinAllocation_isEF1 v hnn

end GameTheory.Mechanism.FairDivision
