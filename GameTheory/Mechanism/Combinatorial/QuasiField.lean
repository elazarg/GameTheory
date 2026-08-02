/-
# Quasi-fields of bundles

Closure lemmas for the finite bundle families used by coordinated
combinatorial mechanisms. Ported mathematically from
`reference/GameTheory-v1/GameTheory/Auctions/Combinatorial.lean` at pinned
commit `a3d8c67ed91d58e197b8c978ddcc00ba96f87c29`.
-/

import GameTheory.Mechanism.Combinatorial.Basic

namespace GameTheory.Mechanism.Combinatorial

variable {A : Type} [Fintype A] [DecidableEq A]

/-- A finite bundle family closed under complements and disjoint unions. -/
def IsQuasiField (Q : Finset (Finset A)) : Prop :=
  (∅ : Finset A) ∈ Q ∧
    (∀ B ∈ Q, (Finset.univ \ B : Finset A) ∈ Q) ∧
      ∀ B ∈ Q, ∀ C ∈ Q, Disjoint B C → B ∪ C ∈ Q

theorem IsQuasiField.empty_mem {Q : Finset (Finset A)} (hQ : IsQuasiField (A := A) Q) :
    (∅ : Finset A) ∈ Q :=
  hQ.1

theorem IsQuasiField.compl_mem {Q : Finset (Finset A)} (hQ : IsQuasiField (A := A) Q)
    {B : Finset A} (hB : B ∈ Q) : (Finset.univ \ B : Finset A) ∈ Q :=
  hQ.2.1 B hB

theorem IsQuasiField.disjoint_union_mem {Q : Finset (Finset A)}
    (hQ : IsQuasiField (A := A) Q) {B C : Finset A} (hB : B ∈ Q) (hC : C ∈ Q)
    (hdisj : Disjoint B C) : B ∪ C ∈ Q :=
  hQ.2.2 B hB C hC hdisj

/-- A quasi-field contains finite unions of pairwise-disjoint member bundles. -/
theorem IsQuasiField.biUnion_mem_of_pairwise_disjoint {Q : Finset (Finset A)}
    (hQ : IsQuasiField (A := A) Q) {ι : Type} (s : Finset ι) (B : ι → Finset A)
    (hmem : ∀ i, i ∈ s → B i ∈ Q)
    (hdisj : ∀ i, i ∈ s → ∀ j, j ∈ s → i ≠ j → Disjoint (B i) (B j)) :
    s.biUnion B ∈ Q := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hQ.empty_mem
  | insert a s has ih =>
      rw [Finset.biUnion_insert]
      apply hQ.disjoint_union_mem
      · exact hmem a (by simp)
      · apply ih
        · intro i hi
          exact hmem i (by simp [hi])
        · intro i hi j hj hij
          exact hdisj i (by simp [hi]) j (by simp [hj]) hij
      · rw [Finset.disjoint_biUnion_right]
        intro j hj
        have haj : a ≠ j := by
          intro h
          subst h
          exact has hj
        exact hdisj a (by simp) j (by simp [hj]) haj

/-- The residual after all other buyers keep their quasi-field bundles is in the quasi-field. -/
theorem IsQuasiField.residualAfterOpponents_mem {Q : Finset (Finset A)}
    (hQ : IsQuasiField (A := A) Q) {ι : Type} [Fintype ι] [DecidableEq ι]
    (γ : Allocation ι A) (i : ι) (hmem : ∀ j, j ≠ i → γ.bundle j ∈ Q) :
    γ.residualAfterOpponents i ∈ Q := by
  classical
  unfold Allocation.residualAfterOpponents
  apply hQ.compl_mem
  apply hQ.biUnion_mem_of_pairwise_disjoint
  · intro j hj
    exact hmem j (by simpa using hj)
  · intro j hj k hk hjk
    exact γ.pairwise_disjoint hjk

end GameTheory.Mechanism.Combinatorial
