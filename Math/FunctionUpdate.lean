import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Finite.Basic

set_option autoImplicit false

namespace Math
namespace Function
namespace Update

variable {ι : Type*}
variable {A : ι → Type*}
variable {β : Type*}

def replaceOn (K : Set ι) [DecidablePred (fun i => i ∈ K)]
    (x y : ∀ i, A i) : (∀ i, A i) :=
  fun i => if i ∈ K then y i else x i

def Ignores [DecidableEq ι] (j : ι) (F : (∀ i, A i) → β) : Prop :=
  ∀ s a, F (Function.update s j a) = F s

theorem foldl_update_invariant
    [DecidableEq ι]
    (F : (∀ i, A i) → β)
    (l : List ι)
    (hF : ∀ j, j ∈ l → ∀ s a, F (Function.update s j a) = F s)
    (base : ∀ i, A i)
    (vals : ∀ i, A i) :
    F (l.foldl (fun s j => Function.update s j (vals j)) base) = F base := by
  induction l generalizing base with
  | nil =>
      simp
  | cons j rest ih =>
      have hHead : ∀ s a, F (Function.update s j a) = F s := hF j (by simp)
      have hTail : ∀ k, k ∈ rest → ∀ s a, F (Function.update s k a) = F s := by
        intro k hk
        exact hF k (by simp [hk])
      simp only [List.foldl]
      calc
        F (rest.foldl (fun s j => Function.update s j (vals j))
            (Function.update base j (vals j)))
            =
          F (Function.update base j (vals j)) := ih hTail _
        _ = F base := hHead _ _

theorem replaceOn_eq_self_of_not_mem
    (K : Set ι) [DecidablePred (fun i => i ∈ K)]
    (x y : ∀ i, A i) (i : ι) (hi : i ∉ K) :
    replaceOn K x y i = x i := by
  simp [replaceOn, hi]

theorem replaceOn_eq_right_of_mem
    (K : Set ι) [DecidablePred (fun i => i ∈ K)]
    (x y : ∀ i, A i) (i : ι) (hi : i ∈ K) :
    replaceOn K x y i = y i := by
  simp [replaceOn, hi]

theorem replaceOn_insert
    [DecidableEq ι]
    (K : Set ι) [DecidablePred (fun i => i ∈ K)]
    (j : ι) [DecidablePred (fun i => i ∈ Set.insert j K)] (x y : ∀ i, A i) :
    replaceOn (Set.insert j K) x y =
      Function.update (replaceOn K x y) j (y j) := by
  funext i
  by_cases hi : i = j
  · subst hi
    have hins : i ∈ Set.insert i K := Set.mem_insert i K
    simp [replaceOn, hins]
  · by_cases hik : i ∈ K
    · have hins : i ∈ Set.insert j K := Set.mem_insert_of_mem j hik
      simp [replaceOn, hi, hik, hins]
    · have hins : i ∉ Set.insert j K := by
        intro h
        rcases Set.mem_insert_iff.mp h with hEq | hk
        · exact hi hEq
        · exact hik hk
      simp [replaceOn, hi, hik, hins]

theorem replaceOn_insert_finset
    [DecidableEq ι]
    (S : Finset ι)
    (a : ι) (x y : ∀ i, A i) :
    replaceOn (K := ((insert a S : Finset ι) : Set ι)) x y =
      Function.update (replaceOn (K := (S : Set ι)) x y) a (y a) := by
  funext i
  by_cases hi : i = a
  · subst hi
    simp [replaceOn]
  · by_cases his : i ∈ S
    · simp [replaceOn, hi, his]
    · simp [replaceOn, hi, his]

theorem replaceOn_involutive_partition
    (K : Set ι) [DecidablePred (fun i => i ∈ K)] [DecidablePred (fun i => i ∈ Kᶜ)] :
    Function.Involutive (fun p : (∀ i, A i) × (∀ i, A i) =>
      (replaceOn Kᶜ p.1 p.2, replaceOn K p.1 p.2)) := by
  intro p
  rcases p with ⟨x, y⟩
  apply Prod.ext
  · funext i
    by_cases hi : i ∈ K
    · simp [replaceOn, hi]
    · simp [replaceOn, hi]
  · funext i
    by_cases hi : i ∈ K
    · simp [replaceOn, hi]
    · simp [replaceOn, hi]

theorem ignores_replaceOn_finset_eq
    [DecidableEq ι]
    (F : (∀ i, A i) → β)
    (S : Finset ι)
    (hign : ∀ j, j ∈ S → Ignores j F)
    (x y : ∀ i, A i) :
    F (replaceOn (K := (S : Set ι)) x y) = F x := by
  classical
  induction S using Finset.induction with
  | empty =>
      have h0 : replaceOn (K := ((∅ : Finset ι) : Set ι)) x y = x := by
        funext i
        simp [replaceOn]
      simp [h0]
  | @insert a S ha ih =>
      have higna : Ignores a F := hign a (by simp)
      have hignS : ∀ j, j ∈ S → Ignores j F := by
        intro j hj
        exact hign j (by simp [hj])
      calc
        F (replaceOn (K := ((insert a S : Finset ι) : Set ι)) x y)
            = F (Function.update (replaceOn (K := (S : Set ι)) x y) a (y a)) := by
                simpa using congrArg F (replaceOn_insert_finset (S := S) a x y)
        _ = F (replaceOn (K := (S : Set ι)) x y) := higna _ _
        _ = F x := ih hignS

theorem ignores_replaceOn_eq
    [DecidableEq ι]
    (F : (∀ i, A i) → β)
    (K : Set ι) [DecidablePred (fun i => i ∈ K)]
    (hK : K.Finite)
    (hign : ∀ j, j ∈ K → Ignores j F)
    (x y : ∀ i, A i) :
    F (replaceOn K x y) = F x := by
  classical
  have hreplace :
      replaceOn K x y = replaceOn (K := ((hK.toFinset : Finset ι) : Set ι)) x y := by
    funext i
    by_cases hi : i ∈ K
    · have hi' : i ∈ hK.toFinset := (hK.mem_toFinset).2 hi
      simp [replaceOn, hi]
    · have hi' : i ∉ hK.toFinset := by
        intro hs
        exact hi ((hK.mem_toFinset).1 hs)
      simp [replaceOn, hi]
  have hignS : ∀ j, j ∈ hK.toFinset → Ignores j F := by
    intro j hj
    exact hign j ((hK.mem_toFinset).1 hj)
  rw [hreplace]
  exact ignores_replaceOn_finset_eq F hK.toFinset hignS x y

theorem aggregate_excluding_index_update_invariant
    [DecidableEq ι]
    (j : ι) (F : (∀ i, A i) → β)
    (hF : ∀ s t, (∀ i, i ≠ j → s i = t i) → F s = F t)
    (x : ∀ i, A i) (a : A j) :
    F (Function.update x j a) = F x := by
  apply hF
  intro i hi
  simp [Function.update, hi]

-- Existing in core: `Function.update_idem`, `Function.update_comm`,
-- `Function.update_eq_self`, `Function.update_of_ne`.

end Update
end Function
end Math
