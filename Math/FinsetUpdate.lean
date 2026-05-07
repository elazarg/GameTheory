import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic

set_option autoImplicit false

/-!
# Finset Sum/Sup Stability Under Function.update

Lemmas for `Finset.sum` and `Finset.sup'` stability under `Function.update`.
-/

namespace Math
namespace Finset
namespace Update

variable {ι α : Type*}

theorem sum_update_eq_sum_of_not_mem
    [DecidableEq ι] [AddCommMonoid α]
    (S : _root_.Finset ι) (j : ι) (hj : j ∉ S) (x : ι → α) (a : α) :
    S.sum (fun i => (Function.update x j a) i) = S.sum (fun i => x i) := by
  exact _root_.Finset.sum_update_of_notMem hj x a

theorem sum_update_eq_sum_erase_add
    [DecidableEq ι] [AddCommMonoid α]
    (S : _root_.Finset ι) (j : ι) (hj : j ∈ S) (x : ι → α) (a : α) :
    S.sum (fun i => (Function.update x j a) i) = (S.erase j).sum (fun i => x i) + a := by
  simpa [_root_.Finset.sdiff_singleton_eq_erase, add_comm] using
    (_root_.Finset.sum_update_of_mem hj x a)

theorem sum_update_eq_sum_insert_sub
    [DecidableEq ι] [AddCommGroup α]
    (S : _root_.Finset ι) (j : ι) (hj : j ∈ S) (x : ι → α) (a : α) :
    S.sum (fun i => (Function.update x j a) i) =
      S.sum (fun i => x i) - x j + a := by
  rw [sum_update_eq_sum_erase_add S j hj x a]
  have hs : S.sum (fun i => x i) = (S.erase j).sum (fun i => x i) + x j := by
    simpa [_root_.Finset.sdiff_singleton_eq_erase] using
      (_root_.Finset.sum_eq_sum_diff_singleton_add hj x)
  rw [hs]
  simp [sub_eq_add_neg, add_assoc, add_comm]

theorem sup'_congr_eqOn
    [SemilatticeSup α]
    (S : _root_.Finset ι) (hS : S.Nonempty)
    (f g : ι → α)
    (hfg : ∀ i, i ∈ S → f i = g i) :
    S.sup' hS f = S.sup' hS g := by
  refine _root_.Finset.sup'_congr hS rfl ?_
  intro i hi
  exact hfg i hi

theorem sup'_update_eq_of_not_mem
    [DecidableEq ι] [SemilatticeSup α]
    (S : _root_.Finset ι) (hS : S.Nonempty)
    (j : ι) (hj : j ∉ S)
    (x : ι → α) (a : α) :
    S.sup' hS (Function.update x j a) = S.sup' hS x := by
  refine sup'_congr_eqOn S hS (Function.update x j a) x ?_
  intro i hi
  have hij : i ≠ j := by
    intro h
    exact hj (h ▸ hi)
  simp [Function.update, hij]

theorem sup'_update_eq_of_forall_ne
    [DecidableEq ι] [SemilatticeSup α]
    (S : _root_.Finset ι) (hS : S.Nonempty)
    (j : ι)
    (hneq : ∀ i, i ∈ S → i ≠ j)
    (x : ι → α) (a : α) :
    S.sup' hS (Function.update x j a) = S.sup' hS x := by
  refine sup'_congr_eqOn S hS (Function.update x j a) x ?_
  intro i hi
  simp [Function.update, hneq i hi]

theorem sup'_update_eq_of_mem
    [DecidableEq ι] [SemilatticeSup α]
    (S : _root_.Finset ι) (hS : S.Nonempty)
    (j : ι) (hj : j ∈ S)
    (hE : (S.erase j).Nonempty)
    (x : ι → α) (a : α) :
    S.sup' hS (Function.update x j a) = a ⊔ (S.erase j).sup' hE x := by
  have hS' : (insert j (S.erase j)).Nonempty := by
    exact _root_.Finset.insert_nonempty _ _
  calc
    S.sup' hS (Function.update x j a)
        = (insert j (S.erase j)).sup' hS' (Function.update x j a) := by
            simp [_root_.Finset.insert_erase hj]
    _ = (Function.update x j a) j ⊔ (S.erase j).sup' hE (Function.update x j a) := by
          simpa using
            (_root_.Finset.sup'_insert (s := S.erase j) (H := hE)
              (f := Function.update x j a) (b := j))
    _ = a ⊔ (S.erase j).sup' hE x := by
          have hcongr :
              (S.erase j).sup' hE (Function.update x j a) = (S.erase j).sup' hE x := by
            refine sup'_congr_eqOn (S.erase j) hE (Function.update x j a) x ?_
            intro i hi
            simp [Function.update, _root_.Finset.ne_of_mem_erase hi]
          simp [hcongr]

end Update
end Finset
end Math
