import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic

set_option autoImplicit false

namespace Math
namespace Finset
namespace Update

variable {ι α : Type*}

theorem sum_update_eq_sum_of_not_mem
    [DecidableEq ι] [AddCommMonoid α]
    (S : _root_.Finset ι) (j : ι) (hj : j ∉ S) (x : ι → α) (a : α) :
    S.sum (fun i => (Function.update x j a) i) = S.sum (fun i => x i) := by
  refine _root_.Finset.sum_congr rfl ?_
  intro i hi
  have hij : i ≠ j := by
    intro hijEq
    apply hj
    simpa [hijEq] using hi
  simp [Function.update, hij]

theorem sum_update_eq_sum_erase_add
    [DecidableEq ι] [AddCommMonoid α]
    (S : _root_.Finset ι) (j : ι) (hj : j ∈ S) (x : ι → α) (a : α) :
    S.sum (fun i => (Function.update x j a) i) = (S.erase j).sum (fun i => x i) + a := by
  calc
    S.sum (fun i => (Function.update x j a) i)
        = (S.erase j).sum (fun i => (Function.update x j a) i) + (Function.update x j a) j := by
            rw [← _root_.Finset.sum_erase_add
              (s := S) (a := j) (f := fun i => (Function.update x j a) i) hj]
    _ = (S.erase j).sum (fun i => x i) + a := by
          simp [sum_update_eq_sum_of_not_mem, hj]

theorem sum_update_eq_sum_insert_sub
    [DecidableEq ι] [AddCommGroup α]
    (S : _root_.Finset ι) (j : ι) (hj : j ∈ S) (x : ι → α) (a : α) :
    S.sum (fun i => (Function.update x j a) i) =
      S.sum (fun i => x i) - x j + a := by
  calc
    S.sum (fun i => (Function.update x j a) i)
        = (S.erase j).sum (fun i => x i) + a := sum_update_eq_sum_erase_add S j hj x a
    _ = (((S.erase j).sum (fun i => x i) + x j) - x j) + a := by
          have hx :
              (((S.erase j).sum (fun i => x i) + x j) - x j)
                = (S.erase j).sum (fun i => x i) := by
            simp [sub_eq_add_neg, add_assoc, add_comm]
          rw [hx]
    _ = S.sum (fun i => x i) - x j + a := by
          have hs :
              (S.erase j).sum (fun i => x i) + x j = S.sum (fun i => x i) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              (_root_.Finset.sum_erase_add (s := S) (a := j) (f := fun i => x i) hj)
          simp [hs, sub_eq_add_neg, add_comm]

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
