import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-! Ranks in canonically sorted finite sets. Counting elements strictly below a
member recovers its ordinal, independently of the finite set's representation. -/
namespace GameTheory.Math.FiniteSetRank

/-- The canonical index of a member equals the number of smaller members. -/
theorem rank_eq_index {α : Type*} [LinearOrder α] (s : Finset α)
    {k : ℕ} (hs : s.card = k) (a : α) (ha : a ∈ s) :
    (s.filter (fun v => v < a)).card = ((s.orderIsoOfFin hs).symm ⟨a, ha⟩).val := by
  let e := s.orderIsoOfFin hs
  have hset : s.filter (fun v => v < a) =
      (Finset.Iio (e.symm ⟨a, ha⟩)).image (s.orderEmbOfFin hs) := by
    ext v
    constructor
    · intro hv
      obtain ⟨hv, hlt⟩ := Finset.mem_filter.mp hv
      apply Finset.mem_image.mpr
      refine ⟨e.symm ⟨v, hv⟩, ?_, ?_⟩
      · apply Finset.mem_Iio.mpr
        exact e.symm.strictMono hlt
      · exact congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      apply Finset.mem_filter.mpr
      refine ⟨Finset.orderEmbOfFin_mem s hs i, ?_⟩
      have hlt := e.strictMono (Finset.mem_Iio.mp hi)
      exact (show (e i).val < (e (e.symm ⟨a, ha⟩)).val from hlt).trans_eq
        (congrArg Subtype.val (e.apply_symm_apply ⟨a, ha⟩))
  rw [hset, Finset.card_image_of_injective _ (s.orderEmbOfFin hs).injective, Fin.card_Iio]


/-- Membership and rank uniquely characterize a canonically selected member. -/
theorem eq_orderEmbOfFin_iff {α : Type*} [LinearOrder α] (s : Finset α)
    {k : ℕ} (hs : s.card = k) (j : Fin k) (a : α) :
    a = s.orderEmbOfFin hs j ↔ a ∈ s ∧ (s.filter (fun v => v < a)).card = j.val := by
  constructor
  · intro he
    subst a
    refine ⟨Finset.orderEmbOfFin_mem s hs j, ?_⟩
    rw [rank_eq_index s hs _ (Finset.orderEmbOfFin_mem s hs j)]
    exact congrArg Fin.val ((s.orderIsoOfFin hs).symm_apply_apply j)
  · rintro ⟨ha, hr⟩
    rw [rank_eq_index s hs a ha] at hr
    have he : (s.orderIsoOfFin hs).symm ⟨a, ha⟩ = j := Fin.ext hr
    have hx := congrArg Subtype.val ((s.orderIsoOfFin hs).apply_symm_apply ⟨a, ha⟩)
    rw [he] at hx
    exact hx.symm

end GameTheory.Math.FiniteSetRank
