import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! Approximate mutual support comparisons force positive masses close to uniform.
The estimates depend only on normalized finite sums, not an equilibrium definition. -/

namespace GameTheory.Math
open scoped BigOperators
variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]

private theorem exists_mass_ge_average {k : ℕ} (hk : 0 < k)
    (z : Fin k → F) (hz : ∑ i, z i = 1) : ∃ i, 1 / (k : F) ≤ z i := by
  have havg : ∑ _i : Fin k, (1 / (k : F)) = 1 := by
    simp [hk.ne']
  obtain ⟨i, _, hi⟩ := Finset.exists_le_of_sum_le
    (show (Finset.univ : Finset (Fin k)).Nonempty from ⟨⟨0, hk⟩, Finset.mem_univ _⟩)
    (show (∑ _i : Fin k, (1 / (k : F))) ≤ ∑ i, z i by rw [havg, hz])
  exact ⟨i, hi⟩

private theorem mass_uniform_of_pairwise {k : ℕ} (hk : 0 < k)
    (z : Fin k → F) (hz : ∑ i, z i = 1) (δ : F)
    (hpair : ∀ i j, z i ≤ z j + δ) (i : Fin k) : |z i - 1 / (k : F)| ≤ δ := by
  have hkQ : (0 : F) < k := by exact_mod_cast hk
  have hprod : (k : F) * (1 / (k : F)) = 1 := by field_simp
  have hlo : (k : F) * (z i - δ) ≤ 1 := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (f := fun _ : Fin k => z i - δ) (g := z) (fun j _ => by linarith [hpair i j])
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hz] using hh
  have hhi : 1 ≤ (k : F) * (z i + δ) := by
    have hh := Finset.sum_le_sum (s := Finset.univ)
      (f := z) (g := fun _ : Fin k => z i + δ) (fun j _ => hpair j i)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hz] using hh
  rw [abs_le]
  constructor <;> nlinarith

/-- Mutual approximate best-response mass comparisons force full support and
coordinatewise proximity to the uniform distribution. -/
theorem matchingMass_uniform {k : ℕ} (hk : 0 < k) (x y : Fin k → F)
    (hsx : ∑ i, x i = 1) (hsy : ∑ i, y i = 1) (δ : F)
    (hsmall : δ < 1 / (k : F))
    (hr : ∀ i, 0 < x i → ∀ j, y j ≤ y i + δ)
    (hc : ∀ i, 0 < y i → ∀ j, x i ≤ x j + δ) :
    (∀ i, 0 < x i ∧ 0 < y i) ∧
      ∀ i, |x i - 1 / (k : F)| ≤ δ ∧ |y i - 1 / (k : F)| ≤ δ := by
  obtain ⟨a, ha⟩ := exists_mass_ge_average hk x hsx
  obtain ⟨b, hb⟩ := exists_mass_ge_average hk y hsy
  have hkF : (0 : F) < k := by exact_mod_cast hk
  have hxa : 0 < x a := lt_of_lt_of_le (one_div_pos.mpr hkF) ha
  have hya : 0 < y a := by linarith [hr a hxa b]
  have hxpos : ∀ i, 0 < x i := fun i => by linarith [hc a hya i]
  have hypos : ∀ i, 0 < y i := fun i => by linarith [hr i (hxpos i) b]
  refine ⟨fun i => ⟨hxpos i, hypos i⟩, fun i => ⟨?_, ?_⟩⟩
  · exact mass_uniform_of_pairwise hk x hsx δ (fun i j => hc i (hypos i) j) i
  · exact mass_uniform_of_pairwise hk y hsy δ (fun i j => hr j (hxpos j) i) i
end GameTheory.Math
