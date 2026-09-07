/-
# Finite-law probability identities

The fixtures deliberately use `Nat` carriers: finite support does not require
the carrier itself to be finite.
-/

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Tests.FinDistProbabilityLemmas

open GameTheory.Math.Probability

def twoPointNat : FinDist Nat :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure 1) (FinDist.pure 2)

def mergeAtZero (n : Nat) : Nat := if n = 1 ∨ n = 2 then 0 else n

def twoPointBool : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num) (FinDist.pure true) (FinDist.pure false)

def jointObservable : Nat × Bool → ℝ := fun p =>
  if p.1 = 1 ∧ p.2 then 3 else if p.1 = 2 ∧ ¬p.2 then 5 else 0

theorem map_probability_merges_at_zero :
    (twoPointNat.map mergeAtZero).prob 0 =
      twoPointNat.probOf (mergeAtZero ⁻¹' ({0} : Set Nat)) := by
  exact FinDist.prob_map_eq_probOf_preimage_singleton mergeAtZero twoPointNat 0

theorem map_probability_merges_at_zero_is_one :
    (twoPointNat.map mergeAtZero).prob 0 = 1 := by
  rw [FinDist.prob_map]
  norm_num [twoPointNat, mergeAtZero, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.prob_pure_eq_ite]

theorem map_probability_outside_support_is_zero :
    (twoPointNat.map mergeAtZero).prob 99 = 0 := by
  rw [FinDist.prob_map]
  norm_num [twoPointNat, mergeAtZero, FinDist.expect_mix, FinDist.expect_pure,
    FinDist.prob_pure_eq_ite]

theorem expect_product_nonseparable :
    (FinDist.product twoPointNat twoPointBool).expect jointObservable =
      twoPointNat.expect (fun a => twoPointBool.expect (fun b => jointObservable (a, b))) := by
  exact FinDist.expect_product twoPointNat twoPointBool jointObservable

theorem expect_product_nonseparable_value :
    (FinDist.product twoPointNat twoPointBool).expect jointObservable = 2 := by
  rw [FinDist.expect_product]
  norm_num [twoPointNat, twoPointBool, jointObservable, FinDist.expect_mix,
    FinDist.expect_pure]

theorem expect_product_pure_right (a : Nat) (b : Bool) (u : Nat × Bool → ℝ) :
    (FinDist.product (FinDist.pure a) (FinDist.pure b)).expect u =
      (FinDist.pure a).expect (fun x => (FinDist.pure b).expect (fun y => u (x, y))) := by
  exact FinDist.expect_product (FinDist.pure a) (FinDist.pure b) u

theorem expect_product_on_infinite_carriers (μ ν : FinDist Nat) (u : Nat × Nat → ℝ) :
    (FinDist.product μ ν).expect u = μ.expect (fun a => ν.expect (fun b => u (a, b))) := by
  exact FinDist.expect_product μ ν u

/-- Both inputs collapse to one summary. Their carriers differ, and the Nat
continuation deliberately disagrees with the Bool continuation off support. -/
theorem bind_matching_summaries_ignores_unreachable_branches :
    (twoPointNat.bind fun n =>
      if n = 1 ∨ n = 2 then FinDist.pure 7 else FinDist.pure 99) =
      twoPointBool.bind (fun _ => FinDist.pure 7) := by
  apply FinDist.bind_eq_of_map_eq twoPointNat twoPointBool
    (fun _ => ()) (fun _ => ()) (by simp)
  intro n hn _ _ _
  have hreachable : n = 1 ∨ n = 2 := by
    simpa [twoPointNat] using
      (FinDist.mem_support_mix_pure_iff (1 / 2) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) 1 2 n).mp hn
  rw [if_pos hreachable]

theorem projection_identity {ι : Type*} [Fintype ι] {A : ι → Type*}
    (laws : ∀ i, FinDist (A i)) :
    (FinDist.pi laws).map (fun values i => values i) = FinDist.pi laws :=
  FinDist.pi_map_embedding (Function.Embedding.refl ι) laws

theorem projection_proper_subset (laws : Fin 3 → FinDist Nat) :
    (FinDist.pi laws).map (fun values (i : Fin 2) => values (i.castLE (by decide))) =
      FinDist.pi (fun i : Fin 2 => laws (i.castLE (by decide))) :=
  FinDist.pi_map_embedding
    ⟨fun i : Fin 2 => i.castLE (show 2 ≤ 3 by decide),
      Fin.castLE_injective (show 2 ≤ 3 by decide)⟩ laws

theorem projection_empty {ι : Type*} [Fintype ι] {A : ι → Type*}
    (laws : ∀ i, FinDist (A i)) (e : Fin 0 ↪ ι) :
    (FinDist.pi laws).map (fun values i => values (e i)) =
      FinDist.pure (fun i => Fin.elim0 i) := by
  rw [FinDist.pi_map_embedding]
  have hlaws : (fun i : Fin 0 => laws (e i)) =
      (fun i : Fin 0 => FinDist.pure (Fin.elim0 i)) := by
    funext i
    exact Fin.elim0 i
  rw [hlaws, FinDist.pi_pure]

end GameTheory.Tests.FinDistProbabilityLemmas
