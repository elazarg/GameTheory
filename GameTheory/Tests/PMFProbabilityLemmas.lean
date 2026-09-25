/-
# Ordinary PMF probability identities

The fixtures deliberately use Nat carriers: PMFs remain meaningful when the
carrier is infinite, and the independent product controls use arbitrary laws.
-/

import GameTheory.Math.Probability.Mixture
import GameTheory.Math.Probability.Product
import GameTheory.Math.Probability.ExpectationComposition
import GameTheory.Math.Probability.ExpectationMixture

noncomputable section

open GameTheory.Math.Probability

namespace GameTheory.Tests.PMFProbabilityLemmas

def twoPointNat : PMF Nat :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure 1) (PMF.pure 2)

def mergeAtZero (n : Nat) : Nat := if n = 1 ∨ n = 2 then 0 else n

def twoPointBool : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure true) (PMF.pure false)

def jointObservable : Nat × Bool → ℝ := fun p =>
  if p.1 = 1 ∧ p.2 then 3 else if p.1 = 2 ∧ ¬p.2 then 5 else 0

def pairLaw (μ : PMF Nat) (ν : PMF Bool) : PMF (Nat × Bool) :=
  bindPairLaw μ (fun _ => ν)

theorem map_probability_merges_at_zero :
    (twoPointNat.map mergeAtZero).toOuterMeasure {0} =
      twoPointNat.toOuterMeasure (mergeAtZero ⁻¹' ({0} : Set Nat)) := by
  exact PMF.toOuterMeasure_map_apply _ _ _

private theorem mergeLaw : twoPointNat.map mergeAtZero = PMF.pure 0 := by
  unfold twoPointNat
  rw [mix_map, PMF.pure_map, PMF.pure_map]
  have hleft : mergeAtZero 1 = 0 := by norm_num [mergeAtZero]
  have hright : mergeAtZero 2 = 0 := by norm_num [mergeAtZero]
  rw [hleft, hright]
  exact mix_self _ (by norm_num) (by norm_num) (PMF.pure 0)

theorem map_probability_merges_at_zero_is_one :
    ((twoPointNat.map mergeAtZero) 0).toReal = 1 := by
  rw [mergeLaw]
  simp

theorem map_probability_outside_support_is_zero :
    (twoPointNat.map mergeAtZero) 99 = 0 := by
  rw [mergeLaw]
  simp

theorem jointObservableIntegrable :
    PayoffIntegrable (pairLaw twoPointNat twoPointBool) jointObservable :=
  payoffIntegrable_of_bounded _ _ (C := 5) (by
    intro p
    unfold jointObservable
    split_ifs <;> norm_num)

theorem jointObservableRowIntegrable (a : Nat) :
    PayoffIntegrable twoPointBool (fun b => jointObservable (a, b)) :=
  payoffIntegrable_of_bounded _ _ (C := 5) (by
    intro b
    unfold jointObservable
    split_ifs <;> norm_num)

theorem jointObservableIteratedIntegrable :
    PayoffIntegrable twoPointNat (fun a =>
      expect twoPointBool (fun b => jointObservable (a, b))
        (jointObservableRowIntegrable a)) :=
  payoffIntegrable_of_bounded _ _ (C := 5) (by
    intro a
    have h := expect_abs_le_of_bounded (by norm_num : (0 : ℝ) ≤ 5)
      (by intro b; unfold jointObservable; split_ifs <;> norm_num)
      (jointObservableRowIntegrable a)
    simpa using h)

theorem expect_product_nonseparable :
    expect (pairLaw twoPointNat twoPointBool) jointObservable
      jointObservableIntegrable =
    expect twoPointNat (fun a =>
      expect twoPointBool (fun b => jointObservable (a, b))
        (jointObservableRowIntegrable a)) jointObservableIteratedIntegrable := by
  exact expect_bindPairLaw_tower twoPointNat twoPointBool jointObservable
    jointObservableIntegrable jointObservableRowIntegrable
    jointObservableIteratedIntegrable

theorem expect_product_nonseparable_value :
    expect (pairLaw twoPointNat twoPointBool) jointObservable
      jointObservableIntegrable = 2 := by
  rw [expect_product_nonseparable]
  have hrowValue (a : Nat) :
      expect twoPointBool (fun b => jointObservable (a, b))
          (jointObservableRowIntegrable a) =
        if a = 1 then 3 / 2 else if a = 2 then 5 / 2 else 0 := by
    have hrowMix : PayoffIntegrable
        (mix (1 / 2) (by norm_num) (by norm_num)
          (PMF.pure true) (PMF.pure false))
        (fun b => jointObservable (a, b)) := by
      simpa [twoPointBool] using jointObservableRowIntegrable a
    unfold twoPointBool
    rw [expect_proof_irrel _ _ hrowMix
      (payoffIntegrable_mix (1 / 2) (by norm_num) (by norm_num)
        (PMF.pure true) (PMF.pure false) (fun b => jointObservable (a, b))
        (payoffIntegrable_pure true _) (payoffIntegrable_pure false _))]
    rw [expect_mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure true) (PMF.pure false) (fun b => jointObservable (a, b))
      (payoffIntegrable_pure true _) (payoffIntegrable_pure false _)]
    split_ifs <;> simp_all [jointObservable, expect_pure] <;> norm_num
  have houterIntegrable :
      PayoffIntegrable twoPointNat
        (fun a => if a = 1 then 3 / 2 else if a = 2 then 5 / 2 else 0) :=
    payoffIntegrable_of_bounded _ _ (C := 3) (by
      intro a
      split_ifs <;> norm_num)
  have hvalue := expect_congr_on_support
    (fun a _ => hrowValue a) jointObservableIteratedIntegrable houterIntegrable
  rw [hvalue]
  have houterMix : PayoffIntegrable
      (mix (1 / 2) (by norm_num) (by norm_num) (PMF.pure 1) (PMF.pure 2))
      (fun a => if a = 1 then 3 / 2 else if a = 2 then 5 / 2 else 0) := by
    simpa [twoPointNat] using houterIntegrable
  unfold twoPointNat
  rw [expect_proof_irrel _ _ houterMix
    (payoffIntegrable_mix (1 / 2) (by norm_num) (by norm_num)
      (PMF.pure 1) (PMF.pure 2)
      (fun a => if a = 1 then 3 / 2 else if a = 2 then 5 / 2 else 0)
      (payoffIntegrable_pure 1 _) (payoffIntegrable_pure 2 _))]
  rw [expect_mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure 1) (PMF.pure 2)
    (fun a => if a = 1 then 3 / 2 else if a = 2 then 5 / 2 else 0)
    (payoffIntegrable_pure 1 _) (payoffIntegrable_pure 2 _)]
  norm_num [expect_pure]

theorem pairLaw_pure_right (a : Nat) (b : Bool) :
    pairLaw (PMF.pure a) (PMF.pure b) = PMF.pure (a, b) := by
  rw [pairLaw, bindPairLaw, PMF.pure_bind, PMF.pure_map]

theorem expect_product_pure_right (a : Nat) (b : Bool) (u : Nat × Bool → ℝ) :
    expect (pairLaw (PMF.pure a) (PMF.pure b)) u
        (payoffIntegrable_congr_law (pairLaw_pure_right a b).symm
          (payoffIntegrable_pure (a, b) u)) =
      expect (PMF.pure a) (fun x =>
        expect (PMF.pure b) (fun y => u (x, y)) (payoffIntegrable_pure b _))
        (payoffIntegrable_pure a _) := by
  have hlaw := pairLaw_pure_right a b
  let hpair := payoffIntegrable_congr_law hlaw.symm (payoffIntegrable_pure (a, b) u)
  calc
    expect (pairLaw (PMF.pure a) (PMF.pure b)) u
        (payoffIntegrable_congr_law hlaw.symm (payoffIntegrable_pure (a, b) u)) =
        expect (PMF.pure (a, b)) u (payoffIntegrable_pure (a, b) u) :=
      expect_congr_law hlaw u hpair (payoffIntegrable_pure (a, b) u)
    _ = expect (PMF.pure a) (fun x =>
        expect (PMF.pure b) (fun y => u (x, y)) (payoffIntegrable_pure b _))
        (payoffIntegrable_pure a _) := by
      simp [expect_pure]

theorem expect_product_on_infinite_carriers (μ ν : PMF Nat)
    (u : Nat × Nat → ℝ)
    (hjoint : PayoffIntegrable (bindPairLaw μ (fun _ => ν)) u)
    (hrow : ∀ a, PayoffIntegrable ν (fun b => u (a, b)))
    (houter : PayoffIntegrable μ (fun a =>
      expect ν (fun b => u (a, b)) (hrow a))) :
    expect (bindPairLaw μ (fun _ => ν)) u hjoint =
      expect μ (fun a => expect ν (fun b => u (a, b)) (hrow a))
        houter := by
  exact expect_bindPairLaw_tower μ ν u hjoint hrow houter

theorem bind_matching_summaries_ignores_unreachable_branches :
    (twoPointNat.bind fun n =>
      if n = 1 ∨ n = 2 then PMF.pure 7 else PMF.pure 99) =
      twoPointBool.bind (fun _ => PMF.pure 7) := by
  have hsupport : ∀ n ∈ twoPointNat.support, n = 1 ∨ n = 2 := by
    intro n hn
    rw [PMF.mem_support_iff, twoPointNat, mix_apply, PMF.pure_apply] at hn
    by_cases h1 : n = 1
    · exact Or.inl h1
    · by_cases h2 : n = 2
      · exact Or.inr h2
      · simp [h1, h2] at hn
  calc
    twoPointNat.bind (fun n =>
        if n = 1 ∨ n = 2 then PMF.pure 7 else PMF.pure 99) =
      twoPointNat.bind (fun _ => PMF.pure 7) := by
        apply bind_congr_on_support
        intro n hn
        simp [hsupport n hn]
    _ = PMF.pure 7 := PMF.bind_const _ _
    _ = twoPointBool.bind (fun _ => PMF.pure 7) := (PMF.bind_const _ _).symm

theorem projection_identity {ι : Type*} [Fintype ι] {A : ι → Type*}
    (laws : ∀ i, PMF (A i)) :
    (independentProduct laws).map (fun values i => values i) = independentProduct laws :=
  independentProduct_map_embedding (Function.Embedding.refl ι) laws

theorem projection_proper_subset (laws : Fin 3 → PMF Nat) :
    (independentProduct laws).map
      (fun values (i : Fin 2) => values (i.castLE (by decide))) =
      independentProduct (fun i : Fin 2 => laws (i.castLE (by decide))) := by
  let e : Fin 2 ↪ Fin 3 := ⟨fun i => i.castLE (by decide), Fin.castLE_injective (by decide)⟩
  exact independentProduct_map_embedding e laws

theorem projection_empty {ι : Type*} [Fintype ι] {A : ι → Type*}
    (laws : ∀ i, PMF (A i)) (e : Fin 0 ↪ ι) :
    (independentProduct laws).map (fun values i => values (e i)) =
      PMF.pure (fun i => Fin.elim0 i) := by
  rw [independentProduct_map_embedding e laws]
  have hlaws : (fun i : Fin 0 => laws (e i)) =
      (fun i : Fin 0 => PMF.pure (Fin.elim0 i)) := by
    funext i
    exact Fin.elim0 i
  rw [hlaws, independentProduct_pure]

end GameTheory.Tests.PMFProbabilityLemmas
