import GameTheory.Core.MatrixGame
import GameTheory.Core.Mixed
import GameTheory.Math.Probability.ExpectationComposition
import GameTheory.Math.Probability.JointMap

/-! Two payoff matrices share the canonical row/column game form. Independent
mixed play and its pure-deviation tests are expressed using ordinary PMFs. -/

noncomputable section

namespace GameTheory.MatrixGame

open GameTheory.Math.Probability

universe u

/-- General-sum row and column utilities on the existing matrix game form. -/
def bimatrixUtility {I J : Type u} (A B : I → J → ℝ) : I × J → Fin 2 → ℝ :=
  fun x => Fin.cons (A x.1 x.2) (Fin.cons (B x.1 x.2) fun k => k.elim0)

/-- Two payoff tables interpreted by the canonical deterministic game form. -/
@[reducible] def bimatrixGame {I J : Type u} (A B : I → J → ℝ) : UtilityGame (Fin 2) where
  form := form I J
  utility := bimatrixUtility A B

/-- Independent mixed play is the ordinary joint law of the two marginal draws. -/
theorem mixed_play_eq_bindPairLaw {I J : Type u} (p : PMF I) (q : PMF J) :
    (form I J).mixed.play (mixedProfile p q) = bindPairLaw p (fun _ => q) := by
  calc
    _ = p.bind (fun a => (form I J).mixed.play (mixedProfile (PMF.pure a) q)) := by
      have h := mixed_play_update_self (form I J) (mixedProfile p q) 0
      simpa only [mixedProfile_zero, mixedProfile_update_zero] using h
    _ = _ := by
      apply congrArg (PMF.bind p)
      funext a
      exact mixed_play_pure_row a q

/-- For finite action carriers, mixed Nash is equivalent to the two families of
pure-action payoff inequalities. -/
theorem isNash_bimatrix_iff {I J : Type u} [Fintype I] [Fintype J]
    (A B : I → J → ℝ) (p : PMF I) (q : PMF J) :
    IsNash (form I J).mixed (euPreference (bimatrixUtility A B)) (mixedProfile p q) ↔
      (∀ a, expect q (A a) ≤ expect (bindPairLaw p (fun _ => q)) (fun x => A x.1 x.2)) ∧
      (∀ b, expect p (fun a => B a b) ≤
        expect (bindPairLaw p (fun _ => q)) (fun x => B x.1 x.2)) := by
  rw [isNash_mixed_iff (hdev := fun _ _ =>
    UtilityIntegrable.hasExpectation (payoffIntegrable_of_finite _ _))]
  have hrow (a : I) :
      euPreference (bimatrixUtility A B) 0 ((form I J).mixed.play (mixedProfile p q))
        ((form I J).mixed.play (Profile.update (mixedProfile p q) 0 (PMF.pure a))) ↔
      expect q (A a) ≤ expect (bindPairLaw p (fun _ => q)) (fun x => A x.1 x.2) := by
    rw [euPreference_iff _ _ _ _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
    change expect ((form I J).mixed.play (Profile.update (mixedProfile p q) 0 (PMF.pure a)))
      (fun x => A x.1 x.2) ≤ expect ((form I J).mixed.play (mixedProfile p q))
      (fun x => A x.1 x.2) ↔ _
    rw [mixedProfile_update_zero, mixed_play_pure_row, mixed_play_eq_bindPairLaw, expect_map]
    rfl
  have hcol (b : J) :
      euPreference (bimatrixUtility A B) 1 ((form I J).mixed.play (mixedProfile p q))
        ((form I J).mixed.play (Profile.update (mixedProfile p q) 1 (PMF.pure b))) ↔
      expect p (fun a => B a b) ≤ expect (bindPairLaw p (fun _ => q)) (fun x => B x.1 x.2) := by
    rw [euPreference_iff _ _ _ _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
    change expect ((form I J).mixed.play (Profile.update (mixedProfile p q) 1 (PMF.pure b)))
      (fun x => B x.1 x.2) ≤ expect ((form I J).mixed.play (mixedProfile p q))
      (fun x => B x.1 x.2) ↔ _
    rw [mixedProfile_update_one, mixed_play_pure_column, mixed_play_eq_bindPairLaw, expect_map]
    rfl
  constructor
  · intro h
    exact ⟨fun a => (hrow a).mp (h 0 a), fun b => (hcol b).mp (h 1 b)⟩
  · rintro ⟨hp, hq⟩ who a
    fin_cases who
    · exact (hrow a).mpr (hp a)
    · exact (hcol a).mpr (hq a)

/-- Renaming both independently sampled actions by an equivalence preserves
the expected payoff of the corresponding renamed table. -/
theorem expect_bimatrix_map_equiv {I J : Type u} (e : I ≃ J)
    (A : I → I → ℝ) (p q : PMF I) :
    expect (bindPairLaw (p.map e) (fun _ => q.map e))
      (fun x => A (e.symm x.1) (e.symm x.2)) =
    expect (bindPairLaw p (fun _ => q)) (fun x => A x.1 x.2) := by
  rw [bindPairLaw_map, expect_map]
  simp only [Function.comp_def, Equiv.symm_apply_apply]

/-- A finite symmetric bimatrix equilibrium is invariant under bijective action
renaming, using the canonical Nash predicate on both sides. -/
theorem isNash_symmetric_bimatrix_map_equiv {I J : Type u} [Fintype I] [Fintype J]
    (e : I ≃ J) (A : I → I → ℝ) (p q : PMF I) :
    IsNash (form I I).mixed (euPreference (bimatrixUtility A (fun a b => A b a)))
      (mixedProfile p q) ↔
    IsNash (form J J).mixed
      (euPreference (bimatrixUtility (fun a b => A (e.symm a) (e.symm b))
        (fun a b => A (e.symm b) (e.symm a))))
      (mixedProfile (p.map e) (q.map e)) := by
  rw [isNash_bimatrix_iff, isNash_bimatrix_iff]
  simp only [expect_map, Function.comp_def, Equiv.symm_apply_apply]
  rw [expect_bimatrix_map_equiv e A p q,
    expect_bimatrix_map_equiv e (fun a b => A b a) p q]
  constructor
  · rintro ⟨hp, hq⟩
    exact ⟨fun a => hp (e.symm a), fun b => hq (e.symm b)⟩
  · rintro ⟨hp, hq⟩
    exact ⟨fun a => by simpa using hp (e a), fun b => by simpa using hq (e b)⟩

end GameTheory.MatrixGame
