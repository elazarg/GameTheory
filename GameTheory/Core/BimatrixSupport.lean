import GameTheory.Core.BimatrixGame

/-! Pure actions in the support of a bimatrix Nash equilibrium attain the
incumbent expected payoff. These equalities give linear constraints once the
two supports are fixed. -/

noncomputable section

namespace GameTheory.MatrixGame

open GameTheory.Math.Probability

universe u

/-- Every positively weighted row action attains the row equilibrium payoff. -/
theorem row_payoff_eq_of_mem_support {I J : Type u} [Fintype I] [Fintype J]
    (A B : I → J → ℝ) (p : PMF I) (q : PMF J)
    (hnash : IsNash (form I J).mixed (euPreference (bimatrixUtility A B))
      (mixedProfile p q)) (a : I) (ha : a ∈ p.support) :
    expect q (A a) =
      expect (bindPairLaw p (fun _ => q)) (fun x => A x.1 x.2) := by
  have hle := (isNash_bimatrix_iff A B p q).mp hnash
  exact expect_eq_const_of_le_on_support p (fun a => expect q (A a)) _
    (payoffIntegrable_of_finite _ _) (fun a _ => hle.1 a)
    (expect_bindPairLaw_tower p q (fun x => A x.1 x.2)
      (payoffIntegrable_of_finite _ _)).symm a ha

/-- Every positively weighted column action attains the column equilibrium payoff. -/
theorem col_payoff_eq_of_mem_support {I J : Type u} [Fintype I] [Fintype J]
    (A B : I → J → ℝ) (p : PMF I) (q : PMF J)
    (hnash : IsNash (form I J).mixed (euPreference (bimatrixUtility A B))
      (mixedProfile p q)) (b : J) (hb : b ∈ q.support) :
    expect p (fun a => B a b) =
      expect (bindPairLaw p (fun _ => q)) (fun x => B x.1 x.2) := by
  have hle := (isNash_bimatrix_iff A B p q).mp hnash
  have hswap : expect (bindPairLaw p (fun _ => q)) (fun x => B x.1 x.2) =
      expect (bindPairLaw q (fun _ => p)) (fun x => B x.2 x.1) := by
    rw [← bindPairLaw_const_map_swap p q, expect_map]
    rfl
  apply expect_eq_const_of_le_on_support q (fun b => expect p (fun a => B a b)) _
    (payoffIntegrable_of_finite _ _) (fun b _ => hle.2 b) ?_ b hb
  rw [hswap]
  exact (expect_bindPairLaw_tower q p (fun x => B x.2 x.1)
    (payoffIntegrable_of_finite _ _)).symm

end GameTheory.MatrixGame
