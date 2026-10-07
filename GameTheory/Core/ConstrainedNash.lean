import GameTheory.Core.BimatrixGame

/-! Payoff-constrained equilibrium existence uses the canonical mixed Nash
predicate together with explicit expected-payoff thresholds. Integrability is
required so each real threshold compares a meaningful expected utility. -/

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo u

/-- A mixed Nash equilibrium meeting each player's expected-payoff threshold.
The integrability clauses give the real threshold comparisons their meaning. -/
def UtilityGame.HasNashWithPayoffAtLeast {ι : Type uι} [Fintype ι] [DecidableEq ι]
    (G : UtilityGame.{uι, us, uo} ι) (threshold : ι → ℝ) : Prop :=
  ∃ σ : Profile G.form.sig.mixed,
    IsNash G.form.mixed (euPreference G.utility) σ ∧
      ∀ who, UtilityIntegrable G.utility who (G.form.mixed.play σ) ∧
        threshold who ≤ expectedUtility G.utility who (G.form.mixed.play σ)

namespace MatrixGame

/-- A two-player mixed profile is determined by its row and column laws. -/
theorem mixedProfile_eta {I J : Type u} (σ : Profile (form I J).sig.mixed) :
    mixedProfile (σ 0) (σ 1) = σ := by
  funext who
  fin_cases who <;> rfl

/-- For a finite bimatrix game, the payoff-one constraint is exactly the two
independent expected-payoff inequalities, with the same canonical Nash profile. -/
theorem hasNashWithPayoffAtLeast_iff {I J : Type u} [Fintype I] [Fintype J]
    (A B : I → J → ℝ) :
    (bimatrixGame A B).HasNashWithPayoffAtLeast (fun _ => 1) ↔
      ∃ (p : PMF I) (q : PMF J),
        IsNash (form I J).mixed (euPreference (bimatrixUtility A B)) (mixedProfile p q) ∧
          1 ≤ expect (bindPairLaw p (fun _ => q)) (fun x => A x.1 x.2) ∧
          1 ≤ expect (bindPairLaw p (fun _ => q)) (fun x => B x.1 x.2) := by
  constructor
  · rintro ⟨σ, hnash, hpay⟩
    have hη := mixedProfile_eta σ
    refine ⟨σ 0, σ 1, ?_, ?_, ?_⟩
    · rwa [hη]
    · have h := (hpay 0).2
      change 1 ≤ expect ((form I J).mixed.play σ) (fun x => A x.1 x.2) at h
      rw [← hη, mixed_play_eq_bindPairLaw] at h
      exact h
    · have h := (hpay 1).2
      change 1 ≤ expect ((form I J).mixed.play σ) (fun x => B x.1 x.2) at h
      rw [← hη, mixed_play_eq_bindPairLaw] at h
      exact h
  · rintro ⟨p, q, hnash, hp, hq⟩
    refine ⟨mixedProfile p q, hnash, ?_⟩
    intro who
    refine ⟨payoffIntegrable_of_finite _ _, ?_⟩
    fin_cases who
    · change 1 ≤ expect ((form I J).mixed.play (mixedProfile p q)) (fun x => A x.1 x.2)
      rwa [mixed_play_eq_bindPairLaw]
    · change 1 ≤ expect ((form I J).mixed.play (mixedProfile p q)) (fun x => B x.1 x.2)
      rwa [mixed_play_eq_bindPairLaw]

private theorem hasNashWithPayoffAtLeast_map {I J : Type u} [Fintype I] [Fintype J]
    (e : I ≃ J) (A : I → I → ℝ) :
    (bimatrixGame A (fun a b => A b a)).HasNashWithPayoffAtLeast (fun _ => 1) →
      (bimatrixGame (fun a b => A (e.symm a) (e.symm b))
        (fun a b => A (e.symm b) (e.symm a))).HasNashWithPayoffAtLeast (fun _ => 1) := by
  rw [hasNashWithPayoffAtLeast_iff, hasNashWithPayoffAtLeast_iff]
  rintro ⟨p, q, hnash, hp, hq⟩
  refine ⟨p.map e, q.map e, (isNash_symmetric_bimatrix_map_equiv e A p q).mp hnash, ?_, ?_⟩
  · rwa [expect_bimatrix_map_equiv]
  · rwa [expect_bimatrix_map_equiv e (fun a b => A b a)]

/-- Bijective action renaming preserves existence of a symmetric mixed Nash
equilibrium meeting the payoff-one thresholds. -/
theorem hasNashWithPayoffAtLeast_map_equiv {I J : Type u} [Fintype I] [Fintype J]
    (e : I ≃ J) (A : I → I → ℝ) :
    (bimatrixGame A (fun a b => A b a)).HasNashWithPayoffAtLeast (fun _ => 1) ↔
      (bimatrixGame (fun a b => A (e.symm a) (e.symm b))
        (fun a b => A (e.symm b) (e.symm a))).HasNashWithPayoffAtLeast (fun _ => 1) := by
  refine ⟨hasNashWithPayoffAtLeast_map e A, fun h => ?_⟩
  have hback := hasNashWithPayoffAtLeast_map e.symm
    (fun a b => A (e.symm a) (e.symm b)) h
  simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using hback

end MatrixGame

end GameTheory
