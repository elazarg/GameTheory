import GameTheory.Core.SatisfiabilityGame

/-! A high-payoff mixed equilibrium of the literal/clause game determines a
satisfying assignment. Welfare saturation restricts the independent supports to
compatible literals; variable and clause deviations then certify coverage. -/

noncomputable section

namespace GameTheory.SatisfiabilityGame

open GameTheory.Math.Probability

private theorem welfare_le_two {n m : ℕ} (C : Clauses n m) (a b : Action n m) :
    payoff C a b + payoff C b a ≤ 2 := by
  rcases a with ⟨v, d⟩ | (v | (c | ⟨⟩)) <;>
    rcases b with ⟨w, e⟩ | (w | (c' | ⟨⟩)) <;>
    simp only [payoff, payoffInt] <;> try split_ifs
  all_goals
    norm_num <;> linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]

private theorem literals_of_welfare_eq_two {n m : ℕ} (C : Clauses n m)
    (a b : Action n m) (h : payoff C a b + payoff C b a = 2) :
    ∃ v d w e, a = literal v d ∧ b = literal w e ∧ (v = w → d = e) := by
  rcases a with ⟨v, d⟩ | (v | (c | ⟨⟩)) <;>
    rcases b with ⟨w, e⟩ | (w | (c' | ⟨⟩))
  case inl.inl =>
    refine ⟨v, d, w, e, rfl, rfl, ?_⟩
    intro hv
    by_contra hd
    simp [payoff, payoffInt, hv, hd, Ne.symm hd] at h
    norm_num at h
  all_goals
    simp only [payoff, payoffInt] at h
    try split_ifs at h
    all_goals norm_num at h <;> linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]

private theorem welfare_saturates {n m : ℕ} (C : Clauses n m)
    (p q : PMF (Action n m)) (hp : 1 ≤ value C p q) (hq : 1 ≤ value C q p) :
    ∀ a ∈ p.support, ∀ b ∈ q.support, payoff C a b + payoff C b a = 2 := by
  let μ := bindPairLaw p (fun _ => q)
  let f := fun x : Action n m × Action n m => payoff C x.1 x.2 + payoff C x.2 x.1
  have hswap : expect μ (fun x => payoff C x.2 x.1) = value C q p := by
    rw [value, ← bindPairLaw_const_map_swap p q, expect_map]
    rfl
  have hsum : expect μ f = value C p q + value C q p := by
    rw [expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _), hswap]
    rfl
  have hle : ∀ x ∈ μ.support, f x ≤ 2 := fun x _ => welfare_le_two C x.1 x.2
  have hbound := expect_le_const μ f (payoffIntegrable_of_finite _ _) 2 hle
  have heq : expect μ f = 2 := by rw [hsum] at hbound ⊢; linarith
  have hs := expect_eq_const_of_le_on_support μ f 2 (payoffIntegrable_of_finite _ _) hle heq
  intro a ha b hb
  apply hs (a, b)
  rw [PMF.mem_support_iff, bindPairLaw_apply]
  exact mul_ne_zero ((PMF.mem_support_iff p a).mp ha) ((PMF.mem_support_iff q b).mp hb)

private theorem value_eq_one_of_threshold {n m : ℕ} (C : Clauses n m)
    (p q : PMF (Action n m)) (hp : 1 ≤ value C p q) (hq : 1 ≤ value C q p) :
    value C p q = 1 := by
  unfold value
  calc
    _ = expect (bindPairLaw p (fun _ => q)) (fun _ => 1) := by
      apply expect_congr_on_support
      rintro ⟨a, b⟩ hab
      have hnz : p a * q b ≠ 0 := by
        simpa only [bindPairLaw_apply] using (PMF.mem_support_iff _ _).mp hab
      have ha : a ∈ p.support := (PMF.mem_support_iff p a).mpr (mul_ne_zero_iff.mp hnz).1
      have hb : b ∈ q.support := (PMF.mem_support_iff q b).mpr (mul_ne_zero_iff.mp hnz).2
      obtain ⟨v, d, w, e, rfl, rfl, hc⟩ :=
        literals_of_welfare_eq_two C a b (welfare_saturates C p q hp hq a ha b hb)
      have hnot : ¬(v = w ∧ d ≠ e) := fun h => h.2 (hc h.1)
      simp [payoff, payoffInt, literal, hnot]
    _ = 1 := expect_constant _ _

/-- At the two payoff thresholds, every independently supported action pair
consists of literals whose signs agree whenever their variables agree. -/
theorem compatible_support_of_threshold {n m : ℕ} (C : Clauses n m)
    (p q : PMF (Action n m)) (hp : 1 ≤ value C p q) (hq : 1 ≤ value C q p)
    (a : Action n m) (ha : a ∈ p.support) (b : Action n m) (hb : b ∈ q.support) :
    ∃ v d w e, a = literal v d ∧ b = literal w e ∧ (v = w → d = e) :=
  literals_of_welfare_eq_two C a b (welfare_saturates C p q hp hq a ha b hb)

private theorem variable_coverage {n m : ℕ} (C : Clauses n m)
    (p q : PMF (Action n m)) (hp : 1 ≤ value C p q) (hq : 1 ≤ value C q p)
    (hdev : ∀ a, expect q (payoff C a) ≤ value C p q) (v : Fin n) :
    ∃ d, literal v d ∈ q.support := by
  by_contra hmissing
  have hconstant : expect q (payoff C (variableAction v)) = 2 := by
    calc
      _ = expect q (fun _ => 2) := by
        apply expect_congr_on_support
        intro b hb
        obtain ⟨a, ha⟩ := p.support_nonempty
        obtain ⟨w, d, z, e, _, rfl, _⟩ :=
          compatible_support_of_threshold C p q hp hq a ha b hb
        have hvz : v ≠ z := by
          intro hvz
          subst z
          exact hmissing ⟨e, hb⟩
        simp [payoff, payoffInt, variableAction, literal, hvz]
      _ = 2 := expect_constant _ _
  have hbound := hdev (variableAction v)
  rw [hconstant, value_eq_one_of_threshold C p q hp hq] at hbound
  norm_num at hbound

private theorem clause_coverage {n m : ℕ} (C : Clauses n m)
    (p q : PMF (Action n m)) (hp : 1 ≤ value C p q) (hq : 1 ≤ value C q p)
    (hdev : ∀ a, expect q (payoff C a) ≤ value C p q) (c : Fin m) :
    ∃ v d, literal v d ∈ q.support ∧ C c v d = true := by
  by_contra hmissing
  have hconstant : expect q (payoff C (clause c)) = 2 := by
    calc
      _ = expect q (fun _ => 2) := by
        apply expect_congr_on_support
        intro b hb
        obtain ⟨a, ha⟩ := p.support_nonempty
        obtain ⟨w, d, z, e, _, rfl, _⟩ :=
          compatible_support_of_threshold C p q hp hq a ha b hb
        have hfalse : C c z e = false := by
          cases he : C c z e
          · rfl
          · exact False.elim (hmissing ⟨z, e, hb, he⟩)
        simp [payoff, payoffInt, clause, literal, hfalse]
      _ = 2 := expect_constant _ _
  have hbound := hdev (clause c)
  rw [hconstant, value_eq_one_of_threshold C p q hp hq] at hbound
  norm_num at hbound

/-- A canonical mixed Nash equilibrium giving both players payoff at least one
certifies a satisfying assignment. The conclusion holds even for an empty
variable carrier; such a carrier cannot support the required high-payoff play. -/
theorem satisfies_of_nash_threshold {n m : ℕ} (C : Clauses n m)
    (p q : PMF (Action n m))
    (hnash : IsNash (game C).form.mixed (euPreference (game C).utility)
      (MatrixGame.mixedProfile p q))
    (hp : 1 ≤ value C p q) (hq : 1 ≤ value C q p) :
    ∃ τ, Satisfies C τ := by
  classical
  obtain ⟨hrow, hcol⟩ := (isNash_iff C p q).mp hnash
  let τ : Fin n → Bool := fun v => (variable_coverage C p q hp hq hrow v).choose
  have hτ (v : Fin n) : literal v (τ v) ∈ q.support :=
    (variable_coverage C p q hp hq hrow v).choose_spec
  have hagree (v : Fin n) (d e : Bool)
      (hd : literal v d ∈ p.support) (he : literal v e ∈ q.support) : d = e := by
    have hs := welfare_saturates C p q hp hq (literal v d) hd (literal v e) he
    by_contra hne
    simp [payoff, payoffInt, literal, hne, Ne.symm hne] at hs
    norm_num at hs
  have hsign (v : Fin n) (d : Bool) (hd : literal v d ∈ q.support) : τ v = d := by
    obtain ⟨e, he⟩ := variable_coverage C q p hq hp hcol v
    exact (hagree v e (τ v) he (hτ v)).symm.trans (hagree v e d he hd)
  refine ⟨τ, fun c => ?_⟩
  obtain ⟨v, d, hd, hc⟩ := clause_coverage C p q hp hq hrow c
  exact ⟨v, by rwa [hsign v d hd]⟩

end GameTheory.SatisfiabilityGame
