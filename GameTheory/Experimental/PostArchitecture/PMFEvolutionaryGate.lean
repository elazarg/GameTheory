/-
# EXP-137: positive-invasion integrability in mixed evolutionary stability

A unique pure resident beats every distinct mutant in the first-order test,
but a geometric mutant has an undefined positive self encounter. The ordinary
all-pair guard rejects it, as does the actual small-invasion formulation.
-/

import GameTheory.Evolutionary
import GameTheory.Experimental.PostArchitecture.PMFRestorationProbe

noncomputable section

namespace GameTheory.Experimental.PMFEvolutionaryGate

open GameTheory.Evolutionary GameTheory.Math.Probability
open GameTheory.Experimental.PMFRestoration

def resident : PMF (Option ℕ) := PMF.pure none

def mutant : PMF (Option ℕ) := geometric.map some

def payoff : Option ℕ → Option ℕ → ℝ
  | none, _ => 1
  | some _, none => 0
  | some n, some _ => exploding n

private theorem mutant_action (action : Option ℕ)
    (haction : action ∈ mutant.support) : ∃ n, action = some n := by
  rw [mutant, PMF.support_map] at haction
  obtain ⟨n, _, rfl⟩ := haction
  exact ⟨n, rfl⟩

theorem resident_self_integrable :
    PayoffIntegrable (bindPairLaw resident (fun _ => resident))
      (fun pair => payoff pair.1 pair.2) := by
  simpa only [resident, bindPairLaw, PMF.pure_bind, PMF.pure_map] using
    (payoffIntegrable_pure (none, none)
      (fun pair => payoff pair.1 pair.2))

theorem resident_self_value :
    mixedPayoff payoff resident resident resident_self_integrable = 1 := by
  unfold mixedPayoff
  simp [resident, bindPairLaw, PMF.pure_bind, PMF.pure_map,
    expect_pure, payoff]

private theorem mutant_resident_score_zero
    (pair : Option ℕ × Option ℕ)
    (hpair : pair ∈ (bindPairLaw mutant (fun _ => resident)).support) :
    payoff pair.1 pair.2 = 0 := by
  rcases pair with ⟨own, opponent⟩
  have hne : mutant own * resident opponent ≠ 0 := by
    simpa only [bindPairLaw_apply] using
      ((bindPairLaw mutant (fun _ => resident)).mem_support_iff
        (own, opponent)).mp hpair
  have hown : own ∈ mutant.support := by
    apply (mutant.mem_support_iff own).mpr
    intro hzero
    simp [hzero] at hne
  have hopponent : opponent = none := by
    have hsupport : opponent ∈ resident.support := by
      apply (resident.mem_support_iff opponent).mpr
      intro hzero
      simp [hzero] at hne
    simpa only [resident, PMF.mem_support_pure_iff] using hsupport
  obtain ⟨n, rfl⟩ := mutant_action own hown
  simp [payoff, hopponent]

theorem mutant_resident_integrable :
    PayoffIntegrable (bindPairLaw mutant (fun _ => resident))
      (fun pair => payoff pair.1 pair.2) := by
  let joint := bindPairLaw mutant (fun _ => resident)
  have hzero : PayoffIntegrable joint (fun _ => (0 : ℝ)) :=
    payoffIntegrable_zero joint
  have hpoint : ∀ pair ∈ joint.support,
      (0 : ℝ) = payoff pair.1 pair.2 := by
    intro pair hpair
    exact (mutant_resident_score_zero pair hpair).symm
  exact payoffIntegrable_congr_on_support hpoint hzero

theorem mutant_resident_value :
    mixedPayoff payoff mutant resident mutant_resident_integrable = 0 := by
  unfold mixedPayoff
  have hzero := expect_congr_on_support
    mutant_resident_score_zero mutant_resident_integrable
    (payoffIntegrable_zero (bindPairLaw mutant (fun _ => resident)))
  simpa only [expect_zero] using hzero

/-- The resident wins the defined first-order test strictly. -/
theorem resident_strict_first_order :
    mixedPayoff payoff resident resident resident_self_integrable >
      mixedPayoff payoff mutant resident mutant_resident_integrable := by
  rw [resident_self_value, mutant_resident_value]
  norm_num

private theorem resident_opponent_none (own : PMF (Option ℕ))
    (pair : Option ℕ × Option ℕ)
    (hpair : pair ∈ (bindPairLaw own (fun _ => resident)).support) :
    pair.2 = none := by
  rcases pair with ⟨action, opponent⟩
  have hne : own action * resident opponent ≠ 0 := by
    simpa only [bindPairLaw_apply] using
      ((bindPairLaw own (fun _ => resident)).mem_support_iff
        (action, opponent)).mp hpair
  have hsupport : opponent ∈ resident.support := by
    apply (resident.mem_support_iff opponent).mpr
    intro hzero
    simp [hzero] at hne
  simpa only [resident, PMF.mem_support_pure_iff] using hsupport

private theorem own_resident_score (own : PMF (Option ℕ))
    (pair : Option ℕ × Option ℕ)
    (hpair : pair ∈ (bindPairLaw own (fun _ => resident)).support) :
    payoff pair.1 pair.2 = if pair.1 = none then 1 else 0 := by
  rw [resident_opponent_none own pair hpair]
  cases pair.1 <;> simp [payoff]

theorem own_resident_integrable (own : PMF (Option ℕ)) :
    PayoffIntegrable (bindPairLaw own (fun _ => resident))
      (fun pair => payoff pair.1 pair.2) := by
  apply payoffIntegrable_of_bounded_on_support (C := 1)
  intro pair hpair
  rw [own_resident_score own pair hpair]
  cases pair.1 <;> norm_num

theorem own_resident_value (own : PMF (Option ℕ)) :
    mixedPayoff payoff own resident (own_resident_integrable own) =
      (own none).toReal := by
  let joint := bindPairLaw own (fun _ => resident)
  let score : Option ℕ → ℝ := fun action => if action = none then 1 else 0
  have hown : PayoffIntegrable own score := by
    apply payoffIntegrable_of_bounded own score (C := 1)
    intro action
    cases action <;> simp [score]
  have hmap : PayoffIntegrable (joint.map Prod.fst) score :=
    payoffIntegrable_congr_law
      (bindPairLaw_map_fst own (fun _ => resident)).symm hown
  have hjoint : PayoffIntegrable joint (fun pair => score pair.1) :=
    (payoffIntegrable_map_iff Prod.fst joint score).mp hmap
  have hpoint : ∀ pair ∈ joint.support,
      payoff pair.1 pair.2 = score pair.1 := by
    intro pair hpair
    exact own_resident_score own pair hpair
  calc
    mixedPayoff payoff own resident (own_resident_integrable own) =
        expect joint (fun pair => score pair.1) hjoint :=
      expect_congr_on_support hpoint (own_resident_integrable own) hjoint
    _ = expect (joint.map Prod.fst) score hmap := by
      exact (expect_map Prod.fst joint score hjoint hmap).symm
    _ = expect own score hown :=
      expect_congr_law (bindPairLaw_map_fst own (fun _ => resident))
        score hmap hown
    _ = (own none).toReal := by
      unfold expect
      rw [tsum_eq_single none]
      · simp [score]
      · intro action hne
        cases action with
        | none => exact False.elim (hne rfl)
        | some n => simp [score]

theorem own_resident_strict_first_order (own : PMF (Option ℕ))
    (hne : own ≠ resident) :
    mixedPayoff payoff resident resident (own_resident_integrable resident) >
      mixedPayoff payoff own resident (own_resident_integrable own) := by
  rw [own_resident_value, own_resident_value]
  have hnotone : own none ≠ 1 := by
    intro hone
    apply hne
    have hsupport := (own.apply_eq_one_iff none).mp hone
    exact pmf_eq_pure_of_support_subset_singleton own none
      (by rw [hsupport])
  have hlt : own none < 1 :=
    lt_of_le_of_ne (own.coe_le_one none) hnotone
  have hreal : (own none).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal (own.apply_ne_top none)
      ENNReal.one_ne_top).2 hlt
  simpa [resident, PMF.pure_apply] using hreal

theorem mutant_self_not_integrable :
    ¬ PayoffIntegrable (bindPairLaw mutant (fun _ => mutant))
      (fun pair => payoff pair.1 pair.2) := by
  intro hself
  let joint := bindPairLaw mutant (fun _ => mutant)
  have hown : PayoffIntegrable joint
      (fun pair => pair.1.elim 0 exploding) := by
    apply payoffIntegrable_congr_on_support
      (μ := joint) (f := fun pair => payoff pair.1 pair.2)
      (g := fun pair => pair.1.elim 0 exploding)
    · rintro ⟨a, b⟩ hab
      have ha : a ∈ mutant.support := by
        have hne : joint (a, b) ≠ 0 :=
          (joint.mem_support_iff (a, b)).mp hab
        rw [show joint (a, b) = mutant a * mutant b from
          bindPairLaw_apply mutant (fun _ => mutant) a b] at hne
        apply (mutant.mem_support_iff a).mpr
        intro hzero
        simp [hzero] at hne
      have hb : b ∈ mutant.support := by
        have hne : joint (a, b) ≠ 0 :=
          (joint.mem_support_iff (a, b)).mp hab
        rw [show joint (a, b) = mutant a * mutant b from
          bindPairLaw_apply mutant (fun _ => mutant) a b] at hne
        apply (mutant.mem_support_iff b).mpr
        intro hzero
        simp [hzero] at hne
      obtain ⟨m, rfl⟩ := mutant_action a ha
      obtain ⟨n, rfl⟩ := mutant_action b hb
      rfl
    · exact hself
  have hmap : PayoffIntegrable (joint.map Prod.fst)
      (fun action => action.elim 0 exploding) :=
    (payoffIntegrable_map_iff Prod.fst joint _).mpr hown
  have hmutant : PayoffIntegrable mutant
      (fun action => action.elim 0 exploding) :=
    payoffIntegrable_congr_law
      (bindPairLaw_map_fst mutant (fun _ => mutant)) hmap
  have hgeometric : PayoffIntegrable geometric exploding := by
    have hsource := (payoffIntegrable_map_iff
      some geometric (fun action : Option ℕ => action.elim 0 exploding)).mp
        hmutant
    simpa [Function.comp_def] using hsource
  apply exploding_not_summable
  have hnonneg (n : ℕ) : 0 ≤ exploding n := by
    unfold exploding
    positivity
  simpa only [PayoffIntegrable, abs_of_nonneg (hnonneg _)] using hgeometric

theorem positive_invasion_not_integrable (share : ℝ)
    (hpositive : 0 < share) (hunit : share < 1) :
    ¬ PayoffIntegrable
      (bindPairLaw mutant (fun _ =>
        invasionPopulation resident mutant share hpositive hunit))
      (fun pair => payoff pair.1 pair.2) := by
  intro hinvasion
  exact mutant_self_not_integrable
    (pairPayoffIntegrable_self_of_positive_invasion
      payoff resident mutant share hpositive hunit hinvasion)

theorem resident_not_mixedESS : ¬ IsMixedESS payoff resident := by
  rintro ⟨hall, _⟩
  exact mutant_self_not_integrable (hall mutant mutant)

theorem resident_not_mixedNSS : ¬ IsMixedNSS payoff resident := by
  rintro ⟨hall, _⟩
  exact mutant_self_not_integrable (hall mutant mutant)

theorem resident_not_actualSmallInvasionESS :
    ¬ IsActualSmallInvasionESS payoff resident := by
  intro hactual
  exact resident_not_mixedESS
    ((isMixedESS_iff_actualSmallInvasion payoff resident).2 hactual)

theorem resident_not_actualSmallInvasionNSS :
    ¬ IsActualSmallInvasionNSS payoff resident := by
  intro hactual
  exact resident_not_mixedNSS
    ((isMixedNSS_iff_actualSmallInvasion payoff resident).2 hactual)

end GameTheory.Experimental.PMFEvolutionaryGate
