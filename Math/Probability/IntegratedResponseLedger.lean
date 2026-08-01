/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.TriangularLedger

/-!
# Integrated response ledgers

This file composes the weighted reset ledger with the shadow-or-separator
payoff ledger.  It records one accounting implication: separator charge need
not carry a separate sublinearity hypothesis when it is paid by the
nonnegative charges of a bounded weighted reset ledger.

The hypotheses remain purely algebraic.  In particular, the results do not
construct accounts, separators, shadows, or a stochastic strategy.
-/

open Filter

namespace Math.Probability

noncomputable section

open scoped BigOperators

/-- Total charge paid by all reset-ledger accounts before a horizon. -/
def totalAccountCharge
    {Account : Type*} [Fintype Account]
    (charge : ℕ → Account → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, ∑ account, charge t account

/-- The part of the shadow-or-separator budget not paid by separator charge. -/
def shadowSeparatorExternalCumulativeBudget
    (T : ℕ)
    (potentialDrift goodBudget : ℕ → ℝ)
    (potentialNoise goodNoise separatorNoise : ℕ → ℝ) : ℝ :=
  ∑ t ∈ Finset.range T,
    (potentialDrift t + goodBudget t +
      potentialNoise t + goodNoise t + separatorNoise t)

/-- A nonnegative budget dominated by a sublinear budget is sublinear. -/
theorem IsAsymptoticallySublinear.of_nonneg_le
    {f g : ℕ → ℝ}
    (hf : ∀ T, 0 ≤ f T)
    (hfg : ∀ T, f T ≤ g T)
    (hg : IsAsymptoticallySublinear g) :
    IsAsymptoticallySublinear f := by
  rw [isAsymptoticallySublinear_iff_tendsto]
  rw [isAsymptoticallySublinear_iff_tendsto] at hg
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun T =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg T)) (hf T)
  · exact Filter.Eventually.of_forall fun T =>
      mul_le_mul_of_nonneg_left
        (hfg T) (inv_nonneg.mpr (Nat.cast_nonneg T))
  · exact hg

/-- A bounded weighted reset ledger has sublinear cumulative total charge.

This is the limit form of
`exists_weightedResetChargeAverage_threshold`. -/
theorem weightedResetTotalCharge_isAsymptoticallySublinear
    {Account : Type*} [Fintype Account]
    (potential charge error : ℕ → Account → ℝ)
    (bound weight direct : Account → ℝ)
    (reset : Account → Account → ℝ)
    (hweight : ∀ account, 0 ≤ weight account)
    (hpotential : ∀ t account,
      |potential t account| ≤ bound account)
    (hcharge : ∀ t account, 0 ≤ charge t account)
    (hcoercive : ∀ payer,
      1 ≤ weight payer * direct payer -
        ∑ account, weight account * reset account payer)
    (hlocal : ∀ t account,
      potential (t + 1) account - potential t account +
          direct account * charge t account -
          ∑ payer, reset account payer * charge t payer ≤
        error t account)
    (herror :
      IsAsymptoticallySublinear (fun T =>
        ∑ t ∈ Finset.range T,
          ∑ account, weight account * error t account)) :
    IsAsymptoticallySublinear (totalAccountCharge charge) := by
  let initialBound : ℝ :=
    2 * ∑ account, weight account * bound account
  let upper : ℕ → ℝ := fun T =>
    initialBound +
      ∑ t ∈ Finset.range T,
        ∑ account, weight account * error t account
  have hupper : IsAsymptoticallySublinear upper :=
    (IsAsymptoticallySublinear.const initialBound).add herror
  apply IsAsymptoticallySublinear.of_nonneg_le
  · intro T
    unfold totalAccountCharge
    exact Finset.sum_nonneg fun t _ =>
      Finset.sum_nonneg fun account _ => hcharge t account
  · intro T
    have hledger :=
      sum_charge_le_weightedPotentialDrop_add_error
        T potential charge error weight direct reset hweight
        (fun t _ account => hcharge t account) hcoercive
        (fun t _ account => hlocal t account)
    have hdrop :
        (∑ account,
          weight account *
            (potential 0 account - potential T account)) ≤
          initialBound := by
      unfold initialBound
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro account _
      have hzero := abs_le.mp (hpotential 0 account)
      have hterminal := abs_le.mp (hpotential T account)
      have hpoint :
          potential 0 account - potential T account ≤
            2 * bound account := by
        linarith
      have hscaled :=
        mul_le_mul_of_nonneg_left hpoint (hweight account)
      calc
        weight account *
            (potential 0 account - potential T account) ≤
            weight account * (2 * bound account) :=
          hscaled
        _ = 2 * (weight account * bound account) := by ring
    unfold totalAccountCharge
    calc
      (∑ t ∈ Finset.range T, ∑ account, charge t account) ≤
          (∑ account,
            weight account *
              (potential 0 account - potential T account)) +
            ∑ t ∈ Finset.range T,
              ∑ account, weight account * error t account :=
        hledger
      _ ≤ upper T := by
        unfold upper
        linarith
  · exact hupper

/-- The full shadow-or-separator cumulative budget splits into its external
part and cumulative separator charge. -/
theorem shadowSeparatorCumulativeBudget_eq_external_add_separator
    (T : ℕ)
    (potentialDrift goodBudget separatorCharge : ℕ → ℝ)
    (potentialNoise goodNoise separatorNoise : ℕ → ℝ) :
    shadowSeparatorCumulativeBudget T
        potentialDrift goodBudget separatorCharge
        potentialNoise goodNoise separatorNoise =
      shadowSeparatorExternalCumulativeBudget T
          potentialDrift goodBudget
          potentialNoise goodNoise separatorNoise +
        ∑ t ∈ Finset.range T, separatorCharge t := by
  unfold shadowSeparatorCumulativeBudget
    shadowSeparatorExternalCumulativeBudget
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- Integrated threshold theorem for a separator charge dominated by a
bounded weighted reset ledger.

The only sublinearity premises outside the account ledger concern the five
remaining shadow-or-separator terms and implementation cost. -/
theorem exists_integratedResponsePayoffErrorAverage_threshold
    {Account : Type*} [Fintype Account]
    (L : ℝ)
    (accountPotential accountCharge accountError :
      ℕ → Account → ℝ)
    (accountBound accountWeight accountDirect : Account → ℝ)
    (accountReset : Account → Account → ℝ)
    (potential payoffError implementationCost : ℕ → ℝ)
    (transientCost potentialDrift potentialNoise : ℕ → ℝ)
    (goodMismatch goodBudget goodNoise : ℕ → ℝ)
    (badTolerance separatorCharge separatorNoise : ℕ → ℝ)
    (haccountWeight : ∀ account, 0 ≤ accountWeight account)
    (haccountPotential : ∀ t account,
      |accountPotential t account| ≤ accountBound account)
    (haccountCharge : ∀ t account, 0 ≤ accountCharge t account)
    (haccountCoercive : ∀ payer,
      1 ≤ accountWeight payer * accountDirect payer -
        ∑ account,
          accountWeight account * accountReset account payer)
    (haccountLocal : ∀ t account,
      accountPotential (t + 1) account -
          accountPotential t account +
          accountDirect account * accountCharge t account -
          ∑ payer,
            accountReset account payer * accountCharge t payer ≤
        accountError t account)
    (haccountError :
      IsAsymptoticallySublinear (fun T =>
        ∑ t ∈ Finset.range T,
          ∑ account,
            accountWeight account * accountError t account))
    (hseparator_nonneg : ∀ t, 0 ≤ separatorCharge t)
    (hseparator_le : ∀ t,
      separatorCharge t ≤ ∑ account, accountCharge t account)
    (hL : 0 ≤ L)
    (hpotential_nonneg : ∀ t, 0 ≤ potential t)
    (hbad_nonneg : ∀ t, 0 ≤ badTolerance t)
    (hpayoff : ∀ t,
      payoffError t ≤
        L * (transientCost t + goodMismatch t) +
          implementationCost t)
    (htransient : ∀ t,
      transientCost t =
        potential t - potential (t + 1) +
          potentialDrift t + potentialNoise t)
    (hgood : ∀ t,
      goodMismatch t ≤ goodBudget t + goodNoise t)
    (hbad : ∀ t,
      badTolerance t ≤ separatorCharge t + separatorNoise t)
    (hexternal :
      IsAsymptoticallySublinear (fun T =>
        shadowSeparatorExternalCumulativeBudget T
          potentialDrift goodBudget
          potentialNoise goodNoise separatorNoise))
    (himplementation :
      IsAsymptoticallySublinear (fun T =>
        ∑ t ∈ Finset.range T, implementationCost t))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      (T : ℝ)⁻¹ *
          (∑ t ∈ Finset.range T, payoffError t) ≤
        δ := by
  have htotal :=
    weightedResetTotalCharge_isAsymptoticallySublinear
      accountPotential accountCharge accountError
      accountBound accountWeight accountDirect accountReset
      haccountWeight haccountPotential haccountCharge
      haccountCoercive haccountLocal haccountError
  have hseparatorCumulative :
      IsAsymptoticallySublinear (fun T =>
        ∑ t ∈ Finset.range T, separatorCharge t) := by
    apply IsAsymptoticallySublinear.of_nonneg_le
    · intro T
      exact Finset.sum_nonneg fun t _ => hseparator_nonneg t
    · intro T
      exact Finset.sum_le_sum fun t _ => hseparator_le t
    · exact htotal
  have hbudget :
      IsAsymptoticallySublinear (fun T =>
        shadowSeparatorCumulativeBudget T
          potentialDrift goodBudget separatorCharge
          potentialNoise goodNoise separatorNoise) := by
    simpa only [
      shadowSeparatorCumulativeBudget_eq_external_add_separator] using
        hexternal.add hseparatorCumulative
  exact
    exists_shadowSeparatorPayoffErrorAverage_threshold
      L potential payoffError implementationCost
      transientCost potentialDrift potentialNoise
      goodMismatch goodBudget goodNoise
      badTolerance separatorCharge separatorNoise
      hL hpotential_nonneg hbad_nonneg
      hpayoff htransient hgood hbad
      hbudget himplementation hδ

/-- Equality specialization of the integrated response threshold. -/
theorem exists_integratedResponsePayoffErrorAverage_threshold_of_eq
    {Account : Type*} [Fintype Account]
    (L : ℝ)
    (accountPotential accountCharge accountError :
      ℕ → Account → ℝ)
    (accountBound accountWeight accountDirect : Account → ℝ)
    (accountReset : Account → Account → ℝ)
    (potential payoffError implementationCost : ℕ → ℝ)
    (transientCost potentialDrift potentialNoise : ℕ → ℝ)
    (goodMismatch goodBudget goodNoise : ℕ → ℝ)
    (badTolerance separatorCharge separatorNoise : ℕ → ℝ)
    (haccountWeight : ∀ account, 0 ≤ accountWeight account)
    (haccountPotential : ∀ t account,
      |accountPotential t account| ≤ accountBound account)
    (haccountCharge : ∀ t account, 0 ≤ accountCharge t account)
    (haccountCoercive : ∀ payer,
      1 ≤ accountWeight payer * accountDirect payer -
        ∑ account,
          accountWeight account * accountReset account payer)
    (haccountLocal : ∀ t account,
      accountPotential (t + 1) account -
          accountPotential t account +
          accountDirect account * accountCharge t account -
          ∑ payer,
            accountReset account payer * accountCharge t payer ≤
        accountError t account)
    (haccountError :
      IsAsymptoticallySublinear (fun T =>
        ∑ t ∈ Finset.range T,
          ∑ account,
            accountWeight account * accountError t account))
    (hseparator_eq : ∀ t,
      separatorCharge t = ∑ account, accountCharge t account)
    (hL : 0 ≤ L)
    (hpotential_nonneg : ∀ t, 0 ≤ potential t)
    (hbad_nonneg : ∀ t, 0 ≤ badTolerance t)
    (hpayoff : ∀ t,
      payoffError t ≤
        L * (transientCost t + goodMismatch t) +
          implementationCost t)
    (htransient : ∀ t,
      transientCost t =
        potential t - potential (t + 1) +
          potentialDrift t + potentialNoise t)
    (hgood : ∀ t,
      goodMismatch t ≤ goodBudget t + goodNoise t)
    (hbad : ∀ t,
      badTolerance t ≤ separatorCharge t + separatorNoise t)
    (hexternal :
      IsAsymptoticallySublinear (fun T =>
        shadowSeparatorExternalCumulativeBudget T
          potentialDrift goodBudget
          potentialNoise goodNoise separatorNoise))
    (himplementation :
      IsAsymptoticallySublinear (fun T =>
        ∑ t ∈ Finset.range T, implementationCost t))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      (T : ℝ)⁻¹ *
          (∑ t ∈ Finset.range T, payoffError t) ≤
        δ := by
  apply exists_integratedResponsePayoffErrorAverage_threshold
    L accountPotential accountCharge accountError
    accountBound accountWeight accountDirect accountReset
    potential payoffError implementationCost
    transientCost potentialDrift potentialNoise
    goodMismatch goodBudget goodNoise
    badTolerance separatorCharge separatorNoise
    haccountWeight haccountPotential haccountCharge
    haccountCoercive haccountLocal haccountError
  · intro t
    rw [hseparator_eq t]
    exact Finset.sum_nonneg fun account _ => haccountCharge t account
  · intro t
    exact (hseparator_eq t).le
  · exact hL
  · exact hpotential_nonneg
  · exact hbad_nonneg
  · exact hpayoff
  · exact htransient
  · exact hgood
  · exact hbad
  · exact hexternal
  · exact himplementation
  · exact hδ

end

end Math.Probability
