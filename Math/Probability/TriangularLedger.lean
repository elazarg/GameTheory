/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Math.Probability.SublinearLedger

/-!
# Weighted reset ledgers

A family of local drift accounts may allow one account to increase when
another account pays a reset charge. Such inequalities are sound only when
the reset dependencies admit positive scalarization weights.

This file proves the finite-horizon algebra behind that scalarization. The
coercivity hypothesis is exactly the weighted small-gain condition. Strictly
triangular reset dependencies admit such weights by backward substitution;
cyclic systems require the same condition as an additional hypothesis.
-/

namespace Math.Probability

noncomputable section

open scoped BigOperators
open Filter

/-- Rearrange the reset part of a weighted family of drift inequalities by
the charge being paid. -/
theorem sum_weight_mul_resetBalance
    {Account : Type*} [Fintype Account]
    (weight direct charge : Account → ℝ)
    (reset : Account → Account → ℝ) :
    (∑ account,
        weight account *
          (direct account * charge account -
            ∑ payer, reset account payer * charge payer)) =
      ∑ payer,
        (weight payer * direct payer -
          ∑ account, weight account * reset account payer) *
            charge payer := by
  classical
  calc
    (∑ account,
        weight account *
          (direct account * charge account -
            ∑ payer, reset account payer * charge payer)) =
        (∑ account,
          weight account * direct account * charge account) -
          ∑ account, ∑ payer,
            weight account * reset account payer * charge payer := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro account _
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro payer _
        ring
    _ =
        (∑ payer,
          weight payer * direct payer * charge payer) -
          ∑ payer, ∑ account,
            weight account * reset account payer * charge payer := by
      rw [Finset.sum_comm]
    _ =
        ∑ payer,
          (weight payer * direct payer -
            ∑ account, weight account * reset account payer) *
              charge payer := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro payer _
      rw [sub_mul, Finset.sum_mul]

/-- Strictly triangular nonnegative reset dependencies admit positive
scalarization weights with any prescribed positive residual coefficient.

The order on `Fin accountCount` is the priority order: a reset of `account`
may be paid only by a strictly higher-priority `payer < account`. The proof
is backward substitution from the lowest-priority account. -/
theorem exists_pos_weight_resetResidual_eq_of_strictTriangular
    (accountCount : ℕ)
    (direct target : Fin accountCount → ℝ)
    (reset : Fin accountCount → Fin accountCount → ℝ)
    (hdirect : ∀ account, 0 < direct account)
    (htarget : ∀ account, 0 < target account)
    (hreset_nonneg : ∀ account payer, 0 ≤ reset account payer)
    (hreset_triangular : ∀ account payer,
      ¬payer < account → reset account payer = 0) :
    ∃ weight : Fin accountCount → ℝ,
      (∀ account, 0 < weight account) ∧
      ∀ payer,
        weight payer * direct payer -
            ∑ account, weight account * reset account payer =
          target payer := by
  induction accountCount with
  | zero =>
      refine ⟨fun account => Fin.elim0 account, ?_, ?_⟩
      · intro account
        exact Fin.elim0 account
      · intro payer
        exact Fin.elim0 payer
  | succ n ih =>
      let last : Fin (n + 1) := Fin.last n
      let lastWeight : ℝ := target last / direct last
      let restrictedDirect : Fin n → ℝ :=
        fun account => direct account.castSucc
      let restrictedReset : Fin n → Fin n → ℝ :=
        fun account payer => reset account.castSucc payer.castSucc
      let restrictedTarget : Fin n → ℝ :=
        fun payer =>
          target payer.castSucc +
            lastWeight * reset last payer.castSucc
      have hlastWeight : 0 < lastWeight := by
        exact div_pos (htarget last) (hdirect last)
      have hrestrictedDirect :
          ∀ account, 0 < restrictedDirect account := by
        intro account
        exact hdirect account.castSucc
      have hrestrictedTarget :
          ∀ payer, 0 < restrictedTarget payer := by
        intro payer
        exact add_pos_of_pos_of_nonneg
          (htarget payer.castSucc)
          (mul_nonneg hlastWeight.le
            (hreset_nonneg last payer.castSucc))
      have hrestrictedResetNonneg :
          ∀ account payer, 0 ≤ restrictedReset account payer := by
        intro account payer
        exact hreset_nonneg account.castSucc payer.castSucc
      have hrestrictedResetTriangular :
          ∀ account payer,
            ¬payer < account → restrictedReset account payer = 0 := by
        intro account payer hnot
        apply hreset_triangular account.castSucc payer.castSucc
        simpa using hnot
      obtain ⟨restrictedWeight, hrestrictedWeight,
          hrestrictedResidual⟩ :=
        ih restrictedDirect restrictedTarget restrictedReset
          hrestrictedDirect hrestrictedTarget hrestrictedResetNonneg
          hrestrictedResetTriangular
      let weight : Fin (n + 1) → ℝ :=
        Fin.snoc restrictedWeight lastWeight
      refine ⟨weight, ?_, ?_⟩
      · intro account
        refine Fin.lastCases ?_ (fun index => ?_) account
        · simpa [weight] using hlastWeight
        · simpa [weight] using hrestrictedWeight index
      · intro payer
        refine Fin.lastCases ?_ (fun index => ?_) payer
        · have hresetLast :
              ∑ account : Fin (n + 1),
                  weight account * reset account last =
                0 := by
            apply Finset.sum_eq_zero
            intro account _
            rw [hreset_triangular account last
              (not_lt_of_ge (Fin.le_last account)), mul_zero]
          rw [hresetLast, sub_zero]
          rw [show weight last = lastWeight by
            simp [weight, last]]
          exact div_mul_cancel₀ (target last) (ne_of_gt (hdirect last))
        · rw [Fin.sum_univ_castSucc]
          simp only [weight, Fin.snoc_castSucc, Fin.snoc_last]
          have hrestricted := hrestrictedResidual index
          change
            restrictedWeight index * direct index.castSucc -
                ((∑ account : Fin n,
                    restrictedWeight account *
                      reset account.castSucc index.castSucc) +
                  lastWeight * reset last index.castSucc) =
              target index.castSucc
          change
            restrictedWeight index * restrictedDirect index -
                ∑ account,
                  restrictedWeight account *
                    restrictedReset account index =
              restrictedTarget index at hrestricted
          dsimp only [restrictedTarget] at hrestricted
          linarith

/-- Unit-residual form of the triangular-weight construction, matching the
coercivity premise of the finite-horizon ledger. -/
theorem exists_pos_weight_one_le_resetResidual_of_strictTriangular
    (accountCount : ℕ)
    (direct : Fin accountCount → ℝ)
    (reset : Fin accountCount → Fin accountCount → ℝ)
    (hdirect : ∀ account, 0 < direct account)
    (hreset_nonneg : ∀ account payer, 0 ≤ reset account payer)
    (hreset_triangular : ∀ account payer,
      ¬payer < account → reset account payer = 0) :
    ∃ weight : Fin accountCount → ℝ,
      (∀ account, 0 < weight account) ∧
      ∀ payer,
        1 ≤ weight payer * direct payer -
          ∑ account, weight account * reset account payer := by
  obtain ⟨weight, hweight, hresidual⟩ :=
    exists_pos_weight_resetResidual_eq_of_strictTriangular
      accountCount direct (fun _ => 1) reset hdirect
      (fun _ => by norm_num) hreset_nonneg hreset_triangular
  exact ⟨weight, hweight, fun payer => (hresidual payer).ge⟩

/-- One round of componentwise drift inequalities scalarizes to one charge
bound.

`reset account payer` is the amount credited to `account` when `payer`
incurs one unit of charge. The coercivity premise says that after weighting
all accounts, every charge retains coefficient at least one. -/
theorem chargeSum_le_weightedPotentialDrop_add_error
    {Account : Type*} [Fintype Account]
    (potential nextPotential charge error : Account → ℝ)
    (weight direct : Account → ℝ)
    (reset : Account → Account → ℝ)
    (hweight : ∀ account, 0 ≤ weight account)
    (hcharge : ∀ account, 0 ≤ charge account)
    (hcoercive : ∀ payer,
      1 ≤ weight payer * direct payer -
        ∑ account, weight account * reset account payer)
    (hlocal : ∀ account,
      nextPotential account - potential account +
          direct account * charge account -
          ∑ payer, reset account payer * charge payer ≤
        error account) :
    ∑ account, charge account ≤
      (∑ account,
        weight account *
          (potential account - nextPotential account)) +
        ∑ account, weight account * error account := by
  classical
  have hweighted :
      (∑ account,
        weight account *
          (nextPotential account - potential account +
            direct account * charge account -
            ∑ payer, reset account payer * charge payer)) ≤
        ∑ account, weight account * error account := by
    apply Finset.sum_le_sum
    intro account _
    exact mul_le_mul_of_nonneg_left (hlocal account) (hweight account)
  have hreset :
      (∑ account,
        weight account *
          (direct account * charge account -
            ∑ payer, reset account payer * charge payer)) =
        ∑ payer,
          (weight payer * direct payer -
            ∑ account, weight account * reset account payer) *
              charge payer :=
    sum_weight_mul_resetBalance weight direct charge reset
  have hcoerciveSum :
      (∑ payer, charge payer) ≤
        ∑ payer,
          (weight payer * direct payer -
            ∑ account, weight account * reset account payer) *
              charge payer := by
    apply Finset.sum_le_sum
    intro payer _
    have := mul_le_mul_of_nonneg_right
      (hcoercive payer) (hcharge payer)
    simpa only [one_mul] using this
  rw [show
      (∑ account,
        weight account *
          (nextPotential account - potential account +
            direct account * charge account -
            ∑ payer, reset account payer * charge payer)) =
        (∑ account,
          weight account *
            (nextPotential account - potential account)) +
          ∑ account,
            weight account *
              (direct account * charge account -
                ∑ payer, reset account payer * charge payer) by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro account _
      ring] at hweighted
  rw [hreset] at hweighted
  calc
    (∑ account, charge account) ≤
        ∑ payer,
          (weight payer * direct payer -
            ∑ account, weight account * reset account payer) *
              charge payer :=
      hcoerciveSum
    _ ≤
        -(∑ account,
          weight account *
            (nextPotential account - potential account)) +
          ∑ account, weight account * error account := by
      linarith
    _ =
        (∑ account,
          weight account *
            (potential account - nextPotential account)) +
          ∑ account, weight account * error account := by
      congr 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro account _
      ring

/-- Finite-horizon weighted reset ledger.

The theorem is pathwise. Probabilistic applications may instantiate its
entries with conditional expectations or already-integrated quantities. -/
theorem sum_charge_le_weightedPotentialDrop_add_error
    {Account : Type*} [Fintype Account]
    (T : ℕ)
    (potential charge error : ℕ → Account → ℝ)
    (weight direct : Account → ℝ)
    (reset : Account → Account → ℝ)
    (hweight : ∀ account, 0 ≤ weight account)
    (hcharge : ∀ t ∈ Finset.range T, ∀ account,
      0 ≤ charge t account)
    (hcoercive : ∀ payer,
      1 ≤ weight payer * direct payer -
        ∑ account, weight account * reset account payer)
    (hlocal : ∀ t ∈ Finset.range T, ∀ account,
      potential (t + 1) account - potential t account +
          direct account * charge t account -
          ∑ payer, reset account payer * charge t payer ≤
        error t account) :
    (∑ t ∈ Finset.range T, ∑ account, charge t account) ≤
      (∑ account,
        weight account *
          (potential 0 account - potential T account)) +
        ∑ t ∈ Finset.range T,
          ∑ account, weight account * error t account := by
  have hround : ∀ t ∈ Finset.range T,
      (∑ account, charge t account) ≤
        (∑ account,
          weight account *
            (potential t account - potential (t + 1) account)) +
          ∑ account, weight account * error t account := by
    intro t ht
    exact chargeSum_le_weightedPotentialDrop_add_error
      (potential t) (potential (t + 1)) (charge t) (error t)
      weight direct reset hweight (hcharge t ht) hcoercive
      (hlocal t ht)
  calc
    (∑ t ∈ Finset.range T, ∑ account, charge t account) ≤
        ∑ t ∈ Finset.range T,
          ((∑ account,
            weight account *
              (potential t account - potential (t + 1) account)) +
            ∑ account, weight account * error t account) :=
      Finset.sum_le_sum hround
    _ =
        (∑ account,
          weight account *
            (potential 0 account - potential T account)) +
          ∑ t ∈ Finset.range T,
            ∑ account, weight account * error t account := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro account _
      rw [← Finset.mul_sum, Finset.sum_range_sub']

/-- A bounded weighted reset ledger with sublinear cumulative error gives one
common horizon threshold after which the average total charge is small. -/
theorem exists_weightedResetChargeAverage_threshold
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
          ∑ account, weight account * error t account))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ T₀ : ℕ, ∀ T, T₀ ≤ T →
      (T : ℝ)⁻¹ *
          (∑ t ∈ Finset.range T, ∑ account, charge t account) ≤
        δ := by
  let initialBound : ℝ :=
    2 * ∑ account, weight account * bound account
  let upper : ℕ → ℝ := fun T =>
    initialBound +
      ∑ t ∈ Finset.range T,
        ∑ account, weight account * error t account
  have hupper : IsAsymptoticallySublinear upper := by
    exact
      (IsAsymptoticallySublinear.const initialBound).add herror
  obtain ⟨T₀, hT₀⟩ :=
    eventually_atTop.mp (hupper.eventually_average_le hδ)
  refine ⟨T₀, fun T hT => ?_⟩
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
  have hfinite :
      (∑ t ∈ Finset.range T, ∑ account, charge t account) ≤
        upper T := by
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
  exact
    (mul_le_mul_of_nonneg_left hfinite
      (inv_nonneg.mpr (Nat.cast_nonneg T))).trans
      (hT₀ T hT)

end

end Math.Probability
