/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDebtTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport

/-!
# Returning a reset excursion by cap--Nash prefixing

A best-response reset cluster need not remain on the minimum-total-debt
fiber.  This file records the exact part of the return mechanism which does
survive that excursion.

If one coordinate has been reset to zero, prefixing by an exact Nash root
against the cluster's cap keeps that coordinate zero.  Every debt coordinate
is scaled by the same joint Continue mass.  Consequently the excursion
excess obeys the exact account

`old excess = new excess + cluster debt * root absorption`.

Moreover, relative to the original minimum point, the entire opposite-face
transfer identity is retained at the prefixed point.  Thus any absorbing
cap--Nash selection makes a strict, quantitatively charged return while
preserving the reset.  The theorem also isolates the remaining selection
seam honestly: on the face where the cap dominates every singleton reward,
the all-Continue cap--Nash root has zero charge, so existence of an exact
Nash root alone does not force return.  Off that face, every cap--Nash root
absorbs and strict return is automatic.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Total semantic debt scales exactly under a cap--Nash prefix. -/
theorem quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
    (pair : QuittingTerminalSemanticPair ι) (root : ι → PMF Bool)
    (hnash : IsεQuittingRootNash reward pair.2 0 root) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward root pair) =
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebtSum pair := by
  unfold quittingTerminalSemanticDebtSum
  simp_rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
    (reward := reward) pair root _ hnash]
  rw [Finset.mul_sum]

/-- Whenever a target has zero debt in the reset coordinate, its aggregate
opposite-face debt change is exactly its total excess over the source plus
the debt erased at the source.  No minimality hypothesis is used here. -/
theorem sum_opponent_debtChange_eq_totalChange_add_sourceDebt_of_target_zero
    (source target : QuittingTerminalSemanticPair ι) (who : ι)
    (htargetZero : quittingTerminalSemanticDebt target who = 0) :
    (∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source target other) =
      (quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source) +
        quittingTerminalSemanticDebt source who := by
  unfold quittingTerminalSemanticDebtChange
  rw [Finset.sum_sub_distrib]
  have htargetSum :
      (∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebt target other) =
        quittingTerminalSemanticDebtSum target := by
    have hsum := Finset.sum_erase_add Finset.univ
      (fun other => quittingTerminalSemanticDebt target other)
      (Finset.mem_univ who)
    change (∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebt target other) +
        quittingTerminalSemanticDebt target who =
      quittingTerminalSemanticDebtSum target at hsum
    rw [htargetZero, add_zero] at hsum
    exact hsum
  have hsourceSum :
      (∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebt source other) =
        quittingTerminalSemanticDebtSum source -
          quittingTerminalSemanticDebt source who := by
    have hsum := Finset.sum_erase_add Finset.univ
      (fun other => quittingTerminalSemanticDebt source other)
      (Finset.mem_univ who)
    change (∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebt source other) +
        quittingTerminalSemanticDebt source who =
      quittingTerminalSemanticDebtSum source at hsum
    linarith
  rw [htargetSum, hsourceSum]
  ring

/-- **Exact one-step reset-excursion return account.**

Starting from a minimum point `source`, let `target` be any attainable
semantic point whose `who` coordinate has been reset.  A cap--Nash prefix of
`target`

* remains attainable and keeps the reset coordinate zero;
* stays between the minimum and the reset cluster in total debt;
* consumes exactly `D(target) * absorption` of excursion excess; and
* retains the exact opposite-face transfer identity relative to `source`.

In particular the transferred amount is still at least the debt erased at
the source. -/
theorem capNashPrefix_resetExcursion_exact_account
    (source target : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hreset : quittingTerminalSemanticDebt target who = 0)
    (hnash : IsεQuittingRootNash reward target.2 0 root) :
    let prefixed := quittingTerminalSemanticPrefix reward root target
    prefixed ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebt prefixed who = 0 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum prefixed ∧
      quittingTerminalSemanticDebtSum prefixed ≤
        quittingTerminalSemanticDebtSum target ∧
      quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source =
        (quittingTerminalSemanticDebtSum prefixed -
            quittingTerminalSemanticDebtSum source) +
          quittingTerminalSemanticDebtSum target *
            quittingRootAbsorptionMass root ∧
      (∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source prefixed other) =
        (quittingTerminalSemanticDebtSum prefixed -
            quittingTerminalSemanticDebtSum source) +
          quittingTerminalSemanticDebt source who ∧
      quittingTerminalSemanticDebt source who ≤
        ∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source prefixed other := by
  let prefixed := quittingTerminalSemanticPrefix reward root target
  have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root target hM hreward htarget
  have hscale : quittingTerminalSemanticDebtSum prefixed =
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebtSum target := by
    exact quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) target root hnash
  have hprefixedReset : quittingTerminalSemanticDebt prefixed who = 0 := by
    rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) target root who hnash, hreset, mul_zero]
  have hsourceLe : quittingTerminalSemanticDebtSum source ≤
      quittingTerminalSemanticDebtSum prefixed :=
    hminimum prefixed hprefixed
  have htargetDebtNonneg : 0 ≤ quittingTerminalSemanticDebtSum target := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_nonneg fun player _ =>
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hM hreward htarget player
  have hcontinueLe : quittingStationaryContinueMass root ≤ 1 :=
    quittingStationaryContinueMass_le_one root
  have hprefixedLe : quittingTerminalSemanticDebtSum prefixed ≤
      quittingTerminalSemanticDebtSum target := by
    rw [hscale]
    nlinarith
  have hexcess :
      quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source =
        (quittingTerminalSemanticDebtSum prefixed -
            quittingTerminalSemanticDebtSum source) +
          quittingTerminalSemanticDebtSum target *
            quittingRootAbsorptionMass root := by
    unfold quittingRootAbsorptionMass
    rw [hscale]
    ring
  have htransfer :=
    sum_opponent_debtChange_eq_totalChange_add_sourceDebt_of_target_zero
      source prefixed who hprefixedReset
  have htransferLower : quittingTerminalSemanticDebt source who ≤
      ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source prefixed other := by
    rw [htransfer]
    linarith
  exact ⟨hprefixed, hprefixedReset, hsourceLe, hprefixedLe, hexcess,
    htransfer, htransferLower⟩

/-- Any absorbing cap--Nash selection gives strict return from a positive-debt
reset cluster, without losing the reset or its opposite-face transfer. -/
theorem capNashPrefix_resetExcursion_strict_descent_of_absorption
    (source target : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hreset : quittingTerminalSemanticDebt target who = 0)
    (htargetPositive : 0 < quittingTerminalSemanticDebtSum target)
    (hnash : IsεQuittingRootNash reward target.2 0 root)
    (habsorbs : 0 < quittingRootAbsorptionMass root) :
    let prefixed := quittingTerminalSemanticPrefix reward root target
    quittingTerminalSemanticDebtSum prefixed <
        quittingTerminalSemanticDebtSum target ∧
      quittingTerminalSemanticDebt prefixed who = 0 ∧
      quittingTerminalSemanticDebt source who ≤
        ∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source prefixed other := by
  let prefixed := quittingTerminalSemanticPrefix reward root target
  have haccount := capNashPrefix_resetExcursion_exact_account
    (reward := reward) source target root who hM hreward hminimum htarget
      hreset hnash
  have hcharge : 0 < quittingTerminalSemanticDebtSum target *
      quittingRootAbsorptionMass root := mul_pos htargetPositive habsorbs
  refine ⟨?_, haccount.2.1, haccount.2.2.2.2.2.2⟩
  linarith [haccount.2.2.2.2.1]

/-- The all-Continue prefix fixes a semantic pair as soon as its envelope
dominates every singleton reward.  This condition concerns the cap, not the
prescribed payoff. -/
theorem quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap
    (pair : QuittingTerminalSemanticPair ι)
    (hcap : ∀ player,
      reward (quittingSingletonTerminal player) player ≤ pair.2 player) :
    quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair =
      pair := by
  apply Prod.ext
  · funext player
    change quittingRootSuccessorPayoff reward pair.1
      quittingAllContinueRoot player = pair.1 player
    rw [quittingRootSuccessorPayoff_eq_endpointMix]
    simp [quittingAllContinueRoot]
  · funext player
    simp only [quittingTerminalSemanticPrefix,
      quittingRootQuitPayoff_allContinueRoot,
      quittingRootContinuePayoff_allContinueRoot,
      Function.update_self]
    exact max_eq_right (hcap player)

/-- **Cap-face dichotomy for a reset excursion.**

If some singleton reward lies strictly above the reset cluster's cap, an
exact cap--Nash root exists and every such root is nontrivial.  Selecting one
therefore gives a strict debt return while retaining both the reset and the
opposite-face transfer.  Otherwise the cap dominates all singleton rewards;
the all-Continue root is exact cap--Nash and fixes the cluster literally.

This isolates the true obstruction to automatic excursion return: not Nash
existence, but the cap-dominating singleton face. -/
theorem resetExcursion_absorbingReturn_or_allContinue_capFace
    (source target : QuittingTerminalSemanticPair ι)
    (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hreset : quittingTerminalSemanticDebt target who = 0)
    (htargetPositive : 0 < quittingTerminalSemanticDebtSum target) :
    (∃ root : ι → PMF Bool,
        IsεQuittingRootNash reward target.2 0 root ∧
        0 < quittingRootAbsorptionMass root ∧
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPrefix reward root target) <
          quittingTerminalSemanticDebtSum target ∧
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPrefix reward root target) who = 0 ∧
        quittingTerminalSemanticDebt source who ≤
          ∑ other ∈ Finset.univ.erase who,
            quittingTerminalSemanticDebtChange source
              (quittingTerminalSemanticPrefix reward root target) other) ∨
      (IsεQuittingRootNash reward target.2 0
          (quittingAllContinueRoot : ι → PMF Bool) ∧
        quittingTerminalSemanticPrefix reward quittingAllContinueRoot target =
          target) := by
  by_cases hcap : ∀ player,
      reward (quittingSingletonTerminal player) player ≤ target.2 player
  · right
    exact ⟨(isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward target.2).2 hcap,
      quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap
        (reward := reward) target hcap⟩
  · left
    obtain ⟨root, hnash⟩ :=
      exists_isZeroQuittingRootNash (reward := reward) target.2
    have hroot : root ≠
        (quittingAllContinueRoot : ι → PMF Bool) := by
      intro heq
      subst root
      exact hcap ((isZeroQuittingRootNash_allContinue_iff_singleton_le
        reward target.2).1 hnash)
    have habsorptionNonneg : 0 ≤ quittingRootAbsorptionMass root :=
      quittingRootAbsorptionMass_nonneg root
    have habsorbs : 0 < quittingRootAbsorptionMass root := by
      apply lt_of_le_of_ne habsorptionNonneg
      intro habsorptionZero
      have hcontinue : quittingStationaryContinueMass root = 1 := by
        unfold quittingRootAbsorptionMass at habsorptionZero
        linarith
      apply hroot
      funext player
      have hpure := eq_pure_false_of_quittingStationaryContinueMass_eq_one
        hcontinue player
      simpa [quittingAllContinueRoot] using hpure
    have hreturn :=
      capNashPrefix_resetExcursion_strict_descent_of_absorption
        (reward := reward) source target root who hM hreward hminimum
          htarget hreset htargetPositive hnash habsorbs
    exact ⟨root, hnash, habsorbs, hreturn.1, hreturn.2.1, hreturn.2.2⟩

/-! ## The canonical constrained stopping point -/

/-- **Reset-face minimizer and exact residual obstruction.**

The attainable reset face `d_who = 0` is compact and nonempty once a reset
cluster is available.  Total debt therefore attains a minimum on that face.
At positive global minimum debt, every exact cap--Nash root at this
reset-face minimizer is all-Continue: any absorption would preserve the reset
while strictly decreasing total debt inside the same constrained face.

Thus an arbitrary reset excursion can always be replaced by a no-worse reset
point carrying the full opposite-face transfer.  Either that point has
returned to the global minimum fiber, or the precise remaining obstruction is
an off-minimum reset point whose cap--Nash correspondence is the singleton
all-Continue root.  This constrained minimization is debt-semantic only: it
does not retain a terminal incidence law attached to the original reset
cluster. -/
theorem exists_resetFace_minimizer_with_unique_allContinue_capNash
    (source target : QuittingTerminalSemanticPair ι)
    (who : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hreset : quittingTerminalSemanticDebt target who = 0) :
    ∃ returned : QuittingTerminalSemanticPair ι,
      returned ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebt returned who = 0 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned ∧
      quittingTerminalSemanticDebtSum returned ≤
        quittingTerminalSemanticDebtSum target ∧
      (∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source returned other) =
        (quittingTerminalSemanticDebtSum returned -
            quittingTerminalSemanticDebtSum source) +
          quittingTerminalSemanticDebt source who ∧
      quittingTerminalSemanticDebt source who ≤
        ∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source returned other ∧
      (quittingTerminalSemanticDebtSum returned =
          quittingTerminalSemanticDebtSum source ∨
        quittingTerminalSemanticDebtSum source <
          quittingTerminalSemanticDebtSum returned) ∧
      IsεQuittingRootNash reward returned.2 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot returned =
        returned ∧
      ∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward returned.2 0 root →
          root = (quittingAllContinueRoot : ι → PMF Bool) := by
  let resetFace : Set (QuittingTerminalSemanticPair ι) :=
    quittingTerminalSemanticCarrier reward ∩
      {pair | quittingTerminalSemanticDebt pair who = 0}
  have hresetClosed : IsClosed
      {pair : QuittingTerminalSemanticPair ι |
        quittingTerminalSemanticDebt pair who = 0} :=
    isClosed_eq (continuous_quittingTerminalSemanticDebt who)
      continuous_const
  have hresetCompact : IsCompact resetFace :=
    (quittingTerminalSemanticCarrier_isCompact reward hM hreward).inter_right
      hresetClosed
  have hresetNonempty : resetFace.Nonempty :=
    ⟨target, htarget, hreset⟩
  obtain ⟨returned, hreturnedFace, hreturnedMin⟩ :=
    hresetCompact.exists_isMinOn hresetNonempty
      continuous_quittingTerminalSemanticDebtSum.continuousOn
  have hreturned : returned ∈ quittingTerminalSemanticCarrier reward :=
    hreturnedFace.1
  have hreturnedReset : quittingTerminalSemanticDebt returned who = 0 :=
    hreturnedFace.2
  have hsourceLe : quittingTerminalSemanticDebtSum source ≤
      quittingTerminalSemanticDebtSum returned :=
    hminimum returned hreturned
  have hreturnedPositive : 0 < quittingTerminalSemanticDebtSum returned :=
    hsourcePositive.trans_le hsourceLe
  have hreturnedLe : quittingTerminalSemanticDebtSum returned ≤
      quittingTerminalSemanticDebtSum target :=
    hreturnedMin ⟨htarget, hreset⟩
  have hallRoots : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward returned.2 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool) := by
    intro root hnash
    let prefixed := quittingTerminalSemanticPrefix reward root returned
    have hprefixed : prefixed ∈ quittingTerminalSemanticCarrier reward :=
      quittingTerminalSemanticPrefix_mem_carrier
        reward root returned hM hreward hreturned
    have hprefixedReset : quittingTerminalSemanticDebt prefixed who = 0 := by
      rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
        (reward := reward) returned root who hnash, hreturnedReset, mul_zero]
    have hminimalPrefix : quittingTerminalSemanticDebtSum returned ≤
        quittingTerminalSemanticDebtSum prefixed :=
      hreturnedMin ⟨hprefixed, hprefixedReset⟩
    have hscale : quittingTerminalSemanticDebtSum prefixed =
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum returned :=
      quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
        (reward := reward) returned root hnash
    have hcontinueLe : quittingStationaryContinueMass root ≤ 1 :=
      quittingStationaryContinueMass_le_one root
    have hcontinue : quittingStationaryContinueMass root = 1 := by
      rw [hscale] at hminimalPrefix
      nlinarith
    funext player
    have hpure := eq_pure_false_of_quittingStationaryContinueMass_eq_one
      hcontinue player
    simpa [quittingAllContinueRoot] using hpure
  obtain ⟨root, hnash⟩ :=
    exists_isZeroQuittingRootNash (reward := reward) returned.2
  have hroot := hallRoots root hnash
  have hallContinueNash : IsεQuittingRootNash reward returned.2 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    simpa [hroot] using hnash
  have hcap : ∀ player,
      reward (quittingSingletonTerminal player) player ≤ returned.2 player :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward returned.2).1 hallContinueNash
  have hfixed :=
    quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap
      (reward := reward) returned hcap
  have htransfer :=
    sum_opponent_debtChange_eq_totalChange_add_sourceDebt_of_target_zero
      source returned who hreturnedReset
  have htransferLower : quittingTerminalSemanticDebt source who ≤
      ∑ other ∈ Finset.univ.erase who,
        quittingTerminalSemanticDebtChange source returned other := by
    rw [htransfer]
    linarith
  have hfiber : quittingTerminalSemanticDebtSum returned =
        quittingTerminalSemanticDebtSum source ∨
      quittingTerminalSemanticDebtSum source <
        quittingTerminalSemanticDebtSum returned :=
    hsourceLe.eq_or_lt.imp Eq.symm id
  exact ⟨returned, hreturned, hreturnedReset, hsourceLe, hreturnedLe,
    htransfer, htransferLower, hfiber, hallContinueNash, hfixed, hallRoots⟩

/-- Quantitative selection premise for returning an off-minimum reset cluster:
the selected cap--Nash root spends all but `tolerance` of the excursion
excess.  This is precisely the extra input not supplied by finite Nash
existence on the cap-dominating singleton face, where the all-Continue
cap--Nash root spends zero. -/
def IsQuittingCapNashResetReturnSelection
    (source target : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (tolerance : ℝ) : Prop :=
  IsεQuittingRootNash reward target.2 0 root ∧
    quittingTerminalSemanticDebtSum target *
        quittingRootAbsorptionMass root ≥
      (quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source) - tolerance

/-- A cap--Nash return selection produces an attainable reset point within
the requested total-debt tolerance, retaining the full source-debt transfer
lower bound. -/
theorem exists_nearMinimum_resetPrefix_of_capNashReturnSelection
    (source target : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (who : ι) (tolerance : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (htarget : target ∈ quittingTerminalSemanticCarrier reward)
    (hreset : quittingTerminalSemanticDebt target who = 0)
    (hselection : IsQuittingCapNashResetReturnSelection
      (reward := reward) source target root tolerance) :
    ∃ returned ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebt returned who = 0 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned ∧
      quittingTerminalSemanticDebtSum returned ≤
        quittingTerminalSemanticDebtSum source + tolerance ∧
      quittingTerminalSemanticDebt source who ≤
        ∑ other ∈ Finset.univ.erase who,
          quittingTerminalSemanticDebtChange source returned other := by
  let returned := quittingTerminalSemanticPrefix reward root target
  have haccount := capNashPrefix_resetExcursion_exact_account
    (reward := reward) source target root who hM hreward hminimum htarget
      hreset hselection.1
  refine ⟨returned, haccount.1, haccount.2.1, haccount.2.2.1, ?_,
    haccount.2.2.2.2.2.2⟩
  linarith [haccount.2.2.2.2.1, hselection.2]

/-- Exact failure certificate for a proposed return tolerance.  If the
cap--Nash prefix does not enter that neighborhood of the minimum fiber, its
absorption charge necessarily falls short by the same amount. -/
theorem capNashPrefix_not_nearMinimum_forces_returnSelection_failure
    (source target : QuittingTerminalSemanticPair ι)
    (root : ι → PMF Bool) (tolerance : ℝ)
    (hnash : IsεQuittingRootNash reward target.2 0 root)
    (hfar : quittingTerminalSemanticDebtSum source + tolerance <
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPrefix reward root target)) :
    quittingTerminalSemanticDebtSum target *
        quittingRootAbsorptionMass root <
      (quittingTerminalSemanticDebtSum target -
          quittingTerminalSemanticDebtSum source) - tolerance := by
  have hscale :=
    quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) target root hnash
  unfold quittingRootAbsorptionMass
  rw [hscale] at hfar
  nlinarith

end GameTheory
