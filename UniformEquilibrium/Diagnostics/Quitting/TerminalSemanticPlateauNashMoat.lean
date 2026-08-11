/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed

/-!
# A Nash-defect moat around the canonical incidence plateau

At the canonical joint reset point selected by the debt/incidence
lexicographic argument, the all-Continue root is the unique exact cap--Nash
root.  Compactness of the finite product root simplex upgrades this qualitative
uniqueness to a uniform separation statement.

For every positive threshold `eta`, all roots whose total opponent incidence
is at least `eta` have total Nash defect bounded below by a positive moat.
The moat persists for every cap in an open neighborhood of the selected cap.
No linear modulus or explicit neighborhood radius is asserted.

The final producer couples this separation with the positive-incidence joint
semantic/law point.  It does not yet identify the nearby cap with the shifted
tail payoff at a chronological row of a realizing profile; that cap-provenance
step remains necessary before the moat becomes a legal stage-deviation charge.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability Math.PMFProduct
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Root coalition mass is continuous in simplex coordinates. -/
theorem continuous_quittingRootCoalitionMass_simplex
    (coalition : Finset ι) :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingRootCoalitionMass (quittingRootOfSimplex root) coalition) := by
  unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
    quittingRootQuitRates
  apply (continuous_finsetProd _ fun player _ => ?_).mul
    (continuous_finsetProd _ fun player _ => ?_)
  · simp only [quittingRootOfSimplex_apply_toReal]
    have hplayer : Continuous (fun root : QuittingRootSimplex ι =>
        (root player : Bool → ℝ)) :=
      continuous_subtype_val.comp (continuous_apply player)
    exact (continuous_apply true).comp hplayer
  · simp only [quittingRootOfSimplex_apply_toReal]
    have hplayer : Continuous (fun root : QuittingRootSimplex ι =>
        (root player : Bool → ℝ)) :=
      continuous_subtype_val.comp (continuous_apply player)
    exact continuous_const.sub ((continuous_apply true).comp hplayer)

/-- Total opponent incidence of a root is continuous in simplex coordinates. -/
theorem continuous_quittingRootTotalOpponentIncidenceMass_simplex
    (owner : ι) :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingRootTotalOpponentIncidenceMass owner
        (quittingRootOfSimplex root)) := by
  unfold quittingRootTotalOpponentIncidenceMass
    quittingRootOpponentIncidenceMass
  exact continuous_finsetSum _ fun _ _ =>
    continuous_finsetSum _ fun terminal _ =>
      continuous_quittingRootCoalitionMass_simplex terminal.val

/-- One-coordinate Nash defect is jointly continuous in the cap and simplex
root. -/
theorem continuous_quittingRootCoordinateNashDefect_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootCoordinateNashDefect reward point.1
        (quittingRootOfSimplex point.2) who) := by
  unfold quittingRootCoordinateNashDefect
  exact ((continuous_quittingRootQuitPayoff_simplex reward who).max
      (continuous_quittingRootContinuePayoff_simplex reward who)).sub
    ((continuous_apply who).comp
      (continuous_quittingRootSuccessorPayoff_simplex reward))

/-- Total Nash defect is jointly continuous in the cap and simplex root. -/
theorem continuous_quittingRootTotalNashDefect_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootTotalNashDefect reward point.1
        (quittingRootOfSimplex point.2)) := by
  unfold quittingRootTotalNashDefect
  exact continuous_finsetSum _ fun who _ =>
    continuous_quittingRootCoordinateNashDefect_simplex reward who

/-- Zero total Nash defect is exactly exact root Nash. -/
theorem isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
    (tail : Payoff ι) (root : ι → PMF Bool) :
    IsεQuittingRootNash reward tail 0 root ↔
      quittingRootTotalNashDefect reward tail root = 0 := by
  rw [isZeroQuittingRootNash_iff_coordinateNashDefect_eq_zero]
  constructor
  · intro hzero
    unfold quittingRootTotalNashDefect
    simp_rw [hzero]
    simp
  · intro hsum who
    have hcoordinateNonneg :=
      quittingRootCoordinateNashDefect_nonneg reward tail root who
    have hcoordinateLe :
        quittingRootCoordinateNashDefect reward tail root who ≤
          quittingRootTotalNashDefect reward tail root := by
      unfold quittingRootTotalNashDefect
      exact Finset.single_le_sum
        (f := fun player =>
          quittingRootCoordinateNashDefect reward tail root player)
        (fun player _ =>
          quittingRootCoordinateNashDefect_nonneg reward tail root player)
        (Finset.mem_univ who)
    rw [hsum] at hcoordinateLe
    exact le_antisymm hcoordinateLe hcoordinateNonneg

/-- The all-Continue root has zero total opponent incidence. -/
@[simp] theorem quittingRootTotalOpponentIncidenceMass_allContinueRoot
    (owner : ι) :
    quittingRootTotalOpponentIncidenceMass owner
      (quittingAllContinueRoot : ι → PMF Bool) = 0 := by
  unfold quittingRootTotalOpponentIncidenceMass
    quittingRootOpponentIncidenceMass
  apply Finset.sum_eq_zero
  intro other _
  apply Finset.sum_eq_zero
  intro terminal _
  unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
    quittingRootQuitRates quittingAllContinueRoot
  obtain ⟨member, hmember⟩ := terminal.property
  have hzero : ∏ player ∈ terminal.val,
      ((PMF.pure false : PMF Bool) true).toReal = 0 := by
    apply Finset.prod_eq_zero hmember
    simp
  rw [hzero, zero_mul]

/-- **Fixed-cap Nash-defect moat.**  If all exact cap--Nash roots are
all-Continue, every root with a fixed positive amount of total opponent
incidence pays a uniformly positive total Nash defect. -/
theorem exists_totalNashDefect_moat_of_unique_allContinue
    (cap : Payoff ι) (owner : ι) (eta : ℝ)
    (heta : 0 < eta)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ root : QuittingRootSimplex ι,
        eta ≤ quittingRootTotalOpponentIncidenceMass owner
          (quittingRootOfSimplex root) →
        moat ≤ quittingRootTotalNashDefect reward cap
          (quittingRootOfSimplex root) := by
  let highIncidence : Set (QuittingRootSimplex ι) :=
    {root | eta ≤ quittingRootTotalOpponentIncidenceMass owner
      (quittingRootOfSimplex root)}
  have hhighClosed : IsClosed highIncidence :=
    isClosed_Ici.preimage
      (continuous_quittingRootTotalOpponentIncidenceMass_simplex owner)
  have hhighCompact : IsCompact highIncidence := hhighClosed.isCompact
  by_cases hhighNonempty : highIncidence.Nonempty
  · have hdefectContinuous : Continuous (fun root : QuittingRootSimplex ι =>
        quittingRootTotalNashDefect reward cap
          (quittingRootOfSimplex root)) := by
      change Continuous
        ((fun point : Payoff ι × QuittingRootSimplex ι =>
            quittingRootTotalNashDefect reward point.1
              (quittingRootOfSimplex point.2)) ∘
          fun root : QuittingRootSimplex ι => (cap, root))
      exact (continuous_quittingRootTotalNashDefect_simplex reward).comp
        (continuous_const.prodMk continuous_id)
    obtain ⟨selected, hselectedHigh, hselectedMin⟩ :=
      hhighCompact.exists_isMinOn hhighNonempty
        hdefectContinuous.continuousOn
    have hselectedNonneg : 0 ≤ quittingRootTotalNashDefect reward cap
        (quittingRootOfSimplex selected) :=
      quittingRootTotalNashDefect_nonneg reward cap
        (quittingRootOfSimplex selected)
    have hselectedPositive : 0 < quittingRootTotalNashDefect reward cap
        (quittingRootOfSimplex selected) := by
      apply lt_of_le_of_ne hselectedNonneg
      intro hzero
      have hnash : IsεQuittingRootNash reward cap 0
          (quittingRootOfSimplex selected) :=
        (isZeroQuittingRootNash_iff_totalNashDefect_eq_zero
          (reward := reward) cap (quittingRootOfSimplex selected)).2 hzero.symm
      have hroot := hunique (quittingRootOfSimplex selected) hnash
      have hincidenceZero :
          quittingRootTotalOpponentIncidenceMass owner
            (quittingRootOfSimplex selected) = 0 := by
        rw [hroot]
        exact quittingRootTotalOpponentIncidenceMass_allContinueRoot owner
      have hselectedEta : eta ≤ quittingRootTotalOpponentIncidenceMass owner
          (quittingRootOfSimplex selected) := hselectedHigh
      rw [hincidenceZero] at hselectedEta
      linarith
    exact ⟨quittingRootTotalNashDefect reward cap
        (quittingRootOfSimplex selected), hselectedPositive,
      fun root hroot => hselectedMin hroot⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro root hroot
    exact False.elim (hhighNonempty ⟨root, hroot⟩)

/-- **Robust Nash-defect moat.**  The fixed-cap moat persists on an open
neighborhood of the cap.  The proof uses closed projection along the compact
root simplex; it supplies no linear modulus or explicit radius. -/
theorem exists_eventually_totalNashDefect_moat_of_unique_allContinue
    (cap : Payoff ι) (owner : ι) (eta : ℝ)
    (heta : 0 < eta)
    (hunique : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward cap 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool)) :
    ∃ moat : ℝ, 0 < moat ∧
      ∀ᶠ nearbyCap in 𝓝 cap,
        ∀ root : QuittingRootSimplex ι,
          eta ≤ quittingRootTotalOpponentIncidenceMass owner
            (quittingRootOfSimplex root) →
          moat ≤ quittingRootTotalNashDefect reward nearbyCap
            (quittingRootOfSimplex root) := by
  obtain ⟨fixedMoat, hfixedMoat, hfixed⟩ :=
    exists_totalNashDefect_moat_of_unique_allContinue
      (reward := reward) cap owner eta heta hunique
  let moat := fixedMoat / 2
  let bad : Set (Payoff ι × QuittingRootSimplex ι) :=
    {point | eta ≤ quittingRootTotalOpponentIncidenceMass owner
          (quittingRootOfSimplex point.2) ∧
      quittingRootTotalNashDefect reward point.1
          (quittingRootOfSimplex point.2) ≤ moat}
  have hbadClosed : IsClosed bad := by
    exact (isClosed_le continuous_const
      ((continuous_quittingRootTotalOpponentIncidenceMass_simplex owner).comp
        continuous_snd)).inter
      (isClosed_le (continuous_quittingRootTotalNashDefect_simplex reward)
        continuous_const)
  have hprojectionClosed : IsClosed (Prod.fst '' bad) :=
    isClosedMap_fst_of_compactSpace bad hbadClosed
  have hcapNotBad : cap ∉ Prod.fst '' bad := by
    rintro ⟨⟨_nearbyCap, root⟩, hrootBad, rfl⟩
    have hlower := hfixed root hrootBad.1
    have hupper : quittingRootTotalNashDefect reward _nearbyCap
        (quittingRootOfSimplex root) ≤ fixedMoat / 2 := by
      simpa only [moat] using hrootBad.2
    linarith
  refine ⟨moat, by dsimp only [moat]; linarith, ?_⟩
  filter_upwards [hprojectionClosed.isOpen_compl.mem_nhds hcapNotBad] with
      nearbyCap hnear root hrootIncidence
  apply le_of_not_gt
  intro hdefectSmall
  exact hnear ⟨(nearbyCap, root), ⟨hrootIncidence, hdefectSmall.le⟩, rfl⟩

/-- The canonical reset-face plateau carries a robust Nash-defect moat at
every positive total-opponent-incidence scale. -/
theorem exists_resetFace_positiveIncidence_robustNashMoat
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (owner : ι) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (htarget : (target, mass) ∈
      quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt target owner = 0)
    (hincidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner mass) :
    ∃ returned : QuittingTerminalSemanticLawPoint ι,
      returned ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt returned.1 owner = 0 ∧
      0 < quittingTerminalTotalOpponentIncidenceMass owner returned.2 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned.1 ∧
      (∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward returned.1.2 0 root →
          root = (quittingAllContinueRoot : ι → PMF Bool)) ∧
      ∀ eta, 0 < eta →
        ∃ moat : ℝ, 0 < moat ∧
          ∀ᶠ nearbyCap in 𝓝 returned.1.2,
            ∀ root : QuittingRootSimplex ι,
              eta ≤ quittingRootTotalOpponentIncidenceMass owner
                (quittingRootOfSimplex root) →
              moat ≤ quittingRootTotalNashDefect reward nearbyCap
                (quittingRootOfSimplex root) := by
  obtain ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
      hsourceLe, _hallContinueNash, _hfixed, hallRoots⟩ :=
    exists_resetFace_positiveTotalIncidence_allContinueCapPlateau
      source target mass owner hM hreward hminimum hsourcePositive
        htarget hreset hincidence
  refine ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
    hsourceLe, hallRoots, ?_⟩
  intro eta heta
  exact exists_eventually_totalNashDefect_moat_of_unique_allContinue
    (reward := reward) returned.1.2 owner eta heta hallRoots

end GameTheory
