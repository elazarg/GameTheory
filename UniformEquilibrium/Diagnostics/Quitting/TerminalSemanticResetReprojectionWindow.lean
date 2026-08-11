/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionGerm
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge

/-!
# Executable windows at an unbounded reset reprojection

The compact reset-reprojection germ can be chosen inside the dense set of
literal executable profiles.  Its positive limiting opponent incidence then
has a fixed coalition label and a finite (profile-dependent) chronological
window carrying a uniform amount of that coalition.

The local Bellman datum is also genuinely matched.  For an arbitrary profile,
not only for a pure-Continue deviation, joint survival times the shifted
best-response debt is bounded by the initial debt.  Consequently every marked
live-row coordinate defect, after weighting by actual survival and normalizing
by the surface-tension scale, vanishes along the executable germ.

The window endpoint is allowed to drift.  No bounded common cutoff follows
from terminal-law compactness: the retained law records the total coalition
mass but forgets its temporal tightness.
-/

noncomputable section

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open scoped Topology

variable {X : Type} [TopologicalSpace X] [FirstCountableTopology X]

/-! ## Dense normalized germs -/

/-- A compact normalized contact germ may be chosen in any dense generating
subset of its carrier.  Strict obstruction inequalities survive passage from
the closed carrier to the dense subset before compactness is applied. -/
theorem exists_normalized_contact_germ_in_dense_of_compact
    (actual carrier : Set X) (hcompact : IsCompact carrier)
    (hactual : actual ⊆ carrier) (hdense : carrier ⊆ closure actual)
    (face tension : X → ℝ)
    (hfaceContinuous : Continuous face)
    (htensionContinuous : Continuous tension)
    (hfaceNonneg : ∀ point ∈ carrier, 0 ≤ face point)
    (hsupport : ∀ point ∈ carrier, face point = 0 → tension point ≤ 0)
    (hobstruction : ∀ penalty, 0 ≤ penalty →
      ∃ point ∈ carrier,
        0 < face point ∧ 0 < tension point ∧
          penalty * face point < tension point) :
    ∃ contact : X, ∃ path : ℕ → X,
      contact ∈ carrier ∧
      (∀ n, path n ∈ actual) ∧
      Tendsto path atTop (nhds contact) ∧
      (∀ n, 0 < face (path n)) ∧
      (∀ n, 0 < tension (path n)) ∧
      Tendsto (fun n ↦ face (path n) / tension (path n))
        atTop (nhds 0) ∧
      face contact = 0 ∧ tension contact = 0 := by
  classical
  have hactualObstruction : ∀ penalty, 0 ≤ penalty →
      ∃ point ∈ actual,
        0 < face point ∧ 0 < tension point ∧
          penalty * face point < tension point := by
    intro penalty hpenalty
    obtain ⟨point, hpointCarrier, hpointFace, hpointTension,
        hpointRatio⟩ := hobstruction penalty hpenalty
    let neighborhood : Set X :=
      {candidate | 0 < face candidate ∧ 0 < tension candidate ∧
        penalty * face candidate < tension candidate}
    have hopen : IsOpen neighborhood := by
      dsimp only [neighborhood]
      change IsOpen ({candidate | 0 < face candidate} ∩
        ({candidate | 0 < tension candidate} ∩
          {candidate | penalty * face candidate < tension candidate}))
      have hzero : Continuous (fun _ : X => (0 : ℝ)) := continuous_const
      have hpenalty : Continuous (fun _ : X => penalty) := continuous_const
      exact (isOpen_lt hzero hfaceContinuous).inter
        ((isOpen_lt hzero htensionContinuous).inter
          (isOpen_lt (hpenalty.mul hfaceContinuous) htensionContinuous))
    have hpointNeighborhood : point ∈ neighborhood :=
      ⟨hpointFace, hpointTension, hpointRatio⟩
    obtain ⟨witness, hwitnessNeighborhood, hwitnessActual⟩ :=
      mem_closure_iff.mp (hdense hpointCarrier) neighborhood hopen
        hpointNeighborhood
    exact ⟨witness, hwitnessActual, hwitnessNeighborhood⟩
  choose witness hwitnessActual hwitnessFace hwitnessTension
      hwitnessRatio using fun n : ℕ ↦
    hactualObstruction ((n : ℝ) + 1) (by positivity)
  have hwitnessCarrier : ∀ n, witness n ∈ carrier :=
    fun n ↦ hactual (hwitnessActual n)
  obtain ⟨contact, hcontact, subseq, hsubseq, hpath⟩ :=
    hcompact.tendsto_subseq hwitnessCarrier
  let path : ℕ → X := fun n ↦ witness (subseq n)
  have hpathActual : ∀ n, path n ∈ actual :=
    fun n ↦ hwitnessActual (subseq n)
  have hpathFace : ∀ n, 0 < face (path n) :=
    fun n ↦ hwitnessFace (subseq n)
  have hpathTension : ∀ n, 0 < tension (path n) :=
    fun n ↦ hwitnessTension (subseq n)
  have hratioUpper : ∀ n,
      face (path n) / tension (path n) ≤
        1 / ((subseq n : ℝ) + 1) := by
    intro n
    have hscale : 0 < (subseq n : ℝ) + 1 := by positivity
    have hraw := hwitnessRatio (subseq n)
    have hdiv : face (path n) <
        tension (path n) / ((subseq n : ℝ) + 1) := by
      apply (lt_div_iff₀ hscale).2
      simpa [path, mul_comm] using hraw
    have hquotient : face (path n) / tension (path n) <
        1 / ((subseq n : ℝ) + 1) := by
      apply (div_lt_iff₀ (hpathTension n)).2
      calc
        face (path n) <
            tension (path n) / ((subseq n : ℝ) + 1) := hdiv
        _ = (1 / ((subseq n : ℝ) + 1)) * tension (path n) := by
          ring
    exact hquotient.le
  have hratio : Tendsto
      (fun n ↦ face (path n) / tension (path n)) atTop (nhds 0) := by
    have hupper : Tendsto (fun n : ℕ ↦
        1 / ((subseq n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hsubseq.tendsto_atTop
    exact squeeze_zero
      (fun n ↦ div_nonneg
        (hfaceNonneg (path n) (hactual (hpathActual n)))
        (hpathTension n).le)
      hratioUpper hupper
  have htensionLimit : Tendsto (fun n ↦ tension (path n))
      atTop (nhds (tension contact)) :=
    htensionContinuous.continuousAt.tendsto.comp hpath
  have hfaceZeroLimit : Tendsto (fun n ↦ face (path n))
      atTop (nhds 0) := by
    have hproduct := hratio.mul htensionLimit
    convert hproduct using 1
    · funext n
      field_simp [(hpathTension n).ne']
    · simp
  have hfaceContact : face contact = 0 := by
    have hfaceLimit : Tendsto (fun n ↦ face (path n))
        atTop (nhds (face contact)) :=
      hfaceContinuous.continuousAt.tendsto.comp hpath
    exact tendsto_nhds_unique hfaceLimit hfaceZeroLimit
  have htensionNonneg : 0 ≤ tension contact :=
    le_of_tendsto_of_tendsto tendsto_const_nhds htensionLimit
      (Eventually.of_forall fun n ↦ (hpathTension n).le)
  have htensionContact : tension contact = 0 :=
    le_antisymm (hsupport contact hcontact hfaceContact) htensionNonneg
  exact ⟨contact, path, hcontact, hpathActual, hpath, hpathFace,
    hpathTension, hratio, hfaceContact, htensionContact⟩

/-! ## Arbitrary-profile survival transport -/

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- Joint survival, rather than opponent survival, transports debt through an
arbitrary mixed owner row. -/
theorem stationaryContinueMass_mul_debt_le_terminalSemanticDebt_prefix
    (pair : QuittingTerminalSemanticPair iota)
    (root : iota → PMF Bool) (who : iota) :
    quittingStationaryContinueMass root *
        quittingTerminalSemanticDebt pair who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPrefix reward root pair) who := by
  let debt := quittingTerminalSemanticDebt pair who
  let quitValue := quittingRootQuitPayoff reward pair.1 root who
  let continueValue := quittingRootContinuePayoff reward pair.1 root who
  let successor := quittingRootSuccessorPayoff reward pair.1 root who
  let opponentContinue := quittingRootOpponentContinueMass root who
  have hownerSum := quittingRoot_continueProbability_add_quitProbability root who
  have hopponentNonneg : 0 ≤ opponentContinue :=
    quittingRootOpponentContinueMass_nonneg root who
  have hquitNonneg : 0 ≤ (root who true).toReal := ENNReal.toReal_nonneg
  have hcontinueNonneg : 0 ≤ (root who false).toReal := ENNReal.toReal_nonneg
  have hstationary : quittingStationaryContinueMass root =
      (root who false).toReal * opponentContinue := by
    dsimp only [opponentContinue]
    rw [quittingRootOpponentContinueMass]
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    rw [show (Finset.univ : Finset iota) =
        insert who (Finset.univ.erase who) by simp]
    rw [Finset.prod_insert (by simp)]
    change (root who false).toReal * ∏ x ∈ Finset.univ.erase who,
        (root x false).toReal = _
    rw [quittingStationaryContinueMass_eq_prod_continueProbability]
    rw [show (Finset.univ : Finset iota) =
        insert who (Finset.univ.erase who) by simp]
    rw [Finset.prod_insert (by simp)]
    simp only [Function.update_self]
    rw [show ((PMF.pure false : PMF Bool) false).toReal = 1 by simp,
      one_mul]
    apply congrArg ((root who false).toReal * ·)
    have herase : (insert who (Finset.univ.erase who)).erase who =
        (Finset.univ : Finset iota).erase who := by
      ext player
      simp
    rw [herase]
    apply Finset.prod_congr rfl
    intro player hplayer
    rw [Function.update_of_ne]
    exact (Finset.mem_erase.mp hplayer).1
  have henvelope : pair.2 who = pair.1 who + debt := by
    dsimp [debt, quittingTerminalSemanticDebt]
    ring
  have hcontinueEnvelope :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        continueValue + opponentContinue * debt := by
    rw [henvelope, quittingRootContinuePayoff_update_add]
  have hsuccessorMix : successor =
      (root who true).toReal * quitValue +
        (root who false).toReal * continueValue := by
    dsimp only [successor, quitValue, continueValue]
    exact quittingRootSuccessorPayoff_eq_endpointMix reward pair.1 root who
  unfold quittingTerminalSemanticDebt quittingTerminalSemanticPrefix
  dsimp only
  rw [hcontinueEnvelope]
  change quittingStationaryContinueMass root * debt ≤
    max quitValue (continueValue + opponentContinue * debt) - successor
  rw [hstationary, hsuccessorMix]
  have hconvex :
      (root who true).toReal * quitValue +
          (root who false).toReal *
            (continueValue + opponentContinue * debt) ≤
        max quitValue (continueValue + opponentContinue * debt) := by
    calc
      (root who true).toReal * quitValue +
          (root who false).toReal *
            (continueValue + opponentContinue * debt) ≤
        (root who true).toReal *
            max quitValue (continueValue + opponentContinue * debt) +
          (root who false).toReal *
            max quitValue (continueValue + opponentContinue * debt) :=
        add_le_add
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hquitNonneg)
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hcontinueNonneg)
      _ = max quitValue (continueValue + opponentContinue * debt) := by
        rw [← add_mul]
        have hsum : (root who true).toReal +
            (root who false).toReal = 1 := by linarith
        rw [hsum, one_mul]
  nlinarith

/-- Along every literal profile, with no purity premise on the displayed
player, actual live survival times shifted semantic debt is bounded by the
initial semantic debt. -/
theorem quittingLiveMass_mul_spineDebt_le_initialDebt
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    ∀ time,
      quittingLiveMass reward profile time *
          quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward
              (quittingAllContinueProfileSpine reward profile time)) who ≤
        quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward profile) who := by
  intro time
  induction time with
  | zero => simp [quittingAllContinueProfileSpine]
  | succ time ih =>
      let current := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile time)
      let tail := quittingTerminalSemanticPair reward
        (quittingAllContinueProfileSpine reward profile (time + 1))
      let root := quittingProfileLiveRoot reward profile time
      have honeStep : quittingStationaryContinueMass root *
          quittingTerminalSemanticDebt tail who ≤
        quittingTerminalSemanticDebt current who := by
        have htransport :=
          stationaryContinueMass_mul_debt_le_terminalSemanticDebt_prefix
            (reward := reward) tail root who
        have hprefix : current =
            quittingTerminalSemanticPrefix reward root tail := by
          dsimp only [current, root, tail]
          exact quittingTerminalSemanticPair_spine_eq_prefix
            reward profile time hM hreward
        rw [hprefix]
        exact htransport
      have hweighted : quittingLiveMass reward profile (time + 1) *
          quittingTerminalSemanticDebt tail who ≤
        quittingLiveMass reward profile time *
          quittingTerminalSemanticDebt current who := by
        have hjoint : quittingJointContinueMass reward profile time =
            quittingStationaryContinueMass root := by
          rw [quittingJointContinueMass_eq_product]
          rw [quittingStationaryContinueMass_eq_prod_continueProbability]
          rfl
        rw [quittingLiveMass_succ, hjoint]
        calc
          (quittingLiveMass reward profile time *
              quittingStationaryContinueMass root) *
                quittingTerminalSemanticDebt tail who =
            quittingLiveMass reward profile time *
              (quittingStationaryContinueMass root *
                quittingTerminalSemanticDebt tail who) := by ring
          _ ≤ quittingLiveMass reward profile time *
              quittingTerminalSemanticDebt current who :=
            mul_le_mul_of_nonneg_left honeStep
              (quittingLiveMass_nonneg reward profile time)
      exact hweighted.trans ih

/-- Every actual live-row coordinate defect is bounded, after weighting by
the actual probability of reaching that row, by the initial best-response
debt.  This is the one-stage-deviation packet needed at a moving mark. -/
theorem quittingLiveMass_mul_coordinateNashDefect_le_initialDebt
    (profile : (quittingGame reward).BehaviorProfile)
    (who : iota) (time : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    quittingLiveMass reward profile time *
        quittingRootCoordinateNashDefect reward
          (quittingTerminalSemanticPair reward
            (quittingAllContinueProfileSpine reward profile (time + 1))).1
          (quittingProfileLiveRoot reward profile time) who ≤
      quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward profile) who := by
  let tail := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile (time + 1))
  let root := quittingProfileLiveRoot reward profile time
  let current := quittingTerminalSemanticPair reward
    (quittingAllContinueProfileSpine reward profile time)
  have htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPair_mem_carrier reward _
  have htailDebt : 0 ≤ quittingTerminalSemanticDebt tail who :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward htailCarrier who
  have hlocal :=
    quittingRootCoordinateNashDefect_le_terminalSemanticDebt_prefix
      reward tail root who htailDebt
  rw [← quittingTerminalSemanticPair_spine_eq_prefix
    reward profile time hM hreward] at hlocal
  have hscaled := mul_le_mul_of_nonneg_left hlocal
    (quittingLiveMass_nonneg reward profile time)
  exact hscaled.trans
    (quittingLiveMass_mul_spineDebt_le_initialDebt
      (reward := reward) profile who hM hreward time)

/-! ## Executable reset-reprojection germ -/

/-- **The unbounded reprojection germ has literal profile provenance.**

The normalized path can be chosen among jointly co-realized semantic/law
points, rather than merely in their closure.  Thus the vanishing reset debt,
positive surface-tension scale, and positive limiting opponent incidence are
simultaneously witnessed by one sequence of executable profiles. -/
theorem exists_executable_positiveIncidence_normalizedReprojectionGerm
    (source : QuittingTerminalSemanticPair iota)
    (returned : QuittingTerminalSemanticLawPoint iota)
    (owner : iota) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ point ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum point)
    (hreturned : returned ∈ quittingTerminalSemanticLawCarrier reward)
    (hexcess : quittingTerminalSemanticDebtSum source <
      quittingTerminalSemanticDebtSum returned.1)
    (hreturnedIncidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner returned.2)
    (hslope : ∀ point ∈ quittingTerminalSemanticLawCarrier reward,
      quittingTerminalSemanticDebt point.1 owner = 0 →
      0 < quittingTerminalTotalOpponentIncidenceMass owner point.2 →
      (quittingTerminalSemanticDebtSum returned.1 -
            quittingTerminalSemanticDebtSum source) /
          quittingTerminalTotalOpponentIncidenceMass owner returned.2 ≤
        (quittingTerminalSemanticDebtSum point.1 -
            quittingTerminalSemanticDebtSum source) /
          quittingTerminalTotalOpponentIncidenceMass owner point.2)
    (hseparated : ∀ point ∈ quittingTerminalSemanticLawCarrier reward,
      quittingTerminalSemanticDebt point.1 owner = 0 →
      quittingTerminalSemanticDebtSum source <
        quittingTerminalSemanticDebtSum point.1)
    (hnoLinear : ¬ ∃ penalty, 0 ≤ penalty ∧
      ∀ point ∈ quittingTerminalSemanticLawCarrier reward,
        quittingResetReprojectionTension source returned point owner ≤
          penalty * quittingTerminalSemanticDebt point.1 owner) :
    ∃ contact : QuittingTerminalSemanticLawPoint iota,
      ∃ profiles : ℕ → (quittingGame reward).BehaviorProfile,
      contact ∈ quittingTerminalSemanticLawCarrier reward ∧
      Tendsto (fun n ↦
        (quittingTerminalSemanticPair reward (profiles n),
          quittingTerminalOutcomeMass reward (profiles n)))
        atTop (nhds contact) ∧
      (∀ n, 0 < quittingTerminalSemanticDebt
        (quittingTerminalSemanticPair reward (profiles n)) owner) ∧
      (∀ n, 0 < quittingResetReprojectionTension source returned
        (quittingTerminalSemanticPair reward (profiles n),
          quittingTerminalOutcomeMass reward (profiles n)) owner) ∧
      Tendsto (fun n ↦
        quittingTerminalSemanticDebt
            (quittingTerminalSemanticPair reward (profiles n)) owner /
          quittingResetReprojectionTension source returned
            (quittingTerminalSemanticPair reward (profiles n),
              quittingTerminalOutcomeMass reward (profiles n)) owner)
        atTop (nhds 0) ∧
      quittingTerminalSemanticDebt contact.1 owner = 0 ∧
      quittingResetReprojectionTension source returned contact owner = 0 ∧
      0 < quittingTerminalTotalOpponentIncidenceMass owner contact.2 ∧
      quittingTerminalRewardMoment reward contact.2 = contact.1.1 := by
  let face : QuittingTerminalSemanticLawPoint iota → ℝ := fun point ↦
    quittingTerminalSemanticDebt point.1 owner
  let tension : QuittingTerminalSemanticLawPoint iota → ℝ := fun point ↦
    quittingResetReprojectionTension source returned point owner
  have hfaceContinuous : Continuous face :=
    (continuous_quittingTerminalSemanticDebt owner).comp continuous_fst
  have htensionContinuous : Continuous tension := by
    dsimp only [tension, quittingResetReprojectionTension]
    apply Continuous.sub
    · exact continuous_const.mul
        ((continuous_quittingTerminalTotalOpponentIncidenceMass owner).comp
          continuous_snd)
    · exact (continuous_quittingTerminalSemanticDebtSum.comp
        continuous_fst).sub continuous_const
  have hfaceNonneg : ∀ point ∈ quittingTerminalSemanticLawCarrier reward,
      0 ≤ face point := by
    intro point hpoint
    exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward
        (terminalSemanticLawCarrier_fst_mem_carrier point hpoint) owner
  have hsupport : ∀ point ∈ quittingTerminalSemanticLawCarrier reward,
      face point = 0 → tension point ≤ 0 := by
    intro point hpoint hface
    have hsupported := surfaceTension_supports_resetFace
      source returned point owner hminimum hreturned hexcess
        hreturnedIncidence hslope hpoint hface
    dsimp only [tension, quittingResetReprojectionTension]
    linarith
  have hobstruction : ∀ penalty, 0 ≤ penalty →
      ∃ point ∈ quittingTerminalSemanticLawCarrier reward,
        0 < face point ∧ 0 < tension point ∧
          penalty * face point < tension point := by
    have halt := surfaceTension_linearPenalty_or_normalizedObstruction
      source returned owner hM hreward hminimum hreturned hexcess
        hreturnedIncidence hslope
    have hunbounded := halt.resolve_left (by
      intro hlinear
      apply hnoLinear
      rcases hlinear with ⟨penalty, hpenalty, hbound⟩
      refine ⟨penalty, hpenalty, ?_⟩
      intro point hpoint
      simpa [quittingResetReprojectionTension] using hbound point hpoint)
    intro penalty hpenalty
    obtain ⟨point, hpoint, hface, htension, hratio⟩ :=
      hunbounded penalty hpenalty
    exact ⟨point, hpoint, hface, htension, hratio⟩
  obtain ⟨contact, path, hcontact, hpathActual, hpath,
      hpathFace, hpathTension, hratio, hcontactFace,
      hcontactTension⟩ :=
    exists_normalized_contact_germ_in_dense_of_compact
      (quittingAttainableTerminalSemanticLawPoints reward)
      (quittingTerminalSemanticLawCarrier reward)
      (quittingTerminalSemanticLawCarrier_isCompact reward hM hreward)
      (subset_closure)
      (by rw [quittingTerminalSemanticLawCarrier])
      face tension hfaceContinuous htensionContinuous hfaceNonneg
        hsupport hobstruction
  have hpathRange : ∀ n, ∃ profile : (quittingGame reward).BehaviorProfile,
      (quittingTerminalSemanticPair reward profile,
        quittingTerminalOutcomeMass reward profile) = path n := by
    intro n
    exact hpathActual n
  choose profiles hprofiles using hpathRange
  have hprofilesTendsto : Tendsto (fun n ↦
      (quittingTerminalSemanticPair reward (profiles n),
        quittingTerminalOutcomeMass reward (profiles n)))
      atTop (nhds contact) := by
    convert hpath using 1
    funext n
    exact hprofiles n
  have hpathEq : path = fun n ↦
      (quittingTerminalSemanticPair reward (profiles n),
        quittingTerminalOutcomeMass reward (profiles n)) := by
    funext n
    exact (hprofiles n).symm
  have hslopePositive : 0 <
      (quittingTerminalSemanticDebtSum returned.1 -
          quittingTerminalSemanticDebtSum source) /
        quittingTerminalTotalOpponentIncidenceMass owner returned.2 :=
    div_pos (sub_pos.mpr hexcess) hreturnedIncidence
  have hcontactSeparated := hseparated contact hcontact hcontactFace
  have hcontactIncidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner contact.2 := by
    dsimp only [tension, quittingResetReprojectionTension] at hcontactTension
    nlinarith
  have hmoment := terminalSemanticLawCarrier_rewardMoment
    reward contact hcontact
  refine ⟨contact, profiles, hcontact, hprofilesTendsto, ?_, ?_, ?_,
    hcontactFace, hcontactTension, hcontactIncidence, hmoment⟩
  · intro n
    rw [hpathEq] at hpathFace
    exact hpathFace n
  · intro n
    rw [hpathEq] at hpathTension
    exact hpathTension n
  · rw [hpathEq] at hratio
    exact hratio

/-! ## A common finite-window packet -/

/-- A terminal coalition mass strictly above `lower` is already captured by
some finite chronological window. -/
theorem exists_finiteWindow_sum_stageCoalitionMass_gt
    (profile : (quittingGame reward).BehaviorProfile)
    (terminal : {S : Finset iota // S.Nonempty}) {lower : ℝ}
    (hlower : lower <
      quittingTerminalOutcomeMass reward profile (some terminal)) :
    ∃ cutoff,
      lower < ∑ time ∈ Finset.range cutoff,
        quittingStageCoalitionMass reward profile time terminal := by
  have hsum :=
    (hasSum_quittingStageCoalitionMass reward profile terminal).tendsto_sum_nat
  change lower < quittingAbsorbedMassLimit reward profile terminal at hlower
  have heventually := hsum.eventually (Ioi_mem_nhds hlower)
  exact heventually.exists

/-- **Same-profile chronological packet.**

If one executable joint semantic/law sequence converges to a law with positive
opponent incidence, while the displayed owner's debt is negligible relative
to a positive scale, then one fixed opponent and coalition carry a uniformly
positive amount of mass in finite (possibly drifting) windows of those very
profiles.  At every moving marked row, the actual survival-weighted owner
defect divided by the same scale tends to zero. -/
theorem exists_sameProfile_finiteWindow_defectPacket
    (contact : QuittingTerminalSemanticLawPoint iota)
    (profiles : ℕ → (quittingGame reward).BehaviorProfile)
    (owner : iota) (scale : ℕ → ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcontact : contact ∈ quittingTerminalSemanticLawCarrier reward)
    (hprofiles : Tendsto (fun n ↦
      (quittingTerminalSemanticPair reward (profiles n),
        quittingTerminalOutcomeMass reward (profiles n)))
      atTop (nhds contact))
    (hincidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner contact.2)
    (hscale : ∀ n, 0 < scale n)
    (hratio : Tendsto (fun n ↦
      quittingTerminalSemanticDebt
          (quittingTerminalSemanticPair reward (profiles n)) owner /
        scale n) atTop (nhds 0)) :
    ∃ other : iota, ∃ terminal : {S : Finset iota // S.Nonempty},
      ∃ lower : ℝ, ∃ cutoff : ℕ → ℕ,
      other ≠ owner ∧ other ∈ terminal.val ∧ 0 < lower ∧
      (∀ᶠ n in atTop,
        lower < ∑ time ∈ Finset.range (cutoff n),
          quittingStageCoalitionMass reward (profiles n) time terminal) ∧
      ∀ mark : ℕ → ℕ,
        Tendsto (fun n ↦
          (quittingLiveMass reward (profiles n) (mark n) *
            quittingRootCoordinateNashDefect reward
              (quittingTerminalSemanticPair reward
                (quittingAllContinueProfileSpine reward (profiles n)
                  (mark n + 1))).1
              (quittingProfileLiveRoot reward (profiles n) (mark n)) owner) /
            scale n) atTop (nhds 0) := by
  classical
  have hmass := terminalSemanticLawCarrier_mass_mem_stdSimplex
    (reward := reward) contact hcontact
  have hcoordinateNonneg : ∀ other ∈ Finset.univ.erase owner,
      0 ≤ quittingTerminalOpponentIncidenceMass owner other contact.2 := by
    intro other _
    unfold quittingTerminalOpponentIncidenceMass
    exact Finset.sum_nonneg fun terminal _ => hmass.1 (some terminal)
  obtain ⟨other, hotherMem, hotherIncidence⟩ :=
    (Finset.sum_pos_iff_of_nonneg hcoordinateNonneg).mp hincidence
  have hotherNe : other ≠ owner := (Finset.mem_erase.mp hotherMem).1
  obtain ⟨terminal, hterminalMem, _hterminalNe, hterminalMass⟩ :=
    exists_positiveMass_terminal_of_opponentIncidence
      owner other contact.2 hmass hotherIncidence
  let lower := contact.2 (some terminal) / 2
  have hlower : 0 < lower := by
    dsimp only [lower]
    linarith
  have hmassTendsto : Tendsto (fun n ↦
      quittingTerminalOutcomeMass reward (profiles n) (some terminal))
      atTop (nhds (contact.2 (some terminal))) :=
    ((continuous_apply (some terminal)).comp continuous_snd).tendsto contact |>.comp
      hprofiles
  have hpersistent : ∀ᶠ n in atTop,
      lower < quittingTerminalOutcomeMass reward (profiles n)
        (some terminal) :=
    hmassTendsto.eventually (Ioi_mem_nhds (by
      dsimp only [lower]
      linarith))
  let cutoff : ℕ → ℕ := fun n ↦
    if h : lower < quittingTerminalOutcomeMass reward (profiles n)
        (some terminal) then
      Classical.choose
        (exists_finiteWindow_sum_stageCoalitionMass_gt
          (reward := reward) (profiles n) terminal h)
    else 0
  have hwindow : ∀ᶠ n in atTop,
      lower < ∑ time ∈ Finset.range (cutoff n),
        quittingStageCoalitionMass reward (profiles n) time terminal := by
    filter_upwards [hpersistent] with n hn
    dsimp only [cutoff]
    rw [dif_pos hn]
    exact Classical.choose_spec
      (exists_finiteWindow_sum_stageCoalitionMass_gt
        (reward := reward) (profiles n) terminal hn)
  refine ⟨other, terminal, lower, cutoff, hotherNe, hterminalMem,
    hlower, hwindow, ?_⟩
  intro mark
  apply squeeze_zero
  · intro n
    exact div_nonneg
      (mul_nonneg (quittingLiveMass_nonneg reward (profiles n) (mark n))
        (quittingRootCoordinateNashDefect_nonneg reward _ _ owner))
      (hscale n).le
  · intro n
    apply (div_le_div_iff_of_pos_right (hscale n)).2
    exact quittingLiveMass_mul_coordinateNashDefect_le_initialDebt
      (reward := reward) (profiles n) owner (mark n) hM hreward
  · exact hratio

end GameTheory
