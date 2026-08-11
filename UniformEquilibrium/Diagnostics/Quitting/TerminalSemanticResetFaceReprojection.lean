/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetSurfaceTension

/-!
# Reprojection across a surface-tension reset face

A separated reset-face selector gives an exact supporting inequality only on
the face where the reset owner's debt is zero.  A routed endpoint move need
not remain on that face.  This file records the strongest unconditional
compactness bridge across that mismatch.

For every positive tolerance, sufficiently small reset-owner debt makes the
surface-tension inequality valid up to that tolerance.  Thus exact support on
the closed face has a uniform nonlinear extension to the whole compact joint
carrier.

The remaining quantitative seam is isolated by an exact alternative.  Either
the extension admits one linear face penalty, or there are off-face carrier
points with positive tension violation whose violation-to-reset-debt ratio is
arbitrarily large.  The second branch is the normalized reprojection
obstruction which must be converted to a tangent before a finite routed reset
word can be compiled.

No endpoint word, Bellman successor, or chronological recurrence is inferred
from compactness alone.
-/

noncomputable section

namespace GameTheory

open Set
open scoped Topology

variable {X : Type} [TopologicalSpace X]

/-! ## A compact nonlinear face penalty -/

/-- A continuous inequality valid on the zero face of a nonnegative
continuous coordinate extends uniformly, with arbitrary additive error, to
a sufficiently small neighborhood of that face inside a compact carrier. -/
theorem exists_nearZero_support_of_compact
    (carrier : Set X) (hcompact : IsCompact carrier)
    (face tension : X → ℝ)
    (hfaceContinuous : Continuous face)
    (htensionContinuous : Continuous tension)
    (hfaceNonneg : ∀ point ∈ carrier, 0 ≤ face point)
    (hsupport : ∀ point ∈ carrier, face point = 0 → tension point ≤ 0)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ delta, 0 < delta ∧
      ∀ point ∈ carrier, face point < delta → tension point < epsilon := by
  let bad : Set X := carrier ∩ {point | epsilon ≤ tension point}
  have hbadCompact : IsCompact bad :=
    hcompact.inter_right
      (isClosed_Ici.preimage htensionContinuous)
  by_cases hbadNonempty : bad.Nonempty
  · obtain ⟨minimizer, hminimizer, hminimal⟩ :=
      hbadCompact.exists_isMinOn hbadNonempty hfaceContinuous.continuousOn
    have hminimizerFacePositive : 0 < face minimizer := by
      have hnonneg : 0 ≤ face minimizer :=
        hfaceNonneg minimizer hminimizer.1
      apply lt_of_le_of_ne hnonneg
      intro hzero
      have hsupportMin := hsupport minimizer hminimizer.1 hzero.symm
      exact (not_lt_of_ge hsupportMin)
        (hepsilon.trans_le hminimizer.2)
    refine ⟨face minimizer, hminimizerFacePositive, ?_⟩
    intro point hpoint hfaceLt
    apply lt_of_not_ge
    intro htensionBad
    have hpointBad : point ∈ bad := ⟨hpoint, htensionBad⟩
    exact (not_lt_of_ge (hminimal hpointBad)) hfaceLt
  · refine ⟨1, by norm_num, ?_⟩
    intro point hpoint _
    apply lt_of_not_ge
    intro htensionBad
    exact hbadNonempty ⟨point, hpoint, htensionBad⟩

variable {X : Type} [TopologicalSpace X]

/-! ## Surface tension near the reset face -/

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- A surface-tension minimizer supports the entire exact reset face in
division-free form, including its zero-incidence boundary. -/
theorem surfaceTension_supports_resetFace
    (source : QuittingTerminalSemanticPair iota)
    (returned candidate : QuittingTerminalSemanticLawPoint iota)
    (owner : iota)
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
    (hcandidate : candidate ∈
      quittingTerminalSemanticLawCarrier reward)
    (hcandidateReset :
      quittingTerminalSemanticDebt candidate.1 owner = 0) :
    ((quittingTerminalSemanticDebtSum returned.1 -
          quittingTerminalSemanticDebtSum source) /
        quittingTerminalTotalOpponentIncidenceMass owner returned.2) *
        quittingTerminalTotalOpponentIncidenceMass owner candidate.2 ≤
      quittingTerminalSemanticDebtSum candidate.1 -
        quittingTerminalSemanticDebtSum source := by
  let slope :=
    (quittingTerminalSemanticDebtSum returned.1 -
        quittingTerminalSemanticDebtSum source) /
      quittingTerminalTotalOpponentIncidenceMass owner returned.2
  let incidence :=
    quittingTerminalTotalOpponentIncidenceMass owner candidate.2
  let excess := quittingTerminalSemanticDebtSum candidate.1 -
    quittingTerminalSemanticDebtSum source
  have hreturnedCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier returned hreturned
  have hcandidateCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier candidate hcandidate
  have hslopePositive : 0 < slope := by
    dsimp only [slope]
    exact div_pos (sub_pos.mpr hexcess) hreturnedIncidence
  have hexcessNonneg : 0 ≤ excess := by
    dsimp only [excess]
    linarith [hminimum candidate.1 hcandidateCarrier]
  by_cases hincidencePositive : 0 < incidence
  · have hquotient := hslope candidate hcandidate hcandidateReset
        hincidencePositive
    change slope ≤ excess / incidence at hquotient
    rw [le_div_iff₀ hincidencePositive] at hquotient
    exact hquotient
  · have hincidenceNonpos : incidence ≤ 0 := le_of_not_gt hincidencePositive
    exact (mul_nonpos_of_nonneg_of_nonpos hslopePositive.le
      hincidenceNonpos).trans hexcessNonneg

/-- **Uniform nonlinear reset-face reprojection.**

At a separated surface-tension minimizer, every carrier point with
sufficiently small reset-owner debt satisfies the supporting inequality up
to a prescribed additive error.  The radius depends on the fixed game,
selected face, and tolerance; no linear rate is asserted. -/
theorem exists_surfaceTension_nearResetFace_penalty
    (source : QuittingTerminalSemanticPair iota)
    (returned : QuittingTerminalSemanticLawPoint iota)
    (owner : iota) {M epsilon : ℝ}
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
    (hepsilon : 0 < epsilon) :
    ∃ delta, 0 < delta ∧
      ∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
        quittingTerminalSemanticDebt candidate.1 owner < delta →
        ((quittingTerminalSemanticDebtSum returned.1 -
              quittingTerminalSemanticDebtSum source) /
            quittingTerminalTotalOpponentIncidenceMass owner returned.2) *
            quittingTerminalTotalOpponentIncidenceMass owner candidate.2 ≤
          (quittingTerminalSemanticDebtSum candidate.1 -
            quittingTerminalSemanticDebtSum source) + epsilon := by
  let face : QuittingTerminalSemanticLawPoint iota → ℝ := fun point =>
    quittingTerminalSemanticDebt point.1 owner
  let tension : QuittingTerminalSemanticLawPoint iota → ℝ := fun point =>
    ((quittingTerminalSemanticDebtSum returned.1 -
          quittingTerminalSemanticDebtSum source) /
        quittingTerminalTotalOpponentIncidenceMass owner returned.2) *
        quittingTerminalTotalOpponentIncidenceMass owner point.2 -
      (quittingTerminalSemanticDebtSum point.1 -
        quittingTerminalSemanticDebtSum source)
  have hfaceContinuous : Continuous face :=
    (continuous_quittingTerminalSemanticDebt owner).comp continuous_fst
  have htensionContinuous : Continuous tension := by
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
    dsimp only [tension]
    linarith
  obtain ⟨delta, hdelta, hnear⟩ := exists_nearZero_support_of_compact
    (quittingTerminalSemanticLawCarrier reward)
      (quittingTerminalSemanticLawCarrier_isCompact reward hM hreward)
      face tension hfaceContinuous htensionContinuous hfaceNonneg hsupport
        hepsilon
  refine ⟨delta, hdelta, ?_⟩
  intro candidate hcandidate hcandidateNear
  have htensionLt := hnear candidate hcandidate hcandidateNear
  dsimp only [tension] at htensionLt
  linarith

/-! ## Linear penalty or normalized obstruction -/

/-- The exact quantitative reprojection seam.  Either one linear multiple of
the reset-owner debt controls surface-tension violation everywhere on the
joint carrier, or arbitrarily large multiples are defeated by positive,
off-face violations.  Exact face support forces every witness in the second
branch to have strictly positive reset debt.

The second branch is a normalized obstruction, not yet a tangent theorem:
extracting a limiting direction still requires choosing a scale and retaining
the realizing strategic provenance. -/
theorem surfaceTension_linearPenalty_or_normalizedObstruction
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
          quittingTerminalTotalOpponentIncidenceMass owner point.2) :
    (∃ penalty, 0 ≤ penalty ∧
      ∀ point ∈ quittingTerminalSemanticLawCarrier reward,
        ((quittingTerminalSemanticDebtSum returned.1 -
              quittingTerminalSemanticDebtSum source) /
            quittingTerminalTotalOpponentIncidenceMass owner returned.2) *
            quittingTerminalTotalOpponentIncidenceMass owner point.2 -
          (quittingTerminalSemanticDebtSum point.1 -
            quittingTerminalSemanticDebtSum source) ≤
          penalty * quittingTerminalSemanticDebt point.1 owner) ∨
    (∀ penalty, 0 ≤ penalty →
      ∃ point ∈ quittingTerminalSemanticLawCarrier reward,
        0 < quittingTerminalSemanticDebt point.1 owner ∧
        0 <
          ((quittingTerminalSemanticDebtSum returned.1 -
                quittingTerminalSemanticDebtSum source) /
              quittingTerminalTotalOpponentIncidenceMass owner returned.2) *
              quittingTerminalTotalOpponentIncidenceMass owner point.2 -
            (quittingTerminalSemanticDebtSum point.1 -
              quittingTerminalSemanticDebtSum source) ∧
        penalty * quittingTerminalSemanticDebt point.1 owner <
          ((quittingTerminalSemanticDebtSum returned.1 -
                quittingTerminalSemanticDebtSum source) /
              quittingTerminalTotalOpponentIncidenceMass owner returned.2) *
              quittingTerminalTotalOpponentIncidenceMass owner point.2 -
            (quittingTerminalSemanticDebtSum point.1 -
              quittingTerminalSemanticDebtSum source)) := by
  classical
  by_cases hlinear : ∃ penalty, 0 ≤ penalty ∧
      ∀ point ∈ quittingTerminalSemanticLawCarrier reward,
        ((quittingTerminalSemanticDebtSum returned.1 -
              quittingTerminalSemanticDebtSum source) /
            quittingTerminalTotalOpponentIncidenceMass owner returned.2) *
            quittingTerminalTotalOpponentIncidenceMass owner point.2 -
          (quittingTerminalSemanticDebtSum point.1 -
            quittingTerminalSemanticDebtSum source) ≤
          penalty * quittingTerminalSemanticDebt point.1 owner
  · exact Or.inl hlinear
  · right
    intro penalty hpenalty
    push Not at hlinear
    obtain ⟨point, hpoint, hviolation⟩ := hlinear penalty hpenalty
    have hfaceNonneg : 0 ≤ quittingTerminalSemanticDebt point.1 owner :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hM hreward
          (terminalSemanticLawCarrier_fst_mem_carrier point hpoint) owner
    have hfacePositive : 0 <
        quittingTerminalSemanticDebt point.1 owner := by
      apply lt_of_le_of_ne hfaceNonneg
      intro hfaceZero
      have hsupported := surfaceTension_supports_resetFace
        source returned point owner hminimum hreturned hexcess
          hreturnedIncidence hslope hpoint hfaceZero.symm
      rw [← hfaceZero] at hviolation
      norm_num at hviolation
      linarith
    have htensionPositive : 0 <
        ((quittingTerminalSemanticDebtSum returned.1 -
              quittingTerminalSemanticDebtSum source) /
            quittingTerminalTotalOpponentIncidenceMass owner returned.2) *
            quittingTerminalTotalOpponentIncidenceMass owner point.2 -
          (quittingTerminalSemanticDebtSum point.1 -
            quittingTerminalSemanticDebtSum source) := by
      have hpenaltyTerm : 0 ≤
          penalty * quittingTerminalSemanticDebt point.1 owner :=
        mul_nonneg hpenalty hfaceNonneg
      linarith
    exact ⟨point, hpoint, hfacePositive, htensionPositive, hviolation⟩

/-! ## Game-facing selector retaining the reprojection costate -/

/-- **Reset-face dichotomy with the surface-tension costate retained.**

The original surface-tension dichotomy exposes the unique all-Continue cap
plateau but intentionally hides the minimizing slope after using it.  Routed
reprojection needs that slope.  This strengthened interface returns the full
supporting inequality together with the cap-root rigidity, so consumers can
apply `exists_surfaceTension_nearResetFace_penalty` and
`surfaceTension_linearPenalty_or_normalizedObstruction` without repeating
the compact selector.

The first branch is an exact joint reset-face return to the global minimum.
The second is the separated plateau equipped with its reprojection costate. -/
theorem resetFace_globalMinimum_or_surfaceTension_reprojectionCostate
    (source target : QuittingTerminalSemanticPair iota)
    (mass : QuittingTerminalOutcome iota → ℝ)
    (owner : iota) {M : ℝ}
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
    (∃ resetMinimum : QuittingTerminalSemanticLawPoint iota,
      resetMinimum ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt resetMinimum.1 owner = 0 ∧
      quittingTerminalSemanticDebtSum resetMinimum.1 =
        quittingTerminalSemanticDebtSum source) ∨
    ∃ returned : QuittingTerminalSemanticLawPoint iota,
      returned ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt returned.1 owner = 0 ∧
      0 < quittingTerminalTotalOpponentIncidenceMass owner returned.2 ∧
      quittingTerminalSemanticDebtSum source <
        quittingTerminalSemanticDebtSum returned.1 ∧
      (∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
        quittingTerminalSemanticDebt candidate.1 owner = 0 →
        0 < quittingTerminalTotalOpponentIncidenceMass owner candidate.2 →
        (quittingTerminalSemanticDebtSum returned.1 -
              quittingTerminalSemanticDebtSum source) /
            quittingTerminalTotalOpponentIncidenceMass owner returned.2 ≤
          (quittingTerminalSemanticDebtSum candidate.1 -
              quittingTerminalSemanticDebtSum source) /
            quittingTerminalTotalOpponentIncidenceMass owner candidate.2) ∧
      ∀ root : iota → PMF Bool,
        IsεQuittingRootNash reward returned.1.2 0 root →
          root = (quittingAllContinueRoot : iota → PMF Bool) := by
  obtain ⟨resetMinimum, hresetMinimum, hresetMinimumReset,
      hresetMinimumIsMin⟩ :=
    exists_joint_resetFace_debtMinimizer target mass owner hM hreward
      htarget hreset
  have hresetMinimumCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier resetMinimum hresetMinimum
  have hsourceLeReset := hminimum resetMinimum.1 hresetMinimumCarrier
  rcases hsourceLeReset.eq_or_lt with heq | hstrict
  · exact Or.inl ⟨resetMinimum, hresetMinimum, hresetMinimumReset,
      heq.symm⟩
  · obtain ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
        hresetMinLeReturned, hslope⟩ :=
      exists_resetFace_minimizer_excess_div_totalOpponentIncidence
        source resetMinimum (target, mass) owner hM hreward
          hresetMinimumIsMin hstrict htarget hreset hincidence
    have hreturnedStrict : quittingTerminalSemanticDebtSum source <
        quittingTerminalSemanticDebtSum returned.1 :=
      hstrict.trans_le hresetMinLeReturned
    refine Or.inr ⟨returned, hreturned, hreturnedReset,
      hreturnedIncidence, hreturnedStrict, hslope, ?_⟩
    intro root hnash
    exact root_eq_allContinue_of_minimal_surfaceTension
      source returned owner root hM hreward hminimum hsourcePositive
        hreturned hreturnedReset hreturnedStrict hreturnedIncidence
        hslope hnash

end GameTheory
