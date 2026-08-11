/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn

/-!
# The debt/incidence variational obstruction on a reset face

Keeping a complete terminal law makes it possible to minimize a genuinely
joint semantic quantity.  Fix a reset player `owner` and an opponent label
`other`.  On joint carrier points with `d_owner = 0` and positive displayed
opponent incidence `I`, consider

`D / I`,

where `D` is total best-response debt.  Positive global minimum debt makes
this quotient coercive at the open boundary `I = 0`, so it attains a minimum
despite the strict positivity constraint.

For an exact cap--Nash prefix, debt and incidence obey

`D' = s D`,  `I' = a + s I`,

where `s` is root survival and `a` is fresh root incidence.  The prefixed
point stays on the reset face.  At a quotient minimizer, positivity of the
global debt floor forces `s > 0`, and the quotient inequality then forces
`a = 0`.  Thus every exact cap--Nash root at the selected joint point has no
fresh incidence in the prescribed opponent coordinate.

For one opponent coordinate this is weaker than forcing all-Continue: an
absorbing root may avoid the chosen opponent.  Summing incidence over all
opponents improves the conclusion to owner-only support.  A final secondary
minimization of `D` on the compact ratio-minimizer slice is decisive: after
fresh total incidence vanishes, a cap prefix scales both `D` and `I` by `s`,
so it remains ratio-minimal; secondary minimality forces `s = 1`.  The
resulting joint point retains positive old opponent incidence while every
exact cap--Nash root is literally all-Continue.

The tempting excess quotient `(D - D_*) / I` has a stronger formal descent
under absorption, but need not attain its infimum: both numerator and
incidence can tend to zero at the omitted boundary.  The unshifted quotient
is the robust variational object.
-/

noncomputable section

namespace GameTheory

open Set
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Displayed opponent incidence is a continuous linear coordinate of a
terminal law. -/
theorem continuous_quittingTerminalOpponentIncidenceMass
    (owner other : ι) :
    Continuous (quittingTerminalOpponentIncidenceMass owner other) := by
  unfold quittingTerminalOpponentIncidenceMass
  exact continuous_finsetSum _ fun terminal _ =>
    continuous_apply (some terminal)

/-- Sum of all displayed opponent-incidence coordinates for one reset owner.
A coalition containing several opponents is counted once for each such
opponent; this multiplicity is useful because vanishing of the total is
equivalent to coordinatewise vanishing. -/
def quittingTerminalTotalOpponentIncidenceMass
    (owner : ι) (mass : QuittingTerminalOutcome ι → ℝ) : ℝ :=
  ∑ other ∈ Finset.univ.erase owner,
    quittingTerminalOpponentIncidenceMass owner other mass

/-- Root-stage analogue of total opponent incidence. -/
def quittingRootTotalOpponentIncidenceMass
    (owner : ι) (root : ι → PMF Bool) : ℝ :=
  ∑ other ∈ Finset.univ.erase owner,
    quittingRootOpponentIncidenceMass owner other root

/-- Total opponent incidence is continuous in the terminal law. -/
theorem continuous_quittingTerminalTotalOpponentIncidenceMass
    (owner : ι) :
    Continuous (quittingTerminalTotalOpponentIncidenceMass owner) := by
  unfold quittingTerminalTotalOpponentIncidenceMass
  exact continuous_finsetSum _ fun other _ =>
    continuous_quittingTerminalOpponentIncidenceMass owner other

/-- Total fresh root incidence is nonnegative. -/
theorem quittingRootTotalOpponentIncidenceMass_nonneg
    (owner : ι) (root : ι → PMF Bool) :
    0 ≤ quittingRootTotalOpponentIncidenceMass owner root := by
  unfold quittingRootTotalOpponentIncidenceMass
  apply Finset.sum_nonneg
  intro other _
  unfold quittingRootOpponentIncidenceMass
  exact Finset.sum_nonneg fun terminal _ =>
    MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
      root terminal.val

/-- Exact affine action of a prefix on total opponent incidence. -/
theorem quittingTerminalTotalOpponentIncidenceMass_lawPrefix
    (owner : ι) (root : ι → PMF Bool)
    (mass : QuittingTerminalOutcome ι → ℝ) :
    quittingTerminalTotalOpponentIncidenceMass owner
        (quittingTerminalOutcomeLawPrefix root mass) =
      quittingRootTotalOpponentIncidenceMass owner root +
        quittingStationaryContinueMass root *
          quittingTerminalTotalOpponentIncidenceMass owner mass := by
  unfold quittingTerminalTotalOpponentIncidenceMass
    quittingRootTotalOpponentIncidenceMass
  simp_rw [quittingTerminalOpponentIncidenceMass_lawPrefix]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- The semantic projection of a joint semantic/law carrier point belongs to
the ordinary terminal-semantic carrier. -/
theorem terminalSemanticLawCarrier_fst_mem_carrier
    (point : QuittingTerminalSemanticLawPoint ι)
    (hpoint : point ∈ quittingTerminalSemanticLawCarrier reward) :
    point.1 ∈ quittingTerminalSemanticCarrier reward := by
  rw [quittingTerminalSemanticCarrier]
  apply map_mem_closure continuous_fst hpoint
  rintro candidate ⟨profile, rfl⟩
  exact ⟨profile, rfl⟩

/-- **Attainment of the debt/incidence quotient on a reset face.**

Although positive incidence is an open condition, the positive global debt
floor prevents a minimizing sequence from approaching incidence zero.  The
proof makes this quantitative: relative to the supplied positive-incidence
target, every possible improvement lies in the closed slice

`I ≥ D_* I_target / D_target`.

The returned point globally minimizes `D / I` among all joint carrier points
on the same reset face with positive displayed incidence. -/
theorem exists_resetFace_minimizer_debt_div_incidence
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (owner other : ι) {M : ℝ}
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
      quittingTerminalOpponentIncidenceMass owner other mass) :
    ∃ returned : QuittingTerminalSemanticLawPoint ι,
      returned ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt returned.1 owner = 0 ∧
      0 < quittingTerminalOpponentIncidenceMass owner other returned.2 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned.1 ∧
      ∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
        quittingTerminalSemanticDebt candidate.1 owner = 0 →
        0 < quittingTerminalOpponentIncidenceMass owner other candidate.2 →
        quittingTerminalSemanticDebtSum returned.1 /
            quittingTerminalOpponentIncidenceMass owner other returned.2 ≤
          quittingTerminalSemanticDebtSum candidate.1 /
            quittingTerminalOpponentIncidenceMass owner other candidate.2 := by
  let sourceDebt := quittingTerminalSemanticDebtSum source
  let targetDebt := quittingTerminalSemanticDebtSum target
  let targetIncidence :=
    quittingTerminalOpponentIncidenceMass owner other mass
  let incidenceFloor := sourceDebt * targetIncidence / targetDebt
  let incidence : QuittingTerminalSemanticLawPoint ι → ℝ := fun point =>
    quittingTerminalOpponentIncidenceMass owner other point.2
  let debt : QuittingTerminalSemanticLawPoint ι → ℝ := fun point =>
    quittingTerminalSemanticDebtSum point.1
  let ratio : QuittingTerminalSemanticLawPoint ι → ℝ := fun point =>
    debt point / incidence point
  let admissible : Set (QuittingTerminalSemanticLawPoint ι) :=
    quittingTerminalSemanticLawCarrier reward ∩
      {point | quittingTerminalSemanticDebt point.1 owner = 0} ∩
      {point | incidenceFloor ≤ incidence point}
  have htargetCarrier : target ∈ quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier (target, mass) htarget
  have hsourceLeTarget : sourceDebt ≤ targetDebt := by
    exact hminimum target htargetCarrier
  have htargetDebtPositive : 0 < targetDebt :=
    hsourcePositive.trans_le hsourceLeTarget
  have hfloorPositive : 0 < incidenceFloor := by
    dsimp only [incidenceFloor, sourceDebt, targetIncidence, targetDebt]
    positivity
  have hfloorLeTarget : incidenceFloor ≤ targetIncidence := by
    rw [show incidenceFloor = sourceDebt * targetIncidence / targetDebt by rfl,
      div_le_iff₀ htargetDebtPositive]
    nlinarith
  have hincidenceContinuous : Continuous incidence :=
    (continuous_quittingTerminalOpponentIncidenceMass owner other).comp
      continuous_snd
  have hdebtContinuous : Continuous debt :=
    continuous_quittingTerminalSemanticDebtSum.comp continuous_fst
  have hresetClosed : IsClosed
      {point : QuittingTerminalSemanticLawPoint ι |
        quittingTerminalSemanticDebt point.1 owner = 0} :=
    isClosed_eq
      ((continuous_quittingTerminalSemanticDebt owner).comp continuous_fst)
      continuous_const
  have hfloorClosed : IsClosed
      {point : QuittingTerminalSemanticLawPoint ι |
        incidenceFloor ≤ incidence point} :=
    isClosed_Ici.preimage hincidenceContinuous
  have hadmissibleCompact : IsCompact admissible :=
    ((quittingTerminalSemanticLawCarrier_isCompact reward hM hreward).inter_right
      hresetClosed).inter_right hfloorClosed
  have htargetAdmissible : (target, mass) ∈ admissible := by
    exact ⟨⟨htarget, hreset⟩, hfloorLeTarget⟩
  have hadmissibleNonempty : admissible.Nonempty :=
    ⟨(target, mass), htargetAdmissible⟩
  have hratioContinuous : ContinuousOn ratio admissible := by
    apply hdebtContinuous.continuousOn.div hincidenceContinuous.continuousOn
    intro point hpoint
    have hfloor := hpoint.2
    have hpositive : 0 < incidence point := hfloorPositive.trans_le hfloor
    exact ne_of_gt hpositive
  obtain ⟨returned, hreturnedAdmissible, hreturnedMin⟩ :=
    hadmissibleCompact.exists_isMinOn hadmissibleNonempty hratioContinuous
  have hreturnedJoint := hreturnedAdmissible.1.1
  have hreturnedReset := hreturnedAdmissible.1.2
  have hreturnedIncidence : 0 < incidence returned :=
    hfloorPositive.trans_le hreturnedAdmissible.2
  have hreturnedCarrier : returned.1 ∈
      quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier returned hreturnedJoint
  have hsourceLeReturned : sourceDebt ≤ debt returned :=
    hminimum returned.1 hreturnedCarrier
  have hreturnedLeTarget : ratio returned ≤ ratio (target, mass) :=
    hreturnedMin htargetAdmissible
  refine ⟨returned, hreturnedJoint, hreturnedReset, hreturnedIncidence,
    hsourceLeReturned, ?_⟩
  intro candidate hcandidateJoint hcandidateReset hcandidateIncidence
  by_cases hcandidateFloor : incidenceFloor ≤ incidence candidate
  · exact hreturnedMin ⟨⟨hcandidateJoint, hcandidateReset⟩, hcandidateFloor⟩
  · have hcandidateFloorLt : incidence candidate < incidenceFloor :=
      lt_of_not_ge hcandidateFloor
    have hcandidateCarrier : candidate.1 ∈
        quittingTerminalSemanticCarrier reward :=
      terminalSemanticLawCarrier_fst_mem_carrier candidate hcandidateJoint
    have hsourceLeCandidate : sourceDebt ≤ debt candidate :=
      hminimum candidate.1 hcandidateCarrier
    have hsmall : incidence candidate * targetDebt <
        sourceDebt * targetIncidence := by
      rw [show incidenceFloor =
        sourceDebt * targetIncidence / targetDebt by rfl,
        lt_div_iff₀ htargetDebtPositive] at hcandidateFloorLt
      simpa [mul_comm] using hcandidateFloorLt
    have htargetRatioLtCandidate :
        ratio (target, mass) < ratio candidate := by
      rw [show ratio (target, mass) = targetDebt / targetIncidence by rfl,
        show ratio candidate = debt candidate / incidence candidate by rfl,
        div_lt_div_iff₀ hincidence hcandidateIncidence]
      nlinarith
    exact hreturnedLeTarget.trans htargetRatioLtCandidate.le

/-- Aggregate version of quotient attainment.  A positive value of the total
opponent incidence is enough to prevent escape through the open zero-incidence
boundary. -/
theorem exists_resetFace_minimizer_debt_div_totalOpponentIncidence
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
      ∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
        quittingTerminalSemanticDebt candidate.1 owner = 0 →
        0 < quittingTerminalTotalOpponentIncidenceMass owner candidate.2 →
        quittingTerminalSemanticDebtSum returned.1 /
            quittingTerminalTotalOpponentIncidenceMass owner returned.2 ≤
          quittingTerminalSemanticDebtSum candidate.1 /
            quittingTerminalTotalOpponentIncidenceMass owner candidate.2 := by
  let sourceDebt := quittingTerminalSemanticDebtSum source
  let targetDebt := quittingTerminalSemanticDebtSum target
  let targetIncidence :=
    quittingTerminalTotalOpponentIncidenceMass owner mass
  let incidenceFloor := sourceDebt * targetIncidence / targetDebt
  let incidence : QuittingTerminalSemanticLawPoint ι → ℝ := fun point =>
    quittingTerminalTotalOpponentIncidenceMass owner point.2
  let debt : QuittingTerminalSemanticLawPoint ι → ℝ := fun point =>
    quittingTerminalSemanticDebtSum point.1
  let ratio : QuittingTerminalSemanticLawPoint ι → ℝ := fun point =>
    debt point / incidence point
  let admissible : Set (QuittingTerminalSemanticLawPoint ι) :=
    quittingTerminalSemanticLawCarrier reward ∩
      {point | quittingTerminalSemanticDebt point.1 owner = 0} ∩
      {point | incidenceFloor ≤ incidence point}
  have htargetCarrier : target ∈ quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier (target, mass) htarget
  have hsourceLeTarget : sourceDebt ≤ targetDebt := by
    exact hminimum target htargetCarrier
  have htargetDebtPositive : 0 < targetDebt :=
    hsourcePositive.trans_le hsourceLeTarget
  have hfloorPositive : 0 < incidenceFloor := by
    dsimp only [incidenceFloor, sourceDebt, targetIncidence, targetDebt]
    positivity
  have hfloorLeTarget : incidenceFloor ≤ targetIncidence := by
    rw [show incidenceFloor = sourceDebt * targetIncidence / targetDebt by rfl,
      div_le_iff₀ htargetDebtPositive]
    nlinarith
  have hincidenceContinuous : Continuous incidence :=
    (continuous_quittingTerminalTotalOpponentIncidenceMass owner).comp
      continuous_snd
  have hdebtContinuous : Continuous debt :=
    continuous_quittingTerminalSemanticDebtSum.comp continuous_fst
  have hresetClosed : IsClosed
      {point : QuittingTerminalSemanticLawPoint ι |
        quittingTerminalSemanticDebt point.1 owner = 0} :=
    isClosed_eq
      ((continuous_quittingTerminalSemanticDebt owner).comp continuous_fst)
      continuous_const
  have hfloorClosed : IsClosed
      {point : QuittingTerminalSemanticLawPoint ι |
        incidenceFloor ≤ incidence point} :=
    isClosed_Ici.preimage hincidenceContinuous
  have hadmissibleCompact : IsCompact admissible :=
    ((quittingTerminalSemanticLawCarrier_isCompact reward hM hreward).inter_right
      hresetClosed).inter_right hfloorClosed
  have htargetAdmissible : (target, mass) ∈ admissible := by
    exact ⟨⟨htarget, hreset⟩, hfloorLeTarget⟩
  have hadmissibleNonempty : admissible.Nonempty :=
    ⟨(target, mass), htargetAdmissible⟩
  have hratioContinuous : ContinuousOn ratio admissible := by
    apply hdebtContinuous.continuousOn.div hincidenceContinuous.continuousOn
    intro point hpoint
    have hpositive : 0 < incidence point :=
      hfloorPositive.trans_le hpoint.2
    exact ne_of_gt hpositive
  obtain ⟨returned, hreturnedAdmissible, hreturnedMin⟩ :=
    hadmissibleCompact.exists_isMinOn hadmissibleNonempty hratioContinuous
  have hreturnedJoint := hreturnedAdmissible.1.1
  have hreturnedReset := hreturnedAdmissible.1.2
  have hreturnedIncidence : 0 < incidence returned :=
    hfloorPositive.trans_le hreturnedAdmissible.2
  have hreturnedCarrier : returned.1 ∈
      quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier returned hreturnedJoint
  have hsourceLeReturned : sourceDebt ≤ debt returned :=
    hminimum returned.1 hreturnedCarrier
  have hreturnedLeTarget : ratio returned ≤ ratio (target, mass) :=
    hreturnedMin htargetAdmissible
  refine ⟨returned, hreturnedJoint, hreturnedReset, hreturnedIncidence,
    hsourceLeReturned, ?_⟩
  intro candidate hcandidateJoint hcandidateReset hcandidateIncidence
  by_cases hcandidateFloor : incidenceFloor ≤ incidence candidate
  · exact hreturnedMin ⟨⟨hcandidateJoint, hcandidateReset⟩, hcandidateFloor⟩
  · have hcandidateFloorLt : incidence candidate < incidenceFloor :=
      lt_of_not_ge hcandidateFloor
    have hcandidateCarrier : candidate.1 ∈
        quittingTerminalSemanticCarrier reward :=
      terminalSemanticLawCarrier_fst_mem_carrier candidate hcandidateJoint
    have hsourceLeCandidate : sourceDebt ≤ debt candidate :=
      hminimum candidate.1 hcandidateCarrier
    have hsmall : incidence candidate * targetDebt <
        sourceDebt * targetIncidence := by
      rw [show incidenceFloor =
        sourceDebt * targetIncidence / targetDebt by rfl,
        lt_div_iff₀ htargetDebtPositive] at hcandidateFloorLt
      simpa [mul_comm] using hcandidateFloorLt
    have htargetRatioLtCandidate :
        ratio (target, mass) < ratio candidate := by
      rw [show ratio (target, mass) = targetDebt / targetIncidence by rfl,
        show ratio candidate = debt candidate / incidence candidate by rfl,
        div_lt_div_iff₀ hincidence hcandidateIncidence]
      nlinarith
    exact hreturnedLeTarget.trans htargetRatioLtCandidate.le

/-- **Lexicographic aggregate selector.**

First minimize total debt per unit of total opponent incidence, then minimize
total debt on that ratio-minimizer slice.  The second stage is again compact:
the positive global debt floor supplies a closed positive-incidence slice,
and the ratio sublevel can be written without division as a closed bilinear
inequality against the first minimizer. -/
theorem exists_resetFace_lexicographic_totalOpponentIncidence_minimizer
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
      (∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
        quittingTerminalSemanticDebt candidate.1 owner = 0 →
        0 < quittingTerminalTotalOpponentIncidenceMass owner candidate.2 →
        quittingTerminalSemanticDebtSum returned.1 /
            quittingTerminalTotalOpponentIncidenceMass owner returned.2 ≤
          quittingTerminalSemanticDebtSum candidate.1 /
            quittingTerminalTotalOpponentIncidenceMass owner candidate.2) ∧
      (∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
        quittingTerminalSemanticDebt candidate.1 owner = 0 →
        0 < quittingTerminalTotalOpponentIncidenceMass owner candidate.2 →
        quittingTerminalSemanticDebtSum candidate.1 /
              quittingTerminalTotalOpponentIncidenceMass owner candidate.2 =
            quittingTerminalSemanticDebtSum returned.1 /
              quittingTerminalTotalOpponentIncidenceMass owner returned.2 →
        quittingTerminalSemanticDebtSum returned.1 ≤
          quittingTerminalSemanticDebtSum candidate.1) := by
  obtain ⟨first, hfirstJoint, hfirstReset, hfirstIncidence,
      hsourceLeFirst, hfirstRatio⟩ :=
    exists_resetFace_minimizer_debt_div_totalOpponentIncidence
      source target mass owner hM hreward hminimum hsourcePositive
        htarget hreset hincidence
  let sourceDebt := quittingTerminalSemanticDebtSum source
  let firstDebt := quittingTerminalSemanticDebtSum first.1
  let firstIncidence :=
    quittingTerminalTotalOpponentIncidenceMass owner first.2
  let incidenceFloor := sourceDebt * firstIncidence / firstDebt
  let incidence : QuittingTerminalSemanticLawPoint ι → ℝ := fun point =>
    quittingTerminalTotalOpponentIncidenceMass owner point.2
  let debt : QuittingTerminalSemanticLawPoint ι → ℝ := fun point =>
    quittingTerminalSemanticDebtSum point.1
  let ratio : QuittingTerminalSemanticLawPoint ι → ℝ := fun point =>
    debt point / incidence point
  let secondary : Set (QuittingTerminalSemanticLawPoint ι) :=
    quittingTerminalSemanticLawCarrier reward ∩
      {point | quittingTerminalSemanticDebt point.1 owner = 0} ∩
      {point | incidenceFloor ≤ incidence point} ∩
      {point | debt point * firstIncidence ≤ firstDebt * incidence point}
  have hfirstDebtPositive : 0 < firstDebt :=
    hsourcePositive.trans_le hsourceLeFirst
  have hfloorPositive : 0 < incidenceFloor := by
    dsimp only [incidenceFloor, sourceDebt, firstIncidence, firstDebt]
    positivity
  have hfloorLeFirst : incidenceFloor ≤ firstIncidence := by
    rw [show incidenceFloor = sourceDebt * firstIncidence / firstDebt by rfl,
      div_le_iff₀ hfirstDebtPositive]
    nlinarith
  have hincidenceContinuous : Continuous incidence :=
    (continuous_quittingTerminalTotalOpponentIncidenceMass owner).comp
      continuous_snd
  have hdebtContinuous : Continuous debt :=
    continuous_quittingTerminalSemanticDebtSum.comp continuous_fst
  have hresetClosed : IsClosed
      {point : QuittingTerminalSemanticLawPoint ι |
        quittingTerminalSemanticDebt point.1 owner = 0} :=
    isClosed_eq
      ((continuous_quittingTerminalSemanticDebt owner).comp continuous_fst)
      continuous_const
  have hfloorClosed : IsClosed
      {point : QuittingTerminalSemanticLawPoint ι |
        incidenceFloor ≤ incidence point} :=
    isClosed_Ici.preimage hincidenceContinuous
  have hratioSublevelClosed : IsClosed
      {point : QuittingTerminalSemanticLawPoint ι |
        debt point * firstIncidence ≤ firstDebt * incidence point} :=
    isClosed_le (hdebtContinuous.mul continuous_const)
      (continuous_const.mul hincidenceContinuous)
  have hsecondaryCompact : IsCompact secondary :=
    (((quittingTerminalSemanticLawCarrier_isCompact reward hM hreward).inter_right
      hresetClosed).inter_right hfloorClosed).inter_right hratioSublevelClosed
  have hfirstSecondary : first ∈ secondary := by
    refine ⟨⟨⟨hfirstJoint, hfirstReset⟩, hfloorLeFirst⟩, ?_⟩
    change firstDebt * firstIncidence ≤ firstDebt * firstIncidence
    exact le_rfl
  obtain ⟨returned, hreturnedSecondary, hreturnedMinDebt⟩ :=
    hsecondaryCompact.exists_isMinOn ⟨first, hfirstSecondary⟩
      hdebtContinuous.continuousOn
  have hreturnedJoint := hreturnedSecondary.1.1.1
  have hreturnedReset := hreturnedSecondary.1.1.2
  have hreturnedIncidence : 0 < incidence returned :=
    hfloorPositive.trans_le hreturnedSecondary.1.2
  have hreturnedCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier returned hreturnedJoint
  have hsourceLeReturned : sourceDebt ≤ debt returned :=
    hminimum returned.1 hreturnedCarrier
  have hreturnedRatioLeFirst : ratio returned ≤ ratio first := by
    rw [show ratio returned = debt returned / incidence returned by rfl,
      show ratio first = firstDebt / firstIncidence by rfl,
      div_le_div_iff₀ hreturnedIncidence hfirstIncidence]
    exact hreturnedSecondary.2
  have hfirstRatioLeReturned : ratio first ≤ ratio returned := by
    exact hfirstRatio returned hreturnedJoint hreturnedReset
      hreturnedIncidence
  have hreturnedRatioEqFirst : ratio returned = ratio first :=
    le_antisymm hreturnedRatioLeFirst hfirstRatioLeReturned
  have hreturnedRatio : ∀ candidate ∈
      quittingTerminalSemanticLawCarrier reward,
      quittingTerminalSemanticDebt candidate.1 owner = 0 →
      0 < incidence candidate → ratio returned ≤ ratio candidate := by
    intro candidate hcandidate hcandidateReset hcandidateIncidence
    rw [hreturnedRatioEqFirst]
    exact hfirstRatio candidate hcandidate hcandidateReset hcandidateIncidence
  refine ⟨returned, hreturnedJoint, hreturnedReset, hreturnedIncidence,
    hsourceLeReturned, hreturnedRatio, ?_⟩
  intro candidate hcandidateJoint hcandidateReset hcandidateIncidence
    hcandidateRatio
  have hsourceLeCandidate : sourceDebt ≤ debt candidate := by
    exact hminimum candidate.1
      (terminalSemanticLawCarrier_fst_mem_carrier candidate hcandidateJoint)
  have hcrossEq : debt candidate * firstIncidence =
      firstDebt * incidence candidate := by
    have hratioFirst : ratio candidate = ratio first := by
      have hcandidateRatio' : ratio candidate = ratio returned :=
        hcandidateRatio
      rw [hreturnedRatioEqFirst] at hcandidateRatio'
      exact hcandidateRatio'
    rw [show ratio candidate = debt candidate / incidence candidate by rfl,
      show ratio first = firstDebt / firstIncidence by rfl,
      div_eq_div_iff hcandidateIncidence.ne' hfirstIncidence.ne'] at hratioFirst
    exact hratioFirst
  have hcandidateFloor : incidenceFloor ≤ incidence candidate := by
    rw [show incidenceFloor =
      sourceDebt * firstIncidence / firstDebt by rfl,
      div_le_iff₀ hfirstDebtPositive]
    nlinarith
  have hcandidateSecondary : candidate ∈ secondary := by
    exact ⟨⟨⟨hcandidateJoint, hcandidateReset⟩, hcandidateFloor⟩,
      hcrossEq.le⟩
  exact hreturnedMinDebt hcandidateSecondary

/-- **Fresh-incidence obstruction at a debt/incidence minimizer.**

Every exact cap--Nash prefix remains on the reset face and transports positive
old incidence because the positive global debt floor forces positive root
survival.  Ratio minimality then forces the root's newly created incidence in
the selected opponent coordinate to vanish. -/
theorem rootOpponentIncidence_eq_zero_of_minimal_debt_div_incidence
    (source : QuittingTerminalSemanticPair ι)
    (returned : QuittingTerminalSemanticLawPoint ι)
    (owner other : ι) (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (hreturned : returned ∈ quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt returned.1 owner = 0)
    (hincidence : 0 <
      quittingTerminalOpponentIncidenceMass owner other returned.2)
    (hratio : ∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
      quittingTerminalSemanticDebt candidate.1 owner = 0 →
      0 < quittingTerminalOpponentIncidenceMass owner other candidate.2 →
      quittingTerminalSemanticDebtSum returned.1 /
          quittingTerminalOpponentIncidenceMass owner other returned.2 ≤
        quittingTerminalSemanticDebtSum candidate.1 /
          quittingTerminalOpponentIncidenceMass owner other candidate.2)
    (hnash : IsεQuittingRootNash reward returned.1.2 0 root) :
    quittingRootOpponentIncidenceMass owner other root = 0 := by
  let prefixed := quittingTerminalSemanticPrefix reward root returned.1
  let prefixedMass := quittingTerminalOutcomeLawPrefix root returned.2
  let survival := quittingStationaryContinueMass root
  let oldIncidence :=
    quittingTerminalOpponentIncidenceMass owner other returned.2
  let freshIncidence := quittingRootOpponentIncidenceMass owner other root
  have hprefixedJoint : (prefixed, prefixedMass) ∈
      quittingTerminalSemanticLawCarrier reward := by
    exact quittingTerminalSemanticLawPrefix_mem_carrier
      reward root returned hM hreward hreturned
  have hprefixedCarrier : prefixed ∈
      quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier
      (prefixed, prefixedMass) hprefixedJoint
  have hprefixedReset : quittingTerminalSemanticDebt prefixed owner = 0 := by
    rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) returned.1 root owner hnash, hreset, mul_zero]
  have hdebtScale : quittingTerminalSemanticDebtSum prefixed =
      survival * quittingTerminalSemanticDebtSum returned.1 := by
    exact quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) returned.1 root hnash
  have hsourceLePrefixed : quittingTerminalSemanticDebtSum source ≤
      quittingTerminalSemanticDebtSum prefixed :=
    hminimum prefixed hprefixedCarrier
  have hsurvivalPositive : 0 < survival := by
    by_contra hnot
    have hsurvivalZero : survival = 0 :=
      le_antisymm (le_of_not_gt hnot)
        (quittingStationaryContinueMass_nonneg root)
    rw [hdebtScale, hsurvivalZero, zero_mul] at hsourceLePrefixed
    linarith
  have hprefixedIncidence :
      quittingTerminalOpponentIncidenceMass owner other prefixedMass =
        freshIncidence + survival * oldIncidence := by
    exact quittingTerminalOpponentIncidenceMass_lawPrefix
      owner other root returned.2
  have hprefixedIncidencePositive : 0 <
      quittingTerminalOpponentIncidenceMass owner other prefixedMass := by
    rw [hprefixedIncidence]
    have hfreshNonneg : 0 ≤ freshIncidence := by
      unfold freshIncidence quittingRootOpponentIncidenceMass
      exact Finset.sum_nonneg fun terminal _ =>
        MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
          root terminal.val
    positivity
  have hminimal := hratio (prefixed, prefixedMass) hprefixedJoint
    hprefixedReset hprefixedIncidencePositive
  have hreturnedDebtPositive : 0 <
      quittingTerminalSemanticDebtSum returned.1 := by
    have hreturnedCarrier :=
      terminalSemanticLawCarrier_fst_mem_carrier returned hreturned
    exact hsourcePositive.trans_le (hminimum returned.1 hreturnedCarrier)
  have hcross : quittingTerminalSemanticDebtSum returned.1 *
      (freshIncidence + survival * oldIncidence) ≤
        (survival * quittingTerminalSemanticDebtSum returned.1) *
          oldIncidence := by
    have holdPositive : 0 < oldIncidence := hincidence
    have hnewPositive : 0 < freshIncidence + survival * oldIncidence := by
      rw [← hprefixedIncidence]
      exact hprefixedIncidencePositive
    change quittingTerminalSemanticDebtSum returned.1 / oldIncidence ≤
      quittingTerminalSemanticDebtSum prefixed /
        quittingTerminalOpponentIncidenceMass owner other prefixedMass at hminimal
    rw [hdebtScale, hprefixedIncidence,
      div_le_div_iff₀ holdPositive hnewPositive] at hminimal
    exact hminimal
  have hfreshNonneg : 0 ≤ freshIncidence := by
    unfold freshIncidence quittingRootOpponentIncidenceMass
    exact Finset.sum_nonneg fun terminal _ =>
      MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
        root terminal.val
  have hfreshZero : freshIncidence = 0 := by
    nlinarith
  exact hfreshZero

/-- Aggregate fresh-incidence obstruction at a total-incidence quotient
minimizer. -/
theorem rootTotalOpponentIncidence_eq_zero_of_minimal_debt_div_incidence
    (source : QuittingTerminalSemanticPair ι)
    (returned : QuittingTerminalSemanticLawPoint ι)
    (owner : ι) (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (hreturned : returned ∈ quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt returned.1 owner = 0)
    (hincidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner returned.2)
    (hratio : ∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
      quittingTerminalSemanticDebt candidate.1 owner = 0 →
      0 < quittingTerminalTotalOpponentIncidenceMass owner candidate.2 →
      quittingTerminalSemanticDebtSum returned.1 /
          quittingTerminalTotalOpponentIncidenceMass owner returned.2 ≤
        quittingTerminalSemanticDebtSum candidate.1 /
          quittingTerminalTotalOpponentIncidenceMass owner candidate.2)
    (hnash : IsεQuittingRootNash reward returned.1.2 0 root) :
    quittingRootTotalOpponentIncidenceMass owner root = 0 := by
  let prefixed := quittingTerminalSemanticPrefix reward root returned.1
  let prefixedMass := quittingTerminalOutcomeLawPrefix root returned.2
  let survival := quittingStationaryContinueMass root
  let oldIncidence :=
    quittingTerminalTotalOpponentIncidenceMass owner returned.2
  let freshIncidence := quittingRootTotalOpponentIncidenceMass owner root
  have hprefixedJoint : (prefixed, prefixedMass) ∈
      quittingTerminalSemanticLawCarrier reward := by
    exact quittingTerminalSemanticLawPrefix_mem_carrier
      reward root returned hM hreward hreturned
  have hprefixedCarrier : prefixed ∈
      quittingTerminalSemanticCarrier reward :=
    terminalSemanticLawCarrier_fst_mem_carrier
      (prefixed, prefixedMass) hprefixedJoint
  have hprefixedReset : quittingTerminalSemanticDebt prefixed owner = 0 := by
    rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) returned.1 root owner hnash, hreset, mul_zero]
  have hdebtScale : quittingTerminalSemanticDebtSum prefixed =
      survival * quittingTerminalSemanticDebtSum returned.1 := by
    exact quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) returned.1 root hnash
  have hsourceLePrefixed : quittingTerminalSemanticDebtSum source ≤
      quittingTerminalSemanticDebtSum prefixed :=
    hminimum prefixed hprefixedCarrier
  have hsurvivalPositive : 0 < survival := by
    by_contra hnot
    have hsurvivalZero : survival = 0 :=
      le_antisymm (le_of_not_gt hnot)
        (quittingStationaryContinueMass_nonneg root)
    rw [hdebtScale, hsurvivalZero, zero_mul] at hsourceLePrefixed
    linarith
  have hprefixedIncidence :
      quittingTerminalTotalOpponentIncidenceMass owner prefixedMass =
        freshIncidence + survival * oldIncidence := by
    exact quittingTerminalTotalOpponentIncidenceMass_lawPrefix
      owner root returned.2
  have hprefixedIncidencePositive : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner prefixedMass := by
    rw [hprefixedIncidence]
    have hfreshNonneg : 0 ≤ freshIncidence :=
      quittingRootTotalOpponentIncidenceMass_nonneg owner root
    positivity
  have hminimal := hratio (prefixed, prefixedMass) hprefixedJoint
    hprefixedReset hprefixedIncidencePositive
  have hreturnedCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier returned hreturned
  have hreturnedDebtPositive : 0 <
      quittingTerminalSemanticDebtSum returned.1 :=
    hsourcePositive.trans_le (hminimum returned.1 hreturnedCarrier)
  have hcross : quittingTerminalSemanticDebtSum returned.1 *
      (freshIncidence + survival * oldIncidence) ≤
        (survival * quittingTerminalSemanticDebtSum returned.1) *
          oldIncidence := by
    have holdPositive : 0 < oldIncidence := hincidence
    have hnewPositive : 0 < freshIncidence + survival * oldIncidence := by
      rw [← hprefixedIncidence]
      exact hprefixedIncidencePositive
    change quittingTerminalSemanticDebtSum returned.1 / oldIncidence ≤
      quittingTerminalSemanticDebtSum prefixed /
        quittingTerminalTotalOpponentIncidenceMass owner prefixedMass at hminimal
    rw [hdebtScale, hprefixedIncidence,
      div_le_div_iff₀ holdPositive hnewPositive] at hminimal
    exact hminimal
  have hfreshNonneg : 0 ≤ freshIncidence :=
    quittingRootTotalOpponentIncidenceMass_nonneg owner root
  have hfreshZero : freshIncidence = 0 := by
    nlinarith
  exact hfreshZero

/-- Vanishing total fresh incidence kills each displayed opponent coordinate. -/
theorem quittingRootOpponentIncidenceMass_eq_zero_of_total_eq_zero
    (owner other : ι) (root : ι → PMF Bool)
    (hother : other ≠ owner)
    (htotal : quittingRootTotalOpponentIncidenceMass owner root = 0) :
    quittingRootOpponentIncidenceMass owner other root = 0 := by
  have hotherMem : other ∈ Finset.univ.erase owner := by
    simp [hother]
  have hcoordinateNonneg : 0 ≤
      quittingRootOpponentIncidenceMass owner other root := by
    unfold quittingRootOpponentIncidenceMass
    exact Finset.sum_nonneg fun terminal _ =>
      MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
        root terminal.val
  have hcoordinateLe :
      quittingRootOpponentIncidenceMass owner other root ≤
        quittingRootTotalOpponentIncidenceMass owner root := by
    unfold quittingRootTotalOpponentIncidenceMass
    exact Finset.single_le_sum
      (f := fun player =>
        quittingRootOpponentIncidenceMass owner player root)
      (fun player _ => by
        unfold quittingRootOpponentIncidenceMass
        exact Finset.sum_nonneg fun terminal _ =>
          MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
            root terminal.val)
      hotherMem
  rw [htotal] at hcoordinateLe
  exact le_antisymm hcoordinateLe hcoordinateNonneg

/-- Zero fresh incidence in one genuine opponent coordinate means that
opponent's entire Quit marginal is zero.  The proof selects the coalition of
all players with positive Quit hazard; if the displayed opponent had positive
hazard, that coalition would have positive product mass and would contribute
to the incidence sum. -/
theorem root_eq_pureContinue_of_opponentIncidence_eq_zero
    (owner other : ι) (root : ι → PMF Bool)
    (hother : other ≠ owner)
    (hzero : quittingRootOpponentIncidenceMass owner other root = 0) :
    root other = PMF.pure false := by
  by_cases hquitZero : (root other true).toReal = 0
  · exact pmf_eq_pure_false_of_apply_true_toReal_eq_zero
      (root other) hquitZero
  · have hquitPositive : 0 < (root other true).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hquitZero)
    let positivePlayers : Finset ι :=
      Finset.univ.filter fun player => 0 < (root player true).toReal
    have hotherMem : other ∈ positivePlayers := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ other, hquitPositive⟩
    have hpositivePlayers : positivePlayers.Nonempty :=
      ⟨other, hotherMem⟩
    let terminal : {S : Finset ι // S.Nonempty} :=
      ⟨positivePlayers, hpositivePlayers⟩
    have hterminalMassPositive : 0 <
        quittingRootCoalitionMass root terminal.val := by
      unfold quittingRootCoalitionMass Math.PMFProduct.coalitionMass
        quittingRootQuitRates
      apply mul_pos
      · exact Finset.prod_pos fun player hplayer =>
          (Finset.mem_filter.mp hplayer).2
      · apply Finset.prod_pos
        intro player hplayer
        have hplayerNotMem : player ∉ positivePlayers := by
          simpa using hplayer
        have hnotPositive : ¬ 0 < (root player true).toReal := by
          intro hpositive
          exact hplayerNotMem
            (Finset.mem_filter.mpr ⟨Finset.mem_univ player, hpositive⟩)
        have hplayerZero : (root player true).toReal = 0 :=
          le_antisymm (le_of_not_gt hnotPositive) ENNReal.toReal_nonneg
        rw [hplayerZero]
        norm_num
    have hterminalFilter : terminal ∈ Finset.univ.filter
        (fun candidate : {S : Finset ι // S.Nonempty} =>
          other ∈ candidate.val ∧ other ≠ owner) := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ terminal, hotherMem, hother⟩
    have hmassLe : quittingRootCoalitionMass root terminal.val ≤
        quittingRootOpponentIncidenceMass owner other root := by
      unfold quittingRootOpponentIncidenceMass
      exact Finset.single_le_sum
        (fun candidate _ =>
          MarkedAbsorptionCylinder.quittingRootCoalitionMass_nonneg
            root candidate.val)
        hterminalFilter
    rw [hzero] at hmassLe
    linarith

/-- Zero total opponent incidence is exactly the owner-only support condition:
every other player Continues purely.  The owner's own hazard is deliberately
unconstrained and may also be zero. -/
theorem opponents_pureContinue_of_rootTotalOpponentIncidence_eq_zero
    (owner : ι) (root : ι → PMF Bool)
    (htotal : quittingRootTotalOpponentIncidenceMass owner root = 0) :
    ∀ other, other ≠ owner → root other = PMF.pure false := by
  intro other hother
  exact root_eq_pureContinue_of_opponentIncidence_eq_zero owner other root hother
    (quittingRootOpponentIncidenceMass_eq_zero_of_total_eq_zero
      owner other root hother htotal)

/-- The secondary debt minimization upgrades owner-only support to literal
all-Continue.  Once fresh total opponent incidence vanishes, a cap prefix
scales both debt and old incidence by the same positive survival factor, so it
stays on the primary ratio-minimum slice.  Secondary debt minimality then
forces survival one. -/
theorem root_eq_allContinue_of_lexicographic_totalOpponentIncidence_minimal
    (source : QuittingTerminalSemanticPair ι)
    (returned : QuittingTerminalSemanticLawPoint ι)
    (owner : ι) (root : ι → PMF Bool) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum candidate)
    (hsourcePositive : 0 < quittingTerminalSemanticDebtSum source)
    (hreturned : returned ∈ quittingTerminalSemanticLawCarrier reward)
    (hreset : quittingTerminalSemanticDebt returned.1 owner = 0)
    (hincidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner returned.2)
    (hratio : ∀ candidate ∈ quittingTerminalSemanticLawCarrier reward,
      quittingTerminalSemanticDebt candidate.1 owner = 0 →
      0 < quittingTerminalTotalOpponentIncidenceMass owner candidate.2 →
      quittingTerminalSemanticDebtSum returned.1 /
          quittingTerminalTotalOpponentIncidenceMass owner returned.2 ≤
        quittingTerminalSemanticDebtSum candidate.1 /
          quittingTerminalTotalOpponentIncidenceMass owner candidate.2)
    (hsecondary : ∀ candidate ∈
      quittingTerminalSemanticLawCarrier reward,
      quittingTerminalSemanticDebt candidate.1 owner = 0 →
      0 < quittingTerminalTotalOpponentIncidenceMass owner candidate.2 →
      quittingTerminalSemanticDebtSum candidate.1 /
            quittingTerminalTotalOpponentIncidenceMass owner candidate.2 =
          quittingTerminalSemanticDebtSum returned.1 /
            quittingTerminalTotalOpponentIncidenceMass owner returned.2 →
      quittingTerminalSemanticDebtSum returned.1 ≤
        quittingTerminalSemanticDebtSum candidate.1)
    (hnash : IsεQuittingRootNash reward returned.1.2 0 root) :
    root = (quittingAllContinueRoot : ι → PMF Bool) := by
  let prefixed := quittingTerminalSemanticPrefix reward root returned.1
  let prefixedMass := quittingTerminalOutcomeLawPrefix root returned.2
  let survival := quittingStationaryContinueMass root
  let oldIncidence :=
    quittingTerminalTotalOpponentIncidenceMass owner returned.2
  have hfreshZero :=
    rootTotalOpponentIncidence_eq_zero_of_minimal_debt_div_incidence
      source returned owner root hM hreward hminimum hsourcePositive
        hreturned hreset hincidence hratio hnash
  have hprefixedJoint : (prefixed, prefixedMass) ∈
      quittingTerminalSemanticLawCarrier reward :=
    quittingTerminalSemanticLawPrefix_mem_carrier
      reward root returned hM hreward hreturned
  have hprefixedCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier
      (prefixed, prefixedMass) hprefixedJoint
  have hprefixedReset : quittingTerminalSemanticDebt prefixed owner = 0 := by
    rw [quittingTerminalSemanticDebt_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) returned.1 root owner hnash, hreset, mul_zero]
  have hdebtScale : quittingTerminalSemanticDebtSum prefixed =
      survival * quittingTerminalSemanticDebtSum returned.1 :=
    quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
      (reward := reward) returned.1 root hnash
  have hsourceLePrefixed : quittingTerminalSemanticDebtSum source ≤
      quittingTerminalSemanticDebtSum prefixed :=
    hminimum prefixed hprefixedCarrier
  have hsurvivalPositive : 0 < survival := by
    by_contra hnot
    have hsurvivalZero : survival = 0 :=
      le_antisymm (le_of_not_gt hnot)
        (quittingStationaryContinueMass_nonneg root)
    rw [hdebtScale, hsurvivalZero, zero_mul] at hsourceLePrefixed
    linarith
  have hincidenceScale :
      quittingTerminalTotalOpponentIncidenceMass owner prefixedMass =
        survival * oldIncidence := by
    rw [quittingTerminalTotalOpponentIncidenceMass_lawPrefix, hfreshZero,
      zero_add]
  have hprefixedIncidence : 0 <
      quittingTerminalTotalOpponentIncidenceMass owner prefixedMass := by
    rw [hincidenceScale]
    exact mul_pos hsurvivalPositive hincidence
  have hratioEq : quittingTerminalSemanticDebtSum prefixed /
          quittingTerminalTotalOpponentIncidenceMass owner prefixedMass =
        quittingTerminalSemanticDebtSum returned.1 /
          quittingTerminalTotalOpponentIncidenceMass owner returned.2 := by
    rw [hdebtScale, hincidenceScale]
    change survival * quittingTerminalSemanticDebtSum returned.1 /
        (survival * oldIncidence) =
      quittingTerminalSemanticDebtSum returned.1 / oldIncidence
    field_simp [hsurvivalPositive.ne', hincidence.ne']
  have hdebtMinimal : quittingTerminalSemanticDebtSum returned.1 ≤
      quittingTerminalSemanticDebtSum prefixed :=
    hsecondary (prefixed, prefixedMass) hprefixedJoint hprefixedReset
      hprefixedIncidence hratioEq
  have hreturnedCarrier :=
    terminalSemanticLawCarrier_fst_mem_carrier returned hreturned
  have hreturnedDebtPositive : 0 <
      quittingTerminalSemanticDebtSum returned.1 :=
    hsourcePositive.trans_le (hminimum returned.1 hreturnedCarrier)
  have hsurvivalLe : survival ≤ 1 :=
    quittingStationaryContinueMass_le_one root
  have hsurvivalOne : survival = 1 := by
    rw [hdebtScale] at hdebtMinimal
    nlinarith
  funext player
  have hpure := eq_pure_false_of_quittingStationaryContinueMass_eq_one
    hsurvivalOne player
  simpa [quittingAllContinueRoot] using hpure

/-- **Canonical positive-incidence cap plateau.**

Every positive-incidence reset excursion supplies a joint reset point which
still has positive total opponent incidence, but whose exact cap--Nash
correspondence is the singleton all-Continue root.  The all-Continue root is
itself exact Nash and fixes the semantic point.

This is a genuine plateau theorem, not a return theorem: the retained old law
contains opponent incidence, while no exact cap root creates absorption. -/
theorem exists_resetFace_positiveTotalIncidence_allContinueCapPlateau
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
      IsεQuittingRootNash reward returned.1.2 0
        (quittingAllContinueRoot : ι → PMF Bool) ∧
      quittingTerminalSemanticPrefix reward quittingAllContinueRoot
        returned.1 = returned.1 ∧
      ∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward returned.1.2 0 root →
          root = (quittingAllContinueRoot : ι → PMF Bool) := by
  obtain ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
      hsourceLe, hratio, hsecondary⟩ :=
    exists_resetFace_lexicographic_totalOpponentIncidence_minimizer
      source target mass owner hM hreward hminimum hsourcePositive
        htarget hreset hincidence
  have hallRoots : ∀ root : ι → PMF Bool,
      IsεQuittingRootNash reward returned.1.2 0 root →
        root = (quittingAllContinueRoot : ι → PMF Bool) := by
    intro root hnash
    exact root_eq_allContinue_of_lexicographic_totalOpponentIncidence_minimal
      source returned owner root hM hreward hminimum hsourcePositive
        hreturned hreturnedReset hreturnedIncidence hratio hsecondary hnash
  obtain ⟨root, hnash⟩ :=
    exists_isZeroQuittingRootNash (reward := reward) returned.1.2
  have hroot := hallRoots root hnash
  have hallContinueNash : IsεQuittingRootNash reward returned.1.2 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
    simpa [hroot] using hnash
  have hcap : ∀ player,
      reward (quittingSingletonTerminal player) player ≤
        returned.1.2 player :=
    (isZeroQuittingRootNash_allContinue_iff_singleton_le
      reward returned.1.2).1 hallContinueNash
  have hfixed :=
    quittingTerminalSemanticPrefix_allContinue_eq_of_singleton_le_cap
      (reward := reward) returned.1 hcap
  exact ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
    hsourceLe, hallContinueNash, hfixed, hallRoots⟩

/-- Existence form of the variational obstruction.  Starting from any
positive-incidence reset point, one obtains a joint reset point with positive
incidence at which every exact cap--Nash root has zero fresh incidence in the
same displayed opponent coordinate. -/
theorem exists_resetFace_debtIncidence_obstruction
    (source target : QuittingTerminalSemanticPair ι)
    (mass : QuittingTerminalOutcome ι → ℝ)
    (owner other : ι) {M : ℝ}
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
      quittingTerminalOpponentIncidenceMass owner other mass) :
    ∃ returned : QuittingTerminalSemanticLawPoint ι,
      returned ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebt returned.1 owner = 0 ∧
      0 < quittingTerminalOpponentIncidenceMass owner other returned.2 ∧
      quittingTerminalSemanticDebtSum source ≤
        quittingTerminalSemanticDebtSum returned.1 ∧
      ∀ root : ι → PMF Bool,
        IsεQuittingRootNash reward returned.1.2 0 root →
          quittingRootOpponentIncidenceMass owner other root = 0 := by
  obtain ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
      hsourceLe, hratio⟩ :=
    exists_resetFace_minimizer_debt_div_incidence
      source target mass owner other hM hreward hminimum hsourcePositive
        htarget hreset hincidence
  refine ⟨returned, hreturned, hreturnedReset, hreturnedIncidence,
    hsourceLe, ?_⟩
  intro root hnash
  exact rootOpponentIncidence_eq_zero_of_minimal_debt_div_incidence
    source returned owner other root hM hreward hminimum hsourcePositive
      hreturned hreturnedReset hreturnedIncidence hratio hnash

/-! ## What the quotient says about a partial reset -/

/-- **Conditional partial-reset cut at a debt/incidence minimizer.**

Suppose a candidate move stays on the reset face used by the quotient and
retains at least the `1 - lambda` fraction of the selected incidence.  If it
decreases the moving player's debt by `gain`, then at least

`gain - lambda * D`

is transferred in aggregate to the other player coordinates.

The qualification is essential.  The landed literal partial-reset theorem
retains incidence, but a reset by a different player need not preserve the
original zero-debt coordinate, so quotient minimality cannot automatically be
applied to it.  Even when the face is preserved, the displayed lower bound is
positive only when the local gain exceeds `lambda * D`. -/
theorem partialTransferCut_of_minimal_debt_div_incidence
    (returned candidate : QuittingTerminalSemanticLawPoint ι)
    (resetOwner mover owner other : ι) (lambda gain : ℝ)
    (hreturnedIncidence : 0 <
      quittingTerminalOpponentIncidenceMass owner other returned.2)
    (hreturnedDebt : 0 < quittingTerminalSemanticDebtSum returned.1)
    (hratio : ∀ point ∈ quittingTerminalSemanticLawCarrier reward,
      quittingTerminalSemanticDebt point.1 resetOwner = 0 →
      0 < quittingTerminalOpponentIncidenceMass owner other point.2 →
      quittingTerminalSemanticDebtSum returned.1 /
          quittingTerminalOpponentIncidenceMass owner other returned.2 ≤
        quittingTerminalSemanticDebtSum point.1 /
          quittingTerminalOpponentIncidenceMass owner other point.2)
    (hcandidate : candidate ∈ quittingTerminalSemanticLawCarrier reward)
    (hcandidateReset :
      quittingTerminalSemanticDebt candidate.1 resetOwner = 0)
    (hlambdaStrict : lambda < 1)
    (hincidenceRetention :
      (1 - lambda) *
          quittingTerminalOpponentIncidenceMass owner other returned.2 ≤
        quittingTerminalOpponentIncidenceMass owner other candidate.2)
    (hdecrease : quittingTerminalSemanticDebt candidate.1 mover =
      quittingTerminalSemanticDebt returned.1 mover - gain) :
    gain - lambda * quittingTerminalSemanticDebtSum returned.1 ≤
      ∑ recipient ∈ Finset.univ.erase mover,
        quittingTerminalSemanticDebtChange
          returned.1 candidate.1 recipient := by
  let oldIncidence :=
    quittingTerminalOpponentIncidenceMass owner other returned.2
  let newIncidence :=
    quittingTerminalOpponentIncidenceMass owner other candidate.2
  let oldDebt := quittingTerminalSemanticDebtSum returned.1
  let newDebt := quittingTerminalSemanticDebtSum candidate.1
  have hnewIncidence : 0 < newIncidence := by
    have hfactor : 0 < 1 - lambda := sub_pos.mpr hlambdaStrict
    exact (mul_pos hfactor hreturnedIncidence).trans_le hincidenceRetention
  have hratioCandidate :=
    hratio candidate hcandidate hcandidateReset hnewIncidence
  have hcross : oldDebt * newIncidence ≤ newDebt * oldIncidence := by
    rw [show oldDebt = quittingTerminalSemanticDebtSum returned.1 by rfl,
      show newDebt = quittingTerminalSemanticDebtSum candidate.1 by rfl,
      show oldIncidence =
        quittingTerminalOpponentIncidenceMass owner other returned.2 by rfl,
      show newIncidence =
        quittingTerminalOpponentIncidenceMass owner other candidate.2 by rfl,
      ← div_le_div_iff₀ hreturnedIncidence hnewIncidence]
    exact hratioCandidate
  have hnewDebtLower : (1 - lambda) * oldDebt ≤ newDebt := by
    have holdIncidence : 0 < oldIncidence := hreturnedIncidence
    have hretention : (1 - lambda) * oldIncidence ≤ newIncidence :=
      hincidenceRetention
    nlinarith
  have hsum := Finset.sum_erase_add Finset.univ
    (fun player => quittingTerminalSemanticDebtChange
      returned.1 candidate.1 player)
    (Finset.mem_univ mover)
  have htotal : (∑ player,
      quittingTerminalSemanticDebtChange returned.1 candidate.1 player) =
      newDebt - oldDebt := by
    dsimp only [newDebt, oldDebt]
    unfold quittingTerminalSemanticDebtChange
      quittingTerminalSemanticDebtSum
    rw [Finset.sum_sub_distrib]
  have hmover : quittingTerminalSemanticDebtChange
      returned.1 candidate.1 mover = -gain := by
    unfold quittingTerminalSemanticDebtChange
    rw [hdecrease]
    ring
  rw [htotal, hmover] at hsum
  nlinarith

end GameTheory
