/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetFaceReprojection

/-!
# Normalized carrier germs at an unbounded reset reprojection

Failure of every linear reset-face penalty is not merely a family of unrelated
points.  Compactness extracts one jointly co-realized semantic/law contact and
a sequence converging to it.  Reset-owner debt is negligible relative to the
positive surface-tension violation along this sequence.  At the limit both
quantities vanish.

On the separated reset-face branch the contact retains strictly positive
opponent incidence.  It also retains the exact reward moment of its displayed
terminal law.  Thus the obstruction cannot escape through the zero-incidence
boundary or through a semantic/law projection mismatch.

This carrier germ is not a Bellman charge-tangent packet.  Its approach
points are limits of executable profiles, but no common chronological window
or positive absorption scale relates consecutive points.  In particular the
existing support-entry and negative-vertex tangent compilers cannot be applied
until such an incidence is supplied.
-/

noncomputable section

namespace GameTheory

open Filter Set
open scoped Topology

variable {X : Type} [TopologicalSpace X] [FirstCountableTopology X]

/-! ## Compact normalized contact extraction -/

/-- Arbitrarily large failures of a linear face penalty concentrate at a
contact point.  The face coordinate is asymptotically negligible relative to
the positive violation. -/
theorem exists_normalized_contact_germ_of_compact
    (carrier : Set X) (hcompact : IsCompact carrier)
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
      (∀ n, path n ∈ carrier) ∧
      Tendsto path atTop (nhds contact) ∧
      (∀ n, 0 < face (path n)) ∧
      (∀ n, 0 < tension (path n)) ∧
      Tendsto (fun n ↦ face (path n) / tension (path n))
        atTop (nhds 0) ∧
      face contact = 0 ∧ tension contact = 0 := by
  classical
  choose witness hwitnessCarrier hwitnessFace hwitnessTension
      hwitnessRatio using fun n : ℕ =>
    hobstruction ((n : ℝ) + 1) (by positivity)
  obtain ⟨contact, hcontact, subseq, hsubseq, hpath⟩ :=
    hcompact.tendsto_subseq hwitnessCarrier
  let path : ℕ → X := fun n ↦ witness (subseq n)
  have hpathCarrier : ∀ n, path n ∈ carrier :=
    fun n ↦ hwitnessCarrier (subseq n)
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
    have hupper : Tendsto (fun n : ℕ =>
        1 / ((subseq n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hsubseq.tendsto_atTop
    exact squeeze_zero
      (fun n ↦ div_nonneg (hfaceNonneg (path n) (hpathCarrier n))
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
  exact ⟨contact, path, hcontact, hpathCarrier, hpath, hpathFace,
    hpathTension, hratio, hfaceContact, htensionContact⟩

/-! ## Game-facing surface-tension germ -/

variable {iota : Type} [Fintype iota] [DecidableEq iota]
variable {reward : {S : Finset iota // S.Nonempty} → Payoff iota}

/-- Surface-tension violation relative to a separated reset-face selector. -/
def quittingResetReprojectionTension
    (source : QuittingTerminalSemanticPair iota)
    (returned point : QuittingTerminalSemanticLawPoint iota)
    (owner : iota) : ℝ :=
  ((quittingTerminalSemanticDebtSum returned.1 -
        quittingTerminalSemanticDebtSum source) /
      quittingTerminalTotalOpponentIncidenceMass owner returned.2) *
      quittingTerminalTotalOpponentIncidenceMass owner point.2 -
    (quittingTerminalSemanticDebtSum point.1 -
      quittingTerminalSemanticDebtSum source)

/-- **Unbounded reprojection produces a positive-incidence joint carrier
germ.**

If no global linear face penalty exists on a genuinely separated reset face,
there is one joint semantic/law contact approached by positive off-face
violations.  Reset debt divided by violation tends to zero.  The contact has
zero reset debt, exact surface-tension equality, strictly positive opponent
incidence, and the exact reward moment of its displayed law.

The last two facts rule out the two elementary escapes (law projection and
zero-incidence collapse).  The hypotheses furnish no Bellman-window incidence
identifying this carrier germ with a charge-normalized strategic tangent. -/
theorem exists_positiveIncidence_normalizedReprojectionGerm
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
      ∃ path : ℕ → QuittingTerminalSemanticLawPoint iota,
      contact ∈ quittingTerminalSemanticLawCarrier reward ∧
      (∀ n, path n ∈ quittingTerminalSemanticLawCarrier reward) ∧
      Tendsto path atTop (nhds contact) ∧
      (∀ n, 0 < quittingTerminalSemanticDebt (path n).1 owner) ∧
      (∀ n, 0 < quittingResetReprojectionTension
        source returned (path n) owner) ∧
      Tendsto (fun n ↦
        quittingTerminalSemanticDebt (path n).1 owner /
          quittingResetReprojectionTension source returned (path n) owner)
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
  obtain ⟨contact, path, hcontact, hpathCarrier, hpath,
      hpathFace, hpathTension, hratio, hcontactFace,
      hcontactTension⟩ :=
    exists_normalized_contact_germ_of_compact
      (quittingTerminalSemanticLawCarrier reward)
      (quittingTerminalSemanticLawCarrier_isCompact reward hM hreward)
      face tension hfaceContinuous htensionContinuous hfaceNonneg
        hsupport hobstruction
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
  exact ⟨contact, path, hcontact, hpathCarrier, hpath, hpathFace,
    hpathTension, hratio, hcontactFace, hcontactTension,
    hcontactIncidence, hmoment⟩

end GameTheory
