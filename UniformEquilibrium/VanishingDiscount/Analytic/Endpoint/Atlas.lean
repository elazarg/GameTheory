/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Adaptive.LocalResponseAtlas
import UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.CirculationEndpointAlternative
import UniformEquilibrium.VanishingDiscount.Analytic.Endpoint.FiniteBiasEndpointAlternative
import UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.EndpointAlternative
import UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.AnalyticDeflationTerminal
import UniformEquilibrium.VanishingDiscount.Analytic.PlayerNeutral.ReachableClassAlternative
import UniformEquilibrium.VanishingDiscount.Analytic.PlayerOwned.CommonPotentialCalendarAccount
import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.ProcessedJetAccountBoundary
import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.ProcessedHarmonicStateAccount
import UniformEquilibrium.VanishingDiscount.Analytic.Accounting.PublicActionFrequencyResponse

/-!
# Honest analytic endpoint leaves for the adaptive obstruction atlas

This file packages the finite analytic endpoint alternatives without
silently promoting intermediate evidence to an adaptive atlas step.

There are four logically different statuses:

* `semanticClose` already proves the desired uniform-payoff statement;
* `harmonicRankDecrease` carries a genuine strict harmonic-rank inequality,
  but still needs a child entry, target, and resume map;
* the remaining constructors carry named obstruction data together with the
  exact kind of reconstruction still required;
* no raw response, bounded potential, span membership, circulation, or
  zero-pairing certificate is called a completed account or local
  punishment.

In particular, the strict player-neutral drift branch is refined at the
actual public entry.  Its residual family yields either a reachable proper
support class, a reachable full-support class, or a bounded reachable
potential.  The first branch contains a strict support-cardinality
inequality, while the latter two remain explicit obstructions.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math Math.OnlineLearning Math.Probability Set
open Math.Probability.AnalyticScaledChargedOccupationPotential
open GameTheory.StochasticGame.AnalyticBellmanGerm.AnalyticScaledChargedOccupationPotential

variable {ι : Type} {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [Fintype ι] [DecidableEq ι]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]

namespace AnalyticBellmanGerm

local instance analyticEndpointAtlasIndexDecidableEq
    (germ : G.AnalyticBellmanGerm) (who : ι) :
    DecidableEq (germ.PlayerNeutralOccupationIndex who) :=
  Classical.decEq _

/-- A missing credibility theorem is a typed map from the supplied
operational response to the actual adaptive certificate at the current
entry and target. -/
structure CredibilityReconstructionAt
    (germ : G.AnalyticBellmanGerm) (entry : G.State)
    (error : ℝ) (Response : Type) : Type where
  closeResponse :
    Response →
      G.IsAdaptivePotentialCertificateAt
        entry (germ.endpointValue entry) error

/-- A missing account theorem must consume the displayed endpoint evidence
all the way into the current adaptive certificate.  Merely constructing a
bounded scalar account is not enough to inhabit this interface. -/
structure AccountDischargeReconstructionAt
    (germ : G.AnalyticBellmanGerm) (entry : G.State)
    (error : ℝ) (Evidence : Type) : Type where
  discharge :
    Evidence →
      G.IsAdaptivePotentialCertificateAt
        entry (germ.endpointValue entry) error

/-- A genuine analytic rank inequality still needs a child problem and a
resume map.  The recursive atlas supplies the child certificate; this
interface records exactly how it would be transported back to the current
entry and target. -/
structure RankChildReconstructionAt
    (germ : G.AnalyticBellmanGerm) (entry : G.State)
    (error : ℝ) (RankEvidence : Type) : Type where
  childEntry : G.State
  childTarget : Payoff ι
  resume :
    RankEvidence →
      G.IsAdaptivePotentialCertificateAt
          childEntry childTarget error →
        G.IsAdaptivePotentialCertificateAt
          entry (germ.endpointValue entry) error

/-- The reachable-class branch additionally needs legal entry, complete
payoff-vector target transport, and a credible parent continuation. -/
structure EntryTargetReconstructionAt
    (germ : G.AnalyticBellmanGerm) (entry : G.State)
    (error : ℝ) (Evidence : Type) : Type where
  closeEntryTarget :
    Evidence →
      G.IsAdaptivePotentialCertificateAt
        entry (germ.endpointValue entry) error

/-- Full support has several legitimate possible exits: an independent
rank coordinate, whole-target identification followed by a recurrent
continuation, or a discharged realized account.  This neutral interface
does not prejudge which one succeeds. -/
structure FullSupportReconstructionAt
    (germ : G.AnalyticBellmanGerm) (entry : G.State)
    (error : ℝ) (Evidence : Type) : Type where
  resolveFullSupport :
    Evidence →
      G.IsAdaptivePotentialCertificateAt
        entry (germ.endpointValue entry) error

/-- Zero pairing can feed a harmonic-rank argument, a legal recurrent
child, or a realized-account argument.  It is therefore kept distinct from
the narrower account-discharge interface. -/
structure ZeroPairingReconstructionAt
    (germ : G.AnalyticBellmanGerm) (entry : G.State)
    (error : ℝ) (Evidence : Type) : Type where
  resolveZeroPairing :
    Evidence →
      G.IsAdaptivePotentialCertificateAt
        entry (germ.endpointValue entry) error

/-- Exact finite-bias evidence in the operational public-response branch. -/
structure FiniteBiasPublicResponseData
    (germ : G.AnalyticBellmanGerm)
    (seed : germ.FiniteBiasSeed) where
  correction : G.State → Payoff ι
  who : ι
  response : germ.ContinuationNeutralAction who
  forcing :
    G.finkBellmanForcingVector
        germ.endpointValue seed.H germ.endpointFinkPoint =
      -G.finkContinuationResidualVector
        correction germ.endpointFinkPoint
  publicResponse :
    Nonempty
      (G.FinkPublicConstraintResponse
        germ.endpointFinkPoint (seed.H - correction)
        response.source who response.1.2)

/-- A fixed actual forward response extracted from a positive analytic
circulation on one player's full operational family.  Its missing step is
credibility at the current public entry and target. -/
structure PlayerOwnedAnalyticPublicResponseData
    (germ : G.AnalyticBellmanGerm) where
  bias : G.State → Payoff ι
  owner : ι
  circulation :
    AnalyticPositiveChargedCirculation
      (germ.rawOwnerAnalyticOccupationColumn owner)
      (germ.rawPlayerOwnedOccupationCharge bias owner)
  lowerOrder :
    PlayerOwnedLowerOrderCirculationData
      germ bias owner circulation
  tiedResponse :
    CirculationTiedAnalyticForwardFinkPublicResponse
      germ bias owner circulation

/-- The synchronized all-player potential branch of the full-owner
charged-flow alternative.  The analytic potential already controls every
pure action of every owner; turning its behavior-calendar bounds into the
current adaptive certificate remains an account-discharge obligation. -/
structure PlayerOwnedCommonScaledPotentialData
    (germ : G.AnalyticBellmanGerm) where
  bias : G.State → Payoff ι
  potential :
    AnalyticOwnerScaledChargedOccupationPotential
      (fun who => OwnerOccupationIndex G who)
      (fun who => germ.rawOwnerAnalyticOccupationColumn who)
      (fun who => germ.rawPlayerOwnedOccupationCharge bias who)

namespace PlayerOwnedCommonScaledPotentialData

/-- Specialize the synchronized potential to one owner without changing its
common pole-clearing order. -/
def ownerPotential
    {germ : G.AnalyticBellmanGerm}
    (data : PlayerOwnedCommonScaledPotentialData germ)
    (who : ι) :
    AnalyticScaledChargedOccupationPotential
      (germ.rawOwnerAnalyticOccupationColumn who)
      (germ.rawPlayerOwnedOccupationCharge data.bias who) :=
  CommonPlayerOwnedPotentialCalendar.ownerPotential
    germ data.bias data.potential who

/-- Every owner specialization has the existing arbitrary-behavior,
all-horizon sublinear calendar account. -/
theorem exists_ownerBehaviorCalendarAccount
    {germ : G.AnalyticBellmanGerm}
    (data : PlayerOwnedCommonScaledPotentialData germ)
    (who : ι) :
    ∃ (startEpoch : ℕ)
        (valid :
          ∀ k : ℕ,
            shiftedUniversalEpochScale startEpoch k ∈
              Ioo (0 : ℝ) germ.radius),
      ∀ (dev : G.BehaviorStrategy who) initial T,
        expectedPlayerOwnedBehaviorCalendarCharge
            germ data.bias who startEpoch valid dev initial T ≤
          playerOwnedPotentialCalendarBudget
            germ data.bias who (data.ownerPotential who) startEpoch T ∧
        IsAsymptoticallySublinear
          (playerOwnedPotentialCalendarBudget
            germ data.bias who (data.ownerPotential who) startEpoch) :=
  AnalyticScaledChargedOccupationPotential.exists_playerOwnedBehaviorCalendarAccount
    germ data.bias who (data.ownerPotential who)

/-- The common potential supplies one calendar burn-in shared by all
players, while retaining an owner-specific sublinear potential budget. -/
theorem exists_commonBehaviorCalendarAccount
    {germ : G.AnalyticBellmanGerm}
    (data : PlayerOwnedCommonScaledPotentialData germ) :
    ∃ (startEpoch : ℕ)
        (valid :
          ∀ k : ℕ,
            shiftedUniversalEpochScale startEpoch k ∈
              Ioo (0 : ℝ) germ.radius),
      ∀ (who : ι) (dev : G.BehaviorStrategy who) initial T,
        expectedPlayerOwnedBehaviorCalendarCharge
            germ data.bias who startEpoch valid dev initial T ≤
          playerOwnedPotentialCalendarBudget
            germ data.bias who (data.ownerPotential who)
            startEpoch T ∧
        IsAsymptoticallySublinear
          (playerOwnedPotentialCalendarBudget
            germ data.bias who (data.ownerPotential who)
            startEpoch) :=
  CommonPlayerOwnedPotentialCalendar.exists_commonPlayerOwnedBehaviorCalendarAccount
    germ data.bias data.potential

end PlayerOwnedCommonScaledPotentialData

/-- A processed finite-bias obstruction, including its forcing
decomposition.  Span membership alone does not provide a realized account. -/
structure FiniteBiasProcessedObstructionData
    (germ : G.AnalyticBellmanGerm)
    (seed : germ.FiniteBiasSeed)
    (span : germ.EndpointHarmonicJetSpan) where
  obstruction : G.State → Payoff ι
  correction : G.State → Payoff ι
  obstruction_ne_zero : obstruction ≠ 0
  processed : obstruction ∈ span.carrier
  harmonic :
    G.finkContinuationResidualVector
      obstruction germ.endpointFinkPoint = 0
  forcing :
    G.finkBellmanForcingVector
        germ.endpointValue seed.H germ.endpointFinkPoint =
      obstruction -
        G.finkContinuationResidualVector
          correction germ.endpointFinkPoint

/-- A genuine strict decrease in the finite endpoint-harmonic rank. -/
structure HarmonicRankDecreaseData
    (germ : G.AnalyticBellmanGerm)
    (span : germ.EndpointHarmonicJetSpan) where
  direction : G.State → Payoff ι
  harmonic : direction ∈ germ.endpointHarmonicSubmodule
  decrease : (span.extend direction harmonic).rank < span.rank

/-- A processed lower-value jet together with the proof that adjoining it
does not decrease the harmonic rank. -/
structure ProcessedLowerValueJetData
    (germ : G.AnalyticBellmanGerm)
    (span : germ.EndpointHarmonicJetSpan) where
  jet : germ.LowerValueJet
  processed : jet.factor 0 ∈ span.carrier
  rank_stagnates :
    (span.extend
        (jet.factor 0)
        (span.carrier_le processed)).rank =
      span.rank

/-- Proper-support residual class data.  `proper` is a real strict
cardinality inequality, but the public child still needs the typed
entry/target reconstruction above. -/
structure PlayerNeutralProperSupportData
    (germ : G.AnalyticBellmanGerm) (entry : G.State) where
  B : G.State → Payoff ι
  who : ι
  P : AnalyticScaledChargedOccupationPotential
    (germ.rawPlayerNeutralOccupationColumn who)
    (germ.rawPlayerNeutralOccupationCharge B who)
  anchor : G.State
  jet : GaugeFixedPotentialJet P anchor
  drift : germ.PlayerNeutralStrictLeadingDriftWithBudget B who jet
  reachable : drift.drift.ReachablePositiveClassData entry
  proper :
    reachable.positiveClass.HasProperSupportRankDescent

/-- Full-support residual class data.  This branch has no support-rank
decrease; regeneration and positive charge do not close it. -/
structure PlayerNeutralFullSupportData
    (germ : G.AnalyticBellmanGerm) (entry : G.State) where
  B : G.State → Payoff ι
  who : ι
  P : AnalyticScaledChargedOccupationPotential
    (germ.rawPlayerNeutralOccupationColumn who)
    (germ.rawPlayerNeutralOccupationCharge B who)
  anchor : G.State
  jet : GaugeFixedPotentialJet P anchor
  drift : germ.PlayerNeutralStrictLeadingDriftWithBudget B who jet
  reachable : drift.drift.ReachablePositiveClassData entry
  fullSupport :
    reachable.positiveClass.IsFullActiveSupportClass

/-- A bounded reachable residual potential.  It is exact potential evidence,
not yet a discharged strategic account. -/
structure PlayerNeutralBoundedPotentialData
    (germ : G.AnalyticBellmanGerm) (entry : G.State) where
  B : G.State → Payoff ι
  who : ι
  P : AnalyticScaledChargedOccupationPotential
    (germ.rawPlayerNeutralOccupationColumn who)
    (germ.rawPlayerNeutralOccupationCharge B who)
  anchor : G.State
  jet : GaugeFixedPotentialJet P anchor
  drift : germ.PlayerNeutralStrictLeadingDriftWithBudget B who jet
  boundedPotential :
    EntryReachableBoundedChargePotential
      drift.drift.zeroDriftKernel
      drift.drift.zeroDriftSource
      drift.drift.zeroDriftCharge entry

/-- A processed player-neutral leading payoff.  This is span membership,
not a realized account discharge. -/
structure PlayerNeutralProcessedHarmonicData
    (germ : G.AnalyticBellmanGerm)
    (span : germ.EndpointHarmonicJetSpan) where
  B : G.State → Payoff ι
  who : ι
  P : AnalyticScaledChargedOccupationPotential
    (germ.rawPlayerNeutralOccupationColumn who)
    (germ.rawPlayerNeutralOccupationCharge B who)
  anchor : G.State
  jet : GaugeFixedPotentialJet P anchor
  processed :
    germ.playerNeutralPotentialJetLeadingPayoff who jet ∈
      span.carrier

/-- The terminal analytic-circulation branch still needs a legal public
entry, whole-vector target transport, and credibility for its owned
response. -/
structure PlayerNeutralAnalyticTerminalEntryTargetData
    (germ : G.AnalyticBellmanGerm) where
  B : G.State → Payoff ι
  who : ι
  initial :
    FiniteDeflationState
      (germ.PlayerNeutralOccupationIndex who)
  terminalAnchor : G.State
  data :
    PlayerNeutralAnalyticCirculationTerminalData
      germ B who initial terminalAnchor

/-- The zero-pairing terminal branch keeps its exact active harmonicity.
It is not full-kernel harmonicity and does not itself provide a child or
account discharge. -/
structure PlayerNeutralZeroPairingObstructionData
    (germ : G.AnalyticBellmanGerm) where
  B : G.State → Payoff ι
  who : ι
  initial :
    FiniteDeflationState
      (germ.PlayerNeutralOccupationIndex who)
  terminalAnchor : G.State
  data :
    PlayerNeutralZeroPairingTerminalData
      germ B who initial terminalAnchor

/-- Honest finite endpoint leaves.

The names identify the mathematical status of each branch.  In particular,
only `semanticClose` is terminal without more construction, and
`harmonicRankDecrease` records only the analytic rank component of an atlas
descent. -/
inductive AnalyticEndpointAtlasLeaf
    (germ : G.AnalyticBellmanGerm)
    (span : germ.EndpointHarmonicJetSpan)
    (entry : G.State) : Type _
  | semanticClose
      (uniform :
        G.IsUniformEquilibriumPayoff
          entry (germ.endpointValue entry))
  | publicResponseCredibility
      {seed : germ.FiniteBiasSeed}
      (data : FiniteBiasPublicResponseData germ seed)
  | playerOwnedAnalyticResponseCredibility
      (data : PlayerOwnedAnalyticPublicResponseData germ)
  | playerOwnedCommonPotentialAccount
      (data : PlayerOwnedCommonScaledPotentialData germ)
  | finiteBiasProcessedAccount
      {seed : germ.FiniteBiasSeed}
      (data : FiniteBiasProcessedObstructionData germ seed span)
  | processedJetAccount
      (data : ProcessedLowerValueJetData germ span)
  | harmonicRankDecrease
      (data : HarmonicRankDecreaseData germ span)
  | transitionMonitorCredibility
      (charge : germ.StateKernelMonitorPowerCharge)
  | playerNeutralProperSupportEntryTarget
      (data : PlayerNeutralProperSupportData germ entry)
  | playerNeutralFullSupport
      (data : PlayerNeutralFullSupportData germ entry)
  | playerNeutralBoundedPotentialAccount
      (data : PlayerNeutralBoundedPotentialData germ entry)
  | playerNeutralProcessedAccount
      (data : PlayerNeutralProcessedHarmonicData germ span)
  | terminalAnalyticCirculationEntryTarget
      (data : PlayerNeutralAnalyticTerminalEntryTargetData germ)
  | terminalZeroPairing
      (data : PlayerNeutralZeroPairingObstructionData germ)

namespace AnalyticEndpointAtlasLeaf

variable
    {germ : G.AnalyticBellmanGerm}
    {span : germ.EndpointHarmonicJetSpan}
    {entry : G.State}

/-- The exact reconstruction type still required by a leaf at one
accuracy.  The semantic branch needs no reconstruction.  Every other branch
names either a credibility map, an account discharge, a rank-child resume,
or an entry/target reconstruction. -/
def RequiredReconstructionAt
    (leaf : germ.AnalyticEndpointAtlasLeaf span entry)
    (error : ℝ) : Type _ :=
  match leaf with
  | .semanticClose _ => PUnit
  | .publicResponseCredibility _ =>
      CredibilityReconstructionAt germ entry error
        (Σ seed : germ.FiniteBiasSeed,
          FiniteBiasPublicResponseData germ seed)
  | .playerOwnedAnalyticResponseCredibility _ =>
      CredibilityReconstructionAt germ entry error
        (PlayerOwnedAnalyticPublicResponseData germ)
  | .playerOwnedCommonPotentialAccount _ =>
      AccountDischargeReconstructionAt germ entry error
        (PlayerOwnedCommonScaledPotentialData germ)
  | .finiteBiasProcessedAccount _ =>
      AccountDischargeReconstructionAt germ entry error
        (Σ seed : germ.FiniteBiasSeed,
          FiniteBiasProcessedObstructionData germ seed span)
  | .processedJetAccount _ =>
      AccountDischargeReconstructionAt germ entry error
        (ProcessedLowerValueJetData germ span)
  | .harmonicRankDecrease _ =>
      RankChildReconstructionAt germ entry error
        (HarmonicRankDecreaseData germ span)
  | .transitionMonitorCredibility _ =>
      CredibilityReconstructionAt germ entry error
        germ.StateKernelMonitorPowerCharge
  | .playerNeutralProperSupportEntryTarget _ =>
      EntryTargetReconstructionAt germ entry error
        (PlayerNeutralProperSupportData germ entry)
  | .playerNeutralFullSupport _ =>
      FullSupportReconstructionAt germ entry error
        (PlayerNeutralFullSupportData germ entry)
  | .playerNeutralBoundedPotentialAccount _ =>
      AccountDischargeReconstructionAt germ entry error
        (PlayerNeutralBoundedPotentialData germ entry)
  | .playerNeutralProcessedAccount _ =>
      AccountDischargeReconstructionAt germ entry error
        (PlayerNeutralProcessedHarmonicData germ span)
  | .terminalAnalyticCirculationEntryTarget _ =>
      EntryTargetReconstructionAt germ entry error
        (PlayerNeutralAnalyticTerminalEntryTargetData germ)
  | .terminalZeroPairing _ =>
      ZeroPairingReconstructionAt germ entry error
        (PlayerNeutralZeroPairingObstructionData germ)

/-- A leaf is fully resolved at one accuracy only when its named
reconstruction is present.  The rank branch additionally needs the child
certificate that a well-founded atlas recursion would supply. -/
def ResolutionAt
    (leaf : germ.AnalyticEndpointAtlasLeaf span entry)
    (error : ℝ) : Type _ :=
  match leaf with
  | .harmonicRankDecrease _ =>
      { reconstruction :
          RankChildReconstructionAt germ entry error
            (HarmonicRankDecreaseData germ span) //
        G.IsAdaptivePotentialCertificateAt
          reconstruction.childEntry reconstruction.childTarget error }
  | _ => leaf.RequiredReconstructionAt error

/-- Once the explicitly named reconstruction is supplied, a leaf either
already gives the semantic theorem or gives the current adaptive
certificate.  This eliminator is intentionally impossible to call with
only raw response, span, potential, circulation, or rank data. -/
theorem semanticClose_or_certificate_of_resolution
    (leaf : germ.AnalyticEndpointAtlasLeaf span entry)
    (error : ℝ)
    (resolution : leaf.ResolutionAt error) :
    G.IsUniformEquilibriumPayoff
        entry (germ.endpointValue entry) ∨
      G.IsAdaptivePotentialCertificateAt
        entry (germ.endpointValue entry) error := by
  cases leaf with
  | semanticClose uniform =>
      exact Or.inl uniform
  | publicResponseCredibility data =>
      exact Or.inr (resolution.closeResponse ⟨_, data⟩)
  | playerOwnedAnalyticResponseCredibility data =>
      exact Or.inr (resolution.closeResponse data)
  | playerOwnedCommonPotentialAccount data =>
      exact Or.inr (resolution.discharge data)
  | finiteBiasProcessedAccount data =>
      exact Or.inr (resolution.discharge ⟨_, data⟩)
  | processedJetAccount data =>
      exact Or.inr (resolution.discharge data)
  | harmonicRankDecrease data =>
      obtain ⟨reconstruction, childCertificate⟩ := resolution
      exact Or.inr
        (reconstruction.resume data childCertificate)
  | transitionMonitorCredibility charge =>
      exact Or.inr (resolution.closeResponse charge)
  | playerNeutralProperSupportEntryTarget data =>
      exact Or.inr (resolution.closeEntryTarget data)
  | playerNeutralFullSupport data =>
      exact Or.inr (resolution.resolveFullSupport data)
  | playerNeutralBoundedPotentialAccount data =>
      exact Or.inr (resolution.discharge data)
  | playerNeutralProcessedAccount data =>
      exact Or.inr (resolution.discharge data)
  | terminalAnalyticCirculationEntryTarget data =>
      exact Or.inr (resolution.closeEntryTarget data)
  | terminalZeroPairing data =>
      exact Or.inr (resolution.resolveZeroPairing data)

/-- A finite-bias endpoint alternative converts exhaustively to one honest
atlas leaf. -/
theorem ofFiniteBiasSeed
    (seed : germ.FiniteBiasSeed) :
    Nonempty (germ.AnalyticEndpointAtlasLeaf span entry) := by
  rcases
      seed.uniformPayoff_or_publicResponse_or_processedObstruction_or_rankDecrease
        span entry with
    uniform | response | processed | decrease
  · exact ⟨.semanticClose uniform⟩
  · obtain ⟨correction, who, action, forcing, publicResponse⟩ := response
    exact ⟨.publicResponseCredibility {
      correction := correction
      who := who
      response := action
      forcing := forcing
      publicResponse := publicResponse
    }⟩
  · obtain ⟨obstruction, correction, nonzero, membership,
      harmonic, forcing⟩ := processed
    exact ⟨.finiteBiasProcessedAccount {
      obstruction := obstruction
      correction := correction
      obstruction_ne_zero := nonzero
      processed := membership
      harmonic := harmonic
      forcing := forcing
    }⟩
  · obtain ⟨obstruction, correction, harmonic, nonzero, _,
      _, decrease⟩ := decrease
    exact ⟨.harmonicRankDecrease {
      direction := obstruction
      harmonic := harmonic
      decrease := decrease
    }⟩

/-- The complete first analytic hierarchy response, with finite bias
further classified, converts to an honest endpoint leaf. -/
theorem ofFirstHierarchyResponse
    (response : germ.FirstHierarchyResponse span) :
    Nonempty (germ.AnalyticEndpointAtlasLeaf span entry) := by
  cases response with
  | finiteBias seed =>
      exact ofFiniteBiasSeed seed
  | processedJet jet processed =>
      exact ⟨.processedJetAccount {
        jet := jet
        processed := processed
        rank_stagnates :=
          jet.processed_extend_rank_eq span processed
      }⟩
  | lowerRank jet harmonic decreases =>
      exact ⟨.harmonicRankDecrease {
        direction := jet.factor 0
        harmonic := harmonic
        decrease := decreases
      }⟩
  | transitionMonitor charge =>
      exact ⟨.transitionMonitorCredibility charge⟩

/-- Every analytic Bellman germ has one finite, honestly labelled endpoint
leaf relative to the processed harmonic span. -/
theorem exists_of_firstHierarchy
    (germ : G.AnalyticBellmanGerm)
    (span : germ.EndpointHarmonicJetSpan)
    (entry : G.State) :
    Nonempty (germ.AnalyticEndpointAtlasLeaf span entry) := by
  obtain ⟨response⟩ := germ.exists_firstHierarchyResponse span
  exact ofFirstHierarchyResponse response

/-- Refine a player-neutral potential-jet endpoint at the actual public
entry.  Strict drift is not terminal: its residual family is split into
proper support, full support, or a bounded reachable potential. -/
theorem ofPlayerNeutralPotentialJetAlternative
    {B : G.State → Payoff ι} {who : ι}
    {P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who)}
    {anchor : G.State}
    {jet : GaugeFixedPotentialJet P anchor}
    (alternative :
      germ.PlayerNeutralPotentialJetEndpointAlternative
        B who jet span) :
    Nonempty (germ.AnalyticEndpointAtlasLeaf span entry) := by
  cases alternative with
  | strictDrift certificate =>
      obtain ⟨drift⟩ := certificate
      rcases drift.drift.reachablePositiveClassData_or_boundedPotential
          entry with reachable | bounded
      · obtain ⟨reachable⟩ := reachable
        rcases reachable.rankAlternative with proper | fullSupport
        · exact ⟨.playerNeutralProperSupportEntryTarget {
            B := B
            who := who
            P := P
            anchor := anchor
            jet := jet
            drift := drift
            reachable := reachable
            proper := proper
          }⟩
        · exact ⟨.playerNeutralFullSupport {
            B := B
            who := who
            P := P
            anchor := anchor
            jet := jet
            drift := drift
            reachable := reachable
            fullSupport := fullSupport
          }⟩
      · obtain ⟨bounded⟩ := bounded
        exact ⟨.playerNeutralBoundedPotentialAccount {
          B := B
          who := who
          P := P
          anchor := anchor
          jet := jet
          drift := drift
          boundedPotential := bounded
        }⟩
  | processedHarmonic membership =>
      exact ⟨.playerNeutralProcessedAccount {
        B := B
        who := who
        P := P
        anchor := anchor
        jet := jet
        processed := membership
      }⟩
  | rankDecrease harmonic decrease =>
      exact ⟨.harmonicRankDecrease {
        direction :=
          germ.playerNeutralPotentialJetLeadingPayoff who jet
        harmonic := harmonic
        decrease := decrease
      }⟩

/-- Run the player-neutral potential extraction and immediately classify
the resulting endpoint leaf at `entry`. -/
theorem exists_of_playerNeutralPotential
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (P : AnalyticScaledChargedOccupationPotential
      (germ.rawPlayerNeutralOccupationColumn who)
      (germ.rawPlayerNeutralOccupationCharge B who))
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (actualOccupationColumn
          (germ.playerNeutralOccupationKernel who)
          (germ.playerNeutralOccupationSource who))
        (germ.playerNeutralOccupationCharge B who))
    (anchor entry : G.State)
    (span : germ.EndpointHarmonicJetSpan) :
    Nonempty (germ.AnalyticEndpointAtlasLeaf span entry) := by
  obtain ⟨jet, alternative⟩ :=
    germ.exists_playerNeutralPotentialJet_endpointAlternative
      B who P circulation anchor span
  exact ofPlayerNeutralPotentialJetAlternative alternative

/-- Convert the two terminal analytic-deflation outcomes without
overstating them.  Analytic circulation retains its entry/target/credibility
gap; zero pairing remains a separately named active-harmonic obstruction. -/
theorem ofPlayerNeutralDeflationTerminal
    {B : G.State → Payoff ι} {who : ι}
    {initial :
      FiniteDeflationState
        (germ.PlayerNeutralOccupationIndex who)}
    {terminalAnchor : G.State}
    (terminal :
      PlayerNeutralAnalyticDeflationTerminalData
        germ B who initial terminalAnchor) :
    Nonempty (germ.AnalyticEndpointAtlasLeaf span entry) := by
  cases terminal with
  | analyticCirculation data =>
      exact ⟨.terminalAnalyticCirculationEntryTarget {
        B := B
        who := who
        initial := initial
        terminalAnchor := terminalAnchor
        data := data
      }⟩
  | zeroPairing data =>
      exact ⟨.terminalZeroPairing {
        B := B
        who := who
        initial := initial
        terminalAnchor := terminalAnchor
        data := data
      }⟩

/-- Run finite player-neutral analytic deflation and expose its honest
terminal atlas leaf. -/
theorem exists_of_playerNeutralDeflation
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (initial :
      FiniteDeflationState
        (germ.PlayerNeutralOccupationIndex who))
    (circulation :
      HasNormalizedPositiveChargedCirculation
        (activeOccupationColumn initial
          (germ.rawPlayerNeutralOccupationColumn who) 0)
        (activeOccupationCharge initial
          (germ.rawPlayerNeutralOccupationCharge B who) 0))
    (terminalAnchor entry : G.State)
    (span : germ.EndpointHarmonicJetSpan) :
    Nonempty (germ.AnalyticEndpointAtlasLeaf span entry) := by
  obtain ⟨terminal⟩ :=
    germ.exists_playerNeutralAnalyticDeflationTerminalData
      B who initial circulation terminalAnchor
  exact ofPlayerNeutralDeflationTerminal terminal

/-- Classify a positive circulation on one player's full operational family
without losing the stronger equal-order conclusion.

At equal leading order, finite neutral deflation produces its honest
terminal leaf.  At lower order, the moving circulation supplies one fixed
forward public response and lands in the explicitly unresolved credibility
leaf. -/
theorem exists_of_playerOwnedAnalyticCirculation
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι) (who : ι)
    (circulation :
      AnalyticPositiveChargedCirculation
        (germ.rawOwnerAnalyticOccupationColumn who)
        (germ.rawPlayerOwnedOccupationCharge B who))
    (terminalAnchor entry : G.State)
    (span : germ.EndpointHarmonicJetSpan) :
    Nonempty (germ.AnalyticEndpointAtlasLeaf span entry) := by
  obtain ⟨alternative⟩ :=
    exists_playerOwnedCirculationEndpointAlternative
      germ B who circulation terminalAnchor
  cases alternative with
  | neutralDeflationTerminal _jet _order_eq terminal =>
      exact ofPlayerNeutralDeflationTerminal terminal
  | lowerOrder _data response =>
      exact ⟨.playerOwnedAnalyticResponseCredibility {
        bias := B
        owner := who
        circulation := circulation
        lowerOrder := _data
        tiedResponse := response
      }⟩

/-- Run the synchronized full-owner charged-flow alternative and place both
outcomes in the honest endpoint atlas.

A circulation is classified by
`exists_of_playerOwnedAnalyticCirculation`.  Otherwise the common
all-player potential is retained as an explicit account-discharge leaf. -/
theorem exists_of_playerOwnedAlternative
    (germ : G.AnalyticBellmanGerm)
    (B : G.State → Payoff ι)
    (terminalAnchor entry : G.State)
    (span : germ.EndpointHarmonicJetSpan) :
    Nonempty (germ.AnalyticEndpointAtlasLeaf span entry) := by
  rcases
      germ.exists_playerOwnedPositiveChargedCirculation_or_commonScaledPotential
        B with
    circulation | commonPotential
  · obtain ⟨who, circulation⟩ := circulation
    obtain ⟨circulation⟩ := circulation
    exact exists_of_playerOwnedAnalyticCirculation
      germ B who circulation terminalAnchor entry span
  · obtain ⟨potential⟩ := commonPotential
    exact ⟨.playerOwnedCommonPotentialAccount {
      bias := B
      potential := potential
    }⟩

end AnalyticEndpointAtlasLeaf
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
