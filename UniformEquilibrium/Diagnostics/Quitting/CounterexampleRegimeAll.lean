/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitLimit
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOrbitSelfLoop
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeBallisticity
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAggregatePrefixConsumption
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAggregatePrefixResidualRegression
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAtomicOwner
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeBoundaryProvenanceAlternative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCapCarrier
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCoalitionLocks
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCollisionAwareFiniteReturn
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCommonWordRealization
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedFloorViability
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedDiffuseClosure
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedDiffuseFixedOutsider
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedDiffuseReset
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedDiffuseFloorClip
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedDiffuseActualRepair
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedDiffuseClippedEdgeObstruction
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedNegativeTangent
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeConditionedSlackThreshold
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtConservation
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtSourceObstructionCarrier
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtSourceDynamicAlternative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtSourceStrategicDecoder
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeKilledCapacityPotential
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeKilledTailPotential
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeOneStageObstructionCarrier
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeExactCycleStrata
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeEventualAllContinuePlateau
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeFiniteInstability
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeStrictToggleOrbit
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeFloorViolationBudget
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacket
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketDefect
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketEnergy
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketSupport
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePacketSurplus
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodOneAttachmentRepair
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodOneTangentReadout
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePreferenceLassoCirculationObstruction
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeReachableCarryTelescope
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeNonpositiveFloorTerminalCapRegression
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTerminalIncomingPathAlternative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeCapacityNearMaximizerRebase
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeStatePreservingChronologyCapacity
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTerminalFundingFarkasDecoder
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTerminalFundingSupportNecessity
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTerminalFundingSupportEnlargement
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeQuantitative
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimePeriodicWindows
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSearchConsequences
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSeam
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeSmallPlayers
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTailBridge
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTargetTailGluingObstruction
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacket
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentAnchoredProjectiveLCP
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentMixingCompatibility
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentPacketEnergy
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentProjectiveGauge
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentProjectiveGaugeDefect
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentProjectiveGaugeScalarClosure
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentProjectiveGaugeSecondJet
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentRegularArcLift
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentSupportTransversality
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerExactRoot
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerPacketEdge
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerPacketDichotomy
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerOutsiderJetDichotomy
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerApproxPunishment
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentTwoOwnerSupport
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeTangentSupportLiftFarkas
import UniformEquilibrium.Quitting.Boundary.Repair.SupportEnlargementAlternative
import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailPositiveAbsorptionRoot
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeToggles
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeViolationCollapse
import UniformEquilibrium.Diagnostics.Quitting.FourPlayerSingletonBlocker
import UniformEquilibrium.Diagnostics.Quitting.MinimalFinCounterexample
import UniformEquilibrium.Diagnostics.Quitting.TerminalDebtLiteralStack
import UniformEquilibrium.Diagnostics.Quitting.TerminalEndpointGapTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticConditionedEndpointRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEqualityStratum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSoloOwnerRefinement
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumSpine
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumSpineTransferRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAllContinuePlateau
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTightness
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedVariational
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedTailLocalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauLocalizedOtherDefect
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPartialResetTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectStratification
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauFractionalResetFloor
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauFractionalResetDropout
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPairDropoutConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPairDropoutSignRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSignedPairDropoutConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticBestEndpointTieDropoutRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedExitNashificationRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMarkedResetCycleRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSoloSpineOccupation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSupportEntry
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicSupportBoundary
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAuxiliaryNashBudget
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashEndpointTransport
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashChronology
import UniformEquilibrium.Diagnostics.Quitting.TerminalCapNashRenewalObstruction
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCapNashDebtSupport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCapNashNearMinimum
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticDebtHomotopySelection
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumDebtSimplex
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticWeightedAuxiliaryNashBudget
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumAggregateSurplus
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumAggregateSurplusConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMinimumPlateauPacket
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauQuantitativePassport
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauTimeDisintegration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauIncidence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectCharge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDefectTelescope
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauPositivePartSplit
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDebtTransfer
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeDebtTransferCardinality
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeThreeRoleSpectator
import UniformEquilibrium.Diagnostics.Quitting.FiveCycleResetWindowHelix
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEssentialityPassportCompressionRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPassiveBackgroundCompressionRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetExcursionReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceCapReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetIncidenceRatio
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetSurfaceTension
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetFaceReprojection
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionGerm
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionWindow
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionTemporalSplit
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionConcentratedConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionFixedLabel
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionTwoFaceBridge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticResetReprojectionDiffuseClockBridge
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSingletonClockDebtFace
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticQuantileNashificationAlternative
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticQuantileVertexEndpointControl
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSingletonClockDefectOverlap
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawMixture
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSimultaneousMixtureWitnessSwitchRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCommonWitnessPassportRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawDebtConvexity
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeAtom
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawTransferBalanceRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCommonSuffixCurvatureRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeCausalRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPureTimeRectangleDisintegration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawFiniteSplice
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawFiniteSpliceMarkedLaw
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawFiniteSpliceNashification
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangle
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveSlopeRectangleAlignmentRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawMinimumTransfer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawMinimumTangent
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSimultaneousResetMinimumDichotomy
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawFlatTangentAlternative
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStoppingLawTangentExtraction
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveMinimumUnitResetCycle
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPositiveMinimumUnitResetOrientation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticConcentratedSingletonConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticConcentratedSingletonCancellation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStrictTailEscapeReturn
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLinearPenaltyResetConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticIncidenceDebtRatioRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFixedTableDiffuseIncidenceRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticFixedTableCapDefectRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticRareHazardPunishmentScalingRegression
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNonstationaryCollisionPunishmentNoGo
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticMacroscopicAtomNashProvenance
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauNashMoat
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticTwoReservoirConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticHarmonicReservoirConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCoalitionToggleDeletion
import UniformEquilibrium.Diagnostics.Quitting.CounterexampleRegimeAtomicBlockerCompletion
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlayerDeletion
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticCemeteryPairClockDecoder
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicBlockerBarrier
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicBlockerResetAdapter
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticDiffuseApproximateDeletion
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauDynamicCostate
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMaxDebtConsumer
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPlateauMaxDebtFlow
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNashDefectMobiusIncidence
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEndpointDefectPolarity
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNashDefectMobiusDeviation
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticNegativeVertexGerm
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticSoloQuantitativePassport
import UniformEquilibrium.Diagnostics.Quitting.TerminalDebtLiteralStackAllContinueRegression
import UniformEquilibrium.Quitting.AbsorptionPath.CollisionConcentration
import UniformEquilibrium.Quitting.Root.TerminalSemanticMoment
import UniformEquilibrium.Quitting.AbsorptionPath.NormalizedFiniteWindowOccupation
import UniformEquilibrium.Quitting.AbsorptionPath.FiniteWindowRefusalReweighting
import UniformEquilibrium.Quitting.AbsorptionPath.FlowCostateObstructionAdapter
import UniformEquilibrium.Quitting.AbsorptionPath.SurvivalWeightedObstructionAdapter
import UniformEquilibrium.Quitting.Classification.SingletonPacketDefectAlgebra
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryLimitGeometry
import UniformEquilibrium.Quitting.Cycles.PhantomBoundaryConditioning
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseChronology
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseUniform
import UniformEquilibrium.Quitting.Cycles.ConditionedProperFaceDeficientClock
import UniformEquilibrium.Quitting.Cycles.ConditionedSoloExtraction
import UniformEquilibrium.Quitting.Cycles.ConditionedDeletedClockSoloCompletion
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseProductRescaling
import UniformEquilibrium.Quitting.Cycles.ConditionedDiffuseStrategicRescaling
import UniformEquilibrium.Quitting.Cycles.ConditionedProductPurification
import UniformEquilibrium.Quitting.Cycles.ConditionedSingletonStrategicPurification
import UniformEquilibrium.Quitting.Cycles.ConditionedTangentSeam
import UniformEquilibrium.Quitting.Cycles.ConditionedPeriodicRenewal
import UniformEquilibrium.Quitting.Cycles.PeriodOneTangentAtlas
import UniformEquilibrium.Quitting.Cycles.PeriodicNormalizedSeam
import UniformEquilibrium.Quitting.Debt.Dynamic.DynamicDebtCapChargedAnchorCounterexample
import UniformEquilibrium.Quitting.Debt.Dynamic.PeriodicDebtHolonomy
import UniformEquilibrium.Quitting.Debt.Dynamic.PunishmentFloorCapSplice
import UniformEquilibrium.Quitting.Paths.OutsiderNeverGluing
import UniformEquilibrium.Quitting.Paths.HazardScaledResidualCompiler
import UniformEquilibrium.Quitting.Paths.JointPolicySeparatedErrorCompiler
import UniformEquilibrium.Quitting.Punishment.ApproximateCompletedCycle
import UniformEquilibrium.Quitting.EssentialAPS.NashBellmanSingletonCycle
import UniformEquilibrium.Quitting.Terminal.TailCompression.SummableTailBestResponse

/-!
# Quitting counterexample regime

This is the public umbrella for the combined counterexample normal form, its
canonical prefix-charge capacity, quantitative exact-D restrictions,
search-facing recurrence tests, the exact bridge from optimized exact-D tails
to punishment-floor prefixes, the membership-toggle and
stationary-cap instability families, support dynamics of the forced packet,
canonical minimal finite counterexamples, emptiness at small player types,
orbit value limits, quantitative floor-violation budgets, the collapse that
makes the extracted optimized tail's absorption unconditionally summable,
its positive-debt all-Continue self-loop limit, and exact evaluation of
periodically restarted tail windows.  The optimized tail additionally carries
exact finite and infinite debt conservation, a logarithmic owner-clock bound,
the positive phantom-plateau theorem, closed augmented-cap membership in the
global floor carrier, and a canonical periodic-window family whose player and
refusal/phase obstruction stabilize on an infinite set.  The forced packet's
noncomplementarity has one uniform compact refusal margin across all normalized
packets of the fixed table.  Stable pure quitting coalitions independently
generate unbounded canonical prefix charge, linking the sure-exit and capacity
screens.  The umbrella also exports the augmented-cap splice
interface and the finite regressions delimiting singleton complementarity and
cap-only arguments.

Literal exact-root prefixing supplies a separate global-minimality consumer:
maximum terminal exploitability is nonincreasing, while a positive singleton
gap strictly decreases total playerwise best-response debt (the unilateral
exploitability gap).  This lexicographic
descent removes both unique-maximal-debtor and fixed-player premises.  Its
positive-part normal form is an action of the survival-weighted block monoid:
opponent survival transports literal debt and the positive root endpoint
premium consumes it.  Arbitrarily deep finite stacks of exact roots exist over
actual near-minimizing suffixes, every displayed semantic pair is co-realized,
and every one-step total debt drop is bounded by the common lexicographic
accuracy.  A macroscopic debtor therefore sees little opponent absorption and
little positive endpoint premium; two macroscopic debtors force every root
marginal close to Continue.  The remaining counterexample input is a literal
positive premium or singleton gap at a positive-debt coordinate of these
triangular stacks; conditioned values and stored Bellman annotations are not
substituted for literal suffix payoffs.

The closure of attainable literal prescribed/envelope pairs is a compact
finite-dimensional carrier invariant under every root prefix.  Total debt
attains a positive minimum in a counterexample.  Selecting an exact finite
Nash root against an arbitrary auxiliary target `b-h` and prefixing it to the
actual minimum pair gives the collision/singleton budget
`D*kappa + sum_i alpha_i*(D-h_i) <= 0`.  Hence every positive minimum is an
exact all-Continue semantic self-loop; the former provenance atomic branch is
globally impossible.  The open auxiliary cube contains only all-Continue
roots, while its critical face is collision-free and admits singleton mass
only on a full-debt coordinate.

Plateau best responses retain a quantitative Never, at-stop collision, or
before-stop opponent-absorption atom.  Its terminal mass has an exact time
disintegration, and every exposed actual live row is an exact carrier-owned
semantic prefix edge.  A positive collision atom over a minimum tail proves
that row is not exact Nash.  Arbitrary-root algebra now charges every observed
opponent absorption to the tail's debt drop plus the row's local Nash defect;
on pure-time response profiles the survival-weighted defect is bounded by the
initial response debt.  The sharp remaining term is positive
survival-weighted tail-debt drift.  Separately, every player subset has one
positive-mass reward-moment outcome carrying its exact aggregate singleton
surplus.  In a counterexample it is either Never or an absorbing coalition
with a strict sure-exit toggle blocker.  The four-player negative control
saturates this finite alternative, so the residual is a chronological
defect/excess telescope or a negative/Never vertex-germ consumer, not another
static reward inequality.

Normalized minimum debts form a probability simplex, with nonnegative
singleton slack above its complementary base.  Singleton tightness is exactly
a unique full-debt, zero-slack vertex gate; away from those gates every exact
minimum root is all-Continue.  Positive costates give the same conclusion for
weighted debt minima through an anisotropic auxiliary moat.  On one realizing
pure-time law, positive-part accounting removes the terminal-outcome count:
debt is paid either by quantitative harmonic Never mass or by quantitative
opponent-containing chronological charge.  A finite Abel telescope consumes
the latter up to endpoint/tail excess and survival-weighted local-defect
occupation.  Uniform near-minimum tails reduce all excess terms to one
epsilon, but diffuse defect occupation is not automatically one player's
collectible regret.  A matched reset/debt-transfer theorem, or a direct bound
on that occupation, is the remaining dynamic consumer.

The maximum-debt objective gives a sharper dynamically aligned version.
Maximum semantic exploitability attains its minimum on the same compact
carrier, every positive minimax point is again an all-Continue plateau, and a
root selected a fixed distance inside a near-minimax auxiliary moat has
absorption bounded by the minimax excess divided by that distance.  Along an
actual chronology, choose a player of maximal debt at every shifted state.
Changing to the next maximizer has nonpositive switching cost on the shared
tail, so one stopped telescope keeps opponent absorption and local defect on
the same coordinate while paying only one near-minimality error.  It also
converts the debt-weighted charge into an unweighted selected-opponent clock
at the positive minimax scale.  Independently, a literal best-response reset
transfers the erased debt to the opposite simplex face: its recipient either
matches an opponent in the same terminal incidence law, or a genuine
two-opponent separator remains.  The unresolved term is now the defect
occupation of changing maximal-debt owners, together with the own-singleton
vertex events invisible to their deleted clocks.

Fractional costates supported on a tied maximum-debt face add no power to a
separable row objective: one maximal-debt coordinate always dominates.  A
coupled finite reset/incidence flow does retain more structure.  Every such
flow obeys exact player-subset Hall inequalities, strict cuts have a
quantitative max-debt/surplus consumer, and positive flows contain a pure
positive label path.  The weighted Hall converse and co-realized semantic
state chronology are deliberately not inferred.  Independently, Boolean
Möbius expansion charges coordinate Nash defect to explicit played
singleton, pair, and higher coalition cylinders.  A finite-cutoff pigeonhole
selects one fixed player/coalition/orientation label carrying a quantitative
share of defect occupation, but positive-part cancellation and scattered
states prevent reading that label as a legal deviation or cycle.

The persistent collision branch has a more direct same-profile conclusion.
At the selected pure-time Quit row, collision mass times the marked player's
local root defect is bounded by reset debt, hence that defect vanishes.  The
row's own shifted-tail cluster either stays strictly above the minimum fiber
or, on the fiber, the other players carry a uniform positive defect sum.
Switching one such player to its better pure endpoint at that reached row and
then resuming the original behavior is a legal unilateral deviation with
exact gain equal to live mass times its coordinate defect.
Moving only a strict fraction toward that endpoint reduces its semantic debt
by the corresponding fraction of the defect and retains at least the
complementary fraction of every terminal incidence atom.  Minimum-reference
accounting charges the gain to opposite-face transfer plus the current
prefixed source's exact excess over the minimum; marked localization puts the
continuation, not automatically this source, on the minimum fiber.
At a full best-endpoint move, every positive marked coalition is routed with
no mass loss to exactly one of four cells: the coalition is preserved, a
member is erased, an outsider is inserted, or the coalition is again
preserved.  More generally, finitely many strict fractional moves cannot
erase a positive collision over positive minimum debt while reaching zero
total root defect.  Any such attempted Nashification has a first unit-weight
move; the original collision remains positive until that move and is then
routed across the corresponding one-player Boolean edge.  This is a local
finite stratum, not a chronological edge or return.
Tracking the routed coalition through the full finite reset word identifies
an exact positive-mass pair-to-singleton member dropout.  In a counterexample
the surviving singleton owner is either in the isolated-negative punishment
branch or has a distinct strict joiner whose pure-Quit update restores an
overlapping positive-mass pair.  This remains a static root transition rather
than a Nash--Bellman continuation.  The dropout itself is unsigned: an exact
two-player regression reaches a zero-defect all-Continue endpoint through a
pair-to-singleton Continue overwrite which the dropout player strictly
disfavors.  A strategic cycle requires a same-row sign invariant in addition
to routed mass.  Recomputed best-endpoint provenance supplies the exact weak
sign: the overwrite gain equals the mover's local Nash defect.  Positive
defect is strict, while zero defect is literal endpoint indifference.  A
second exact regression shows that best-endpoint routing, positive incidence,
negative singleton reward, and a zero-defect endpoint can all coexist with
this tie.  Global chronology must exclude or consume that neutral branch.
The neutral deletion is not minimum-face safe: in the same literal regression
the pair profile globally minimizes semantic debt at zero, but deleting the
indifferent player preserves that player's debt while increasing the
survivor's debt by one.  Mover neutrality alone gives no merge operation.
General exit-face Nashification cannot remove those defects while retaining
the marked inequality: a two-player regression loses collision support and
reverses the marked endpoint inequality even under approximate Nashification.
Iterating exact endpoint resets is not a substitute: another two-player
regression transfers the defect once, kills collision mass, and then reaches
the zero-absorption all-Continue root.  A counterexample does have a finite
closed strict membership-toggle orbit in the static coalition cube, but this
does not supply Bellman chronology.

Off-minimum reset excursions have an exact return account.  A cap--Nash
prefix preserves the reset coordinate and opposite-face transfer, while its
absorption pays exactly for the fall in excursion excess.  Minimizing total
debt on the reset face produces either a return to the global minimum fiber
or a canonical off-minimum point whose only cap--Nash root is all-Continue.
The compact joint carrier of semantic pairs and complete terminal outcome laws
repairs the incidence projection: fixed-law reset minimization retains every
incidence coordinate, and literal prefixing acts by fresh root atoms plus joint
survival times the old law.  Therefore a positive-survival cap-return selection
reaches near the minimum while retaining positive same-law incidence.  The
remaining dynamic step is to produce that return selection, or eliminate or
compile the constrained all-Continue cap face.
At a fixed-law reset minimizer there is an unconditional exact dispatch.  A
singleton cap violation yields an absorbing strict debt descent; positive
global minimum debt forces its survival to be positive, so incidence is
retained.  Otherwise all-Continue is the cap fixed point.  Positive incidence
and a supported strict coalition toggle do not rule out the latter: a literal
two-player semantic/law point has reset debt zero, unit collision incidence,
and only the all-Continue cap--Nash root.
There is also a canonical variational form of this residual.  On the positive
total-opponent-incidence reset face, lexicographically minimize total debt per
incidence and then total debt.  Every exact cap--Nash prefix at the selected
point first creates zero fresh opponent incidence; secondary minimality then
forces survival one.  Hence all-Continue is the unique exact cap root and
fixes the semantic point, even though the retained terminal law still has
positive opponent incidence.  A half-reset regression shows that the primary
debt/incidence quotient alone can be exactly flat; the secondary minimum and
the positive global debt floor are load-bearing.
A background-subtracted selector first minimizes debt on the closed reset
face.  Either that face meets the global minimum fiber, or the separated
excess density `(D-D*)/I`
attains.  At a slope minimizer the exact prefix action gives the nonnegative
identity `(D-D*)*fresh + (1-survival)*D* * I <= 0`, forcing every exact cap
root to all-Continue.  For every fixed positive incidence threshold this
unique root has a robust positive total-defect moat under cap perturbation.
A fixed normalized three-player table nevertheless keeps incidence uniformly
positive while its local total defect at the displayed semantic cap tends to
zero, so no linear diffuse modulus follows.  The harmonic and finite
positive-part reservoirs can be kept on one co-realized reset law and
dispatched without contamination; the all-Continue cap face is the remaining
branch.
At the no-join harmonic endpoint, the sure-solo row is fully absorbing and
locally exact, but its unique noncontracting owner has stationary cap zero and
strictly fails punishment admissibility.  The harmonic reservoir therefore
gives a quantitative obstruction to both period-one and instant punishment
completion rather than a solo-payoff compiler.
Coordinatewise rare scaling does not repair this branch.  A fixed normalized
three-player regression has punishment value `-1`, attained by a sure
two-opponent collision, while independently shrinking both opponent hazards
to zero sends the owner's stationary cap to `1`.  Collision punishment is
quadratic whereas singleton leakage is first order; any rare-hazard repair
must preserve coalition phases or assume singleton-mixture support.
The common limiting law is weaker than a common strategic account: fixed-law
minimization can change the envelope and the realizing profiles, and it does
not preserve the marked stopping time or live row.  Stored terminal incidence
also differs from fresh incidence of the cap--Nash prefix.  The missing
producer must co-realize these data at one reached row.
The slope support extends uniformly with arbitrary additive error to points
of sufficiently small reset debt.  Exact quantitative reprojection splits
into a global linear face penalty or positive off-face violations with
unbounded violation-to-reset-debt ratio.  The latter is a normalized carrier
obstruction with joint-law provenance; it furnishes neither a finite routed
word nor a chronological tangent.
The linear branch gives an exact finite-word floor
`retention * initialExcess <= finalExcess + penalty * finalResetDebt` and a
matching opposite-face transfer bound.  Exact return to the minimum reset
face forces a first unit-weight overwrite, but anchored support gives no
stepwise Lyapunov descent and the forced overwrite has no payoff sign.
In the unbounded branch, compactness selects one joint semantic/law contact
and positive off-face approach points with reset debt negligible relative to
tension.  The contact has zero tension and reset debt, retains strictly
positive opponent incidence, and satisfies its exact reward-moment identity.
The approach may be chosen through literal executable profiles.  One fixed
opponent and terminal coalition then carry uniform positive mass in finite
profile-dependent windows, while every moving row's survival-weighted owner
defect is negligible at the tension scale.  The cutoff may drift, so this is
not yet a bounded Bellman window or a chronological tangent.  The exact
temporal split is explicit: either a positive stage atom recurs and gives a
literal concentrated prefix packet, or the same profiles carry a finite unit
coalition clock whose mesh tends uniformly to zero.  The diffuse clock still
lacks an exact-Nash policy and common shifted-tail state.  In the concentrated
branch, the owner defect becomes unweighted and vanishes.  Compactifying the
actual shifted tails gives a singleton cylinder, strict escape above the
minimum fiber, or a uniform positive defect on other players at the minimum
fiber.  The latter selects a legal best-endpoint deviation with exact positive
payoff gain and no-loss coalition routing; recurrence/punishment compilation
is the remaining step.  Finite-label extraction freezes one non-owner player,
one best endpoint, and a joint root/tail limit with positive coalition mass
and quantitative positive defect.  The limit is therefore provably non-Nash,
so it cannot enter an exact reset or cycle compiler without Nashification.
The corresponding same-profile partial reset is fully co-realized: it has
exact positive gain, exact debt transfer, and retains the marked stage atom.
It reaches the mover's zero-debt face exactly when the one-row gain pays the
mover's entire source debt; it need not preserve the old owner's zero face.
In the singleton-cylinder branch, owner defect control becomes vanishing
positive Quit advantage and yields a third-player strict joiner, an
owner-join gain canceled by other coalition states, or a punishment moat.
The cancellation branch has a fixed finite label: either the shifted tail
frequently rises by a fixed fraction of the singleton gain, or one fixed
opponent coalition carries a quantitative loss when the owner joins it.
The tail-escape branch is orientation-consistent: cap--Nash return is exactly
equivalent to spending the tail's excess debt by absorption, while an
all-Continue cap face can stall with zero spend.

Cap--Nash prefixing gives an actual-profile counterpart with no jointly
realized cap premise.  Select an exact mixed Nash root against the common
continuation profile's coordinatewise best-response cap, then execute that
same profile after joint Continue.  Every literal debt coordinate and the
uniform random-deviation audit loss are multiplied exactly by the root's
joint Continue mass.  Hence positive total-debt infimum charges absorption
and its survival odds to the displayed excess above that infimum.  The sharp
joining-loss constant then transports every solo endpoint to the cap.  More
strongly, selecting against `cap - q` at a near-minimum semantic pair gives a
single root with a quantitative absorption moat and a simultaneous singleton
floor on every prescribed or comparison coordinate.  Sending the excess to
zero and then `q` to the positive minimum excludes a persistent conditioned
singleton gap whenever the comparison value is co-realized by those same
near-minimizers.  It does not make independently periodized renewal profiles
near-minimal or identify a chronological owner occupation.  An explicit
comparison of the two moat errors also forces every exact Nash root against
the unshifted cap to be literally all-Continue.  Thus iterating arbitrary
cap--Nash prefixes close to the minimum can freeze and supplies no automatic
nonzero tangent.  Iterating before that freeze does give literal finite
backward cap chronologies of arbitrary depth, with every suffix executable
and every root exact against the suffix's behavioral cap.  Their coordinate
debts scale by the full survival product, while the positive total-debt
infimum times the unweighted sum of all displayed absorption hazards is at
most the terminal debt excess.  Near the infimum the whole stack therefore
has vanishing total absorption, payoff and cap displacement are only linear
in that absorption, and each finite block's survival remains uniformly
positive.  Stacks selected at different depths need not be compatible, so no
infinite Never path or renewal follows.

If a cap stack nevertheless reaches a distant debt target, it must spend a
macroscopic absorption fraction.  Its exact conditional-delivery identity
then isolates cancellation between absorbed delivery and the surviving
terminal cap as the only payoff escape.  An honest period-one regression
shows that exact cap--Nash selection may instead stall.  The cap-to-prescribed
debt homotopy has the same sharp boundary: at a positive minimum every
pre-endpoint exact root is all-Continue; a nontrivial endpoint is a unique
solo debt gate with a joiner or punishment certificate, but the exact Nash
selection can remain all-Continue on the whole closed homotopy.

At a negative zero-slack debt vertex, stationary escape has an exact
consumer.  If outsiders do not gain by joining the owner's singleton exit,
any stationary semantic germ whose honest owner payoff approaches the
singleton and whose owner debt vanishes forces the punishment value below
that singleton and compiles the singleton vector.  A counterexample therefore
has either a strict joiner or a fixed positive punishment moat separating all
stationary caps from the singleton.  The same alternative is co-realized with
the plateau's harmonic-Never/opponent-charge law; the remaining obstruction is
genuinely nonstationary.

Finite-window renewal closes one older provenance seam without identifying a
stored cap.  Periodically repeating a longer source-tail window is an ordinary
product behavior profile, its literal payoff is exactly the normalized
restart delivery, and those payoffs converge to the canonical value
conditioned on eventual absorption.  The full cap is already the exact finite
maximum of refusal and first-pass phase stops.  What renewal does not preserve
is minimax or lexicographic near-minimality; a counterexample must expose a
stabilized refusal/phase-stop excess on these honest periodic profiles.

Every unaugmented value on the optimized tail already dominates the behavioral
punishment floor, so every finite chronological tail segment reverses to a
legal exact floor prefix with the same charge.  The tail is also uniformly
ballistic in absorption time: after one date, every positive-absorption window
has endpoint distance at least one fixed positive multiple of its absorbed
mass.  Thus no late window closes at little-o of charge scale.  This does not
produce recurrence; finite total charge permits a bounded ballistic approach
to the limiting all-Continue state.  The signed normalization is retained
more precisely: either the tail is eventually literally all-Continue, or
positive one-stage windows extract a nonzero charge-tangent packet from the
same roots.  Its remaining finite sign dispatch is a negative coordinate or,
after excluding all negative coordinates, a positive active-owner coordinate.
The corresponding phase-repair and support-enlargement consumers remain open.
On the active-positive branch, after excluding every negative tangent
coordinate, the same tail-derived packet is canonically a normalized
singleton-source packet.  Its weighted surplus is its mass-weighted tangent,
so it contains a distinct supported pair with positive reciprocal singleton
effect.  For any supplied product root and intended interior support, the
remaining collision-aware continuation lift is now one explicit finite affine
system: its physical branch decodes an exact Nash--Bellman edge, and its dual
branch supplies Farkas multipliers certifying that this root has no lift.
Actual collision and higher Möbius terms are retained in the rows.  Choosing
the simultaneous quit probabilities remains a genuinely multiaffine search;
the singleton-level handoff does not itself produce that root or contradict
all of its pointwise certificates.
The same packet also embeds canonically into the existing anchored projective
singleton LCP at every positive cemetery weight: singleton weights are a
rescaling of packet mass and the anchor is boundary minus the corresponding
rescaled tangent.  An active-positive coordinate becomes a strictly negative
projective LCP direction.  What remains absent in arbitrary player count is
the resolved-chart feasibility/arc lift turning that anchored first-event
datum into actual product-root Nash--Bellman rates; the three-player analytic
compiler does not supply such a generic constructor.
At the first blow-up, the active mixing row has a simpler exact form.  On a
positive-mass owner it is the mass-weighted pair-join effect
`sum_{j≠i} mass_j * (r_i({i,j})-r_i({i}))`.  Either every active row
vanishes, or a supported outsider has the same strict sign and supplies a
finite pair-join pivot.  In the compatible active-positive branch, collision
energy must cancel the positive singleton energy exactly, forcing a supported
pair with negative reciprocal collision increment.  These are finite
first-order directions; neither the canonical sign separator nor the pair
it selects is yet a feasible analytic arc or a strategic Farkas certificate.
On the compatible branch, the first radial blow-up supplies the exact
polynomial interface.  Hazards are `t*leading` and continuation is
`boundary+t*drift`; exact polynomial residuals retain every coalition and
factor the physical Bellman and mixing equations by `t`.  The packet solves
the exceptional-divisor Bellman rows, and compatibility solves its active
mixing rows.  If the blow-up derivative is surjective and its kernel has a
positive radial direction, the existing analytic implicit-function theorem
produces a positive radial equality arc.  With the strict physical cell signs,
each nonzero point decodes to an exact Nash--Bellman root.  The literal
ungauged compatible chart cannot meet those two regularity hypotheses:
compatibility makes every exceptional-divisor base point lie on one
projective scale line, whose nonzero tangent has radial coordinate zero; the
source has exactly one dimension more than the equality rows, so
surjectivity makes that line the whole kernel.  A projective gauge or a
radial-parameter implicit-function theorem is therefore mandatory.  On a
three-owner support, one explicit radial minor exactly separates the
transverse-surjective/no-outward branch from the singular/outward branch and
the latter supplies a finite left costate.  None of these statements creates
a global return.
The canonical projective gauge `sum leading = 1` now removes exactly the
scale line, with an injective affine chart and an exact equality between its
full-residual zero image and the ungauged zero set on that hyperplane.  The
gauged full system is square, so full derivative surjectivity would isolate
the base rather than produce an arc.  A nonvacuous regular theorem therefore
uses a codimension-one reduced residual together with an explicit local
recovery equivalence to the full equations.  Surjectivity and an outward
kernel direction for that reduced system produce an analytic arc of literal
full zeros and feed the existing Nash--Bellman decoder.  Constructing the
reduced equation/recovery pair remains the exact analytic gate.  The natural
choice of simply deleting one active mixing row fails in general.  Its exact
missing scalar is `Bellman_i + (1-t*a_i)*Mixing_i`; after Bellman closure and
nonzero own survival, this vanishes exactly when the omitted row does.  A
normalized regression through the packet keeps every Bellman row and all
retained mixing rows zero while the omitted row varies as `s*(Jv)_i`.
Compatibility kills only the packet mass direction, not arbitrary zero-sum
gauge variations, so no local recovery theorem follows from it.
Nor does packet sign/energy force the missing scalar to cross zero.  For a
three-owner support, a nonzero radial minor makes the omitted defect have a
nonzero derivative and hence one fixed one-sided sign along any supplied
reduced branch.  If the minor vanishes, the explicit outward direction kills
all selected first-order rows and leaves an honest higher-order closure
problem.  The finite alternative is transverse sign obstruction versus
higher-order singularity, not an implicit first-order repair.
For the three-owner zero-minor branch, the first nontrivial omitted-row
calculation is now exact.  Along the sum-one Bellman-forced affine outward
path, the defect is `s^2*(Q+s*C)`.  Nonzero quadratic coefficient gives an
eventual fixed sign; if it vanishes, a nonzero cubic coefficient gives a
fixed sign at every positive scale; if both vanish, this scalar is identically
zero along the path.  The path is not asserted to solve the retained
nonlinear mixing rows, so this classifies the second jet without constructing
an arc or return.
For two declared active owners, Bellman elimination makes the reduced support
Jacobian exactly `[[0,D₁₂],[D₂₁,0]]`, where
`Dᵢⱼ=r_i({i,j})-r_i({i})`.  A signed directed pivot is regular precisely
when its reciprocal effect is nonzero, and the outward leading variation is
explicit.  In contrast, if those two owners are the entire positive support
and both packet rows are compatible, positivity forces `D₁₂=D₂₁=0`:
the whole reduced Jacobian vanishes.  This singularity integrates exactly
rather than requiring a second jet.  For arbitrary hazards below one, the
Bellman-eliminated continuation has active coordinates
`w_i=(z_i-p_j*r_i({j}))/(1-p_j)` and symmetrically; both active gains vanish,
because a two-owner root has no triple or higher coalition.  If the inactive
gain signs hold, this packages one exact Nash--Bellman edge.  Artificial
continuation floor and upper-box bounds can be recentered around the boundary
and disappear from bare edge existence; the original bounds remain later
viability obligations.  Any reachable return, lasso, or cycle is separate.
Along the packet-selected ray
`p_i=t*mass_i`, positive subunit hazards and survival are automatic.  Active
continuation is exactly `boundary_i-t*tangent_i/(1-t*mass_j)`: nonnegative
tangent makes its upper bound automatic, strict floor slack is stable for
small `t`, and a tight floor with positive tangent fails at every positive
scale.  Strict outsider singleton slack also gives eventual outsider Nash
signs through an exact finite polynomial regression.  A singleton-tight
outsider has the exact form `t*(linear+t*quadratic)`.  Consequently either
every sufficiently small positive scale supplies a positive-charge exact
edge, or a tight inactive owner has positive linear coefficient, or zero
linear coefficient followed by positive quadratic coefficient.  This is a
finite support-entry pivot, not the enlarged-support root itself.
The tight active punishment face is nevertheless asymptotically consumable
at any fixed tolerance.  Its exact floor deficit tends to zero with the
hazard scale, and approximate min--max supplies a player-specific
target-closed punishment tail below the exact-ray continuation plus the
chosen rationality error and tail slack.  A single stationary row working
for all errors would force actual attainment of the punishment infimum, so
the available tails necessarily depend on scale/tolerance and do not yet
form one common multi-player suffix or return.

Independently of that selected-tail geometry, reward-table closure gives a
robust finite-cycle restriction: a hypothetical counterexample has one
positive-radius reward neighborhood containing no punishment-admissible exact
cycle of any period.  For a fixed root cycle, a common own-set reward shift is
governed by an exact finite global feedback system.  On an absorbing cycle its
value correction is unique, its unit multipliers lie on probability scale,
and the system eliminates player by player.  This does not prove density of
solved-cycle strata or show that own-set shifts exhaust general reward-table
perturbations.

For proper-face arguments, the umbrella exports an original-coordinate
outsider-`Never` estimate.  If the outsider's live continuation is at most
`eta` below its solo reward and insider absorption is at most `delta` at every
date, every behavioral deviation gains at most `eta + 2*M*delta` over literal
`Never`.  The theorem does not derive either quantitative premise from a
restricted equilibrium.

The umbrella also exports the general summable-tail boundary geometry used by
the regime: an explicit remaining-charge bound on literal behavioral best
responses, simultaneous annotation convergence with an active-owner pinning
criterion, and the scalar phase/refusal algebra that separates underfunding
from punishment-floor failure.  None of these results identifies the forced
packet with a tail occupation or realizes an augmented cap as a suffix.
At the local dynamic-debt level, vanishing of the named diagonal seam is
exactly the criterion for the displayed root to lift to a Nash--Bellman edge
between augmented caps; the umbrella does not assert that this criterion holds
along the optimized tail.
Playerwise dynamic debt is also exported as an exact killed-potential
reference account.  An excessive account with the same initial value can
dissipate only by losing the corresponding surviving boundary: boundary
dominance is equivalent to zero total killed dissipation, forces every
positively reached local dissipation to vanish, and strict dissipation forces
strict boundary shortfall.  The counterexample
regime does not supply that boundary dominance, so this accounting theorem
does not erase the positive phantom plateau.
The canonical prefix-capacity potential nevertheless supplies a natural
account: remaining capacity is nonnegative, pays each chronological
absorption charge, and after singleton-cap scaling is killed-excessive for
the exact debt source.  Its initial mismatch with exact debt is explicit and
has no proved sign or vanishing property; shifting the account arithmetically
does not preserve excessivity automatically.
Product-root collision mass is at most `choose (card ι) 2` times squared
one-stage absorption.  The exported weighted-window concentration theorem has
a separate zero-absorption branch; its conditional singleton-mixture payoff
comparison applies when both absorption and singleton mass are positive.
On a supplied finite exact-debt window, a positive debt coordinate that returns
to its initial value forces every opponent to Continue throughout.  Two
distinct returning positive coordinates make the entire window all-Continue,
so an absorbing return can carry at most one such coordinate.
The forced packet's weighted surplus is a quadratic form depending only on the
symmetric reciprocal part of the singleton solo-effect matrix.  Consequently
every counterexample packet supports a pair with positive reciprocal solo
effect; if all reciprocal pair sums are nonpositive, the complementary-mixture
compiler supplies a uniform payoff.
Canonical source-typed finite windows now retain normalized singleton owner
occupation, collision mass, and full absorbing delivery.  Late collision
vanishes at the product-law rate, and positive limiting owner occupation pins
the annotation boundary directly.  Normalizing the singleton mixture by total
absorption gives a collision error bound without a positive singleton-mass
premise.  Refusal conditioning uses a different
deleted-player survival law; its normalized discrepancy is explicitly bounded
by the chronological reweighting error divided by a positive deleted-absorption
denominator.  No theorem here makes that ratio vanish for the canonical
windows.
Adjacent source windows also form exact survival-weighted obstruction blocks:
singleton and collision charge in the later window is killed by the earlier
joint-survival factor, while endpoint displacement is an unweighted
coboundary.  This makes normalized tangent composition explicit, but does not
yet supply a strategically feasible raw-current family or a compatible
co-state.
The same data is exported as a sparse two-grade raw flow.  Raw charge has
survival degree one, endpoint coboundary has degree zero, and arbitrary finite
co-states obey the exact adjoint pairing law across adjacent windows.  This
flow has an exact compact one-stage carrier: its source retains boxed exact
Nash--Bellman and dynamic-debt constraints together with the punishment floor
at both endpoints, every canonical tail edge belongs to it, and every finite
co-state support is attained.  Enriching this carrier by the playerwise
diagonal dynamic-debt source makes the previously missing debt price literal:
the negative coordinate selector exposes exactly the zero-source face, and
for an exact edge this face is equivalent to the corresponding augmented-cap
transport equation.  Consecutive source coordinates fold to current debt
minus survival-weighted terminal debt.  The theorem still does not force the
canonical tail into that face, prove recurrence there, or decode a
strategically realizable exit.
The exact dynamic alternative shows why: at every date the selected tail flow
is in the zero-source face now, is there at the next edge, or the canonical
killed-capacity account dissipates strictly.  The latter is exactly strict
growth of the survival-scaled debt/capacity boundary mismatch.  Face
recurrence follows if that mismatch is nonexpanding on positive-length
windows at arbitrarily late starts, but the current regime supplies only the
reverse weak inequality.  Thus the remaining premise is a concrete boundary
comparison, not compactness or co-state selection.
Projective provenance cannot silently provide that comparison: a moving zero
terminal boundary may escape every fixed coordinate and leave a positive
harmonic limit, even under exact finite killed recursions.  The two-ended
compactification retains a reverse ray but no bridge survival, while the
metrizable marked decoder jointly retains both anchors and repair state but
does not carry the canonical capacity potential.  On the actual optimized
tail the capacity account is antitone, its killed dissipations are summable,
and the one-step boundary-mismatch excess tends to zero.  This gives
asymptotic equality only; every finite excess may remain strictly positive.

Periodic attachment has a second, exact normalization fence.  For an
absorbing exact Nash--Bellman word, the finite-stop and refusal branches of
the literal periodic best-response envelope are controlled by endpoint drift
divided by the joint and opponent survival gaps.  Ordinary endpoint
convergence does not imply these normalized ratios vanish; on the optimized
counterexample tail the joint-absorption ratio is eventually bounded away
from zero in endpoint-distance scale.  In the refusal branch, positive debt
can survive precisely in this normalization, so a
tail-derived singleton packet and a phantom plateau need not contradict one
another even after occupation identification.  The isolated
opponent-survival-one branch remains the separately classified negative-solo
exception.
For a repeated one-root word these coefficients have an exact mass atlas.
Writing `A` for absorption, `mu` for the normalized singleton-owner mass,
`C` for joint survival, and `rho` for opponent survival gives
`rho-C=A*mu` and `1-rho=A*(1-mu)`.  The phase evaluator is
`-C*tangent-phaseSlack`; on `mu<1` the refusal evaluator is
`mu/(1-mu)*tangent-refusalSlack/(A*(1-mu))`.  At `mu=1` every opponent
continues surely and the refusal denominator is genuinely zero.  The
canonical extraction retains literal one-stage fuel and now packages actual
root-mass and endpoint-tangent convergence to the tail packet, with one fixed
signed coordinate.  Its single exact Nash--Bellman edge makes both displayed
slacks nonnegative.  The periodically repeated root remains a diagnostic
deviation; the source tail is not asserted to be periodic or attached to that
restart.
On the active-positive owner, full limiting mass is impossible.  The selected
roots eventually have proper positive owner mass, positive endpoint tangent,
and positive own Continue probability; exact root complementarity then makes
the refusal slack zero.  The diagnostic repeated-root refusal gain converges
to `mass/(1-mass)*tangent` and is eventually strictly positive.  This sharpens
the refusal branch quantitatively.  The exact attachment formula shows what
prevents an unconditional transfer: actual attached `Never` gain is the
periodic refusal gain plus the joint-survival tangent correction plus
opponent survival times the difference between actual suffix-`Never` payoff
and stationary refusal value.  The counterexample tail neither realizes its
far annotation as an honest suffix payoff nor controls this final boundary
defect.  If both facts are supplied, the diagnostic becomes an eventual
literal profitable deviation; they are not consequences of the present tail
asymptotics.
The terminal-gap lane remains co-realized even when that owner-specific
attachment fails.  Every positive finite prefix has behavioral-tail repair
value at least the regime gap, because the boundary value and all-behavior
envelope come from the same actual suffix.  Elementary tail compression
therefore returns, behind every selected one-root prefix, a sure-joint,
sure-solo, or `Never` cap whose terminal exploitability remains above half the
gap.  This is an unconditional terminal obstruction, not a recovery of the
active owner's deviation or of the stored Nash--Bellman annotation.
For the canonical aggregate minimizer, this co-realized repair floor is also
bounded above by the optimized aggregate exact-`D` objective.  Consequently
every cutoff has a marked aggregate anchor whose packet mass carries the
terminal gap with an explicit reward/cardinality constant.  The packet is not
yet a punishment-floor reachable predecessor.  A conditional consumption
theorem splits half the gap between the next-cutoff objective drop and one
legal predecessor charge once literal state attachment and the comparison
`capped exploitability ≤ objective drop + scaled charge` are supplied; neither
premise follows from tail compression alone.
Among the elementary caps, immediate `Never` has an exact zero-boundary
interpretation: its terminal exploitability is the calibrated path's maximum
dynamic debt.  The generic consumption inequality then reduces to the
concrete endpoint requirement that next-cutoff aggregate debt be paid by a
scaled legal predecessor charge.  For a literally attached reachable edge,
one-edge conservation gives the sharp bound
`residual ≤ jointContinue * oldDebt + |I| * M * charge`.  Thus the new
diagonal seam is charged automatically, but old debt that survives joint
Continue is a separate potential and must itself be charged before the
consumer closes.  A rational augmented-cap regression has positive carried
debt at an exact all-Continue Nash root with zero absorption, so no local
exact-Nash bound may erase this term; the regression does not assert
punishment-floor reachability.  A positive internal cutoff retains an arbitrary word,
while sure-joint and sure-solo caps introduce nonzero pure-exit boundaries;
those branches still need boundary reinsertion or an exact appended
Nash--Bellman chain.
Across a supplied coherent chronology of literally reachable predecessor
edges, the canonical remaining-capacity potential does amortize every new
diagonal seam.  Its scaled account is killed-excessive for aggregate debt,
and finite telescoping reduces all carried terms to one survival-weighted
far-end boundary comparison.  Neither reachability nor finite charge
capacity supplies that comparison, and the calibrated minimizers have not
yet been assembled into such a literal coherent reachable chronology.  A
literal reachable state must dominate the punishment floor coordinatewise,
which the zero-boundary aggregate-minimizer API does not establish; any
strict floor violation rules out the required identification.  At the other
end, a finitely killed window closes the telescope outright.  Otherwise the
only quantitative error is the exact survival-weighted far debt, so a
cofinal construction must make that remainder vanish or compare same-state
debt with remaining capacity.
When the punishment vector is coordinatewise nonpositive, every exact-`D`
point of every finite zero-boundary chain already dominates the floor.  The
reversed selected chain is therefore a literal path in the global
floor-admissible relation, starting from its own terminal zero-payoff state;
it becomes floor-anchor reachable if that one terminal state is reachable.
More importantly, the global admissible capacity potential telescopes debt
along each selected finite chain separately, so no nesting of minimizers
across cutoffs is needed.  The remaining hypothesis is still the same-state
terminal exact-debt cap being dominated by the terminal admissible capacity
account.  Nonpositive punishment does not prove that comparison.
The far datum is now explicit: terminal payoff is zero and terminal aggregate
debt is `sum_i max(0,r_i({i}))`.  If this cap vanishes, the telescope closes.
More generally, an admissible path ending at the terminal state reserves its
charge in terminal remaining capacity and closes the estimate when the
scaled incoming charge pays that cap.  The intrinsic reversed chain has the
opposite orientation and spends, rather than funds, terminal capacity.  A
two-player regression has nonpositive punishment values but positive
terminal cap, so `punishment ≤ 0` alone cannot erase the boundary; it is not
a counterexample-regime witness and does not falsify the full capacity
inequality.
The terminal cap is at most the reward bound `M`, rather than merely
`|I|*M`.  In a counterexample regime it is positive, and the player-cardinality
restriction therefore makes it strictly smaller than `|I|*M`; the former
saturation branch cannot occur.  Nevertheless the canonical one-owner funding
root never supplies the desired incoming edge: its selected owner has positive
singleton reward, so the exact zero-target Bellman row gives a finite Farkas
obstruction.  Any physical funding root must enlarge support, and every such
root must place positive conditional mass on a simultaneous-quitting coalition
that pays the positive-singleton owner strictly negatively.  A compatible
two-owner tangent packet with vanishing pair-join rows still cannot provide
this zero-target lift on exactly its two-owner support.

Capacity can also be optimized without discarding chronology: among literal
zero-boundary exact-`D` chains, a near-maximal chain has an actual state-matched
predecessor edge of arbitrarily small absorption while retaining positive
aggregate debt.  Payoff drift, debt loss, and normalized owner hazards are all
uniformly bounded on charge scale.  This is the correct compact control datum,
but not yet a viability theorem.  At zero absorption an exact dynamic-debt edge
fixes payoff and debt while leaving the successor stored root arbitrary; two
successive zero-charge limits therefore collapse to the known positive-debt
all-Continue phantom plateau.  No current equation controls root velocity or
turns this compactified edge into a strategic return.

Conditioning a positive-survival tail on eventual absorption provides a
second, chronology-preserving normalization.  Its conditioned values satisfy
an exact affine recursion with absorption weight in `[0,1]`, remain in the
reward box, and approach the active singleton face at the corresponding
relative opponent-absorption rate.  Singleton-support rows admit exact
product-root purification at the new hazard scale.  Multi-owner rows are
rigid: with positive Continue mass and two active marginals, preserving the
conditional nonempty-coalition law forces scale one, so a genuine phantom
boundary cannot be removed by exact rowwise product rescaling.

Conditioning also has a sharp punishment-floor boundary.  Coordinates where
the phantom plateau equals the punishment floor remain viable at every
conditionable date; a violation can occur only at a coordinate with strict
plateau slack, and its size is paid quantitatively by that slack.  A common
affine shrink restores all floors pointwise, but exact transport of the shrink
retains a positive Never mass, so this is not a strategic repair.  On the
stronger stratum where every source row is an interior literal singleton row
and the plateau is coordinatewise singleton-tight, conditioning preserves the
exact Bellman and endpoint-Nash equations along the whole path.  Absence of a
uniform equilibrium then forces an opponent-survival obstruction.  Two
persistent owners kill every deleted clock.  A positive-rate one-owner limit
is a stationary solo endpoint equilibrium; punishment completion enforces
its singleton payoff, even when the owner's own payoff is negative.  Thus the
remaining tight-singleton obstruction is genuinely diffuse.

That diffuse stratum has a complete clock alternative. Divide every
source hazard by the remaining eventual-absorption mass.  The resulting
product roots are legal, retain every nonsummable player-deleted clock, and
approximate the conditioned coalition law quadratically in the normalized
mesh.  Exact source complementarity improves the active Continue error to the
player-deleted absorption scale.  A two-clock telescope therefore gives an
explicit asymptotic Nash profile whenever the boundary is coordinatewise
singleton-tight, the mesh is uniformly small, and every conditioned deleted
clock is nonsummable. Its policy, Quit, and Continue errors are all linear in
the mesh bound and vanish on late diffuse suffixes. If one deleted clock is
summable, rescaling instead forces a unique nonsummable owner, summable
non-owner hazards, and literal terminal convergence to the owner's singleton
vector. Owner-active rows feed the approximate punishment-completed solo
compiler under singleton individual rationality. Exact rowwise purification
is unnecessary: both deleted-clock cases compile on the singleton-tight
stratum. On a proper face, strict plateau players are literal `Never` and the
compiler leaves only their uniform immediate-Quit defect. If a deleted clock
is summable while that defect vanishes, direct conditioned solo extraction
places the owner's singleton vector above every singleton floor and punishment
completion compiles it. Hence a counterexample has a fixed positive rescaled
Quit defect recurring arbitrarily far along the tail, independently of its
deleted-clock classification. One fixed strict-plateau outsider realizes this
defect cofinally while remaining prescribed `Never`; its conditioned value is
uniformly below its singleton reward, and its literal endpoint difference
against the next conditioned target is uniformly positive. At a fixed
continuation this is a discontinuous reset obligation: support-local endpoint
optimality with tolerance below the gap forces the obstructing player to Quit
surely, while changing only that player's marginal cannot reduce the endpoint
gap. Mixed-Nash existence supplies a positive-absorption endpoint root into
each target below a singleton reward. These roots need not preserve the
punishment floor or match their Bellman predecessor to the source chronology.

Negative ordinary tangent also has an exact conditioned interpretation.  It
either remains a negative conditioned delivery gap, giving strict upward
conditioned motion on a boundary-safe coordinate, or is quantitatively paid
by strict phantom slack.  At an active negative coordinate the repeated-root
phase gain converges to the negated tangent.  The exact punishment threshold
is whether the tangent magnitude fits inside plateau punishment slack.  If it
does not, the repeated-root delivery is eventually both phase-exploitable and
below the punishment floor.  Exact affine shrink transport cannot repair this
by rejoining the original chronology at a finite date.  These are real
restrictions, but do not attach the diagnostic repetition to the varying
source suffix.

The literal eventual all-Continue alternative has no hidden late dynamics.
Two consecutive all-Continue roots force equality of the complete augmented
states, so the tail is eventually the constant extracted limit.  Its actual
terminal payoff is zero and the displayed value is wholly phantom.  The
selected owner nevertheless satisfies
`terminalGap ≤ debt ≤ singleton reward ≤ displayed value`.  Every positive
solo rate has a strict joining blocker, and any exact endpoint-Nash root at
that singleton target with positive owner hazard must place positive hazard
on a second player.  This forces support enlargement without solving the
enlarged root's simultaneous complementarity equations.

The strategic consumers are explicit.  Any supplied finite
collision-aware product-root return satisfying exact Nash and punishment
admissibility is a solved exact cycle.  On the proper singleton stratum, a
state-matched Nash--Bellman cycle with changing owners is already an essential
APS cycle and needs no separate punishment field.  Likewise, a simultaneous
all-player zero-debt-source face return compiles to a solved cycle.  A
counterexample forbids all three.  What is not supplied is the common
chronological word itself.  Playerwise target-closed punishment tails do not
glue: their simultaneous existence is compatible with a strictly positive
common-tail repair value, and the packet's strict preference lasso actually
excludes using the whole packet mass as a singleton-circulation phase.
-/
