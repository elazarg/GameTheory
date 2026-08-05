import FixedPointTheorems.brouwer
import FixedPointTheorems.kakutani
import GameTheory
import Math.SchauderFixedPoint

-- Fixed-point infrastructure used by existence theorems.
#print axioms brouwer_fixed_point
#print axioms brouwer_fixed_point_isFixedPt
#print axioms brouwer_fixedPoints_nonempty
#print axioms kakutani_fixed_point
#print axioms Math.Schauder.schauder_fixed_point
#print axioms Math.Schauder.schauder_fixed_point_isFixedPt
#print axioms Math.Schauder.schauder_fixedPoints_nonempty

-- README headline theorem packages.
#print axioms GameTheory.KernelGame.mixed_nash_exists
#print axioms GameTheory.KernelGame.correlatedEq_exists
#print axioms GameTheory.KernelGame.coarseCorrelatedEq_exists
#print axioms EFG.zermelo
#print axioms EFG.oneShotDeviation_iff_spe
#print axioms GameTheory.KernelGame.von_neumann_minimax
#print axioms ObsModel.kuhn_behavioral_to_mixed
#print axioms ObsModel.kuhn_mixed_to_behavioral_semantic
#print axioms ObsModelCore.kuhn_behavioral_to_mixed
#print axioms ObsModelCore.kuhn_mixed_to_behavioral_semantic
#print axioms GameTheory.arrow_impossibility_exact
#print axioms GameTheory.SCF.gibbard_satterthwaite
#print axioms GameTheory.May.may_theorem
#print axioms GameTheory.GeneralMechanism.revelation_principle
#print axioms GameTheory.SocialChoice.FairDivision.Divisible.stromquist_envyFree_exists
#print axioms GameTheory.SocialChoice.FairDivision.Divisible.MeasureInstance.envyFree_exists
#print axioms GameTheory.CoalGame.shapleyValue_unique
#print axioms GameTheory.VNM.exists_representsExpectedUtility_of_vnmAxioms
#print axioms GameTheory.VNM.vnmAxioms_iff_exists_representsExpectedUtility

-- Repeated games and online learning.
#print axioms GameTheory.KernelGame.discounted_folk_theorem_approx
#print axioms Math.OnlineLearning.mw_externalRegret_le
#print axioms GameTheory.KernelGame.timeAverage_isεCCE_of_regret_le
#print axioms Math.Approachability.blackwell_approaches
#print axioms Math.Approachability.regretMatch_approaches

-- Auction and mechanism-design headline results.
#print axioms GameTheory.VCGSetup.vcg_truthful
#print axioms GameTheory.vickrey_truthful_dominant
#print axioms GameTheory.ReserveVickrey.mechanism_isDSIC
#print axioms GameTheory.KnapsackAuction.welfareMaximizingMechanism_isDSIC
#print axioms GameTheory.SingleParameterMechanism.existsUnique_zeroNormalized_payment_of_isMonotone

-- Social choice, matching, and cooperative games.
#print axioms GameTheory.sen_paretian_liberal
#print axioms GameTheory.median_is_condorcet_winner
#print axioms GameTheory.MatchingMarket.exists_stable
#print axioms GameTheory.MatchingMarket.OptionalOrder.lattice
#print axioms GameTheory.CoalGame.IsCore.isBalanced
#print axioms GameTheory.CoalGame.costOfStability_eq_zero_iff_core
#print axioms GameTheory.CoalGame.banzhafIndex_additive
#print axioms GameTheory.CoalGame.shapleyShubikIndex_sum_eq_one

-- Indivisible fair division and correlation saturation.
#print axioms GameTheory.SocialChoice.FairDivision.Indivisible.roundRobinAllocation_isEF1
#print axioms GameTheory.SocialChoice.FairDivision.Indivisible.exists_efx_two_agents
#print axioms GameTheory.KernelGame.strictDominant_isCoarseCorrelationSaturated
#print axioms GameTheory.KernelGame.IsIESDSSolvable.isCorrelationSaturated

-- ============================================================================
-- Uniform-equilibrium / quitting-game program: headline landed declarations.
-- The two intentional open declarations (`GameTheory.quittingGame_exists_
-- uniformEquilibriumPayoff` and `GameTheory.exists_uniformDeviationCapConstructor`)
-- are deliberately excluded: they carry `sorry` and are expected to report it.
-- ============================================================================

-- Terminal-to-uniform selection and the asymptotic-Nash bridge.
#print axioms GameTheory.StochasticGame.isUniformεEquilibrium_of_isεAsymptoticNash_of_upperApproximation
#print axioms GameTheory.quittingGame_exists_uniformEquilibriumPayoff_of_terminalNash_all_errors
#print axioms GameTheory.quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors

-- The admissible-cycle compiler and the three-branch trichotomy.
#print axioms GameTheory.exists_uniformEquilibriumPayoff_of_admissible_quittingCyclicContinuationBlock
#print axioms GameTheory.exists_uniformEquilibriumPayoff_of_zeroSolo_or_admissibleCycle
#print axioms GameTheory.quittingCycle_zeroSolo_or_admissible_or_isolatedNegative
#print axioms GameTheory.QuittingDisjunctionCounterexample.not_zeroSolo_and_not_admissible_and_isolatedNegative
#print axioms GameTheory.quittingThreeBranch_not_mutually_exclusive

-- The two-player closure of the quitting conjecture.
#print axioms GameTheory.QuittingTwoPlayerExistence.quittingGame_exists_uniformEquilibriumPayoff_twoPlayer
#print axioms GameTheory.QuittingTwoPlayerExistence.quittingGame_isUniformEquilibriumPayoff_jointExit

-- The exact dynamic-debt transport law and the seam-price results.
#print axioms GameTheory.quittingFiniteDynamicDebt_eq_max_zero_sub_accumulatedStageGaps
#print axioms GameTheory.quitting_sub_blockFixedPoint_eq_div
#print axioms GameTheory.QuittingSeamPriceDeviationFalsity.seamPriceLaw_fails_for_deviation_via_fullDeficit

-- Punishment level and individual rationality.
#print axioms GameTheory.StochasticGame.punishmentLevel_le_add_of_isUniformEquilibriumPayoff
#print axioms GameTheory.StochasticGame.not_isUniformEquilibriumPayoff_of_punishmentLevel_gt
#print axioms GameTheory.StochasticGame.eventually_isεIndividuallyRational_of_isUniformEquilibriumPayoff
#print axioms GameTheory.punishmentLevel_quittingGame_le_max

-- The action-legality chain, including the disintegration payoff equality.
#print axioms GameTheory.StochasticGame.finiteAveragePayoff_devPrime_eq
#print axioms GameTheory.StochasticGame.isLegalUniformEquilibriumPayoff_of_witness

-- The `PMF Bool` / real-hazard encoding bridge.
#print axioms GameTheory.isExactRowComplementary_hazardOfRoot_iff

-- The perturbed-cyclic-weight exclusion and the row dichotomy it restates.
#print axioms GameTheory.atMostOnePositive_of_isεQuittingRootEndpointNash_cyclicWeightReward
#print axioms GameTheory.atMostOnePositive_of_isExactRowComplementary

-- Joint complementarity, absorption-from-optimality, and coordinate silence.
#print axioms GameTheory.isQuittingJointComplementary_quittingCyclicBlockRoots
#print axioms GameTheory.isCompletelyAbsorbing_of_isQuittingJointComplementary_of_solo_pos
#print axioms GameTheory.QuittingCandidateHardWeightCoordinateSilence.quitProbability_true_eq_zero_of_isQuittingJointComplementary

-- Backward stability of root ε-complementarity (E64, period-one base case)
-- and the lens-identity's first leg: the condition number is the
-- weighted-to-unweighted conversion factor.
#print axioms GameTheory.exists_exact_of_isεQuittingRootEndpointNash
#print axioms GameTheory.exists_exact_of_pure
#print axioms GameTheory.abs_le_div_min_of_weighted_bounds
#print axioms GameTheory.abs_quittingRootEndpointDifference_le_div_min_of_isεQuittingRootEndpointNash
#print axioms GameTheory.exists_exact_ownShift_abs_eq_abs_quittingRootEndpointDifference
#print axioms GameTheory.min_lt_inv_of_exists_weighted_bound_not_isεRowComplementary

-- The weighted continue-mass bound and its scaled-cyclic-weight absence package.
#print axioms GameTheory.exists_pos_le_continueMass
#print axioms GameTheory.hasNoInstantApproxEquilibria_scaledCyclicWeight

-- The two-coordinate circulation boundary: the headline closed form.
#print axioms GameTheory.QuittingCirculationTwoCoordinateBoundary.circulationTwoExists_iff

-- The repaired four-player stress-point orbit and the general multi-owner
-- face-circulation orbit theorem.
#print axioms GameTheory.RepairedFourPlayerStress.exists_stressCirculation_orbit
#print axioms GameTheory.exists_multiCirculation_orbit

-- The one-sided decision-variation maximal inequality and the quitting
-- live-chain domination cap.
#print axioms Math.Probability.expect_indicator_scoreRunningMax_le_div
#print axioms GameTheory.quittingTerminalPayoff_update_quittingPhaseSwitchProfile_le_of_quitRegret_le

-- The pinned-pure row decoupling exclusion.
#print axioms GameTheory.not_isExactRowComplementary_cyclicWeight_of_pinned
