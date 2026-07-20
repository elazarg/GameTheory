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
