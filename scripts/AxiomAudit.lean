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
