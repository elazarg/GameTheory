module

/-
# `GameTheory.Analysis`

Opt-in analytic game theory.  This root gathers the stable topology,
convexity, fixed-point, convergence, learning, repeated, stochastic, and
protocol-analysis families without making any of them reachable from the
lightweight `GameTheory` umbrella.
-/

public import GameTheory.Analysis.Approachability
public import GameTheory.Analysis.BayesianHierarchy
public import GameTheory.Analysis.BimatrixCertificateExistence
public import GameTheory.Analysis.Correlated
public import GameTheory.Analysis.CorrelationHierarchy
public import GameTheory.Analysis.DominanceHierarchy
public import GameTheory.Analysis.FictitiousPlayPotential
public import GameTheory.Analysis.IncentiveCone
public import GameTheory.Analysis.IncentiveHierarchy
public import GameTheory.Analysis.Learning
public import GameTheory.Analysis.MatrixValue
public import GameTheory.Analysis.Protocol
public import GameTheory.Analysis.PseudoCorrelated
public import GameTheory.Analysis.PseudoNash
public import GameTheory.Analysis.Repeated
public import GameTheory.Analysis.Stochastic
public import GameTheory.Analysis.TremblingHand
public import GameTheory.Analysis.ZeroSumLearning

@[expose] public section

namespace GameTheory.Analysis

end GameTheory.Analysis
