import Math.Probability
import Math.Fin
import Math.Fintype
import Math.Fintype.Transport
import Math.List
import Math.Reindex
import Math.ProbabilityMassFunction
import Math.FiniteProbabilityMassFunction
import Math.ProbabilityMassFunction.TotalVariation
import Math.ProbabilityMassFunction.Distinguishing
import Math.ProbabilityMassFunction.Simplex
import Math.PMFProduct
import Math.Coupling
import Math.PMFIter
import Math.OutcomeClosure
import Math.Knowledge
import Math.NondeterministicRefinement
import Math.TraceRun
import Math.ParameterizedChain
import Math.OptimizationLocalGlobal
import Math.AffineLowerEnvelope
import Math.BoundedLists
import Math.DAG
import Math.WeightedMedian
import Math.WindowedContraction
import Math.SchauderFixedPoint
import Math.SimplexApproximation
import Math.Simplex
import Math.OnlineLearning
import Math.OnlineAlgorithms
import Math.MeasureTheory.UnitInterval
import Math.FixedPoint.KKM
import Math.FixedPoint.Scarf
import Math.Minimax.MinimaxLoomis
import Math.Minimax.Loomis
import Math.LinearAlgebra.FourierMotzkin
import Math.LinearAlgebra.Farkas
import Math.LinearAlgebra.PerronFrobenius
import Math.LinearAlgebra.Pi
import Math.LinearAlgebra.WeightedIncidence
import Math.LinearAlgebra.ZeroSum
import Math.LinearProgramming
import Math.Topology.WeakDominance

/-!
# Math

Public umbrella for the repository's standalone mathematical library. Modules
under `Math/` may support GameTheory developments, independent proof routes,
or downstream users directly. Consequently, absence of an in-repository
GameTheory caller is not by itself a deprecation signal; public results such as
Scarf, Loomis minimax, Perron--Frobenius, and the specialized topology and
optimization utilities are intentionally built by this target.
-/
