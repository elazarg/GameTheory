/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticBellmanHierarchy
import Math.Probability.RealizedAccountDeflation

/-!
# Boundary of the processed harmonic-jet branch

The `processedJet` response in the analytic Bellman hierarchy contains only
a proof that its leading endpoint-harmonic coefficient belongs to the
previously processed span.  Extending by such a coefficient leaves both the
span and its well-founded rank unchanged.

Consequently that branch needs an independent discharge mechanism.  One
sound mechanism is the realized-account interface in
`Math.Probability.RealizedAccountDeflation`: stage charges must be actual
account increments, with controlled endpoint motion.  The one-dimensional
counterexample in that module proves that span membership alone does not
supply such an account.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame
namespace AnalyticBellmanGerm
namespace EndpointHarmonicJetSpan

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

omit [DecidableEq G.State] in
/-- Adjoining a direction already in the processed carrier does not enlarge
that carrier. -/
theorem carrier_extend_eq_of_mem
    (span : germ.EndpointHarmonicJetSpan)
    (H : G.State → Payoff ι)
    (harmonic : H ∈ germ.endpointHarmonicSubmodule)
    (processed : H ∈ span.carrier) :
    (span.extend H harmonic).carrier = span.carrier := by
  apply le_antisymm
  · change
      span.carrier ⊔ Submodule.span ℝ {H} ≤
        span.carrier
    apply sup_le le_rfl
    apply Submodule.span_le.mpr
    intro K hK
    rw [Set.mem_singleton_iff.mp hK]
    exact processed
  · exact le_sup_left

omit [DecidableEq G.State] in
/-- The harmonic rank is exactly unchanged in the processed branch. -/
theorem rank_extend_eq_of_mem
    (span : germ.EndpointHarmonicJetSpan)
    (H : G.State → Payoff ι)
    (harmonic : H ∈ germ.endpointHarmonicSubmodule)
    (processed : H ∈ span.carrier) :
    (span.extend H harmonic).rank = span.rank := by
  simp only [rank]
  rw [span.carrier_extend_eq_of_mem H harmonic processed]

end EndpointHarmonicJetSpan

namespace LowerValueJet

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : StochasticGame ι}
  [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
  {germ : G.AnalyticBellmanGerm}

omit [DecidableEq G.State] in
/-- The membership carried by `FirstHierarchyResponse.processedJet` cannot
serve as a recursive rank decrease. -/
theorem processed_extend_rank_eq
    (jet : germ.LowerValueJet)
    (span : germ.EndpointHarmonicJetSpan)
    (processed : jet.factor 0 ∈ span.carrier) :
    (span.extend
        (jet.factor 0)
        (span.carrier_le processed)).rank =
      span.rank :=
  span.rank_extend_eq_of_mem
    (jet.factor 0) (span.carrier_le processed) processed

end LowerValueJet
end AnalyticBellmanGerm
end StochasticGame
end GameTheory
