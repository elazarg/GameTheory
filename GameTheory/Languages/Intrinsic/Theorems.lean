import GameTheory.Languages.Intrinsic.Compile

/-!
# Theorems for Games in Intrinsic Form

Structural results about W-games and their compilation to KernelGame.
-/

namespace Intrinsic

open GameTheory Math.Probability

-- ============================================================================
-- Solution map properties
-- ============================================================================

/-- The solution map satisfies the fixed-point equation. -/
theorem solutionMap_isFixedPoint (M : WModel) (hsolv : Solvable M)
    (strat : PureProfile M) (ω : M.Ω) (a : M.A) :
    solutionMap M hsolv strat ω a = (strat a).act ⟨ω, solutionMap M hsolv strat ω⟩ :=
  solutionMap_spec M hsolv strat ω a

/-- If two strategy profiles agree pointwise, they produce the same solution. -/
theorem solutionMap_ext (M : WModel) (hsolv : Solvable M)
    (strat strat' : PureProfile M) (ω : M.Ω)
    (h : ∀ a (h : M.H), (strat a).act h = (strat' a).act h) :
    solutionMap M hsolv strat ω = solutionMap M hsolv strat' ω := by
  have hfp : isFixedPoint M strat' ω (solutionMap M hsolv strat ω) := by
    intro a
    rw [solutionMap_isFixedPoint]
    exact h a _
  exact solutionMap_unique M hsolv strat' ω _ hfp

-- ============================================================================
-- Strategy lifting
-- ============================================================================

/-- The lifted profile recovers each agent's strategy from their owner's
    player strategy. -/
theorem liftProfile_apply (G : WGame) (strats : ∀ p : G.P, PlayerStrategySpace G p)
    (a : G.A) :
    liftProfile G strats a = strats (G.owner a) ⟨a, by simp [WGame.agents]⟩ :=
  rfl

/-- Product-mixed to behavioral preserves measurability. -/
theorem productMixedToBehavioral_meas (G : WGame) (p : G.P)
    (π : ProductMixedStrategy G p) (a : G.agents p)
    (h h' : G.toWModel.H) (hequiv : (G.toWModel.info a).r h h') :
    (productMixedToBehavioral G p π a).kernel h =
    (productMixedToBehavioral G p π a).kernel h' :=
  (productMixedToBehavioral G p π a).meas h h' hequiv

end Intrinsic
