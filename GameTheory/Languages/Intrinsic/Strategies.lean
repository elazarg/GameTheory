import GameTheory.Languages.Intrinsic.Syntax
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Strategy Types for Games in Intrinsic Form

Three notions of randomized strategies, following Section 3 of
Heymann–De Lara–Chancelier (2020):

1. **Mixed** (Definition 8): a probability distribution over a player's
   joint pure strategy space `Λₚ = ∏_{a ∈ Aₚ} Λₐ`.
2. **Product-mixed** (Definition 10): each agent independently randomizes
   over their own pure strategy space. A product-mixed strategy is a
   product probability `⊗_{a ∈ Aₚ} πₐ`.
3. **Behavioral** (Definition 11): each agent independently randomizes
   at each information set. A behavioral strategy is a family of
   information-measurable stochastic kernels `βₐ(· | h)`.

## Key results

- `Proposition12`: product-mixed → behavioral (the induced behavioral
  strategy, equation 24)
- `Proposition13`: behavioral → product-mixed (the realization, equation 25)
- These two directions hold unconditionally (no perfect recall needed).
-/

namespace Intrinsic

variable (G : WGame)

-- ============================================================================
-- Mixed W-strategies (Definition 8)
-- ============================================================================

/-- The pure strategy space of a player `p`: the product of pure strategy
    spaces of the player's agents. -/
def PlayerStrategySpace (G : WGame) (p : G.P) : Type :=
  ∀ a : G.agents p, PureStrategy G.toWModel a

/-- A mixed W-strategy for player `p`: a probability distribution over
    the player's joint pure strategy space (Definition 8). -/
def MixedStrategy (G : WGame) (p : G.P) : Type :=
  PMF (PlayerStrategySpace G p)

-- ============================================================================
-- Product-mixed W-strategies (Definition 10)
-- ============================================================================

/-- A product-mixed W-strategy for player `p`: each agent independently
    randomizes over their own pure strategy space (Definition 10).
    This induces a product probability over `Λₚ`. -/
def ProductMixedStrategy (G : WGame) (p : G.P) : Type :=
  ∀ a : G.agents p, PMF (PureStrategy G.toWModel a)

-- ============================================================================
-- Behavioral W-strategies (Definition 11)
-- ============================================================================

/-- A behavioral W-strategy for one agent `a`: an information-measurable
    stochastic kernel from configurations to decisions (Definition 11).

    `kernel h u` is the probability that agent `a` chooses decision `u`
    when the configuration is `h`. Information-measurability means the
    kernel is constant on equivalence classes of the agent's information. -/
structure BehavioralAgentStrategy (M : WModel) (a : M.A) where
  /-- The stochastic kernel: `kernel h` is a PMF over `U a`. -/
  kernel : M.H → PMF (M.U a)
  /-- Measurability: equivalent configurations yield the same distribution. -/
  meas : ∀ h h' : M.H, (M.info a).r h h' → kernel h = kernel h'

/-- A behavioral W-strategy for player `p`: a family of behavioral agent
    strategies, one per agent of the player. -/
def BehavioralStrategy (G : WGame) (p : G.P) : Type :=
  ∀ a : G.agents p, BehavioralAgentStrategy G.toWModel a

-- ============================================================================
-- Product-mixed → Behavioral (Proposition 12)
-- ============================================================================

/-- Proposition 12: A product-mixed strategy naturally induces a behavioral
    strategy. For each agent `a`, the induced behavioral kernel at
    configuration `h` assigns to decision `u` the probability
    `πₐ({λₐ ∈ Λₐ | λₐ(h) = u})` (equation 24). -/
noncomputable def productMixedToBehavioral (G : WGame) (p : G.P)
    (π : ProductMixedStrategy G p) : BehavioralStrategy G p := by
  classical
  intro ⟨a, ha⟩
  refine {
    kernel := fun h => (π ⟨a, ha⟩).map (fun s => s.act h)
    meas := ?_
  }
  intro h h' hequiv
  congr 1
  funext s
  exact s.meas h h' hequiv

-- ============================================================================
-- Behavioral → Product-mixed (Proposition 13)
-- ============================================================================

/-- Proposition 13: A behavioral strategy can be "realized" as a
    product-mixed strategy. For each agent, we construct a probability
    distribution over pure strategies as the product of the behavioral
    kernel values over all information set atoms (equation 26c).

    The key identity (equation 25):
    `π̌ₐ({λₐ | λₐ(h) = u}) = βₐ({u} | h)` -/
theorem behavioral_realizes_productMixed (G : WGame) (p : G.P)
    (β : BehavioralStrategy G p) :
    ∃ π : ProductMixedStrategy G p,
      ∀ (a : G.agents p) (h : G.toWModel.H) (u : G.toWModel.U a),
        (π a).toOuterMeasure {s | s.act h = u} =
        (β a).kernel h u := by
  sorry

end Intrinsic
