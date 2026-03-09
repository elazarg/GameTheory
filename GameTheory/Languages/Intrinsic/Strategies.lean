import GameTheory.Languages.Intrinsic.Syntax
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Math.PMFProduct

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

- `productMixedToBehavioral`: product-mixed → behavioral (Proposition 12)
- `behavioral_realizes_productMixed`: behavioral → product-mixed (Proposition 13)
- These two directions hold unconditionally (no perfect recall needed).
-/

namespace Intrinsic

open Math.PMFProduct

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
-- Information classes and strategy equivalence
-- ============================================================================

/-- The information quotient for agent `a`: configurations modulo the
    agent's information equivalence. Each element represents an
    information set. -/
abbrev InfoClass (M : WModel) (a : M.A) : Type :=
  Quotient (M.info a)

open Classical in
noncomputable instance (M : WModel) (a : M.A) : Fintype (InfoClass M a) :=
  Quotient.fintype (M.info a)

@[ext] theorem PureStrategy.ext {M : WModel} {a : M.A}
    {s t : PureStrategy M a} (h : s.act = t.act) : s = t := by
  cases s; cases t; simp_all

/-- Build a pure strategy from a function on information classes. -/
def PureStrategy.ofQuotientFun (M : WModel) (a : M.A)
    (f : InfoClass M a → M.U a) : PureStrategy M a where
  act := fun h => f ⟦h⟧
  meas := fun h h' hequiv => by
    show f ⟦h⟧ = f ⟦h'⟧
    congr 1
    exact Quotient.sound hequiv

/-- Extract the quotient function from a pure strategy. -/
noncomputable def PureStrategy.toQuotientFun (M : WModel) (a : M.A)
    (s : PureStrategy M a) : InfoClass M a → M.U a :=
  Quotient.lift s.act (fun h h' hequiv => s.meas h h' hequiv)

theorem PureStrategy.ofQuotientFun_toQuotientFun (M : WModel) (a : M.A)
    (s : PureStrategy M a) :
    PureStrategy.ofQuotientFun M a (PureStrategy.toQuotientFun M a s) = s := by
  ext1
  funext h
  simp [ofQuotientFun, toQuotientFun]

theorem PureStrategy.toQuotientFun_ofQuotientFun (M : WModel) (a : M.A)
    (f : InfoClass M a → M.U a) :
    PureStrategy.toQuotientFun M a (PureStrategy.ofQuotientFun M a f) = f := by
  ext q
  induction q using Quotient.inductionOn with
  | h x => simp [ofQuotientFun, toQuotientFun]

/-- Pure strategies for agent `a` are equivalent to functions from
    information classes to decisions. -/
noncomputable def pureStrategyEquiv (M : WModel) (a : M.A) :
    PureStrategy M a ≃ (InfoClass M a → M.U a) where
  toFun := PureStrategy.toQuotientFun M a
  invFun := PureStrategy.ofQuotientFun M a
  left_inv := PureStrategy.ofQuotientFun_toQuotientFun M a
  right_inv := PureStrategy.toQuotientFun_ofQuotientFun M a

open Classical in
noncomputable instance (M : WModel) (a : M.A) : Fintype (PureStrategy M a) :=
  Fintype.ofEquiv _ (pureStrategyEquiv M a).symm

-- ============================================================================
-- Behavioral → Product-mixed (Proposition 13)
-- ============================================================================

/-- The behavioral kernel descends to a well-defined PMF on each information
    class (it is constant on equivalence classes by measurability). -/
noncomputable def BehavioralAgentStrategy.classKernel
    {M : WModel} {a : M.A} (β : BehavioralAgentStrategy M a) :
    InfoClass M a → PMF (M.U a) :=
  Quotient.lift β.kernel (fun h h' hequiv => β.meas h h' hequiv)

@[simp] theorem BehavioralAgentStrategy.classKernel_mk
    {M : WModel} {a : M.A} (β : BehavioralAgentStrategy M a) (h : M.H) :
    β.classKernel ⟦h⟧ = β.kernel h :=
  rfl

open Classical in
/-- The product PMF over information classes. -/
noncomputable def behavioralProductPMF {M : WModel} {a : M.A}
    (β : BehavioralAgentStrategy M a) :
    PMF (InfoClass M a → M.U a) :=
  pmfPi β.classKernel

open Classical in
/-- Transport the product PMF on quotient functions to a PMF on pure strategies. -/
noncomputable def behavioralToPureStrategyPMF {M : WModel} {a : M.A}
    (β : BehavioralAgentStrategy M a) :
    PMF (PureStrategy M a) :=
  (behavioralProductPMF β).map (PureStrategy.ofQuotientFun M a)

/-- The preimage of `{s | s.act h = u}` under `ofQuotientFun` is
    `{f | f ⟦h⟧ = u}`. -/
theorem ofQuotientFun_preimage_act {M : WModel} {a : M.A}
    (h : M.H) (u : M.U a) :
    PureStrategy.ofQuotientFun M a ⁻¹' {s | s.act h = u} =
    {f | f ⟦h⟧ = u} := by
  ext f
  simp [PureStrategy.ofQuotientFun, Set.mem_setOf_eq]

open Classical in
/-- Key lemma: the probability that a randomly chosen pure strategy
    assigns decision `u` at configuration `h` equals `β(u | h)`.

    This is the marginal identity (equation 25). -/
theorem behavioralToPureStrategyPMF_marginal {M : WModel} {a : M.A}
    (β : BehavioralAgentStrategy M a) (h : M.H) (u : M.U a) :
    (behavioralToPureStrategyPMF β).toOuterMeasure {s | s.act h = u} =
    β.kernel h u := by
  -- Step 1: map + toOuterMeasure = toOuterMeasure of preimage
  rw [behavioralToPureStrategyPMF, PMF.toOuterMeasure_map_apply]
  -- Step 2: preimage simplification
  rw [ofQuotientFun_preimage_act]
  -- Step 3: expand toOuterMeasure as fintype sum
  rw [PMF.toOuterMeasure_apply_fintype]
  -- Step 4: this is exactly pmfPi_coord_mass
  simp only [Set.indicator, Set.mem_setOf_eq, behavioralProductPMF]
  rw [pmfPi_coord_mass β.classKernel ⟦h⟧ u]
  simp

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
        (β a).kernel h u :=
  ⟨fun a => behavioralToPureStrategyPMF (β a),
    fun a h u => behavioralToPureStrategyPMF_marginal (β a) h u⟩

end Intrinsic
