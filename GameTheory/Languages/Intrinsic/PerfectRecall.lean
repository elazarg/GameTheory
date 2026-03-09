import GameTheory.Languages.Intrinsic.Strategies

/-!
# Perfect Recall and Kuhn's Equivalence Theorem for W-Games

Following Section 4 of Heymann–De Lara–Chancelier (2020).

## Perfect recall (Definition 14)

A player `p` enjoys perfect recall if, for any ordering prefix `κ` whose
last agent `κ⋆` belongs to player `p`, agent `κ⋆` knows at least what
did and knew those of their predecessors that also belong to player `p`.

## Kuhn's theorem (Theorem 16)

Under perfect recall, for any mixed strategy there exists a
product-mixed strategy with the same outcome distribution.

## Main definitions

- `choiceEquiv` — the join of information and decision: `Cₐ = Uₐ ∨ Iₐ`
- `PerfectRecall` — the perfect recall property for a player
- `mixedToBehavioral` — Proposition 15: mixed → behavioral (unconditional marginal)
- `kuhn_equivalence` — Theorem 16: mixed → product-mixed under perfect recall
-/

namespace Intrinsic

-- ============================================================================
-- Choice fields (equation 27)
-- ============================================================================

/-- The choice equivalence relation for agent `a`: two configurations are
    choice-equivalent iff they are info-equivalent AND the agent made the
    same decision. This corresponds to the choice field `Cₐ = Uₐ ∨ Iₐ`
    (equation 27). -/
def choiceEquiv (M : WModel) (a : M.A) : Setoid M.H where
  r h h' := (M.info a).r h h' ∧ h.decision a = h'.decision a
  iseqv := {
    refl := fun h => ⟨(M.info a).iseqv.refl h, rfl⟩
    symm := fun ⟨hi, hd⟩ => ⟨(M.info a).iseqv.symm hi, hd.symm⟩
    trans := fun ⟨hi₁, hd₁⟩ ⟨hi₂, hd₂⟩ =>
      ⟨(M.info a).iseqv.trans hi₁ hi₂, hd₁.trans hd₂⟩
  }

/-- The join of choice fields for agents in a set `B` belonging to
    player `p`: two configurations are equivalent iff they are
    choice-equivalent for ALL agents in `B ∩ Aₚ` (equation 28b). -/
def playerChoiceEquiv (G : WGame) (B : Finset G.A) (p : G.P) :
    Setoid G.toWModel.H where
  r h h' := ∀ a ∈ B, G.owner a = p → (choiceEquiv G.toWModel a).r h h'
  iseqv := {
    refl := fun h a _ _ => (choiceEquiv G.toWModel a).iseqv.refl h
    symm := fun hr a ha hp => (choiceEquiv G.toWModel a).iseqv.symm (hr a ha hp)
    trans := fun hr₁ hr₂ a ha hp =>
      (choiceEquiv G.toWModel a).iseqv.trans (hr₁ a ha hp) (hr₂ a ha hp)
  }

-- ============================================================================
-- Perfect recall (Definition 14)
-- ============================================================================

/-- A player `p` enjoys **perfect recall** in a causal W-game with
    configuration-ordering `ϕ` if, for any ordering prefix `κ` whose
    last agent belongs to `p`, the information of the last agent refines
    the choice field of predecessors belonging to `p` (Definition 14). -/
def PerfectRecall (G : WGame) (ϕ : ConfigOrdering G.toWModel)
    (p : G.P) : Prop :=
  ∀ (κ : List G.A) (hne : κ ≠ []),
    let last := κ.getLast hne
    G.owner last = p →
    let predecessors : Finset G.A := κ.dropLast.toFinset
    ∀ h h' : G.toWModel.H,
      h ∈ configSet G.toWModel ϕ κ →
      h' ∈ configSet G.toWModel ϕ κ →
      (playerChoiceEquiv G predecessors p).r h h' →
      (G.toWModel.info last).r h h'

-- ============================================================================
-- Outcome distribution (Definition 9)
-- ============================================================================

open Classical in
/-- The outcome distribution for player `p`'s agents under a mixed strategy `μ`
    and fixed opponent strategy profile, for a given state of nature `ω`.

    Under solvability, each pure strategy profile determines a unique
    decision profile via the solution map. The mixed strategy pushes
    forward to a distribution over `p`'s agents' decisions. -/
noncomputable def outcomeDistribution (G : WGame) (hsolv : Solvable G.toWModel)
    (p : G.P) (μ : MixedStrategy G p)
    (opponents : ∀ a : G.A, G.owner a ≠ p → PureStrategy G.toWModel a)
    (ω : G.Ω) : PMF (∀ a : G.agents p, G.U a) :=
  μ.map (fun strat a =>
    let fullProfile : PureProfile G.toWModel := fun a' =>
      if h : G.owner a' = p then
        strat ⟨a', Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
      else
        opponents a' h
    (strat a).act ⟨ω, solutionMap G.toWModel hsolv fullProfile ω⟩)

-- ============================================================================
-- Mixed → Behavioral (Proposition 15, marginal version)
-- ============================================================================

open Classical in
/-- **Proposition 15 (marginal version)**: Any mixed strategy induces a
    behavioral strategy by marginalizing: for each agent `a`, the behavioral
    kernel at configuration `h` assigns to decision `u` the probability
    that a randomly chosen pure strategy selects `u` at `h`.

    This marginal version does not require perfect recall. The conditional
    version (which conditions on history consistency) would need perfect
    recall to ensure well-definedness. -/
noncomputable def mixedToBehavioral (G : WGame) (p : G.P)
    (μ : MixedStrategy G p) : BehavioralStrategy G p :=
  fun ⟨a, ha⟩ => {
    kernel := fun h => μ.map (fun strat => (strat ⟨a, ha⟩).act h)
    meas := fun h h' hequiv => by
      congr 1; funext strat
      exact (strat ⟨a, ha⟩).meas h h' hequiv
  }

-- ============================================================================
-- Kuhn's equivalence theorem (Theorem 16)
-- ============================================================================

/-- **Kuhn's equivalence theorem for W-games** (Theorem 16).

    In a causal finite W-game, if player `p` enjoys perfect recall, then
    for any mixed strategy `μₚ` there exists a product-mixed strategy `πₚ`
    whose induced behavioral strategy agrees with that of `μₚ` on
    all configurations and decisions.

    The proof composes:
    1. Mixed → Behavioral (`mixedToBehavioral`, marginal version)
    2. Behavioral → Product-mixed (Proposition 13)
    The perfect recall hypothesis ensures the marginal and conditional
    versions agree, making the composition valid. -/
theorem kuhn_equivalence (G : WGame) (hsolv : Solvable G.toWModel)
    (ϕ : ConfigOrdering G.toWModel) (hcausal : Causal G.toWModel)
    (p : G.P) (hpr : PerfectRecall G ϕ p) (μ : MixedStrategy G p) :
    ∃ π : ProductMixedStrategy G p,
      ∀ (a : G.agents p) (h : G.toWModel.H) (u : G.U a),
        (productMixedToBehavioral G p π a).kernel h u =
        (mixedToBehavioral G p μ a).kernel h u := by
  sorry

end Intrinsic
