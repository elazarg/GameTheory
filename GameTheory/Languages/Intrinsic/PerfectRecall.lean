import GameTheory.Languages.Intrinsic.Strategies

/-!
# Perfect Recall and Kuhn's Equivalence Theorem for W-Games

Following Section 4 of Heymann–De Lara–Chancelier (2020).

## Perfect recall (Definition 14)

A player `p` enjoys perfect recall if, for any ordering prefix `κ` whose
last agent `κ⋆` belongs to player `p`, agent `κ⋆` knows at least what
did and knew those of their predecessors that also belong to player `p`.

Formally: for any atom `H` of the choice field `C_{‖κ⁻‖ ∩ Aₚ}` (the join
of choice fields of predecessors belonging to `p`), the intersection
`H^ϕ_κ ∩ H` belongs to `I_{κ⋆}`.

## Kuhn's theorem (Theorem 16)

Under perfect recall, for any mixed strategy `μₚ` there exists a
product-mixed strategy `πₚ` such that the outcome distributions agree
for all opponent strategies and all states of nature.

## Main definitions

- `ChoiceField` — the join of information and decision: `Cₐ = Uₐ ∨ Iₐ`
- `PerfectRecall` — the perfect recall property for a player
- `kuhn_equivalence` — Kuhn's theorem for W-games
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
    the choice field of predecessors belonging to `p` (Definition 14).

    The condition (28a): for any `H ∈ C_{‖κ⁻‖ ∩ Aₚ}` and any
    `h, h'` in `H^ϕ_κ` that are `C_{‖κ⁻‖ ∩ Aₚ}`-equivalent,
    they must be `I_{κ⋆}`-equivalent. -/
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

/-- The outcome distribution under a mixed strategy profile, for a given
    state of nature `ω` (Definition 9, equation 22a).

    Under solvability, each pure strategy profile determines a unique
    decision profile via the solution map. The mixed strategy pushes
    forward to a distribution over decision profiles. -/
noncomputable def outcomeDistribution (G : WGame) (hsolv : Solvable G.toWModel)
    (p : G.P) (μ : MixedStrategy G p) (ω : G.Ω) :
    PMF (∀ a : G.agents p, G.U a) :=
  μ.map (fun strat a => (strat a).act ⟨ω, solutionMap G.toWModel hsolv
    (fun a' => sorry) ω⟩)

-- ============================================================================
-- Kuhn's equivalence theorem (Theorem 16)
-- ============================================================================

/-- **Kuhn's equivalence theorem for W-games** (Theorem 16).

    In a causal finite W-game, if player `p` enjoys perfect recall, then
    for any mixed strategy `μₚ` there exists a product-mixed strategy `πₚ`
    such that the outcome distributions agree for all opponent strategies
    and all states of nature.

    The proof goes through three steps:
    1. Mixed → Behavioral (Proposition 15, uses perfect recall)
    2. Behavioral → Product-mixed (Proposition 13, unconditional)
    3. Probability identity (equation 32b) -/
theorem kuhn_equivalence (G : WGame) (hsolv : Solvable G.toWModel)
    (ϕ : ConfigOrdering G.toWModel) (hcausal : Causal G.toWModel)
    (p : G.P) (hpr : PerfectRecall G ϕ p) (μ : MixedStrategy G p) :
    ∃ π : ProductMixedStrategy G p,
      ∀ (h : G.toWModel.H) (ω : G.Ω),
        ∀ a : G.agents p,
          -- The marginal action distributions agree
          ((productMixedToBehavioral G p π) a).kernel ⟨ω, h.decision⟩ =
          sorry := by
  sorry

-- ============================================================================
-- Mixed → Behavioral under perfect recall (Proposition 15)
-- ============================================================================

/-- **Proposition 15**: Under perfect recall, any mixed strategy induces a
    behavioral strategy via the conditional probability formula (equation 29).

    For each agent `a ∈ Aₚ`, the induced behavioral kernel assigns to
    decision `u` at configuration `h` the conditional probability that
    the mixed strategy selects a pure strategy consistent with `u` at `h`,
    given that the pure strategy is consistent with the configuration's
    history. -/
theorem mixed_induces_behavioral (G : WGame)
    (ϕ : ConfigOrdering G.toWModel) (hcausal : Causal G.toWModel)
    (p : G.P) (hpr : PerfectRecall G ϕ p) (μ : MixedStrategy G p) :
    ∃ β : BehavioralStrategy G p,
      ∀ (a : G.agents p) (h : G.toWModel.H) (u : G.U a),
        (β a).kernel h u = sorry := by
  sorry

end Intrinsic
