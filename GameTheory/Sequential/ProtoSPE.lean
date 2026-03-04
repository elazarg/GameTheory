import GameTheory.Sequential.SeqProto
import GameTheory.Concepts.SolutionConcepts
import Math.Probability
import Math.ProbabilityMassFunction

/-!
# Subgames and Subgame-Perfect Equilibrium on Protocol

Defines subgames of a `Protocol` and subgame-perfect equilibrium (SPE) at the
Protocol level of abstraction. Concrete formats (EFG, MAID, NFG) can encode
into Protocol and inherit these definitions as corollaries.

## Main definitions

- `evalRounds_cons` — single-round decomposition
- `evalRounds_append` — concatenation decomposition
- `Protocol.subgameEval` — evaluate a subgame (suffix from index `k`, state `s`)
- `Protocol.subgameEu` — expected utility at a subgame
- `Protocol.IsSubgamePerfect` — Nash at every subgame
- `Protocol.spe_implies_isNash` — SPE implies full-game Nash

## Design

A subgame at `(k, s)` is the suffix `G.rounds.drop k` starting from state `s`.
The full game is the subgame at `(0, G.init)`.
-/

namespace GameTheory

open Math.Probability

variable {n : ℕ} {S V A Sig : Type}

-- ============================================================================
-- Decomposition lemmas for evalRounds
-- ============================================================================

/-- Evaluation of an empty list of rounds is a point mass at the initial state. -/
@[simp]
theorem evalRounds_nil (σ : PureProfile n V A) (s : S) :
    evalRounds ([] : List (Round n S V A Sig)) σ s = PMF.pure s := rfl

/-- Single-round decomposition: evaluating `r :: rest` is the same as
    evaluating `r` then binding the rest. -/
theorem evalRounds_cons (r : Round n S V A Sig) (rest : List (Round n S V A Sig))
    (σ : PureProfile n V A) (s : S) :
    evalRounds (r :: rest) σ s = (r.eval σ s).bind (evalRounds rest σ) := by
  simp only [evalRounds, List.foldl]
  rw [Math.ProbabilityMassFunction.foldl_bind_eq_bind_foldl_pure]
  exact congrArg (PMF.bind · (evalRounds rest σ)) (PMF.pure_bind s (r.eval σ))

/-- Concatenation decomposition: evaluating `l₁ ++ l₂` is the same as
    evaluating `l₁` then binding `l₂`. -/
theorem evalRounds_append (l₁ l₂ : List (Round n S V A Sig))
    (σ : PureProfile n V A) (s : S) :
    evalRounds (l₁ ++ l₂) σ s = (evalRounds l₁ σ s).bind (evalRounds l₂ σ) := by
  induction l₁ generalizing s with
  | nil => simp [evalRounds, PMF.pure_bind]
  | cons r rest ih =>
    rw [List.cons_append, evalRounds_cons, evalRounds_cons]
    rw [PMF.bind_bind]
    congr 1; funext s'
    exact ih s'

-- ============================================================================
-- Subgames
-- ============================================================================

/-- A subgame of protocol `G` at index `k` and state `s`:
    play the suffix `G.rounds.drop k` starting from state `s`. -/
noncomputable def Protocol.subgameEval (G : Protocol n S V A Sig)
    (k : ℕ) (s : S) (σ : PureProfile n V A) : PMF S :=
  evalRounds (G.rounds.drop k) σ s

/-- The full protocol evaluation decomposes into prefix + suffix. -/
theorem Protocol.eval_decompose (G : Protocol n S V A Sig)
    (k : ℕ) (σ : PureProfile n V A) :
    G.eval σ = (evalRounds (G.rounds.take k) σ G.init).bind
      (fun s => G.subgameEval k s σ) := by
  simp only [Protocol.eval, Protocol.subgameEval]
  rw [← evalRounds_append]
  simp [List.take_append_drop]

/-- Evaluating the subgame at index 0 from the initial state gives the full eval. -/
theorem Protocol.subgameEval_zero (G : Protocol n S V A Sig)
    (σ : PureProfile n V A) :
    G.subgameEval 0 G.init σ = G.eval σ := by
  simp [Protocol.subgameEval, Protocol.eval, List.drop]

-- ============================================================================
-- Expected utility at a subgame
-- ============================================================================

/-- Expected utility of player `i` at subgame `(k, s)` under utility `u`. -/
noncomputable def Protocol.subgameEu (G : Protocol n S V A Sig)
    (u : S → Fin n → ℝ) (k : ℕ) (s : S) (σ : PureProfile n V A)
    (i : Fin n) : ℝ :=
  expect (G.subgameEval k s σ) (fun s' => u s' i)

-- ============================================================================
-- Subgame-perfect equilibrium
-- ============================================================================

open Classical in
/-- A pure profile `σ` is a subgame-perfect equilibrium if at every
    subgame `(k, s)`, no player can improve their expected utility
    by deviating in `σ`. -/
def Protocol.IsSubgamePerfect (G : Protocol n S V A Sig)
    (u : S → Fin n → ℝ) (σ : PureProfile n V A) : Prop :=
  ∀ (k : ℕ) (s : S) (i : Fin n) (si' : PureStrategy V A),
    G.subgameEu u k s σ i ≥
      G.subgameEu u k s (Function.update σ i si') i

/-- SPE implies Nash equilibrium for the full game (the `k = 0, s = G.init` case). -/
theorem Protocol.spe_implies_nash (G : Protocol n S V A Sig)
    (u : S → Fin n → ℝ) (σ : PureProfile n V A)
    (hspe : G.IsSubgamePerfect u σ) :
    ∀ (i : Fin n) (si' : PureStrategy V A),
      G.subgameEu u 0 G.init σ i ≥
        G.subgameEu u 0 G.init (Function.update σ i si') i :=
  fun i si' => hspe 0 G.init i si'

open Classical in
/-- SPE implies Nash in the KernelGame sense: if σ is SPE, then it is Nash
    in the KernelGame derived from the protocol. -/
theorem Protocol.spe_implies_isNash (G : Protocol n S V A Sig)
    (u : S → Fin n → ℝ) (σ : PureProfile n V A)
    (hspe : G.IsSubgamePerfect u σ) :
    (G.toKernelGame u).IsNash σ := by
  intro who s'
  have h := hspe 0 G.init who s'
  simp only [ge_iff_le, KernelGame.eu, Protocol.toKernelGame, Protocol.eval]
  simp only [Protocol.subgameEu, Protocol.subgameEval, List.drop_zero, ge_iff_le] at h
  convert h using 2
  all_goals (congr 1; funext i; simp [Function.update])

end GameTheory
