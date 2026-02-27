import GameTheory.NFG
import GameTheory.EFG

/-!
## NFG → EFG: simultaneous game as a sequential tree

Embeds any finite normal-form game into an extensive-form game tree.
Players move sequentially (in `Fin n` order), each with a single
info set (imperfect information — no one observes previous moves).

### Definitions
- `nfgInfoS` — `InfoStructure` for an arbitrary NFG
- `nfgTree` — sequential tree built by folding over players
- `NFGGame.toEFG` — the `EFGGame` wrapping the tree

### Theorems
- `nfgTree_evalDist_pure` — evalDist under pure behavioral profile equals the NFG outcome
-/
namespace NFG

open EFG

variable {n : Nat} {A : Fin n → Type}
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]

-- ============================================================================
-- InfoStructure from an NFG
-- ============================================================================

/-- `InfoStructure` for an `n`-player simultaneous game.
    Each player has one info set (`Unit`), arity = `Fintype.card (A i)`. -/
@[reducible] def nfgInfoS (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] :
    InfoStructure where
  n := n
  Infoset := fun _ => Unit
  arity := fun p _ => Fintype.card (A p)
  arity_pos := fun _ _ => Fintype.card_pos

/-- Equivalence between `Fin (Fintype.card (A p))` and `A p`. -/
noncomputable def actEquiv (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (p : Fin n) : Fin (Fintype.card (A p)) ≃ A p :=
  Fintype.equivFin (A p) |>.symm

-- ============================================================================
-- Tree construction
-- ============================================================================

/-- Build a sequential EFG tree from an NFG outcome function.
    Iterates over the given list of players, each making a decision.
    `profile` accumulates the choices made so far. -/
noncomputable def nfgTreeAux (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    {Outcome : Type}
    (outcome : (∀ i, A i) → Outcome)
    (players : List (Fin n)) (profile : ∀ i, A i) :
    GameTree (nfgInfoS A) Outcome :=
  match players with
  | [] => .terminal (outcome profile)
  | p :: rest =>
    .decision (p := p) () (fun act =>
      nfgTreeAux A outcome rest (Function.update profile p (actEquiv A p act)))

/-- The full sequential tree for an NFG: players move in order `0, 1, …, n-1`. -/
noncomputable def nfgTree (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    {Outcome : Type}
    (outcome : (∀ i, A i) → Outcome) :
    GameTree (nfgInfoS A) Outcome :=
  nfgTreeAux A outcome (List.finRange n) (fun i => Classical.arbitrary (A i))

-- ============================================================================
-- EFGGame from NFG
-- ============================================================================

/-- Convert an NFGGame to an EFGGame. -/
noncomputable def NFGGame.toEFG (G : NFGGame (Fin n) A) : EFGGame where
  inf := nfgInfoS A
  Outcome := G.Outcome
  tree := nfgTree A G.outcome
  utility := G.utility

-- ============================================================================
-- Evaluation theorem
-- ============================================================================

/-- Helper: `nfgTreeAux` under a pure profile that plays `s p` for each player
    in the remaining list produces the final profile with those overrides. -/
private theorem nfgTreeAux_evalDist_pure
    (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    {Outcome : Type}
    (outcome : (∀ i, A i) → Outcome)
    (players : List (Fin n)) (profile : ∀ i, A i)
    (s : ∀ i, A i)
    (σ : BehavioralProfile (nfgInfoS A))
    (hσ : ∀ p, σ p () = PMF.pure ((actEquiv A p).symm (s p)))
    (hnodup : players.Nodup)
    (hall : ∀ i, i ∈ players ∨ profile i = s i) :
    (nfgTreeAux A outcome players profile).evalDist σ =
    PMF.pure (outcome s) := by
  induction players generalizing profile with
  | nil =>
    simp only [nfgTreeAux, evalDist_terminal]
    have : profile = s := funext fun i =>
      (hall i).elim (fun h => nomatch h) id
    rw [this]
  | cons p rest ih =>
    simp only [nfgTreeAux, evalDist_decision, hσ p, PMF.pure_bind]
    exact ih _ (hnodup.of_cons) (fun i => by
      by_cases hip : i = p
      · subst hip; right
        simp [Function.update, Equiv.apply_symm_apply]
      · rw [show Function.update profile p _ i = profile i from by simp [Function.update, hip]]
        exact (hall i).elim (fun hm => by
          cases List.mem_cons.mp hm with
          | inl h => exact absurd h hip
          | inr h => exact Or.inl h) Or.inr)

/-- Under a pure behavioral profile mapping each player `p` to action `s p`,
    the NFG tree evaluates to the NFG outcome at `s`. -/
theorem nfgTree_evalDist_pure
    (A : Fin n → Type)
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    {Outcome : Type}
    (outcome : (∀ i, A i) → Outcome)
    (s : ∀ i, A i)
    (σ : BehavioralProfile (nfgInfoS A))
    (hσ : ∀ p, σ p () = PMF.pure ((actEquiv A p).symm (s p))) :
    (nfgTree A outcome).evalDist σ = PMF.pure (outcome s) := by
  unfold nfgTree
  exact nfgTreeAux_evalDist_pure A outcome (List.finRange n) _ s σ hσ
    (List.nodup_finRange n) (fun i => Or.inl (List.mem_finRange i))


end NFG
