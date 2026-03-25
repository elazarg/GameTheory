import GameTheory.Languages.MAID.Syntax

/-!
# Fold-Based MAID Evaluation

Sequential evaluation of a MAID by folding `evalStep` along a topological order.
This is the natural description of what an EFG tree computes when unrolling a MAID,
so it lives here (separate from the order-free `evalAssignDist` in `Syntax.lean`)
for use by the MAID→EFG bridge.

## Main definitions

- `evalStep` — one step: draw at node `nd`, update assignment
- `evalFold` — fold `evalStep` along a topological order

## Main results

- `evalFold_eq_assignProb` — fold = Bayesian product pointwise
- `evalAssignDist_eq_evalFold` — canonical PMF = fold
- `evalStep_swap` — independent nodes commute
- `evalFold_swap_adj` — swapping adjacent independent nodes preserves the fold
-/

namespace MAID

open GameTheory

variable {Player : Type} [DecidableEq Player] [fp : Fintype Player] {n : Nat}

-- ============================================================================
-- Fold definitions
-- ============================================================================

/-- One step of the evaluation fold: draw a value at `nd` and update the assignment. -/
noncomputable def evalStep (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (acc : PMF (TAssign S)) (nd : Fin n) : PMF (TAssign S) :=
  acc.bind (fun a =>
    (nodeDist S sem pol nd a).bind (fun v =>
      PMF.pure (updateAssign a nd v)))

/-- Fold-based evaluation along a topological order. This computes the same
distribution as `assignProb` (see `evalFold_eq_assignProb`) but is easier
to relate to sequential tree constructions (e.g. EFG reduction). -/
noncomputable def evalFold (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (σ : TopologicalOrder S) : PMF (TAssign S) :=
  σ.order.foldl (evalStep S sem pol) (PMF.pure (defaultAssign S))

-- ============================================================================
-- Fold = Bayesian product
-- ============================================================================

/-- The fold-based evaluation computes the Bayesian network product formula. -/
theorem evalFold_eq_assignProb (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (σ : TopologicalOrder S) (a : TAssign S) :
    (evalFold S sem pol σ) a = assignProb S sem pol a := by
  unfold evalFold assignProb
  -- evalStep unfolds to the inline lambda in bayesian_marginal_fold
  change (σ.order.foldl (fun acc nd => acc.bind (fun a' =>
    (nodeDist S sem pol nd a').bind (fun v =>
      PMF.pure (updateAssign a' nd v))))
    (PMF.pure (defaultAssign S))) a = _
  rw [bayesian_marginal_fold sem pol σ.order σ.nodup
    (fun i p hp => σ.respects i p hp) a]
  have hmem : ∀ nd : Fin n, nd ∈ σ.order := σ.mem
  have hcond : (∀ nd, ¬ nd ∈ σ.order → a nd = (defaultAssign S) nd) = True :=
    propext ⟨fun _ => trivial, fun _ nd h => absurd (hmem nd) h⟩
  simp only [hcond, ite_true, mul_one]
  congr 1
  have hfs : σ.order.toFinset = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [List.toFinset_card_of_nodup σ.nodup, σ.length, Fintype.card_fin]
  rw [hfs]

/-- `evalAssignDist` agrees with fold-based evaluation along any topological order. -/
theorem evalAssignDist_eq_evalFold (S : Struct Player n) (sem : Sem S) (pol : Policy S)
    (σ : TopologicalOrder S) :
    evalAssignDist S sem pol = evalFold S sem pol σ := by
  ext a; exact (evalFold_eq_assignProb S sem pol σ a).symm

-- ============================================================================
-- Order-independence — swap lemmas
-- ============================================================================

/-- Swapping two adjacent independent nodes in `evalStep` gives the same result. -/
theorem evalStep_swap {S : Struct Player n} (sem : Sem S) (pol : Policy S)
    (nd₁ nd₂ : Fin n) (hne : nd₁ ≠ nd₂)
    (hindep : NoDirectEdge S nd₁ nd₂)
    (acc : PMF (TAssign S)) :
    evalStep S sem pol (evalStep S sem pol acc nd₁) nd₂ =
    evalStep S sem pol (evalStep S sem pol acc nd₂) nd₁ := by
  simp only [evalStep, PMF.bind_bind, PMF.pure_bind]
  congr 1; funext a
  simp_rw [nodeDist_update_irrel sem pol nd₁ nd₂ a _ hindep.1]
  simp_rw [nodeDist_update_irrel sem pol nd₂ nd₁ a _ hindep.2]
  simp_rw [updateAssign_comm a nd₁ nd₂ _ _ hne]
  exact PMF.bind_comm _ _ _

/-- Swap two adjacent elements in a list. -/
def swapAdj (l : List α) (i : Nat) (hi : i + 1 < l.length) : List α :=
  let a := l[i]'(by omega)
  let b := l[i + 1]'hi
  (l.set i b).set (i + 1) a

/-- General lemma: swapping adjacent elements in a `foldl` is invariant when
    the fold function commutes on those two elements (for any accumulator). -/
theorem foldl_swapAdj {α β : Type*} (f : α → β → α) (init : α) (l : List β)
    (i : Nat) (hi : i + 1 < l.length)
    (hcomm : ∀ acc, f (f acc (l[i]'(by omega))) (l[i + 1]'hi) =
                     f (f acc (l[i + 1]'hi)) (l[i]'(by omega))) :
    l.foldl f init = (swapAdj l i hi).foldl f init := by
  induction i generalizing l init with
  | zero =>
    match l, hi with
    | a :: b :: rest, _ =>
      simp only [swapAdj, List.getElem_cons_zero, List.getElem_cons_succ,
                  List.set_cons_zero, List.set_cons_succ, List.set_cons_zero,
                  List.foldl_cons]
      have h := hcomm init
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h
      rw [h]
  | succ j ih =>
    match l, hi with
    | x :: xs, hi' =>
      simp only [List.foldl_cons]
      have hlen : j + 1 < xs.length := by
        simp only [List.length_cons] at hi'; omega
      have hswap : swapAdj (x :: xs) (j + 1) hi' = x :: swapAdj xs j hlen := by
        unfold swapAdj
        simp [List.getElem_cons_succ, List.set_cons_succ]
      rw [hswap, List.foldl_cons]
      exact ih (f init x) xs hlen (fun acc => by
        have := hcomm acc
        simp only [List.getElem_cons_succ] at this
        exact this)

/-- Swapping two adjacent independent nodes in a topological order doesn't change
the fold-based evaluation. -/
theorem evalFold_swap_adj {S : Struct Player n} (sem : Sem S) (pol : Policy S)
    (σ : TopologicalOrder S)
    (i : Nat) (hi : i + 1 < σ.order.length)
    (hne : σ.order[i]'(by omega) ≠ σ.order[i + 1]'hi)
    (hindep : NoDirectEdge S (σ.order[i]'(by omega)) (σ.order[i + 1]'hi)) :
    evalFold S sem pol σ =
    (swapAdj σ.order i hi).foldl (evalStep S sem pol) (PMF.pure (defaultAssign S)) := by
  simp only [evalFold]
  exact foldl_swapAdj _ _ _ i hi (fun acc =>
    evalStep_swap sem pol _ _ hne hindep acc)

end MAID
