/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.Foundations.Convergence
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Fictitious play

Fictitious play (Brown 1951): each player repeatedly plays a best response to the **empirical
frequency** of opponents' past pure actions. This is the belief-learning counterpart of the
payoff-learning no-regret dynamics (`NoRegretToCCE`).

This file gives the structural core: the empirical-marginal belief state and the fictitious-play
predicate on a play sequence (modelled as a predicate, in the library's `IsNash`/`IsStable` style,
rather than a tie-broken construction). The headline convergence theorems (Robinson for zero-sum,
Monderer–Shapley for potential games) are separate, harder developments; what is proved here is the
"limits of fictitious play are Nash" direction.

## Main definitions

* `KernelGame.empiricalMarginal` — player `j`'s empirical action distribution over the first `t`
  rounds
* `KernelGame.belief` — the profile of opponents' empirical marginals entering a round
* `KernelGame.IsFictitiousPlay` — the play sequence best-responds to the empirical beliefs each
  round
-/

namespace GameTheory

open Math.Probability
open scoped BigOperators

namespace KernelGame

variable {ι : Type} [DecidableEq ι] [Fintype ι] (M : KernelGame ι)

/-- The empirical distribution of player `j`'s pure actions over the first `t` rounds: the uniform
    average of the point masses at `a 0 j, …, a (t-1) j`. -/
noncomputable def empiricalMarginal (a : ℕ → M.Profile) (j : ι) (t : ℕ) [NeZero t] :
    PMF (M.Strategy j) :=
  (PMF.uniformOfFintype (Fin t)).bind (fun s => PMF.pure (a (s : ℕ) j))

omit [DecidableEq ι] [Fintype ι] in
open Classical in
/-- The empirical marginal weight is the count of matching past plays divided by
the averaging horizon. -/
theorem empiricalMarginal_apply_toReal
    (a : ℕ → M.Profile) (j : ι) (t : ℕ) [NeZero t] (s : M.Strategy j) :
    ((M.empiricalMarginal a j t) s).toReal =
      ((Finset.univ.filter fun k : Fin t => a (k : ℕ) j = s).card : ℝ) / t := by
  classical
  rw [empiricalMarginal, PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, PMF.pure_apply]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
    have hsum :
        (∑ x : Fin t, (if s = a (x : ℕ) j then (1 : ENNReal) else 0).toReal) =
          ((Finset.univ.filter fun k : Fin t => s = a (k : ℕ) j).card : ℝ) := by
      have htoReal :
          (∑ x : Fin t, (if s = a (x : ℕ) j then (1 : ENNReal) else 0).toReal) =
            ∑ x : Fin t, if s = a (x : ℕ) j then (1 : ℝ) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        by_cases hxs : s = a (x : ℕ) j <;> simp [hxs]
      rw [htoReal]
      simp
    change (↑t)⁻¹ *
        (∑ x : Fin t, (if s = a (x : ℕ) j then (1 : ENNReal) else 0).toReal) =
      ((Finset.univ.filter fun k : Fin t => a (k : ℕ) j = s).card : ℝ) / t
    rw [hsum]
    have hcard :
        ((Finset.univ.filter fun k : Fin t => s = a (k : ℕ) j).card : ℝ) =
          ((Finset.univ.filter fun k : Fin t => a (k : ℕ) j = s).card : ℝ) := by
      have hfilter :
          (Finset.univ.filter fun k : Fin t => s = a (k : ℕ) j) =
            (Finset.univ.filter fun k : Fin t => a (k : ℕ) j = s) := by
        ext k
        simp [eq_comm]
      rw [hfilter]
    rw [hcard, div_eq_inv_mul]
  · intro k hk
    by_cases hks : s = a (k : ℕ) j
    · simp [hks, NeZero.ne t]
    · simp [hks]

/-- The belief profile entering round `t`: each player's empirical marginal over the first `t`
    rounds, viewed as a mixed-strategy profile. -/
noncomputable def belief (a : ℕ → M.Profile) (t : ℕ) [NeZero t] : M.mixedExtension.Profile :=
  fun j => M.empiricalMarginal a j t

/-- A play sequence `a` is **fictitious play** if at every round the pure action played by each
    player is a best response, in the mixed extension, to the opponents' empirical marginals. The
    belief is indexed at `t + 1` (over rounds `0 … t`), so the averaging horizon is always positive;
    round `0` is the unconstrained initial play. -/
def IsFictitiousPlay (a : ℕ → M.Profile) : Prop :=
  ∀ (t : ℕ) (i : ι) (s' : M.Strategy i),
    M.mixedExtension.eu (Function.update (M.belief a (t + 1)) i (PMF.pure (a (t + 1) i))) i
      ≥ M.mixedExtension.eu (Function.update (M.belief a (t + 1)) i (PMF.pure s')) i

end KernelGame

end GameTheory
