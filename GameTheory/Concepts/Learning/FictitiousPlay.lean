/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.Foundations.Convergence

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

namespace KernelGame

variable {ι : Type} [DecidableEq ι] [Fintype ι] (M : KernelGame ι)

/-- The empirical distribution of player `j`'s pure actions over the first `t` rounds: the uniform
    average of the point masses at `a 0 j, …, a (t-1) j`. -/
noncomputable def empiricalMarginal (a : ℕ → M.Profile) (j : ι) (t : ℕ) [NeZero t] :
    PMF (M.Strategy j) :=
  (PMF.uniformOfFintype (Fin t)).bind (fun s => PMF.pure (a (s : ℕ) j))

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
