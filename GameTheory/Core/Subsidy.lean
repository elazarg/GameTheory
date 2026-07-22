/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Core.KernelGame
import Math.Probability

/-!
# Profile-observed subsidies

A transfer scheme observes the realized pure strategy profile and adds a
profile-dependent transfer to each player's payoff. Transfers may have either
sign. The transformed game records the
original outcome together with the profile whose transfers are being paid.
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type}

/-- Add profile-observed transfers to a kernel game. The strategic choices are
unchanged; outcomes are tagged with the profile so the utility field can add the
appropriate transfer. -/
noncomputable def subsidize (G : KernelGame ι) (V : Profile G → Payoff ι) :
    KernelGame ι where
  Strategy := G.Strategy
  Outcome := Profile G × G.Outcome
  utility := fun p i => G.utility p.2 i + V p.1 i
  outcomeKernel := fun σ => PMF.map (fun ω => (σ, ω)) (G.outcomeKernel σ)

@[simp] theorem subsidize_Strategy (G : KernelGame ι) (V : Profile G → Payoff ι) :
    (G.subsidize V).Strategy = G.Strategy := rfl

@[simp] theorem subsidize_utility (G : KernelGame ι) (V : Profile G → Payoff ι)
    (p : Profile G × G.Outcome) (i : ι) :
    (G.subsidize V).utility p i = G.utility p.2 i + V p.1 i := rfl

@[simp] theorem subsidize_outcomeKernel (G : KernelGame ι) (V : Profile G → Payoff ι)
    (σ : Profile G) :
    (G.subsidize V).outcomeKernel σ =
      PMF.map (fun ω => (σ, ω)) (G.outcomeKernel σ) := rfl

/-- Expected utility in a subsidized finite-outcome game is original expected
utility plus the transfer at the played profile. -/
@[simp] theorem subsidize_eu (G : KernelGame ι) [Finite G.Outcome]
    (V : Profile G → Payoff ι) (σ : Profile G) (i : ι) :
    (G.subsidize V).eu σ i = G.eu σ i + V σ i := by
  classical
  letI : Fintype G.Outcome := Fintype.ofFinite G.Outcome
  unfold KernelGame.eu subsidize
  rw [expect_map_fintype_source]
  rw [expect_eq_sum]
  calc
    (∑ ω : G.Outcome,
        (G.outcomeKernel σ ω).toReal * (G.utility ω i + V σ i))
        =
        (∑ ω : G.Outcome, (G.outcomeKernel σ ω).toReal * G.utility ω i) +
          (∑ ω : G.Outcome, (G.outcomeKernel σ ω).toReal * V σ i) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun ω _ => by ring
    _ =
        (∑ ω : G.Outcome, (G.outcomeKernel σ ω).toReal * G.utility ω i) +
          V σ i * (∑ ω : G.Outcome, (G.outcomeKernel σ ω).toReal) := by
          congr 1
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun ω _ => by ring
    _ = (∑ ω : G.Outcome, (G.outcomeKernel σ ω).toReal * G.utility ω i) + V σ i := by
          rw [pmf_toReal_sum_one]
          ring

/-- Zero subsidies leave finite-outcome expected utilities unchanged. -/
@[simp] theorem subsidize_zero_eu (G : KernelGame ι) [Finite G.Outcome]
    (σ : Profile G) (i : ι) :
    (G.subsidize (fun _ _ => 0)).eu σ i = G.eu σ i := by
  simp

end KernelGame

end GameTheory
