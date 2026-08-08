/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Bellman.Finite.NashBellmanSpine
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Paths.OpponentClockDichotomy

/-!
# Nash--Bellman spine clock reduction

Compact one-stage Nash selection produces one bounded exact Bellman spine.
The opponent-clock dichotomy is then applied to that selected spine, without
assuming that the compact selection can favor either branch.  If every
opponent clock diverges, the qualitative dying-clock compiler makes the
initial Bellman value a uniform-equilibrium payoff.  Otherwise the same
spine has a player with a summable opponent clock and a positive-survival
suffix.

The useful theorem takes the spine as input.  Its unconditional existence
corollary is fenced by an explicit regression: the constant all-Continue
phantom spine is always exact and always has zero, hence summable, opponent
clocks.  Meaningful consumers must supply additional provenance, such as a
zero-boundary finite-chain construction.
-/

noncomputable section

namespace GameTheory

open Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The canonical bounded exact Nash--Bellman spine certificate. -/
def IsCanonicalExactQuittingNashBellmanSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool) : Prop :=
  (∀ time who, |value time who| ≤ quittingRewardBound reward) ∧
    (∀ time, value time = quittingRootSuccessorPayoff reward
      (value (time + 1)) (roots time)) ∧
    ∀ time, IsεQuittingRootNash reward
      (value (time + 1)) 0 (roots time)

/-- A supplied bounded exact spine obeys the exhaustive clock alternative.
This is the reusable reduction: provenance hypotheses on a graph-directed or
anchored spine can be established before invoking it. -/
theorem uniformEquilibriumPayoff_or_summableClock_of_exactNashBellmanSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool)
    (hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots) :
    (quittingGame reward).IsUniformEquilibriumPayoff none (value 0) ∨
      ∃ owner,
        Summable (quittingOpponentClockCharge roots owner) ∧
          ∃ start,
            0 < quittingLiveMassLimit reward
              (quittingOpponentOnlyProfile reward
                (quittingAllContinueProfileSpine reward
                  (quittingInfinitePathProfile reward roots) start)
                owner) := by
  rcases divergent_opponentClocks_or_positive_exceptionalSuffix reward roots with
    hdivergent | hexceptional
  · left
    exact infinitePath_isUniformEquilibriumPayoff_of_survival_tendsto_zero
      reward roots value
      (fun who start => (hdivergent who).2 start)
      (quittingRewardBound_nonneg reward)
      (abs_reward_le_quittingRewardBound reward)
      hspine.1 hspine.2.1 hspine.2.2
  · exact Or.inr hexceptional

/-- One compactly selected exact spine obeys the same exhaustive clock
alternative.  This unconditional corollary is structurally weak: arbitrary
compact selection need not avoid the phantom all-Continue spine fenced
below. -/
theorem exists_exactQuittingNashBellmanSpine_with_clockAlternative
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
      IsCanonicalExactQuittingNashBellmanSpine reward value roots ∧
        ((quittingGame reward).IsUniformEquilibriumPayoff none (value 0) ∨
          ∃ owner,
            Summable (quittingOpponentClockCharge roots owner) ∧
              ∃ start,
                0 < quittingLiveMassLimit reward
                  (quittingOpponentOnlyProfile reward
                    (quittingAllContinueProfileSpine reward
                      (quittingInfinitePathProfile reward roots) start)
                    owner)) := by
  obtain ⟨value, roots, hbound, hpolicy, hnash⟩ :=
    exists_exact_quittingNashBellmanSpine reward
  let hspine : IsCanonicalExactQuittingNashBellmanSpine reward value roots :=
    ⟨hbound, hpolicy, hnash⟩
  exact ⟨value, roots, hspine,
    uniformEquilibriumPayoff_or_summableClock_of_exactNashBellmanSpine
      reward value roots hspine⟩

/-- **Structurally weak existence corollary.**  Every finite quitting game
either already has a uniform-equilibrium payoff, or one exact bounded
Nash--Bellman spine selected by compactness has a summable playerwise
opponent clock together with the positive-survival exceptional suffix.

This is deliberately an alternative about the selected spine; it does not
assert that compact Nash selection can be steered toward the divergent-clock
branch. -/
theorem uniformEquilibriumPayoff_or_exists_exactNashBellmanSpine_summableClock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    (∃ payoff : Payoff ι,
        (quittingGame reward).IsUniformEquilibriumPayoff none payoff) ∨
      ∃ (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool) (owner : ι),
        IsCanonicalExactQuittingNashBellmanSpine reward value roots ∧
          Summable (quittingOpponentClockCharge roots owner) ∧
            ∃ start,
              0 < quittingLiveMassLimit reward
                (quittingOpponentOnlyProfile reward
                  (quittingAllContinueProfileSpine reward
                    (quittingInfinitePathProfile reward roots) start)
                  owner) := by
  obtain ⟨value, roots, hspine, huniform | hexceptional⟩ :=
    exists_exactQuittingNashBellmanSpine_with_clockAlternative reward
  · exact Or.inl ⟨value 0, huniform⟩
  · obtain ⟨owner, hsummable, hpositive⟩ := hexceptional
    exact Or.inr ⟨value, roots, owner, hspine, hsummable, hpositive⟩

/-! ## Phantom-spine regression -/

omit [DecidableEq ι] in
/- At the all-Continue root, the successor payoff is exactly the declared
continuation vector. -/
theorem quittingRootSuccessorPayoff_allContinueRoot_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) :
    quittingRootSuccessorPayoff reward continuation
      (quittingAllContinueRoot : ι → PMF Bool) = continuation := by
  classical
  funext who
  rw [quittingRootSuccessorPayoff_eq_endpointMix]
  simp [quittingAllContinueRoot]

/-- If the continuation coordinate dominates quitting alone, all-Continue is
an exact root Nash equilibrium. -/
theorem quittingAllContinueRoot_isZeroNash_of_singleton_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι)
    (hdominate : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ continuation who) :
    IsεQuittingRootNash reward continuation 0
      (quittingAllContinueRoot : ι → PMF Bool) := by
  apply (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
    reward continuation quittingAllContinueRoot).1
  intro who
  constructor
  · simpa [quittingAllContinueRoot] using
      (sub_nonpos.mpr (hdominate who))
  · simp [quittingAllContinueRoot]

/-- The canonical phantom spine carries the reward bound forever while every
player always continues. -/
def quittingCanonicalPhantomValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ℕ → Payoff ι :=
  fun _ _ => quittingRewardBound reward

/-- Root path of the canonical phantom spine. -/
def quittingCanonicalPhantomRoots : ℕ → ι → PMF Bool :=
  fun _ => quittingAllContinueRoot

/-- The phantom path is a genuine canonical bounded exact Nash--Bellman
spine for every payoff table.  Hence arbitrary-spine existence alone carries
no absorption or divergent-clock content. -/
theorem canonicalPhantom_isExactQuittingNashBellmanSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCanonicalExactQuittingNashBellmanSpine reward
      (quittingCanonicalPhantomValue reward)
      (quittingCanonicalPhantomRoots (ι := ι)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro time who
    simp only [quittingCanonicalPhantomValue]
    rw [abs_of_nonneg (quittingRewardBound_nonneg reward)]
  · intro time
    exact (quittingRootSuccessorPayoff_allContinueRoot_eq reward
      (quittingCanonicalPhantomValue reward (time + 1))).symm
  · intro time
    apply quittingAllContinueRoot_isZeroNash_of_singleton_le
    intro who
    exact (le_abs_self _).trans
      (abs_reward_le_quittingRewardBound reward
        (quittingSingletonTerminal who) who)

/-- Every playerwise opponent clock of the phantom spine is identically
zero. -/
theorem quittingOpponentClockCharge_canonicalPhantom_eq_zero
    (owner : ι) (time : ℕ) :
    quittingOpponentClockCharge
      (quittingCanonicalPhantomRoots (ι := ι)) owner time = 0 := by
  rw [quittingOpponentClockCharge_eq_one_sub]
  unfold quittingFixedOpponentsContinueMass
  have hupdate : Function.update
      (quittingAllContinueRoot : ι → PMF Bool) owner (PMF.pure false) =
      quittingAllContinueRoot := by
    funext player
    by_cases hplayer : player = owner
    · subst player
      simp [quittingAllContinueRoot]
    · simp [Function.update_of_ne hplayer]
  simp only [quittingCanonicalPhantomRoots]
  rw [hupdate]
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [quittingAllContinueRoot]

/-- In particular every phantom opponent clock is summable. -/
theorem summable_quittingOpponentClockCharge_canonicalPhantom
    (owner : ι) :
    Summable (quittingOpponentClockCharge
      (quittingCanonicalPhantomRoots (ι := ι)) owner) := by
  have hzero : quittingOpponentClockCharge
      (quittingCanonicalPhantomRoots (ι := ι)) owner =
      fun _ : ℕ => 0 := by
    funext time
    exact quittingOpponentClockCharge_canonicalPhantom_eq_zero owner time
  rw [hzero]
  exact summable_zero

/-- For a nonempty player set, the phantom spine always realizes the
summable/positive-survival branch of the unconditional clock fork. -/
theorem canonicalPhantom_realizes_summableClockBranch
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsCanonicalExactQuittingNashBellmanSpine reward
        (quittingCanonicalPhantomValue reward)
        (quittingCanonicalPhantomRoots (ι := ι)) ∧
      ∃ owner,
        Summable (quittingOpponentClockCharge
          (quittingCanonicalPhantomRoots (ι := ι)) owner) ∧
          ∃ start,
            0 < quittingLiveMassLimit reward
              (quittingOpponentOnlyProfile reward
                (quittingAllContinueProfileSpine reward
                  (quittingInfinitePathProfile reward
                    (quittingCanonicalPhantomRoots (ι := ι))) start)
                owner) := by
  refine ⟨canonicalPhantom_isExactQuittingNashBellmanSpine reward, ?_⟩
  let owner : ι := Classical.choice (inferInstance : Nonempty ι)
  have hsummable :=
    summable_quittingOpponentClockCharge_canonicalPhantom owner
  exact ⟨owner, hsummable,
    exists_suffix_positive_opponentLiveMassLimit_of_summable reward
      (quittingCanonicalPhantomRoots (ι := ι)) owner hsummable⟩

end GameTheory
