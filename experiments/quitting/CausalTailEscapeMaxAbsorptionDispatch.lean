/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticStrictTailEscapeReturn
import UniformEquilibrium.Quitting.Boundary.Repair.ComplementarityClosed
import UniformEquilibrium.Quitting.Boundary.Repair.FixedTailUniformAbsorption
import UniformEquilibrium.Quitting.Circulation.MultiOwnerFaceCirculationCompactPath
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticLawCarrierCausalization
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticPureTimeRectangleDisintegration
import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticAtomicSupportBoundary
import UniformEquilibrium.Quitting.Bellman.Finite.PunishmentFloorFinitePrefix

/-!
# Maximal-absorption dispatch for a causal tail escape

Proof-frontier passport:

* seam attacked: strict Q183 tail escape below a literal causal suffix atom;
* input consumed: compact exact cap--Nash correspondence, exact prefix debt
  scaling, and `CausalTailEscapeReturnGate`'s return-selection interface;
* output delivered: a same-tail return, or universal quantitative
  undercharge even at the maximal-absorption exact root;
* downstream consumer: the return branch feeds
  `capNashTailEscapeReturnSelection_retains_causalSuffixAtom`; the obstruction
  rules out further selection-only work at the unchanged tail.

The exact cap--Nash correspondence at a fixed tail is compact.  Hence its
one-stage absorption mass has a maximizer.  This removes an artificial
root-selection ambiguity from the causal tail-escape gate:

* if the maximizer spends enough of the tail excess, the existing return gate
  retains the literal suffix atom near the minimum fiber;
* otherwise no exact cap--Nash root at that same tail can spend enough.

The second branch is the precise same-tail obstruction.  It splits further:
the all-Continue root is exact Nash, or the maximal root has positive
absorption forced by a concrete singleton-cap gap but is still quantitatively
undercharged.  Thus finite Nash existence, extremal root selection, and local
singleton-gap forcing are all exhausted.  Any further argument must change
the cap/state or use additional chronology.

Q184 state-change passport:

* seam attacked: universal same-tail undercharge after selection has been
  exhausted, now allowing the literal state and its cap to change;
* input consumed: maximal exact cap roots, exact semantic prefix scaling,
  fixed-tail absorption bounds, closed endpoint Nash graphs, and compactness
  of the joint terminal semantic/law carrier;
* output delivered: a nested maximal-root chronology with summable charge,
  retained suffix atoms, and finite charged cap rise; its envelope states are
  now proved to be a literal exact punishment-floor prefix with the identical
  absorption charge;
* frontier delta: every positive-absorption/support-entry branch is therefore
  accepted by the existing prefix-capacity interface.  The only surviving
  local obstruction is a cap whose exact Nash correspondence is the singleton
  all-Continue root.  No owner decoder is needed merely to consume the charge.
-/

noncomputable section

namespace GameTheory

open Set Math.Probability Math.PMFProduct Math.ProbabilityMassFunction

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- Absorption attains a maximum on the exact cap--Nash correspondence at a
fixed continuation vector. -/
theorem exists_maximalAbsorption_isZeroQuittingRootNash
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (tail : Payoff iota) :
    ∃ root : iota → PMF Bool,
      IsεQuittingRootNash reward tail 0 root ∧
      ∀ other : iota → PMF Bool,
        IsεQuittingRootNash reward tail 0 other →
          quittingRootAbsorptionMass other ≤
            quittingRootAbsorptionMass root := by
  let roots : Set (QuittingRootSimplex iota) :=
    {root | IsεQuittingRootEndpointNash reward tail 0
      (quittingRootOfSimplex root)}
  have hcompact : IsCompact roots := by
    simpa only [roots] using
      isCompact_setOf_isZeroQuittingRootEndpointNash_root reward tail
  have hnonempty : roots.Nonempty := by
    obtain ⟨root, hroot⟩ :=
      exists_isZeroQuittingRootEndpointNash_simplex reward tail
    exact ⟨root, hroot⟩
  obtain ⟨chosen, hchosen, hmax⟩ := hcompact.exists_isMaxOn hnonempty
    continuous_quittingSimplexAbsorptionMass.continuousOn
  let root := quittingRootOfSimplex chosen
  have hnash : IsεQuittingRootNash reward tail 0 root :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward tail 0 root).1 hchosen
  refine ⟨root, hnash, ?_⟩
  intro other hother
  let otherSimplex : QuittingRootSimplex iota :=
    fun who ↦ stdSimplexEquiv (other who)
  have hotherRoot : quittingRootOfSimplex otherSimplex = other := by
    funext who
    exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (other who)
  have hotherEndpoint : IsεQuittingRootEndpointNash reward tail 0
      (quittingRootOfSimplex otherSimplex) := by
    rw [hotherRoot]
    exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward tail 0 other).2 hother
  rw [isMaxOn_iff] at hmax
  have hmaximal := hmax otherSimplex hotherEndpoint
  rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass,
    quittingSimplexAbsorptionMass_eq_rootAbsorptionMass] at hmaximal
  simpa only [root, hotherRoot] using hmaximal

/-- **Maximal-absorption causal tail dispatch.**

At a strict escaped tail carrying a literal suffix atom, choose an exact
cap--Nash root with maximal absorption.  Positive minimum debt forces this
root to retain positive survival.  Either it returns to the requested
minimum neighborhood and the atom survives literally, or every exact root at
this same tail fails the return selection.

In the universal-failure branch, either all-Continue is already exact Nash,
or a concrete singleton-cap gap forces the maximal root to absorb with the
standard positive modulus.  In the latter case even that forced, maximal
charge is insufficient: this is the sharp local obstruction left after
extremal root selection. -/
theorem exists_maximalCapNash_returnSelection_or_sameTailUndercharge
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum tail : QuittingTerminalSemanticPair iota)
    (tolerance : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ outcome player, |reward outcome player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hescape : quittingTerminalSemanticDebtSum minimum <
      quittingTerminalSemanticDebtSum tail)
    (htailCarrier : tail ∈ quittingTerminalSemanticCarrier reward) :
    ∃ root : iota → PMF Bool,
      IsεQuittingRootNash reward tail.2 0 root ∧
      0 < quittingStationaryContinueMass root ∧
      (∀ other : iota → PMF Bool,
        IsεQuittingRootNash reward tail.2 0 other →
          quittingRootAbsorptionMass other ≤
            quittingRootAbsorptionMass root) ∧
      (IsQuittingCapNashResetReturnSelection
          (reward := reward) minimum tail root tolerance ∨
        ((∀ other : iota → PMF Bool,
            IsεQuittingRootNash reward tail.2 0 other →
              ¬ IsQuittingCapNashResetReturnSelection
                (reward := reward) minimum tail other tolerance) ∧
          quittingTerminalSemanticDebtSum tail *
                quittingRootAbsorptionMass root <
            (quittingTerminalSemanticDebtSum tail -
                quittingTerminalSemanticDebtSum minimum) - tolerance ∧
          (IsεQuittingRootNash reward
              tail.2 0
                (quittingAllContinueRoot : iota → PMF Bool) ∨
            ∃ blocker : iota,
              let eta := reward (quittingSingletonTerminal blocker) blocker -
                tail.2 blocker
              0 < eta ∧
                eta / (eta + 2 * M) ≤
                  quittingRootAbsorptionMass root ∧
                ¬ IsQuittingCapNashResetReturnSelection
                  (reward := reward) minimum tail root tolerance))) := by
  obtain ⟨root, hnash, hmax⟩ :=
    exists_maximalAbsorption_isZeroQuittingRootNash reward tail.2
  have htailDebtNonneg : 0 ≤ quittingTerminalSemanticDebtSum tail :=
    hminimumPositive.le.trans hescape.le
  have hcontinue : 0 < quittingStationaryContinueMass root := by
    have hcontinueNonneg : 0 ≤ quittingStationaryContinueMass root :=
      quittingStationaryContinueMass_nonneg root
    by_contra hnot
    have hcontinueZero : quittingStationaryContinueMass root = 0 :=
      le_antisymm (le_of_not_gt hnot) hcontinueNonneg
    let returned := quittingTerminalSemanticPrefix reward root tail
    have hreturnedCarrier : returned ∈
        quittingTerminalSemanticCarrier reward :=
      quittingTerminalSemanticPrefix_mem_carrier
        reward root tail hM hreward htailCarrier
    have hreturnedLower := hminimum returned hreturnedCarrier
    have hscale : quittingTerminalSemanticDebtSum returned =
        quittingStationaryContinueMass root *
          quittingTerminalSemanticDebtSum tail :=
      quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
        (reward := reward) tail root hnash
    rw [hscale, hcontinueZero, zero_mul] at hreturnedLower
    linarith
  refine ⟨root, hnash, hcontinue, hmax, ?_⟩
  by_cases hselection : IsQuittingCapNashResetReturnSelection
      (reward := reward) minimum tail root tolerance
  · left
    exact hselection
  · right
    have huniversal : ∀ other : iota → PMF Bool,
        IsεQuittingRootNash reward tail.2 0 other →
          ¬ IsQuittingCapNashResetReturnSelection
            (reward := reward) minimum tail other tolerance := by
      intro other hother hotherSelection
      apply hselection
      refine ⟨hnash, ?_⟩
      have habsorption := hmax other hother
      have hscaled :
          quittingTerminalSemanticDebtSum tail *
              quittingRootAbsorptionMass other ≤
            quittingTerminalSemanticDebtSum tail *
              quittingRootAbsorptionMass root :=
        mul_le_mul_of_nonneg_left habsorption htailDebtNonneg
      exact hotherSelection.2.trans hscaled
    have hundercharge :
        quittingTerminalSemanticDebtSum tail *
              quittingRootAbsorptionMass root <
          (quittingTerminalSemanticDebtSum tail -
              quittingTerminalSemanticDebtSum minimum) - tolerance := by
      apply lt_of_not_ge
      intro hcharge
      exact hselection ⟨hnash, hcharge⟩
    refine ⟨huniversal, hundercharge, ?_⟩
    by_cases hallContinue : IsεQuittingRootNash reward tail.2 0
        (quittingAllContinueRoot : iota → PMF Bool)
    · exact Or.inl hallContinue
    · right
      have hnotCap : ¬ ∀ player,
          reward (quittingSingletonTerminal player) player ≤ tail.2 player :=
        fun hcap ↦ hallContinue
          ((isZeroQuittingRootNash_allContinue_iff_singleton_le
            reward tail.2).2 hcap)
      push Not at hnotCap
      obtain ⟨blocker, hgap⟩ := hnotCap
      let eta := reward (quittingSingletonTerminal blocker) blocker -
        tail.2 blocker
      have heta : 0 < eta := by dsimp [eta]; linarith
      have hendpoint : IsεQuittingRootEndpointNash reward tail.2 0 root :=
        (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
          reward tail.2 0 root).2 hnash
      have hgapForm : tail.2 blocker ≤
          reward (quittingSingletonTerminal blocker) blocker - eta := by
        dsimp [eta]
        linarith
      have habsorption :=
        gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
          reward tail.2 root blocker hM heta hreward hgapForm hendpoint
      exact ⟨blocker, heta, habsorption, hselection⟩

end GameTheory

/-! ## Recursive state-changing maximal prefixes -/

namespace GameTheory

open Filter Set Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology
open scoped Topology

variable {iota : Type} [Fintype iota] [DecidableEq iota]

/-- A canonical maximal-absorption exact cap root at one literal profile. -/
noncomputable def quittingMaximalCapPrefixRoot
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) : iota → PMF Bool :=
  Classical.choose (exists_maximalAbsorption_isZeroQuittingRootNash reward
    (quittingTerminalSemanticPair reward profile).2)

theorem quittingMaximalCapPrefixRoot_exactNash
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile) :
    IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward profile).2 0
        (quittingMaximalCapPrefixRoot reward profile) :=
  (Classical.choose_spec
    (exists_maximalAbsorption_isZeroQuittingRootNash reward
      (quittingTerminalSemanticPair reward profile).2)).1

theorem quittingMaximalCapPrefixRoot_maximal
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (profile : (quittingGame reward).BehaviorProfile)
    (other : iota → PMF Bool)
    (hother : IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward profile).2 0 other) :
    quittingRootAbsorptionMass other ≤
      quittingRootAbsorptionMass
        (quittingMaximalCapPrefixRoot reward profile) :=
  (Classical.choose_spec
    (exists_maximalAbsorption_isZeroQuittingRootNash reward
      (quittingTerminalSemanticPair reward profile).2)).2 other hother

/-- Prefix outward recursively, recomputing a maximal-absorption exact root
against the cap of the newly reached literal state at every step. -/
noncomputable def quittingMaximalCapPrefixProfile
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) :
    ℕ → (quittingGame reward).BehaviorProfile
  | 0 => terminal
  | n + 1 => quittingRootThenContinuationProfile reward
      (quittingMaximalCapPrefixRoot reward
        (quittingMaximalCapPrefixProfile reward terminal n))
      (quittingMaximalCapPrefixProfile reward terminal n)

@[simp] theorem quittingMaximalCapPrefixProfile_zero
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) :
    quittingMaximalCapPrefixProfile reward terminal 0 = terminal := rfl

@[simp] theorem quittingMaximalCapPrefixProfile_succ
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile) (n : ℕ) :
    quittingMaximalCapPrefixProfile reward terminal (n + 1) =
      quittingRootThenContinuationProfile reward
        (quittingMaximalCapPrefixRoot reward
          (quittingMaximalCapPrefixProfile reward terminal n))
        (quittingMaximalCapPrefixProfile reward terminal n) := rfl

/-- Exact total-debt recursion along the state-changing maximal-prefix
sequence. -/
theorem quittingMaximalCapPrefixProfile_debt_succ
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) (n : ℕ) :
    quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal (n + 1))) =
      quittingStationaryContinueMass
          (quittingMaximalCapPrefixRoot reward
            (quittingMaximalCapPrefixProfile reward terminal n)) *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal n)) := by
  rw [quittingMaximalCapPrefixProfile_succ,
    quittingTerminalSemanticPair_rootThenContinuation reward
      (quittingMaximalCapPrefixRoot reward
        (quittingMaximalCapPrefixProfile reward terminal n))
      (quittingMaximalCapPrefixProfile reward terminal n) hM hreward]
  exact quittingTerminalSemanticDebtSum_prefix_eq_continueMass_mul_of_capNash
    (reward := reward)
    (quittingTerminalSemanticPair reward
      (quittingMaximalCapPrefixProfile reward terminal n))
    (quittingMaximalCapPrefixRoot reward
      (quittingMaximalCapPrefixProfile reward terminal n))
    (quittingMaximalCapPrefixRoot_exactNash reward
      (quittingMaximalCapPrefixProfile reward terminal n))

/-- A suffix stage atom is shifted one date and scaled by the exact joint
Continue mass at every recursive prefix. -/
theorem quittingMaximalCapPrefixProfile_stage_succ
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (stage n : ℕ) (coalition : {S : Finset iota // S.Nonempty}) :
    quittingStageCoalitionMass reward
        (quittingMaximalCapPrefixProfile reward terminal (n + 1))
        (n + 1 + stage) coalition =
      quittingStationaryContinueMass
          (quittingMaximalCapPrefixRoot reward
            (quittingMaximalCapPrefixProfile reward terminal n)) *
        quittingStageCoalitionMass reward
          (quittingMaximalCapPrefixProfile reward terminal n)
          (n + stage) coalition := by
  rw [quittingMaximalCapPrefixProfile_succ]
  rw [show n + 1 + stage = (n + stage) + 1 by omega,
    quittingStageCoalitionMass_rootThenContinuation_succ]

/-- Debt and one fixed suffix atom are multiplied by the same recursive
survival factor.  This cross-multiplied form avoids introducing a separate
infinite-product object. -/
theorem quittingMaximalCapPrefixProfile_debt_mul_stage_eq
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (stage n : ℕ) (coalition : {S : Finset iota // S.Nonempty})
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward terminal) *
        quittingStageCoalitionMass reward
          (quittingMaximalCapPrefixProfile reward terminal n)
          (n + stage) coalition =
      quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal n)) *
        quittingStageCoalitionMass reward terminal stage coalition := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [quittingMaximalCapPrefixProfile_stage_succ,
        quittingMaximalCapPrefixProfile_debt_succ
          reward terminal hM hreward]
      calc
        _ = quittingStationaryContinueMass
              (quittingMaximalCapPrefixRoot reward
                (quittingMaximalCapPrefixProfile reward terminal n)) *
            (quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward terminal) *
              quittingStageCoalitionMass reward
                (quittingMaximalCapPrefixProfile reward terminal n)
                (n + stage) coalition) := by ring
        _ = quittingStationaryContinueMass
              (quittingMaximalCapPrefixRoot reward
                (quittingMaximalCapPrefixProfile reward terminal n)) *
            (quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward
                  (quittingMaximalCapPrefixProfile reward terminal n)) *
              quittingStageCoalitionMass reward terminal stage coalition) := by
                rw [ih]
        _ = _ := by ring

/-- The global positive semantic minimum charges the whole finite prefix of
the recursively changed-state chronology. -/
theorem minimum_mul_sum_maximalCapPrefix_absorption_le_debtDrop
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∀ horizon : ℕ,
      quittingTerminalSemanticDebtSum minimum *
          ∑ n ∈ Finset.range horizon,
            quittingRootAbsorptionMass
              (quittingMaximalCapPrefixRoot reward
                (quittingMaximalCapPrefixProfile reward terminal n)) ≤
        quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward terminal) -
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingMaximalCapPrefixProfile reward terminal horizon)) := by
  intro horizon
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      let profile := quittingMaximalCapPrefixProfile reward terminal horizon
      let root := quittingMaximalCapPrefixRoot reward profile
      let debt := quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward profile)
      have hcarrier : quittingTerminalSemanticPair reward profile ∈
          quittingTerminalSemanticCarrier reward :=
        quittingTerminalSemanticPair_mem_carrier reward profile
      have hminimumDebt : quittingTerminalSemanticDebtSum minimum ≤ debt :=
        hminimum _ hcarrier
      have habsorption : 0 ≤ quittingRootAbsorptionMass root :=
        quittingRootAbsorptionMass_nonneg root
      have hlocal : quittingTerminalSemanticDebtSum minimum *
            quittingRootAbsorptionMass root ≤
          debt * quittingRootAbsorptionMass root :=
        mul_le_mul_of_nonneg_right hminimumDebt habsorption
      have hstep := quittingMaximalCapPrefixProfile_debt_succ
        reward terminal hM hreward horizon
      have hlocalDrop : quittingTerminalSemanticDebtSum minimum *
            quittingRootAbsorptionMass root ≤
          debt - quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward
              (quittingMaximalCapPrefixProfile reward terminal (horizon + 1))) := by
        dsimp only [profile, root, debt] at hstep ⊢
        unfold quittingRootAbsorptionMass at hlocal ⊢
        nlinarith
      rw [Finset.sum_range_succ]
      dsimp only [profile, root, debt] at hlocalDrop
      nlinarith [hlocalDrop]

/-- The changed-state maximal-prefix hazards are summable under a positive
global semantic debt floor. -/
theorem summable_maximalCapPrefix_absorption
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum) :
    Summable (fun n ↦ quittingRootAbsorptionMass
      (quittingMaximalCapPrefixRoot reward
        (quittingMaximalCapPrefixProfile reward terminal n))) := by
  refine summable_of_sum_range_le
    (c := quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward terminal) /
      quittingTerminalSemanticDebtSum minimum)
    (fun n ↦ quittingRootAbsorptionMass_nonneg _) ?_
  intro horizon
  have hcharge :=
    minimum_mul_sum_maximalCapPrefix_absorption_le_debtDrop
      reward minimum terminal hM hreward hminimum horizon
  have hprofileLower := hminimum
    (quittingTerminalSemanticPair reward
      (quittingMaximalCapPrefixProfile reward terminal horizon))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  apply (le_div_iff₀ hminimumPositive).2
  nlinarith

/-- A fixed positive singleton-cap gap cannot persist along the recursively
state-changing chronology.  Otherwise every maximal root would have the
same positive absorption lower bound, contradicting summability. -/
theorem exists_maximalCapPrefix_singletonGapCollapse
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (blocker : iota) (eta : ℝ)
    {M : ℝ} (hM : 0 ≤ M) (heta : 0 < eta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum) :
    ∃ n,
      reward (quittingSingletonTerminal blocker) blocker - eta <
        (quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal n)).2 blocker := by
  by_contra hnot
  push Not at hnot
  let absorption : ℕ → ℝ := fun n ↦ quittingRootAbsorptionMass
    (quittingMaximalCapPrefixRoot reward
      (quittingMaximalCapPrefixProfile reward terminal n))
  have habsorption : Tendsto absorption atTop (nhds 0) := by
    exact (summable_maximalCapPrefix_absorption reward minimum terminal
      hM hreward hminimum hminimumPositive).tendsto_atTop_zero
  have hratio : 0 < eta / (eta + 2 * M) := by positivity
  have hsmall : ∀ᶠ n in atTop, absorption n < eta / (eta + 2 * M) :=
    habsorption.eventually (Iio_mem_nhds hratio)
  rw [eventually_atTop] at hsmall
  obtain ⟨n, hn⟩ := hsmall
  have hnSmall := hn n le_rfl
  have hnash := quittingMaximalCapPrefixRoot_exactNash reward
    (quittingMaximalCapPrefixProfile reward terminal n)
  have hendpoint :=
    (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward
        (quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal n)).2 0 _).2 hnash
  have hlower := gap_div_le_quittingRootAbsorptionMass_of_isZeroEndpointNash
    reward
      (quittingTerminalSemanticPair reward
        (quittingMaximalCapPrefixProfile reward terminal n)).2
      (quittingMaximalCapPrefixRoot reward
        (quittingMaximalCapPrefixProfile reward terminal n))
      blocker hM heta hreward (hnot n) hendpoint
  exact (not_lt_of_ge hlower) hnSmall

/-- If the original tail has a singleton-cap gap `eta`, some finite changed
state raises that same cap coordinate by more than `eta / 2`.  This is a
cumulative envelope-drift certificate; it is not yet a same-row unilateral
gain or a marked-atom charge. -/
theorem exists_maximalCapPrefix_capRise_halfGap
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (blocker : iota) (eta : ℝ)
    {M : ℝ} (hM : 0 ≤ M) (heta : 0 < eta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hinitialGap :
      (quittingTerminalSemanticPair reward terminal).2 blocker ≤
        reward (quittingSingletonTerminal blocker) blocker - eta) :
    ∃ n, eta / 2 <
      (quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal n)).2 blocker -
        (quittingTerminalSemanticPair reward terminal).2 blocker := by
  obtain ⟨n, hcollapse⟩ := exists_maximalCapPrefix_singletonGapCollapse
    reward minimum terminal blocker (eta / 2) hM (by positivity) hreward
      hminimum hminimumPositive
  exact ⟨n, by linarith⟩

/-- Cumulative cap drift along the recursive chronology is paid by the
literal absorption charge of the same finite prefix. -/
theorem abs_maximalCapPrefix_cap_sub_initial_le_charge
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (who : iota) {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    ∀ horizon : ℕ,
      |(quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal horizon)).2 who -
          (quittingTerminalSemanticPair reward terminal).2 who| ≤
        4 * M * ∑ n ∈ Finset.range horizon,
          quittingRootAbsorptionMass
            (quittingMaximalCapPrefixRoot reward
              (quittingMaximalCapPrefixProfile reward terminal n)) := by
  intro horizon
  induction horizon with
  | zero => simp
  | succ horizon ih =>
      let profile := quittingMaximalCapPrefixProfile reward terminal horizon
      let root := quittingMaximalCapPrefixRoot reward profile
      have hstack : IsQuittingCapNashRootStack reward [root] profile := by
        exact ⟨quittingMaximalCapPrefixRoot_exactNash reward profile, trivial⟩
      have hstepRaw :=
        abs_quittingContinuationBestResponseValue_capNashRootStack_sub_terminal_le
          (reward := reward) [root] profile who hM hreward hstack
      have hstep :
          |(quittingTerminalSemanticPair reward
                (quittingMaximalCapPrefixProfile reward terminal (horizon + 1))).2
                who -
              (quittingTerminalSemanticPair reward profile).2 who| ≤
            4 * M * quittingRootAbsorptionMass root := by
        simpa [quittingMaximalCapPrefixProfile_succ,
          quittingLiteralRootStackProfile, quittingTerminalSemanticPair,
          quittingCapNashStackAbsorptionSum] using hstepRaw
      have htriangle := abs_sub_le
        ((quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal (horizon + 1))).2 who)
        ((quittingTerminalSemanticPair reward profile).2 who)
        ((quittingTerminalSemanticPair reward terminal).2 who)
      rw [Finset.sum_range_succ]
      dsimp only [profile, root] at hstep ⊢
      calc
        _ ≤ |(quittingTerminalSemanticPair reward
                  (quittingMaximalCapPrefixProfile reward terminal (horizon + 1))).2
                  who -
                (quittingTerminalSemanticPair reward
                  (quittingMaximalCapPrefixProfile reward terminal horizon)).2 who| +
              |(quittingTerminalSemanticPair reward
                  (quittingMaximalCapPrefixProfile reward terminal horizon)).2 who -
                (quittingTerminalSemanticPair reward terminal).2 who| :=
            htriangle
        _ ≤ 4 * M * quittingRootAbsorptionMass
                (quittingMaximalCapPrefixRoot reward
                  (quittingMaximalCapPrefixProfile reward terminal horizon)) +
              4 * M * ∑ n ∈ Finset.range horizon,
                quittingRootAbsorptionMass
                  (quittingMaximalCapPrefixRoot reward
                    (quittingMaximalCapPrefixProfile reward terminal n)) :=
            add_le_add hstep ih
        _ = _ := by ring

/-- Every fixed suffix atom retains the debt-ratio fraction of its original
mass throughout the changed-state maximal-prefix chronology. -/
theorem maximalCapPrefix_atomMass_lowerBound
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (stage n : ℕ) (coalition : {S : Finset iota // S.Nonempty})
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum) :
    quittingTerminalSemanticDebtSum minimum /
          quittingTerminalSemanticDebtSum
            (quittingTerminalSemanticPair reward terminal) *
        quittingStageCoalitionMass reward terminal stage coalition ≤
      quittingStageCoalitionMass reward
        (quittingMaximalCapPrefixProfile reward terminal n)
        (n + stage) coalition := by
  let initialDebt := quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward terminal)
  let currentDebt := quittingTerminalSemanticDebtSum
    (quittingTerminalSemanticPair reward
      (quittingMaximalCapPrefixProfile reward terminal n))
  let initialMass := quittingStageCoalitionMass reward terminal stage coalition
  let currentMass := quittingStageCoalitionMass reward
    (quittingMaximalCapPrefixProfile reward terminal n) (n + stage) coalition
  have hinitialPositive : 0 < initialDebt :=
    hminimumPositive.trans_le (hminimum _
      (quittingTerminalSemanticPair_mem_carrier reward terminal))
  have hcurrentLower : quittingTerminalSemanticDebtSum minimum ≤ currentDebt :=
    hminimum _ (quittingTerminalSemanticPair_mem_carrier reward _)
  have hinitialMassNonneg : 0 ≤ initialMass :=
    quittingStageCoalitionMass_nonneg reward terminal stage coalition
  have hscaled : quittingTerminalSemanticDebtSum minimum * initialMass ≤
      currentDebt * initialMass :=
    mul_le_mul_of_nonneg_right hcurrentLower hinitialMassNonneg
  have hinvariant := quittingMaximalCapPrefixProfile_debt_mul_stage_eq
    reward terminal stage n coalition hM hreward
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hinitialPositive).2
  rw [mul_comm _
    (quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward terminal)), hinvariant]
  exact hscaled

/-- **Smallest state-changing transport interface.**

An initial singleton-cap gap forces one finite nested exact chronology whose
same cap coordinate rises, whose actual absorption charge pays that rise,
and whose shifted causal suffix atom retains the uniform debt-ratio mass.
All three facts concern the same changed-state profile.  What remains absent
is an owner decoder turning the jointly generated cap rise or charge into one
legal unilateral gain. -/
theorem exists_maximalCapPrefix_chargedCapRise_retainingAtom
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (blocker : iota) (eta : ℝ)
    (stage : ℕ) (coalition : {S : Finset iota // S.Nonempty})
    {M : ℝ} (hM : 0 ≤ M) (heta : 0 < eta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hinitialGap :
      (quittingTerminalSemanticPair reward terminal).2 blocker ≤
        reward (quittingSingletonTerminal blocker) blocker - eta) :
    ∃ horizon,
      eta / 2 <
        (quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal horizon)).2 blocker -
          (quittingTerminalSemanticPair reward terminal).2 blocker ∧
      eta / 2 < 4 * M * ∑ n ∈ Finset.range horizon,
        quittingRootAbsorptionMass
          (quittingMaximalCapPrefixRoot reward
            (quittingMaximalCapPrefixProfile reward terminal n)) ∧
      quittingTerminalSemanticDebtSum minimum /
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward terminal) *
          quittingStageCoalitionMass reward terminal stage coalition ≤
        quittingStageCoalitionMass reward
          (quittingMaximalCapPrefixProfile reward terminal horizon)
          (horizon + stage) coalition := by
  obtain ⟨horizon, hrise⟩ := exists_maximalCapPrefix_capRise_halfGap
    reward minimum terminal blocker eta hM heta hreward hminimum
      hminimumPositive hinitialGap
  have hcapBound := abs_maximalCapPrefix_cap_sub_initial_le_charge
    reward terminal blocker hM hreward horizon
  have hrisePositive : 0 <
      (quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal horizon)).2 blocker -
        (quittingTerminalSemanticPair reward terminal).2 blocker := by
    linarith
  have hriseAbs : eta / 2 <
      |(quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal horizon)).2 blocker -
        (quittingTerminalSemanticPair reward terminal).2 blocker| := by
    rw [abs_of_pos hrisePositive]
    exact hrise
  refine ⟨horizon, hrise, hriseAbs.trans_le hcapBound, ?_⟩
  exact maximalCapPrefix_atomMass_lowerBound reward minimum terminal stage
    horizon coalition hM hreward hminimum hminimumPositive

/-- **State-changing limit of universal same-tail undercharge.**

Recursively recomputing a maximal exact cap root produces a genuinely nested
literal chronology.  If none of its states enters the requested minimum
neighborhood, a joint semantic/law subsequence converges to an off-minimum
point which retains a uniform fraction of the original causal suffix atom.
The roots converge to all-Continue, so closed endpoint complementarity makes
all-Continue exact Nash at the limiting cap.

Maximality is deliberately not passed to the limit.  The conclusion instead
exposes the exhaustive residual: either the limiting exact-Nash
correspondence is the singleton all-Continue root, or a positive-absorption
root appears discontinuously at the limiting cap.  The latter is the precise
support-entry branch that a changed-state return theorem would have to
consume. -/
theorem exists_offMinimum_retainedLaw_allContinue_or_supportEntry
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (coalition : {S : Finset iota // S.Nonempty})
    (tolerance : ℝ) {M : ℝ}
    (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hatom : 0 < quittingStageCoalitionMass reward terminal stage coalition)
    (hnoReturn : ∀ n,
      quittingTerminalSemanticDebtSum minimum + tolerance <
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward
            (quittingMaximalCapPrefixProfile reward terminal n))) :
    ∃ cluster : QuittingTerminalSemanticLawPoint iota,
      cluster ∈ quittingTerminalSemanticLawCarrier reward ∧
      quittingTerminalSemanticDebtSum minimum + tolerance ≤
        quittingTerminalSemanticDebtSum cluster.1 ∧
      quittingTerminalSemanticDebtSum minimum /
            quittingTerminalSemanticDebtSum
              (quittingTerminalSemanticPair reward terminal) *
          quittingStageCoalitionMass reward terminal stage coalition ≤
        cluster.2 (some coalition) ∧
      0 < cluster.2 (some coalition) ∧
      IsεQuittingRootNash reward cluster.1.2 0
        (quittingAllContinueRoot : iota → PMF Bool) ∧
      ((∀ root : iota → PMF Bool,
          IsεQuittingRootNash reward cluster.1.2 0 root →
            root = (quittingAllContinueRoot : iota → PMF Bool)) ∨
        ∃ root : iota → PMF Bool,
          IsεQuittingRootNash reward cluster.1.2 0 root ∧
            0 < quittingRootAbsorptionMass root) := by
  let profile : ℕ → (quittingGame reward).BehaviorProfile :=
    quittingMaximalCapPrefixProfile reward terminal
  let root : ℕ → iota → PMF Bool := fun n ↦
    quittingMaximalCapPrefixRoot reward (profile n)
  let point : ℕ → QuittingTerminalSemanticLawPoint iota := fun n ↦
    (quittingTerminalSemanticPair reward (profile n),
      quittingTerminalOutcomeMass reward (profile n))
  have habsorption : Tendsto
      (fun n ↦ quittingRootAbsorptionMass (root n)) atTop (nhds 0) := by
    exact (summable_maximalCapPrefix_absorption reward minimum terminal
      hM hreward hminimum hminimumPositive).tendsto_atTop_zero
  have hquit : ∀ who, Tendsto (fun n ↦ (root n who true).toReal)
      atTop (nhds 0) := by
    intro who
    apply squeeze_zero
    · exact fun _ ↦ ENNReal.toReal_nonneg
    · exact fun n ↦ quitProbability_le_quittingRootAbsorptionMass
        (root n) who
    · exact habsorption
  let simplexRoot : ℕ → QuittingRootSimplex iota :=
    fun n who ↦ stdSimplexEquiv (root n who)
  have hsimplexRoot : Tendsto simplexRoot atTop
      (nhds (quittingAllContinueSimplexRoot : QuittingRootSimplex iota)) := by
    rw [tendsto_pi_nhds]
    intro who
    rw [tendsto_subtype_rng, tendsto_pi_nhds]
    intro action
    have hcoordinate : ∀ n,
        ((simplexRoot n who : stdSimplex ℝ Bool) : Bool → ℝ) action =
          (root n who action).toReal := by
      intro n
      exact congrFun (coe_stdSimplexEquiv_apply (root n who)) action
    have hallCoordinate :
        (((quittingAllContinueSimplexRoot : QuittingRootSimplex iota) who :
          stdSimplex ℝ Bool) : Bool → ℝ) action =
            (PMF.pure false action).toReal := by
      exact congrFun (coe_stdSimplexEquiv_apply (PMF.pure false)) action
    have hbase : Tendsto (fun n ↦ (root n who action).toReal)
        atTop (nhds ((PMF.pure false action).toReal)) := by
      cases action with
      | true => simpa using hquit who
      | false =>
          have hidentity : (fun n ↦ (root n who false).toReal) =
              fun n ↦ 1 - (root n who true).toReal := by
            funext n
            linarith [quittingRoot_continueProbability_add_quitProbability
              (root n) who]
          rw [hidentity]
          simpa using tendsto_const_nhds.sub (hquit who)
    have hactual := hbase.congr'
      (Filter.Eventually.of_forall fun n ↦ (hcoordinate n).symm)
    convert hactual using 1
    · rfl
    · exact congrArg nhds hallCoordinate
  have hpointMem : ∀ n, point n ∈
      quittingTerminalSemanticLawCarrier reward := by
    intro n
    exact quittingTerminalSemanticLawPoint_mem_carrier reward (profile n)
  obtain ⟨cluster, hcluster, subseq, hsubseq, hpointLimit⟩ :=
    (quittingTerminalSemanticLawCarrier_isCompact reward hM hreward).tendsto_subseq
      hpointMem
  have hpairLimit : Tendsto (fun rank ↦ (point (subseq rank)).1)
      atTop (nhds cluster.1) :=
    continuous_fst.continuousAt.tendsto.comp hpointLimit
  have hcapLimit : Tendsto (fun rank ↦ (point (subseq rank)).1.2)
      atTop (nhds cluster.1.2) :=
    continuous_snd.continuousAt.tendsto.comp hpairLimit
  have hrootLimit : Tendsto (fun rank ↦ simplexRoot (subseq rank))
      atTop (nhds (quittingAllContinueSimplexRoot : QuittingRootSimplex iota)) :=
    hsimplexRoot.comp hsubseq.tendsto_atTop
  have hnashLimit : IsεQuittingRootEndpointNash reward cluster.1.2 0
      (quittingRootOfSimplex
        (quittingAllContinueSimplexRoot : QuittingRootSimplex iota)) := by
    apply isεQuittingRootEndpointNash_of_tendsto reward
      (fun _ : ℕ ↦ 0) (fun rank ↦ (point (subseq rank)).1.2)
      (fun rank ↦ simplexRoot (subseq rank))
      tendsto_const_nhds hcapLimit hrootLimit
    filter_upwards [] with rank
    have hnash := quittingMaximalCapPrefixRoot_exactNash reward
      (profile (subseq rank))
    have hrootEq : quittingRootOfSimplex (simplexRoot (subseq rank)) =
        root (subseq rank) := by
      funext who
      exact (stdSimplexEquiv (α := Bool)).symm_apply_apply
        (root (subseq rank) who)
    rw [hrootEq]
    exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward (point (subseq rank)).1.2 0 (root (subseq rank))).2 hnash
  have hdebtLimit : Tendsto (fun rank ↦
      quittingTerminalSemanticDebtSum (point (subseq rank)).1)
      atTop (nhds (quittingTerminalSemanticDebtSum cluster.1)) :=
    continuous_quittingTerminalSemanticDebtSum.continuousAt.tendsto.comp
      hpairLimit
  have hoffMinimum : quittingTerminalSemanticDebtSum minimum + tolerance ≤
      quittingTerminalSemanticDebtSum cluster.1 :=
    ge_of_tendsto' hdebtLimit fun rank ↦ (hnoReturn (subseq rank)).le
  have hlawLimit : Tendsto (fun rank ↦
      (point (subseq rank)).2 (some coalition)) atTop
      (nhds (cluster.2 (some coalition))) :=
    ((continuous_apply (some coalition)).comp continuous_snd).continuousAt.tendsto.comp
      hpointLimit
  let lower := quittingTerminalSemanticDebtSum minimum /
      quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward terminal) *
      quittingStageCoalitionMass reward terminal stage coalition
  have hlower : ∀ n, lower ≤ (point n).2 (some coalition) := by
    intro n
    have hstageLower := maximalCapPrefix_atomMass_lowerBound
      reward minimum terminal stage n coalition hM hreward hminimum
        hminimumPositive
    have hstageToLaw := quittingStageCoalitionMass_le_terminalOutcomeMass
      reward (profile n) (n + stage) coalition
    exact hstageLower.trans hstageToLaw
  have hlawLower : lower ≤ cluster.2 (some coalition) :=
    ge_of_tendsto' hlawLimit fun rank ↦ hlower (subseq rank)
  have hinitialDebtPositive : 0 < quittingTerminalSemanticDebtSum
      (quittingTerminalSemanticPair reward terminal) :=
    hminimumPositive.trans_le (hminimum _
      (quittingTerminalSemanticPair_mem_carrier reward terminal))
  have hlowerPositive : 0 < lower := by
    exact mul_pos (div_pos hminimumPositive hinitialDebtPositive) hatom
  have hnashAllContinue : IsεQuittingRootNash reward cluster.1.2 0
      (quittingAllContinueRoot : iota → PMF Bool) := by
    rw [← quittingRootOfSimplex_allContinueSimplexRoot]
    exact (isεQuittingRootEndpointNash_iff_isεQuittingRootNash
      reward cluster.1.2 0 _).1 hnashLimit
  refine ⟨cluster, hcluster, hoffMinimum, hlawLower,
    hlowerPositive.trans_le hlawLower, hnashAllContinue, ?_⟩
  by_cases hunique : ∀ candidate : iota → PMF Bool,
      IsεQuittingRootNash reward cluster.1.2 0 candidate →
        candidate = (quittingAllContinueRoot : iota → PMF Bool)
  · exact Or.inl hunique
  · right
    push Not at hunique
    obtain ⟨candidate, hnash, hne⟩ := hunique
    refine ⟨candidate, hnash, ?_⟩
    have habsorptionNonneg : 0 ≤ quittingRootAbsorptionMass candidate :=
      quittingRootAbsorptionMass_nonneg candidate
    apply lt_of_le_of_ne habsorptionNonneg
    intro hzero
    have hcontinue : quittingStationaryContinueMass candidate = 1 := by
      unfold quittingRootAbsorptionMass at hzero
      linarith
    apply hne
    funext who
    simpa [quittingAllContinueRoot] using
      eq_pure_false_of_quittingStationaryContinueMass_eq_one hcontinue who

/-! ## Exact punishment-prefix realization of the changed-cap chronology -/

/-- Exact Nash against the envelope coordinate makes the new envelope itself
an exact Bellman successor of the old envelope.  This is stronger than the
usual debt-scaling identity: the cap chronology, unlike the prescribed-payoff
chronology, is already an exact Nash--Bellman chronology. -/
theorem quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (pair : QuittingTerminalSemanticPair iota)
    (root : iota → PMF Bool)
    (hnash : IsεQuittingRootNash reward pair.2 0 root) :
    (quittingTerminalSemanticPrefix reward root pair).2 =
      quittingRootSuccessorPayoff reward pair.2 root := by
  funext who
  have hquit : quittingRootQuitPayoff reward pair.1 root who =
      quittingRootQuitPayoff reward pair.2 root who :=
    quittingRootQuitPayoff_continuation_invariant
      reward pair.1 pair.2 root who
  have hcontinue :
      quittingRootContinuePayoff reward
          (Function.update pair.1 who (pair.2 who)) root who =
        quittingRootContinuePayoff reward pair.2 root who := by
    apply quittingRootExpectedPayoff_continuation_congr
    simp
  unfold quittingTerminalSemanticPrefix
  dsimp only
  rw [quittingRootSuccessorPayoff_eq_max_of_isZeroNash
    reward pair.2 root who hnash, hquit, hcontinue]

/-- The recursively recomputed maximal-cap roots, read in their natural
outward order, form an exact punishment-floor prefix on the *behavioral cap*
states.  Thus their absorption sum is not merely an analytic charge: it is
already accepted by the canonical finite-prefix capacity interface.

The construction uses no extra residual predicate. -/
noncomputable def quittingMaximalCapPrefixPunishmentFloorPrefix
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (horizon : ℕ) : QuittingPunishmentFloorFinitePrefix reward where
  roots := fun time ↦ quittingMaximalCapPrefixRoot reward
    (quittingMaximalCapPrefixProfile reward terminal time)
  value := fun time ↦
    (quittingTerminalSemanticPair reward
      (quittingMaximalCapPrefixProfile reward terminal time)).2
  horizon := horizon
  value_mem := by
    intro time _
    constructor
    · intro who
      exact neg_le_of_abs_le
        (abs_quittingContinuationBestResponseValue_le reward
          (quittingMaximalCapPrefixProfile reward terminal time) who
          (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward))
    · intro who
      exact le_of_abs_le
        (abs_quittingContinuationBestResponseValue_le reward
          (quittingMaximalCapPrefixProfile reward terminal time) who
          (quittingRewardBound_nonneg reward)
          (abs_reward_le_quittingRewardBound reward))
  anchor_floor := by
    intro who
    exact quittingPunishmentValue_le_terminalSemanticEnvelope
      (quittingTerminalSemanticPair reward terminal)
      (quittingTerminalSemanticPair_mem_carrier reward terminal) who
  policy := by
    intro time _
    rw [quittingMaximalCapPrefixProfile_succ,
      quittingTerminalSemanticPair_rootThenContinuation reward
        (quittingMaximalCapPrefixRoot reward
          (quittingMaximalCapPrefixProfile reward terminal time))
        (quittingMaximalCapPrefixProfile reward terminal time)
        (quittingRewardBound_nonneg reward)
        (abs_reward_le_quittingRewardBound reward)]
    exact
      quittingTerminalSemanticPrefix_envelope_eq_rootSuccessorPayoff_of_capNash
        reward
        (quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal time))
        (quittingMaximalCapPrefixRoot reward
          (quittingMaximalCapPrefixProfile reward terminal time))
        (quittingMaximalCapPrefixRoot_exactNash reward
          (quittingMaximalCapPrefixProfile reward terminal time))
  exactNash := by
    intro time _
    exact quittingMaximalCapPrefixRoot_exactNash reward
      (quittingMaximalCapPrefixProfile reward terminal time)

@[simp]
theorem quittingMaximalCapPrefixPunishmentFloorPrefix_charge
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (horizon : ℕ) :
    (quittingMaximalCapPrefixPunishmentFloorPrefix
        reward terminal horizon).charge =
      ∑ n ∈ Finset.range horizon,
        quittingRootAbsorptionMass
          (quittingMaximalCapPrefixRoot reward
            (quittingMaximalCapPrefixProfile reward terminal n)) := by
  rfl

/-- **Capacity-exhaustion no-go for the maximal-cap chronology.**  Although
every finite segment is a legal punishment-floor prefix, its charge is
uniformly bounded by the initial semantic excess divided by the positive
minimum debt.  Consequently this chronology cannot by itself trigger the
unbounded-prefix-charge compiler.  Any Q184 closure through capacity must
produce charge not already paid by this debt-scaling telescope. -/
theorem maximalCapPrefixPunishmentFloorPrefix_charge_le_semanticBudget
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (horizon : ℕ) :
    (quittingMaximalCapPrefixPunishmentFloorPrefix
        reward terminal horizon).charge ≤
      (quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward terminal) -
        quittingTerminalSemanticDebtSum minimum) /
          quittingTerminalSemanticDebtSum minimum := by
  rw [quittingMaximalCapPrefixPunishmentFloorPrefix_charge]
  have hcharged := minimum_mul_sum_maximalCapPrefix_absorption_le_debtDrop
    reward minimum terminal hM hreward hminimum horizon
  have hfinalLower := hminimum
    (quittingTerminalSemanticPair reward
      (quittingMaximalCapPrefixProfile reward terminal horizon))
    (quittingTerminalSemanticPair_mem_carrier reward _)
  apply (le_div_iff₀ hminimumPositive).2
  nlinarith

/-- **Hard Q184 reduction.**  At a positive global semantic minimum, the
first state-changing maximal cap root has only two possibilities.  If it has
positive absorption, it is already a positively charged exact
punishment-floor prefix and it literally retains every positive suffix atom.
If it has zero absorption, maximality forces *every* exact root against the
same cap to be all-Continue.

Consequently neither a separate owner decoder nor a support-entry decoder is
needed for the positive-absorption branch.  The unique all-Continue
correspondence is the sole surviving local obstruction. -/
theorem maximalCapPrefix_positivePunishmentCharge_retainingAtom_or_uniqueAllContinue
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (stage : ℕ) (coalition : {S : Finset iota // S.Nonempty})
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hatom : 0 <
      quittingStageCoalitionMass reward terminal stage coalition) :
    (0 < (quittingMaximalCapPrefixPunishmentFloorPrefix
          reward terminal 1).charge ∧
      0 < quittingStageCoalitionMass reward
        (quittingMaximalCapPrefixProfile reward terminal 1)
        (1 + stage) coalition) ∨
      ∀ candidate : iota → PMF Bool,
        IsεQuittingRootNash reward
            (quittingTerminalSemanticPair reward terminal).2 0 candidate →
          candidate = (quittingAllContinueRoot : iota → PMF Bool) := by
  let root := quittingMaximalCapPrefixRoot reward terminal
  have hnash : IsεQuittingRootNash reward
      (quittingTerminalSemanticPair reward terminal).2 0 root := by
    exact quittingMaximalCapPrefixRoot_exactNash reward terminal
  have hcontinue : 0 < quittingStationaryContinueMass root := by
    have hcontinueNonneg : 0 ≤ quittingStationaryContinueMass root :=
      quittingStationaryContinueMass_nonneg root
    by_contra hnot
    have hcontinueZero : quittingStationaryContinueMass root = 0 :=
      le_antisymm (le_of_not_gt hnot) hcontinueNonneg
    have hnextLower := hminimum
      (quittingTerminalSemanticPair reward
        (quittingMaximalCapPrefixProfile reward terminal 1))
      (quittingTerminalSemanticPair_mem_carrier reward _)
    have hstep := quittingMaximalCapPrefixProfile_debt_succ
      reward terminal hM hreward 0
    change quittingTerminalSemanticDebtSum
        (quittingTerminalSemanticPair reward
          (quittingMaximalCapPrefixProfile reward terminal 1)) =
      quittingStationaryContinueMass root *
        quittingTerminalSemanticDebtSum
          (quittingTerminalSemanticPair reward terminal) at hstep
    rw [hcontinueZero, zero_mul] at hstep
    rw [hstep] at hnextLower
    linarith
  by_cases hpositive : 0 < quittingRootAbsorptionMass root
  · left
    constructor
    · change 0 < ∑ n ∈ Finset.range 1,
          quittingRootAbsorptionMass
            (quittingMaximalCapPrefixRoot reward
              (quittingMaximalCapPrefixProfile reward terminal n))
      simpa [root]
    · have hstage := quittingMaximalCapPrefixProfile_stage_succ
        reward terminal stage 0 coalition
      have hstage' : quittingStageCoalitionMass reward
          (quittingMaximalCapPrefixProfile reward terminal 1)
            (1 + stage) coalition =
        quittingStationaryContinueMass root *
          quittingStageCoalitionMass reward terminal stage coalition := by
        simpa [root] using hstage
      rw [hstage']
      exact mul_pos hcontinue hatom
  · right
    have hrootZero : quittingRootAbsorptionMass root = 0 :=
      le_antisymm (le_of_not_gt hpositive)
        (quittingRootAbsorptionMass_nonneg root)
    intro candidate hcandidate
    have hle := quittingMaximalCapPrefixRoot_maximal
      reward terminal candidate hcandidate
    have hcandidateZero : quittingRootAbsorptionMass candidate = 0 := by
      apply le_antisymm
      · simpa [root, hrootZero] using hle
      · exact quittingRootAbsorptionMass_nonneg candidate
    have hcandidateContinue : quittingStationaryContinueMass candidate = 1 := by
      unfold quittingRootAbsorptionMass at hcandidateZero
      linarith
    funext who
    simpa [quittingAllContinueRoot] using
      eq_pure_false_of_quittingStationaryContinueMass_eq_one
        hcandidateContinue who

/-- The charged cap-rise/atom-retention theorem lands directly in the exact
punishment-prefix family.  This discharges the previously claimed "owner
decoder" gap for this branch: the cap rise need not first be decoded as a
same-row deviation in order for the canonical capacity to consume its
absorption charge. -/
theorem exists_maximalCapPrefix_punishmentFloorCharge_retainingAtom
    (reward : {S : Finset iota // S.Nonempty} → Payoff iota)
    (minimum : QuittingTerminalSemanticPair iota)
    (terminal : (quittingGame reward).BehaviorProfile)
    (blocker : iota) (eta : ℝ)
    (stage : ℕ) (coalition : {S : Finset iota // S.Nonempty})
    {M : ℝ} (hM : 0 ≤ M) (heta : 0 < eta)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hminimum : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum minimum ≤
        quittingTerminalSemanticDebtSum candidate)
    (hminimumPositive : 0 < quittingTerminalSemanticDebtSum minimum)
    (hinitialGap :
      (quittingTerminalSemanticPair reward terminal).2 blocker ≤
        reward (quittingSingletonTerminal blocker) blocker - eta) :
    ∃ horizon,
      let cert := quittingMaximalCapPrefixPunishmentFloorPrefix
        reward terminal horizon
      eta / 2 <
          (quittingTerminalSemanticPair reward
              (quittingMaximalCapPrefixProfile reward terminal horizon)).2
                blocker -
            (quittingTerminalSemanticPair reward terminal).2 blocker ∧
        eta / 2 < 4 * M * cert.charge ∧
        quittingTerminalSemanticDebtSum minimum /
              quittingTerminalSemanticDebtSum
                (quittingTerminalSemanticPair reward terminal) *
            quittingStageCoalitionMass reward terminal stage coalition ≤
          quittingStageCoalitionMass reward
            (quittingMaximalCapPrefixProfile reward terminal horizon)
            (horizon + stage) coalition := by
  obtain ⟨horizon, hrise, hcharge, hatom⟩ :=
    exists_maximalCapPrefix_chargedCapRise_retainingAtom
      reward minimum terminal blocker eta stage coalition hM heta hreward
        hminimum hminimumPositive hinitialGap
  refine ⟨horizon, hrise, ?_, hatom⟩
  simpa using hcharge

end GameTheory
