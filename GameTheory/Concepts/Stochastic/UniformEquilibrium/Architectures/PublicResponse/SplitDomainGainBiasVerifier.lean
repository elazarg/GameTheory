/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Architectures.PublicResponse.ExplicitDomainGainBiasVerifier
import Math.MeanErgodic

/-!
# Split-domain gain--bias verification

There are two genuinely different relevant domains here.  Prescribed
delivery is asserted on `R = ⋃ i, R_i`, while unilateral caps for player `i`
are asserted only on `R_i`.  The older `ClosedResponseRegion` cannot express
this split: its `prescribed_unilateral` field requires its prescribed domain
to lie in every owner arena.

This module adds the smallest separate foundation needed by that statement:
declared entries, a delivery domain, owner-specific arenas, the two inclusions
identifying delivery with their union, and independent prescribed/unilateral
support closure.  Two private-purpose adapters let existing theorems consume
the appropriate half without refactoring `ClosedResponseRegion`.

The main result is the sound gain--bias sufficiency direction on the exact
split domains.  The module also records that the existing mean-ergodic and
controlled-Farkas theorems already synthesize the prescribed and unilateral
biases once their respective hypotheses are available.  It does not prove the
asymptotic-property converse, recurrent coverage, necessity, or a fifth
obstruction theorem.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math.Probability
open scoped Topology

variable {ι : Type} {G : StochasticGame ι}

attribute [local instance] Fintype.ofFinite

namespace FiniteResponseArchitecture

section SplitFoundation

variable {initial : G.State} [Fintype ι] [DecidableEq ι]

/-- The split relevant domains for one supplied finite architecture.

`delivery` is exactly the union of the owner-specific `unilateral` arenas.
Entries are kept explicit because credibility may be claimed at more than the
architecture's distinguished start. -/
structure SplitResponseDomain (A : G.FiniteResponseArchitecture initial) where
  /-- Declared initial and handoff entries. -/
  entry : A.Config → Prop
  /-- Domain on which prescribed delivery is claimed. -/
  delivery : A.Config → Prop
  /-- Owner-specific unilateral arenas. -/
  unilateral : ι → A.Config → Prop
  /-- The architecture's distinguished start is a declared entry. -/
  start_entry : entry A.start
  /-- Every entry is in the delivery domain. -/
  entry_delivery : ∀ z, entry z → delivery z
  /-- Every entry belongs to every owner arena. -/
  entry_unilateral : ∀ who z, entry z → unilateral who z
  /-- Every owner arena lies in the delivery union. -/
  unilateral_delivery : ∀ who z, unilateral who z → delivery z
  /-- Every delivery-relevant node belongs to some owner arena. -/
  delivery_covered : ∀ z, delivery z → ∃ who, unilateral who z
  /-- Each owner arena is closed under that owner's pure unilateral rows. -/
  unilateral_closed : ∀ who z, unilateral who z → ∀ act y,
    y ∈ (A.nextConfigDist who z (PMF.pure act)).support → unilateral who y
  /-- The delivery domain is closed under prescribed play. -/
  delivery_closed : ∀ z, delivery z → ∀ y,
    y ∈ (A.prescribedConfigDist z).support → delivery y

namespace SplitResponseDomain

variable {A : G.FiniteResponseArchitecture initial}

/-- The delivery predicate is exactly the union of owner arenas. -/
theorem delivery_iff (D : A.SplitResponseDomain) (z : A.Config) :
    D.delivery z ↔ ∃ who, D.unilateral who z :=
  ⟨D.delivery_covered z, fun ⟨who, hz⟩ =>
    D.unilateral_delivery who z hz⟩

/-- Every declared entry belongs to both sides of the split. -/
theorem entry_domains (D : A.SplitResponseDomain) {z : A.Config}
    (hz : D.entry z) :
    D.delivery z ∧ ∀ who, D.unilateral who z :=
  ⟨D.entry_delivery z hz, fun who => D.entry_unilateral who z hz⟩

/-- Adapter for prescribed-delivery theorems.  Its unilateral predicate is
deliberately `True`; consumers of this adapter use only `.prescribed`. -/
def deliveryRegion (D : A.SplitResponseDomain) : A.ClosedResponseRegion where
  unilateral := fun _ _ => True
  prescribed := D.delivery
  start_unilateral := fun _ => trivial
  start_prescribed := D.entry_delivery A.start D.start_entry
  prescribed_unilateral := fun _ _ _ => trivial
  unilateral_closed := fun _ _ _ _ _ _ => trivial
  prescribed_closed := D.delivery_closed

/-- Adapter for owner-arena theorems.  Its unilateral predicates are exactly
the declared owner arenas.  The technical prescribed predicate is their
common intersection, which is prescribed-closed because prescribed play is a
mixture of every owner's pure rows.  Unilateral consumers read only
`.unilateral`. -/
def ownerRegion (D : A.SplitResponseDomain) : A.ClosedResponseRegion where
  unilateral := D.unilateral
  prescribed := fun z => ∀ who, D.unilateral who z
  start_unilateral := fun who => D.entry_unilateral who A.start D.start_entry
  start_prescribed := fun who =>
    D.entry_unilateral who A.start D.start_entry
  prescribed_unilateral := fun who _ hz => hz who
  unilateral_closed := D.unilateral_closed
  prescribed_closed := by
    intro z hz y hy who
    rw [A.prescribedConfigDist_eq who z,
      ClosedResponseRegion.nextConfigDist_eq_bind
        (A := A) who z (A.play z who),
      PMF.mem_support_bind_iff] at hy
    obtain ⟨act, -, hrow⟩ := hy
    exact D.unilateral_closed who z (hz who) act y hrow

@[simp] theorem deliveryRegion_prescribed (D : A.SplitResponseDomain)
    (z : A.Config) : D.deliveryRegion.prescribed z = D.delivery z :=
  rfl

@[simp] theorem ownerRegion_unilateral (D : A.SplitResponseDomain)
    (who : ι) (z : A.Config) :
    D.ownerRegion.unilateral who z = D.unilateral who z :=
  rfl

end SplitResponseDomain
end SplitFoundation

section ExistingBiasSynthesis

variable {initial : G.State} (A : G.FiniteResponseArchitecture initial)
  [Fintype ι] [DecidableEq ι]

namespace SplitResponseDomain

/-- Prescribed kernel restricted to the split delivery domain, with inert
self-loops outside. -/
noncomputable def restrictedPrescribedKernel (D : A.SplitResponseDomain)
    (z : A.Config) : PMF A.Config := by
  classical
  exact if D.delivery z then A.prescribedConfigDist z else PMF.pure z

/-- The Poisson charge `u_i-r_i^0` on the delivery domain and zero outside. -/
noncomputable def prescribedPoissonCharge (D : A.SplitResponseDomain)
    (u : A.Config → Payoff ι) (who : ι) (z : A.Config) : ℝ := by
  classical
  exact if D.delivery z then u z who - A.prescribedStagePayoff z who else 0

/-- The existing finite-dimensional mean-ergodic theorem supplies (A2) on the
delivery domain once the restricted prescribed charge has Cesàro limit zero. -/
theorem exists_prescribedBias_of_tendsto_cesaro_zero
    (D : A.SplitResponseDomain) (u : A.Config → Payoff ι) (who : ι)
    (hzero : Tendsto (fun T : ℕ =>
      (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
        ((Math.MeanErgodic.markovOperator
          (restrictedPrescribedKernel (A := A) D)) ^ t)
          (prescribedPoissonCharge (A := A) D u who)) atTop (nhds 0)) :
    ∃ bias : A.Config → ℝ, ∀ z : A.Config, D.delivery z →
      u z who + bias z = A.prescribedStagePayoff z who +
        expect (A.prescribedConfigDist z) bias := by
  classical
  obtain ⟨bias, hbias⟩ :=
    Math.MeanErgodic.exists_poisson_of_tendsto_cesaro_zero
      (restrictedPrescribedKernel (A := A) D)
      (prescribedPoissonCharge (A := A) D u who) hzero
  refine ⟨bias, ?_⟩
  intro z hz
  have h := hbias z
  simp [restrictedPrescribedKernel, prescribedPoissonCharge, hz] at h
  linarith

variable [∀ i, Finite (G.Act i)]

/-- The existing controlled Farkas theorem supplies (A4) on the owner arenas
from owner-local (Ti) and (N). -/
theorem exists_unilateralBias_of_targetOccupation
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hTi : ∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ act : G.Act who,
        expect (A.nextConfigDist who z (PMF.pure act))
          (fun y => u y who) ≤ u z who)
    (hN : A.IsNeutralOccupationNonpositiveOn D.ownerRegion u)
    (who : ι) :
    ∃ bias : A.Config → ℝ, ∀ z : A.Config, D.unilateral who z →
      ∀ act : G.Act who,
        A.stagePayoffAt who z (PMF.pure act) +
            expect (A.nextConfigDist who z (PMF.pure act)) bias ≤
          u z who + bias z := by
  have hTiOn : A.IsUnilateralTargetSuperharmonicOn D.ownerRegion u := by
    intro player z hz act
    exact hTi player z hz act
  exact A.exists_deviationPotentialOn hTiOn hN who

/-- Mean-ergodic prescribed charges together with owner-local (Ti) and (N)
produce both prescribed and unilateral bias families on their exact split
domains. -/
theorem exists_gainBiases_of_cesaro_targetOccupation
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hTi : ∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ act : G.Act who,
        expect (A.nextConfigDist who z (PMF.pure act))
          (fun y => u y who) ≤ u z who)
    (hN : A.IsNeutralOccupationNonpositiveOn D.ownerRegion u)
    (hzero : ∀ who : ι, Tendsto (fun T : ℕ =>
      (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T,
        ((Math.MeanErgodic.markovOperator
          (restrictedPrescribedKernel (A := A) D)) ^ t)
          (prescribedPoissonCharge (A := A) D u who)) atTop (nhds 0)) :
    ∃ prescribedBias unilateralBias : ι → A.Config → ℝ,
      (∀ (who : ι) (z : A.Config), D.delivery z →
        u z who + prescribedBias who z = A.prescribedStagePayoff z who +
          expect (A.prescribedConfigDist z) (prescribedBias who)) ∧
      (∀ (who : ι) (z : A.Config), D.unilateral who z →
        ∀ act : G.Act who,
          A.stagePayoffAt who z (PMF.pure act) +
              expect (A.nextConfigDist who z (PMF.pure act))
                (unilateralBias who) ≤
            u z who + unilateralBias who z) := by
  classical
  choose prescribedBias hprescribedBias using fun who =>
    D.exists_prescribedBias_of_tendsto_cesaro_zero A u who (hzero who)
  choose unilateralBias hunilateralBias using fun who =>
    D.exists_unilateralBias_of_targetOccupation A hTi hN who
  exact ⟨prescribedBias, unilateralBias, hprescribedBias, hunilateralBias⟩

end SplitResponseDomain
end ExistingBiasSynthesis

section SplitSufficiency

variable {initial : G.State} (A : G.FiniteResponseArchitecture initial)
  [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ i, Finite (G.Act i)]

/-- **Split-domain gain--bias sufficiency.**

The exact prescribed endpoint identity is valid at every node of the delivery
union.  The unilateral endpoint cap is valid at every node of the selected
owner's arena.  One explicit finite constant controls both `O(1/T)` remainders
uniformly over players, starts, horizons, and behavior deviations. -/
theorem exists_splitDomainGainBiasVerifier
    (D : A.SplitResponseDomain) {u : A.Config → Payoff ι}
    (hT0 : ∀ (who : ι) (z : A.Config), D.delivery z →
      expect (A.prescribedConfigDist z) (fun y => u y who) = u z who)
    (hTi : ∀ (who : ι) (z : A.Config), D.unilateral who z →
      ∀ act : G.Act who,
        expect (A.nextConfigDist who z (PMF.pure act))
          (fun y => u y who) ≤ u z who)
    (prescribedBias unilateralBias : ι → A.Config → ℝ)
    (hprescribedBias : ∀ (who : ι) (z : A.Config), D.delivery z →
      u z who + prescribedBias who z = A.prescribedStagePayoff z who +
        expect (A.prescribedConfigDist z) (prescribedBias who))
    (hunilateralBias : ∀ (who : ι) (z : A.Config),
      D.unilateral who z → ∀ act : G.Act who,
        A.stagePayoffAt who z (PMF.pure act) +
            expect (A.nextConfigDist who z (PMF.pure act))
              (unilateralBias who) ≤
          u z who + unilateralBias who z) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ (who : ι) (z : A.Config), D.delivery z → ∀ T : ℕ,
        (∑ t ∈ Finset.range T,
            G.expectedStagePayoff (A.rebase z).phaseProfile.behaviorProfile
              (A.publicState z) t who) =
          (T : ℝ) * u z who + prescribedBias who z -
            G.expectedHistoryValue (A.rebase z).phaseProfile.behaviorProfile
              (A.publicState z)
              (fun t h => prescribedBias who
                ((A.rebase z).configAt t h)) T) ∧
      (∀ (who : ι) (z : A.Config), D.unilateral who z →
        ∀ (dev : G.BehaviorStrategy who) (T : ℕ),
          (∑ t ∈ Finset.range T,
              G.expectedStagePayoff
                (Function.update (A.rebase z).phaseProfile.behaviorProfile
                  who dev)
                (A.publicState z) t who) ≤
            (T : ℝ) * u z who + unilateralBias who z -
              G.expectedHistoryValue
                (Function.update (A.rebase z).phaseProfile.behaviorProfile
                  who dev)
                (A.publicState z)
                (fun t h => unilateralBias who
                  ((A.rebase z).configAt t h)) T) ∧
      (∀ (who : ι) (z : A.Config), D.delivery z →
        ∀ {T : ℕ}, 0 < T →
          |G.finiteAveragePayoff (A.publicState z) T
              (A.rebase z).phaseProfile.behaviorProfile who - u z who| ≤
            M / T) ∧
      (∀ (who : ι) (z : A.Config), D.unilateral who z →
        ∀ (dev : G.BehaviorStrategy who) {T : ℕ}, 0 < T →
          G.finiteAveragePayoff (A.publicState z) T
              (Function.update (A.rebase z).phaseProfile.behaviorProfile
                who dev)
              who ≤ u z who + M / T) := by
  classical
  have hT0On : A.IsPrescribedTargetHarmonicOn D.deliveryRegion u := by
    intro who z hz
    exact hT0 who z hz
  have hTiOn : A.IsUnilateralTargetSuperharmonicOn D.ownerRegion u := by
    intro who z hz act
    exact hTi who z hz act
  let M : ℝ := ∑ who : ι,
    (2 * A.configBound (prescribedBias who) +
      2 * A.configBound (unilateralBias who))
  have hM : 0 ≤ M := by
    dsimp [M]
    exact Finset.sum_nonneg fun who _ => by
      have hp := A.configBound_nonneg (prescribedBias who)
      have hu := A.configBound_nonneg (unilateralBias who)
      linarith
  have hprescribedLe : ∀ who : ι,
      2 * A.configBound (prescribedBias who) ≤ M := by
    intro who
    have hpick :
        2 * A.configBound (prescribedBias who) +
            2 * A.configBound (unilateralBias who) ≤ M := by
      dsimp [M]
      exact Finset.single_le_sum
        (f := fun player =>
          2 * A.configBound (prescribedBias player) +
            2 * A.configBound (unilateralBias player))
        (fun player _ => by
          have hp := A.configBound_nonneg (prescribedBias player)
          have hu := A.configBound_nonneg (unilateralBias player)
          linarith)
        (Finset.mem_univ who)
    have hu := A.configBound_nonneg (unilateralBias who)
    linarith
  have hunilateralLe : ∀ who : ι,
      2 * A.configBound (unilateralBias who) ≤ M := by
    intro who
    have hpick :
        2 * A.configBound (prescribedBias who) +
            2 * A.configBound (unilateralBias who) ≤ M := by
      dsimp [M]
      exact Finset.single_le_sum
        (f := fun player =>
          2 * A.configBound (prescribedBias player) +
            2 * A.configBound (unilateralBias player))
        (fun player _ => by
          have hp := A.configBound_nonneg (prescribedBias player)
          have hu := A.configBound_nonneg (unilateralBias player)
          linarith)
        (Finset.mem_univ who)
    have hp := A.configBound_nonneg (prescribedBias who)
    linarith
  refine ⟨M, hM, ?_, ?_, ?_, ?_⟩
  · intro who z hz T
    exact A.expectedCumulativePayoff_prescribed_from_eq_on
      hT0On who (prescribedBias who) (hprescribedBias who) z hz T
  · intro who z hz dev T
    exact A.expectedCumulativePayoff_update_from_le_on
      hTiOn who (unilateralBias who) (hunilateralBias who) z hz dev T
  · intro who z hz T hT
    have hlocal := A.abs_finiteAveragePayoff_prescribed_from_sub_le_on
      hT0On who (prescribedBias who) (hprescribedBias who) z hz hT
    have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
    have hdiv := (div_le_div_iff_of_pos_right hTreal).2
      (hprescribedLe who)
    exact le_trans hlocal hdiv
  · intro who z hz dev T hT
    have hlocal := A.finiteAveragePayoff_update_from_le_on
      hTiOn who (unilateralBias who) (hunilateralBias who) z hz dev hT
    have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
    have hdiv := (div_le_div_iff_of_pos_right hTreal).2
      (hunilateralLe who)
    linarith

end SplitSufficiency

end FiniteResponseArchitecture
end StochasticGame
end GameTheory
