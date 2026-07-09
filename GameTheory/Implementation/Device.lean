/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Correlation.CorrelatedNashMixed
import GameTheory.Concepts.Correlation.Regret
import GameTheory.Concepts.Correlation.ApproximateCorrelatedEq
import GameTheory.Concepts.Mixed.MixedDominance
import GameTheory.Implementation.Exact
import Math.ProbabilityMassFunction

/-!
# Implementation devices

Semantic skeleton for the implementation devices used in
Monderer--Tennenholtz Section 6. A device draws private signals, players choose
signal-contingent actions, and the device pays nonnegative transfers based on
the signal profile and realized action profile.

The paper's dominance condition for devices is interim and conditional on
positive-probability signals. That proof layer is intentionally separate from
this file's prior-free compilation to a `KernelGame`.
-/

namespace GameTheory

open Math.Probability
open Math.ProbabilityMassFunction

namespace KernelGame

variable {ι : Type}

/-- An implementation device for a base game `G`: private signal spaces, a law
over signal profiles, and nonnegative transfers observed after signals and
actions are realized. -/
structure ImplementationDevice (G : KernelGame ι) where
  Signal : ι → Type
  law : PMF (∀ i, Signal i)
  transfer : (∀ i, Signal i) → Profile G → Payoff ι
  transfer_nonneg : ∀ θ σ i, 0 ≤ transfer θ σ i

namespace ImplementationDevice

variable {G : KernelGame ι} (I : G.ImplementationDevice)

/-- The base-game action profile realized by a device strategy profile at a
signal profile. -/
def play (b : ∀ i, I.Signal i → G.Strategy i) (θ : ∀ i, I.Signal i) :
    Profile G :=
  fun i => b i (θ i)

@[simp] theorem play_update [DecidableEq ι]
    (b : ∀ i, I.Signal i → G.Strategy i) (i : ι)
    (bi : I.Signal i → G.Strategy i) (θ : ∀ i, I.Signal i) :
    I.play (Function.update b i bi) θ =
      Function.update (I.play b θ) i (bi (θ i)) := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [play]
  · simp [play, Function.update_of_ne hji]

/-- The distribution over base-game profiles induced by device strategies. -/
noncomputable def inducedDistribution
    (b : ∀ i, I.Signal i → G.Strategy i) : PMF (Profile G) :=
  PMF.map (I.play b) I.law

/-- Device strategies induce the target profile distribution `μ`. -/
def ImplementsDistribution (b : ∀ i, I.Signal i → G.Strategy i)
    (μ : PMF (Profile G)) : Prop :=
  I.inducedDistribution b = μ

/-- A private signal has positive probability under the device law. -/
def PositiveSignal (i : ι) (si : I.Signal i) : Prop :=
  pmfMass (μ := I.law) (fun θ => θ i = si) ≠ 0

/-- The device law conditioned on player `i` receiving signal `si`. -/
noncomputable def conditionalSignalLaw (i : ι) (si : I.Signal i)
    (hsi : I.PositiveSignal i si) : PMF (∀ j, I.Signal j) :=
  pmfCond (μ := I.law) (fun θ => θ i = si) hsi

/-- Conditioning on `i`'s signal only leaves signal profiles with that
coordinate in support. -/
theorem conditionalSignalLaw_ne_zero_implies {i : ι} {si : I.Signal i}
    (hsi : I.PositiveSignal i si) {θ : ∀ j, I.Signal j}
    (hθ : I.conditionalSignalLaw i si hsi θ ≠ 0) :
    θ i = si :=
  pmfCond_ne_zero_implies I.law (fun θ => θ i = si) hsi hθ

/-- Compile an implementation device into a kernel game. A strategy is a
signal-contingent action rule. Outcomes record the signal profile, realized
base-game profile, and base-game outcome, so utilities can add the promised
transfer. -/
noncomputable def deviceGame : KernelGame ι where
  Strategy := fun i => I.Signal i → G.Strategy i
  Outcome := (∀ i, I.Signal i) × Profile G × G.Outcome
  utility := fun ω i => G.utility ω.2.2 i + I.transfer ω.1 ω.2.1 i
  outcomeKernel := fun b =>
    I.law.bind fun θ =>
      PMF.map (fun ω => (θ, I.play b θ, ω)) (G.outcomeKernel (I.play b θ))

@[simp] theorem deviceGame_Strategy :
    I.deviceGame.Strategy = fun i => I.Signal i → G.Strategy i := rfl

@[simp] theorem deviceGame_utility
    (ω : (∀ i, I.Signal i) × Profile G × G.Outcome) (i : ι) :
    I.deviceGame.utility ω i = G.utility ω.2.2 i + I.transfer ω.1 ω.2.1 i := rfl

@[simp] theorem deviceGame_outcomeKernel
    (b : Profile I.deviceGame) :
    I.deviceGame.outcomeKernel b =
      I.law.bind fun θ =>
        PMF.map (fun ω => (θ, I.play b θ, ω)) (G.outcomeKernel (I.play b θ)) := rfl

/-- Expected utility in the compiled device game is the signal-law expectation
of base expected utility plus the realized transfer. This finite version is the
bridge needed by the paper's device arguments. -/
theorem deviceGame_eu [Finite (∀ i, I.Signal i)] [Finite (Profile G)]
    [Finite G.Outcome] (b : ∀ i, I.Signal i → G.Strategy i) (i : ι) :
    I.deviceGame.eu b i =
      expect I.law (fun θ => G.eu (I.play b θ) i + I.transfer θ (I.play b θ) i) := by
  classical
  letI : Finite I.deviceGame.Outcome := by
    change Finite ((∀ i, I.Signal i) × Profile G × G.Outcome)
    infer_instance
  rw [KernelGame.eu]
  change
    expect
      (I.law.bind fun θ =>
        PMF.map (fun ω => (θ, I.play b θ, ω)) (G.outcomeKernel (I.play b θ)))
      (fun ω => I.deviceGame.utility ω i) =
    expect I.law (fun θ => G.eu (I.play b θ) i + I.transfer θ (I.play b θ) i)
  rw [expect_bind]
  congr 1
  funext θ
  let σ : Profile G := I.play b θ
  calc
    expect (PMF.map (fun ω => (θ, I.play b θ, ω)) (G.outcomeKernel (I.play b θ)))
        (fun ω => I.deviceGame.utility ω i)
        = expect (G.outcomeKernel σ) (fun ω => I.deviceGame.utility (θ, σ, ω) i) := by
          letI : Fintype G.Outcome := Fintype.ofFinite G.Outcome
          rw [expect_map_fintype_source, expect_eq_sum]
    _ = expect (G.outcomeKernel σ)
        (fun ω => G.utility ω i + I.transfer θ σ i) := by
          rfl
    _ = G.eu σ i + I.transfer θ σ i := by
          rw [expect_add]
          simp [KernelGame.eu]

/-- The conditional outcome kernel used for interim utility after player `i`
observes signal `si`. -/
noncomputable def interimOutcomeKernel (i : ι) (si : I.Signal i)
    (hsi : I.PositiveSignal i si) (b : Profile I.deviceGame) :
    PMF I.deviceGame.Outcome :=
  (I.conditionalSignalLaw i si hsi).bind fun θ =>
    PMF.map (fun ω => (θ, I.play b θ, ω)) (G.outcomeKernel (I.play b θ))

/-- Interim expected utility in the device game, conditional on player `i`'s
private signal. -/
noncomputable def interimEu (i : ι) (si : I.Signal i)
    (hsi : I.PositiveSignal i si) (b : Profile I.deviceGame) : ℝ :=
  expect (I.interimOutcomeKernel i si hsi b) (fun ω => I.deviceGame.utility ω i)

/-- Interim expected utility is expectation under the conditional signal law of
base expected utility plus transfer. -/
theorem interimEu_eq_expect_conditional
    [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    (i : ι) (si : I.Signal i) (hsi : I.PositiveSignal i si)
    (b : ∀ j, I.Signal j → G.Strategy j) :
    I.interimEu i si hsi b =
      expect (I.conditionalSignalLaw i si hsi)
        (fun θ => G.eu (I.play b θ) i + I.transfer θ (I.play b θ) i) := by
  classical
  letI : Finite I.deviceGame.Outcome := by
    change Finite ((∀ i, I.Signal i) × Profile G × G.Outcome)
    infer_instance
  rw [interimEu, interimOutcomeKernel]
  rw [expect_bind]
  congr 1
  funext θ
  let σ : Profile G := I.play b θ
  calc
    expect (PMF.map (fun ω => (θ, I.play b θ, ω)) (G.outcomeKernel (I.play b θ)))
        (fun ω => I.deviceGame.utility ω i)
        = expect (G.outcomeKernel σ) (fun ω => I.deviceGame.utility (θ, σ, ω) i) := by
          letI : Fintype G.Outcome := Fintype.ofFinite G.Outcome
          rw [expect_map_fintype_source, expect_eq_sum]
    _ = expect (G.outcomeKernel σ)
        (fun ω => G.utility ω i + I.transfer θ σ i) := by
          rfl
    _ = G.eu σ i + I.transfer θ σ i := by
          rw [expect_add]
          simp [KernelGame.eu]

section InterimDominance

variable [DecidableEq ι]

/-- Interim weak dominance of one signal-contingent strategy over another:
after every positive-probability own signal, it gives at least as much
conditional expected utility against every opponent behavior profile. -/
def InterimWeaklyDominates (i : ι)
    (b c : I.Signal i → G.Strategy i) : Prop :=
  ∀ (si : I.Signal i) (hsi : I.PositiveSignal i si) (β : Profile I.deviceGame),
    I.interimEu i si hsi (Function.update β i b) ≥
      I.interimEu i si hsi (Function.update β i c)

/-- Interim weak dominance with at least one strict conditional witness. -/
def InterimWeaklyStrictlyDominates (i : ι)
    (b c : I.Signal i → G.Strategy i) : Prop :=
  I.InterimWeaklyDominates i b c ∧
    ∃ (si : I.Signal i) (hsi : I.PositiveSignal i si) (β : Profile I.deviceGame),
      I.interimEu i si hsi (Function.update β i b) >
        I.interimEu i si hsi (Function.update β i c)

/-- Paper-style interim weak dominance of one action over another after a fixed
positive-probability signal. The comparison holds against every profile of
opponents' signal-contingent behavior; the player's own contingent behavior away
from the observed signal is irrelevant, so we represent the two actions by
constant rules. -/
def InterimActionWeaklyDominates (i : ι) (si : I.Signal i)
    (hsi : I.PositiveSignal i si) (a b : G.Strategy i) : Prop :=
  ∀ β : Profile I.deviceGame,
    I.interimEu i si hsi (Function.update β i (fun _ => a)) ≥
      I.interimEu i si hsi (Function.update β i (fun _ => b))

/-- Paper-style interim weak dominance with a strict witness after a fixed
positive-probability signal. -/
def InterimActionWeaklyStrictlyDominates (i : ι) (si : I.Signal i)
    (hsi : I.PositiveSignal i si) (a b : G.Strategy i) : Prop :=
  I.InterimActionWeaklyDominates i si hsi a b ∧
    ∃ β : Profile I.deviceGame,
      I.interimEu i si hsi (Function.update β i (fun _ => a)) >
        I.interimEu i si hsi (Function.update β i (fun _ => b))

/-- Conditional on signal `si`, a player's contingent rule only matters through
its value at `si`. -/
theorem interimEu_update_eq_const_at_signal [Finite (∀ j, I.Signal j)]
    [Finite (Profile G)] [Finite G.Outcome]
    {i : ι} {si : I.Signal i} (hsi : I.PositiveSignal i si)
    (β : Profile I.deviceGame) (b : I.Signal i → G.Strategy i) :
    I.interimEu i si hsi (Function.update β i b) =
      I.interimEu i si hsi (Function.update β i (fun _ => b si)) := by
  rw [I.interimEu_eq_expect_conditional]
  rw [I.interimEu_eq_expect_conditional]
  refine expect_congr_of_ne_zero (I.conditionalSignalLaw i si hsi) _ _ ?_
  intro θ hθ
  have hθi := I.conditionalSignalLaw_ne_zero_implies hsi hθ
  have hplay :
      I.play (Function.update β i b) θ =
        I.play (Function.update β i (fun _ => b si)) θ := by
    rw [I.play_update, I.play_update, hθi]
  simp [hplay]

/-- Signal-by-signal action dominance lifts to dominance between
signal-contingent rules. -/
theorem interimWeaklyStrictlyDominates_of_interimAction
    [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    {i : ι} {b c : I.Signal i → G.Strategy i}
    (hweak : ∀ si (hsi : I.PositiveSignal i si),
      I.InterimActionWeaklyDominates i si hsi (b si) (c si))
    (hstrict : ∃ (si : I.Signal i) (hsi : I.PositiveSignal i si),
      I.InterimActionWeaklyStrictlyDominates i si hsi (b si) (c si)) :
    I.InterimWeaklyStrictlyDominates i b c := by
  constructor
  · intro si hsi β
    calc
      I.interimEu i si hsi (Function.update β i b) =
          I.interimEu i si hsi (Function.update β i (fun _ => b si)) :=
            I.interimEu_update_eq_const_at_signal hsi β b
      _ ≥ I.interimEu i si hsi (Function.update β i (fun _ => c si)) :=
            hweak si hsi β
      _ = I.interimEu i si hsi (Function.update β i c) :=
            (I.interimEu_update_eq_const_at_signal hsi β c).symm
  · rcases hstrict with ⟨si, hsi, hact⟩
    rcases hact.2 with ⟨β, hβ⟩
    refine ⟨si, hsi, β, ?_⟩
    calc
      I.interimEu i si hsi (Function.update β i b) =
          I.interimEu i si hsi (Function.update β i (fun _ => b si)) :=
            I.interimEu_update_eq_const_at_signal hsi β b
      _ > I.interimEu i si hsi (Function.update β i (fun _ => c si)) := hβ
      _ = I.interimEu i si hsi (Function.update β i c) :=
            (I.interimEu_update_eq_const_at_signal hsi β c).symm

/-- A signal-contingent strategy is interim dominant if it interim-weakly
dominates every alternative signal-contingent strategy. -/
def InterimDominant (i : ι) (b : I.Signal i → G.Strategy i) : Prop :=
  ∀ c : I.Signal i → G.Strategy i, I.InterimWeaklyDominates i b c

/-- Every player follows an interim dominant signal-contingent strategy. -/
def InterimDominantProfile (b : ∀ i, I.Signal i → G.Strategy i) : Prop :=
  ∀ i, I.InterimDominant i (b i)

/-- A signal-contingent strategy is strictly interim dominant when it interim
weakly-strictly dominates every distinct alternative. This is the device-level
analogue of the paper's dominance convention with an existential strict
conditional witness. -/
def InterimWeaklyStrictlyDominant (i : ι)
    (b : I.Signal i → G.Strategy i) : Prop :=
  ∀ c : I.Signal i → G.Strategy i, c ≠ b →
    I.InterimWeaklyStrictlyDominates i b c

/-- Every player follows a strictly interim dominant signal-contingent strategy. -/
def InterimWeaklyStrictlyDominantProfile
    (b : ∀ i, I.Signal i → G.Strategy i) : Prop :=
  ∀ i, I.InterimWeaklyStrictlyDominant i (b i)

theorem InterimWeaklyStrictlyDominant.interimDominant {i : ι}
    {b : I.Signal i → G.Strategy i}
    (h : I.InterimWeaklyStrictlyDominant i b) :
    I.InterimDominant i b := by
  intro c
  by_cases hc : c = b
  · subst hc
    intro si hsi β
    rfl
  · exact (h c hc).1

theorem InterimWeaklyStrictlyDominantProfile.interimDominantProfile
    {b : ∀ i, I.Signal i → G.Strategy i}
    (h : I.InterimWeaklyStrictlyDominantProfile b) :
    I.InterimDominantProfile b :=
  fun i => (h i).interimDominant (I := I)

/-- A device interim-dominantly implements a distribution when interim dominant
behavior induces that distribution over base-game profiles. -/
def InterimDominantImplementsDistribution
    (b : ∀ i, I.Signal i → G.Strategy i) (μ : PMF (Profile G)) : Prop :=
  I.InterimDominantProfile b ∧ I.ImplementsDistribution b μ

/-- Device-level k-implementation of a distribution: interim dominant behavior
induces the target law, and total transfers on every signal profile in the
device's support are bounded by `k`. -/
def InterimDominantKImplementsDistribution [Fintype ι]
    (b : ∀ i, I.Signal i → G.Strategy i) (μ : PMF (Profile G)) (k : ℝ) : Prop :=
  I.InterimDominantImplementsDistribution b μ ∧
    ∀ θ, I.law θ ≠ 0 → ∑ i, I.transfer θ (I.play b θ) i ≤ k

/-- Expected realized transfer paid by a device when the signal-contingent
profile `b` is followed.  This is the ex-ante mediator outlay, unlike
`InterimDominantKImplementsDistribution`, whose budget is pointwise on every
supported signal profile. -/
noncomputable def expectedRealizedTransfer [Fintype ι]
    (b : ∀ i, I.Signal i → G.Strategy i) : ℝ :=
  expect I.law fun θ => ∑ i, I.transfer θ (I.play b θ) i

/-- Player `i`'s expected realized transfer when the signal-contingent profile
`b` is followed. -/
noncomputable def expectedRealizedTransferTo
    (b : ∀ i, I.Signal i → G.Strategy i) (i : ι) : ℝ :=
  expect I.law fun θ => I.transfer θ (I.play b θ) i

/-- Expected-cost version of device-level implementation.  This is deliberately
separate from the paper-facing pointwise budget above. -/
def InterimDominantExpectedKImplementsDistribution [Fintype ι]
    (b : ∀ i, I.Signal i → G.Strategy i) (μ : PMF (Profile G)) (k : ℝ) : Prop :=
  I.InterimDominantImplementsDistribution b μ ∧
    I.expectedRealizedTransfer b ≤ k

/-- Strict interim-dominance implementation of a distribution. This mirrors the
paper's device dominance convention, where every distinct alternative is
dominated with an existential strict conditional witness. -/
def InterimWeaklyStrictlyDominantImplementsDistribution
    (b : ∀ i, I.Signal i → G.Strategy i) (μ : PMF (Profile G)) : Prop :=
  I.InterimWeaklyStrictlyDominantProfile b ∧ I.ImplementsDistribution b μ

/-- k-bounded strict interim-dominance implementation of a distribution. -/
def InterimWeaklyStrictlyDominantKImplementsDistribution [Fintype ι]
    (b : ∀ i, I.Signal i → G.Strategy i) (μ : PMF (Profile G)) (k : ℝ) : Prop :=
  I.InterimWeaklyStrictlyDominantImplementsDistribution b μ ∧
    ∀ θ, I.law θ ≠ 0 → ∑ i, I.transfer θ (I.play b θ) i ≤ k

/-- Expected-cost version of strict device-level implementation. -/
def InterimWeaklyStrictlyDominantExpectedKImplementsDistribution [Fintype ι]
    (b : ∀ i, I.Signal i → G.Strategy i) (μ : PMF (Profile G)) (k : ℝ) : Prop :=
  I.InterimWeaklyStrictlyDominantImplementsDistribution b μ ∧
    I.expectedRealizedTransfer b ≤ k

omit [DecidableEq ι] in
theorem expectedRealizedTransfer_nonneg [Fintype ι]
    (b : ∀ i, I.Signal i → G.Strategy i) :
    0 ≤ I.expectedRealizedTransfer b := by
  classical
  exact expect_nonneg I.law _ fun θ =>
    Finset.sum_nonneg fun i _ => I.transfer_nonneg θ (I.play b θ) i

omit [DecidableEq ι] in
theorem expectedRealizedTransferTo_nonneg
    (b : ∀ i, I.Signal i → G.Strategy i) (i : ι) :
    0 ≤ I.expectedRealizedTransferTo b i :=
  expect_nonneg I.law _ fun θ => I.transfer_nonneg θ (I.play b θ) i

omit [DecidableEq ι] in
theorem expectedRealizedTransfer_eq_sum_to [Fintype ι] [Finite (∀ i, I.Signal i)]
    (b : ∀ i, I.Signal i → G.Strategy i) :
    I.expectedRealizedTransfer b = ∑ i, I.expectedRealizedTransferTo b i := by
  classical
  rw [expectedRealizedTransfer, ← expect_sum_comm]
  rfl

theorem InterimDominantKImplementsDistribution.toExpected
    [Fintype ι] [Finite (∀ i, I.Signal i)]
    {b : ∀ i, I.Signal i → G.Strategy i} {μ : PMF (Profile G)} {k : ℝ}
    (h : I.InterimDominantKImplementsDistribution b μ k) :
    I.InterimDominantExpectedKImplementsDistribution b μ k := by
  classical
  letI : Fintype (∀ i, I.Signal i) := Fintype.ofFinite (∀ i, I.Signal i)
  refine ⟨h.1, ?_⟩
  rw [expectedRealizedTransfer, expect_eq_sum]
  calc
    (∑ θ : ∀ i, I.Signal i,
        (I.law θ).toReal * ∑ i, I.transfer θ (I.play b θ) i)
        ≤ ∑ θ : ∀ i, I.Signal i, (I.law θ).toReal * k := by
          refine Finset.sum_le_sum ?_
          intro θ _
          by_cases hθ : I.law θ = 0
          · simp [hθ]
          · exact mul_le_mul_of_nonneg_left (h.2 θ hθ) ENNReal.toReal_nonneg
    _ = k := by
          rw [← Finset.sum_mul, pmf_toReal_sum_one, one_mul]

theorem InterimWeaklyStrictlyDominantKImplementsDistribution.toExpected
    [Fintype ι] [Finite (∀ i, I.Signal i)]
    {b : ∀ i, I.Signal i → G.Strategy i} {μ : PMF (Profile G)} {k : ℝ}
    (h : I.InterimWeaklyStrictlyDominantKImplementsDistribution b μ k) :
    I.InterimWeaklyStrictlyDominantExpectedKImplementsDistribution b μ k := by
  classical
  refine ⟨h.1, ?_⟩
  have hweak :
      I.InterimDominantKImplementsDistribution b μ k :=
    ⟨⟨h.1.1.interimDominantProfile (G := G) (I := I), h.1.2⟩, h.2⟩
  exact hweak.toExpected.2

/-- Interim weak dominance implies ordinary weak dominance in the compiled
device game. This is the finite law-of-total-expectation bridge from the
paper's conditional dominance convention to the library's ex-ante dominance. -/
theorem InterimWeaklyDominates.toWeaklyDominates
    [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    {i : ι} [Finite (I.Signal i)]
    {b c : I.Signal i → G.Strategy i}
    (h : I.InterimWeaklyDominates i b c) :
    I.deviceGame.WeaklyDominates i b c := by
  classical
  letI : Fintype (I.Signal i) := Fintype.ofFinite (I.Signal i)
  intro β
  let β' : ∀ j, I.Signal j → G.Strategy j := β
  let βb : ∀ j, I.Signal j → G.Strategy j := Function.update β' i b
  let βc : ∀ j, I.Signal j → G.Strategy j := Function.update β' i c
  change I.deviceGame.eu βb i ≥ I.deviceGame.eu βc i
  rw [I.deviceGame_eu βb i]
  rw [I.deviceGame_eu βc i]
  let F : (∀ j, I.Signal j) → ℝ :=
    fun θ => G.eu (I.play βc θ) i + I.transfer θ (I.play βc θ) i
  let H : (∀ j, I.Signal j) → ℝ :=
    fun θ => G.eu (I.play βb θ) i + I.transfer θ (I.play βb θ) i
  change expect I.law F ≤ expect I.law H
  rw [expect_eq_sum_fiber_cond (μ := I.law) (proj := fun θ => θ i) (f := F)]
  rw [expect_eq_sum_fiber_cond (μ := I.law) (proj := fun θ => θ i) (f := H)]
  exact Finset.sum_le_sum fun si _ => by
    by_cases hsi : pmfMass (μ := I.law) (fun θ => si = θ i) ≠ 0
    · simp only [dif_pos hsi]
      have hsi' : I.PositiveSignal i si := by
        simpa [PositiveSignal, eq_comm] using hsi
      have hcond := h si hsi' β
      rw [I.interimEu_eq_expect_conditional i si hsi'] at hcond
      rw [I.interimEu_eq_expect_conditional i si hsi'] at hcond
      change expect (I.conditionalSignalLaw i si hsi') H ≥
        expect (I.conditionalSignalLaw i si hsi') F at hcond
      have hcond' :
          expect (pmfCond (μ := I.law) (fun θ => si = θ i) hsi) F ≤
            expect (pmfCond (μ := I.law) (fun θ => si = θ i) hsi) H := by
        simpa [conditionalSignalLaw, PositiveSignal, eq_comm] using hcond
      exact mul_le_mul_of_nonneg_left hcond' ENNReal.toReal_nonneg
    · simp [hsi]

/-- Interim weak dominance with a strict conditional witness gives ordinary
weak dominance with a strict witness in the compiled device game. -/
theorem InterimWeaklyStrictlyDominates.toWeaklyStrictlyDominates
    [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    {i : ι} [Finite (I.Signal i)]
    {b c : I.Signal i → G.Strategy i}
    (h : I.InterimWeaklyStrictlyDominates i b c) :
    I.deviceGame.WeaklyStrictlyDominates i b c := by
  classical
  letI : Fintype (I.Signal i) := Fintype.ofFinite (I.Signal i)
  refine ⟨h.1.toWeaklyDominates (G := G) (I := I), ?_⟩
  obtain ⟨si, hsi, β, hstrict⟩ := h.2
  refine ⟨β, ?_⟩
  let β' : ∀ j, I.Signal j → G.Strategy j := β
  let βb : ∀ j, I.Signal j → G.Strategy j := Function.update β' i b
  let βc : ∀ j, I.Signal j → G.Strategy j := Function.update β' i c
  change I.deviceGame.eu βb i > I.deviceGame.eu βc i
  rw [I.deviceGame_eu βb i]
  rw [I.deviceGame_eu βc i]
  let F : (∀ j, I.Signal j) → ℝ :=
    fun θ => G.eu (I.play βc θ) i + I.transfer θ (I.play βc θ) i
  let H : (∀ j, I.Signal j) → ℝ :=
    fun θ => G.eu (I.play βb θ) i + I.transfer θ (I.play βb θ) i
  change expect I.law H > expect I.law F
  rw [expect_eq_sum_fiber_cond (μ := I.law) (proj := fun θ => θ i) (f := H)]
  rw [expect_eq_sum_fiber_cond (μ := I.law) (proj := fun θ => θ i) (f := F)]
  apply Finset.sum_lt_sum
  · intro sj _
    by_cases hsj : pmfMass (μ := I.law) (fun θ => sj = θ i) ≠ 0
    · simp only [dif_pos hsj]
      have hsj' : I.PositiveSignal i sj := by
        simpa [PositiveSignal, eq_comm] using hsj
      have hcond := h.1 sj hsj' β
      rw [I.interimEu_eq_expect_conditional i sj hsj'] at hcond
      rw [I.interimEu_eq_expect_conditional i sj hsj'] at hcond
      change expect (I.conditionalSignalLaw i sj hsj') H ≥
        expect (I.conditionalSignalLaw i sj hsj') F at hcond
      have hcond' :
          expect (pmfCond (μ := I.law) (fun θ => sj = θ i) hsj) F ≤
            expect (pmfCond (μ := I.law) (fun θ => sj = θ i) hsj) H := by
        simpa [conditionalSignalLaw, PositiveSignal, eq_comm] using hcond
      exact mul_le_mul_of_nonneg_left hcond' ENNReal.toReal_nonneg
    · simp [hsj]
  · refine ⟨si, Finset.mem_univ si, ?_⟩
    have hsi_symm : pmfMass (μ := I.law) (fun θ => si = θ i) ≠ 0 := by
      simpa [PositiveSignal, eq_comm] using hsi
    simp only [dif_pos hsi_symm]
    rw [I.interimEu_eq_expect_conditional i si hsi] at hstrict
    rw [I.interimEu_eq_expect_conditional i si hsi] at hstrict
    change expect (I.conditionalSignalLaw i si hsi) H >
      expect (I.conditionalSignalLaw i si hsi) F at hstrict
    have hstrict' :
        expect (pmfCond (μ := I.law) (fun θ => si = θ i) hsi_symm) F <
          expect (pmfCond (μ := I.law) (fun θ => si = θ i) hsi_symm) H := by
      simpa [conditionalSignalLaw, PositiveSignal, eq_comm] using hstrict
    have hmass_pos :
        0 < (pmfMass (μ := I.law) (fun θ => si = θ i)).toReal :=
      ENNReal.toReal_pos hsi_symm (pmfMass_ne_top I.law (fun θ => si = θ i))
    exact mul_lt_mul_of_pos_left hstrict' hmass_pos

/-- Interim dominance gives ordinary dominance in the compiled device game. -/
theorem InterimDominant.isDominant
    [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    {i : ι} [Finite (I.Signal i)] {b : I.Signal i → G.Strategy i}
    (h : I.InterimDominant i b) :
    I.deviceGame.IsDominant i b := by
  intro β c
  exact (h c).toWeaklyDominates (G := G) (I := I) β

/-- Interim dominance also gives dominance against mixed deviations in the
mixed extension of the compiled device game. -/
theorem InterimDominant.isDominant_mixedExtension
    [Fintype ι] [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ j, Finite (I.Signal j)] [∀ j, Finite (G.Strategy j)]
    {i : ι} {b : I.Signal i → G.Strategy i}
    (h : I.InterimDominant i b) :
    I.deviceGame.mixedExtension.IsDominant i (PMF.pure b) := by
  classical
  haveI : Finite I.deviceGame.Outcome := by
    change Finite ((∀ j, I.Signal j) × Profile G × G.Outcome)
    infer_instance
  haveI : ∀ j, Finite (I.deviceGame.Strategy j) := by
    intro j
    change Finite (I.Signal j → G.Strategy j)
    infer_instance
  haveI : Finite (Profile I.deviceGame) := by
    change Finite (∀ j, I.Signal j → G.Strategy j)
    infer_instance
  exact (h.isDominant (G := G) (I := I)).pure_to_mixedExtension

/-- Any interim-dominant expected implementation must compensate each player's
swap regret in expectation.  The proof uses the compiled device game: a swap
deviation in the base game is simulated by the signal-contingent rule
`si ↦ dev (b_i si)`. -/
theorem swapRegret_le_expectedRealizedTransferTo_of_interimDominant
    [Finite (∀ i, I.Signal i)] [∀ i, Finite (I.Signal i)]
    [Finite (Profile G)] [Finite G.Outcome]
    {b : ∀ i, I.Signal i → G.Strategy i} {μ : PMF (Profile G)}
    (h : I.InterimDominantImplementsDistribution b μ)
    (i : ι) (dev : G.Strategy i → G.Strategy i) :
    G.swapRegret μ i dev ≤ I.expectedRealizedTransferTo b i := by
  classical
  letI : Fintype (∀ i, I.Signal i) := Fintype.ofFinite (∀ i, I.Signal i)
  let bProfile : Profile I.deviceGame := b
  let c : I.Signal i → G.Strategy i := fun si => dev (b i si)
  let devProfile : Profile I.deviceGame := Function.update bProfile i c
  have hweak : I.InterimWeaklyDominates i (b i) c := h.1 i c
  have hdom : I.deviceGame.WeaklyDominates i (b i) c :=
    hweak.toWeaklyDominates (G := G) (I := I)
  have heu_raw := hdom bProfile
  have hupdate_self : Function.update bProfile i (b i) = bProfile := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp [bProfile]
    · simp [bProfile, Function.update_of_ne hji]
  have heu : I.deviceGame.eu bProfile i ≥ I.deviceGame.eu devProfile i := by
    rw [hupdate_self] at heu_raw
    exact heu_raw
  rw [I.deviceGame_eu bProfile i] at heu
  rw [I.deviceGame_eu devProfile i] at heu
  have hdev_play :
      ∀ θ, I.play devProfile θ =
        Function.update (I.play b θ) i (dev ((I.play b θ) i)) := by
    intro θ
    dsimp [devProfile]
    rw [I.play_update]
    simp [bProfile, c, ImplementationDevice.play]
  have heu' :
      expect I.law
          (fun θ => G.eu (I.play b θ) i + I.transfer θ (I.play b θ) i) ≥
        expect I.law
          (fun θ =>
            G.eu (Function.update (I.play b θ) i (dev ((I.play b θ) i))) i +
              I.transfer θ
                (Function.update (I.play b θ) i (dev ((I.play b θ) i))) i) := by
    simpa [bProfile, devProfile, hdev_play, c, ImplementationDevice.play] using heu
  rw [expect_add] at heu'
  rw [expect_add] at heu'
  have hdev_le_with_transfer :
      expect I.law
          (fun θ => G.eu (Function.update (I.play b θ) i (dev ((I.play b θ) i))) i) ≤
        expect I.law
          (fun θ =>
            G.eu (Function.update (I.play b θ) i (dev ((I.play b θ) i))) i +
              I.transfer θ
                (Function.update (I.play b θ) i (dev ((I.play b θ) i))) i) := by
    rw [expect_add]
    exact le_add_of_nonneg_right
      (expect_nonneg I.law _ fun θ =>
        I.transfer_nonneg θ
          (Function.update (I.play b θ) i (dev ((I.play b θ) i))) i)
  rw [expect_add] at hdev_le_with_transfer
  have hdev_le :
      expect I.law
          (fun θ => G.eu (Function.update (I.play b θ) i (dev ((I.play b θ) i))) i) ≤
        expect I.law (fun θ => G.eu (I.play b θ) i) +
          I.expectedRealizedTransferTo b i := by
    rw [expectedRealizedTransferTo]
    linarith
  have hμ_obey :
      G.correlatedEu μ i = expect I.law (fun θ => G.eu (I.play b θ) i) := by
    calc
      G.correlatedEu μ i = expect μ (fun σ => G.eu σ i) := by
        exact G.correlatedEu_eq_expect_eu μ i
      _ = expect (I.inducedDistribution b) (fun σ => G.eu σ i) := by
        rw [h.2]
      _ = expect I.law (fun θ => G.eu (I.play b θ) i) := by
        rw [ImplementationDevice.inducedDistribution, expect_map_fintype_target]
  have hμ_dev :
      G.correlatedEu (G.unilateralDeviationDistribution μ i dev) i =
        expect I.law
          (fun θ => G.eu (Function.update (I.play b θ) i (dev ((I.play b θ) i))) i) := by
    calc
      G.correlatedEu (G.unilateralDeviationDistribution μ i dev) i =
          expect μ (fun σ => G.eu (Function.update σ i (dev (σ i))) i) := by
            exact G.correlatedEu_unilateralDeviationDistribution_eq_expect_update μ i dev
      _ = expect (I.inducedDistribution b)
          (fun σ => G.eu (Function.update σ i (dev (σ i))) i) := by
            rw [h.2]
      _ = expect I.law
          (fun θ => G.eu (Function.update (I.play b θ) i (dev ((I.play b θ) i))) i) := by
            rw [ImplementationDevice.inducedDistribution, expect_map_fintype_target]
  rw [swapRegret, hμ_dev, hμ_obey]
  linarith

/-- Expected-cost lower bound for interim-dominant implementation: the total
expected realized transfer is at least the sum of players' maximum swap
regrets. -/
theorem sum_maxSwapRegret_le_expectedRealizedTransfer_of_interimDominant
    [Fintype ι] [Finite (∀ i, I.Signal i)] [∀ i, Finite (I.Signal i)]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, DecidableEq (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    {b : ∀ i, I.Signal i → G.Strategy i} {μ : PMF (Profile G)}
    (h : I.InterimDominantImplementsDistribution b μ) :
    ∑ i, G.maxSwapRegret μ i ≤ I.expectedRealizedTransfer b := by
  classical
  rw [I.expectedRealizedTransfer_eq_sum_to b]
  refine Finset.sum_le_sum ?_
  intro i _
  apply Finset.sup'_le
  intro dev _
  exact I.swapRegret_le_expectedRealizedTransferTo_of_interimDominant h i dev

theorem sum_maxSwapRegret_le_of_expectedKImplementation
    [Fintype ι] [Finite (∀ i, I.Signal i)] [∀ i, Finite (I.Signal i)]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, DecidableEq (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    {b : ∀ i, I.Signal i → G.Strategy i} {μ : PMF (Profile G)} {k : ℝ}
    (h : I.InterimDominantExpectedKImplementsDistribution b μ k) :
    ∑ i, G.maxSwapRegret μ i ≤ k :=
  le_trans (I.sum_maxSwapRegret_le_expectedRealizedTransfer_of_interimDominant h.1) h.2

/-- Necessity side for expected zero-cost device implementation: with finite
signals and actions, expected-cost zero implementation forces the target law to
be a correlated equilibrium. -/
theorem isCorrelatedEq_of_interimDominantExpectedKImplDist_zero
    [Fintype ι] [Finite (∀ i, I.Signal i)] [∀ i, Finite (I.Signal i)]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {b : ∀ i, I.Signal i → G.Strategy i} {μ : PMF (Profile G)}
    (h : I.InterimDominantExpectedKImplementsDistribution b μ 0) :
    G.IsCorrelatedEq μ := by
  classical
  letI : (i : ι) → Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  rw [G.isCorrelatedEq_iff_noSwapRegret]
  intro i dev
  have hsum : ∑ j, G.maxSwapRegret μ j ≤ 0 :=
    I.sum_maxSwapRegret_le_of_expectedKImplementation h
  have hmax_le_sum :
      G.maxSwapRegret μ i ≤ ∑ j, G.maxSwapRegret μ j :=
    Finset.single_le_sum
      (fun j _ => G.maxSwapRegret_nonneg μ j)
      (Finset.mem_univ i)
  exact le_trans (G.swapRegret_le_maxSwapRegret μ i dev)
    (le_trans hmax_le_sum hsum)

/-- Pointwise device implementation by an arbitrary finite-signal deterministic
device must cover every conditional swap-regret constraint of the induced
recommendation law. -/
theorem conditionalSwapRegret_le_of_interimDominantKImplDist
    [Fintype ι] [Finite (∀ i, I.Signal i)] [∀ i, Finite (I.Signal i)]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {b : ∀ i, I.Signal i → G.Strategy i} {μ : PMF (Profile G)} {k : ℝ}
    (h : I.InterimDominantKImplementsDistribution b μ k)
    (i : ι) (si : G.Strategy i) :
    G.conditionalSwapRegret μ i si ≤ k := by
  classical
  letI : Fintype (∀ j, I.Signal j) := Fintype.ofFinite (∀ j, I.Signal j)
  rw [conditionalSwapRegret]
  by_cases hsiμ : pmfMass (μ := μ) (fun θ : Profile G => si = θ i) ≠ 0
  · simp only [dif_pos hsiμ]
    apply Finset.sup'_le
    intro a _
    let bProfile : ∀ j, I.Signal j → G.Strategy j := b
    let dev : I.Signal i → G.Strategy i :=
      fun ti => if b i ti = si then a else b i ti
    let devProfile : ∀ j, I.Signal j → G.Strategy j := Function.update bProfile i dev
    let E : (∀ j, I.Signal j) → Prop := fun θ => si = (I.play b θ) i
    let gain : Profile G → ℝ := fun θ =>
      G.eu (Function.update θ i a) i - G.eu θ i
    have hinduced : I.inducedDistribution b = μ := h.1.2
    have hpush : pushforward I.law (I.play b) = μ := by
      simpa [ImplementationDevice.inducedDistribution, pushforward] using hinduced
    have hEpush :
        pmfMass (μ := pushforward I.law (I.play b))
            (fun θ : Profile G => si = θ i) ≠ 0 := by
      simpa [hpush] using hsiμ
    have hE : pmfMass (μ := I.law) E ≠ 0 := by
      simpa [E, pmfMass_pushforward] using hEpush
    have hweak : I.InterimWeaklyDominates i (b i) dev := h.1.1 i dev
    have hdom : I.deviceGame.WeaklyDominates i (b i) dev :=
      hweak.toWeaklyDominates (G := G) (I := I)
    have hraw := hdom bProfile
    have hupdate_self : Function.update bProfile i (b i) = bProfile := by
      funext j
      by_cases hji : j = i
      · subst hji
        simp [bProfile]
      · simp [bProfile, Function.update_of_ne hji]
    have heu : I.deviceGame.eu bProfile i ≥ I.deviceGame.eu devProfile i := by
      simpa [bProfile, devProfile, hupdate_self] using hraw
    rw [I.deviceGame_eu bProfile i] at heu
    rw [I.deviceGame_eu devProfile i] at heu
    have hdev_play :
        ∀ θ, I.play devProfile θ =
          if E θ then Function.update (I.play b θ) i a else I.play b θ := by
      intro θ
      by_cases hEθ : E θ
      · have hbθ : b i (θ i) = si := by
          simpa [ImplementationDevice.play] using hEθ.symm
        rw [if_pos hEθ]
        rw [I.play_update]
        funext j
        by_cases hji : j = i
        · subst hji
          simp [dev, bProfile, hbθ]
        · simp [Function.update_of_ne hji, bProfile, ImplementationDevice.play]
      · have hbθ : b i (θ i) ≠ si := by
          intro hb
          exact hEθ (by simpa [E, ImplementationDevice.play] using hb.symm)
        rw [if_neg hEθ]
        rw [I.play_update]
        funext j
        by_cases hji : j = i
        · subst hji
          simp [dev, bProfile, hbθ, ImplementationDevice.play]
        · simp [Function.update_of_ne hji, bProfile, ImplementationDevice.play]
    let F : (∀ j, I.Signal j) → ℝ := fun θ =>
      G.eu (I.play b θ) i + I.transfer θ (I.play b θ) i
    let H : (∀ j, I.Signal j) → ℝ := fun θ =>
      G.eu (I.play devProfile θ) i + I.transfer θ (I.play devProfile θ) i
    have hcond := expect_cond_le_of_expect_le_of_eq_off
      (μ := I.law) (E := E) (hE := hE) (f := F) (g := H)
      (show expect I.law H ≤ expect I.law F from by
        simpa [F, H] using heu)
      ?_
    · have hH_gain :
          expect (pmfCond (μ := I.law) E hE)
              (fun θ => G.eu (Function.update (I.play b θ) i a) i) ≤
            expect (pmfCond (μ := I.law) E hE) H := by
        calc
          expect (pmfCond (μ := I.law) E hE)
              (fun θ => G.eu (Function.update (I.play b θ) i a) i)
              ≤ expect (pmfCond (μ := I.law) E hE)
                  (fun θ => G.eu (Function.update (I.play b θ) i a) i +
                    I.transfer θ (Function.update (I.play b θ) i a) i) := by
                rw [expect_add]
                exact le_add_of_nonneg_right
                  (expect_nonneg _ _ fun θ =>
                    I.transfer_nonneg θ (Function.update (I.play b θ) i a) i)
          _ = expect (pmfCond (μ := I.law) E hE) H := by
                refine expect_congr_of_ne_zero _ _ _ ?_
                intro θ hθ
                have hEθ := pmfCond_ne_zero_implies I.law E hE hθ
                simp [H, hdev_play θ, E, hEθ]
      have hF_eq :
          expect (pmfCond (μ := I.law) E hE) F =
            expect (pmfCond (μ := I.law) E hE)
              (fun θ => G.eu (I.play b θ) i) +
            expect (pmfCond (μ := I.law) E hE)
              (fun θ => I.transfer θ (I.play b θ) i) := by
        rw [expect_add]
      have hgain_signal :
          expect (pmfCond (μ := I.law) E hE)
              (fun θ => G.eu (Function.update (I.play b θ) i a) i - G.eu (I.play b θ) i) ≤
            expect (pmfCond (μ := I.law) E hE)
              (fun θ => I.transfer θ (I.play b θ) i) := by
        rw [expect_sub]
        rw [hF_eq] at hcond
        linarith
      have hgain_push :=
        expect_pmfCond_pushforward I.law (I.play b)
          (fun θ : Profile G => si = θ i) hEpush gain
      have hgain_base :
          expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsiμ) gain =
            expect (pmfCond (μ := I.law) E hE)
              (fun θ => gain (I.play b θ)) := by
        have hpre :
            pmfMass (μ := I.law) (fun ω => si = (I.play b ω) i) ≠ 0 := by
          simpa [E] using hE
        have hgain_push' :
            expect (pmfCond (μ := pushforward I.law (I.play b))
                (fun θ : Profile G => si = θ i) hEpush) gain =
              expect (pmfCond (μ := I.law)
                (fun ω => si = (I.play b ω) i) hpre)
                (fun ω => gain (I.play b ω)) := by
          simpa [E] using hgain_push
        simpa [hpush, hpre, E] using hgain_push'
      have htransfer_le :
          expect (pmfCond (μ := I.law) E hE)
              (fun θ => I.transfer θ (I.play b θ) i) ≤ k := by
        rw [expect_eq_sum]
        calc
          (∑ θ : ∀ j, I.Signal j,
              ((pmfCond (μ := I.law) E hE) θ).toReal *
                I.transfer θ (I.play b θ) i)
              ≤ ∑ θ : ∀ j, I.Signal j,
                  ((pmfCond (μ := I.law) E hE) θ).toReal * k := by
                refine Finset.sum_le_sum ?_
                intro θ _
                by_cases hθcond : pmfCond (μ := I.law) E hE θ = 0
                · simp [hθcond]
                · have hθlaw : I.law θ ≠ 0 :=
                    ((pmfCond_ne_zero_iff I.law E hE).mp hθcond).2
                  have hi_le_sum :
                      I.transfer θ (I.play b θ) i ≤
                        ∑ j, I.transfer θ (I.play b θ) j :=
                    Finset.single_le_sum
                      (fun j _ => I.transfer_nonneg θ (I.play b θ) j)
                      (Finset.mem_univ i)
                  exact mul_le_mul_of_nonneg_left
                    (hi_le_sum.trans (h.2 θ hθlaw)) ENNReal.toReal_nonneg
          _ = k := by
                rw [← Finset.sum_mul, pmf_toReal_sum_one, one_mul]
      change expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsiμ) gain ≤
        k
      rw [hgain_base]
      exact hgain_signal.trans htransfer_le
    · intro θ hEθ
      have hplay : I.play devProfile θ = I.play b θ := by
        simp [hdev_play θ, hEθ]
      simp [F, H, hplay]
  · have hk_nonneg : 0 ≤ k := by
      rcases I.law.support_nonempty with ⟨θ, hθsupp⟩
      have hθ : I.law θ ≠ 0 := by
        simpa [PMF.mem_support_iff] using hθsupp
      have hsum_nonneg : 0 ≤ ∑ j, I.transfer θ (I.play b θ) j :=
        Finset.sum_nonneg fun j _ => I.transfer_nonneg θ (I.play b θ) j
      exact hsum_nonneg.trans (h.2 θ hθ)
    simp [hsiμ, hk_nonneg]

/-- A profile of interim dominant device strategies is a profile of ordinary
dominant strategies in the compiled device game. -/
theorem InterimDominantProfile.isDominantProfile
    [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (I.Signal i)] {b : ∀ i, I.Signal i → G.Strategy i}
    (h : I.InterimDominantProfile b) :
    ∀ i, I.deviceGame.IsDominant i (b i) :=
  fun i => (h i).isDominant (G := G) (I := I)

/-- A profile of interim dominant device strategies is dominant against mixed
deviations in the mixed extension of the compiled device game. -/
theorem InterimDominantProfile.isDominantMixedProfile
    [Fintype ι] [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ j, Finite (I.Signal j)] [∀ j, Finite (G.Strategy j)]
    {b : ∀ i, I.Signal i → G.Strategy i}
    (h : I.InterimDominantProfile b) :
    ∀ i, I.deviceGame.mixedExtension.IsDominant i (PMF.pure (b i)) :=
  fun i => (h i).isDominant_mixedExtension (G := G) (I := I)

/-- A behavioral device strategy for player `i`, represented as the induced
mixed strategy over pure signal-contingent rules. Each signal's mixed action is
sampled independently. -/
noncomputable def behaviorStrategyLaw [Fintype (I.Signal i)]
    (β : I.Signal i → PMF (G.Strategy i)) : PMF (I.deviceGame.Strategy i) :=
  Math.PMFProduct.pmfPi β

omit [DecidableEq ι] in
@[simp] theorem behaviorStrategyLaw_pure [Fintype (I.Signal i)]
    (b : I.Signal i → G.Strategy i) :
    I.behaviorStrategyLaw (G := G) (i := i) (fun si => PMF.pure (b si)) =
      PMF.pure b := by
  exact Math.PMFProduct.pmfPi_pure b

/-- Interim dominance remains dominance against behavioral deviations. This is
the paper's closing linearity remark in behavior-strategy form: a behavioral
strategy induces a mixed distribution over signal-contingent pure rules. -/
theorem InterimDominant.weaklyDominates_behaviorStrategy
    [Fintype ι] [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ j, Finite (I.Signal j)] [∀ j, Finite (G.Strategy j)]
    {i : ι} [Fintype (I.Signal i)] {b : I.Signal i → G.Strategy i}
    (h : I.InterimDominant i b)
    (β : I.Signal i → PMF (G.Strategy i)) :
    I.deviceGame.mixedExtension.WeaklyDominates i
      (PMF.pure b) (I.behaviorStrategyLaw (G := G) (i := i) β) :=
  (h.isDominant_mixedExtension (G := G) (I := I)).weaklyDominates
    (I.behaviorStrategyLaw (G := G) (i := i) β)

/-- Strict interim dominance persists against pure mixed-extension deviations
in the compiled device game. -/
theorem InterimWeaklyStrictlyDominates.toWeaklyStrictlyDominates_mixedExtension
    [Fintype ι] [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ j, Finite (I.Signal j)] [∀ j, Finite (G.Strategy j)]
    {i : ι} {b c : I.Signal i → G.Strategy i}
    (h : I.InterimWeaklyStrictlyDominates i b c) :
    I.deviceGame.mixedExtension.WeaklyStrictlyDominates i (PMF.pure b) (PMF.pure c) := by
  classical
  haveI : Finite I.deviceGame.Outcome := by
    change Finite ((∀ j, I.Signal j) × Profile G × G.Outcome)
    infer_instance
  haveI : ∀ j, Finite (I.deviceGame.Strategy j) := by
    intro j
    change Finite (I.Signal j → G.Strategy j)
    infer_instance
  haveI : Finite (Profile I.deviceGame) := by
    change Finite (∀ j, I.Signal j → G.Strategy j)
    infer_instance
  exact (h.toWeaklyStrictlyDominates (G := G) (I := I)).pure_to_mixedExtension

/-- A strictly interim-dominant device rule weakly-strictly dominates every
distinct mixed rule in the mixed extension of the compiled device game. -/
theorem InterimWeaklyStrictlyDominant.toWeaklyStrictlyDominates_mixedExtension
    [Fintype ι] [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ j, Finite (I.Signal j)] [∀ j, Finite (G.Strategy j)]
    {i : ι} {b : I.Signal i → G.Strategy i}
    (h : I.InterimWeaklyStrictlyDominant i b)
    {τ : PMF (I.deviceGame.Strategy i)} (hτ : τ ≠ PMF.pure b) :
    I.deviceGame.mixedExtension.WeaklyStrictlyDominates i (PMF.pure b) τ := by
  classical
  haveI : Finite I.deviceGame.Outcome := by
    change Finite ((∀ j, I.Signal j) × Profile G × G.Outcome)
    infer_instance
  haveI : ∀ j, Finite (I.deviceGame.Strategy j) := by
    intro j
    change Finite (I.Signal j → G.Strategy j)
    infer_instance
  haveI : Finite (Profile I.deviceGame) := by
    change Finite (∀ j, I.Signal j → G.Strategy j)
    infer_instance
  exact forall_weaklyStrictlyDominates_pure_to_mixedExtension
    (G := I.deviceGame) (who := i) (s := b)
    (fun c hc => (h c hc).toWeaklyStrictlyDominates (G := G) (I := I)) hτ

/-- Profile form of strict interim dominance against mixed deviations. -/
theorem InterimWeaklyStrictlyDominantProfile.toWeaklyStrictlyDominates_mixedExtension
    [Fintype ι] [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ j, Finite (I.Signal j)] [∀ j, Finite (G.Strategy j)]
    {b : ∀ i, I.Signal i → G.Strategy i}
    (h : I.InterimWeaklyStrictlyDominantProfile b) :
    ∀ i (τ : PMF (I.deviceGame.Strategy i)), τ ≠ PMF.pure (b i) →
      I.deviceGame.mixedExtension.WeaklyStrictlyDominates i (PMF.pure (b i)) τ :=
  fun i τ hτ =>
    (h i).toWeaklyStrictlyDominates_mixedExtension (G := G) (I := I) (τ := τ) hτ

/-- Strict interim dominance remains strict dominance against every behavioral
deviation whose induced mixed rule is not concentrated on the target pure rule. -/
theorem InterimWeaklyStrictlyDominant.weaklyStrictlyDominates_behaviorStrategy
    [Fintype ι] [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ j, Finite (I.Signal j)] [∀ j, Finite (G.Strategy j)]
    {i : ι} [Fintype (I.Signal i)] {b : I.Signal i → G.Strategy i}
    (h : I.InterimWeaklyStrictlyDominant i b)
    (β : I.Signal i → PMF (G.Strategy i))
    (hβ : I.behaviorStrategyLaw (G := G) (i := i) β ≠ PMF.pure b) :
    I.deviceGame.mixedExtension.WeaklyStrictlyDominates i
      (PMF.pure b) (I.behaviorStrategyLaw (G := G) (i := i) β) :=
  h.toWeaklyStrictlyDominates_mixedExtension (G := G) (I := I) hβ

/-- Profile form of strict dominance against behavioral deviations. -/
theorem InterimWeaklyStrictlyDominantProfile.weaklyStrictlyDominates_behaviorStrategy
    [Fintype ι] [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ j, Fintype (I.Signal j)] [∀ j, Finite (I.Signal j)] [∀ j, Finite (G.Strategy j)]
    {b : ∀ i, I.Signal i → G.Strategy i}
    (h : I.InterimWeaklyStrictlyDominantProfile b) :
    ∀ i (β : I.Signal i → PMF (G.Strategy i)),
      I.behaviorStrategyLaw (G := G) (i := i) β ≠ PMF.pure (b i) →
        I.deviceGame.mixedExtension.WeaklyStrictlyDominates i
          (PMF.pure (b i)) (I.behaviorStrategyLaw (G := G) (i := i) β) :=
  fun i β hβ =>
    (h i).weaklyStrictlyDominates_behaviorStrategy (G := G) (I := I) β hβ

/-- Interim dominant device behavior is undominated in the compiled device game. -/
theorem InterimDominantProfile.mem_undominatedProfiles
    [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (I.Signal i)] {b : ∀ i, I.Signal i → G.Strategy i}
    (h : I.InterimDominantProfile b) :
    b ∈ I.deviceGame.undominatedProfiles := by
  intro i
  exact (h.isDominantProfile (G := G) (I := I) i).isUndominated

/-- If a device behavior profile is interim dominant, then the undominated
profiles of the compiled device game are exactly the product of the ordinary
utility-equivalence classes of its signal-contingent strategies. -/
theorem InterimDominantProfile.undominatedProfiles_eq_utilityEquivalentClass
    [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (I.Signal i)] {b : ∀ i, I.Signal i → G.Strategy i}
    (h : I.InterimDominantProfile b) :
    I.deviceGame.undominatedProfiles =
      {c : Profile I.deviceGame |
        ∀ i, I.deviceGame.UtilityEquivalent i (c i) (b i)} :=
  I.deviceGame.undominatedProfiles_eq_utilityEquivalentClass_of_forall_weaklyDominates
    (fun i c => (h.isDominantProfile (G := G) (I := I) i).weaklyDominates c)

/-- Under interim dominance, the compiled device game's undominated profiles
collapse to the obedient profile exactly when each signal-contingent
utility-equivalence class is trivial. -/
theorem InterimDominantProfile.undominatedProfiles_eq_singleton_iff
    [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (I.Signal i)] {b : ∀ i, I.Signal i → G.Strategy i}
    (h : I.InterimDominantProfile b) :
    I.deviceGame.undominatedProfiles =
        ({b} : Set (Profile I.deviceGame)) ↔
      ∀ i (c : I.deviceGame.Strategy i),
        I.deviceGame.UtilityEquivalent i c (b i) → c = b i :=
  I.deviceGame.undominatedProfiles_eq_singleton_iff_utilityEquivalent_eq
    (fun i c => (h.isDominantProfile (G := G) (I := I) i).weaklyDominates c)

/-- A profile of interim dominant device strategies is a Nash equilibrium of
the compiled device game. -/
theorem InterimDominantProfile.isNash
    [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (I.Signal i)] (b : ∀ i, I.Signal i → G.Strategy i)
    (h : I.InterimDominantProfile b) :
    I.deviceGame.IsNash b :=
  I.deviceGame.dominant_is_nash b h.isDominantProfile

/-- In the compiled device game, a signal-contingent rule only matters on
positive-probability own signals.  Rules that agree there are utility
equivalent, regardless of what they do at null signals. -/
theorem deviceGame_utilityEquivalent_of_eq_on_positive_signals
    [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    {i : ι} {b c : I.Signal i → G.Strategy i}
    (hbc : ∀ si, I.PositiveSignal i si → b si = c si) :
    I.deviceGame.UtilityEquivalent i b c := by
  intro β
  rw [I.deviceGame_eu, I.deviceGame_eu]
  refine expect_congr_of_ne_zero I.law _ _ ?_
  intro θ hθ
  have hpos : I.PositiveSignal i (θ i) :=
    pmfMass_ne_zero_of_mem_ne_zero I.law (a := θ) rfl hθ
  have hplay :
      I.play (Function.update β i b) θ =
        I.play (Function.update β i c) θ := by
    rw [I.play_update, I.play_update, hbc (θ i) hpos]
  simp [hplay]

/-- Transfer-class version of
`deviceGame_utilityEquivalent_of_eq_on_positive_signals` for the zero
profile-observed implementation transfer. -/
theorem deviceGame_zeroTransferClassUtilityEquivalent_of_eq_on_positive_signals
    [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    {i : ι} {b c : I.Signal i → G.Strategy i}
    (hbc : ∀ si, I.PositiveSignal i si → b si = c si) :
    I.deviceGame.TransferClassUtilityEquivalent
      ({fun _ _ => 0} : Set (Profile I.deviceGame → Payoff ι)) i b c := by
  intro V hV
  have hVzero : V = fun _ _ => 0 := Set.mem_singleton_iff.mp hV
  subst V
  intro β
  haveI : Finite I.deviceGame.Outcome := by
    change Finite ((∀ j, I.Signal j) × Profile G × G.Outcome)
    infer_instance
  let β0 : Profile I.deviceGame := β
  change
    (I.deviceGame.subsidize (fun _ _ => 0)).eu (Function.update β0 i b) i =
      (I.deviceGame.subsidize (fun _ _ => 0)).eu (Function.update β0 i c) i
  rw [KernelGame.subsidize_zero_eu, KernelGame.subsidize_zero_eu]
  exact I.deviceGame_utilityEquivalent_of_eq_on_positive_signals hbc β0

end InterimDominance

end ImplementationDevice

/-- Expected-cost implementation budgets over finite-signal devices. This is
the ex-ante analogue of the paper's pointwise device budget. -/
def finiteExpectedDeviceImplementationCosts (G : KernelGame ι) [DecidableEq ι] [Fintype ι]
    (μ : PMF (Profile G)) : Set ℝ :=
  {k | ∃ (I : G.ImplementationDevice)
      (b : ∀ i, I.Signal i → G.Strategy i),
    Finite (∀ i, I.Signal i) ∧
      (∀ i, Finite (I.Signal i)) ∧
        I.InterimDominantExpectedKImplementsDistribution b μ k}

/-- Infimum expected implementation cost over finite-signal devices. -/
noncomputable def finiteExpectedDeviceImplPrice (G : KernelGame ι) [DecidableEq ι] [Fintype ι]
    (μ : PMF (Profile G)) : ℝ :=
  sInf (G.finiteExpectedDeviceImplementationCosts μ)

theorem finiteExpectedDeviceImplementationCosts_bddBelow
    (G : KernelGame ι) [DecidableEq ι] [Fintype ι] (μ : PMF (Profile G)) :
    BddBelow (G.finiteExpectedDeviceImplementationCosts μ) := by
  refine ⟨0, ?_⟩
  intro k hk
  rcases hk with ⟨I, b, _hSig, _hEach, hK⟩
  exact (I.expectedRealizedTransfer_nonneg b).trans hK.2

/-- Pointwise implementation budgets over arbitrary finite-signal devices. This
is the paper-facing budget convention, but with no restriction that signals are
the recommended base-game actions. -/
def finitePointwiseDeviceImplementationCosts (G : KernelGame ι) [DecidableEq ι]
    [Fintype ι] (μ : PMF (Profile G)) : Set ℝ :=
  {k | ∃ (I : G.ImplementationDevice)
      (b : ∀ i, I.Signal i → G.Strategy i),
    Finite (∀ i, I.Signal i) ∧
      (∀ i, Finite (I.Signal i)) ∧
        I.InterimDominantKImplementsDistribution b μ k}

/-- Infimum pointwise implementation cost over arbitrary finite-signal
devices. -/
noncomputable def finitePointwiseDeviceImplPrice (G : KernelGame ι)
    [DecidableEq ι] [Fintype ι] (μ : PMF (Profile G)) : ℝ :=
  sInf (G.finitePointwiseDeviceImplementationCosts μ)

theorem finitePointwiseDeviceImplementationCosts_bddBelow
    (G : KernelGame ι) [DecidableEq ι] [Fintype ι] (μ : PMF (Profile G)) :
    BddBelow (G.finitePointwiseDeviceImplementationCosts μ) := by
  refine ⟨0, ?_⟩
  intro k hk
  rcases hk with ⟨I, b, _hSig, _hEach, hK⟩
  rcases I.law.support_nonempty with ⟨θ, hθsupp⟩
  have hθ : I.law θ ≠ 0 := by
    simpa [PMF.mem_support_iff] using hθsupp
  have hsum_nonneg : 0 ≤ ∑ i, I.transfer θ (I.play b θ) i :=
    Finset.sum_nonneg fun i _ => I.transfer_nonneg θ (I.play b θ) i
  exact hsum_nonneg.trans (hK.2 θ hθ)

/-- `M` bounds each player's expected-utility range over pure profiles. This is
the device theorem's natural hypothesis: if payoffs lie in an interval of length
`M`, then any one player's payoff loss from changing profiles is at most `M`. -/
def EuDiameterBound (G : KernelGame ι) (M : ℝ) : Prop :=
  ∀ i (σ τ : Profile G), G.eu σ i - G.eu τ i ≤ M

/-- A concrete finite payoff-diameter bound, useful when a theorem only needs
some obedience bonus large enough to dominate base-game payoff changes. -/
noncomputable def euDiameterSum (G : KernelGame ι) [Fintype ι] [Fintype (Profile G)] :
    ℝ :=
  ∑ i, ∑ σ : Profile G, ∑ τ : Profile G, |G.eu σ i - G.eu τ i|

theorem euDiameterBound_sum (G : KernelGame ι) [Fintype ι] [Fintype (Profile G)] :
    G.EuDiameterBound G.euDiameterSum := by
  classical
  intro i σ τ
  have h_abs : G.eu σ i - G.eu τ i ≤ |G.eu σ i - G.eu τ i| := le_abs_self _
  have hτ :
      |G.eu σ i - G.eu τ i| ≤
        ∑ τ' : Profile G, |G.eu σ i - G.eu τ' i| := by
    exact Finset.single_le_sum
      (fun τ' _ => show 0 ≤ |G.eu σ i - G.eu τ' i| from abs_nonneg _)
      (Finset.mem_univ τ)
  have hσ :
      (∑ τ' : Profile G, |G.eu σ i - G.eu τ' i|) ≤
        ∑ σ' : Profile G, ∑ τ' : Profile G, |G.eu σ' i - G.eu τ' i| := by
    exact Finset.single_le_sum
      (fun σ' _ => Finset.sum_nonneg fun τ' _ =>
        show 0 ≤ |G.eu σ' i - G.eu τ' i| from abs_nonneg _)
      (Finset.mem_univ σ)
  have hi :
      (∑ σ' : Profile G, ∑ τ' : Profile G, |G.eu σ' i - G.eu τ' i|) ≤
        ∑ i, ∑ σ' : Profile G, ∑ τ' : Profile G, |G.eu σ' i - G.eu τ' i| := by
    exact Finset.single_le_sum
      (fun i' _ => Finset.sum_nonneg fun σ' _ =>
        Finset.sum_nonneg fun τ' _ =>
          show 0 ≤ |G.eu σ' i' - G.eu τ' i'| from abs_nonneg _)
      (Finset.mem_univ i)
  exact h_abs.trans (hτ.trans (hσ.trans hi))

section RecommendationDevice

variable (G : KernelGame ι)

/-- The obedient device strategy: play the recommended action. -/
def obedientDeviceStrategy : ∀ i, G.Strategy i → G.Strategy i :=
  fun _ s => s

/-- Paper-style obedience bonus: player `i` is paid `B` exactly when `i`
follows the recommendation and some other player does not. -/
noncomputable def recommendationTransfer (B : ℝ) :
    Profile G → Profile G → Payoff ι :=
  open Classical in
  fun θ σ i =>
    if σ i = θ i ∧ ∃ j : ι, j ≠ i ∧ σ j ≠ θ j then B else 0

@[simp] theorem recommendationTransfer_obedient (B : ℝ) (θ : Profile G) (i : ι) :
    G.recommendationTransfer B θ θ i = 0 := by
  classical
  unfold recommendationTransfer
  simp

@[simp] theorem recommendationTransfer_update_obedient_self [DecidableEq ι]
    (B : ℝ) (θ : Profile G) (i : ι) (c : G.Strategy i) :
    G.recommendationTransfer B θ (Function.update θ i c) i = 0 := by
  classical
  unfold recommendationTransfer
  by_cases hic : c = θ i
  · have hno_other :
        ¬ ∃ j : ι, j ≠ i ∧ Function.update θ i c j ≠ θ j := by
      rintro ⟨j, hji, hj⟩
      simp [Function.update_of_ne hji] at hj
    simp [hic]
  · simp [hic]

open Classical in
@[simp] theorem recommendationTransfer_update_self [DecidableEq ι]
    (B : ℝ) (θ σ : Profile G) (i : ι) (a : G.Strategy i) :
    G.recommendationTransfer B θ (Function.update σ i a) i =
      if a = θ i ∧ ∃ j : ι, j ≠ i ∧ σ j ≠ θ j then B else 0 := by
  classical
  unfold recommendationTransfer
  have hiff :
      (Function.update σ i a i = θ i ∧
          ∃ j : ι, j ≠ i ∧ Function.update σ i a j ≠ θ j) ↔
        (a = θ i ∧ ∃ j : ι, j ≠ i ∧ σ j ≠ θ j) := by
    constructor
    · rintro ⟨ha, hothers⟩
      refine ⟨by simpa using ha, ?_⟩
      rcases hothers with ⟨j, hji, hj⟩
      exact ⟨j, hji, by simpa [Function.update_of_ne hji] using hj⟩
    · rintro ⟨ha, hothers⟩
      refine ⟨by simp [ha], ?_⟩
      rcases hothers with ⟨j, hji, hj⟩
      exact ⟨j, hji, by simpa [Function.update_of_ne hji] using hj⟩
  by_cases h : a = θ i ∧ ∃ j : ι, j ≠ i ∧ σ j ≠ θ j
  · have h' := hiff.mpr h
    rw [if_pos h', if_pos h]
  · have h' :
        ¬ (Function.update σ i a i = θ i ∧
          ∃ j : ι, j ≠ i ∧ Function.update σ i a j ≠ θ j) := by
      intro hu
      exact h (hiff.mp hu)
    rw [if_neg h', if_neg h]

/-- Recommendation-device transfer that pays the conditional swap-regret price
when a player obeys, plus the usual off-path obedience bonus.  The conditional
payment is on path and is the expected-cost part; the bonus is off path and is
only used to make obedience robust to opponents' signal-contingent deviations. -/
noncomputable def regretRecommendationTransfer [DecidableEq ι]
    (μ : PMF (Profile G)) (B : ℝ)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] :
    Profile G → Profile G → Payoff ι := by
  classical
  exact fun θ σ i =>
    (if σ i = θ i then G.conditionalSwapRegret μ i (θ i) else 0) +
      G.recommendationTransfer B θ σ i

theorem regretRecommendationTransfer_nonneg [DecidableEq ι]
    (μ : PMF (Profile G)) {B : ℝ} (hB : 0 ≤ B)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (θ σ : Profile G) (i : ι) :
    0 ≤ G.regretRecommendationTransfer μ B θ σ i := by
  classical
  unfold regretRecommendationTransfer recommendationTransfer
  apply add_nonneg
  · by_cases h : σ i = θ i
    · rw [if_pos h]
      exact G.conditionalSwapRegret_nonneg μ i (θ i)
    · rw [if_neg h]
  · by_cases h : σ i = θ i ∧ ∃ j : ι, j ≠ i ∧ σ j ≠ θ j
    · simp [h, hB]
    · simp [h]

/-- On-path payments for the exact pointwise recommendation-device LP.  The
variables are nonnegative payments `p θ i` made when the recommendation profile
`θ` is obeyed.  The incentive constraints require the conditional expected
payment after each own recommendation to cover every constant deviation from
that recommendation, and the budget constraint is pointwise on every supported
recommendation profile. -/
def RecommendationPaymentFeasible [DecidableEq ι] [Fintype ι]
    (μ : PMF (Profile G)) (p : Profile G → Payoff ι) (k : ℝ) : Prop :=
  (∀ θ i, 0 ≤ p θ i) ∧
    (∀ θ, μ θ ≠ 0 → ∑ i, p θ i ≤ k) ∧
      ∀ (i : ι) (si : G.Strategy i)
        (hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ i) ≠ 0)
        (a : G.Strategy i),
        expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsi)
            (fun θ => G.eu (Function.update θ i a) i - G.eu θ i) ≤
          expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsi)
            (fun θ => p θ i)

/-- Feasible pointwise budgets for the exact on-path-payment LP associated to
recommendation devices. -/
def recommendationPaymentImplementationCosts [DecidableEq ι] [Fintype ι]
    (μ : PMF (Profile G)) : Set ℝ :=
  {k | ∃ p : Profile G → Payoff ι, G.RecommendationPaymentFeasible μ p k}

/-- Infimum of the exact on-path-payment LP for recommendation devices. -/
noncomputable def recommendationPaymentImplPrice [DecidableEq ι] [Fintype ι]
    (μ : PMF (Profile G)) : ℝ :=
  sInf (G.recommendationPaymentImplementationCosts μ)

theorem recommendationPaymentImplementationCosts_bddBelow [DecidableEq ι] [Fintype ι]
    (μ : PMF (Profile G)) :
    BddBelow (G.recommendationPaymentImplementationCosts μ) := by
  classical
  refine ⟨0, ?_⟩
  intro k hk
  rcases hk with ⟨p, hp⟩
  rcases μ.support_nonempty with ⟨θ, hθsupp⟩
  have hθ : μ θ ≠ 0 := by
    simpa [PMF.mem_support_iff] using hθsupp
  have hsum_nonneg : 0 ≤ ∑ i, p θ i :=
    Finset.sum_nonneg fun i _ => hp.1 θ i
  exact hsum_nonneg.trans (hp.2.1 θ hθ)

theorem recommendationPaymentImplPrice_le_of_mem [DecidableEq ι] [Fintype ι]
    {μ : PMF (Profile G)} {k : ℝ}
    (hk : k ∈ G.recommendationPaymentImplementationCosts μ) :
    G.recommendationPaymentImplPrice μ ≤ k :=
  csInf_le (G.recommendationPaymentImplementationCosts_bddBelow μ) hk

theorem le_recommendationPaymentImplPrice_of_forall_le [DecidableEq ι] [Fintype ι]
    {μ : PMF (Profile G)} {L : ℝ}
    (hne : (G.recommendationPaymentImplementationCosts μ).Nonempty)
    (h : ∀ k, k ∈ G.recommendationPaymentImplementationCosts μ → L ≤ k) :
    L ≤ G.recommendationPaymentImplPrice μ := by
  rw [recommendationPaymentImplPrice]
  exact le_csInf hne h

namespace ImplementationDevice

/-- Pool an arbitrary device's on-path realized transfers by the base-game
recommendation profile they induce.  This is the payment schedule used by the
revelation-principle direction from arbitrary finite devices to recommendation
devices. -/
noncomputable def pooledRecommendationPayment
    (I : G.ImplementationDevice) [Finite (∀ j, I.Signal j)]
    (b : ∀ i, I.Signal i → G.Strategy i) : Profile G → Payoff ι :=
  fun θ i =>
    if hθ : pmfMass (μ := I.law) (fun s => I.play b s = θ) ≠ 0 then
      expect (pmfCond (μ := I.law) (fun s => I.play b s = θ) hθ)
        (fun s => I.transfer s (I.play b s) i)
    else 0

theorem pooledRecommendationPayment_nonneg
    (I : G.ImplementationDevice) [Finite (∀ j, I.Signal j)]
    (b : ∀ i, I.Signal i → G.Strategy i) (θ : Profile G) (i : ι) :
    0 ≤ ImplementationDevice.pooledRecommendationPayment (G := G) I b θ i := by
  classical
  unfold pooledRecommendationPayment
  by_cases hθ : pmfMass (μ := I.law) (fun s => I.play b s = θ) ≠ 0
  · simp only [dif_pos hθ]
    exact expect_nonneg _ _ fun s => I.transfer_nonneg s (I.play b s) i
  · simp [hθ]

/-- Conditional payoff gains from a constant action deviation are bounded by
the conditional expected on-path transfer whenever `b` is interim dominant. -/
theorem conditionalDeviationGain_le_expectedTransfer_of_interimDominantProfile
    (I : G.ImplementationDevice)
    [DecidableEq ι] [Finite (∀ j, I.Signal j)] [Finite (Profile G)] [Finite G.Outcome]
    [∀ j, Finite (I.Signal j)]
    {b : ∀ i, I.Signal i → G.Strategy i}
    (h : I.InterimDominantProfile b) (i : ι) (si : G.Strategy i)
    (hE : pmfMass (μ := I.law) (fun θ => si = (I.play b θ) i) ≠ 0)
    (a : G.Strategy i) :
    expect (pmfCond (μ := I.law) (fun θ => si = (I.play b θ) i) hE)
        (fun θ => G.eu (Function.update (I.play b θ) i a) i -
          G.eu (I.play b θ) i) ≤
      expect (pmfCond (μ := I.law) (fun θ => si = (I.play b θ) i) hE)
        (fun θ => I.transfer θ (I.play b θ) i) := by
  classical
  let bProfile : ∀ j, I.Signal j → G.Strategy j := b
  let dev : I.Signal i → G.Strategy i :=
    fun ti => if b i ti = si then a else b i ti
  let devProfile : ∀ j, I.Signal j → G.Strategy j := Function.update bProfile i dev
  let E : (∀ j, I.Signal j) → Prop := fun θ => si = (I.play b θ) i
  have hweak : I.InterimWeaklyDominates i (b i) dev := h i dev
  have hdom : I.deviceGame.WeaklyDominates i (b i) dev :=
    hweak.toWeaklyDominates (G := G) (I := I)
  have hraw := hdom bProfile
  have hupdate_self : Function.update bProfile i (b i) = bProfile := by
    funext j
    by_cases hji : j = i
    · subst hji
      simp [bProfile]
    · simp [bProfile, Function.update_of_ne hji]
  have heu : I.deviceGame.eu bProfile i ≥ I.deviceGame.eu devProfile i := by
    simpa [bProfile, devProfile, hupdate_self] using hraw
  rw [I.deviceGame_eu bProfile i] at heu
  rw [I.deviceGame_eu devProfile i] at heu
  have hdev_play :
      ∀ θ, I.play devProfile θ =
        if E θ then Function.update (I.play b θ) i a else I.play b θ := by
    intro θ
    by_cases hEθ : E θ
    · have hbθ : b i (θ i) = si := by
        simpa [ImplementationDevice.play] using hEθ.symm
      rw [if_pos hEθ]
      rw [I.play_update]
      funext j
      by_cases hji : j = i
      · subst hji
        simp [dev, bProfile, hbθ]
      · simp [Function.update_of_ne hji, bProfile, ImplementationDevice.play]
    · have hbθ : b i (θ i) ≠ si := by
        intro hb
        exact hEθ (by simpa [E, ImplementationDevice.play] using hb.symm)
      rw [if_neg hEθ]
      rw [I.play_update]
      funext j
      by_cases hji : j = i
      · subst hji
        simp [dev, bProfile, hbθ, ImplementationDevice.play]
      · simp [Function.update_of_ne hji, bProfile, ImplementationDevice.play]
  let F : (∀ j, I.Signal j) → ℝ := fun θ =>
    G.eu (I.play b θ) i + I.transfer θ (I.play b θ) i
  let H : (∀ j, I.Signal j) → ℝ := fun θ =>
    G.eu (I.play devProfile θ) i + I.transfer θ (I.play devProfile θ) i
  have hcond := expect_cond_le_of_expect_le_of_eq_off
    (μ := I.law) (E := E) (hE := by simpa [E] using hE) (f := F) (g := H)
    (show expect I.law H ≤ expect I.law F from by
      simpa [F, H] using heu)
    ?_
  · have hH_gain :
        expect (pmfCond (μ := I.law) E (by simpa [E] using hE))
            (fun θ => G.eu (Function.update (I.play b θ) i a) i) ≤
          expect (pmfCond (μ := I.law) E (by simpa [E] using hE)) H := by
      calc
        expect (pmfCond (μ := I.law) E (by simpa [E] using hE))
            (fun θ => G.eu (Function.update (I.play b θ) i a) i)
            ≤ expect (pmfCond (μ := I.law) E (by simpa [E] using hE))
                (fun θ => G.eu (Function.update (I.play b θ) i a) i +
                  I.transfer θ (Function.update (I.play b θ) i a) i) := by
              rw [expect_add]
              exact le_add_of_nonneg_right
                (expect_nonneg _ _ fun θ =>
                  I.transfer_nonneg θ (Function.update (I.play b θ) i a) i)
        _ = expect (pmfCond (μ := I.law) E (by simpa [E] using hE)) H := by
              refine expect_congr_of_ne_zero _ _ _ ?_
              intro θ hθ
              have hEθ := pmfCond_ne_zero_implies I.law E (by simpa [E] using hE) hθ
              simp [H, hdev_play θ, E, hEθ]
    have hF_eq :
        expect (pmfCond (μ := I.law) E (by simpa [E] using hE)) F =
          expect (pmfCond (μ := I.law) E (by simpa [E] using hE))
            (fun θ => G.eu (I.play b θ) i) +
          expect (pmfCond (μ := I.law) E (by simpa [E] using hE))
            (fun θ => I.transfer θ (I.play b θ) i) := by
      rw [expect_add]
    have hgain_signal :
        expect (pmfCond (μ := I.law) E (by simpa [E] using hE))
            (fun θ => G.eu (Function.update (I.play b θ) i a) i -
              G.eu (I.play b θ) i) ≤
          expect (pmfCond (μ := I.law) E (by simpa [E] using hE))
            (fun θ => I.transfer θ (I.play b θ) i) := by
      rw [expect_sub]
      rw [hF_eq] at hcond
      linarith
    simpa [E] using hgain_signal
  · intro θ hEθ
    have hplay : I.play devProfile θ = I.play b θ := by
      simp [hdev_play θ, hEθ]
    simp [F, H, hplay]

/-- Pooling a finite device's realized transfers by the induced recommendation
profile yields a feasible recommendation-payment schedule with the same
pointwise budget. -/
theorem pooledRecommendationPayment_feasible_of_interimDominantKImplDist
    (I : G.ImplementationDevice)
    [DecidableEq ι] [Fintype ι] [Finite (∀ j, I.Signal j)] [Finite (Profile G)]
    [Finite G.Outcome] [∀ j, Finite (I.Signal j)]
    {b : ∀ i, I.Signal i → G.Strategy i} {μ : PMF (Profile G)} {k : ℝ}
    (h : I.InterimDominantKImplementsDistribution b μ k) :
    G.RecommendationPaymentFeasible μ
      (ImplementationDevice.pooledRecommendationPayment (G := G) I b) k := by
  classical
  letI : Fintype (∀ j, I.Signal j) := Fintype.ofFinite (∀ j, I.Signal j)
  letI : Fintype (Profile G) := Fintype.ofFinite (Profile G)
  let p : Profile G → Payoff ι :=
    ImplementationDevice.pooledRecommendationPayment (G := G) I b
  have hinduced : I.inducedDistribution b = μ := h.1.2
  have hpush : pushforward I.law (I.play b) = μ := by
    simpa [ImplementationDevice.inducedDistribution, pushforward] using hinduced
  refine ⟨?_, ?_, ?_⟩
  · intro θ i
    exact ImplementationDevice.pooledRecommendationPayment_nonneg (G := G) I b θ i
  · intro θ hθμ
    have hθpush : (pushforward I.law (I.play b)) θ ≠ 0 := by
      simpa [hpush] using hθμ
    have hθfiber : pmfMass (μ := I.law) (fun s => I.play b s = θ) ≠ 0 := by
      simpa [pushforward_apply_eq_pmfMass] using hθpush
    let condLaw : PMF (∀ j, I.Signal j) :=
      pmfCond (μ := I.law) (fun s => I.play b s = θ) hθfiber
    have hbudget_cond :
        expect condLaw (fun s => ∑ i, I.transfer s (I.play b s) i) ≤ k := by
      rw [expect_eq_sum]
      calc
        (∑ s : ∀ j, I.Signal j,
            (condLaw s).toReal * ∑ i, I.transfer s (I.play b s) i)
            ≤ ∑ s : ∀ j, I.Signal j, (condLaw s).toReal * k := by
              refine Finset.sum_le_sum ?_
              intro s _
              by_cases hs : condLaw s = 0
              · simp [hs]
              · have hslaw : I.law s ≠ 0 :=
                  ((pmfCond_ne_zero_iff I.law (fun s => I.play b s = θ)
                    hθfiber).mp hs).2
                exact mul_le_mul_of_nonneg_left (h.2 s hslaw) ENNReal.toReal_nonneg
        _ = k := by
              rw [← Finset.sum_mul, pmf_toReal_sum_one, one_mul]
    calc
      (∑ i, p θ i)
          = ∑ i, expect condLaw (fun s => I.transfer s (I.play b s) i) := by
            simp [p, pooledRecommendationPayment, condLaw, hθfiber]
      _ = expect condLaw (fun s => ∑ i, I.transfer s (I.play b s) i) := by
            exact expect_sum_comm condLaw (fun i s => I.transfer s (I.play b s) i)
      _ ≤ k := hbudget_cond
  · intro i si hsiμ a
    let Eμ : Profile G → Prop := fun θ => si = θ i
    let E : (∀ j, I.Signal j) → Prop := fun θ => si = (I.play b θ) i
    have hEpush :
        pmfMass (μ := pushforward I.law (I.play b)) Eμ ≠ 0 := by
      simpa [hpush, Eμ] using hsiμ
    have hE : pmfMass (μ := I.law) E ≠ 0 := by
      simpa [E, Eμ, pmfMass_pushforward] using hEpush
    let gain : Profile G → ℝ := fun θ =>
      G.eu (Function.update θ i a) i - G.eu θ i
    let paySignal : (∀ j, I.Signal j) → ℝ := fun θ =>
      I.transfer θ (I.play b θ) i
    have hgain_signal :
        expect (pmfCond (μ := I.law) E hE) (fun θ => gain (I.play b θ)) ≤
          expect (pmfCond (μ := I.law) E hE) paySignal := by
      simpa [gain, paySignal, E] using
        ImplementationDevice.conditionalDeviationGain_le_expectedTransfer_of_interimDominantProfile
          (G := G) I
          h.1.1 i si hE a
    have hgain_push :=
      expect_pmfCond_pushforward I.law (I.play b) Eμ hEpush gain
    have hgain_base :
        expect (pmfCond (μ := μ) Eμ hsiμ) gain =
          expect (pmfCond (μ := I.law) E hE) (fun θ => gain (I.play b θ)) := by
      have hgain_push' :
          expect (pmfCond (μ := pushforward I.law (I.play b)) Eμ hEpush) gain =
            expect (pmfCond (μ := I.law) E hE) (fun θ => gain (I.play b θ)) := by
        simpa [E, Eμ] using hgain_push
      simpa [hpush, Eμ] using hgain_push'
    have hpay_push :=
      expect_pmfCond_pushforward_fiberCond I.law (I.play b) Eμ hEpush paySignal
    have hpay_base :
        expect (pmfCond (μ := μ) Eμ hsiμ) (fun θ => p θ i) =
          expect (pmfCond (μ := I.law) E hE) paySignal := by
      have hpay_push' :
          expect (pmfCond (μ := pushforward I.law (I.play b)) Eμ hEpush)
              (fun θ => p θ i) =
            expect (pmfCond (μ := I.law) E hE) paySignal := by
        simpa [p, pooledRecommendationPayment, E, Eμ, paySignal] using hpay_push
      simpa [hpush, Eμ] using hpay_push'
    change expect (pmfCond (μ := μ) Eμ hsiμ) gain ≤
      expect (pmfCond (μ := μ) Eμ hsiμ) (fun θ => p θ i)
    rw [hgain_base, hpay_base]
    exact hgain_signal

end ImplementationDevice

/-- The conditional gain in one recommendation-payment incentive constraint. -/
noncomputable def recommendationPaymentIncentiveGain [DecidableEq ι]
    (μ : PMF (Profile G)) (i : ι) (si a : G.Strategy i) : ℝ :=
  if hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ i) ≠ 0 then
    expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsi)
      (fun θ => G.eu (Function.update θ i a) i - G.eu θ i)
  else 0

/-- Coefficient of an on-path payment variable in one recommendation-payment
incentive constraint. -/
noncomputable def recommendationPaymentIncentiveCoeff [DecidableEq ι]
    (μ : PMF (Profile G)) (i : ι) (si _a : G.Strategy i) (θ : Profile G) : ℝ :=
  if hsi : pmfMass (μ := μ) (fun ω : Profile G => si = ω i) ≠ 0 then
    ((pmfCond (μ := μ) (fun ω : Profile G => si = ω i) hsi) θ).toReal
  else 0

theorem recommendationPaymentIncentiveGain_le_weighted_payment
    [DecidableEq ι] [Fintype ι] [Fintype (Profile G)] {μ : PMF (Profile G)}
    {p : Profile G → Payoff ι} {k : ℝ}
    (hp : G.RecommendationPaymentFeasible μ p k)
    (i : ι) (si a : G.Strategy i) :
    G.recommendationPaymentIncentiveGain μ i si a ≤
      ∑ θ : Profile G, G.recommendationPaymentIncentiveCoeff μ i si a θ * p θ i := by
  classical
  rw [recommendationPaymentIncentiveGain]
  by_cases hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ i) ≠ 0
  · simp only [dif_pos hsi]
    calc
      expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsi)
          (fun θ => G.eu (Function.update θ i a) i - G.eu θ i)
          ≤ expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsi)
              (fun θ => p θ i) := hp.2.2 i si hsi a
      _ = ∑ θ : Profile G,
          ((pmfCond (μ := μ) (fun ω : Profile G => si = ω i) hsi) θ).toReal *
            p θ i := by
            rw [expect_eq_sum]
      _ = ∑ θ : Profile G, G.recommendationPaymentIncentiveCoeff μ i si a θ * p θ i := by
            simp [recommendationPaymentIncentiveCoeff, hsi]
  · simp [hsi, recommendationPaymentIncentiveCoeff]

/-- A semantic weighted certificate for lower bounds on the pointwise
recommendation-payment price.  The nonnegative weights `λ` combine incentive
constraints; `γ` combines supported pointwise-budget constraints.  If the
weighted incentive coefficients fit under `γ`, and the weighted incentive gains
are at least `L`, then every feasible budget is at least `L`. -/
theorem le_recommendationPaymentImplPrice_of_weighted_certificate
    [DecidableEq ι] [Fintype ι] [Fintype (Profile G)]
    [∀ i, Fintype (G.Strategy i)]
    {μ : PMF (Profile G)} {L : ℝ}
    (hne : (G.recommendationPaymentImplementationCosts μ).Nonempty)
    (lam : (i : ι) → G.Strategy i → G.Strategy i → ℝ)
    (γ : Profile G → ℝ)
    (hlam_nonneg : ∀ i si a, 0 ≤ lam i si a)
    (hγ_nonneg : ∀ θ, 0 ≤ γ θ)
    (hγ_zero : ∀ θ, μ θ = 0 → γ θ = 0)
    (hγ_sum : (∑ θ : Profile G, γ θ) = 1)
    (hcoeff : ∀ θ i,
      (∑ si : G.Strategy i, ∑ a : G.Strategy i,
        lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) ≤ γ θ)
    (hvalue : L ≤
      ∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
        lam i si a * G.recommendationPaymentIncentiveGain μ i si a) :
    L ≤ G.recommendationPaymentImplPrice μ := by
  classical
  refine G.le_recommendationPaymentImplPrice_of_forall_le hne ?_
  intro k hk
  rcases hk with ⟨p, hp⟩
  have hgain_le_payment :
      (∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
          lam i si a * G.recommendationPaymentIncentiveGain μ i si a) ≤
        ∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
          lam i si a *
            (∑ θ : Profile G,
              G.recommendationPaymentIncentiveCoeff μ i si a θ * p θ i) := by
    refine Finset.sum_le_sum ?_
    intro i _
    refine Finset.sum_le_sum ?_
    intro si _
    refine Finset.sum_le_sum ?_
    intro a _
    exact mul_le_mul_of_nonneg_left
      (G.recommendationPaymentIncentiveGain_le_weighted_payment hp i si a)
      (hlam_nonneg i si a)
  have hpayment_rearrange :
      (∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
          lam i si a *
            (∑ θ : Profile G,
              G.recommendationPaymentIncentiveCoeff μ i si a θ * p θ i)) =
        ∑ θ : Profile G, ∑ i,
          (∑ si : G.Strategy i, ∑ a : G.Strategy i,
            lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) *
              p θ i := by
    calc
      (∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
          lam i si a *
            (∑ θ : Profile G,
              G.recommendationPaymentIncentiveCoeff μ i si a θ * p θ i))
          =
        ∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i, ∑ θ : Profile G,
          (lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) *
            p θ i := by
            simp [Finset.mul_sum, mul_assoc]
      _ = ∑ i, ∑ θ : Profile G, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
          (lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) *
            p θ i := by
            refine Finset.sum_congr rfl ?_
            intro i _
            calc
              (∑ si : G.Strategy i, ∑ a : G.Strategy i, ∑ θ : Profile G,
                  (lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) *
                    p θ i)
                  =
                ∑ si : G.Strategy i, ∑ θ : Profile G, ∑ a : G.Strategy i,
                  (lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) *
                    p θ i := by
                    refine Finset.sum_congr rfl ?_
                    intro si _
                    rw [Finset.sum_comm]
              _ = ∑ θ : Profile G, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
                  (lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) *
                    p θ i := by
                    rw [Finset.sum_comm]
      _ = ∑ θ : Profile G, ∑ i,
          (∑ si : G.Strategy i, ∑ a : G.Strategy i,
            lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) *
              p θ i := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro θ _
            refine Finset.sum_congr rfl ?_
            intro i _
            calc
              (∑ si : G.Strategy i, ∑ a : G.Strategy i,
                  (lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) *
                    p θ i)
                  =
                ∑ si : G.Strategy i, ∑ a : G.Strategy i,
                  p θ i *
                    (lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) := by
                    simp [mul_left_comm, mul_comm]
              _ = p θ i *
                  (∑ si : G.Strategy i, ∑ a : G.Strategy i,
                    lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) := by
                    rw [Finset.mul_sum]
                    refine Finset.sum_congr rfl ?_
                    intro si _
                    rw [Finset.mul_sum]
              _ = (∑ si : G.Strategy i, ∑ a : G.Strategy i,
                    lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) *
                    p θ i := by
                    rw [mul_comm]
  have hcoeff_payment :
      (∑ θ : Profile G, ∑ i,
          (∑ si : G.Strategy i, ∑ a : G.Strategy i,
            lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) *
              p θ i) ≤
        ∑ θ : Profile G, γ θ * ∑ i, p θ i := by
    refine Finset.sum_le_sum ?_
    intro θ _
    calc
      (∑ i,
          (∑ si : G.Strategy i, ∑ a : G.Strategy i,
            lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) *
              p θ i)
          ≤ ∑ i, γ θ * p θ i := by
            refine Finset.sum_le_sum ?_
            intro i _
            exact mul_le_mul_of_nonneg_right (hcoeff θ i) (hp.1 θ i)
      _ = γ θ * ∑ i, p θ i := by
            rw [Finset.mul_sum]
  have hbudget :
      (∑ θ : Profile G, γ θ * ∑ i, p θ i) ≤ ∑ θ : Profile G, γ θ * k := by
    refine Finset.sum_le_sum ?_
    intro θ _
    by_cases hθ : μ θ = 0
    · simp [hγ_zero θ hθ]
    · exact mul_le_mul_of_nonneg_left (hp.2.1 θ hθ) (hγ_nonneg θ)
  calc
    L ≤ ∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
        lam i si a * G.recommendationPaymentIncentiveGain μ i si a := hvalue
    _ ≤ ∑ i, ∑ si : G.Strategy i, ∑ a : G.Strategy i,
        lam i si a *
          (∑ θ : Profile G,
            G.recommendationPaymentIncentiveCoeff μ i si a θ * p θ i) :=
          hgain_le_payment
    _ = ∑ θ : Profile G, ∑ i,
        (∑ si : G.Strategy i, ∑ a : G.Strategy i,
          lam i si a * G.recommendationPaymentIncentiveCoeff μ i si a θ) *
            p θ i := hpayment_rearrange
    _ ≤ ∑ θ : Profile G, γ θ * ∑ i, p θ i := hcoeff_payment
    _ ≤ ∑ θ : Profile G, γ θ * k := hbudget
    _ = k := by
          rw [← Finset.sum_mul, hγ_sum, one_mul]

/-- Recommendation-device transfer generated by on-path payments `p`, together
with the usual off-path obedience bonus. -/
noncomputable def paymentRecommendationTransfer [DecidableEq ι]
    (p : Profile G → Payoff ι) (B : ℝ) :
    Profile G → Profile G → Payoff ι := by
  classical
  exact fun θ σ i =>
    (if σ i = θ i then p θ i else 0) + G.recommendationTransfer B θ σ i

theorem paymentRecommendationTransfer_nonneg [DecidableEq ι]
    {p : Profile G → Payoff ι} (hp : ∀ θ i, 0 ≤ p θ i)
    {B : ℝ} (hB : 0 ≤ B) :
    ∀ θ σ i, 0 ≤ G.paymentRecommendationTransfer p B θ σ i := by
  classical
  intro θ σ i
  unfold paymentRecommendationTransfer recommendationTransfer
  apply add_nonneg
  · by_cases h : σ i = θ i
    · simpa [h] using hp θ i
    · simp [h]
  · by_cases h : σ i = θ i ∧ ∃ j : ι, j ≠ i ∧ σ j ≠ θ j
    · simp [h, hB]
    · simp [h]

@[simp] theorem paymentRecommendationTransfer_obedient [DecidableEq ι]
    (p : Profile G → Payoff ι) (B : ℝ) (θ : Profile G) (i : ι) :
    G.paymentRecommendationTransfer p B θ θ i = p θ i := by
  classical
  simp [paymentRecommendationTransfer]

/-- A recommendation device with an arbitrary nonnegative transfer rule.  This
is the right abstraction for pointwise-price lower bounds: signals are exactly
recommended base-game actions, but transfers are otherwise unrestricted. -/
noncomputable abbrev transferRecommendationDevice
    (μ : PMF (Profile G)) (T : Profile G → Profile G → Payoff ι)
    (hT : ∀ θ σ i, 0 ≤ T θ σ i) : G.ImplementationDevice where
  Signal := G.Strategy
  law := μ
  transfer := T
  transfer_nonneg := hT

@[simp] theorem transferRecommendationDevice_law
    (μ : PMF (Profile G)) (T : Profile G → Profile G → Payoff ι)
    (hT : ∀ θ σ i, 0 ≤ T θ σ i) :
    (G.transferRecommendationDevice μ T hT).law = μ := rfl

@[simp] theorem transferRecommendationDevice_transfer
    (μ : PMF (Profile G)) (T : Profile G → Profile G → Payoff ι)
    (hT : ∀ θ σ i, 0 ≤ T θ σ i)
    (θ σ : Profile G) (i : ι) :
    (G.transferRecommendationDevice μ T hT).transfer θ σ i = T θ σ i := rfl

@[simp] theorem transferRecommendationDevice_play_obedient
    (μ : PMF (Profile G)) (T : Profile G → Profile G → Payoff ι)
    (hT : ∀ θ σ i, 0 ≤ T θ σ i) (θ : Profile G) :
    (G.transferRecommendationDevice μ T hT).play (G.obedientDeviceStrategy) θ = θ := by
  rfl

/-- Feasible pointwise budgets for recommendation devices with arbitrary
nonnegative transfers.  This is narrower than arbitrary `ImplementationDevice`s:
the signal spaces are the base strategy spaces and the law is the target
distribution. -/
def recommendationDevicePointwiseImplementationCosts [DecidableEq ι] [Fintype ι]
    (μ : PMF (Profile G)) : Set ℝ :=
  {k | ∃ (T : Profile G → Profile G → Payoff ι)
      (hT : ∀ θ σ i, 0 ≤ T θ σ i),
    (G.transferRecommendationDevice μ T hT).InterimDominantKImplementsDistribution
      (G.obedientDeviceStrategy) μ k}

/-- Infimum pointwise implementation cost over recommendation devices with
arbitrary nonnegative transfers. -/
noncomputable def recommendationDevicePointwiseImplPrice [DecidableEq ι] [Fintype ι]
    (μ : PMF (Profile G)) : ℝ :=
  sInf (G.recommendationDevicePointwiseImplementationCosts μ)

theorem recommendationDevicePointwiseImplementationCosts_bddBelow [DecidableEq ι] [Fintype ι]
    (μ : PMF (Profile G)) :
    BddBelow (G.recommendationDevicePointwiseImplementationCosts μ) := by
  classical
  refine ⟨0, ?_⟩
  intro k hk
  rcases hk with ⟨T, hT, hK⟩
  rcases μ.support_nonempty with ⟨θ, hθsupp⟩
  have hθ : μ θ ≠ 0 := by
    simpa [PMF.mem_support_iff] using hθsupp
  have hsum_nonneg : 0 ≤ ∑ i, T θ θ i :=
    Finset.sum_nonneg fun i _ => hT θ θ i
  exact hsum_nonneg.trans (hK.2 θ hθ)

theorem conditionalSwapRegret_le_of_transferRecommendationDevice_pointwiseKImpl
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)} {T : Profile G → Profile G → Payoff ι}
    {hT : ∀ θ σ i, 0 ≤ T θ σ i} {k : ℝ}
    (hK : (G.transferRecommendationDevice μ T hT).InterimDominantKImplementsDistribution
      (G.obedientDeviceStrategy) μ k)
    (i : ι) (si : G.Strategy i) :
    G.conditionalSwapRegret μ i si ≤ k := by
  classical
  let I := G.transferRecommendationDevice μ T hT
  haveI : Finite (∀ j, I.Signal j) := by
    change Finite (Profile G)
    infer_instance
  have hk_nonneg : 0 ≤ k := by
    rcases μ.support_nonempty with ⟨θ, hθsupp⟩
    have hθ : μ θ ≠ 0 := by
      simpa [PMF.mem_support_iff] using hθsupp
    have hsum_nonneg : 0 ≤ ∑ j, T θ θ j :=
      Finset.sum_nonneg fun j _ => hT θ θ j
    exact hsum_nonneg.trans (hK.2 θ hθ)
  rw [conditionalSwapRegret]
  by_cases hsi : pmfMass (μ := μ) (fun θ : Profile G => si = θ i) ≠ 0
  · simp only [dif_pos hsi]
    apply Finset.sup'_le
    intro a _
    let condLaw : PMF (Profile G) :=
      pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsi
    let constA : I.Signal i → G.Strategy i := fun _ => a
    let β : Profile I.deviceGame := G.obedientDeviceStrategy
    have hsiDevice : I.PositiveSignal i si := by
      simpa [I, ImplementationDevice.PositiveSignal, eq_comm] using hsi
    have hweak := hK.1.1 i constA si hsiDevice β
    rw [I.interimEu_eq_expect_conditional i si hsiDevice] at hweak
    rw [I.interimEu_eq_expect_conditional i si hsiDevice] at hweak
    have hweak' :
        expect condLaw (fun θ : Profile G => G.eu θ i + T θ θ i) ≥
          expect condLaw
            (fun θ : Profile G => G.eu (Function.update θ i a) i +
              T θ (Function.update θ i a) i) := by
      simpa [I, condLaw, β, constA, ImplementationDevice.conditionalSignalLaw,
        ImplementationDevice.play, obedientDeviceStrategy, eq_comm] using hweak
    have hdev_le :
        expect condLaw (fun θ : Profile G => G.eu (Function.update θ i a) i) ≤
          expect condLaw (fun θ : Profile G => G.eu θ i) +
            expect condLaw (fun θ : Profile G => T θ θ i) := by
      have hdev_transfer_nonneg :
          0 ≤ expect condLaw
            (fun θ : Profile G => T θ (Function.update θ i a) i) :=
        expect_nonneg condLaw _ fun θ => hT θ (Function.update θ i a) i
      rw [expect_add] at hweak'
      rw [expect_add] at hweak'
      linarith
    have htransfer_le :
        expect condLaw (fun θ : Profile G => T θ θ i) ≤ k := by
      rw [expect_eq_sum]
      calc
        (∑ θ : Profile G, (condLaw θ).toReal * T θ θ i)
            ≤ ∑ θ : Profile G, (condLaw θ).toReal * k := by
              refine Finset.sum_le_sum ?_
              intro θ _
              by_cases hθcond : condLaw θ = 0
              · simp [hθcond]
              · have hθμ : μ θ ≠ 0 :=
                  ((pmfCond_ne_zero_iff μ (fun θ : Profile G => si = θ i) hsi).mp
                    (by simpa [condLaw] using hθcond)).2
                have hi_le_sum :
                    T θ θ i ≤ ∑ j, T θ θ j :=
                  Finset.single_le_sum
                    (fun j _ => hT θ θ j)
                    (Finset.mem_univ i)
                exact mul_le_mul_of_nonneg_left
                  (hi_le_sum.trans (hK.2 θ hθμ)) ENNReal.toReal_nonneg
        _ = k := by
              rw [← Finset.sum_mul, pmf_toReal_sum_one, one_mul]
    rw [expect_sub]
    linarith
  · simp [hsi, hk_nonneg]

theorem maxConditionalSwapRegret_le_of_transferRecommendationDevice_pointwiseKImpl
    [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)} {T : Profile G → Profile G → Payoff ι}
    {hT : ∀ θ σ i, 0 ≤ T θ σ i} {k : ℝ}
    (hK : (G.transferRecommendationDevice μ T hT).InterimDominantKImplementsDistribution
      (G.obedientDeviceStrategy) μ k) :
    G.maxConditionalSwapRegret μ ≤ k := by
  classical
  unfold maxConditionalSwapRegret
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro si _
  exact G.conditionalSwapRegret_le_of_transferRecommendationDevice_pointwiseKImpl hK i si

theorem maxConditionalSwapRegret_le_of_recommendationDevicePointwiseCost
    [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)} {k : ℝ}
    (hk : k ∈ G.recommendationDevicePointwiseImplementationCosts μ) :
    G.maxConditionalSwapRegret μ ≤ k := by
  rcases hk with ⟨T, hT, hK⟩
  exact G.maxConditionalSwapRegret_le_of_transferRecommendationDevice_pointwiseKImpl
    (T := T) (hT := hT) hK

/-- Any pointwise implementation by a recommendation device induces a feasible
solution of the on-path-payment LP, by reading off the payments made when the
recommendation profile is obeyed. -/
theorem recommendationPaymentFeasible_of_transferRecommendationDevice_pointwiseKImpl
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    {μ : PMF (Profile G)} {T : Profile G → Profile G → Payoff ι}
    {hT : ∀ θ σ i, 0 ≤ T θ σ i} {k : ℝ}
    (hK : (G.transferRecommendationDevice μ T hT).InterimDominantKImplementsDistribution
      (G.obedientDeviceStrategy) μ k) :
    G.RecommendationPaymentFeasible μ (fun θ i => T θ θ i) k := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro θ i
    exact hT θ θ i
  · intro θ hθ
    exact hK.2 θ hθ
  · intro i si hsi a
    let I := G.transferRecommendationDevice μ T hT
    haveI : Finite (∀ j, I.Signal j) := by
      change Finite (Profile G)
      infer_instance
    let condLaw : PMF (Profile G) :=
      pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsi
    let constA : I.Signal i → G.Strategy i := fun _ => a
    let β : Profile I.deviceGame := G.obedientDeviceStrategy
    have hsiDevice : I.PositiveSignal i si := by
      simpa [I, ImplementationDevice.PositiveSignal, eq_comm] using hsi
    have hweak := hK.1.1 i constA si hsiDevice β
    rw [I.interimEu_eq_expect_conditional i si hsiDevice] at hweak
    rw [I.interimEu_eq_expect_conditional i si hsiDevice] at hweak
    have hweak' :
        expect condLaw (fun θ : Profile G => G.eu θ i + T θ θ i) ≥
          expect condLaw
            (fun θ : Profile G =>
              G.eu (Function.update θ i a) i + T θ (Function.update θ i a) i) := by
      simpa [I, condLaw, β, constA, ImplementationDevice.conditionalSignalLaw,
        ImplementationDevice.play, obedientDeviceStrategy, eq_comm] using hweak
    have hdev_transfer_nonneg :
        0 ≤ expect condLaw
          (fun θ : Profile G => T θ (Function.update θ i a) i) :=
      expect_nonneg condLaw _ fun θ => hT θ (Function.update θ i a) i
    rw [expect_add] at hweak'
    rw [expect_add] at hweak'
    change expect condLaw
        (fun θ : Profile G => G.eu (Function.update θ i a) i - G.eu θ i) ≤
      expect condLaw (fun θ : Profile G => T θ θ i)
    rw [expect_sub]
    linarith

theorem recommendationDevicePointwiseCost_subset_recommendationPaymentCost
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    {μ : PMF (Profile G)} {k : ℝ}
    (hk : k ∈ G.recommendationDevicePointwiseImplementationCosts μ) :
    k ∈ G.recommendationPaymentImplementationCosts μ := by
  rcases hk with ⟨T, hT, hK⟩
  exact ⟨fun θ i => T θ θ i,
    G.recommendationPaymentFeasible_of_transferRecommendationDevice_pointwiseKImpl hK⟩

/-- A feasible on-path-payment LP solution becomes an interim-dominant
recommendation device after adding a large enough off-path obedience bonus.
The LP constraints handle the case where opponents obey; the bonus handles
arbitrary signal-contingent opponent deviations. -/
theorem paymentRecommendationTransfer_obedient_interimDominantProfile_of_feasible
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    {μ : PMF (Profile G)} {p : Profile G → Payoff ι} {k M B : ℝ}
    (hp : G.RecommendationPaymentFeasible μ p k)
    (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus : 2 * M ≤ B) :
    (G.transferRecommendationDevice μ (G.paymentRecommendationTransfer p B)
        (G.paymentRecommendationTransfer_nonneg hp.1 hB)).InterimDominantProfile
      (G.obedientDeviceStrategy) := by
  classical
  intro i c si hsi β
  let T : Profile G → Profile G → Payoff ι := G.paymentRecommendationTransfer p B
  let hT : ∀ θ σ i, 0 ≤ T θ σ i := G.paymentRecommendationTransfer_nonneg hp.1 hB
  let I := G.transferRecommendationDevice μ T hT
  haveI : Finite (∀ j, I.Signal j) := by
    change Finite (Profile G)
    infer_instance
  let condLaw : PMF (Profile G) := I.conditionalSignalLaw i si hsi
  let obeyi : I.Signal i → G.Strategy i := G.obedientDeviceStrategy i
  let leftProfile : Profile I.deviceGame := Function.update β i obeyi
  let rightProfile : Profile I.deviceGame := Function.update β i c
  change I.interimEu i si hsi leftProfile ≥ I.interimEu i si hsi rightProfile
  by_cases hcsi : c si = si
  · rw [I.interimEu_update_eq_const_at_signal hsi β obeyi]
    rw [I.interimEu_update_eq_const_at_signal hsi β c]
    simp [obeyi, KernelGame.obedientDeviceStrategy, hcsi]
  · rw [I.interimEu_eq_expect_conditional i si hsi leftProfile]
    rw [I.interimEu_eq_expect_conditional i si hsi rightProfile]
    let L : Profile G → ℝ := fun θ =>
      G.eu (I.play leftProfile θ) i + I.transfer θ (I.play leftProfile θ) i
    let R : Profile G → ℝ := fun θ =>
      G.eu (I.play rightProfile θ) i + I.transfer θ (I.play rightProfile θ) i
    let CEObey : Profile G → ℝ := fun θ => G.eu θ i
    let CEDev : Profile G → ℝ := fun θ =>
      G.eu (Function.update θ i (c (θ i))) i
    let Pay : Profile G → ℝ := fun θ =>
      if c (θ i) = θ i then 0 else p θ i
    change expect condLaw L ≥ expect condLaw R
    have hpoint :
        ∀ θ : Profile G, R θ - L θ ≤ CEDev θ - CEObey θ - Pay θ := by
      intro θ
      let σβ : Profile G := I.play β θ
      have hleft_play :
          I.play leftProfile θ = Function.update σβ i (θ i) := by
        simp [leftProfile, obeyi, σβ, KernelGame.obedientDeviceStrategy]
      have hright_play :
          I.play rightProfile θ = Function.update σβ i (c (θ i)) := by
        simp [rightProfile, σβ]
      by_cases hself : c (θ i) = θ i
      · have hright_left :
            Function.update σβ i (c (θ i)) = Function.update σβ i (θ i) := by
          simp [hself]
        have hce_same : Function.update θ i (c (θ i)) = θ := by
          simp [hself, Function.update_eq_self]
        simp [L, R, CEDev, CEObey, Pay, hleft_play, hright_play, hself]
      · by_cases hopp : ∃ j : ι, j ≠ i ∧ σβ j ≠ θ j
        · have hβ_range :
              G.eu (Function.update σβ i (c (θ i))) i -
                G.eu (Function.update σβ i (θ i)) i ≤ M :=
            hdiam i (Function.update σβ i (c (θ i)))
              (Function.update σβ i (θ i))
          have hce_range :
              G.eu θ i - G.eu (Function.update θ i (c (θ i))) i ≤ M :=
            hdiam i θ (Function.update θ i (c (θ i)))
          have hpay_nonneg : 0 ≤ p θ i := hp.1 θ i
          simp [L, R, CEDev, CEObey, Pay, I, T, hleft_play, hright_play,
            paymentRecommendationTransfer, recommendationTransfer_update_self,
            hself, hopp]
          linarith
        · have hσβ_off : ∀ j : ι, j ≠ i → σβ j = θ j := by
            intro j hji
            by_contra hne
            exact hopp ⟨j, hji, hne⟩
          have hleft_eq : Function.update σβ i (θ i) = θ := by
            funext j
            by_cases hji : j = i
            · subst hji
              simp
            · simp [Function.update_of_ne hji, hσβ_off j hji]
          have hright_eq :
              Function.update σβ i (c (θ i)) =
                Function.update θ i (c (θ i)) := by
            funext j
            by_cases hji : j = i
            · subst hji
              simp
            · simp [Function.update_of_ne hji, hσβ_off j hji]
          simp [L, R, CEDev, CEObey, Pay, I, T, hleft_play, hright_play,
            hleft_eq, hright_eq, paymentRecommendationTransfer, hself]
    have hdiff_expect :
        expect condLaw (fun θ => R θ - L θ) ≤
          expect condLaw (fun θ => CEDev θ - CEObey θ - Pay θ) :=
      expect_mono condLaw (fun θ => R θ - L θ)
        (fun θ => CEDev θ - CEObey θ - Pay θ) hpoint
    have hsiμ : pmfMass (μ := μ) (fun θ : Profile G => θ i = si) ≠ 0 := by
      simpa [I, ImplementationDevice.PositiveSignal] using hsi
    have hsiμ' : pmfMass (μ := μ) (fun θ : Profile G => si = θ i) ≠ 0 := by
      simpa [eq_comm] using hsiμ
    have hgain_eq :
        expect condLaw (fun θ => CEDev θ - CEObey θ) =
          expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsiμ')
            (fun θ => G.eu (Function.update θ i (c si)) i - G.eu θ i) := by
      refine (expect_congr_of_ne_zero condLaw
        (fun θ => CEDev θ - CEObey θ)
        (fun θ => G.eu (Function.update θ i (c si)) i - G.eu θ i) ?_).trans ?_
      · intro θ hθ
        have hθi := I.conditionalSignalLaw_ne_zero_implies hsi hθ
        simp [CEDev, CEObey, hθi]
      · simp [condLaw, I, ImplementationDevice.conditionalSignalLaw, eq_comm]
    have hgain_le :
        expect condLaw (fun θ => CEDev θ - CEObey θ) ≤
          expect condLaw Pay := by
      have hpay_eq :
          expect condLaw Pay =
            expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsiμ')
              (fun θ => p θ i) := by
        calc
          expect condLaw Pay =
              expect condLaw (fun θ : Profile G => p θ i) := by
                refine expect_congr_of_ne_zero condLaw Pay
                  (fun θ : Profile G => p θ i) ?_
                intro θ hθ
                have hθi := I.conditionalSignalLaw_ne_zero_implies hsi hθ
                simp [Pay, hθi, hcsi]
          _ = expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsiμ')
              (fun θ => p θ i) := by
                simp [condLaw, I, ImplementationDevice.conditionalSignalLaw,
                  eq_comm]
      calc
        expect condLaw (fun θ => CEDev θ - CEObey θ)
            = expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsiμ')
                (fun θ => G.eu (Function.update θ i (c si)) i - G.eu θ i) := hgain_eq
        _ ≤ expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsiμ')
                (fun θ => p θ i) := hp.2.2 i si hsiμ' (c si)
        _ = expect condLaw Pay := hpay_eq.symm
    have hrhs_eq :
        expect condLaw (fun θ => CEDev θ - CEObey θ - Pay θ) =
          expect condLaw (fun θ => CEDev θ - CEObey θ) -
            expect condLaw Pay := by
      rw [expect_sub]
    rw [hrhs_eq] at hdiff_expect
    have hdiff_nonpos : expect condLaw (fun θ => R θ - L θ) ≤ 0 := by
      linarith
    rw [expect_sub] at hdiff_nonpos
    linarith

theorem recommendationPaymentCost_subset_recommendationDevicePointwiseCost
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    {μ : PMF (Profile G)} {k : ℝ}
    (hk : k ∈ G.recommendationPaymentImplementationCosts μ) :
    k ∈ G.recommendationDevicePointwiseImplementationCosts μ := by
  classical
  letI : Fintype (Profile G) := Fintype.ofFinite (Profile G)
  rcases hk with ⟨p, hp⟩
  let M : ℝ := G.euDiameterSum
  let B : ℝ := 2 * M
  have hM_nonneg : 0 ≤ M := by
    dsimp [M, euDiameterSum]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun σ _ =>
      Finset.sum_nonneg fun τ _ =>
        show 0 ≤ |G.eu σ i - G.eu τ i| from abs_nonneg _
  have hB : 0 ≤ B := by
    nlinarith
  have hbonus : 2 * M ≤ B := by
    rfl
  let T : Profile G → Profile G → Payoff ι := G.paymentRecommendationTransfer p B
  let hT : ∀ θ σ i, 0 ≤ T θ σ i :=
    G.paymentRecommendationTransfer_nonneg hp.1 hB
  refine ⟨T, hT, ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact G.paymentRecommendationTransfer_obedient_interimDominantProfile_of_feasible
      (p := p) (k := k) (M := M) (B := B) hp hB G.euDiameterBound_sum hbonus
  · rw [ImplementationDevice.ImplementsDistribution,
      ImplementationDevice.inducedDistribution]
    change PMF.map (fun θ : Profile G => θ) μ = μ
    exact PMF.map_id μ
  · intro θ hθ
    simpa [T] using hp.2.1 θ hθ

theorem recommendationDevicePointwiseImplementationCosts_eq_recommendationPaymentCosts
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    (μ : PMF (Profile G)) :
    G.recommendationDevicePointwiseImplementationCosts μ =
      G.recommendationPaymentImplementationCosts μ := by
  ext k
  constructor
  · exact G.recommendationDevicePointwiseCost_subset_recommendationPaymentCost
  · exact G.recommendationPaymentCost_subset_recommendationDevicePointwiseCost

theorem recommendationDevicePointwiseImplPrice_eq_recommendationPaymentImplPrice
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    (μ : PMF (Profile G)) :
    G.recommendationDevicePointwiseImplPrice μ =
      G.recommendationPaymentImplPrice μ := by
  rw [recommendationDevicePointwiseImplPrice, recommendationPaymentImplPrice,
    G.recommendationDevicePointwiseImplementationCosts_eq_recommendationPaymentCosts μ]

@[simp] theorem regretRecommendationTransfer_obedient [DecidableEq ι]
    (μ : PMF (Profile G)) (B : ℝ)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (θ : Profile G) (i : ι) :
    G.regretRecommendationTransfer μ B θ θ i =
      G.conditionalSwapRegret μ i (θ i) := by
  rw [regretRecommendationTransfer, if_pos rfl, recommendationTransfer_obedient]
  simp

/-- Recommendation device with an obedience bonus. Its signals are recommended
base-game strategies and its law is the desired correlated distribution. -/
noncomputable abbrev recommendationDevice (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B) :
    G.ImplementationDevice where
  Signal := G.Strategy
  law := μ
  transfer := G.recommendationTransfer B
  transfer_nonneg := by
    classical
    intro θ σ i
    unfold recommendationTransfer
    by_cases h : σ i = θ i ∧ ∃ j : ι, j ≠ i ∧ σ j ≠ θ j
    · simp [h, hB]
    · simp [h]

/-- Recommendation device that pays conditional swap regret on the obedient
path, plus an off-path obedience bonus. -/
noncomputable abbrev regretRecommendationDevice [DecidableEq ι]
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] :
    G.ImplementationDevice where
  Signal := G.Strategy
  law := μ
  transfer := G.regretRecommendationTransfer μ B
  transfer_nonneg := G.regretRecommendationTransfer_nonneg μ hB

@[simp] theorem recommendationDevice_law
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B) :
    (G.recommendationDevice μ B hB).law = μ := rfl

@[simp] theorem recommendationDevice_transfer
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B)
    (θ σ : Profile G) (i : ι) :
    (G.recommendationDevice μ B hB).transfer θ σ i =
      G.recommendationTransfer B θ σ i := rfl

@[simp] theorem regretRecommendationDevice_law [DecidableEq ι]
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] :
    (G.regretRecommendationDevice μ B hB).law = μ := rfl

@[simp] theorem regretRecommendationDevice_transfer [DecidableEq ι]
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (θ σ : Profile G) (i : ι) :
    (G.regretRecommendationDevice μ B hB).transfer θ σ i =
      G.regretRecommendationTransfer μ B θ σ i := rfl

@[simp] theorem recommendationDevice_play_obedient
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B) (θ : Profile G) :
    (G.recommendationDevice μ B hB).play (G.obedientDeviceStrategy) θ = θ := by
  rfl

@[simp] theorem regretRecommendationDevice_play_obedient [DecidableEq ι]
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (θ : Profile G) :
    (G.regretRecommendationDevice μ B hB).play (G.obedientDeviceStrategy) θ = θ := by
  rfl

@[simp] theorem recommendationDevice_play_update_obedient [DecidableEq ι]
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B)
    (θ : Profile G) (i : ι) (c : G.Strategy i → G.Strategy i) :
    (G.recommendationDevice μ B hB).play
        (Function.update (G.obedientDeviceStrategy) i c) θ =
      Function.update θ i (c (θ i)) := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [ImplementationDevice.play]
  · simp [ImplementationDevice.play, Function.update_of_ne hji, obedientDeviceStrategy]

/-- Obedience induces exactly the recommendation law over base-game profiles. -/
theorem recommendationDevice_inducedDistribution_obedient
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B) :
    (G.recommendationDevice μ B hB).inducedDistribution
      (G.obedientDeviceStrategy) = μ := by
  rw [ImplementationDevice.inducedDistribution]
  change PMF.map (fun θ : Profile G => θ) μ = μ
  exact PMF.map_id μ

/-- Obedience implements the target distribution at the distributional level. -/
theorem recommendationDevice_implementsDistribution_obedient
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B) :
    (G.recommendationDevice μ B hB).ImplementsDistribution
      (G.obedientDeviceStrategy) μ :=
  G.recommendationDevice_inducedDistribution_obedient μ B hB

/-- Obedience in the regret-paying recommendation device induces exactly the
recommendation law. -/
theorem regretRecommendationDevice_inducedDistribution_obedient [DecidableEq ι]
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] :
    (G.regretRecommendationDevice μ B hB).inducedDistribution
      (G.obedientDeviceStrategy) = μ := by
  rw [ImplementationDevice.inducedDistribution]
  change PMF.map (fun θ : Profile G => θ) μ = μ
  exact PMF.map_id μ

/-- Obedience implements the target law at the distributional level in the
regret-paying recommendation device. -/
theorem regretRecommendationDevice_implementsDistribution_obedient [DecidableEq ι]
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] :
    (G.regretRecommendationDevice μ B hB).ImplementsDistribution
      (G.obedientDeviceStrategy) μ :=
  G.regretRecommendationDevice_inducedDistribution_obedient μ B hB

/-- Expected on-path outlay of the regret-paying recommendation device.  The
off-path obedience bonus contributes zero on the obedient path. -/
theorem regretRecommendationDevice_expectedRealizedTransfer_obedient [DecidableEq ι]
    [Fintype ι] [Finite (Profile G)]
    (μ : PMF (Profile G)) (B : ℝ) (hB : 0 ≤ B)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] :
    (G.regretRecommendationDevice μ B hB).expectedRealizedTransfer
        (G.obedientDeviceStrategy) =
      ∑ i, expect μ (fun θ => G.conditionalSwapRegret μ i (θ i)) := by
  classical
  let I := G.regretRecommendationDevice μ B hB
  change I.expectedRealizedTransfer G.obedientDeviceStrategy =
    ∑ i, expect μ (fun θ => G.conditionalSwapRegret μ i (θ i))
  rw [I.expectedRealizedTransfer_eq_sum_to]
  refine Finset.sum_congr rfl ?_
  intro i _
  simp [I, ImplementationDevice.expectedRealizedTransferTo]

/-- Correlated-equilibrium obedience is interim dominant in the recommendation
device when the obedience bonus covers two payoff-range losses. The hypothesis
`G.EuDiameterBound M` is the paper's bounded-payoff hypothesis in range form:
any two expected utilities of the same player differ by at most `M`. Thus the
weak dominance argument uses the paper-shaped condition `2 * M ≤ B`. -/
theorem recommendationDevice_obedient_interimDominantProfile_of_eu_diameter_bound
    [DecidableEq ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus : 2 * M ≤ B) :
    (G.recommendationDevice μ B hB).InterimDominantProfile
      (G.obedientDeviceStrategy) := by
  classical
  intro i c si hsi β
  let I := G.recommendationDevice μ B hB
  haveI : Finite (∀ j, I.Signal j) := by
    change Finite (Profile G)
    infer_instance
  let condLaw : PMF (Profile G) := I.conditionalSignalLaw i si hsi
  let obeyi : I.Signal i → G.Strategy i := G.obedientDeviceStrategy i
  let leftProfile : Profile I.deviceGame := Function.update β i obeyi
  let rightProfile : Profile I.deviceGame := Function.update β i c
  change I.interimEu i si hsi leftProfile ≥ I.interimEu i si hsi rightProfile
  rw [I.interimEu_eq_expect_conditional i si hsi leftProfile]
  rw [I.interimEu_eq_expect_conditional i si hsi rightProfile]
  let L : Profile G → ℝ := fun θ =>
    G.eu (I.play leftProfile θ) i + I.transfer θ (I.play leftProfile θ) i
  let R : Profile G → ℝ := fun θ =>
    G.eu (I.play rightProfile θ) i + I.transfer θ (I.play rightProfile θ) i
  let CEObey : Profile G → ℝ := fun θ => G.eu θ i
  let CEDev : Profile G → ℝ := fun θ =>
    G.eu (Function.update θ i (c (θ i))) i
  change expect condLaw L ≥ expect condLaw R
  have hce_cond := hce.conditional_obedience i si (c si) hsi
  have hdev_eq :
      expect condLaw CEDev =
        expect condLaw (fun θ : Profile G => G.eu (Function.update θ i (c si)) i) := by
    refine expect_congr_of_ne_zero condLaw CEDev
      (fun θ : Profile G => G.eu (Function.update θ i (c si)) i) ?_
    intro θ hθ
    have hθi := I.conditionalSignalLaw_ne_zero_implies hsi hθ
    simp [CEDev, hθi]
  have hce_var : expect condLaw CEDev ≤ expect condLaw CEObey := by
    rw [hdev_eq]
    simpa [condLaw, I, CEObey, ImplementationDevice.conditionalSignalLaw] using hce_cond
  have hpoint : ∀ θ : Profile G, R θ - L θ ≤ CEDev θ - CEObey θ := by
    intro θ
    let σβ : Profile G := I.play β θ
    have hleft_play :
        I.play leftProfile θ = Function.update σβ i (θ i) := by
      simp [leftProfile, obeyi, σβ, KernelGame.obedientDeviceStrategy]
    have hright_play :
        I.play rightProfile θ = Function.update σβ i (c (θ i)) := by
      simp [rightProfile, σβ]
    by_cases hself : c (θ i) = θ i
    · have hright_left :
          Function.update σβ i (c (θ i)) = Function.update σβ i (θ i) := by
        simp [hself]
      have hce_same : Function.update θ i (c (θ i)) = θ := by
        simp [hself, Function.update_eq_self]
      simp [L, R, CEDev, CEObey, hleft_play, hright_play, hright_left, hce_same]
    · by_cases hopp : ∃ j : ι, j ≠ i ∧ σβ j ≠ θ j
      · have hβ_range :
            G.eu (Function.update σβ i (c (θ i))) i -
              G.eu (Function.update σβ i (θ i)) i ≤ M :=
          hdiam i (Function.update σβ i (c (θ i)))
            (Function.update σβ i (θ i))
        have hce_range :
            G.eu θ i - G.eu (Function.update θ i (c (θ i))) i ≤ M :=
          hdiam i θ (Function.update θ i (c (θ i)))
        simp [L, R, CEDev, CEObey, I, hleft_play, hright_play,
          recommendationTransfer_update_self, hself, hopp]
        linarith
      · have hσβ_off : ∀ j : ι, j ≠ i → σβ j = θ j := by
          intro j hji
          by_contra hne
          exact hopp ⟨j, hji, hne⟩
        have hleft_eq : Function.update σβ i (θ i) = θ := by
          funext j
          by_cases hji : j = i
          · subst hji
            simp
          · simp [Function.update_of_ne hji, hσβ_off j hji]
        have hright_eq :
            Function.update σβ i (c (θ i)) =
              Function.update θ i (c (θ i)) := by
          funext j
          by_cases hji : j = i
          · subst hji
            simp
          · simp [Function.update_of_ne hji, hσβ_off j hji]
        simp [L, R, CEDev, CEObey, I, hleft_play, hright_play,
          hleft_eq, hright_eq]
  have hdiff_expect :
      expect condLaw (fun θ => R θ - L θ) ≤
        expect condLaw (fun θ => CEDev θ - CEObey θ) :=
    expect_mono condLaw (fun θ => R θ - L θ)
      (fun θ => CEDev θ - CEObey θ) hpoint
  have hce_diff_nonpos :
      expect condLaw (fun θ => CEDev θ - CEObey θ) ≤ 0 := by
    rw [expect_sub]
    linarith
  have hdiff_nonpos : expect condLaw (fun θ => R θ - L θ) ≤ 0 :=
    hdiff_expect.trans hce_diff_nonpos
  rw [expect_sub] at hdiff_nonpos
  linarith

/-- The regret-paying recommendation device interim-dominantly implements any
finite distribution.  Conditional swap-regret payments cover profitable
on-path deviations, while the off-path obedience bonus handles arbitrary
opponent signal-contingent deviations. -/
theorem regretRecommendationDevice_obedient_interimDominantProfile_of_eu_diameter_bound
    [DecidableEq ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)}
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus : 2 * M ≤ B) :
    (G.regretRecommendationDevice μ B hB).InterimDominantProfile
      (G.obedientDeviceStrategy) := by
  classical
  intro i c si hsi β
  let I := G.regretRecommendationDevice μ B hB
  haveI : Finite (∀ j, I.Signal j) := by
    change Finite (Profile G)
    infer_instance
  let condLaw : PMF (Profile G) := I.conditionalSignalLaw i si hsi
  let obeyi : I.Signal i → G.Strategy i := G.obedientDeviceStrategy i
  let leftProfile : Profile I.deviceGame := Function.update β i obeyi
  let rightProfile : Profile I.deviceGame := Function.update β i c
  change I.interimEu i si hsi leftProfile ≥ I.interimEu i si hsi rightProfile
  by_cases hcsi : c si = si
  · rw [I.interimEu_update_eq_const_at_signal hsi β obeyi]
    rw [I.interimEu_update_eq_const_at_signal hsi β c]
    simp [obeyi, KernelGame.obedientDeviceStrategy, hcsi]
  · rw [I.interimEu_eq_expect_conditional i si hsi leftProfile]
    rw [I.interimEu_eq_expect_conditional i si hsi rightProfile]
    let L : Profile G → ℝ := fun θ =>
      G.eu (I.play leftProfile θ) i + I.transfer θ (I.play leftProfile θ) i
    let R : Profile G → ℝ := fun θ =>
      G.eu (I.play rightProfile θ) i + I.transfer θ (I.play rightProfile θ) i
    let CEObey : Profile G → ℝ := fun θ => G.eu θ i
    let CEDev : Profile G → ℝ := fun θ =>
      G.eu (Function.update θ i (c (θ i))) i
    let Pay : Profile G → ℝ := fun θ =>
      if c (θ i) = θ i then 0 else G.conditionalSwapRegret μ i (θ i)
    change expect condLaw L ≥ expect condLaw R
    have hpoint :
        ∀ θ : Profile G, R θ - L θ ≤ CEDev θ - CEObey θ - Pay θ := by
      intro θ
      let σβ : Profile G := I.play β θ
      have hleft_play :
          I.play leftProfile θ = Function.update σβ i (θ i) := by
        simp [leftProfile, obeyi, σβ, KernelGame.obedientDeviceStrategy]
      have hright_play :
          I.play rightProfile θ = Function.update σβ i (c (θ i)) := by
        simp [rightProfile, σβ]
      by_cases hself : c (θ i) = θ i
      · have hright_left :
            Function.update σβ i (c (θ i)) = Function.update σβ i (θ i) := by
          simp [hself]
        have hce_same : Function.update θ i (c (θ i)) = θ := by
          simp [hself, Function.update_eq_self]
        simp [L, R, CEDev, CEObey, Pay, hleft_play, hright_play, hself]
      · by_cases hopp : ∃ j : ι, j ≠ i ∧ σβ j ≠ θ j
        · have hβ_range :
              G.eu (Function.update σβ i (c (θ i))) i -
                G.eu (Function.update σβ i (θ i)) i ≤ M :=
            hdiam i (Function.update σβ i (c (θ i)))
              (Function.update σβ i (θ i))
          have hce_range :
              G.eu θ i - G.eu (Function.update θ i (c (θ i))) i ≤ M :=
            hdiam i θ (Function.update θ i (c (θ i)))
          have hpay_nonneg : 0 ≤ G.conditionalSwapRegret μ i (θ i) :=
            G.conditionalSwapRegret_nonneg μ i (θ i)
          simp [L, R, CEDev, CEObey, Pay, I, hleft_play, hright_play,
            regretRecommendationTransfer, recommendationTransfer_update_self,
            hself, hopp]
          linarith
        · have hσβ_off : ∀ j : ι, j ≠ i → σβ j = θ j := by
            intro j hji
            by_contra hne
            exact hopp ⟨j, hji, hne⟩
          have hleft_eq : Function.update σβ i (θ i) = θ := by
            funext j
            by_cases hji : j = i
            · subst hji
              simp
            · simp [Function.update_of_ne hji, hσβ_off j hji]
          have hright_eq :
              Function.update σβ i (c (θ i)) =
                Function.update θ i (c (θ i)) := by
            funext j
            by_cases hji : j = i
            · subst hji
              simp
            · simp [Function.update_of_ne hji, hσβ_off j hji]
          simp [L, R, CEDev, CEObey, Pay, I, hleft_play, hright_play,
            hleft_eq, hright_eq, regretRecommendationTransfer, hself]
    have hdiff_expect :
        expect condLaw (fun θ => R θ - L θ) ≤
          expect condLaw (fun θ => CEDev θ - CEObey θ - Pay θ) :=
      expect_mono condLaw (fun θ => R θ - L θ)
        (fun θ => CEDev θ - CEObey θ - Pay θ) hpoint
    have hsiμ : pmfMass (μ := μ) (fun θ : Profile G => θ i = si) ≠ 0 := by
      simpa [I, ImplementationDevice.PositiveSignal] using hsi
    have hsiμ' : pmfMass (μ := μ) (fun θ : Profile G => si = θ i) ≠ 0 := by
      simpa [eq_comm] using hsiμ
    have hgain_eq :
        expect condLaw (fun θ => CEDev θ - CEObey θ) =
          expect (pmfCond (μ := μ) (fun θ : Profile G => si = θ i) hsiμ')
            (fun θ => G.eu (Function.update θ i (c si)) i - G.eu θ i) := by
      refine (expect_congr_of_ne_zero condLaw
        (fun θ => CEDev θ - CEObey θ)
        (fun θ => G.eu (Function.update θ i (c si)) i - G.eu θ i) ?_).trans ?_
      · intro θ hθ
        have hθi := I.conditionalSignalLaw_ne_zero_implies hsi hθ
        simp [CEDev, CEObey, hθi]
      · simp [condLaw, I, ImplementationDevice.conditionalSignalLaw, eq_comm]
    have hgain_le :
        expect condLaw (fun θ => CEDev θ - CEObey θ) ≤
          G.conditionalSwapRegret μ i si := by
      rw [hgain_eq]
      exact G.conditionalGain_le_conditionalSwapRegret μ i si (c si) hsiμ'
    have hpay_eq :
        expect condLaw Pay = G.conditionalSwapRegret μ i si := by
      calc
        expect condLaw Pay =
            expect condLaw (fun _ : Profile G =>
              G.conditionalSwapRegret μ i si) := by
              refine expect_congr_of_ne_zero condLaw Pay
                (fun _ : Profile G => G.conditionalSwapRegret μ i si) ?_
              intro θ hθ
              have hθi := I.conditionalSignalLaw_ne_zero_implies hsi hθ
              simp [Pay, hθi, hcsi]
        _ = G.conditionalSwapRegret μ i si := by simp
    have hrhs_eq :
        expect condLaw (fun θ => CEDev θ - CEObey θ - Pay θ) =
          expect condLaw (fun θ => CEDev θ - CEObey θ) -
            expect condLaw Pay := by
      rw [expect_sub]
    rw [hrhs_eq] at hdiff_expect
    have hdiff_nonpos : expect condLaw (fun θ => R θ - L θ) ≤ 0 := by
      linarith
    rw [expect_sub] at hdiff_nonpos
    linarith

/-- Expected-cost implementation by the regret-paying recommendation device,
with cost equal to the sum of maximum swap regrets. -/
theorem regretRecommendationDevice_obedient_interimDominantExpectedKImplDist
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, DecidableEq (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)}
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus : 2 * M ≤ B) :
    (G.regretRecommendationDevice μ B hB).InterimDominantExpectedKImplementsDistribution
      (G.obedientDeviceStrategy) μ
      (∑ i, G.maxSwapRegret μ i) := by
  refine ⟨⟨
    G.regretRecommendationDevice_obedient_interimDominantProfile_of_eu_diameter_bound
      hB hdiam hbonus,
    G.regretRecommendationDevice_implementsDistribution_obedient μ B hB⟩, ?_⟩
  rw [G.regretRecommendationDevice_expectedRealizedTransfer_obedient μ B hB]
  exact le_of_eq (Finset.sum_congr rfl fun i _ =>
    (G.maxSwapRegret_eq_expect_conditionalSwapRegret μ i).symm)

/-- Pointwise-cost implementation by the regret-paying recommendation device.
At each supported recommendation profile, the on-path outlay is the realized
sum of conditional swap regrets. -/
theorem regretRecommendationDevice_obedient_interimDominantKImplDist
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)}
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus : 2 * M ≤ B) :
    (G.regretRecommendationDevice μ B hB).InterimDominantKImplementsDistribution
      (G.obedientDeviceStrategy) μ
      (G.maxSupportedPointwiseConditionalSwapRegret μ) := by
  classical
  refine ⟨⟨
    G.regretRecommendationDevice_obedient_interimDominantProfile_of_eu_diameter_bound
      hB hdiam hbonus,
    G.regretRecommendationDevice_implementsDistribution_obedient μ B hB⟩, ?_⟩
  intro θ hθ
  simpa using
    G.sum_conditionalSwapRegret_le_maxSupportedPointwiseConditionalSwapRegret μ hθ

/-- Action-level strict dominance theorem for the recommendation device. This is
the paper's Section 6 dominance statement: after any positive-probability
recommendation, obeying that recommendation weakly dominates every alternative
action and is strictly better against a suitable opponent behavior profile. -/
theorem recommendationDevice_obedient_interimActionWeaklyStrictlyDominates_of_eu_diameter_bound
    [DecidableEq ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    {i : ι} {si a : G.Strategy i}
    (hsi : (G.recommendationDevice μ B hB).PositiveSignal i si)
    (ha : a ≠ si)
    (hopponent : ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    (G.recommendationDevice μ B hB).InterimActionWeaklyStrictlyDominates
      i si hsi si a := by
  classical
  let I := G.recommendationDevice μ B hB
  haveI : Finite (∀ k, I.Signal k) := by
    change Finite (Profile G)
    infer_instance
  have hweakProfile :
      I.InterimDominantProfile G.obedientDeviceStrategy :=
    G.recommendationDevice_obedient_interimDominantProfile_of_eu_diameter_bound
      hce hB hdiam hbonus_weak
  refine ⟨?_, ?_⟩
  · intro β
    let βI : Profile I.deviceGame := β
    let constSi : I.deviceGame.Strategy i := fun _ : I.Signal i => si
    let constA : I.deviceGame.Strategy i := fun _ : I.Signal i => a
    let obeyi : I.deviceGame.Strategy i := G.obedientDeviceStrategy i
    let leftConst : Profile I.deviceGame := Function.update βI i constSi
    let rightConst : Profile I.deviceGame := Function.update βI i constA
    let leftObey : Profile I.deviceGame := Function.update βI i obeyi
    change I.interimEu i si hsi leftConst ≥
      I.interimEu i si hsi rightConst
    have hweak := hweakProfile i constA si hsi βI
    change I.interimEu i si hsi leftObey ≥
      I.interimEu i si hsi rightConst at hweak
    have hleft_eq :
        I.interimEu i si hsi leftConst =
          I.interimEu i si hsi leftObey := by
      rw [I.interimEu_eq_expect_conditional i si hsi leftConst]
      rw [I.interimEu_eq_expect_conditional i si hsi leftObey]
      refine expect_congr_of_ne_zero (I.conditionalSignalLaw i si hsi) _ _ ?_
      intro θ hθ
      have hθi := I.conditionalSignalLaw_ne_zero_implies hsi hθ
      simp [leftConst, leftObey, constSi, obeyi, I,
        ImplementationDevice.play, obedientDeviceStrategy, hθi]
    rw [hleft_eq]
    exact hweak
  · obtain ⟨j, hji, hjalt⟩ := hopponent
    let disobeyj : G.Strategy j → G.Strategy j :=
      fun sj => Classical.choose (hjalt sj)
    have hdisobeyj : ∀ sj, disobeyj sj ≠ sj :=
      fun sj => Classical.choose_spec (hjalt sj)
    let β : Profile I.deviceGame :=
      Function.update G.obedientDeviceStrategy j disobeyj
    let constSi : I.deviceGame.Strategy i := fun _ : I.Signal i => si
    let constA : I.deviceGame.Strategy i := fun _ : I.Signal i => a
    refine ⟨β, ?_⟩
    let leftProfile : Profile I.deviceGame :=
      Function.update β i constSi
    let rightProfile : Profile I.deviceGame :=
      Function.update β i constA
    change I.interimEu i si hsi leftProfile >
      I.interimEu i si hsi rightProfile
    rw [I.interimEu_eq_expect_conditional i si hsi leftProfile]
    rw [I.interimEu_eq_expect_conditional i si hsi rightProfile]
    let condLaw : PMF (Profile G) := I.conditionalSignalLaw i si hsi
    let L : Profile G → ℝ := fun θ =>
      G.eu (I.play leftProfile θ) i + I.transfer θ (I.play leftProfile θ) i
    let R : Profile G → ℝ := fun θ =>
      G.eu (I.play rightProfile θ) i + I.transfer θ (I.play rightProfile θ) i
    let L0 : Profile G → ℝ := fun θ => G.eu (I.play leftProfile θ) i + B
    let R0 : Profile G → ℝ := fun θ => G.eu (I.play rightProfile θ) i
    change expect condLaw L > expect condLaw R
    have hL_eq : expect condLaw L = expect condLaw L0 := by
      refine expect_congr_of_ne_zero condLaw L L0 ?_
      intro θ hθ
      have hθi := I.conditionalSignalLaw_ne_zero_implies hsi hθ
      have hleft_transfer :
          I.transfer θ (I.play leftProfile θ) i = B := by
        have hown : I.play leftProfile θ i = θ i := by
          simp [leftProfile, constSi, ImplementationDevice.play, hθi]
        have hjdisobeys : I.play leftProfile θ j ≠ θ j := by
          have hval : I.play leftProfile θ j = disobeyj (θ j) := by
            simp [leftProfile, β, disobeyj, ImplementationDevice.play,
              Function.update_of_ne hji]
          rw [hval]
          exact hdisobeyj (θ j)
        have hothers :
            ∃ k : ι, k ≠ i ∧ I.play leftProfile θ k ≠ θ k :=
          ⟨j, hji, hjdisobeys⟩
        change G.recommendationTransfer B θ (I.play leftProfile θ) i = B
        unfold recommendationTransfer
        exact if_pos ⟨hown, hothers⟩
      simp [L, L0, hleft_transfer]
    have hR_eq : expect condLaw R = expect condLaw R0 := by
      refine expect_congr_of_ne_zero condLaw R R0 ?_
      intro θ hθ
      have hθi := I.conditionalSignalLaw_ne_zero_implies hsi hθ
      have hright_transfer :
          I.transfer θ (I.play rightProfile θ) i = 0 := by
        have hown_ne : I.play rightProfile θ i ≠ θ i := by
          have hplay_i : I.play rightProfile θ i = a := by
            simp [rightProfile, constA, ImplementationDevice.play]
          rw [hplay_i, hθi]
          exact ha
        change G.recommendationTransfer B θ (I.play rightProfile θ) i = 0
        unfold recommendationTransfer
        rw [if_neg]
        intro h
        exact hown_ne h.1
      simp [R, R0, hright_transfer]
    have hdiff_point : ∀ θ : Profile G, R0 θ - L0 θ ≤ M - B := by
      intro θ
      have hrange :
          G.eu (I.play rightProfile θ) i - G.eu (I.play leftProfile θ) i ≤ M :=
        hdiam i (I.play rightProfile θ) (I.play leftProfile θ)
      simp [R0, L0]
      linarith
    have hdiff_expect : expect condLaw (fun θ => R0 θ - L0 θ) ≤ M - B := by
      have hmono := expect_mono condLaw (fun θ : Profile G => R0 θ - L0 θ)
        (fun _ : Profile G => M - B) hdiff_point
      simpa using hmono
    rw [expect_sub] at hdiff_expect
    have hconst_strict : M - B < 0 := by
      linarith
    linarith

/-- Full-support strict-dominance profile theorem for the recommendation
device. Full support is exactly what turns "distinct rule" into "differs at a
positive-probability recommendation". -/
theorem recommendationDevice_obedient_strictInterimDominantProfile_of_eu_diameter_bound
    [DecidableEq ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    (hfull : ∀ i (si : G.Strategy i),
      (G.recommendationDevice μ B hB).PositiveSignal i si)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    (G.recommendationDevice μ B hB).InterimWeaklyStrictlyDominantProfile
      (G.obedientDeviceStrategy) := by
  classical
  intro i c hc
  have hdiff : ∃ si : G.Strategy i,
      (G.recommendationDevice μ B hB).PositiveSignal i si ∧ c si ≠ si := by
    by_contra hnone
    apply hc
    funext si
    by_contra hne
    exact hnone ⟨si, hfull i si, hne⟩
  let I := G.recommendationDevice μ B hB
  refine I.interimWeaklyStrictlyDominates_of_interimAction ?_ ?_
  · intro si hsi
    by_cases hcsi : c si = si
    · intro β
      simp [obedientDeviceStrategy, hcsi]
    · have hact :=
        G.recommendationDevice_obedient_interimActionWeaklyStrictlyDominates_of_eu_diameter_bound
          hce hB hdiam hbonus_weak hbonus_strict hsi hcsi (hopponent i)
      simpa [I, obedientDeviceStrategy] using hact.1
  · obtain ⟨si, hsi, hcsi⟩ := hdiff
    refine ⟨si, hsi, ?_⟩
    have hact :=
      G.recommendationDevice_obedient_interimActionWeaklyStrictlyDominates_of_eu_diameter_bound
        hce hB hdiam hbonus_weak hbonus_strict hsi hcsi (hopponent i)
    simpa [I, obedientDeviceStrategy] using hact

/-- Strict device dominance without the full-support assumption: obedience
weakly-strictly dominates any rule that disagrees with it on at least one
positive-probability recommendation. -/
theorem recommendationDevice_obedient_interimWeaklyStrictlyDominates_of_diff_on_positive
    [DecidableEq ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj)
    {i : ι} {c : G.Strategy i → G.Strategy i}
    (hdiff : ∃ si : G.Strategy i,
      (G.recommendationDevice μ B hB).PositiveSignal i si ∧ c si ≠ si) :
    (G.recommendationDevice μ B hB).InterimWeaklyStrictlyDominates
      i (G.obedientDeviceStrategy i) c := by
  classical
  let I := G.recommendationDevice μ B hB
  refine I.interimWeaklyStrictlyDominates_of_interimAction ?_ ?_
  · intro si hsi
    by_cases hcsi : c si = si
    · intro β
      simp [obedientDeviceStrategy, hcsi]
    · have hact :=
        G.recommendationDevice_obedient_interimActionWeaklyStrictlyDominates_of_eu_diameter_bound
          hce hB hdiam hbonus_weak hbonus_strict hsi hcsi (hopponent i)
      simpa [I, obedientDeviceStrategy] using hact.1
  · obtain ⟨si, hsi, hcsi⟩ := hdiff
    refine ⟨si, hsi, ?_⟩
    have hact :=
      G.recommendationDevice_obedient_interimActionWeaklyStrictlyDominates_of_eu_diameter_bound
        hce hB hdiam hbonus_weak hbonus_strict hsi hcsi (hopponent i)
    simpa [I, obedientDeviceStrategy] using hact

/-- Distributional strict interim-dominance form of the recommendation-device
theorem, under full support of recommendations. -/
theorem recommendationDevice_obedient_strictInterimDominantImplDist_of_eu_diameter_bound
    [DecidableEq ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    (hfull : ∀ i (si : G.Strategy i),
      (G.recommendationDevice μ B hB).PositiveSignal i si)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    (G.recommendationDevice μ B hB).InterimWeaklyStrictlyDominantImplementsDistribution
      (G.obedientDeviceStrategy) μ :=
  ⟨G.recommendationDevice_obedient_strictInterimDominantProfile_of_eu_diameter_bound
      hce hB hdiam hbonus_weak hbonus_strict hfull hopponent,
    G.recommendationDevice_implementsDistribution_obedient μ B hB⟩

/-- Zero-cost strict interim-dominance form of the recommendation-device theorem.
The strictness hypotheses concern off-path behavior; obedient realized transfers
remain zero on every signal profile in the law's support. -/
theorem recommendationDevice_obedient_strictInterimDominantKImplDist_of_eu_diameter_bound
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    (hfull : ∀ i (si : G.Strategy i),
      (G.recommendationDevice μ B hB).PositiveSignal i si)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    (G.recommendationDevice μ B hB).InterimWeaklyStrictlyDominantKImplementsDistribution
      (G.obedientDeviceStrategy) μ 0 := by
  refine ⟨
    G.recommendationDevice_obedient_strictInterimDominantImplDist_of_eu_diameter_bound
      hce hB hdiam hbonus_weak hbonus_strict hfull hopponent, ?_⟩
  intro θ _hθ
  simp

/-- Expected-cost version of the strict recommendation-device theorem. -/
theorem recommendationDevice_obedient_strictInterimDominantExpectedKImplDist_of_eu_diameter_bound
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    (hfull : ∀ i (si : G.Strategy i),
      (G.recommendationDevice μ B hB).PositiveSignal i si)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    (G.recommendationDevice μ B hB).InterimWeaklyStrictlyDominantExpectedKImplementsDistribution
      (G.obedientDeviceStrategy) μ 0 :=
  (G.recommendationDevice_obedient_strictInterimDominantKImplDist_of_eu_diameter_bound
    hce hB hdiam hbonus_weak hbonus_strict hfull hopponent).toExpected

/-- In the compiled recommendation-device game, full-support strict interim
dominance leaves exactly the obedient signal-contingent profile undominated. -/
theorem recommendationDevice_undominatedProfiles_eq_singleton_obedient_of_eu_diameter_bound
    [DecidableEq ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    (hfull : ∀ i (si : G.Strategy i),
      (G.recommendationDevice μ B hB).PositiveSignal i si)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    (G.recommendationDevice μ B hB).deviceGame.undominatedProfiles =
      ({G.obedientDeviceStrategy} :
        Set (Profile (G.recommendationDevice μ B hB).deviceGame)) := by
  classical
  let I := G.recommendationDevice μ B hB
  haveI : Finite (∀ k, I.Signal k) := by
    change Finite (Profile G)
    infer_instance
  have hstrict :
      I.InterimWeaklyStrictlyDominantProfile G.obedientDeviceStrategy :=
    G.recommendationDevice_obedient_strictInterimDominantProfile_of_eu_diameter_bound
      hce hB hdiam hbonus_weak hbonus_strict hfull hopponent
  have hweak : I.InterimDominantProfile G.obedientDeviceStrategy :=
    hstrict.interimDominantProfile (G := G) (I := I)
  apply Set.Subset.antisymm
  · intro b hb
    refine Set.mem_singleton_iff.mpr ?_
    funext i si
    by_contra hne
    have hrule_ne : b i ≠ G.obedientDeviceStrategy i := by
      intro hrule
      exact hne (by
        simpa [obedientDeviceStrategy] using congrFun hrule si)
    have hinterim :
        I.InterimWeaklyStrictlyDominates i
          (G.obedientDeviceStrategy i) (b i) :=
      hstrict i (b i) hrule_ne
    have hdom :
        I.deviceGame.WeaklyStrictlyDominates i
          (G.obedientDeviceStrategy i) (b i) :=
      hinterim.toWeaklyStrictlyDominates (G := G) (I := I)
    exact hb i (G.obedientDeviceStrategy i) hdom
  · intro b hb
    have hb_obedient : b = G.obedientDeviceStrategy :=
      Set.mem_singleton_iff.mp hb
    rw [hb_obedient]
    exact hweak.mem_undominatedProfiles (G := G) (I := I)

/-- Without full support, the strict recommendation-device hypotheses identify
the compiled device game's undominated profiles exactly up to null
recommendations: a surviving signal-contingent rule must agree with obedience
on every positive-probability recommendation, and arbitrary behavior at
zero-probability recommendations is payoff-equivalent. -/
theorem recommendationDevice_undominatedProfiles_eq_supported_obedient_class
    [DecidableEq ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    (G.recommendationDevice μ B hB).deviceGame.undominatedProfiles =
      {b : Profile (G.recommendationDevice μ B hB).deviceGame |
        ∀ i (si : G.Strategy i),
          (G.recommendationDevice μ B hB).PositiveSignal i si →
            b i si = si} := by
  classical
  let I := G.recommendationDevice μ B hB
  haveI : Finite (∀ k, I.Signal k) := by
    change Finite (Profile G)
    infer_instance
  have hweak : I.InterimDominantProfile G.obedientDeviceStrategy :=
    G.recommendationDevice_obedient_interimDominantProfile_of_eu_diameter_bound
      hce hB hdiam hbonus_weak
  rw [hweak.undominatedProfiles_eq_utilityEquivalentClass (G := G) (I := I)]
  ext b
  constructor
  · intro hb i si hsi
    by_contra hne
    have hdiff : ∃ si : G.Strategy i, I.PositiveSignal i si ∧ b i si ≠ si :=
      ⟨si, hsi, hne⟩
    have hinterim :
        I.InterimWeaklyStrictlyDominates i (G.obedientDeviceStrategy i) (b i) :=
      G.recommendationDevice_obedient_interimWeaklyStrictlyDominates_of_diff_on_positive
        hce hB hdiam hbonus_weak hbonus_strict hopponent hdiff
    have hdom :
        I.deviceGame.WeaklyStrictlyDominates i
          (G.obedientDeviceStrategy i) (b i) :=
      hinterim.toWeaklyStrictlyDominates (G := G) (I := I)
    obtain ⟨β, hβ⟩ := hdom.strict_witness
    have heq := (hb i).symm β
    linarith
  · intro hb i
    apply I.deviceGame_utilityEquivalent_of_eq_on_positive_signals
    intro si hsi
    simpa [obedientDeviceStrategy] using hb i si hsi

/-- Standard exact-implementation form of the strict recommendation-device
capstone: in the compiled device game, zero additional profile-observed
transfers exactly implement the obedient signal-contingent profile. -/
theorem recommendationDevice_obedient_zeroTransfer_exactKImplementation_of_eu_diameter_bound
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    (hfull : ∀ i (si : G.Strategy i),
      (G.recommendationDevice μ B hB).PositiveSignal i si)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    (G.recommendationDevice μ B hB).deviceGame.IsExactKImplementation
      (fun _ _ => 0)
      ({G.obedientDeviceStrategy} :
        Set (Profile (G.recommendationDevice μ B hB).deviceGame)) 0 := by
  classical
  let I := G.recommendationDevice μ B hB
  haveI : Finite I.deviceGame.Outcome := by
    change Finite ((∀ i, I.Signal i) × Profile G × G.Outcome)
    infer_instance
  change I.deviceGame.IsExactKImplementation (fun _ _ => 0)
    ({G.obedientDeviceStrategy} : Set (Profile I.deviceGame)) 0
  exact I.deviceGame.zeroTransfer_isExactKImplementation_of_undominatedProfiles_eq
    (G.recommendationDevice_undominatedProfiles_eq_singleton_obedient_of_eu_diameter_bound
      hce hB hdiam hbonus_weak hbonus_strict hfull hopponent)

/-- Distributional form of the recommendation-device theorem: with a sufficiently
large obedience bonus, the obedient strategy profile interim-dominantly
implements the correlated-equilibrium law. -/
theorem recommendationDevice_obedient_interimDominantImplementsDistribution_of_eu_diameter_bound
    [DecidableEq ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus : 2 * M ≤ B) :
    (G.recommendationDevice μ B hB).InterimDominantImplementsDistribution
      (G.obedientDeviceStrategy) μ :=
  ⟨G.recommendationDevice_obedient_interimDominantProfile_of_eu_diameter_bound
      hce hB hdiam hbonus,
    G.recommendationDevice_implementsDistribution_obedient μ B hB⟩

/-- Zero-cost form of the recommendation-device theorem. Transfers are zero
on every obediently realized signal profile, so the device implements the target
law at cost `0` even though the off-path bonus may be large. -/
theorem recommendationDevice_obedient_interimDominantKImplementsDistribution_of_eu_diameter_bound
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus : 2 * M ≤ B) :
    (G.recommendationDevice μ B hB).InterimDominantKImplementsDistribution
      (G.obedientDeviceStrategy) μ 0 := by
  refine ⟨
    G.recommendationDevice_obedient_interimDominantImplementsDistribution_of_eu_diameter_bound
      hce hB hdiam hbonus, ?_⟩
  intro θ _hθ
  simp

/-- Expected-cost form of the recommendation-device theorem.  This is a
corollary of the stronger pointwise zero-cost statement. -/
theorem recommendationDevice_obedient_interimDominantExpectedKImplDist_of_eu_diameter_bound
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus : 2 * M ≤ B) :
    (G.recommendationDevice μ B hB).InterimDominantExpectedKImplementsDistribution
      (G.obedientDeviceStrategy) μ 0 :=
  (G.recommendationDevice_obedient_interimDominantKImplementsDistribution_of_eu_diameter_bound
    hce hB hdiam hbonus).toExpected

/-- Closing-remark form of the recommendation-device theorem: obedient
signal-contingent strategies remain dominant against mixed deviations in the
mixed extension of the compiled device game. -/
theorem recommendationDevice_obedient_mixedDominantProfile_of_eu_diameter_bound
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus : 2 * M ≤ B) :
    ∀ i, (G.recommendationDevice μ B hB).deviceGame.mixedExtension.IsDominant i
      (PMF.pure (G.obedientDeviceStrategy i)) := by
  classical
  let I := G.recommendationDevice μ B hB
  have hprofile :
      I.InterimDominantProfile G.obedientDeviceStrategy :=
    G.recommendationDevice_obedient_interimDominantProfile_of_eu_diameter_bound
      hce hB hdiam hbonus
  exact hprofile.isDominantMixedProfile (G := G) (I := I)

/-- Strict closing-remark form of the recommendation-device theorem: under the
strict device hypotheses, each obedient point mass weakly-strictly dominates
every distinct mixed signal-contingent rule in the mixed extension of the
compiled device game. -/
theorem recommendationDevice_obedient_mixedWeaklyStrictlyDominantProfile_of_eu_diameter_bound
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    {M B : ℝ} (hB : 0 ≤ B)
    (hdiam : G.EuDiameterBound M)
    (hbonus_weak : 2 * M ≤ B) (hbonus_strict : M < B)
    (hfull : ∀ i (si : G.Strategy i),
      (G.recommendationDevice μ B hB).PositiveSignal i si)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    ∀ i (τ : PMF ((G.recommendationDevice μ B hB).deviceGame.Strategy i)),
      τ ≠ PMF.pure (G.obedientDeviceStrategy i) →
        KernelGame.WeaklyStrictlyDominates
          ((G.recommendationDevice μ B hB).deviceGame.mixedExtension)
          i (PMF.pure (G.obedientDeviceStrategy i)) τ := by
  classical
  let I := G.recommendationDevice μ B hB
  have hprofile :
      I.InterimWeaklyStrictlyDominantProfile G.obedientDeviceStrategy :=
    G.recommendationDevice_obedient_strictInterimDominantProfile_of_eu_diameter_bound
      hce hB hdiam hbonus_weak hbonus_strict hfull hopponent
  exact hprofile.toWeaklyStrictlyDominates_mixedExtension (G := G) (I := I)

/-- Paper-shaped existence theorem for correlated equilibria: every correlated
equilibrium law has a recommendation device, with signal spaces equal to the
base strategy spaces and law equal to the correlated distribution, that
interim-dominantly implements the law at cost `0`. The proof chooses an
explicitly large enough off-path obedience bonus from a finite bound on
expected-utility diameters. -/
theorem exists_recommendationDevice_interimDominantKImplementsDistribution
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.recommendationDevice μ B hB).InterimDominantKImplementsDistribution
        (G.obedientDeviceStrategy) μ 0 := by
  classical
  obtain ⟨M, hMrange⟩ :
      BddAbove
        (Set.range fun p : ι × Profile G × Profile G =>
          G.eu p.2.1 p.1 - G.eu p.2.2 p.1) :=
    Finite.bddAbove_range fun p : ι × Profile G × Profile G =>
      G.eu p.2.1 p.1 - G.eu p.2.2 p.1
  let B : ℝ := max 0 (2 * M)
  have hB : 0 ≤ B := le_max_left 0 (2 * M)
  have hbonus : 2 * M ≤ B := le_max_right 0 (2 * M)
  have hdiam : G.EuDiameterBound M := by
    intro i σ τ
    exact hMrange ⟨(i, σ, τ), rfl⟩
  exact ⟨B, hB,
    G.recommendationDevice_obedient_interimDominantKImplementsDistribution_of_eu_diameter_bound
      hce hB hdiam hbonus⟩

/-- Expected-cost version of the correlated-equilibrium recommendation-device
existence theorem. -/
theorem exists_recommendationDevice_interimDominantExpectedKImplementsDistribution
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.recommendationDevice μ B hB).InterimDominantExpectedKImplementsDistribution
        (G.obedientDeviceStrategy) μ 0 := by
  rcases G.exists_recommendationDevice_interimDominantKImplementsDistribution hce with
    ⟨B, hB, himpl⟩
  exact ⟨B, hB, himpl.toExpected⟩

/-- Arbitrary finite distributions have an expected-cost implementation by the
regret-paying recommendation device.  The cost is the sum of maximum swap
regrets; the off-path obedience bonus is chosen from a finite expected-utility
diameter bound and contributes zero on the obedient path. -/
theorem exists_regretRecommendationDevice_interimDominantExpectedKImplDist
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, DecidableEq (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.regretRecommendationDevice μ B hB).InterimDominantExpectedKImplementsDistribution
        (G.obedientDeviceStrategy) μ
        (∑ i, G.maxSwapRegret μ i) := by
  classical
  obtain ⟨M, hMrange⟩ :
      BddAbove
        (Set.range fun p : ι × Profile G × Profile G =>
          G.eu p.2.1 p.1 - G.eu p.2.2 p.1) :=
    Finite.bddAbove_range fun p : ι × Profile G × Profile G =>
      G.eu p.2.1 p.1 - G.eu p.2.2 p.1
  let B : ℝ := max 0 (2 * M)
  have hB : 0 ≤ B := le_max_left 0 (2 * M)
  have hbonus : 2 * M ≤ B := le_max_right 0 (2 * M)
  have hdiam : G.EuDiameterBound M := by
    intro i σ τ
    exact hMrange ⟨(i, σ, τ), rfl⟩
  exact ⟨B, hB,
    G.regretRecommendationDevice_obedient_interimDominantExpectedKImplDist
      hB hdiam hbonus⟩

/-- Expected-cost revelation principle for deterministic finite-signal
devices: any finite-signal expected implementation can be matched, within the
same budget, by the regret-paying recommendation device. -/
theorem exists_regretRecommendationDevice_expectedKImplDist_of_finiteDevice
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {I : G.ImplementationDevice}
    [Finite (∀ i, I.Signal i)] [∀ i, Finite (I.Signal i)]
    {b : ∀ i, I.Signal i → G.Strategy i} {μ : PMF (Profile G)} {k : ℝ}
    (h : I.InterimDominantExpectedKImplementsDistribution b μ k) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.regretRecommendationDevice μ B hB).InterimDominantExpectedKImplementsDistribution
        (G.obedientDeviceStrategy) μ k := by
  classical
  have hsum : ∑ i, G.maxSwapRegret μ i ≤ k :=
    I.sum_maxSwapRegret_le_of_expectedKImplementation h
  rcases G.exists_regretRecommendationDevice_interimDominantExpectedKImplDist μ with
    ⟨B, hB, hrec⟩
  exact ⟨B, hB, ⟨hrec.1, hrec.2.trans hsum⟩⟩

theorem sum_maxSwapRegret_mem_finiteExpectedDeviceImplementationCosts
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, DecidableEq (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    (∑ i, G.maxSwapRegret μ i) ∈
      G.finiteExpectedDeviceImplementationCosts μ := by
  classical
  rcases G.exists_regretRecommendationDevice_interimDominantExpectedKImplDist μ with
    ⟨B, hB, hK⟩
  refine ⟨G.regretRecommendationDevice μ B hB, G.obedientDeviceStrategy, ?_, ?_, hK⟩
  · change Finite (Profile G)
    infer_instance
  · intro i
    change Finite (G.Strategy i)
    infer_instance

theorem finiteExpectedDeviceImplementationCosts_nonempty
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    (G.finiteExpectedDeviceImplementationCosts μ).Nonempty := by
  classical
  letI : (i : ι) → Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  exact ⟨∑ i, G.maxSwapRegret μ i,
    G.sum_maxSwapRegret_mem_finiteExpectedDeviceImplementationCosts μ⟩

theorem sum_maxSwapRegret_le_finiteExpectedDeviceImplPrice
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, DecidableEq (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    (∑ i, G.maxSwapRegret μ i) ≤ G.finiteExpectedDeviceImplPrice μ := by
  classical
  rw [finiteExpectedDeviceImplPrice]
  exact le_csInf (G.finiteExpectedDeviceImplementationCosts_nonempty μ) fun k hk => by
    rcases hk with ⟨I, b, hSig, hEach, hK⟩
    letI : Finite (∀ i, I.Signal i) := hSig
    letI : ∀ i, Finite (I.Signal i) := hEach
    exact I.sum_maxSwapRegret_le_of_expectedKImplementation hK

theorem finiteExpectedDeviceImplPrice_le_sum_maxSwapRegret
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, DecidableEq (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.finiteExpectedDeviceImplPrice μ ≤ ∑ i, G.maxSwapRegret μ i := by
  exact csInf_le (G.finiteExpectedDeviceImplementationCosts_bddBelow μ)
    (G.sum_maxSwapRegret_mem_finiteExpectedDeviceImplementationCosts μ)

/-- Expected device price is exactly total maximum swap regret. -/
theorem finiteExpectedDeviceImplPrice_eq_sum_maxSwapRegret
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, DecidableEq (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.finiteExpectedDeviceImplPrice μ = ∑ i, G.maxSwapRegret μ i :=
  le_antisymm (G.finiteExpectedDeviceImplPrice_le_sum_maxSwapRegret μ)
    (G.sum_maxSwapRegret_le_finiteExpectedDeviceImplPrice μ)

theorem finiteExpectedDeviceImplPrice_le_card_mul_of_isεCorrelatedEq
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)} {ε : ℝ} (hε : G.IsεCorrelatedEq ε μ) :
    G.finiteExpectedDeviceImplPrice μ ≤ (Fintype.card ι : ℝ) * ε := by
  classical
  letI : (i : ι) → Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  rw [G.finiteExpectedDeviceImplPrice_eq_sum_maxSwapRegret μ]
  rw [G.isεCorrelatedEq_iff_swapRegret_le] at hε
  calc
    (∑ i, G.maxSwapRegret μ i)
        ≤ ∑ _i : ι, ε := by
          refine Finset.sum_le_sum ?_
          intro i _
          apply Finset.sup'_le
          intro dev _
          exact hε i dev
    _ = (Fintype.card ι : ℝ) * ε := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

theorem isεCorrelatedEq_of_finiteExpectedDeviceImplPrice_le
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)} {ε : ℝ}
    (hprice : G.finiteExpectedDeviceImplPrice μ ≤ ε) :
    G.IsεCorrelatedEq ε μ := by
  classical
  letI : (i : ι) → Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  rw [G.isεCorrelatedEq_iff_swapRegret_le]
  intro i dev
  calc
    G.swapRegret μ i dev ≤ G.maxSwapRegret μ i :=
      G.swapRegret_le_maxSwapRegret μ i dev
    _ ≤ ∑ j, G.maxSwapRegret μ j :=
      Finset.single_le_sum
        (fun j _ => G.maxSwapRegret_nonneg μ j)
        (Finset.mem_univ i)
    _ = G.finiteExpectedDeviceImplPrice μ := by
      rw [G.finiteExpectedDeviceImplPrice_eq_sum_maxSwapRegret μ]
    _ ≤ ε := hprice

theorem isCorrelatedEq_iff_finiteExpectedDeviceImplPrice_le_zero
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)} :
    G.IsCorrelatedEq μ ↔ G.finiteExpectedDeviceImplPrice μ ≤ 0 := by
  classical
  letI : (i : ι) → Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  constructor
  · intro hce
    rw [G.isCorrelatedEq_iff_isεCorrelatedEq_zero] at hce
    simpa using
      G.finiteExpectedDeviceImplPrice_le_card_mul_of_isεCorrelatedEq
        (μ := μ) hce
  · intro hprice
    rw [G.isCorrelatedEq_iff_isεCorrelatedEq_zero]
    exact G.isεCorrelatedEq_of_finiteExpectedDeviceImplPrice_le hprice

/-- Arbitrary finite distributions have a pointwise-cost implementation by the
regret-paying recommendation device.  The pointwise budget is the largest
supported realized sum of conditional swap regrets. -/
theorem exists_regretRecommendationDevice_interimDominantKImplDist
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.regretRecommendationDevice μ B hB).InterimDominantKImplementsDistribution
        (G.obedientDeviceStrategy) μ
        (G.maxSupportedPointwiseConditionalSwapRegret μ) := by
  classical
  obtain ⟨M, hMrange⟩ :
      BddAbove
        (Set.range fun p : ι × Profile G × Profile G =>
          G.eu p.2.1 p.1 - G.eu p.2.2 p.1) :=
    Finite.bddAbove_range fun p : ι × Profile G × Profile G =>
      G.eu p.2.1 p.1 - G.eu p.2.2 p.1
  let B : ℝ := max 0 (2 * M)
  have hB : 0 ≤ B := le_max_left 0 (2 * M)
  have hbonus : 2 * M ≤ B := le_max_right 0 (2 * M)
  have hdiam : G.EuDiameterBound M := by
    intro i σ τ
    exact hMrange ⟨(i, σ, τ), rfl⟩
  exact ⟨B, hB,
    G.regretRecommendationDevice_obedient_interimDominantKImplDist
      hB hdiam hbonus⟩

theorem maxSupportedPointwiseConditionalSwapRegret_mem_recommendationDevicePointwiseCosts
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.maxSupportedPointwiseConditionalSwapRegret μ ∈
      G.recommendationDevicePointwiseImplementationCosts μ := by
  classical
  rcases G.exists_regretRecommendationDevice_interimDominantKImplDist μ with
    ⟨B, hB, hK⟩
  exact ⟨G.regretRecommendationTransfer μ B,
    G.regretRecommendationTransfer_nonneg μ hB, hK⟩

theorem maxSupportedPointwiseConditionalSwapRegret_mem_recommendationPaymentCosts
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.maxSupportedPointwiseConditionalSwapRegret μ ∈
      G.recommendationPaymentImplementationCosts μ := by
  have h :=
    G.maxSupportedPointwiseConditionalSwapRegret_mem_recommendationDevicePointwiseCosts μ
  rwa [G.recommendationDevicePointwiseImplementationCosts_eq_recommendationPaymentCosts μ] at h

theorem recommendationPaymentImplementationCosts_nonempty
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    (G.recommendationPaymentImplementationCosts μ).Nonempty := by
  classical
  letI : (i : ι) → Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  exact ⟨G.maxSupportedPointwiseConditionalSwapRegret μ,
    G.maxSupportedPointwiseConditionalSwapRegret_mem_recommendationPaymentCosts μ⟩

theorem maxConditionalSwapRegret_le_recommendationDevicePointwiseImplPrice
    [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.maxConditionalSwapRegret μ ≤
      G.recommendationDevicePointwiseImplPrice μ := by
  classical
  have hcosts_nonempty :
      (G.recommendationDevicePointwiseImplementationCosts μ).Nonempty :=
    ⟨G.maxSupportedPointwiseConditionalSwapRegret μ,
      G.maxSupportedPointwiseConditionalSwapRegret_mem_recommendationDevicePointwiseCosts μ⟩
  rw [recommendationDevicePointwiseImplPrice]
  exact le_csInf hcosts_nonempty fun k hk =>
    G.maxConditionalSwapRegret_le_of_recommendationDevicePointwiseCost hk

theorem recommendationDevicePointwiseImplPrice_le_maxSupportedPointwiseConditionalSwapRegret
    [DecidableEq ι] [Fintype ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.recommendationDevicePointwiseImplPrice μ ≤
      G.maxSupportedPointwiseConditionalSwapRegret μ := by
  exact csInf_le (G.recommendationDevicePointwiseImplementationCosts_bddBelow μ)
    (G.maxSupportedPointwiseConditionalSwapRegret_mem_recommendationDevicePointwiseCosts μ)

theorem recommendationDevicePointwiseImplPrice_sandwich
    [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.maxConditionalSwapRegret μ ≤
        G.recommendationDevicePointwiseImplPrice μ ∧
      G.recommendationDevicePointwiseImplPrice μ ≤
        G.maxSupportedPointwiseConditionalSwapRegret μ :=
  ⟨G.maxConditionalSwapRegret_le_recommendationDevicePointwiseImplPrice μ,
    G.recommendationDevicePointwiseImplPrice_le_maxSupportedPointwiseConditionalSwapRegret μ⟩

theorem maxConditionalSwapRegret_le_recommendationPaymentImplPrice
    [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.maxConditionalSwapRegret μ ≤
      G.recommendationPaymentImplPrice μ := by
  have h := G.maxConditionalSwapRegret_le_recommendationDevicePointwiseImplPrice μ
  rwa [G.recommendationDevicePointwiseImplPrice_eq_recommendationPaymentImplPrice μ] at h

theorem recommendationPaymentImplPrice_le_maxSupportedPointwiseConditionalSwapRegret
    [DecidableEq ι] [Fintype ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.recommendationPaymentImplPrice μ ≤
      G.maxSupportedPointwiseConditionalSwapRegret μ :=
  G.recommendationPaymentImplPrice_le_of_mem
    (G.maxSupportedPointwiseConditionalSwapRegret_mem_recommendationPaymentCosts μ)

theorem recommendationPaymentImplPrice_sandwich
    [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.maxConditionalSwapRegret μ ≤
        G.recommendationPaymentImplPrice μ ∧
      G.recommendationPaymentImplPrice μ ≤
        G.maxSupportedPointwiseConditionalSwapRegret μ :=
  ⟨G.maxConditionalSwapRegret_le_recommendationPaymentImplPrice μ,
    G.recommendationPaymentImplPrice_le_maxSupportedPointwiseConditionalSwapRegret μ⟩

/-- Any finite-signal pointwise implementation gives a lower bound on the
pointwise budget in terms of the target law's maximum conditional swap regret. -/
theorem maxConditionalSwapRegret_le_of_finitePointwiseDeviceCost
    [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {μ : PMF (Profile G)} {k : ℝ}
    (hk : k ∈ G.finitePointwiseDeviceImplementationCosts μ) :
    G.maxConditionalSwapRegret μ ≤ k := by
  classical
  rcases hk with ⟨I, b, hSig, hEach, hK⟩
  letI : Finite (∀ i, I.Signal i) := hSig
  letI : ∀ i, Finite (I.Signal i) := hEach
  unfold maxConditionalSwapRegret
  apply Finset.sup'_le
  intro i _
  apply Finset.sup'_le
  intro si _
  exact I.conditionalSwapRegret_le_of_interimDominantKImplDist hK i si

/-- Recommendation-device pointwise feasible budgets are feasible for the
larger class of arbitrary finite-signal deterministic devices. -/
theorem recommendationDevicePointwiseCost_subset_finitePointwiseDeviceCost
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} {k : ℝ}
    (hk : k ∈ G.recommendationDevicePointwiseImplementationCosts μ) :
    k ∈ G.finitePointwiseDeviceImplementationCosts μ := by
  classical
  rcases hk with ⟨T, hT, hK⟩
  refine ⟨G.transferRecommendationDevice μ T hT, G.obedientDeviceStrategy, ?_, ?_, hK⟩
  · change Finite (Profile G)
    infer_instance
  · intro i
    change Finite (G.Strategy i)
    infer_instance

/-- Pointwise implementation by an arbitrary finite-signal deterministic device
can be pooled into a feasible recommendation-payment LP solution with the same
budget. -/
theorem finitePointwiseDeviceCost_subset_recommendationPaymentCost
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    {μ : PMF (Profile G)} {k : ℝ}
    (hk : k ∈ G.finitePointwiseDeviceImplementationCosts μ) :
    k ∈ G.recommendationPaymentImplementationCosts μ := by
  classical
  rcases hk with ⟨I, b, hSig, hEach, hK⟩
  letI : Finite (∀ i, I.Signal i) := hSig
  letI : ∀ i, Finite (I.Signal i) := hEach
  exact ⟨ImplementationDevice.pooledRecommendationPayment (G := G) I b,
    ImplementationDevice.pooledRecommendationPayment_feasible_of_interimDominantKImplDist
      (G := G) I hK⟩

/-- Revelation-principle equality for pointwise device budgets: arbitrary
finite-signal devices have exactly the same feasible pointwise costs as the
recommendation-payment LP. -/
theorem finitePointwiseDeviceImplementationCosts_eq_recommendationPaymentCosts
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.finitePointwiseDeviceImplementationCosts μ =
      G.recommendationPaymentImplementationCosts μ := by
  ext k
  constructor
  · exact G.finitePointwiseDeviceCost_subset_recommendationPaymentCost
  · intro hk
    exact G.recommendationDevicePointwiseCost_subset_finitePointwiseDeviceCost
      (G.recommendationPaymentCost_subset_recommendationDevicePointwiseCost hk)

/-- Pointwise price equality for arbitrary finite devices and the exact
recommendation-payment LP. -/
theorem finitePointwiseDeviceImplPrice_eq_recommendationPaymentImplPrice
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.finitePointwiseDeviceImplPrice μ =
      G.recommendationPaymentImplPrice μ := by
  rw [finitePointwiseDeviceImplPrice, recommendationPaymentImplPrice,
    G.finitePointwiseDeviceImplementationCosts_eq_recommendationPaymentCosts μ]

/-- Arbitrary finite devices and recommendation devices have the same
pointwise implementation price. -/
theorem finitePointwiseDeviceImplPrice_eq_recommendationDevicePointwiseImplPrice
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.finitePointwiseDeviceImplPrice μ =
      G.recommendationDevicePointwiseImplPrice μ := by
  calc
    G.finitePointwiseDeviceImplPrice μ =
        G.recommendationPaymentImplPrice μ :=
      G.finitePointwiseDeviceImplPrice_eq_recommendationPaymentImplPrice μ
    _ = G.recommendationDevicePointwiseImplPrice μ :=
      (G.recommendationDevicePointwiseImplPrice_eq_recommendationPaymentImplPrice μ).symm

theorem finitePointwiseDeviceImplementationCosts_nonempty
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    (G.finitePointwiseDeviceImplementationCosts μ).Nonempty := by
  classical
  letI : (i : ι) → Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  exact ⟨G.maxSupportedPointwiseConditionalSwapRegret μ,
    G.recommendationDevicePointwiseCost_subset_finitePointwiseDeviceCost
      (G.maxSupportedPointwiseConditionalSwapRegret_mem_recommendationDevicePointwiseCosts μ)⟩

theorem maxConditionalSwapRegret_le_finitePointwiseDeviceImplPrice
    [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.maxConditionalSwapRegret μ ≤ G.finitePointwiseDeviceImplPrice μ := by
  classical
  rw [finitePointwiseDeviceImplPrice]
  exact le_csInf (G.finitePointwiseDeviceImplementationCosts_nonempty μ) fun k hk =>
    G.maxConditionalSwapRegret_le_of_finitePointwiseDeviceCost hk

theorem finitePointwiseDeviceImplPrice_le_recommendationDevicePointwiseImplPrice
    [DecidableEq ι] [Fintype ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.finitePointwiseDeviceImplPrice μ ≤ G.recommendationDevicePointwiseImplPrice μ := by
  classical
  letI : (i : ι) → Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  rw [recommendationDevicePointwiseImplPrice]
  exact le_csInf
    ⟨G.maxSupportedPointwiseConditionalSwapRegret μ,
      G.maxSupportedPointwiseConditionalSwapRegret_mem_recommendationDevicePointwiseCosts μ⟩
    fun k hk =>
      csInf_le (G.finitePointwiseDeviceImplementationCosts_bddBelow μ)
        (G.recommendationDevicePointwiseCost_subset_finitePointwiseDeviceCost hk)

theorem finitePointwiseDeviceImplPrice_sandwich
    [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G)) :
    G.maxConditionalSwapRegret μ ≤ G.finitePointwiseDeviceImplPrice μ ∧
      G.finitePointwiseDeviceImplPrice μ ≤
        G.recommendationDevicePointwiseImplPrice μ := by
  classical
  exact
    ⟨G.maxConditionalSwapRegret_le_finitePointwiseDeviceImplPrice μ,
      G.finitePointwiseDeviceImplPrice_le_recommendationDevicePointwiseImplPrice μ⟩

/-- Exact pointwise recommendation-device price in the degenerate LP case where
no supported recommendation profile accumulates more total conditional regret
than the largest one-signal conditional regret. -/
theorem recommendationDevicePointwiseImplPrice_eq_maxConditionalSwapRegret_of_supported_sum_le
    [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G))
    (h :
      ∀ θ : Profile G, μ θ ≠ 0 →
        (∑ i, G.conditionalSwapRegret μ i (θ i)) ≤
          G.maxConditionalSwapRegret μ) :
    G.recommendationDevicePointwiseImplPrice μ =
      G.maxConditionalSwapRegret μ := by
  classical
  apply le_antisymm
  · have hupper :
        G.maxSupportedPointwiseConditionalSwapRegret μ ≤
          G.maxConditionalSwapRegret μ := by
      unfold maxSupportedPointwiseConditionalSwapRegret
      apply Finset.sup'_le
      intro θ hθ
      exact h θ (Finset.mem_filter.mp hθ).2
    exact
      (G.recommendationDevicePointwiseImplPrice_le_maxSupportedPointwiseConditionalSwapRegret
        μ).trans hupper
  · exact G.maxConditionalSwapRegret_le_recommendationDevicePointwiseImplPrice μ

theorem recommendationPaymentImplPrice_eq_maxConditionalSwapRegret_of_supported_sum_le
    [DecidableEq ι] [Fintype ι] [Nonempty ι]
    [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (μ : PMF (Profile G))
    (h :
      ∀ θ : Profile G, μ θ ≠ 0 →
        (∑ i, G.conditionalSwapRegret μ i (θ i)) ≤
          G.maxConditionalSwapRegret μ) :
    G.recommendationPaymentImplPrice μ =
      G.maxConditionalSwapRegret μ := by
  rw [← G.recommendationDevicePointwiseImplPrice_eq_recommendationPaymentImplPrice μ]
  exact G.recommendationDevicePointwiseImplPrice_eq_maxConditionalSwapRegret_of_supported_sum_le
    μ h

private theorem exists_recommendationDevice_strictParameters
    [Finite ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)}
    (hfull : ∀ i (si : G.Strategy i),
      pmfMass (μ := μ) (fun θ : Profile G => θ i = si) ≠ 0) :
    ∃ (M B : ℝ) (hB : 0 ≤ B),
      G.EuDiameterBound M ∧
        2 * M ≤ B ∧
          M < B ∧
            ∀ i (si : G.Strategy i),
              (G.recommendationDevice μ B hB).PositiveSignal i si := by
  classical
  obtain ⟨M, hMrange⟩ :
      BddAbove
        (Set.range fun p : ι × Profile G × Profile G =>
          G.eu p.2.1 p.1 - G.eu p.2.2 p.1) :=
    Finite.bddAbove_range fun p : ι × Profile G × Profile G =>
      G.eu p.2.1 p.1 - G.eu p.2.2 p.1
  let B : ℝ := max 0 (2 * M) + 1
  have hB : 0 ≤ B := by
    have hmax : 0 ≤ max 0 (2 * M) := le_max_left 0 (2 * M)
    linarith
  have hbonus_weak : 2 * M ≤ B := by
    have hmax : 2 * M ≤ max 0 (2 * M) := le_max_right 0 (2 * M)
    linarith
  have hbonus_strict : M < B := by
    have hmax0 : 0 ≤ max 0 (2 * M) := le_max_left 0 (2 * M)
    have hmax2 : 2 * M ≤ max 0 (2 * M) := le_max_right 0 (2 * M)
    nlinarith
  have hdiam : G.EuDiameterBound M := by
    intro i σ τ
    exact hMrange ⟨(i, σ, τ), rfl⟩
  have hfullDevice : ∀ i (si : G.Strategy i),
      (G.recommendationDevice μ B hB).PositiveSignal i si := by
    intro i si
    simpa [ImplementationDevice.PositiveSignal] using hfull i si
  exact ⟨M, B, hB, hdiam, hbonus_weak, hbonus_strict, hfullDevice⟩

/-- Strict paper-shaped existence theorem for correlated equilibria. If every
recommendation has positive marginal probability and every player has an
opponent able to disobey each recommendation, the same recommendation device
strictly interim-dominantly implements the law at cost `0`. -/
theorem exists_recommendationDevice_strictInterimDominantKImplementsDistribution
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    (hfull : ∀ i (si : G.Strategy i),
      pmfMass (μ := μ) (fun θ : Profile G => θ i = si) ≠ 0)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.recommendationDevice μ B hB).InterimWeaklyStrictlyDominantKImplementsDistribution
        (G.obedientDeviceStrategy) μ 0 := by
  obtain ⟨M, B, hB, hdiam, hbonus_weak, hbonus_strict, hfullDevice⟩ :=
    exists_recommendationDevice_strictParameters (G := G) hfull
  exact ⟨B, hB,
    G.recommendationDevice_obedient_strictInterimDominantKImplDist_of_eu_diameter_bound
      hce hB hdiam hbonus_weak hbonus_strict hfullDevice hopponent⟩

/-- Expected-cost version of the strict recommendation-device existence
theorem. -/
theorem exists_recommendationDevice_strictInterimDominantExpectedKImplementsDistribution
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    (hfull : ∀ i (si : G.Strategy i),
      pmfMass (μ := μ) (fun θ : Profile G => θ i = si) ≠ 0)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.recommendationDevice μ B hB).InterimWeaklyStrictlyDominantExpectedKImplementsDistribution
        (G.obedientDeviceStrategy) μ 0 := by
  rcases G.exists_recommendationDevice_strictInterimDominantKImplementsDistribution
      hce hfull hopponent with
    ⟨B, hB, himpl⟩
  exact ⟨B, hB, himpl.toExpected⟩

/-- Strict exact-implementation existence theorem for the compiled
recommendation device. Under full support and nontrivial opponents, some
obedience bonus makes zero additional profile-observed transfers exactly
implement the obedient signal-contingent profile. -/
theorem exists_recommendationDevice_obedient_zeroTransfer_exactKImplementation
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {μ : PMF (Profile G)} (hce : G.IsCorrelatedEq μ)
    (hfull : ∀ i (si : G.Strategy i),
      pmfMass (μ := μ) (fun θ : Profile G => θ i = si) ≠ 0)
    (hopponent : ∀ i, ∃ j : ι, j ≠ i ∧
      ∀ sj : G.Strategy j, ∃ a : G.Strategy j, a ≠ sj) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.recommendationDevice μ B hB).deviceGame.IsExactKImplementation
        (fun _ _ => 0)
        ({G.obedientDeviceStrategy} :
          Set (Profile (G.recommendationDevice μ B hB).deviceGame)) 0 := by
  obtain ⟨M, B, hB, hdiam, hbonus_weak, hbonus_strict, hfullDevice⟩ :=
    exists_recommendationDevice_strictParameters (G := G) hfull
  exact ⟨B, hB,
    G.recommendationDevice_obedient_zeroTransfer_exactKImplementation_of_eu_diameter_bound
      hce hB hdiam hbonus_weak hbonus_strict hfullDevice hopponent⟩

/-- Paper-shaped mixed-equilibrium device theorem. A mixed Nash profile induces
a correlated-equilibrium product law, so the correlated-equilibrium
recommendation device implements that product law at cost `0`. -/
theorem exists_recommendationDevice_interimDominantKImplementsDistribution_of_mixedNash
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    (p : Profile G.mixedExtension) (hN : G.mixedExtension.IsNash p) :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.recommendationDevice (Math.PMFProduct.pmfPi p) B hB).InterimDominantKImplementsDistribution
        (G.obedientDeviceStrategy) (Math.PMFProduct.pmfPi p) 0 :=
  G.exists_recommendationDevice_interimDominantKImplementsDistribution
    (G.mixed_nash_isCorrelatedEq p hN)

/-- Expected-cost version of the mixed-equilibrium device theorem. -/
theorem exists_recommendationDevice_interimDominantExpectedKImplDist_of_mixedNash
    [DecidableEq ι] [Fintype ι] [Finite (Profile G)] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    (p : Profile G.mixedExtension) (hN : G.mixedExtension.IsNash p) :
    let μ : PMF (Profile G) := Math.PMFProduct.pmfPi p
    ∃ (B : ℝ) (hB : 0 ≤ B),
      (G.recommendationDevice μ B hB).InterimDominantExpectedKImplementsDistribution
        (G.obedientDeviceStrategy) μ 0 := by
  dsimp
  exact G.exists_recommendationDevice_interimDominantExpectedKImplementsDistribution
    (G.mixed_nash_isCorrelatedEq p hN)

end RecommendationDevice

end KernelGame

end GameTheory
