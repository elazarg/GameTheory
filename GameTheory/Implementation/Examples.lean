/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation.DifferentialPrivacy
import GameTheory.Implementation.Device
import GameTheory.Implementation.DeviceLP
import GameTheory.Implementation.Mixed
import GameTheory.Implementation.Regular
import GameTheory.Implementation.Singleton
import GameTheory.Concepts.Mixed.BinaryMixed
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Topology.Order.UpperLowerSetTopology

/-!
# k-implementation examples

Small examples and counterexamples around the finite singleton theorem.
-/

namespace GameTheory

open Math.Probability
open Math.ProbabilityMassFunction

namespace KernelGame

namespace ImplementationExamples

/-- Fast service provider in the introductory congestion example. -/
abbrev congestionFast : Bool := false

/-- Slow service provider in the introductory congestion example. -/
abbrev congestionSlow : Bool := true

/-- Payoffs for the introductory two-player congestion game. -/
def congestionPayoff (σ : (i : Fin 2) → Bool) : Payoff (Fin 2) :=
  fun
    | 0 =>
        match σ 0, σ 1 with
        | false, false => 3
        | false, true => 6
        | true, false => 4
        | true, true => 2
    | 1 =>
        match σ 0, σ 1 with
        | false, false => 3
        | false, true => 4
        | true, false => 6
        | true, true => 2

/-- The paper's introductory 2x2 congestion game. -/
noncomputable abbrev congestionGame : KernelGame (Fin 2) :=
  KernelGame.ofPureEU (fun _ : Fin 2 => Bool) congestionPayoff

instance congestionGame_outcome_finite : Finite congestionGame.Outcome := by
  change Finite ((i : Fin 2) → Bool)
  infer_instance

/-- A profile in the introductory congestion game. -/
def congestionProfile (a1 a2 : Bool) : Profile congestionGame :=
  fun i => if i = 0 then a1 else a2

@[simp] theorem congestionProfile_zero (a1 a2 : Bool) :
    congestionProfile a1 a2 0 = a1 := by
  simp [congestionProfile]

@[simp] theorem congestionProfile_one (a1 a2 : Bool) :
    congestionProfile a1 a2 1 = a2 := by
  simp [congestionProfile]

@[simp] theorem congestionProfile_update_zero (a1 a2 b : Bool) :
    Function.update (congestionProfile a1 a2) 0 b = congestionProfile b a2 := by
  funext i
  fin_cases i <;> simp [congestionProfile]

@[simp] theorem congestionProfile_update_zero_apply_zero (a1 a2 b : Bool) :
    Function.update (congestionProfile a1 a2) 0 b 0 = b := by
  simp [Function.update]

@[simp] theorem congestionProfile_update_zero_apply_one (a1 a2 b : Bool) :
    Function.update (congestionProfile a1 a2) 0 b 1 = a2 := by
  simp [Function.update, congestionProfile]

@[simp] theorem congestionProfile_update_one (a1 a2 b : Bool) :
    Function.update (congestionProfile a1 a2) 1 b = congestionProfile a1 b := by
  funext i
  fin_cases i <;> simp [congestionProfile]

@[simp] theorem congestionProfile_update_one_apply_zero (a1 a2 b : Bool) :
    Function.update (congestionProfile a1 a2) 1 b 0 = a1 := by
  simp [Function.update, congestionProfile]

@[simp] theorem congestionProfile_update_one_apply_one (a1 a2 b : Bool) :
    Function.update (congestionProfile a1 a2) 1 b 1 = b := by
  simp [Function.update]

/-- The target profile implemented in the paper's introductory example:
player 1 uses the fast provider and player 2 uses the slow provider. -/
def congestionTarget : Profile congestionGame :=
  congestionProfile congestionFast congestionSlow

/-- The paper's promised transfers: pay player 1 if both use `fast`, and pay
player 2 if both use `slow`. -/
noncomputable def congestionPromise : Profile congestionGame → Payoff (Fin 2) :=
  by
    classical
    exact fun σ =>
      fun
        | 0 => if σ 0 = congestionFast ∧ σ 1 = congestionFast then 10 else 0
        | 1 => if σ 0 = congestionSlow ∧ σ 1 = congestionSlow then 10 else 0

theorem congestionPromise_nonneg :
    ∀ σ i, 0 ≤ congestionPromise σ i := by
  intro σ i
  fin_cases i <;>
    simp [congestionPromise] <;>
    split_ifs <;>
    norm_num

theorem congestionTarget_isNash : congestionGame.IsNash congestionTarget := by
  intro i s
  fin_cases i <;>
    cases s <;>
    simp [congestionGame, congestionPayoff, congestionTarget, congestionFast,
      congestionSlow] <;>
    norm_num

/-- The other pure Nash profile in the introductory congestion game. The
promise below selects `congestionTarget`, not this equilibrium. -/
def congestionOtherNash : Profile congestionGame :=
  congestionProfile congestionSlow congestionFast

theorem congestionOtherNash_isNash : congestionGame.IsNash congestionOtherNash := by
  intro i s
  fin_cases i <;>
    cases s <;>
    simp [congestionGame, congestionPayoff, congestionOtherNash, congestionFast,
      congestionSlow] <;>
    norm_num

theorem congestionOtherNash_ne_target :
    congestionOtherNash ≠ congestionTarget := by
  intro h
  have h0 := congrFun h 0
  norm_num [congestionOtherNash, congestionTarget, congestionFast, congestionSlow] at h0
  exact Bool.noConfusion h0

theorem congestionPromise_zero_on_target (i : Fin 2) :
    congestionPromise congestionTarget i = 0 := by
  fin_cases i <;> simp [congestionPromise, congestionTarget]

/-- The transformed payoff table after the paper's promised transfers. -/
def congestionPromisedPayoff (σ : (i : Fin 2) → Bool) : Payoff (Fin 2) :=
  fun
    | 0 =>
        match σ 0, σ 1 with
        | false, false => 13
        | false, true => 6
        | true, false => 4
        | true, true => 2
    | 1 =>
        match σ 0, σ 1 with
        | false, false => 3
        | false, true => 4
        | true, false => 6
        | true, true => 12

/-- The introductory congestion game after adding the promised transfers. -/
noncomputable abbrev congestionPromisedGame : KernelGame (Fin 2) :=
  KernelGame.ofPureEU (fun _ : Fin 2 => Bool) congestionPromisedPayoff

/-- The hand-written transformed table is exactly the expected utility of the
original congestion game after adding `congestionPromise`. -/
theorem congestion_subsidize_eu_eq_promised
    (σ : Profile (congestionGame.subsidize congestionPromise)) (i : Fin 2) :
    (congestionGame.subsidize congestionPromise).eu σ i =
      congestionPromisedPayoff σ i := by
  let a1 := σ 0
  let a2 := σ 1
  have hσ : σ = congestionProfile a1 a2 := by
    funext j
    fin_cases j <;> simp [a1, a2, congestionProfile]
  rw [hσ]
  fin_cases i <;>
    cases a1 <;>
    cases a2 <;>
    simp [congestionGame, congestionPayoff, congestionPromisedPayoff,
      congestionPromise, congestionProfile, congestionFast, congestionSlow] <;>
    norm_num

theorem congestionPromised_fast_strictlyDominates_slow :
    congestionPromisedGame.StrictlyDominates 0 congestionFast congestionSlow := by
  intro σ
  let a1 := σ 0
  let a2 := σ 1
  have hσ : σ = congestionProfile a1 a2 := by
    funext i
    fin_cases i <;> simp [a1, a2, congestionProfile]
  rw [hσ]
  cases a1 <;>
    cases a2 <;>
    norm_num [congestionPromisedGame, congestionPromisedPayoff,
      congestionProfile, congestionFast, congestionSlow]

theorem congestionPromise_fast_strictlyDominates_slow :
    (congestionGame.subsidize congestionPromise).StrictlyDominates 0
      congestionFast congestionSlow := by
  intro σ
  rw [congestion_subsidize_eu_eq_promised, congestion_subsidize_eu_eq_promised]
  let a1 := σ 0
  let a2 := σ 1
  have hσ : σ = congestionProfile a1 a2 := by
    funext i
    fin_cases i <;> simp [a1, a2, congestionProfile]
  rw [hσ]
  cases a1 <;>
    cases a2 <;>
    norm_num [congestionPromisedPayoff, congestionProfile, congestionFast,
      congestionSlow]

theorem congestionPromised_slow_strictlyDominates_fast :
    congestionPromisedGame.StrictlyDominates 1 congestionSlow congestionFast := by
  intro σ
  let a1 := σ 0
  let a2 := σ 1
  have hσ : σ = congestionProfile a1 a2 := by
    funext i
    fin_cases i <;> simp [a1, a2, congestionProfile]
  rw [hσ]
  cases a1 <;>
    cases a2 <;>
    norm_num [congestionPromisedGame, congestionPromisedPayoff,
      congestionProfile, congestionFast, congestionSlow]

theorem congestionPromise_slow_strictlyDominates_fast :
    (congestionGame.subsidize congestionPromise).StrictlyDominates 1
      congestionSlow congestionFast := by
  intro σ
  rw [congestion_subsidize_eu_eq_promised, congestion_subsidize_eu_eq_promised]
  let a1 := σ 0
  let a2 := σ 1
  have hσ : σ = congestionProfile a1 a2 := by
    funext i
    fin_cases i <;> simp [a1, a2, congestionProfile]
  rw [hσ]
  cases a1 <;>
    cases a2 <;>
    norm_num [congestionPromisedPayoff, congestionProfile, congestionFast,
      congestionSlow]

theorem congestionPromise_fast_weaklyStrictlyDominates_slow :
    (congestionGame.subsidize congestionPromise).WeaklyStrictlyDominates 0
      congestionFast congestionSlow := by
  exact StrictlyDominates.toWeaklyStrictlyDominates
    (G := congestionGame.subsidize congestionPromise) ⟨congestionTarget⟩
    congestionPromise_fast_strictlyDominates_slow

theorem congestionPromise_slow_weaklyStrictlyDominates_fast :
    (congestionGame.subsidize congestionPromise).WeaklyStrictlyDominates 1
      congestionSlow congestionFast := by
  exact StrictlyDominates.toWeaklyStrictlyDominates
    (G := congestionGame.subsidize congestionPromise) ⟨congestionTarget⟩
    congestionPromise_slow_strictlyDominates_fast

theorem congestionPromise_target_undominated :
    congestionTarget ∈
      (congestionGame.subsidize congestionPromise).undominatedProfiles := by
  intro i t ht
  fin_cases i
  · cases t
    · exact WeaklyStrictlyDominates.irrefl
        (G := congestionGame.subsidize congestionPromise) (who := 0)
        congestionFast ht
    · exact congestionPromise_fast_weaklyStrictlyDominates_slow.asymm ht
  · cases t
    · exact congestionPromise_slow_weaklyStrictlyDominates_fast.asymm ht
    · exact WeaklyStrictlyDominates.irrefl
        (G := congestionGame.subsidize congestionPromise) (who := 1)
        congestionSlow ht

theorem congestionPromise_undominated_subset_singleton :
    ∀ σ : Profile congestionGame,
      σ ∈ (congestionGame.subsidize congestionPromise).undominatedProfiles →
        σ ∈ ({congestionTarget} : Set (Profile congestionGame)) := by
  intro σ hσ
  have h0 : σ 0 = congestionFast := by
    cases h : σ 0
    · rfl
    · exact False.elim
        (hσ 0 congestionFast
          (by simpa [h] using congestionPromise_fast_weaklyStrictlyDominates_slow))
  have h1 : σ 1 = congestionSlow := by
    cases h : σ 1
    · exact False.elim
        (hσ 1 congestionSlow
          (by simpa [h] using congestionPromise_slow_weaklyStrictlyDominates_fast))
    · rfl
  exact Set.mem_singleton_iff.mpr (by
    funext i
    fin_cases i <;> simp [congestionTarget, h0, h1, congestionFast,
      congestionSlow])

/-- The introductory congestion promise implements the target profile at zero
cost in the original game. -/
theorem congestionPromise_isZeroKImplementation :
    congestionGame.IsKImplementation congestionPromise
      ({congestionTarget} : Set (Profile congestionGame)) 0 := by
  refine ⟨?_, ?_⟩
  · refine ⟨congestionPromise_nonneg, ?_, ?_⟩
    · exact ⟨congestionTarget, congestionPromise_target_undominated⟩
    · exact congestionPromise_undominated_subset_singleton
  · intro σ hσ
    have htarget : σ = congestionTarget :=
      Set.mem_singleton_iff.mp (congestionPromise_undominated_subset_singleton σ hσ)
    rw [htarget]
    simp [congestionPromise_zero_on_target]

theorem congestionPromise_otherNash_not_undominated :
    congestionOtherNash ∉
      (congestionGame.subsidize congestionPromise).undominatedProfiles := by
  intro h
  have hmem := congestionPromise_undominated_subset_singleton congestionOtherNash h
  exact congestionOtherNash_ne_target (Set.mem_singleton_iff.mp hmem)

theorem congestionTarget_implPrice_eq_zero :
    congestionGame.implPrice ({congestionTarget} : Set (Profile congestionGame)) = 0 := by
  letI : ∀ i : Fin 2, Fintype (congestionGame.Strategy i) :=
    fun _ => inferInstanceAs (Fintype Bool)
  letI : ∀ i : Fin 2, Nonempty (congestionGame.Strategy i) :=
    fun _ => inferInstanceAs (Nonempty Bool)
  rw [implPrice_singleton (G := congestionGame) (z := congestionTarget)]
  exact Finset.sum_eq_zero fun i _ =>
    implementationGap_eq_zero_of_isNash (G := congestionGame)
      congestionTarget congestionTarget_isNash i

/-- A concrete two-player constant-payoff game used to instantiate the
recommendation-device theorem non-vacuously. -/
def deviceTiePayoff (_ : (i : Fin 2) → Bool) : Payoff (Fin 2) :=
  fun _ => 0

/-- A two-player Boolean game in which every profile gives payoff zero. -/
noncomputable abbrev deviceTieGame : KernelGame (Fin 2) :=
  KernelGame.ofPureEU (fun _ : Fin 2 => Bool) deviceTiePayoff

instance deviceTieGame_strategy_fintype (i : Fin 2) :
    Fintype (deviceTieGame.Strategy i) :=
  inferInstanceAs (Fintype Bool)

instance deviceTieGame_strategy_nonempty (i : Fin 2) :
    Nonempty (deviceTieGame.Strategy i) :=
  inferInstanceAs (Nonempty Bool)

instance deviceTieGame_outcome_finite : Finite deviceTieGame.Outcome := by
  change Finite ((i : Fin 2) → Bool)
  infer_instance

@[simp] theorem deviceTieGame_eu (σ : Profile deviceTieGame) (i : Fin 2) :
    deviceTieGame.eu σ i = 0 := by
  simp [deviceTieGame, deviceTiePayoff]

/-- Uniform recommendations over the four profiles of `deviceTieGame`. -/
noncomputable def deviceTieUniformLaw : PMF (Profile deviceTieGame) :=
  PMF.uniformOfFintype (Profile deviceTieGame)

theorem deviceTieUniformLaw_isCorrelatedEq :
    deviceTieGame.IsCorrelatedEq deviceTieUniformLaw := by
  intro who dev
  rw [deviceTieGame.correlatedEu_eq_expect_eu,
    deviceTieGame.correlatedEu_eq_expect_eu]
  simp [deviceTieUniformLaw, deviceTiePayoff]

theorem deviceTieUniformLaw_fullSupport :
    ∀ i (si : deviceTieGame.Strategy i),
      pmfMass (μ := deviceTieUniformLaw)
        (fun θ : Profile deviceTieGame => θ i = si) ≠ 0 := by
  intro i si
  let θ : Profile deviceTieGame := fun j => if h : j = i then h ▸ si else false
  have hθ : θ i = si := by simp [θ]
  refine pmfMass_ne_zero_of_mem_ne_zero
    (μ := deviceTieUniformLaw)
    (E := fun θ : Profile deviceTieGame => θ i = si) (a := θ) hθ ?_
  rw [deviceTieUniformLaw, PMF.uniformOfFintype_apply]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem deviceTieGame_nontrivialOpponent :
    ∀ i : Fin 2, ∃ j : Fin 2, j ≠ i ∧
      ∀ sj : deviceTieGame.Strategy j, ∃ a : deviceTieGame.Strategy j, a ≠ sj := by
  intro i
  fin_cases i
  · refine ⟨1, by decide, ?_⟩
    intro sj
    refine ⟨!sj, ?_⟩
    cases sj <;> simp
  · refine ⟨0, by decide, ?_⟩
    intro sj
    refine ⟨!sj, ?_⟩
    cases sj <;> simp

/-- The strict recommendation-device capstone is non-vacuous: it applies to an
explicit finite game and a full-support correlated equilibrium. -/
theorem deviceTie_exists_strictRecommendationDevice_exactKImplementation :
    ∃ (B : ℝ) (hB : 0 ≤ B),
      KernelGame.IsExactKImplementation
        (deviceTieGame.recommendationDevice deviceTieUniformLaw B hB).deviceGame
        (fun _ _ => 0)
        ({deviceTieGame.obedientDeviceStrategy} :
          Set (Profile
            (deviceTieGame.recommendationDevice deviceTieUniformLaw B hB).deviceGame)) 0 := by
  exact deviceTieGame.exists_recommendationDevice_obedient_zeroTransfer_exactKImplementation
    deviceTieUniformLaw_isCorrelatedEq deviceTieUniformLaw_fullSupport
    deviceTieGame_nontrivialOpponent

/-- Degenerate recommendations: both players are always recommended `false`.
This is a correlated equilibrium but does not have full signal support. -/
noncomputable def deviceTieDegenerateLaw : PMF (Profile deviceTieGame) :=
  PMF.pure (fun _ => false)

theorem deviceTieDegenerateLaw_zero_true_signal :
    pmfMass (μ := deviceTieDegenerateLaw)
      (fun θ : Profile deviceTieGame => θ 0 = true) = 0 := by
  classical
  rw [pmfMass_eq_toOuterMeasure]
  change (PMF.pure (fun _ : Fin 2 => false)).toOuterMeasure
    {θ : Profile deviceTieGame | θ 0 = true} = 0
  rw [PMF.toOuterMeasure_pure_apply, if_neg]
  intro hmem
  change (fun _ : Fin 2 => false) 0 = true at hmem
  simp at hmem

theorem deviceTieDegenerateLaw_isCorrelatedEq :
    deviceTieGame.IsCorrelatedEq deviceTieDegenerateLaw := by
  intro who dev
  rw [deviceTieGame.correlatedEu_eq_expect_eu,
    deviceTieGame.correlatedEu_eq_expect_eu]
  simp [deviceTieDegenerateLaw, deviceTiePayoff]

theorem deviceTieDegenerateLaw_not_fullSupport :
    ¬ ∀ i (si : deviceTieGame.Strategy i),
      pmfMass (μ := deviceTieDegenerateLaw)
        (fun θ : Profile deviceTieGame => θ i = si) ≠ 0 := by
  intro hfull
  have h := hfull 0 true
  have hzero :
      pmfMass (μ := deviceTieDegenerateLaw)
        (fun θ : Profile deviceTieGame => θ 0 = true) = 0 := by
    exact deviceTieDegenerateLaw_zero_true_signal
  exact h hzero

/-- Full support is necessary for strict dominance of signal-contingent rules:
if a recommendation is never sent, a rule that differs from obedience only at
that signal cannot be strictly dominated by obedience. -/
theorem deviceTieDegenerate_obedient_not_strictInterimDominantProfile
    (B : ℝ) (hB : 0 ≤ B) :
    ¬ ImplementationDevice.InterimWeaklyStrictlyDominantProfile
        (deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB)
        deviceTieGame.obedientDeviceStrategy := by
  classical
  let I := deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB
  let c : I.Signal 0 → deviceTieGame.Strategy 0 := fun _ => false
  intro hdom
  have hc : c ≠ deviceTieGame.obedientDeviceStrategy 0 := by
    intro h
    have htrue := congrFun h true
    simp [c, KernelGame.obedientDeviceStrategy] at htrue
  obtain ⟨si, hsi, β, hstrict⟩ := (hdom 0 c hc).2
  have hsi_false : si = false := by
    cases si
    · rfl
    · exfalso
      have hzero :
          pmfMass (μ := deviceTieDegenerateLaw)
            (fun θ : Profile deviceTieGame => θ 0 = true) = 0 := by
        exact deviceTieDegenerateLaw_zero_true_signal
      exact hsi (by simpa [I, ImplementationDevice.PositiveSignal, hzero])
  rw [I.interimEu_update_eq_const_at_signal hsi β
    (deviceTieGame.obedientDeviceStrategy 0)] at hstrict
  rw [I.interimEu_update_eq_const_at_signal hsi β c] at hstrict
  simp [c, KernelGame.obedientDeviceStrategy, hsi_false] at hstrict

/-- A rule profile that differs from obedience only at player 0's null
recommendation `true`. -/
noncomputable def deviceTieDegenerateNullRuleProfile (B : ℝ) (hB : 0 ≤ B) :
    Profile (deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB).deviceGame :=
  Function.update deviceTieGame.obedientDeviceStrategy 0 (fun _ => false)

theorem deviceTieDegenerateNullRuleProfile_ne_obedient (B : ℝ) (hB : 0 ≤ B) :
    deviceTieDegenerateNullRuleProfile B hB ≠ deviceTieGame.obedientDeviceStrategy := by
  intro h
  have htrue := congrFun (congrFun h 0) true
  simp [deviceTieDegenerateNullRuleProfile, KernelGame.obedientDeviceStrategy] at htrue

/-- The null-signal rule profile is equivalent to obedience for the zero
profile-observed implementation transfer.  This is the saturation reason full
support is needed for singleton exact implementation in the compiled device
game. -/
theorem deviceTieDegenerateNullRule_transferClassEquivalent_obedient
    (B : ℝ) (hB : 0 ≤ B) :
    KernelGame.TransferClassProfileEquivalent
      (deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB).deviceGame
        ({fun _ _ => 0} :
          Set (Profile
            (deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB).deviceGame →
              Payoff (Fin 2)))
        (deviceTieDegenerateNullRuleProfile B hB)
        deviceTieGame.obedientDeviceStrategy := by
  classical
  let I := deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB
  intro i
  fin_cases i
  · change I.deviceGame.TransferClassUtilityEquivalent
      ({fun _ _ => 0} : Set (Profile I.deviceGame → Payoff (Fin 2))) 0
        (fun _ : I.Signal 0 => false) (deviceTieGame.obedientDeviceStrategy 0)
    apply I.deviceGame_zeroTransferClassUtilityEquivalent_of_eq_on_positive_signals
    intro si hsi
    have hsi_false : si = false := by
      cases si
      · rfl
      · exfalso
        change
          pmfMass (μ := deviceTieDegenerateLaw)
            (fun θ : Profile deviceTieGame => θ 0 = true) ≠ 0 at hsi
        exact hsi deviceTieDegenerateLaw_zero_true_signal
    simp [KernelGame.obedientDeviceStrategy, hsi_false]
  · change I.deviceGame.TransferClassUtilityEquivalent
      ({fun _ _ => 0} : Set (Profile I.deviceGame → Payoff (Fin 2))) 1
        (deviceTieGame.obedientDeviceStrategy 1) (deviceTieGame.obedientDeviceStrategy 1)
    exact TransferClassUtilityEquivalent.refl
      (G := I.deviceGame)
      (C := ({fun _ _ => 0} : Set (Profile I.deviceGame → Payoff (Fin 2))))
      (deviceTieGame.obedientDeviceStrategy 1)

/-- The saturation theorem gives the same obstruction at the implementation
level: zero-transfer singleton exact implementation fails for the degenerate
recommendation device because a null-signal variant of obedience cannot be
separated. -/
theorem deviceTieDegenerate_zeroTransfer_not_exactSingletonImplementation
    (B : ℝ) (hB : 0 ≤ B) :
    ¬ KernelGame.IsExactImplementation
        (deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB).deviceGame
        (fun _ _ => 0)
        ({deviceTieGame.obedientDeviceStrategy} :
          Set (Profile
            (deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB).deviceGame)) := by
  intro h
  let I := deviceTieGame.recommendationDevice deviceTieDegenerateLaw B hB
  have himpl :
      I.deviceGame.IsImplementation (fun _ _ => 0)
        ({deviceTieGame.obedientDeviceStrategy} : Set (Profile I.deviceGame)) :=
    h.toImplementation ⟨deviceTieGame.obedientDeviceStrategy, Set.mem_singleton _⟩
  have heq :
      deviceTieDegenerateNullRuleProfile B hB = deviceTieGame.obedientDeviceStrategy := by
    exact himpl.eq_of_transferClassProfileEquivalent_singleton
      (C := ({fun _ _ => 0} : Set (Profile I.deviceGame → Payoff (Fin 2))))
      (V := fun _ _ => 0) (by simp)
      (deviceTieDegenerateNullRule_transferClassEquivalent_obedient B hB)
  exact deviceTieDegenerateNullRuleProfile_ne_obedient B hB heq

namespace OverlappingRegretPaymentExample

/-!
A concrete recommendation-payment instance where the pointwise budget is a real
LP value, not either endpoint of the elementary regret sandwich.
-/

/-- Two-player Boolean game with player 0 wanting `true` and player 1 wanting
`false`; payoffs do not depend on the opponent. -/
noncomputable def game : KernelGame (Fin 2) :=
  KernelGame.ofPureEU (fun _ : Fin 2 => Bool) fun σ =>
    fun
      | 0 => if σ 0 = true then 1 else 0
      | 1 => if σ 1 = true then 0 else 1

instance strategyFintype (i : Fin 2) : Fintype (game.Strategy i) :=
  inferInstanceAs (Fintype Bool)

instance strategyDecidableEq (i : Fin 2) : DecidableEq (game.Strategy i) :=
  inferInstanceAs (DecidableEq Bool)

instance strategyNonempty (i : Fin 2) : Nonempty (game.Strategy i) :=
  inferInstanceAs (Nonempty Bool)

instance profileFintype : Fintype (Profile game) := by
  change Fintype ((i : Fin 2) → Bool)
  infer_instance

instance profileDecidableEq : DecidableEq (Profile game) := by
  change DecidableEq ((i : Fin 2) → Bool)
  infer_instance

instance profileNonempty : Nonempty (Profile game) := by
  change Nonempty ((i : Fin 2) → Bool)
  infer_instance

instance outcomeFinite : Finite game.Outcome := by
  change Finite ((i : Fin 2) → Bool)
  infer_instance

/-- A profile in the overlapping-regret example. -/
def profile (a b : Bool) : Profile game :=
  fun i => if i = 0 then a else b

@[simp] theorem profile_zero (a b : Bool) : profile a b 0 = a := by
  simp [profile]

@[simp] theorem profile_one (a b : Bool) : profile a b 1 = b := by
  simp [profile]

@[simp] theorem profile_eq_profile_iff {a b c d : Bool} :
    profile a b = profile c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    change a = c at h0
    change b = d at h1
    exact ⟨h0, h1⟩
  · rintro ⟨hac, hbd⟩
    subst hac
    subst hbd
    rfl

@[simp] theorem profile_update_zero (a b c : Bool) :
    Function.update (profile a b) 0 c = profile c b := by
  funext i
  fin_cases i <;> simp [profile]

@[simp] theorem profile_update_one (a b c : Bool) :
    Function.update (profile a b) 1 c = profile a c := by
  funext i
  fin_cases i <;> simp [profile]

def profileEquiv : Profile game ≃ Bool × Bool where
  toFun θ := (θ 0, θ 1)
  invFun p := profile p.1 p.2
  left_inv θ := by
    funext i
    fin_cases i <;> simp [profile]
  right_inv p := by
    cases p
    simp [profile]

theorem profile_card : Fintype.card (Profile game) = 4 := by
  rw [Fintype.card_congr profileEquiv]
  norm_num

@[simp] theorem eu_zero (σ : Profile game) :
    game.eu σ 0 = if σ 0 = true then 1 else 0 := by
  simp [game]

@[simp] theorem eu_one (σ : Profile game) :
    game.eu σ 1 = if σ 1 = true then 0 else 1 := by
  simp [game]

/-- Uniform law over the four recommendation profiles. -/
noncomputable def law : PMF (Profile game) :=
  PMF.uniformOfFintype (Profile game)

lemma law_profile_ne_zero (a b : Bool) : law (profile a b) ≠ 0 := by
  rw [law, PMF.uniformOfFintype_apply, profile_card]
  exact ENNReal.inv_ne_zero.mpr (by norm_num : (4 : ENNReal) ≠ ⊤)

private theorem law_coord0_false_mass_toReal :
    (pmfMass (μ := law) (fun θ : Profile game => false = θ 0)).toReal = (1 / 2 : ℝ) := by
  rw [pmfMass_eq_toOuterMeasure, law, PMF.toOuterMeasure_uniformOfFintype_apply]
  have hnum : Fintype.card ↥{a : Profile game | false = a 0} = 2 := by
    let e : ↥{a : Profile game | false = a 0} ≃ Bool :=
      { toFun := fun θ => θ.1 1
        invFun := fun b => ⟨profile false b, by simp⟩
        left_inv := by
          intro θ
          apply Subtype.ext
          funext i
          fin_cases i
          · cases h0 : θ.1 0
            · exact h0.symm
            · have hprop : false = θ.1 0 := θ.2
              rw [h0] at hprop
              cases hprop
          · simp [profile]
        right_inv := by
          intro b
          simp [profile] }
    rw [Fintype.card_congr e]
    norm_num
  rw [hnum, profile_card]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_natCast]

private theorem law_coord1_true_mass_toReal :
    (pmfMass (μ := law) (fun θ : Profile game => true = θ 1)).toReal = (1 / 2 : ℝ) := by
  rw [pmfMass_eq_toOuterMeasure, law, PMF.toOuterMeasure_uniformOfFintype_apply]
  have hnum : Fintype.card ↥{a : Profile game | true = a 1} = 2 := by
    let e : ↥{a : Profile game | true = a 1} ≃ Bool :=
      { toFun := fun θ => θ.1 0
        invFun := fun a => ⟨profile a true, by simp⟩
        left_inv := by
          intro θ
          apply Subtype.ext
          funext i
          fin_cases i
          · simp [profile]
          · cases h1 : θ.1 1
            · have hprop : true = θ.1 1 := θ.2
              rw [h1] at hprop
              cases hprop
            · exact h1.symm
        right_inv := by
          intro a
          simp [profile] }
    rw [Fintype.card_congr e]
    norm_num
  rw [hnum, profile_card]
  norm_num [ENNReal.toReal_div, ENNReal.toReal_natCast]

private lemma coord0_false_payment_expect (p : Profile game → Payoff (Fin 2))
    (h : pmfMass (μ := law) (fun θ : Profile game => false = θ 0) ≠ 0) :
    expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 0) h)
      (fun θ => p θ 0) = (p (profile false false) 0 + p (profile false true) 0) / 2 := by
  classical
  let E : Profile game → Prop := fun θ => false = θ 0
  let f : Profile game → ℝ := fun θ => p θ 0
  have hmass : (pmfMass (μ := law) E).toReal = (1 / 2 : ℝ) :=
    law_coord0_false_mass_toReal
  have hscaled0 := pmfMass_toReal_mul_expect_cond law E h f
  have hmasked :
      (∑ ω : Profile game,
        @ite ℝ (E ω) (Classical.propDecidable (E ω)) ((law ω).toReal * f ω) 0) =
        (p (profile false false) 0 + p (profile false true) 0) / 4 := by
    dsimp [E, f]
    change (∑ ω : Profile game,
        @ite ℝ (false = ω 0) (Classical.propDecidable (false = ω 0))
          ((law ω).toReal * p ω 0) 0) =
      (p (profile false false) 0 + p (profile false true) 0) / 4
    rw [Fintype.sum_equiv profileEquiv
      (fun ω => @ite ℝ (false = ω 0) (Classical.propDecidable (false = ω 0))
        ((law ω).toReal * p ω 0) 0)
      (fun q => @ite ℝ (false = (profileEquiv.symm q) 0)
        (Classical.propDecidable (false = (profileEquiv.symm q) 0))
        ((law (profileEquiv.symm q)).toReal * p (profileEquiv.symm q) 0) 0)]
    · rw [Fintype.sum_prod_type]
      simp [profileEquiv, law, PMF.uniformOfFintype_apply, profile_card]
      ring
    · intro θ
      simp
  have hscaled : (1 / 2 : ℝ) * expect (pmfCond (μ := law) E h) f =
      (p (profile false false) 0 + p (profile false true) 0) / 4 := by
    calc
      (1 / 2 : ℝ) * expect (pmfCond (μ := law) E h) f =
          (pmfMass (μ := law) E).toReal * expect (pmfCond (μ := law) E h) f := by
            rw [hmass]
      _ = ∑ ω : Profile game,
            @ite ℝ (E ω) (Classical.propDecidable (E ω)) ((law ω).toReal * f ω) 0 :=
          hscaled0
      _ = (p (profile false false) 0 + p (profile false true) 0) / 4 :=
          hmasked
  change expect (pmfCond (μ := law) E h) f = _
  nlinarith

private lemma coord1_true_payment_expect (p : Profile game → Payoff (Fin 2))
    (h : pmfMass (μ := law) (fun θ : Profile game => true = θ 1) ≠ 0) :
    expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 1) h)
      (fun θ => p θ 1) = (p (profile false true) 1 + p (profile true true) 1) / 2 := by
  classical
  let E : Profile game → Prop := fun θ => true = θ 1
  let f : Profile game → ℝ := fun θ => p θ 1
  have hmass : (pmfMass (μ := law) E).toReal = (1 / 2 : ℝ) :=
    law_coord1_true_mass_toReal
  have hscaled0 := pmfMass_toReal_mul_expect_cond law E h f
  have hmasked :
      (∑ ω : Profile game,
        @ite ℝ (E ω) (Classical.propDecidable (E ω)) ((law ω).toReal * f ω) 0) =
        (p (profile false true) 1 + p (profile true true) 1) / 4 := by
    dsimp [E, f]
    change (∑ ω : Profile game,
        @ite ℝ (true = ω 1) (Classical.propDecidable (true = ω 1))
          ((law ω).toReal * p ω 1) 0) =
      (p (profile false true) 1 + p (profile true true) 1) / 4
    rw [Fintype.sum_equiv profileEquiv
      (fun ω => @ite ℝ (true = ω 1) (Classical.propDecidable (true = ω 1))
        ((law ω).toReal * p ω 1) 0)
      (fun q => @ite ℝ (true = (profileEquiv.symm q) 1)
        (Classical.propDecidable (true = (profileEquiv.symm q) 1))
        ((law (profileEquiv.symm q)).toReal * p (profileEquiv.symm q) 1) 0)]
    · rw [Fintype.sum_prod_type]
      simp [profileEquiv, law, PMF.uniformOfFintype_apply, profile_card]
      ring
    · intro θ
      simp
  have hscaled : (1 / 2 : ℝ) * expect (pmfCond (μ := law) E h) f =
      (p (profile false true) 1 + p (profile true true) 1) / 4 := by
    calc
      (1 / 2 : ℝ) * expect (pmfCond (μ := law) E h) f =
          (pmfMass (μ := law) E).toReal * expect (pmfCond (μ := law) E h) f := by
            rw [hmass]
      _ = ∑ ω : Profile game,
            @ite ℝ (E ω) (Classical.propDecidable (E ω)) ((law ω).toReal * f ω) 0 :=
          hscaled0
      _ = (p (profile false true) 1 + p (profile true true) 1) / 4 :=
          hmasked
  change expect (pmfCond (μ := law) E h) f = _
  nlinarith

private lemma gain0_false_false
    (h : pmfMass (μ := law) (fun θ : Profile game => false = θ 0) ≠ 0) :
    expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 0) h)
      (fun θ => game.eu (Function.update θ 0 false) 0 - game.eu θ 0) = 0 := by
  calc
    expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 0) h)
        (fun θ => game.eu (Function.update θ 0 false) 0 - game.eu θ 0)
        = expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 0) h)
          (fun _ => 0) := by
            refine expect_congr_of_ne_zero _ _ _ ?_
            intro θ hθ
            have hθ0 := pmfCond_ne_zero_implies law (fun θ : Profile game => false = θ 0) h hθ
            simp [hθ0.symm]
    _ = 0 := by simp

private lemma gain0_false_true
    (h : pmfMass (μ := law) (fun θ : Profile game => false = θ 0) ≠ 0) :
    expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 0) h)
      (fun θ => game.eu (Function.update θ 0 true) 0 - game.eu θ 0) = 1 := by
  calc
    expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 0) h)
        (fun θ => game.eu (Function.update θ 0 true) 0 - game.eu θ 0)
        = expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 0) h)
          (fun _ => 1) := by
            refine expect_congr_of_ne_zero _ _ _ ?_
            intro θ hθ
            have hθ0 := pmfCond_ne_zero_implies law (fun θ : Profile game => false = θ 0) h hθ
            simp [hθ0.symm]
    _ = 1 := by simp

private lemma gain0_true_false
    (h : pmfMass (μ := law) (fun θ : Profile game => true = θ 0) ≠ 0) :
    expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 0) h)
      (fun θ => game.eu (Function.update θ 0 false) 0 - game.eu θ 0) = -1 := by
  calc
    expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 0) h)
        (fun θ => game.eu (Function.update θ 0 false) 0 - game.eu θ 0)
        = expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 0) h)
          (fun _ => -1) := by
            refine expect_congr_of_ne_zero _ _ _ ?_
            intro θ hθ
            have hθ0 := pmfCond_ne_zero_implies law (fun θ : Profile game => true = θ 0) h hθ
            simp [hθ0.symm]
    _ = -1 := by simp

private lemma gain0_true_true
    (h : pmfMass (μ := law) (fun θ : Profile game => true = θ 0) ≠ 0) :
    expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 0) h)
      (fun θ => game.eu (Function.update θ 0 true) 0 - game.eu θ 0) = 0 := by
  calc
    expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 0) h)
        (fun θ => game.eu (Function.update θ 0 true) 0 - game.eu θ 0)
        = expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 0) h)
          (fun _ => 0) := by
            refine expect_congr_of_ne_zero _ _ _ ?_
            intro θ hθ
            have hθ0 := pmfCond_ne_zero_implies law (fun θ : Profile game => true = θ 0) h hθ
            simp [hθ0.symm]
    _ = 0 := by simp

private lemma gain1_false_false
    (h : pmfMass (μ := law) (fun θ : Profile game => false = θ 1) ≠ 0) :
    expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 1) h)
      (fun θ => game.eu (Function.update θ 1 false) 1 - game.eu θ 1) = 0 := by
  calc
    expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 1) h)
        (fun θ => game.eu (Function.update θ 1 false) 1 - game.eu θ 1)
        = expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 1) h)
          (fun _ => 0) := by
            refine expect_congr_of_ne_zero _ _ _ ?_
            intro θ hθ
            have hθ1 := pmfCond_ne_zero_implies law (fun θ : Profile game => false = θ 1) h hθ
            simp [hθ1.symm]
    _ = 0 := by simp

private lemma gain1_false_true
    (h : pmfMass (μ := law) (fun θ : Profile game => false = θ 1) ≠ 0) :
    expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 1) h)
      (fun θ => game.eu (Function.update θ 1 true) 1 - game.eu θ 1) = -1 := by
  calc
    expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 1) h)
        (fun θ => game.eu (Function.update θ 1 true) 1 - game.eu θ 1)
        = expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 1) h)
          (fun _ => -1) := by
            refine expect_congr_of_ne_zero _ _ _ ?_
            intro θ hθ
            have hθ1 := pmfCond_ne_zero_implies law (fun θ : Profile game => false = θ 1) h hθ
            simp [hθ1.symm]
    _ = -1 := by simp

private lemma gain1_true_false
    (h : pmfMass (μ := law) (fun θ : Profile game => true = θ 1) ≠ 0) :
    expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 1) h)
      (fun θ => game.eu (Function.update θ 1 false) 1 - game.eu θ 1) = 1 := by
  calc
    expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 1) h)
        (fun θ => game.eu (Function.update θ 1 false) 1 - game.eu θ 1)
        = expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 1) h)
          (fun _ => 1) := by
            refine expect_congr_of_ne_zero _ _ _ ?_
            intro θ hθ
            have hθ1 := pmfCond_ne_zero_implies law (fun θ : Profile game => true = θ 1) h hθ
            simp [hθ1.symm]
    _ = 1 := by simp

private lemma gain1_true_true
    (h : pmfMass (μ := law) (fun θ : Profile game => true = θ 1) ≠ 0) :
    expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 1) h)
      (fun θ => game.eu (Function.update θ 1 true) 1 - game.eu θ 1) = 0 := by
  calc
    expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 1) h)
        (fun θ => game.eu (Function.update θ 1 true) 1 - game.eu θ 1)
        = expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 1) h)
          (fun _ => 0) := by
            refine expect_congr_of_ne_zero _ _ _ ?_
            intro θ hθ
            have hθ1 := pmfCond_ne_zero_implies law (fun θ : Profile game => true = θ 1) h hθ
            simp [hθ1.symm]
    _ = 0 := by simp

/-- Feasible payments that share the overlapping active constraints. -/
noncomputable def payment : Profile game → Payoff (Fin 2) :=
  fun θ i =>
    match i with
    | 0 => if θ 0 = false then if θ 1 = false then (4 / 3 : ℝ) else 2 / 3 else 0
    | 1 => if θ 1 = true then if θ 0 = false then (2 / 3 : ℝ) else 4 / 3 else 0

lemma payment_nonneg : ∀ θ i, 0 ≤ payment θ i := by
  intro θ i
  fin_cases i <;> simp [payment] <;> split_ifs <;> norm_num

lemma payment_budget (θ : Profile game) : ∑ i : Fin 2, payment θ i ≤ (4 / 3 : ℝ) := by
  let a := θ 0
  let b := θ 1
  have hθ : θ = profile a b := by
    funext i
    fin_cases i <;> simp [a, b, profile]
  rw [hθ, Fin.sum_univ_two]
  cases a <;> cases b <;> simp [payment, profile] <;> norm_num

lemma payment_active0_expect
    (h : pmfMass (μ := law) (fun θ : Profile game => false = θ 0) ≠ 0) :
    expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 0) h)
      (fun θ => payment θ 0) = 1 := by
  rw [coord0_false_payment_expect payment h]
  simp [payment, profile]
  norm_num

lemma payment_active1_expect
    (h : pmfMass (μ := law) (fun θ : Profile game => true = θ 1) ≠ 0) :
    expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 1) h)
      (fun θ => payment θ 1) = 1 := by
  rw [coord1_true_payment_expect payment h]
  simp [payment, profile]
  norm_num

lemma payment_feasible : game.RecommendationPaymentFeasible law payment (4 / 3) := by
  classical
  refine ⟨payment_nonneg, ?_, ?_⟩
  · intro θ _hθ
    exact payment_budget θ
  · intro i si hsi a
    have hpay_nonneg :
        0 ≤ expect (pmfCond (μ := law) (fun θ : Profile game => si = θ i) hsi)
          (fun θ => payment θ i) :=
      expect_nonneg _ _ fun θ => payment_nonneg θ i
    fin_cases i <;> cases si <;> cases a
    · have hgain := gain0_false_false hsi
      have hle :
          expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 0) hsi)
            (fun θ => game.eu (Function.update θ 0 false) 0 - game.eu θ 0) ≤ 0 := by
        linarith
      exact le_trans hle hpay_nonneg
    · calc
        expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 0) hsi)
            (fun θ => game.eu (Function.update θ 0 true) 0 - game.eu θ 0)
            = 1 := gain0_false_true hsi
        _ ≤ expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 0) hsi)
            (fun θ => payment θ 0) := by rw [payment_active0_expect hsi]
    · have hgain := gain0_true_false hsi
      have hle :
          expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 0) hsi)
            (fun θ => game.eu (Function.update θ 0 false) 0 - game.eu θ 0) ≤ 0 := by
        linarith
      exact le_trans hle hpay_nonneg
    · have hgain := gain0_true_true hsi
      have hle :
          expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 0) hsi)
            (fun θ => game.eu (Function.update θ 0 true) 0 - game.eu θ 0) ≤ 0 := by
        linarith
      exact le_trans hle hpay_nonneg
    · have hgain := gain1_false_false hsi
      have hle :
          expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 1) hsi)
            (fun θ => game.eu (Function.update θ 1 false) 1 - game.eu θ 1) ≤ 0 := by
        linarith
      exact le_trans hle hpay_nonneg
    · have hgain := gain1_false_true hsi
      have hle :
          expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 1) hsi)
            (fun θ => game.eu (Function.update θ 1 true) 1 - game.eu θ 1) ≤ 0 := by
        linarith
      exact le_trans hle hpay_nonneg
    · calc
        expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 1) hsi)
            (fun θ => game.eu (Function.update θ 1 false) 1 - game.eu θ 1)
            = 1 := gain1_true_false hsi
        _ ≤ expect (pmfCond (μ := law) (fun θ => true = θ 1) hsi)
            (fun θ => payment θ 1) := by rw [payment_active1_expect hsi]
    · have hgain := gain1_true_true hsi
      have hle :
          expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 1) hsi)
            (fun θ => game.eu (Function.update θ 1 true) 1 - game.eu θ 1) ≤ 0 := by
        linarith
      exact le_trans hle hpay_nonneg

/-- Dual-style weights on the active conditional incentive constraints. -/
noncomputable def lowerBoundLam :
    (i : Fin 2) → game.Strategy i → game.Strategy i → ℝ :=
  fun i si a =>
    match i with
    | 0 =>
        if si = (false : game.Strategy 0) ∧ a = (true : game.Strategy 0) then
          (2 / 3 : ℝ)
        else 0
    | 1 =>
        if si = (true : game.Strategy 1) ∧ a = (false : game.Strategy 1) then
          (2 / 3 : ℝ)
        else 0

/-- Dual-style weights on the pointwise budget constraints. -/
noncomputable def lowerBoundGamma (θ : Profile game) : ℝ :=
  if θ = profile true false then 0 else (1 / 3 : ℝ)

lemma lowerBoundLam_nonneg : ∀ i si a, 0 ≤ lowerBoundLam i si a := by
  intro i si a
  fin_cases i <;> simp [lowerBoundLam] <;> split_ifs <;> norm_num

lemma lowerBoundGamma_nonneg : ∀ θ, 0 ≤ lowerBoundGamma θ := by
  intro θ
  simp [lowerBoundGamma]
  split_ifs <;> norm_num

lemma law_ne_zero (θ : Profile game) : law θ ≠ 0 := by
  let a := θ 0
  let b := θ 1
  have hθ : θ = profile a b := by
    funext i
    fin_cases i <;> simp [a, b, profile]
  rw [hθ]
  exact law_profile_ne_zero a b

lemma lowerBoundGamma_zero : ∀ θ, law θ = 0 → lowerBoundGamma θ = 0 := by
  intro θ hθ
  exact False.elim (law_ne_zero θ hθ)

lemma lowerBoundGamma_sum :
    (∑ θ : Profile game, lowerBoundGamma θ) = 1 := by
  rw [Fintype.sum_equiv profileEquiv
    lowerBoundGamma
    (fun q => lowerBoundGamma (profileEquiv.symm q))]
  · rw [Fintype.sum_prod_type]
    simp [profileEquiv, lowerBoundGamma]
    norm_num
  · intro θ
    simp

private lemma incentiveGain_zero_false_true :
    game.recommendationPaymentIncentiveGain law 0
      (false : game.Strategy 0) (true : game.Strategy 0) = 1 := by
  have hmass :
      pmfMass (μ := law) (fun θ : Profile game => (false : game.Strategy 0) = θ 0) ≠
        0 := by
    have hto := law_coord0_false_mass_toReal
    intro hzero
    rw [hzero] at hto
    norm_num at hto
  rw [recommendationPaymentIncentiveGain]
  change (if h : pmfMass (μ := law)
      (fun θ : Profile game => (false : game.Strategy 0) = θ 0) ≠ 0 then
      expect (pmfCond (μ := law)
        (fun θ : Profile game => (false : game.Strategy 0) = θ 0) h)
        (fun θ => game.eu (Function.update θ 0 (true : game.Strategy 0)) 0 - game.eu θ 0)
    else 0) = 1
  rw [dif_pos hmass]
  exact gain0_false_true hmass

private lemma incentiveGain_one_true_false :
    game.recommendationPaymentIncentiveGain law 1
      (true : game.Strategy 1) (false : game.Strategy 1) = 1 := by
  have hmass :
      pmfMass (μ := law) (fun θ : Profile game => (true : game.Strategy 1) = θ 1) ≠
        0 := by
    have hto := law_coord1_true_mass_toReal
    intro hzero
    rw [hzero] at hto
    norm_num at hto
  rw [recommendationPaymentIncentiveGain]
  change (if h : pmfMass (μ := law)
      (fun θ : Profile game => (true : game.Strategy 1) = θ 1) ≠ 0 then
      expect (pmfCond (μ := law)
        (fun θ : Profile game => (true : game.Strategy 1) = θ 1) h)
        (fun θ => game.eu (Function.update θ 1 (false : game.Strategy 1)) 1 - game.eu θ 1)
    else 0) = 1
  rw [dif_pos hmass]
  exact gain1_true_false hmass

lemma lowerBoundWeightedValue :
    (∑ i, ∑ si : game.Strategy i, ∑ a : game.Strategy i,
      lowerBoundLam i si a * game.recommendationPaymentIncentiveGain law i si a) =
        (4 / 3 : ℝ) := by
  rw [Fin.sum_univ_two]
  dsimp [lowerBoundLam]
  change
    ((∑ x : Bool, ∑ y : Bool,
        (if x = false ∧ y = true then (2 / 3 : ℝ) else 0) *
          game.recommendationPaymentIncentiveGain law 0
            (x : game.Strategy 0) (y : game.Strategy 0)) +
      ∑ x : Bool, ∑ y : Bool,
        (if x = true ∧ y = false then (2 / 3 : ℝ) else 0) *
          game.recommendationPaymentIncentiveGain law 1
            (x : game.Strategy 1) (y : game.Strategy 1)) = (4 / 3 : ℝ)
  repeat rw [Fintype.sum_bool]
  simp [incentiveGain_zero_false_true, incentiveGain_one_true_false]
  norm_num

private lemma incentiveCoeff_zero_false_true (a b : Bool) :
    game.recommendationPaymentIncentiveCoeff law 0
      (false : game.Strategy 0) (true : game.Strategy 0) (profile a b) =
        if a = false then (1 / 2 : ℝ) else 0 := by
  have hmass :
      pmfMass (μ := law) (fun θ : Profile game => (false : game.Strategy 0) = θ 0) ≠
        0 := by
    have hto := law_coord0_false_mass_toReal
    intro hzero
    rw [hzero] at hto
    norm_num at hto
  rw [recommendationPaymentIncentiveCoeff]
  change (if h : pmfMass (μ := law)
      (fun θ : Profile game => (false : game.Strategy 0) = θ 0) ≠ 0 then
      ((pmfCond (μ := law)
        (fun θ : Profile game => (false : game.Strategy 0) = θ 0) h) (profile a b)).toReal
    else 0) = if a = false then (1 / 2 : ℝ) else 0
  rw [dif_pos hmass]
  by_cases ha : a = false
  · subst a
    have hmass_to := law_coord0_false_mass_toReal
    have hnum :
        (pmfMask (μ := law)
          (fun θ : Profile game => (false : game.Strategy 0) = θ 0)
          (profile false b)).toReal = (1 / 4 : ℝ) := by
      have hprob : (law (profile false b)).toReal = (1 / 4 : ℝ) := by
        simp [law, PMF.uniformOfFintype_apply, profile_card]
      simpa [pmfMask, profile] using hprob
    rw [pmfCond_apply]
    rw [ENNReal.toReal_div]
    rw [hnum, hmass_to]
    norm_num
  · rw [if_neg ha]
    rw [pmfCond_apply]
    simp [pmfMask, ha, profile]

private lemma incentiveCoeff_one_true_false (a b : Bool) :
    game.recommendationPaymentIncentiveCoeff law 1
      (true : game.Strategy 1) (false : game.Strategy 1) (profile a b) =
        if b = true then (1 / 2 : ℝ) else 0 := by
  have hmass :
      pmfMass (μ := law) (fun θ : Profile game => (true : game.Strategy 1) = θ 1) ≠
        0 := by
    have hto := law_coord1_true_mass_toReal
    intro hzero
    rw [hzero] at hto
    norm_num at hto
  rw [recommendationPaymentIncentiveCoeff]
  change (if h : pmfMass (μ := law)
      (fun θ : Profile game => (true : game.Strategy 1) = θ 1) ≠ 0 then
      ((pmfCond (μ := law)
        (fun θ : Profile game => (true : game.Strategy 1) = θ 1) h) (profile a b)).toReal
    else 0) = if b = true then (1 / 2 : ℝ) else 0
  rw [dif_pos hmass]
  by_cases hb : b = true
  · subst b
    have hmass_to := law_coord1_true_mass_toReal
    have hnum :
        (pmfMask (μ := law)
          (fun θ : Profile game => (true : game.Strategy 1) = θ 1)
          (profile a true)).toReal = (1 / 4 : ℝ) := by
      have hprob : (law (profile a true)).toReal = (1 / 4 : ℝ) := by
        simp [law, PMF.uniformOfFintype_apply, profile_card]
      simpa [pmfMask, profile] using hprob
    rw [pmfCond_apply]
    rw [ENNReal.toReal_div]
    rw [hnum, hmass_to]
    norm_num
  · rw [if_neg hb]
    rw [pmfCond_apply]
    simp [pmfMask, hb, profile]

private lemma lowerBoundCoeff_zero_sum (θ : Profile game) :
    (∑ si : game.Strategy 0, ∑ a : game.Strategy 0,
      lowerBoundLam 0 si a * game.recommendationPaymentIncentiveCoeff law 0 si a θ) =
        (2 / 3 : ℝ) *
          game.recommendationPaymentIncentiveCoeff law 0
            (false : game.Strategy 0) (true : game.Strategy 0) θ := by
  dsimp [lowerBoundLam]
  change (∑ si : Bool, ∑ a : Bool,
      (if si = false ∧ a = true then (2 / 3 : ℝ) else 0) *
        game.recommendationPaymentIncentiveCoeff law 0
          (si : game.Strategy 0) (a : game.Strategy 0) θ) =
    (2 / 3 : ℝ) *
      game.recommendationPaymentIncentiveCoeff law 0
        (false : game.Strategy 0) (true : game.Strategy 0) θ
  repeat rw [Fintype.sum_bool]
  simp

private lemma lowerBoundCoeff_one_sum (θ : Profile game) :
    (∑ si : game.Strategy 1, ∑ a : game.Strategy 1,
      lowerBoundLam 1 si a * game.recommendationPaymentIncentiveCoeff law 1 si a θ) =
        (2 / 3 : ℝ) *
          game.recommendationPaymentIncentiveCoeff law 1
            (true : game.Strategy 1) (false : game.Strategy 1) θ := by
  dsimp [lowerBoundLam]
  change (∑ si : Bool, ∑ a : Bool,
      (if si = true ∧ a = false then (2 / 3 : ℝ) else 0) *
        game.recommendationPaymentIncentiveCoeff law 1
          (si : game.Strategy 1) (a : game.Strategy 1) θ) =
    (2 / 3 : ℝ) *
      game.recommendationPaymentIncentiveCoeff law 1
        (true : game.Strategy 1) (false : game.Strategy 1) θ
  repeat rw [Fintype.sum_bool]
  simp

lemma lowerBoundCoeff (θ : Profile game) (i : Fin 2) :
    (∑ si : game.Strategy i, ∑ a : game.Strategy i,
      lowerBoundLam i si a * game.recommendationPaymentIncentiveCoeff law i si a θ) ≤
        lowerBoundGamma θ := by
  let x := θ 0
  let y := θ 1
  have hθ : θ = profile x y := by
    funext j
    fin_cases j <;> simp [x, y, profile]
  rw [hθ]
  fin_cases i
  · change (∑ si : game.Strategy 0, ∑ a : game.Strategy 0,
        lowerBoundLam 0 si a * game.recommendationPaymentIncentiveCoeff law 0 si a
          (profile x y)) ≤ lowerBoundGamma (profile x y)
    rw [lowerBoundCoeff_zero_sum]
    cases x <;> cases y
      <;> simp [lowerBoundGamma, incentiveCoeff_zero_false_true]
      <;> norm_num
  · change (∑ si : game.Strategy 1, ∑ a : game.Strategy 1,
        lowerBoundLam 1 si a * game.recommendationPaymentIncentiveCoeff law 1 si a
          (profile x y)) ≤ lowerBoundGamma (profile x y)
    rw [lowerBoundCoeff_one_sum]
    cases x <;> cases y
      <;> simp [lowerBoundGamma, incentiveCoeff_one_true_false]
      <;> norm_num

theorem four_thirds_le_recommendationPaymentImplPrice_by_weighted_certificate :
    (4 / 3 : ℝ) ≤ game.recommendationPaymentImplPrice law := by
  refine game.le_recommendationPaymentImplPrice_of_weighted_certificate
    (μ := law) (L := (4 / 3 : ℝ))
    (hne := ⟨4 / 3, payment, payment_feasible⟩)
    lowerBoundLam lowerBoundGamma
    lowerBoundLam_nonneg lowerBoundGamma_nonneg lowerBoundGamma_zero
    lowerBoundGamma_sum lowerBoundCoeff ?_
  rw [lowerBoundWeightedValue]

/-- The explicit raw matrix-dual vector behind the `4 / 3` lower bound. -/
noncomputable def lowerBoundRawDual : game.RecommendationPaymentLPRow → ℝ :=
  game.recommendationPaymentDualVector lowerBoundLam lowerBoundGamma

/-- The raw matrix-dual vector is feasible for the zero-objective dual LP. -/
theorem lowerBoundRawDual_dualFeasible :
    Math.LinearProgramming.DualFeasible
      (game.recommendationPaymentLPA law)
      (fun _ : game.RecommendationPaymentLPCol => 0)
      lowerBoundRawDual := by
  exact game.recommendationPaymentDualVector_dualFeasible
    lowerBoundLam lowerBoundGamma
    lowerBoundLam_nonneg lowerBoundGamma_nonneg lowerBoundGamma_zero lowerBoundCoeff

/-- The raw dual value is negative exactly below budget `4 / 3`. -/
theorem lowerBoundRawDual_dualValue (k : ℝ) :
    Math.LinearProgramming.dualValue (game.recommendationPaymentLPb law k)
        lowerBoundRawDual =
      k - (4 / 3 : ℝ) := by
  rw [lowerBoundRawDual]
  rw [game.recommendationPaymentDualVector_dualValue
    lowerBoundLam lowerBoundGamma lowerBoundGamma_zero]
  rw [lowerBoundGamma_sum, lowerBoundWeightedValue]
  ring

/-- Raw LP/Farkas certificate for the `4 / 3` lower bound. -/
theorem four_thirds_le_recommendationPaymentImplPrice_by_raw_lp_certificate :
    (4 / 3 : ℝ) ≤ game.recommendationPaymentImplPrice law := by
  refine game.le_recommendationPaymentImplPrice_of_dual_certificates
    (μ := law) (L := (4 / 3 : ℝ))
    (hne := ⟨4 / 3, payment, payment_feasible⟩) ?_
  intro k hk
  refine ⟨lowerBoundRawDual, lowerBoundRawDual_dualFeasible, ?_⟩
  rw [lowerBoundRawDual_dualValue]
  linarith

/-- The exact pointwise recommendation-payment price is `4 / 3` for the
overlapping-regret distribution. -/
theorem recommendationPaymentImplPrice_eq_four_thirds :
    game.recommendationPaymentImplPrice law = (4 / 3 : ℝ) := by
  apply le_antisymm
  · exact game.recommendationPaymentImplPrice_le_of_mem ⟨payment, payment_feasible⟩
  · exact four_thirds_le_recommendationPaymentImplPrice_by_raw_lp_certificate

lemma conditionalSwapRegret_zero_false :
    game.conditionalSwapRegret law 0 (false : game.Strategy 0) = 1 := by
  classical
  have hmass :
      pmfMass (μ := law) (fun θ : Profile game => (false : game.Strategy 0) = θ 0) ≠
        0 := by
    have hto := law_coord0_false_mass_toReal
    intro hzero
    rw [hzero] at hto
    norm_num at hto
  let f : game.Strategy 0 → ℝ := fun a =>
    expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 0) hmass)
      (fun θ => game.eu (Function.update θ 0 a) 0 - game.eu θ 0)
  rw [conditionalSwapRegret]
  change (if hsi :
        pmfMass (μ := law) (fun θ : Profile game => (false : game.Strategy 0) = θ 0) ≠
          0 then
        Finset.univ.sup' (Finset.univ_nonempty (α := game.Strategy 0)) f
      else 0) = 1
  rw [dif_pos hmass]
  have hf_false : f (false : game.Strategy 0) = 0 := gain0_false_false hmass
  have hf_true : f (true : game.Strategy 0) = 1 := gain0_false_true hmass
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    cases a
    · rw [hf_false]
      norm_num
    · rw [hf_true]
  · have hle : (1 : ℝ) ≤ f (true : game.Strategy 0) := by rw [hf_true]
    exact hle.trans
      (Finset.le_sup' (s := Finset.univ) (f := f) (Finset.mem_univ (true : game.Strategy 0)))

lemma conditionalSwapRegret_zero_true :
    game.conditionalSwapRegret law 0 (true : game.Strategy 0) = 0 := by
  classical
  have hmass :
      pmfMass (μ := law) (fun θ : Profile game => (true : game.Strategy 0) = θ 0) ≠
        0 :=
    pmfMass_ne_zero_of_mem_ne_zero law (a := profile true false)
      (by simp) (law_profile_ne_zero true false)
  let f : game.Strategy 0 → ℝ := fun a =>
    expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 0) hmass)
      (fun θ => game.eu (Function.update θ 0 a) 0 - game.eu θ 0)
  rw [conditionalSwapRegret]
  change (if hsi :
        pmfMass (μ := law) (fun θ : Profile game => (true : game.Strategy 0) = θ 0) ≠
          0 then
        Finset.univ.sup' (Finset.univ_nonempty (α := game.Strategy 0)) f
      else 0) = 0
  rw [dif_pos hmass]
  have hf_false : f (false : game.Strategy 0) = -1 := gain0_true_false hmass
  have hf_true : f (true : game.Strategy 0) = 0 := gain0_true_true hmass
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    cases a
    · rw [hf_false]
      norm_num
    · rw [hf_true]
  · have hle : (0 : ℝ) ≤ f (true : game.Strategy 0) := by rw [hf_true]
    exact hle.trans
      (Finset.le_sup' (s := Finset.univ) (f := f) (Finset.mem_univ (true : game.Strategy 0)))

lemma conditionalSwapRegret_one_false :
    game.conditionalSwapRegret law 1 (false : game.Strategy 1) = 0 := by
  classical
  have hmass :
      pmfMass (μ := law) (fun θ : Profile game => (false : game.Strategy 1) = θ 1) ≠
        0 :=
    pmfMass_ne_zero_of_mem_ne_zero law (a := profile false false)
      (by simp) (law_profile_ne_zero false false)
  let f : game.Strategy 1 → ℝ := fun a =>
    expect (pmfCond (μ := law) (fun θ : Profile game => false = θ 1) hmass)
      (fun θ => game.eu (Function.update θ 1 a) 1 - game.eu θ 1)
  rw [conditionalSwapRegret]
  change (if hsi :
        pmfMass (μ := law) (fun θ : Profile game => (false : game.Strategy 1) = θ 1) ≠
          0 then
        Finset.univ.sup' (Finset.univ_nonempty (α := game.Strategy 1)) f
      else 0) = 0
  rw [dif_pos hmass]
  have hf_false : f (false : game.Strategy 1) = 0 := gain1_false_false hmass
  have hf_true : f (true : game.Strategy 1) = -1 := gain1_false_true hmass
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    cases a
    · rw [hf_false]
    · rw [hf_true]
      norm_num
  · have hle : (0 : ℝ) ≤ f (false : game.Strategy 1) := by rw [hf_false]
    exact hle.trans
      (Finset.le_sup' (s := Finset.univ) (f := f) (Finset.mem_univ (false : game.Strategy 1)))

lemma conditionalSwapRegret_one_true :
    game.conditionalSwapRegret law 1 (true : game.Strategy 1) = 1 := by
  classical
  have hmass :
      pmfMass (μ := law) (fun θ : Profile game => (true : game.Strategy 1) = θ 1) ≠
        0 := by
    have hto := law_coord1_true_mass_toReal
    intro hzero
    rw [hzero] at hto
    norm_num at hto
  let f : game.Strategy 1 → ℝ := fun a =>
    expect (pmfCond (μ := law) (fun θ : Profile game => true = θ 1) hmass)
      (fun θ => game.eu (Function.update θ 1 a) 1 - game.eu θ 1)
  rw [conditionalSwapRegret]
  change (if hsi :
        pmfMass (μ := law) (fun θ : Profile game => (true : game.Strategy 1) = θ 1) ≠
          0 then
        Finset.univ.sup' (Finset.univ_nonempty (α := game.Strategy 1)) f
      else 0) = 1
  rw [dif_pos hmass]
  have hf_false : f (false : game.Strategy 1) = 1 := gain1_true_false hmass
  have hf_true : f (true : game.Strategy 1) = 0 := gain1_true_true hmass
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    cases a
    · rw [hf_false]
    · rw [hf_true]
      norm_num
  · have hle : (1 : ℝ) ≤ f (false : game.Strategy 1) := by rw [hf_false]
    exact hle.trans
      (Finset.le_sup' (s := Finset.univ) (f := f) (Finset.mem_univ (false : game.Strategy 1)))

theorem maxConditionalSwapRegret_eq_one :
    game.maxConditionalSwapRegret law = 1 := by
  classical
  apply le_antisymm
  · unfold maxConditionalSwapRegret
    apply Finset.sup'_le
    intro i _
    fin_cases i
    · apply Finset.sup'_le
      intro si _
      cases si
      · simpa using
          (show game.conditionalSwapRegret law 0 (false : game.Strategy 0) ≤ 1 by
            rw [conditionalSwapRegret_zero_false])
      · simpa using
          (show game.conditionalSwapRegret law 0 (true : game.Strategy 0) ≤ 1 by
            rw [conditionalSwapRegret_zero_true]
            norm_num)
    · apply Finset.sup'_le
      intro si _
      cases si
      · simpa using
          (show game.conditionalSwapRegret law 1 (false : game.Strategy 1) ≤ 1 by
            rw [conditionalSwapRegret_one_false]
            norm_num)
      · simpa using
          (show game.conditionalSwapRegret law 1 (true : game.Strategy 1) ≤ 1 by
            rw [conditionalSwapRegret_one_true])
  · simpa [conditionalSwapRegret_zero_false] using
      (game.conditionalSwapRegret_le_maxConditionalSwapRegret law 0 false)

theorem maxSupportedPointwiseConditionalSwapRegret_eq_two :
    game.maxSupportedPointwiseConditionalSwapRegret law = 2 := by
  classical
  apply le_antisymm
  · unfold maxSupportedPointwiseConditionalSwapRegret
    apply Finset.sup'_le
    intro θ hθ
    let a := θ 0
    let b := θ 1
    have hθeq : θ = profile a b := by
      funext i
      fin_cases i <;> simp [a, b, profile]
    rw [hθeq, Fin.sum_univ_two]
    cases a <;> cases b <;>
      simp [conditionalSwapRegret_zero_false, conditionalSwapRegret_zero_true,
        conditionalSwapRegret_one_false, conditionalSwapRegret_one_true];
      norm_num
  · have h :=
      game.sum_conditionalSwapRegret_le_maxSupportedPointwiseConditionalSwapRegret
        law (hθ := law_profile_ne_zero false true)
    rw [Fin.sum_univ_two, profile_zero, profile_one,
      conditionalSwapRegret_zero_false, conditionalSwapRegret_one_true] at h
    norm_num at h
    exact h

theorem recommendationPaymentImplPrice_strict_between_sandwich :
    game.maxConditionalSwapRegret law < game.recommendationPaymentImplPrice law ∧
      game.recommendationPaymentImplPrice law <
        game.maxSupportedPointwiseConditionalSwapRegret law := by
  rw [maxConditionalSwapRegret_eq_one, recommendationPaymentImplPrice_eq_four_thirds,
    maxSupportedPointwiseConditionalSwapRegret_eq_two]
  norm_num

end OverlappingRegretPaymentExample

namespace ExpectedDeviceEpsilonCounterexample

/-!
The expected device price is total maximum swap regret.  Therefore
`ε`-correlated equilibrium implies expected price at most `|N| * ε`, but the
converse with the same `|N| * ε` threshold is false for the standard
per-player definition of `ε`-CE.
-/

/-- Two players, Boolean actions.  Player 0 gets payoff `2` from `true`;
player 1 is payoff-neutral. -/
noncomputable def game : KernelGame (Fin 2) :=
  KernelGame.ofPureEU (fun _ : Fin 2 => Bool) fun σ =>
    fun
      | 0 => if σ 0 = true then 2 else 0
      | 1 => 0

instance strategyFintype (i : Fin 2) : Fintype (game.Strategy i) :=
  inferInstanceAs (Fintype Bool)

instance strategyDecidableEq (i : Fin 2) : DecidableEq (game.Strategy i) :=
  inferInstanceAs (DecidableEq Bool)

instance strategyNonempty (i : Fin 2) : Nonempty (game.Strategy i) :=
  inferInstanceAs (Nonempty Bool)

instance profileFintype : Fintype (Profile game) := by
  change Fintype ((i : Fin 2) → Bool)
  infer_instance

instance profileFinite : Finite (Profile game) := inferInstance

instance outcomeFinite : Finite game.Outcome := by
  change Finite ((i : Fin 2) → Bool)
  infer_instance

/-- The recommendation profile assigning `false` to both players. -/
def target : Profile game := fun _ => false

@[simp] theorem target_apply (i : Fin 2) : target i = false := rfl

@[simp] theorem eu_zero (σ : Profile game) :
    game.eu σ 0 = if σ 0 = true then 2 else 0 := by
  simp [game]

@[simp] theorem eu_one (σ : Profile game) :
    game.eu σ 1 = 0 := by
  simp [game]

/-- Degenerate recommendation law at the bad recommendation. -/
noncomputable def law : PMF (Profile game) :=
  PMF.pure target

def devToTrue : game.Strategy 0 → game.Strategy 0 :=
  fun _ => true

lemma swapRegret_zero_devToTrue :
    game.swapRegret law 0 devToTrue = 2 := by
  rw [KernelGame.swapRegret,
    game.correlatedEu_unilateralDeviationDistribution_eq_expect_update,
    law, KernelGame.correlatedEu_pure]
  simp [target, devToTrue]

lemma swapRegret_zero_le_two (dev : game.Strategy 0 → game.Strategy 0) :
    game.swapRegret law 0 dev ≤ 2 := by
  rw [KernelGame.swapRegret,
    game.correlatedEu_unilateralDeviationDistribution_eq_expect_update,
    law, KernelGame.correlatedEu_pure]
  simp [target]
  split_ifs <;> norm_num

lemma swapRegret_one_eq_zero (dev : game.Strategy 1 → game.Strategy 1) :
    game.swapRegret law 1 dev = 0 := by
  rw [KernelGame.swapRegret,
    game.correlatedEu_unilateralDeviationDistribution_eq_expect_update,
    law, KernelGame.correlatedEu_pure]
  simp

lemma maxSwapRegret_zero_le_two :
    game.maxSwapRegret law 0 ≤ 2 := by
  rw [KernelGame.maxSwapRegret]
  apply Finset.sup'_le
  intro dev _
  exact swapRegret_zero_le_two dev

lemma maxSwapRegret_one_le_zero :
    game.maxSwapRegret law 1 ≤ 0 := by
  rw [KernelGame.maxSwapRegret]
  apply Finset.sup'_le
  intro dev _
  rw [swapRegret_one_eq_zero dev]

lemma finiteExpectedDeviceImplPrice_le_two :
    game.finiteExpectedDeviceImplPrice law ≤ 2 := by
  rw [game.finiteExpectedDeviceImplPrice_eq_sum_maxSwapRegret law]
  rw [Fin.sum_univ_two]
  linarith [maxSwapRegret_zero_le_two, maxSwapRegret_one_le_zero]

lemma not_isOneCorrelatedEq :
    ¬ game.IsεCorrelatedEq 1 law := by
  intro h
  rw [game.isεCorrelatedEq_iff_swapRegret_le] at h
  have hreg := h 0 devToTrue
  rw [swapRegret_zero_devToTrue] at hreg
  norm_num at hreg

/-- The implication `finite expected device price ≤ |N|ε → ε-CE` is false for
the standard per-player definition of approximate correlated equilibrium. -/
theorem finiteExpectedDeviceImplPrice_le_card_mul_one_and_not_isOneCorrelatedEq :
    game.finiteExpectedDeviceImplPrice law ≤ (Fintype.card (Fin 2) : ℝ) * 1 ∧
      ¬ game.IsεCorrelatedEq 1 law := by
  constructor
  · norm_num
    exact finiteExpectedDeviceImplPrice_le_two
  · exact not_isOneCorrelatedEq

end ExpectedDeviceEpsilonCounterexample

namespace SelectionAdmissibleNotAnalyticExample

/-!
The semantic regular-transfer condition is strictly weaker than analytic
admissibility.  The example uses the two-point upper-set topology: `{good}` is
open but not closed, so the nonnegative indicator payoff of `{good}` makes
`good` dominant while failing upper semicontinuity.
-/

inductive Strategy where
  | bad
  | good
  deriving DecidableEq

open Strategy

instance strategyFintype : Fintype Strategy where
  elems := {bad, good}
  complete := by
    intro s
    cases s <;> simp

instance strategyPreorder : Preorder Strategy where
  le s t := s = bad ∨ t = good
  le_refl := by
    intro s
    cases s <;> simp
  le_trans := by
    intro a b c hab hbc
    cases a <;> cases b <;> cases c <;> simp at hab hbc ⊢

instance strategyTopologicalSpace : TopologicalSpace Strategy :=
  Topology.upperSet Strategy

instance strategyIsUpperSet : Topology.IsUpperSet Strategy where
  topology_eq_upperSetTopology := rfl

instance strategyCompactSpace : CompactSpace Strategy where
  isCompact_univ := Set.finite_univ.isCompact

/-- One-player zero-payoff game on the two-point upper-set space. -/
noncomputable def game : KernelGame (Fin 1) :=
  KernelGame.ofPureEU (fun _ : Fin 1 => Strategy) (fun _ _ => 0)

instance gameStrategyTopologicalSpace (i : Fin 1) :
    TopologicalSpace (game.Strategy i) := by
  change TopologicalSpace Strategy
  infer_instance

instance gameStrategyCompactSpace (i : Fin 1) :
    CompactSpace (game.Strategy i) := by
  change CompactSpace Strategy
  infer_instance

/-- The good point is the intended singleton target. -/
def target : Profile game :=
  fun _ => good

/-- The nonnegative indicator of the good point. It makes `good` dominant but is
not upper semicontinuous in the upper-set topology. -/
def spikeTransfer : Profile game → Payoff (Fin 1) :=
  fun σ _ =>
    match σ 0 with
    | bad => 0
    | good => 1

theorem spikeTransfer_nonneg :
    ∀ σ i, 0 ≤ spikeTransfer σ i := by
  intro σ i
  dsimp [spikeTransfer]
  split <;> norm_num

lemma singleton_good_not_closed :
    ¬ IsClosed ({good} : Set Strategy) := by
  intro hclosed
  have hlower : IsLowerSet ({good} : Set Strategy) :=
    (Topology.IsUpperSet.isClosed_iff_isLower (α := Strategy)).mp hclosed
  have hle : bad ≤ good := by simp [(· ≤ ·)]
  have hbad_mem := hlower hle (by simp)
  simp at hbad_mem

lemma preimage_superlevel_eq_singleton_good :
    ((fun s : Strategy =>
        (game.subsidize spikeTransfer).eu (Function.update target 0 s) 0) ⁻¹'
          Set.Ici ((1 / 2 : ℝ))) = ({good} : Set Strategy) := by
  ext s
  cases s
  · simp [game, KernelGame.ofPureEU, KernelGame.eu, KernelGame.subsidize,
      spikeTransfer, PMF.pure_map, expect_pure, Function.update]
  · simp [game, KernelGame.ofPureEU, KernelGame.eu, KernelGame.subsidize,
      spikeTransfer, PMF.pure_map, expect_pure, Function.update]
    norm_num

lemma subsidized_target_eu_eq_one
    (σ : (game.subsidize spikeTransfer).Profile) :
    (game.subsidize spikeTransfer).eu (Function.update σ 0 (target 0)) 0 = 1 := by
  simp [game, KernelGame.ofPureEU, KernelGame.eu, KernelGame.subsidize,
    spikeTransfer, target, PMF.pure_map, expect_pure, Function.update]

lemma subsidized_update_eu_le_one
    (σ : (game.subsidize spikeTransfer).Profile)
    (t : (game.subsidize spikeTransfer).Strategy 0) :
    (game.subsidize spikeTransfer).eu (Function.update σ 0 t) 0 ≤ 1 := by
  cases t <;>
    simp [game, KernelGame.ofPureEU, KernelGame.eu, KernelGame.subsidize,
      spikeTransfer, PMF.pure_map, expect_pure, Function.update]

lemma target_isDominant :
    (game.subsidize spikeTransfer).IsDominant 0 (target 0) := by
  intro σ t
  have hleft := subsidized_target_eu_eq_one σ
  have hright := subsidized_update_eu_le_one σ t
  linarith

/-- The spike transfer satisfies the semantic selection condition. -/
theorem spikeTransfer_selectionAdmissible :
    game.RegularSelectionAdmissibleAt spikeTransfer target := by
  apply RegularSelectionAdmissibleAt.of_dominant
  intro i
  fin_cases i
  exact target_isDominant

/-- The same transfer is not analytically admissible. -/
theorem spikeTransfer_not_analyticAdmissible :
    ¬ game.RegularAnalyticAdmissible spikeTransfer := by
  intro h
  have husc :
      UpperSemicontinuous
        (fun s : Strategy =>
          (game.subsidize spikeTransfer).eu (Function.update target 0 s) 0) := by
    exact upperSemicontinuousOn_univ_iff.mp (h 0 target)
  have hclosed :=
    (upperSemicontinuous_iff_isClosed_preimage.mp husc) ((1 / 2 : ℝ))
  rw [preimage_superlevel_eq_singleton_good] at hclosed
  exact singleton_good_not_closed hclosed

/-- Selection-admissibility is strictly weaker than analytic admissibility even
for nonnegative transfers. -/
theorem selectionAdmissible_and_not_analyticAdmissible :
    (∀ σ i, 0 ≤ spikeTransfer σ i) ∧
      game.RegularSelectionAdmissibleAt spikeTransfer target ∧
      ¬ game.RegularAnalyticAdmissible spikeTransfer :=
  ⟨spikeTransfer_nonneg, spikeTransfer_selectionAdmissible,
    spikeTransfer_not_analyticAdmissible⟩

end SelectionAdmissibleNotAnalyticExample

namespace MetricSelectionAdmissibleNotAnalyticExample

/-!
The same separation can be witnessed on a compact metric space.  On the
strategy interval `[0,1]`, the nonnegative transfer that pays `1` away from
`0` makes the target `1` a semantic undominated best response, but the
superlevel set `(0,1]` is not closed, so the subsidized payoff is not upper
semicontinuous.
-/

abbrev Strategy := Set.Icc (0 : ℝ) 1

/-- One-player zero-payoff game on the compact metric interval `[0,1]`. -/
noncomputable def game : KernelGame (Fin 1) :=
  KernelGame.ofPureEU (fun _ : Fin 1 => Strategy) (fun _ _ => 0)

instance gameStrategyTopologicalSpace (i : Fin 1) :
    TopologicalSpace (game.Strategy i) := by
  change TopologicalSpace Strategy
  infer_instance

instance gameStrategyCompactSpace (i : Fin 1) :
    CompactSpace (game.Strategy i) := by
  change CompactSpace Strategy
  infer_instance

/-- The left endpoint. -/
def zero : Strategy :=
  ⟨0, by simp⟩

/-- The intended target action, the right endpoint. -/
def one : Strategy :=
  ⟨1, by norm_num⟩

/-- The singleton target profile. -/
def target : Profile game :=
  fun _ => one

/-- The real coordinate of an action in the one-player interval game. -/
def actionReal (s : game.Strategy 0) : ℝ :=
  ((show Strategy from s) : ℝ)

/-- Nonnegative transfer paying `1` at every positive action and `0` at `0`. -/
noncomputable def spikeTransfer : Profile game → Payoff (Fin 1) :=
  fun σ _ => if actionReal (σ 0) = 0 then 0 else 1

theorem spikeTransfer_nonneg :
    ∀ σ i, 0 ≤ spikeTransfer σ i := by
  intro σ i
  dsimp [spikeTransfer]
  split <;> norm_num

lemma positive_set_not_closed :
    ¬ IsClosed ({s : Strategy | 0 < (s : ℝ)} : Set Strategy) := by
  intro hclosed
  have hclosure : (0 : Strategy) ∈
      closure ({s : Strategy | 0 < (s : ℝ)} : Set Strategy) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := min (ε / 2) (1 / 2)
    have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
    have hδle_one : δ ≤ 1 := by
      calc
        δ ≤ (1 / 2 : ℝ) := min_le_right _ _
        _ ≤ 1 := by norm_num
    let s : Strategy := ⟨δ, ⟨le_of_lt hδpos, hδle_one⟩⟩
    refine ⟨s, hδpos, ?_⟩
    have hdist : dist (0 : Strategy) s = δ := by
      rw [Subtype.dist_eq]
      simp [s, Real.dist_eq, abs_of_nonneg (le_of_lt hδpos)]
    rw [hdist]
    calc
      δ ≤ ε / 2 := min_le_left _ _
      _ < ε := by linarith
  rw [hclosed.closure_eq] at hclosure
  exact (not_lt_of_ge (show 0 ≤ ((0 : Strategy) : ℝ) by norm_num)) hclosure

lemma preimage_superlevel_eq_positive :
    ((fun s : Strategy =>
        (game.subsidize spikeTransfer).eu (Function.update target 0 s) 0) ⁻¹'
          Set.Ici ((1 / 2 : ℝ))) =
      ({s : Strategy | 0 < (s : ℝ)} : Set Strategy) := by
  ext s
  change ((1 / 2 : ℝ) ≤
      (game.subsidize spikeTransfer).eu
        (Function.update (show Profile (game.subsidize spikeTransfer) from target) 0 s) 0) ↔
    0 < (s : ℝ)
  by_cases hs : s = (0 : Strategy)
  · subst hs
    have heu :
        (game.subsidize spikeTransfer).eu
            (Function.update (show Profile (game.subsidize spikeTransfer) from target)
              0 (0 : Strategy)) 0 =
          0 := by
      simp [game, KernelGame.ofPureEU, KernelGame.eu, KernelGame.subsidize,
        spikeTransfer, actionReal, PMF.pure_map]
    rw [heu]
    simp
  · have hs_val_ne : (s : ℝ) ≠ 0 := by
      intro hval
      exact hs (Subtype.ext hval)
    have hs_pos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs_val_ne)
    have heu :
        (game.subsidize spikeTransfer).eu
            (Function.update (show Profile (game.subsidize spikeTransfer) from target)
              0 s) 0 = 1 := by
      simp [game, KernelGame.ofPureEU, KernelGame.eu, KernelGame.subsidize,
        spikeTransfer, actionReal, PMF.pure_map, hs]
    rw [heu]
    exact ⟨fun _ => hs_pos, fun _ => by norm_num⟩

lemma subsidized_target_eu_eq_one
    (σ : (game.subsidize spikeTransfer).Profile) :
    (game.subsidize spikeTransfer).eu (Function.update σ 0 (target 0)) 0 = 1 := by
  have hone_ne_zero : one ≠ (0 : Strategy) := by
    intro h
    have hval := congrArg Subtype.val h
    norm_num [one] at hval
  simp [game, KernelGame.ofPureEU, KernelGame.eu, KernelGame.subsidize,
    spikeTransfer, actionReal, target, PMF.pure_map, hone_ne_zero]

lemma subsidized_update_eu_le_one
    (σ : (game.subsidize spikeTransfer).Profile)
    (t : (game.subsidize spikeTransfer).Strategy 0) :
    (game.subsidize spikeTransfer).eu (Function.update σ 0 t) 0 ≤ 1 := by
  simp [game, KernelGame.ofPureEU, KernelGame.eu, KernelGame.subsidize,
    spikeTransfer, actionReal, PMF.pure_map]
  split <;> norm_num

lemma target_isDominant :
    (game.subsidize spikeTransfer).IsDominant 0 (target 0) := by
  intro σ t
  have hleft := subsidized_target_eu_eq_one σ
  have hright := subsidized_update_eu_le_one σ t
  linarith

/-- The spike transfer satisfies the semantic selection condition. -/
theorem spikeTransfer_selectionAdmissible :
    game.RegularSelectionAdmissibleAt spikeTransfer target := by
  apply RegularSelectionAdmissibleAt.of_dominant
  intro i
  fin_cases i
  exact target_isDominant

/-- The same transfer is not analytically admissible, even though the strategy
space is compact and metrizable. -/
theorem spikeTransfer_not_analyticAdmissible :
    ¬ game.RegularAnalyticAdmissible spikeTransfer := by
  intro h
  have husc :
      UpperSemicontinuous
        (fun s : Strategy =>
          (game.subsidize spikeTransfer).eu (Function.update target 0 s) 0) := by
    exact upperSemicontinuousOn_univ_iff.mp (h 0 target)
  have hclosed :=
    (upperSemicontinuous_iff_isClosed_preimage.mp husc) ((1 / 2 : ℝ))
  rw [preimage_superlevel_eq_positive] at hclosed
  exact positive_set_not_closed hclosed

/-- Selection-admissibility is strictly weaker than analytic admissibility even
on a compact metric strategy space and for nonnegative transfers. -/
theorem selectionAdmissible_and_not_analyticAdmissible :
    (∀ σ i, 0 ≤ spikeTransfer σ i) ∧
      game.RegularSelectionAdmissibleAt spikeTransfer target ∧
      ¬ game.RegularAnalyticAdmissible spikeTransfer :=
  ⟨spikeTransfer_nonneg, spikeTransfer_selectionAdmissible,
    spikeTransfer_not_analyticAdmissible⟩

end MetricSelectionAdmissibleNotAnalyticExample

/-- A one-player two-action game with constant zero payoff. -/
noncomputable abbrev onePlayerTieGame : KernelGame (Fin 1) :=
  { Strategy := fun _ => Bool
    Outcome := Unit
    utility := fun _ _ => 0
    outcomeKernel := fun _ => PMF.pure () }

/-- The unique one-player profile choosing `a`. -/
def onePlayerProfile (a : Bool) : Profile onePlayerTieGame :=
  fun _ => a

@[simp] theorem onePlayerTieGame_eu (σ : Profile onePlayerTieGame) (i : Fin 1) :
    onePlayerTieGame.eu σ i = 0 := by
  simp [KernelGame.eu, onePlayerTieGame]

@[simp] theorem onePlayerTieGame_subsidize_eu
    (V : Profile onePlayerTieGame → Payoff (Fin 1))
    (σ : Profile onePlayerTieGame) (i : Fin 1) :
    (onePlayerTieGame.subsidize V).eu σ i = V σ i := by
  simp

@[simp] theorem onePlayerProfile_update (σ : Profile onePlayerTieGame) (a : Bool) :
    Function.update σ 0 a = onePlayerProfile a := by
  funext i
  fin_cases i
  simp [onePlayerProfile]

/-- In the tie game, every one-player profile is Nash. -/
theorem onePlayerTie_target_isNash :
    onePlayerTieGame.IsNash (onePlayerProfile false) := by
  intro i s
  simp

/-- The corrected singleton price formula still gives price zero in the
one-player tie game. The issue is non-attainment, not the infimum. -/
theorem onePlayerTie_implPrice_singleton_eq_zero :
    onePlayerTieGame.implPrice
      ({onePlayerProfile false} : Set (Profile onePlayerTieGame)) = 0 := by
  rw [implPrice_singleton (G := onePlayerTieGame) (z := onePlayerProfile false)]
  exact Finset.sum_eq_zero fun i _ =>
    implementationGap_eq_zero_of_isNash (G := onePlayerTieGame)
      (onePlayerProfile false) onePlayerTie_target_isNash i

/-- A zero-utility game with a fully revealing outcome kernel. It is cheap to
implement every singleton because payoffs do not depend on outcomes, but the
kernel is not differentially private. -/
noncomputable abbrev revealingZeroUtilityGame : KernelGame (Fin 1) :=
  { Strategy := fun _ => Bool
    Outcome := Bool
    utility := fun _ _ => 0
    outcomeKernel := fun σ => PMF.pure (σ 0) }

instance revealingZeroUtilityGame_outcome_finite :
    Finite revealingZeroUtilityGame.Outcome := by
  change Finite Bool
  infer_instance

/-- A profile in the revealing zero-utility game. -/
def revealingZeroUtilityProfile (a : Bool) : Profile revealingZeroUtilityGame :=
  fun _ => a

@[simp] theorem revealingZeroUtilityGame_eu
    (σ : Profile revealingZeroUtilityGame) (i : Fin 1) :
    revealingZeroUtilityGame.eu σ i = 0 := by
  simp [KernelGame.eu, revealingZeroUtilityGame]

theorem revealingZeroUtilityGame_isNash
    (z : Profile revealingZeroUtilityGame) :
    revealingZeroUtilityGame.IsNash z := by
  intro i s
  simp

/-- Cheap implementation does not imply differential privacy: this kernel
reveals the one player's action exactly, so it is not `0`-DP. -/
theorem revealingZeroUtilityGame_not_zeroDifferentiallyPrivate :
    ¬ revealingZeroUtilityGame.IsEpsilonDifferentiallyPrivate 0 := by
  intro hDP
  have hbad := hDP 0 (revealingZeroUtilityProfile false) true true
  simp [revealingZeroUtilityGame, revealingZeroUtilityProfile, PMF.pure_apply] at hbad
  norm_num at hbad

/-- Despite nonprivacy, every singleton has zero implementation price because
all utilities are identically zero. -/
theorem revealingZeroUtilityGame_implPrice_singleton_eq_zero
    (z : Profile revealingZeroUtilityGame) :
    revealingZeroUtilityGame.implPrice ({z} : Set (Profile revealingZeroUtilityGame)) = 0 := by
  rw [implPrice_singleton (G := revealingZeroUtilityGame) (z := z)]
  exact Finset.sum_eq_zero fun i _ =>
    implementationGap_eq_zero_of_isNash (G := revealingZeroUtilityGame) z
      (revealingZeroUtilityGame_isNash z) i

/-- A minimal positive-ε differential-privacy witness. The outcome kernel is
strategy-independent, so the game is `ε`-differentially private for every
nonnegative `ε`; utilities are nonzero to exercise the bounded-utility
hypotheses of the DP price theorem. -/
noncomputable abbrev constantPrivateGame : KernelGame (Fin 1) :=
  { Strategy := fun _ => Bool
    Outcome := PUnit
    utility := fun _ _ => 1
    outcomeKernel := fun _ => PMF.pure PUnit.unit }

instance constantPrivateGame_outcome_finite :
    Finite constantPrivateGame.Outcome := by
  change Finite PUnit
  infer_instance

/-- A profile in the constant private game. -/
def constantPrivateProfile (a : Bool) : Profile constantPrivateGame :=
  fun _ => a

@[simp] theorem constantPrivateGame_eu
    (σ : Profile constantPrivateGame) (i : Fin 1) :
    constantPrivateGame.eu σ i = 1 := by
  simp [KernelGame.eu, constantPrivateGame]

theorem constantPrivateGame_isEpsilonDifferentiallyPrivate
    {ε : ℝ} (hε : 0 ≤ ε) :
    constantPrivateGame.IsEpsilonDifferentiallyPrivate ε := by
  intro i σ s ω
  cases ω
  simpa [constantPrivateGame] using Real.one_le_exp hε

theorem constantPrivateGame_oneDifferentiallyPrivate :
    constantPrivateGame.IsEpsilonDifferentiallyPrivate 1 :=
  constantPrivateGame_isEpsilonDifferentiallyPrivate (by norm_num)

theorem constantPrivateGame_implPrice_singleton_dp_bound
    (z : Profile constantPrivateGame) :
    constantPrivateGame.implPrice ({z} : Set (Profile constantPrivateGame)) ≤
      (Fintype.card (Fin 1) : ℝ) * ((Real.exp 1 - 1) * 1) :=
  implPrice_singleton_le_card_mul_dp_bound
    (G := constantPrivateGame) constantPrivateGame_oneDifferentiallyPrivate
    (by norm_num) (by intro ω i; norm_num [constantPrivateGame])
    (by intro ω i; norm_num [constantPrivateGame]) z

/-- Payoffs for a mixed-extension counterexample to the converse of Theorem 3.
At the pure target `(false, false)`, player 0 can profitably deviate to `true`;
symmetrically, player 1 can profitably deviate to `true`. -/
def mixedConversePayoff (σ : (i : Fin 2) → Bool) : Payoff (Fin 2) :=
  fun
    | 0 => if σ 0 = true ∧ σ 1 = false then 1 else 0
    | 1 => if σ 0 = false ∧ σ 1 = true then 1 else 0

/-- The finite two-player game used to falsify the unrestricted converse of the
mixed-extension k-implementation theorem. -/
noncomputable abbrev mixedConverseGame : KernelGame (Fin 2) :=
  KernelGame.ofPureEU (fun _ : Fin 2 => Bool) mixedConversePayoff

instance mixedConverseGame_outcome_finite : Finite mixedConverseGame.Outcome := by
  change Finite ((i : Fin 2) → Bool)
  infer_instance

/-- Binary labels for the mixed-converse counterexample. -/
def mixedConverseLabels : BinaryActionLabels mixedConverseGame where
  player := finTwoEquiv
  toBool := fun _ => Equiv.refl Bool

@[simp] theorem mixedConverseLabels_action (i : Fin 2) (b : Bool) :
    mixedConverseLabels.action i b = b := by
  rfl

@[simp] theorem mixedConverseLabels_player_zero :
    mixedConverseLabels.player 0 = false := by
  rfl

@[simp] theorem mixedConverseLabels_player_one :
    mixedConverseLabels.player 1 = true := by
  rfl

@[simp] theorem mixedConverseLabels_playerOf_false :
    mixedConverseLabels.playerOf false = 0 := by
  rfl

@[simp] theorem mixedConverseLabels_playerOf_true :
    mixedConverseLabels.playerOf true = 1 := by
  rfl

/-- Probability assigned to the target action `false`. -/
def mixedConverseTargetProb (q : PMF Bool) : ℝ :=
  (q false).toReal

theorem mixedConverseTargetProb_nonneg (q : PMF Bool) :
    0 ≤ mixedConverseTargetProb q :=
  ENNReal.toReal_nonneg

theorem mixedConverseTargetProb_le_one (q : PMF Bool) :
    mixedConverseTargetProb q ≤ 1 :=
  ENNReal.toReal_le_of_le_ofReal zero_le_one (by
    simpa using PMF.coe_le_one q false)

@[simp] theorem mixedConverseTargetProb_pure_false :
    mixedConverseTargetProb (PMF.pure false) = 1 := by
  simp [mixedConverseTargetProb]

@[simp] theorem mixedConverseTargetProb_pure_true :
    mixedConverseTargetProb (PMF.pure true) = 0 := by
  simp [mixedConverseTargetProb]

theorem mixedConverse_true_toReal (q : PMF Bool) :
    (q true).toReal = 1 - mixedConverseTargetProb q := by
  have hsum := Math.Probability.pmf_toReal_sum_one q
  rw [Fintype.sum_bool] at hsum
  dsimp [mixedConverseTargetProb]
  linarith

theorem mixedConverseTargetProb_lt_one_of_ne_pure_false
    (q : PMF Bool) (hq : q ≠ PMF.pure false) :
    mixedConverseTargetProb q < 1 := by
  obtain ⟨b, hbne, hbpos⟩ := exists_ne_of_ne_pure q hq
  have hbtrue : b = true := by
    cases b
    · contradiction
    · rfl
  subst b
  have hpos : 0 < (q true).toReal :=
    ENNReal.toReal_pos hbpos (PMF.apply_ne_top q true)
  have hsum := Math.Probability.pmf_toReal_sum_one q
  rw [Fintype.sum_bool] at hsum
  dsimp [mixedConverseTargetProb]
  linarith

/-- The Boolean PMF with the requested probability on `false`. -/
noncomputable def boolPmfFalseProb (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : PMF Bool :=
  PMF.ofFintype
    (fun b : Bool => if b = false then ENNReal.ofReal p else ENNReal.ofReal (1 - p))
    (by
      rw [Fintype.sum_bool]
      simp only [Bool.true_eq_false, ↓reduceIte]
      rw [add_comm]
      rw [← ENNReal.ofReal_add hp0 (sub_nonneg.mpr hp1)]
      norm_num)

@[simp] theorem mixedConverseTargetProb_boolPmfFalseProb
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    mixedConverseTargetProb (boolPmfFalseProb p hp0 hp1) = p := by
  simp [mixedConverseTargetProb, boolPmfFalseProb, hp0]

theorem boolPmfFalseProb_ne_pure_false {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp_lt : p < 1) :
    boolPmfFalseProb p hp0 hp1 ≠ PMF.pure false := by
  intro h
  have hp : p = 1 := by
    calc
      p = mixedConverseTargetProb (boolPmfFalseProb p hp0 hp1) := by simp
      _ = mixedConverseTargetProb (PMF.pure false) := by rw [h]
      _ = 1 := by simp
  linarith

/-- Move a mixed action halfway toward the target action `false`. -/
noncomputable def mixedConverseMidpointToFalse (q : PMF Bool) : PMF Bool :=
  boolPmfFalseProb ((1 + mixedConverseTargetProb q) / 2)
    (by
      have h0 := mixedConverseTargetProb_nonneg q
      linarith)
    (by
      have h1 := mixedConverseTargetProb_le_one q
      linarith)

@[simp] theorem mixedConverseTargetProb_midpointToFalse (q : PMF Bool) :
    mixedConverseTargetProb (mixedConverseMidpointToFalse q) =
      (1 + mixedConverseTargetProb q) / 2 := by
  simp [mixedConverseMidpointToFalse]

theorem mixedConverse_midpoint_ne_pure_false_of_ne
    (q : PMF Bool) (hq : q ≠ PMF.pure false) :
    mixedConverseMidpointToFalse q ≠ PMF.pure false := by
  apply boolPmfFalseProb_ne_pure_false
  have hlt := mixedConverseTargetProb_lt_one_of_ne_pure_false q hq
  linarith

theorem mixedConverseTargetProb_lt_midpoint_of_ne
    (q : PMF Bool) (hq : q ≠ PMF.pure false) :
    mixedConverseTargetProb q <
      mixedConverseTargetProb (mixedConverseMidpointToFalse q) := by
  rw [mixedConverseTargetProb_midpointToFalse]
  have hlt := mixedConverseTargetProb_lt_one_of_ne_pure_false q hq
  linarith

theorem mixedConverse_eu_zero (σ : Profile mixedConverseGame.mixedExtension) :
    mixedConverseGame.mixedExtension.eu σ 0 =
      (1 - mixedConverseTargetProb (σ 0)) * mixedConverseTargetProb (σ 1) := by
  rw [mixedConverseLabels.mixedExtension_eu_binary σ 0]
  let qT : PMF Bool := σ (mixedConverseLabels.playerOf true)
  let qF : PMF Bool := σ (mixedConverseLabels.playerOf false)
  let f : (Bool → Bool) → ℝ := fun x =>
    ((qT (mixedConverseLabels.action (mixedConverseLabels.playerOf true) (x true))).toReal *
      (qF (mixedConverseLabels.action (mixedConverseLabels.playerOf false) (x false))).toReal) *
      mixedConverseGame.eu
        (fun i => mixedConverseLabels.action i (x (mixedConverseLabels.player i))) 0
  change ∑ x, f x =
    (1 - mixedConverseTargetProb (σ 0)) * mixedConverseTargetProb (σ 1)
  rw [Fintype.sum_equiv (Equiv.boolArrowEquivProd Bool) f
    (fun p : Bool × Bool => f ((Equiv.boolArrowEquivProd Bool).symm p))
    (by intro x; rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_bool, Fintype.sum_bool]
  norm_num [f, qT, qF, Equiv.boolArrowEquivProd, mixedConversePayoff,
    mixedConverseTargetProb, mixedConverse_true_toReal]
  rw [mixedConverseLabels_playerOf_true, mixedConverseLabels_playerOf_false]
  ring

theorem mixedConverse_eu_one (σ : Profile mixedConverseGame.mixedExtension) :
    mixedConverseGame.mixedExtension.eu σ 1 =
      mixedConverseTargetProb (σ 0) * (1 - mixedConverseTargetProb (σ 1)) := by
  rw [mixedConverseLabels.mixedExtension_eu_binary σ 1]
  let qT : PMF Bool := σ (mixedConverseLabels.playerOf true)
  let qF : PMF Bool := σ (mixedConverseLabels.playerOf false)
  let f : (Bool → Bool) → ℝ := fun x =>
    ((qT (mixedConverseLabels.action (mixedConverseLabels.playerOf true) (x true))).toReal *
      (qF (mixedConverseLabels.action (mixedConverseLabels.playerOf false) (x false))).toReal) *
      mixedConverseGame.eu
        (fun i => mixedConverseLabels.action i (x (mixedConverseLabels.player i))) 1
  change ∑ x, f x =
    mixedConverseTargetProb (σ 0) * (1 - mixedConverseTargetProb (σ 1))
  rw [Fintype.sum_equiv (Equiv.boolArrowEquivProd Bool) f
    (fun p : Bool × Bool => f ((Equiv.boolArrowEquivProd Bool).symm p))
    (by intro x; rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_prod_type]
  rw [Fintype.sum_bool, Fintype.sum_bool]
  norm_num [f, qT, qF, Equiv.boolArrowEquivProd, mixedConversePayoff,
    mixedConverseTargetProb, mixedConverse_true_toReal]
  rw [mixedConverseLabels_playerOf_true, mixedConverseLabels_playerOf_false]
  ring

/-- The non-Nash mixed target used in the unrestricted Theorem 3 converse
counterexample. -/
noncomputable def mixedConverseMixedTarget : Profile mixedConverseGame.mixedExtension :=
  fun _ => PMF.pure false

open Classical in
/-- Transfer implementing the non-Nash mixed target in the mixed extension.
The non-target branch rewards higher probability on `false`; hence every
non-target mix is dominated by a closer-to-target non-target mix. -/
noncomputable def mixedConverseTransfer :
    Profile mixedConverseGame.mixedExtension → Payoff (Fin 2) :=
  fun σ i =>
    match i with
    | 0 =>
        if σ 0 = PMF.pure false then
          4 * (1 - mixedConverseTargetProb (σ 1))
        else
          2 * mixedConverseTargetProb (σ 0)
    | 1 =>
        if σ 1 = PMF.pure false then
          4 * (1 - mixedConverseTargetProb (σ 0))
        else
          2 * mixedConverseTargetProb (σ 1)

@[simp] theorem mixedConverseTransfer_target (i : Fin 2) :
    mixedConverseTransfer mixedConverseMixedTarget i = 0 := by
  fin_cases i <;> simp [mixedConverseTransfer, mixedConverseMixedTarget]

theorem mixedConverseTransfer_nonneg :
    ∀ σ i, 0 ≤ mixedConverseTransfer σ i := by
  intro σ i
  fin_cases i <;>
    simp only [mixedConverseTransfer]
  · split
    · have hle := mixedConverseTargetProb_le_one (σ 1)
      nlinarith
    · have hnonneg := mixedConverseTargetProb_nonneg (σ 0)
      nlinarith
  · split
    · have hle := mixedConverseTargetProb_le_one (σ 0)
      nlinarith
    · have hnonneg := mixedConverseTargetProb_nonneg (σ 1)
      nlinarith

theorem mixedConverse_midpoint_strictlyDominates_zero
    {q : PMF Bool} (hq : q ≠ PMF.pure false) :
    (mixedConverseGame.mixedExtension.subsidize mixedConverseTransfer).StrictlyDominates
      0 (mixedConverseMidpointToFalse q) q := by
  intro σ
  have hm_ne := mixedConverse_midpoint_ne_pure_false_of_ne q hq
  have hq_lt_mid := mixedConverseTargetProb_lt_midpoint_of_ne q hq
  have hq_lt_one := mixedConverseTargetProb_lt_one_of_ne_pure_false q hq
  have hop_le := mixedConverseTargetProb_le_one (σ 1)
  rw [mixedExtension_subsidize_eu, mixedExtension_subsidize_eu]
  rw [mixedConverse_eu_zero, mixedConverse_eu_zero]
  simp [mixedConverseTransfer, hq, hm_ne, Function.update]
  nlinarith

theorem mixedConverse_midpoint_strictlyDominates_one
    {q : PMF Bool} (hq : q ≠ PMF.pure false) :
    (mixedConverseGame.mixedExtension.subsidize mixedConverseTransfer).StrictlyDominates
      1 (mixedConverseMidpointToFalse q) q := by
  intro σ
  have hm_ne := mixedConverse_midpoint_ne_pure_false_of_ne q hq
  have hq_lt_mid := mixedConverseTargetProb_lt_midpoint_of_ne q hq
  have hq_lt_one := mixedConverseTargetProb_lt_one_of_ne_pure_false q hq
  have hop_le := mixedConverseTargetProb_le_one (σ 0)
  rw [mixedExtension_subsidize_eu, mixedExtension_subsidize_eu]
  rw [mixedConverse_eu_one, mixedConverse_eu_one]
  simp [mixedConverseTransfer, hq, hm_ne, Function.update]
  nlinarith

theorem mixedConverse_target_undominated_zero :
    (mixedConverseGame.mixedExtension.subsidize mixedConverseTransfer).IsUndominated
      0 (PMF.pure false) := by
  classical
  intro t ht
  by_cases ht_target : t = PMF.pure false
  · subst t
    exact WeaklyStrictlyDominates.irrefl
      (G := mixedConverseGame.mixedExtension.subsidize mixedConverseTransfer)
      (who := 0) (PMF.pure false) ht
  · let σ : Profile mixedConverseGame.mixedExtension :=
      fun i => if i = 1 then PMF.pure true else PMF.pure false
    have hweak := ht.toWeaklyDominates σ
    rw [mixedExtension_subsidize_eu, mixedExtension_subsidize_eu] at hweak
    rw [mixedConverse_eu_zero, mixedConverse_eu_zero] at hweak
    let t' : PMF Bool := t
    have ht_target' : t' ≠ PMF.pure false := by
      intro h
      exact ht_target (by simpa [t'] using h)
    have hweak' : 4 ≤ if t' = PMF.pure false then 4 else 2 * mixedConverseTargetProb t' := by
      simpa [mixedConverseTransfer, σ, Function.update, t'] using hweak
    rw [if_neg ht_target'] at hweak'
    have ht_le' := mixedConverseTargetProb_le_one t'
    nlinarith

theorem mixedConverse_target_undominated_one :
    (mixedConverseGame.mixedExtension.subsidize mixedConverseTransfer).IsUndominated
      1 (PMF.pure false) := by
  classical
  intro t ht
  by_cases ht_target : t = PMF.pure false
  · subst t
    exact WeaklyStrictlyDominates.irrefl
      (G := mixedConverseGame.mixedExtension.subsidize mixedConverseTransfer)
      (who := 1) (PMF.pure false) ht
  · let σ : Profile mixedConverseGame.mixedExtension :=
      fun i => if i = 0 then PMF.pure true else PMF.pure false
    have hweak := ht.toWeaklyDominates σ
    rw [mixedExtension_subsidize_eu, mixedExtension_subsidize_eu] at hweak
    rw [mixedConverse_eu_one, mixedConverse_eu_one] at hweak
    let t' : PMF Bool := t
    have ht_target' : t' ≠ PMF.pure false := by
      intro h
      exact ht_target (by simpa [t'] using h)
    have hweak' : 4 ≤ if t' = PMF.pure false then 4 else 2 * mixedConverseTargetProb t' := by
      simpa [mixedConverseTransfer, σ, Function.update, t'] using hweak
    rw [if_neg ht_target'] at hweak'
    have ht_le' := mixedConverseTargetProb_le_one t'
    nlinarith

theorem mixedConverse_target_mem_undominated :
    mixedConverseMixedTarget ∈
      (mixedConverseGame.mixedExtension.subsidize mixedConverseTransfer).undominatedProfiles := by
  intro i
  fin_cases i
  · exact mixedConverse_target_undominated_zero
  · exact mixedConverse_target_undominated_one

theorem mixedConverse_undominated_subset_singleton :
    ∀ σ : Profile mixedConverseGame.mixedExtension,
      σ ∈ (mixedConverseGame.mixedExtension.subsidize mixedConverseTransfer).undominatedProfiles →
        σ ∈ ({mixedConverseMixedTarget} : Set (Profile mixedConverseGame.mixedExtension)) := by
  intro σ hσ
  have h0 : σ 0 = PMF.pure false := by
    by_contra hne
    have hdom :=
      (mixedConverse_midpoint_strictlyDominates_zero (q := σ 0) hne).toWeaklyStrictlyDominates
        (G := mixedConverseGame.mixedExtension.subsidize mixedConverseTransfer)
        ⟨mixedConverseMixedTarget⟩
    exact (hσ 0 (mixedConverseMidpointToFalse (σ 0)) hdom).elim
  have h1 : σ 1 = PMF.pure false := by
    by_contra hne
    have hdom :=
      (mixedConverse_midpoint_strictlyDominates_one (q := σ 1) hne).toWeaklyStrictlyDominates
        (G := mixedConverseGame.mixedExtension.subsidize mixedConverseTransfer)
        ⟨mixedConverseMixedTarget⟩
    exact (hσ 1 (mixedConverseMidpointToFalse (σ 1)) hdom).elim
  exact Set.mem_singleton_iff.mpr (by
    funext i
    fin_cases i <;> simp [mixedConverseMixedTarget, h0, h1])

theorem mixedConverseTransfer_isImplementation :
    mixedConverseGame.mixedExtension.IsImplementation mixedConverseTransfer
      ({mixedConverseMixedTarget} : Set (Profile mixedConverseGame.mixedExtension)) := by
  refine ⟨mixedConverseTransfer_nonneg, ?_, ?_⟩
  · exact ⟨mixedConverseMixedTarget, mixedConverse_target_mem_undominated⟩
  · exact mixedConverse_undominated_subset_singleton

theorem mixedConverseTransfer_isZeroKImplementation :
    mixedConverseGame.mixedExtension.IsKImplementation mixedConverseTransfer
      ({mixedConverseMixedTarget} : Set (Profile mixedConverseGame.mixedExtension)) 0 := by
  refine ⟨mixedConverseTransfer_isImplementation, ?_⟩
  intro σ hσ
  have hmem := mixedConverse_undominated_subset_singleton σ hσ
  have hσeq : σ = mixedConverseMixedTarget := Set.mem_singleton_iff.mp hmem
  subst σ
  simp

theorem mixedConverseMixedTarget_not_nash :
    ¬ mixedConverseGame.mixedExtension.IsNash mixedConverseMixedTarget := by
  intro hN
  have hdev := hN 0 (PMF.pure true)
  have htarget :
      mixedConverseGame.mixedExtension.eu mixedConverseMixedTarget 0 = 0 := by
    rw [mixedConverse_eu_zero]
    simp [mixedConverseMixedTarget]
  have hdeviation :
      mixedConverseGame.mixedExtension.eu
          (Function.update mixedConverseMixedTarget 0 (PMF.pure true)) 0 = 1 := by
    rw [mixedConverse_eu_zero]
    simp [mixedConverseMixedTarget, Function.update]
  linarith

/-- The unrestricted counterexample lies exactly outside the semantic
admissibility class used by the corrected mixed-extension converse. -/
theorem mixedConverseTransfer_not_selectionAdmissible :
    ¬ mixedConverseGame.MixedSelectionAdmissibleAt
      mixedConverseTransfer mixedConverseMixedTarget := by
  haveI : ∀ i : Fin 2, Nonempty (mixedConverseGame.Strategy i) := fun _ => by
    change Nonempty Bool
    infer_instance
  haveI : ∀ i : Fin 2, Finite (mixedConverseGame.Strategy i) := fun _ => by
    change Finite Bool
    infer_instance
  intro hadm
  exact mixedConverseMixedTarget_not_nash
    (mixedConverseGame.isNash_of_exists_zero_mixedAdmissibleKImplementation
      ⟨mixedConverseTransfer, hadm, mixedConverseTransfer_isZeroKImplementation⟩)

/-- The unrestricted converse of the paper's Theorem 3 is false: this mixed
profile is 0-implementable in the mixed extension, but it is not Nash. -/
theorem mixedConverse_zeroKImplementation_and_not_nash :
    mixedConverseGame.mixedExtension.IsKImplementation mixedConverseTransfer
        ({mixedConverseMixedTarget} : Set (Profile mixedConverseGame.mixedExtension)) 0 ∧
      ¬ mixedConverseGame.mixedExtension.IsNash mixedConverseMixedTarget :=
  ⟨mixedConverseTransfer_isZeroKImplementation, mixedConverseMixedTarget_not_nash⟩

theorem mixedConverse_implPrice_singleton_eq_zero :
    mixedConverseGame.mixedExtension.implPrice
      ({mixedConverseMixedTarget} : Set (Profile mixedConverseGame.mixedExtension)) = 0 := by
  have hle :=
    implPrice_le_of_isKImplementation
      (G := mixedConverseGame.mixedExtension)
      (V := mixedConverseTransfer)
      mixedConverseTransfer_isZeroKImplementation
  have hne :
      (mixedConverseGame.mixedExtension.implementationCosts
        ({mixedConverseMixedTarget} : Set (Profile mixedConverseGame.mixedExtension))).Nonempty :=
    ⟨0, mixedConverseTransfer, mixedConverseTransfer_isZeroKImplementation⟩
  have hge :=
    implPrice_nonneg_of_implementationCosts_nonempty
      (G := mixedConverseGame.mixedExtension)
      (O := ({mixedConverseMixedTarget} : Set (Profile mixedConverseGame.mixedExtension))) hne
  linarith

/-- The one-player hypothesis cannot be silently allowed in the zero-cost
singleton corollary: the target is Nash, but no nonnegative zero-cost transfer
can make it the only undominated profile. -/
theorem onePlayerTie_not_zero_singletonKImplementable :
    ¬ ∃ V : Profile onePlayerTieGame → Payoff (Fin 1),
      onePlayerTieGame.IsKImplementation V
        ({onePlayerProfile false} : Set (Profile onePlayerTieGame)) 0 := by
  rintro ⟨V, hV⟩
  have htarget_undom :
      onePlayerProfile false ∈ (onePlayerTieGame.subsidize V).undominatedProfiles :=
    singleton_target_undominated_of_isImplementation (G := onePlayerTieGame)
      hV.implementation
  have htarget_cost := hV.cost_bound (onePlayerProfile false) htarget_undom
  have htarget_nonneg := hV.nonneg (onePlayerProfile false) 0
  have htarget_pay_zero : V (onePlayerProfile false) 0 = 0 := by
    have hle : V (onePlayerProfile false) 0 ≤ 0 := by
      simpa using htarget_cost
    exact le_antisymm hle htarget_nonneg
  have htrue_undom :
      (onePlayerTieGame.subsidize V).IsUndominated 0 true := by
    intro t hdom
    cases t
    · have hweak := hdom.toWeaklyDominates (onePlayerProfile true)
      have hpay_le : V (onePlayerProfile true) 0 ≤ 0 := by
        have hweak' :
            V (onePlayerProfile true) 0 ≤ V (onePlayerProfile false) 0 := by
          simpa using hweak
        linarith
      have htrue_pay_zero : V (onePlayerProfile true) 0 = 0 :=
        le_antisymm hpay_le (hV.nonneg (onePlayerProfile true) 0)
      obtain ⟨σ, hstrict⟩ := hdom.strict_witness
      have hstrict' :
          V (onePlayerProfile true) 0 < V (onePlayerProfile false) 0 := by
        simpa using hstrict
      linarith
    · exact WeaklyStrictlyDominates.irrefl
        (G := onePlayerTieGame.subsidize V) (who := 0) true hdom
  have htrue_profile_undom :
      onePlayerProfile true ∈ (onePlayerTieGame.subsidize V).undominatedProfiles := by
    intro i
    fin_cases i
    exact htrue_undom
  have hmem := hV.implementation.subset (onePlayerProfile true) htrue_profile_undom
  have hprofile_eq :
      onePlayerProfile true = onePlayerProfile false := Set.mem_singleton_iff.mp hmem
  have hcoord : true = false := congrFun hprofile_eq 0
  cases hcoord

/-- Equivalently, zero is not a feasible singleton implementation budget in the
one-player tie game, even though it is the implementation price. -/
theorem onePlayerTie_zero_not_mem_implementationCosts :
    (0 : ℝ) ∉ onePlayerTieGame.implementationCosts
      ({onePlayerProfile false} : Set (Profile onePlayerTieGame)) := by
  intro h
  exact onePlayerTie_not_zero_singletonKImplementable h

end ImplementationExamples

end KernelGame

end GameTheory
