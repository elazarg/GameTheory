/-
# Public-action repeated play

This is the stable deterministic-path layer for repeated games. A repeated
strategy observes the finite history of stage profiles chosen so far and
chooses the next stage strategy. If the stage form is stochastic, the public
history still records chosen strategy profiles while payoffs use the stage
form's expected utility; realized-signal monitoring is a separate finite-prefix
construction.

No probability law over an infinite path is introduced. Infinite-horizon
payoff aggregations build on the generated `ℕ`-indexed path in `Discounted`.
-/

import GameTheory.Core.Utility
import Mathlib.Topology.Instances.Nat

noncomputable section

namespace GameTheory

open Probability

universe uι us uo

variable {ι : Type uι}

namespace UtilityGame

/-- Public stage-profile history, in chronological order. Its length is the
current period. -/
abbrev ProfileHistory (G : UtilityGame ι) : Type _ :=
  List (Profile G.form.sig)

/-- A repeated strategy chooses a stage strategy after every finite public
profile history. -/
abbrev RepeatedStrategy (G : UtilityGame ι) (i : ι) : Type _ :=
  G.ProfileHistory → G.form.sig.Strategy i

/-- Signature of the repeated strategic form. Its outcome is the repeated
strategy profile itself; a utility may evaluate the generated path. -/
abbrev repeatedSignature (G : UtilityGame ι) : GameSignature ι where
  Strategy := G.RepeatedStrategy
  Outcome := ∀ i, G.RepeatedStrategy i

/-- A profile of history-dependent repeated strategies. -/
abbrev RepeatedProfile (G : UtilityGame ι) : Type _ :=
  Profile G.repeatedSignature

/-- The utility-free repeated form. Play is deterministic; the discounted or
finite-horizon evaluator remains separate utility data. -/
@[reducible]
def repeatedForm (G : UtilityGame ι) : GameForm ι where
  sig := G.repeatedSignature
  play profile := FinDist.pure profile

/-- Stationary repetition of one stage profile. -/
def stationaryRepeatedProfile (G : UtilityGame ι)
    (profile : Profile G.form.sig) : G.RepeatedProfile :=
  fun i _ => profile i

/-- Periodic repetition of a nonempty finite cycle of stage profiles. -/
def periodicRepeatedProfile (G : UtilityGame ι)
    {n : ℕ} [NeZero n] (cycle : Fin n → Profile G.form.sig) :
    G.RepeatedProfile :=
  fun i history => cycle (Fin.ofNat n history.length) i

/-- The stage-profile path generated recursively by a repeated profile. -/
def repeatedPlay (G : UtilityGame ι)
    (profile : G.RepeatedProfile) : (t : ℕ) → Profile G.form.sig
  | t => fun i => profile i
      (List.ofFn fun k : Fin t => repeatedPlay G profile k)
termination_by t => t
decreasing_by exact k.isLt

@[simp]
theorem repeatedPlay_stationaryRepeatedProfile (G : UtilityGame ι)
    (profile : Profile G.form.sig) (t : ℕ) :
    G.repeatedPlay (G.stationaryRepeatedProfile profile) t = profile := by
  funext i
  simp [repeatedPlay, stationaryRepeatedProfile]

@[simp]
theorem repeatedPlay_periodicRepeatedProfile (G : UtilityGame ι)
    {n : ℕ} [NeZero n] (cycle : Fin n → Profile G.form.sig) (t : ℕ) :
    G.repeatedPlay (G.periodicRepeatedProfile cycle) t =
      cycle (Fin.ofNat n t) := by
  funext i
  rw [repeatedPlay]
  simp only [periodicRepeatedProfile, List.length_ofFn]

/-- A unilateral deviation from stationary play changes only that player's
stage coordinate in every period. -/
theorem repeatedPlay_update_stationaryRepeatedProfile
    (G : UtilityGame ι) [DecidableEq ι]
    (profile : Profile G.form.sig) (who : ι)
    (deviation : G.RepeatedStrategy who) (t : ℕ) :
    G.repeatedPlay
        (Profile.update (G.stationaryRepeatedProfile profile) who deviation) t =
      Profile.update profile who
        (deviation (List.ofFn fun k : Fin t => G.repeatedPlay
          (Profile.update (G.stationaryRepeatedProfile profile) who deviation) k)) := by
  funext i
  by_cases hi : i = who
  · subst hi
    rw [repeatedPlay]
    simp only [Profile.update_same]
  · rw [repeatedPlay]
    simp only [Profile.update_of_ne _ _ hi, stationaryRepeatedProfile]

/-- Expected payoff of one chosen stage profile. -/
def stagePayoff (G : UtilityGame ι) (profile : Profile G.form.sig)
    (who : ι) : ℝ :=
  expectedUtility G.utility who (G.form.play profile)

/-- Average expected payoff over the first `T` generated stages. -/
def finiteAveragePayoff (G : UtilityGame ι) (T : ℕ)
    (profile : G.RepeatedProfile) (who : ι) : ℝ :=
  (T : ℝ)⁻¹ *
    ∑ t ∈ Finset.range T, G.stagePayoff (G.repeatedPlay profile t) who

@[simp]
theorem finiteAveragePayoff_one (G : UtilityGame ι)
    (profile : G.RepeatedProfile) (who : ι) :
    G.finiteAveragePayoff 1 profile who =
      G.stagePayoff (G.repeatedPlay profile 0) who := by
  simp [finiteAveragePayoff]

/-- A nonempty finite average of stationary play is its stage payoff. -/
theorem finiteAveragePayoff_stationaryRepeatedProfile
    (G : UtilityGame ι) {T : ℕ} (hT : T ≠ 0)
    (profile : Profile G.form.sig) (who : ι) :
    G.finiteAveragePayoff T (G.stationaryRepeatedProfile profile) who =
      G.stagePayoff profile who := by
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT
  simp [finiteAveragePayoff, Finset.sum_const, ← mul_assoc,
    inv_mul_cancel₀ hT']

/-- A stagewise upper bound bounds every nonempty finite average. -/
theorem finiteAveragePayoff_le_of_forall_stagePayoff_le
    (G : UtilityGame ι) {profile : G.RepeatedProfile} {bound : ℝ}
    {who : ι}
    (hle : ∀ t, G.stagePayoff (G.repeatedPlay profile t) who ≤ bound)
    {T : ℕ} (hT : T ≠ 0) :
    G.finiteAveragePayoff T profile who ≤ bound := by
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT
  calc
    G.finiteAveragePayoff T profile who ≤
        (T : ℝ)⁻¹ * ∑ _t ∈ Finset.range T, bound := by
      unfold finiteAveragePayoff
      gcongr with t _
      exact hle t
    _ = bound := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hT', one_mul]

/-- A repeated profile has long-run average payoff `value` when its finite
averages converge coordinatewise. -/
def HasLongRunAveragePayoff (G : UtilityGame ι)
    (profile : G.RepeatedProfile) (value : ι → ℝ) : Prop :=
  ∀ who, Filter.Tendsto (fun horizon =>
    G.finiteAveragePayoff horizon profile who)
      Filter.atTop (nhds (value who))

/-- Stationary repetition converges to its stage payoff. -/
theorem hasLongRunAveragePayoff_stationaryRepeatedProfile
    (G : UtilityGame ι) (profile : Profile G.form.sig) :
    G.HasLongRunAveragePayoff (G.stationaryRepeatedProfile profile)
      (fun who => G.stagePayoff profile who) := by
  intro who
  have heventually :
      (fun _ : ℕ => G.stagePayoff profile who) =ᶠ[Filter.atTop]
        fun horizon => G.finiteAveragePayoff horizon
          (G.stationaryRepeatedProfile profile) who := by
    filter_upwards [Filter.eventually_ge_atTop 1] with horizon hhorizon
    exact (G.finiteAveragePayoff_stationaryRepeatedProfile
      (by omega) profile who).symm
  exact Filter.Tendsto.congr' heventually tendsto_const_nhds

end UtilityGame

end GameTheory
