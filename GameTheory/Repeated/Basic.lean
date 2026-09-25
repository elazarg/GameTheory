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

open GameTheory.Math.Probability

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
  play profile := PMF.pure profile

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
    (who : ι)
    (hstage : UtilityIntegrable G.utility who (G.form.play profile)) : ℝ :=
  expectedUtility G.utility who (G.form.play profile) hstage

/-- Average expected payoff over the first `T` generated stages. -/
def finiteAveragePayoff (G : UtilityGame ι) (T : ℕ)
    (profile : G.RepeatedProfile) (who : ι)
    (hstage : ∀ t < T,
      UtilityIntegrable G.utility who (G.form.play (G.repeatedPlay profile t))) : ℝ :=
  (T : ℝ)⁻¹ *
    ∑ t : Fin T,
      G.stagePayoff (G.repeatedPlay profile t) who (hstage t t.isLt)

@[simp]
theorem finiteAveragePayoff_one (G : UtilityGame ι)
    (profile : G.RepeatedProfile) (who : ι)
    (hstage : ∀ t < 1,
      UtilityIntegrable G.utility who (G.form.play (G.repeatedPlay profile t))) :
    G.finiteAveragePayoff 1 profile who hstage =
      G.stagePayoff (G.repeatedPlay profile 0) who (hstage 0 (by omega)) := by
  simp [finiteAveragePayoff]

/-- A nonempty finite average of stationary play is its stage payoff. -/
theorem finiteAveragePayoff_stationaryRepeatedProfile
    (G : UtilityGame ι) {T : ℕ} (hT : T ≠ 0)
    (profile : Profile G.form.sig) (who : ι)
    (hstage : UtilityIntegrable G.utility who (G.form.play profile)) :
    G.finiteAveragePayoff T (G.stationaryRepeatedProfile profile) who
      (fun t _ => by simpa using hstage) =
      G.stagePayoff profile who hstage := by
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT
  simp only [finiteAveragePayoff]
  have hsum :
      (∑ t : Fin T,
        G.stagePayoff
          (G.repeatedPlay (G.stationaryRepeatedProfile profile) t) who
          (by simpa using hstage)) =
        (T : ℝ) * G.stagePayoff profile who hstage := by
    calc
      (∑ t : Fin T,
        G.stagePayoff
          (G.repeatedPlay (G.stationaryRepeatedProfile profile) t) who
          (by simpa using hstage)) =
          ∑ _t : Fin T, G.stagePayoff profile who hstage := by
        apply Finset.sum_congr rfl
        intro t _
        simp only [G.repeatedPlay_stationaryRepeatedProfile]
      _ = (T : ℝ) * G.stagePayoff profile who hstage := by
        rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  rw [hsum, ← mul_assoc, inv_mul_cancel₀ hT', one_mul]

/-- A stagewise upper bound bounds every nonempty finite average. -/
theorem finiteAveragePayoff_le_of_forall_stagePayoff_le
    (G : UtilityGame ι) {profile : G.RepeatedProfile} {bound : ℝ}
    {who : ι} {T : ℕ}
    (hstage : ∀ t < T,
      UtilityIntegrable G.utility who (G.form.play (G.repeatedPlay profile t)))
    (hle : ∀ t : Fin T,
      G.stagePayoff (G.repeatedPlay profile t) who (hstage t t.isLt) ≤ bound)
    (hT : T ≠ 0) :
    G.finiteAveragePayoff T profile who hstage ≤ bound := by
  have hT' : (T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hT
  calc
    G.finiteAveragePayoff T profile who hstage ≤
        (T : ℝ)⁻¹ * ∑ _t : Fin T, bound := by
      unfold finiteAveragePayoff
      gcongr with t _
      exact hle t
    _ = bound := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hT', one_mul]

/-- A repeated profile has long-run average payoff `value` when its finite
averages converge coordinatewise. -/
def HasLongRunAveragePayoff (G : UtilityGame ι)
    (profile : G.RepeatedProfile)
    (hstage : ∀ t who,
      UtilityIntegrable G.utility who (G.form.play (G.repeatedPlay profile t)))
    (value : ι → ℝ) : Prop :=
  ∀ who, Filter.Tendsto (fun horizon =>
    G.finiteAveragePayoff horizon profile who
      (fun t _ => hstage t who))
      Filter.atTop (nhds (value who))

/-- Stationary repetition converges to its stage payoff. -/
theorem hasLongRunAveragePayoff_stationaryRepeatedProfile
    (G : UtilityGame ι) (profile : Profile G.form.sig)
    (hstage : ∀ who,
      UtilityIntegrable G.utility who (G.form.play profile)) :
    G.HasLongRunAveragePayoff (G.stationaryRepeatedProfile profile)
      (fun t who => by simpa using hstage who)
      (fun who => G.stagePayoff profile who (hstage who)) := by
  intro who
  have heventually :
      (fun _ : ℕ => G.stagePayoff profile who (hstage who)) =ᶠ[Filter.atTop]
        fun horizon => G.finiteAveragePayoff horizon
          (G.stationaryRepeatedProfile profile) who
          (fun t _ => by simpa using hstage who) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with horizon hhorizon
    exact (G.finiteAveragePayoff_stationaryRepeatedProfile
      (by omega) profile who (hstage who)).symm
  exact Filter.Tendsto.congr' heventually tendsto_const_nhds

end UtilityGame

end GameTheory
