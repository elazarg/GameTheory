/-
# Correlated pseudo-equilibria and the coupling of sizes

On the ensemble form, a correlation device must be one law over strategy
profiles used at every size, so a device given size by size has to be coupled
across sizes, and a correlated deviation reads the recommended strategy at all
sizes at once. The coupling matters, already with two sizes. Each player's
strategy is an action at size `0` and one at size `1`, and play at size `0` is
chicken. The device recommends swerve–swerve, swerve–dare and dare–swerve with
probability one third each, at both sizes. Repeating the draw gives a
correlated equilibrium. Recommending each player, at size `1`, the other's
size-`0` action gives the same device at each size, yet the size-`1`
recommendation reveals the opponent's size-`0` action and daring against a
swerver becomes profitable.

`ParameterizedGame.IsPseudoCorrelatedEq` avoids the choice by drawing each
size's recommendation inside play at that size; the chicken device is a
pseudo-correlated equilibrium of the fixed game.
-/
import GameTheory.Analysis.PseudoCorrelated
import GameTheory.Math.Probability.Uniform

noncomputable section

namespace GameTheory.Tests.PseudoCorrelated

open GameTheory GameTheory.Math.Probability

/-- Chicken, with `true` for swerve: swerving against a swerver pays six,
swerving against a darer two, daring against a swerver seven, and a crash
nothing. -/
def chickenPayoff (mine theirs : Bool) : ℝ :=
  if mine then (if theirs then 6 else 2) else (if theirs then 7 else 0)

/-- Each player chooses an action at size `0` and one at size `1`; the outcome
is the pair of size-`0` actions. -/
abbrev twoSizes : GameForm (Fin 2) :=
  GameForm.deterministic { Strategy := fun _ => Bool × Bool, Outcome := Bool × Bool }
    fun profile => ((profile 0).1, (profile 1).1)

def chickenUtility (outcome : Bool × Bool) (who : Fin 2) : ℝ :=
  if who = 0 then chickenPayoff outcome.1 outcome.2 else chickenPayoff outcome.2 outcome.1

/-- The chicken device, as a joint recommendation of size-`0` actions. -/
def draws : Fin 3 → Bool × Bool := ![(true, true), (true, false), (false, true)]

/-- Coupling by repetition: each player gets its draw at both sizes. -/
def sameDraw (i : Fin 3) : Profile twoSizes.sig :=
  fun who => if who = 0 then ((draws i).1, (draws i).1) else ((draws i).2, (draws i).2)

/-- Coupling by exchange: at size `1` each player gets the other's size-`0`
recommendation. -/
def swappedDraw (i : Fin 3) : Profile twoSizes.sig :=
  fun who => if who = 0 then ((draws i).1, (draws i).2) else ((draws i).2, (draws i).1)

/-- The uniform draw. -/
abbrev device : PMF (Fin 3) := PMF.uniformOfFintype (Fin 3)

/-- At each size, both couplings recommend the same joint action. -/
theorem sameDraw_swappedDraw_marginals (i : Fin 3) :
    ((sameDraw i 0).1, (sameDraw i 1).1) = draws i ∧
      ((swappedDraw i 0).1, (swappedDraw i 1).1) = draws i ∧
      ((sameDraw i 0).2, (sameDraw i 1).2) = draws i ∧
      ((swappedDraw i 0).2, (swappedDraw i 1).2) = ((draws i).2, (draws i).1) := by
  simp [sameDraw, swappedDraw]

/-- Exchanging the pair keeps the device's law at size `1`: swerve–dare and
dare–swerve trade places. -/
theorem swapped_size_one_law :
    device.map (fun i => ((draws i).2, (draws i).1)) = device.map draws := by
  ext x
  rcases x with ⟨_ | _, _ | _⟩ <;>
    simp [PMF.map_apply, tsum_fintype, Fin.sum_univ_three, draws]

private theorem utility_integrable (who : Fin 2) (law : PMF (Bool × Bool)) :
    UtilityIntegrable chickenUtility who law :=
  payoffIntegrable_of_finite law _

private theorem expectedUtility_bind_pure (law : PMF (Fin 3))
    (outcome : Fin 3 → Bool × Bool) (who : Fin 2) :
    expectedUtility chickenUtility who (law.bind fun i => PMF.pure (outcome i)) =
      expect law fun i => chickenUtility (outcome i) who := by
  rw [expectedUtility, show law.bind (fun i => PMF.pure (outcome i)) = law.map outcome from
    PMF.bind_pure_comp outcome law, expect_map]
  rfl

/-- **Repeating the draw is a correlated equilibrium.** -/
theorem sameDraw_isCorrelatedEq :
    IsCorrelatedEq twoSizes (euPreference chickenUtility) (device.map sameDraw) := by
  rw [isCorrelatedEq_iff]
  intro who respond
  rw [euPreference_iff _ _ _ _ (utility_integrable _ _) (utility_integrable _ _)]
  simp only [GameForm.outcomeLaw, PMF.bind_map, Function.comp_def]
  rw [expectedUtility_bind_pure, expectedUtility_bind_pure, expect_uniformFin,
    expect_uniformFin]
  simp only [Fin.sum_univ_three]
  fin_cases who
  · cases h1 : (respond (true, true)).1 <;> cases h2 : (respond (false, false)).1 <;>
      simp [sameDraw, draws, chickenUtility, chickenPayoff, Profile.update, h1, h2] <;> norm_num
  · cases h1 : (respond (true, true)).1 <;> cases h2 : (respond (false, false)).1 <;>
      simp [sameDraw, draws, chickenUtility, chickenPayoff, Profile.update, h1, h2] <;> norm_num

/-- **Exchanging the draws is not a correlated equilibrium**: player `0` reads
the opponent's size-`0` action from its own size-`1` recommendation and dares
against a swerver. -/
theorem swappedDraw_not_isCorrelatedEq :
    ¬ IsCorrelatedEq twoSizes (euPreference chickenUtility) (device.map swappedDraw) := by
  rw [isCorrelatedEq_iff]
  intro h
  have hdev := h 0 fun recommendation => (!recommendation.2, recommendation.2)
  rw [euPreference_iff _ _ _ _ (utility_integrable _ _) (utility_integrable _ _)] at hdev
  simp only [GameForm.outcomeLaw, PMF.bind_map, Function.comp_def] at hdev
  rw [expectedUtility_bind_pure, expectedUtility_bind_pure, expect_uniformFin,
    expect_uniformFin] at hdev
  simp [Fin.sum_univ_three, swappedDraw, draws, chickenUtility, chickenPayoff,
    Profile.update] at hdev
  norm_num at hdev


/-- Chicken at a single size. -/
abbrev chickenForm : GameForm (Fin 2) :=
  GameForm.deterministic { Strategy := fun _ => Bool, Outcome := Bool × Bool }
    fun profile => (profile 0, profile 1)

/-- The chicken device as a law over recommendation profiles. -/
def chickenDevice : PMF (Profile chickenForm.sig) :=
  device.map fun i who => if who = 0 then (draws i).1 else (draws i).2

theorem chickenDevice_isCorrelatedEq :
    IsCorrelatedEq chickenForm (euPreference chickenUtility) chickenDevice := by
  rw [isCorrelatedEq_iff]
  intro who respond
  rw [euPreference_iff _ _ _ _ (utility_integrable _ _) (utility_integrable _ _)]
  simp only [chickenDevice, GameForm.outcomeLaw, PMF.bind_map, Function.comp_def]
  rw [expectedUtility_bind_pure, expectedUtility_bind_pure, expect_uniformFin,
    expect_uniformFin]
  simp only [Fin.sum_univ_three]
  fin_cases who
  · cases h1 : respond true <;> cases h2 : respond false <;>
      simp [draws, chickenUtility, chickenPayoff, Profile.update, h1, h2] <;> norm_num
  · cases h1 : respond true <;> cases h2 : respond false <;>
      simp [draws, chickenUtility, chickenPayoff, Profile.update, h1, h2] <;> norm_num

/-- **The functionality model gives the per-size answer.** The chicken device,
drawn afresh at every size inside play, is a pseudo-correlated equilibrium; no
coupling across sizes is chosen. -/
theorem chicken_isPseudoCorrelatedEq :
    (ParameterizedGame.constant chickenForm chickenUtility).IsPseudoCorrelatedEq
      (fun _ => chickenDevice) :=
  (ParameterizedGame.isPseudoCorrelatedEq_constant_iff chickenForm chickenUtility
    (fun who => ⟨7, fun outcome => by
      simp only [chickenUtility, chickenPayoff]
      split_ifs <;> norm_num⟩) chickenDevice).mpr chickenDevice_isCorrelatedEq

end GameTheory.Tests.PseudoCorrelated
