/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Cycles.CycleIsolatedCoordinate
import Math.MaxAffineStoppingValue

/-!
# The isolated coordinate is an instance of the max-affine anchored value

`QuittingCycleIsolatedCoordinate.lean` shows that at an isolated coordinate
`who` -- every opponent silent, the `P_who = 1` regime -- the cyclic
companion composite's phase map collapses to `w ↦ max {r_who({who}), w}`
(`quittingRootCompanionMap_of_isolated`), and that iterating it from the
solo-quit anchor `Λ_who = max {0, r_who({who})}` is constant
(`tendsto_iterate_soloQuitAnchor_of_isolated`).

This is exactly the `P = 1`, `T = 0` regime of
`Math.MaxAffineStopping.System`: the stop payoff `A := r_who({who})`, no
stage reward, full survival.  This file makes that identification precise:
the isolated companion composite over any window is the iterate of the
abstract operator `Φ` for this system (`quittingCompanionComposite_eq_iterate_Φ_of_isolated`),
the solo-quit anchor is the abstract anchored value at boundary payoff `0`
(`quittingPositiveSingletonDebtCap_eq_anchoredValue`), and the constancy of
the anchored orbit is a direct corollary of the regime dichotomy's fixed-set
characterization, not a bespoke argument.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.MaxAffineStopping

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The isolated max-affine system at `who`.**  Stop payoff `r_who({who})`,
no stage reward, full survival: exactly the coefficients
`quittingRootCompanionMap_of_isolated` reads off an isolated root. -/
def quittingIsolatedSystem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) : System where
  A := reward (quittingSingletonTerminal who) who
  T := 0
  P := 1
  P_nonneg := by norm_num
  P_le_one := le_refl 1

omit [Fintype ι] [DecidableEq ι] in
/-- The isolated system's operator agrees with `max {A, ·}`, the same
formula `quittingRootCompanionMap_of_isolated` proves for an isolated root's
companion map. -/
theorem quittingIsolatedSystem_Φ_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) (w : ℝ) :
    (quittingIsolatedSystem reward who).Φ w =
      max (reward (quittingSingletonTerminal who) who) w := by
  change max (reward (quittingSingletonTerminal who) who) ((0 : ℝ) + 1 * w) = _
  ring_nf

/-- **The companion map at an isolated root is the abstract operator `Φ`.** -/
theorem quittingRootCompanionMap_eq_Φ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {root : ι → PMF Bool} {who : ι} (hiso : IsQuittingIsolatedRoot root who) :
    quittingRootCompanionMap reward root who = (quittingIsolatedSystem reward who).Φ := by
  funext w
  rw [quittingRootCompanionMap_of_isolated reward hiso, quittingIsolatedSystem_Φ_apply]

/-- **The composite over an isolated window is the iterate of `Φ`.**  Every
phase's companion map is the *same* abstract operator `Φ` (the stop payoff
`r_who({who})` does not depend on the phase), so composing `fuel` of them is
literally iterating `Φ` `fuel` times. -/
theorem quittingCompanionComposite_eq_iterate_Φ_of_isolated
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (start fuel : ℕ)
    (hiso : IsQuittingIsolatedWindow roots who (start + fuel)) :
    quittingCompanionComposite reward roots who start fuel =
      (quittingIsolatedSystem reward who).Φ^[fuel] := by
  induction fuel generalizing start with
  | zero => funext w; rfl
  | succ fuel ih =>
      funext w
      have hisoStart : IsQuittingIsolatedRoot (roots start) who := hiso start (by omega)
      have hisoRest : IsQuittingIsolatedWindow roots who (start + 1 + fuel) :=
        fun t ht ↦ hiso t (by omega)
      rw [quittingCompanionComposite_succ, ih (start + 1) hisoRest,
        quittingRootCompanionMap_eq_Φ reward hisoStart, Function.iterate_succ_apply']

omit [Fintype ι] [DecidableEq ι] in
/-- **The solo-quit anchor is the abstract anchored value.**  `Λ_who = max {0,
r_who({who})}` is `quittingIsolatedSystem`'s anchored value at boundary
payoff `0`, by the `P = 1`, `T = 0` regime dichotomy. -/
theorem quittingPositiveSingletonDebtCap_eq_anchoredValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingPositiveSingletonDebtCap reward who =
      (quittingIsolatedSystem reward who).anchoredValue 0 := by
  rw [(quittingIsolatedSystem reward who).anchoredValue_eq_max_of_P_eq_one_of_T_eq_zero rfl rfl 0,
    quittingSoloQuitAnchor_eq, max_comm]
  rfl

/-- **The bridge, reassembled.**  The isolated orbit's constancy
(`tendsto_iterate_soloQuitAnchor_of_isolated`) is the `P = 1`, `T = 0`
regime's anchored value being a fixed point of `Φ`, transported through
`quittingCompanionComposite_eq_iterate_Φ_of_isolated`: the game-local
iteration literally *is* the abstract operator's anchored iteration, not
merely an object with the same numeric limit. -/
theorem tendsto_iterate_soloQuitAnchor_of_isolated_via_anchoredValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι) (period : ℕ)
    (hiso : IsQuittingIsolatedWindow roots who period) :
    Filter.Tendsto
      (fun N : ℕ =>
        (quittingCompanionComposite reward roots who 0 period)^[N]
          (quittingPositiveSingletonDebtCap reward who))
      Filter.atTop (nhds (quittingPositiveSingletonDebtCap reward who)) := by
  set sys := quittingIsolatedSystem reward who
  have hcomposite : quittingCompanionComposite reward roots who 0 period = sys.Φ^[period] :=
    quittingCompanionComposite_eq_iterate_Φ_of_isolated reward roots who 0 period
      (by simpa using hiso)
  have hanchor : quittingPositiveSingletonDebtCap reward who = sys.anchoredValue 0 :=
    quittingPositiveSingletonDebtCap_eq_anchoredValue reward who
  have hfix : Function.IsFixedPt sys.Φ (sys.anchoredValue 0) :=
    (sys.isFixedPt_iff_of_P_eq_one_of_T_eq_zero rfl rfl (sys.anchoredValue 0)).mpr
      (by rw [← hanchor, quittingSoloQuitAnchor_eq]; exact le_max_right _ _)
  have hperiodFix : Function.IsFixedPt (sys.Φ^[period]) (sys.anchoredValue 0) :=
    Function.iterate_fixed hfix period
  have hconst : ∀ N : ℕ, (sys.Φ^[period])^[N] (sys.anchoredValue 0) = sys.anchoredValue 0 :=
    fun N ↦ Function.iterate_fixed hperiodFix N
  rw [hcomposite, hanchor]
  simp only [hconst]
  exact tendsto_const_nhds

end GameTheory
