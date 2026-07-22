/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Stochastic.FinkLimit

/-!
# The corrected Fink endpoint

This file records the exact endpoint of the vanishing-discount program.  The
canonical fast Fink family already supplies discounted fixed points, a value
limit, and the quantitative value approximation needed by the verifier.  The
only additional mathematical input required by the strongest corrected-target
verifier is a correction sequence whose indexed family is corrected-calendar
selectable.

`HasFastFinkCorrectedCalendarSelection` states only that missing selection
principle.  `exists_uniformEquilibriumPayoff_of_fastFinkCorrectedCalendarSelection`
then derives the full existential conclusion, including the preliminary
finite payoff bound, from it.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math.Probability

/-- The explicit error rate supplied by
`exists_fast_approachOne_finkFixedPoint_family`. -/
def fastFinkValueError (n : ℕ) : ℝ := (((n + 1 : ℕ) : ℝ))⁻¹

/-- The remaining selection principle at the corrected Fink endpoint.

One must jointly choose a fast convergent family of discounted Fink fixed
points and a time-dependent correction whose corrected target is selectable
by an annealing calendar.  The existential quantifiers are essential: an
arbitrary convergent choice of discounted equilibria need not have the needed
first-order regularity.  The family without the final correction/selectability
clause is already supplied by
`exists_fast_approachOne_finkFixedPoint_family`.
-/
def HasFastFinkCorrectedCalendarSelection (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] : Prop :=
  ∀ (U : ℝ) (_hU : 0 ≤ U)
      (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U),
    ∃ (β : ℕ → ℝ) (z : ℕ → G.finkDomain U)
        (zlim : G.finkDomain U) (hβ0 : ∀ n, 0 ≤ β n)
        (hβ1 : ∀ n, β n < 1) (R : ℕ → G.State → Payoff ι),
      (∀ n, G.finkMap (β n) U (hβ0 n) (hβ1 n).le hpay (z n) = z n) ∧
      Tendsto β atTop (nhds 1) ∧
      Tendsto z atTop (nhds zlim) ∧
      (∀ n s who,
        |G.finkValue (z n) s who - G.finkValue zlim s who| ≤
          fastFinkValueError n) ∧
      G.IsIndexedFinkCorrectedCalendarSelectable β U z
        (G.finkValue zlim) R fastFinkValueError

/-- At a fixed payoff bound, the corrected selection principle closes the
uniform-equilibrium-payoff theorem.  This is the direct formal composition of
the canonical fast-family theorem and the corrected-target endpoint verifier.
-/
theorem exists_uniformEquilibriumPayoff_of_fastFinkCorrectedCalendarSelection_aux
    (G : StochasticGame ι)
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, Nonempty (G.Act i)]
    (s₀ : G.State) (U : ℝ) (hU : 0 ≤ U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (hselection : G.HasFastFinkCorrectedCalendarSelection) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  obtain ⟨β, z, zlim, hβ0, hβ1, R, hfix, _hβlim, _hz,
      hclose, hselect⟩ := hselection U hU hpay
  refine ⟨G.finkValue zlim s₀, ?_⟩
  apply G.isUniformEquilibriumPayoff_of_indexedFinkFixedPoints_correctedTarget
    s₀ β U hβ0 hβ1 hpay z (G.finkValue zlim)
      (fun s who => G.abs_finkValue_le zlim s who)
      R fastFinkValueError hfix hclose hselect

/-- A corrected-calendar selection for fast Fink families implies the full
uniform-equilibrium-payoff existence statement.  Finiteness supplies a common
absolute stage-payoff bound, so the sole substantive hypothesis is
`HasFastFinkCorrectedCalendarSelection`.
-/
theorem exists_uniformEquilibriumPayoff_of_fastFinkCorrectedCalendarSelection
    (G : StochasticGame ι)
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ i, Finite (G.Act i)] [∀ i, Nonempty (G.Act i)] (s₀ : G.State)
    (hselection :
      letI : Fintype G.State := Fintype.ofFinite G.State
      letI : ∀ i, Fintype (G.Act i) := fun i => Fintype.ofFinite (G.Act i)
      G.HasFastFinkCorrectedCalendarSelection) :
    ∃ v : Payoff ι, G.IsUniformEquilibriumPayoff s₀ v := by
  letI : Fintype G.State := Fintype.ofFinite G.State
  letI : ∀ i, Fintype (G.Act i) := fun i => Fintype.ofFinite (G.Act i)
  let payoffCoordinate : G.State × G.JointAct × ι → ℝ := fun p =>
    G.stagePayoff p.1 p.2.1 p.2.2
  obtain ⟨C, hC⟩ :=
    Math.Probability.exists_abs_bound_of_finite payoffCoordinate
  let U : ℝ := max C 0
  have hU : 0 ≤ U := le_max_right C 0
  have hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U := by
    intro s a who
    exact (hC (s, a, who)).trans (le_max_left C 0)
  exact G.exists_uniformEquilibriumPayoff_of_fastFinkCorrectedCalendarSelection_aux
    s₀ U hU hpay hselection

end StochasticGame
end GameTheory
