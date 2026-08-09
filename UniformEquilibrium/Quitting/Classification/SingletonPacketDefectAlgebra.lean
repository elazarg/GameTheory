/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Singleton packet phase/refusal defect algebra

For a player with owner mass `lambda`, pinned singleton target `z`, and
conditional refusal value `R`, the singleton mixture is

`mixture = lambda * z + (1 - lambda) * R`.

A phase defect and a refusal defect have opposite packet geometry.  A phase
defect makes the pinned target underfunded.  A positive refusal defect at a
proper positive owner mass makes funding strict; any remaining failure of the
funding-and-floor clauses must therefore be the punishment floor.

These are scalar identities.  This file does not identify a periodic-window
occupation with a supplied packet, and it does not prove the survival-
reweighting estimate needed for such an identification.
-/

namespace GameTheory

/-- Mixture decomposition at an owner whose singleton value is `z`. -/
theorem singletonMixture_eq_owner_add_refusal
    (lambda z R : ℝ) :
    lambda * z + (1 - lambda) * R =
      R - lambda * (R - z) := by
  ring

/-- A phase-stop margin at a pinned player transfers verbatim to the packet
target.  Positivity of the margin is deliberately not needed here. -/
theorem phaseDefect_margin_le_target
    {solo mixture target eta : ℝ}
    (hpin : target = solo) (hphase : mixture + eta ≤ solo) :
    mixture + eta ≤ target := by
  simpa [hpin] using hphase

/-- A positive phase-stop defect at a pinned player makes the singleton
mixture strictly underfund the target. -/
theorem phaseDefect_forces_underfunding
    {solo mixture target eta : ℝ}
    (hpin : target = solo) (heta : 0 < eta)
    (hphase : mixture + eta ≤ solo) :
    mixture < target := by
  have hmargin := phaseDefect_margin_le_target hpin hphase
  linarith

/-- A positive refusal defect at a proper positive owner mass makes the
refusal value and the mixture strictly exceed the pinned target. -/
theorem refusalDefect_forces_strictFunding
    {lambda z R mixture eta : ℝ}
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hmixture : mixture = lambda * z + (1 - lambda) * R)
    (heta : 0 < eta) (hrefusal : mixture + eta ≤ R) :
    z < R ∧ z < mixture := by
  have hgap : eta ≤ lambda * (R - z) := by
    rw [hmixture, singletonMixture_eq_owner_add_refusal] at hrefusal
    linarith
  have hRz : 0 < R - z := by
    by_contra hnot
    have hnonpos : R - z ≤ 0 := le_of_not_gt hnot
    have : lambda * (R - z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hlambda0.le hnonpos
    linarith
  constructor
  · linarith
  · rw [hmixture]
    have hweight : 0 < 1 - lambda := sub_pos.mpr hlambda1
    nlinarith

/-- Under a common payoff bound, a refusal margin forces a quantitative
lower bound on the owner's occupation share. -/
theorem refusalDefect_forces_ownerMass
    {lambda z R mixture eta M : ℝ}
    (hlambda0 : 0 ≤ lambda)
    (hmixture : mixture = lambda * z + (1 - lambda) * R)
    (hz : |z| ≤ M) (hR : |R| ≤ M)
    (hrefusal : mixture + eta ≤ R) :
    eta ≤ 2 * M * lambda := by
  have hgap : eta ≤ lambda * (R - z) := by
    rw [hmixture, singletonMixture_eq_owner_add_refusal] at hrefusal
    linarith
  have hRz : R - z ≤ 2 * M := by
    have hz' := abs_le.mp hz
    have hR' := abs_le.mp hR
    linarith
  calc
    eta ≤ lambda * (R - z) := hgap
    _ ≤ lambda * (2 * M) := mul_le_mul_of_nonneg_left hRz hlambda0
    _ = 2 * M * lambda := by ring

/-- Corrected packet-clause alternative.  In the phase branch funding fails.
In the refusal branch funding is strict; if funding and floor nevertheless do
not jointly hold, it is exactly the floor inequality which fails. -/
theorem phaseUnderfunded_or_refusalFloorMissing
    {lambda z R mixture eta chi : ℝ}
    (hlambda0 : 0 < lambda) (hlambda1 : lambda < 1)
    (hmixture : mixture = lambda * z + (1 - lambda) * R)
    (heta : 0 < eta)
    (hbranch : mixture + eta ≤ z ∨ mixture + eta ≤ R)
    (hnotPacketClauses : ¬(z ≤ mixture ∧ chi ≤ z)) :
    mixture < z ∨ (z < mixture ∧ ¬chi ≤ z) := by
  rcases hbranch with hphase | hrefusal
  · exact Or.inl (lt_of_lt_of_le (lt_add_of_pos_right mixture heta) hphase)
  · right
    have hfund := (refusalDefect_forces_strictFunding hlambda0 hlambda1
      hmixture heta hrefusal).2
    exact ⟨hfund, fun hfloor ↦ hnotPacketClauses ⟨hfund.le, hfloor⟩⟩

end GameTheory
