/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.AllTailRepairValue
import UniformEquilibrium.Quitting.Root.NearSureRoot
import UniformEquilibrium.Quitting.Terminal.TailCompression.ElementaryCaps

/-!
# The fixed-prefix behavioral-tail repair value

This module specializes the common fixed-family holonomy modulus to the
source-independent family of all quitting behavior tails.  Each tail supplies
one co-realized boundary pair: its prescribed terminal payoff and its literal
all-behavior best-response envelope.  The infimum over these actual pairs is
therefore Lipschitz in the prefix holonomy.

The result is a fixed-prefix statement.  It does not say that a positive value
after one prefix is a global terminal exploitability gap, and it does not by
itself identify the coefficient expression with exploitability of an attached
infinite phase-switch profile.  The latter is a separate semantic adapter.
-/

noncomputable section

namespace GameTheory

open StochasticGame Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

namespace QuittingBoundaryHolonomy

/-- The prescribed boundary vector co-realized by one behavioral tail. -/
def behavioralTailPrescribedBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) : ι → ℝ :=
  fun who => quittingRootSequenceTerminalValue reward roots who 0

/-- The all-behavior unilateral envelope co-realized by the same tail. -/
def behavioralTailEnvelopeBoundary
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) : ι → ℝ :=
  fun who => quittingRootSequenceBestResponseValue reward roots who

/-- Maximum positive prefix gain at the boundary pair supplied by one actual
behavioral tail. -/
def behavioralTailGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (holonomy : QuittingBoundaryHolonomy ι)
    (roots : ℕ → ι → PMF Bool) : ℝ :=
  holonomy.maxCoRealizedGain
    (behavioralTailPrescribedBoundary reward roots)
    (behavioralTailEnvelopeBoundary reward roots)

/-- The best gain obtainable by attaching an arbitrary behavioral tail after
the fixed prefix, represented as the infimum over co-realized boundary pairs.
-/
def behavioralTailRepairValue
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (holonomy : QuittingBoundaryHolonomy ι) : ℝ :=
  sInf (Set.range (behavioralTailGain reward holonomy))

omit [DecidableEq ι] [Nonempty ι] in
theorem abs_behavioralTailPrescribedBoundary_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |behavioralTailPrescribedBoundary reward roots who| ≤ M := by
  exact abs_quittingRootSequenceTerminalValue_le
    reward roots who 0 hM hreward

omit [Nonempty ι] in
theorem abs_behavioralTailEnvelopeBoundary_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (who : ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |behavioralTailEnvelopeBoundary reward roots who| ≤ M := by
  simpa [behavioralTailEnvelopeBoundary,
    quittingRootSequenceBestResponseValue,
    quittingContinuationBestResponse] using
    (abs_quittingContinuationBestResponse_le reward
      (quittingRootSequenceProfile reward roots 0) who hM hreward)

/-- Every maximum-positive gain is nonnegative. -/
theorem behavioralTailGain_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (holonomy : QuittingBoundaryHolonomy ι)
    (roots : ℕ → ι → PMF Bool) :
    0 ≤ behavioralTailGain reward holonomy roots := by
  let who : ι := Classical.choice inferInstance
  unfold behavioralTailGain maxCoRealizedGain
  exact (le_max_left 0
      (holonomy.coRealizedGain
        (behavioralTailPrescribedBoundary reward roots)
        (behavioralTailEnvelopeBoundary reward roots) who)).trans
    (le_finitePlayerMax (fun player => max 0
      (holonomy.coRealizedGain
        (behavioralTailPrescribedBoundary reward roots)
        (behavioralTailEnvelopeBoundary reward roots) player)) who)

/-- The actual behavioral-tail gain family is bounded below. -/
theorem bddBelow_range_behavioralTailGain
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (holonomy : QuittingBoundaryHolonomy ι) :
    BddBelow (Set.range (behavioralTailGain reward holonomy)) := by
  refine ⟨0, ?_⟩
  rintro value ⟨roots, rfl⟩
  exact behavioralTailGain_nonneg reward holonomy roots

/-- The common coefficient modulus applies to every actual behavioral tail,
with the prescribed and envelope coordinates kept co-realized. -/
theorem behavioralTailGain_lipschitz
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M : ℝ) (holonomy holonomy' : QuittingBoundaryHolonomy ι)
    (roots : ℕ → ι → PMF Bool)
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |behavioralTailGain reward holonomy roots -
        behavioralTailGain reward holonomy' roots| ≤
      maxCoordinateDistance M holonomy holonomy' := by
  exact maxCoRealizedGain_lipschitz M holonomy holonomy'
    (behavioralTailPrescribedBoundary reward roots)
    (behavioralTailEnvelopeBoundary reward roots)
    (fun who => abs_behavioralTailPrescribedBoundary_le
      reward roots who hM hreward)
    (fun who => abs_behavioralTailEnvelopeBoundary_le
      reward roots who hM hreward)

/-- The infimum over all co-realized behavioral tails inherits the same
fixed-prefix Lipschitz modulus. -/
theorem behavioralTailRepairValue_lipschitz
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M : ℝ) (holonomy holonomy' : QuittingBoundaryHolonomy ι)
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M) :
    |behavioralTailRepairValue reward holonomy -
        behavioralTailRepairValue reward holonomy'| ≤
      maxCoordinateDistance M holonomy holonomy' := by
  apply sInf_range_lipschitz_of_common_modulus
    (behavioralTailGain reward holonomy)
    (behavioralTailGain reward holonomy')
    (maxCoordinateDistance M holonomy holonomy')
    (bddBelow_range_behavioralTailGain reward holonomy)
    (bddBelow_range_behavioralTailGain reward holonomy')
  · intro roots
    have habs := behavioralTailGain_lipschitz
      reward M holonomy holonomy' roots hM hreward
    have hle := (le_abs_self
      (behavioralTailGain reward holonomy roots -
        behavioralTailGain reward holonomy' roots)).trans habs
    linarith
  · intro roots
    have habs := behavioralTailGain_lipschitz
      reward M holonomy holonomy' roots hM hreward
    have hle := (neg_le_abs
      (behavioralTailGain reward holonomy roots -
        behavioralTailGain reward holonomy' roots)).trans habs
    linarith

/-- One actual tail which repairs the center with buffer repairs every prefix
inside the corresponding holonomy ball. -/
theorem behavioralTail_repair_transfer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M ε : ℝ) (holonomy holonomy₀ : QuittingBoundaryHolonomy ι)
    (roots : ℕ → ι → PMF Bool)
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hcenter : behavioralTailGain reward holonomy₀ roots < ε / 4)
    (hclose : maxCoordinateDistance M holonomy holonomy₀ < ε / 4) :
    behavioralTailGain reward holonomy roots < ε / 2 := by
  apply fixedFamily_repair_transfer
    (behavioralTailGain reward) holonomy holonomy₀ ε
    (maxCoordinateDistance M holonomy holonomy₀) roots
  · intro tail
    exact behavioralTailGain_lipschitz
      reward M holonomy holonomy₀ tail hM hreward
  · exact hcenter
  · exact hclose

/-- A buffered positive all-tail value at the center is a floor against every
behavioral tail throughout the corresponding holonomy ball. -/
theorem behavioralTail_obstruction_transfer
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M ε : ℝ) (holonomy holonomy₀ : QuittingBoundaryHolonomy ι)
    (hM : 0 ≤ M)
    (hreward : ∀ terminal player, |reward terminal player| ≤ M)
    (hinf : ε / 4 ≤ behavioralTailRepairValue reward holonomy₀)
    (hclose : maxCoordinateDistance M holonomy holonomy₀ < ε / 8)
    (roots : ℕ → ι → PMF Bool) :
    ε / 8 ≤ behavioralTailGain reward holonomy roots := by
  apply fixedFamily_obstruction_transfer
    (behavioralTailGain reward) holonomy holonomy₀ ε
    (maxCoordinateDistance M holonomy holonomy₀)
  · intro tail
    exact behavioralTailGain_lipschitz
      reward M holonomy holonomy₀ tail hM hreward
  · exact bddBelow_range_behavioralTailGain reward holonomy₀
  · simpa [behavioralTailRepairValue] using hinf
  · exact hclose

end QuittingBoundaryHolonomy

end GameTheory
