import Math.PMFProduct
import Math.Probability
import GameTheory.Concepts.SolutionConcepts

/-!
# Mixed Extension Properties

Basic properties of the mixed extension of a kernel game: EU decomposition,
gain characterization, and the Nash gain-sum identity.

These are definitions and properties of the mixed extension concept, not
the existence theorem (which lives in `Theorems.NashExistenceMixed`).
-/

noncomputable section

open scoped BigOperators
namespace GameTheory

open Math.Probability

namespace KernelGame
open Math.PMFProduct

variable {ι : Type} [DecidableEq ι]

-- ============================================================================
-- EU in the mixed extension
-- ============================================================================

set_option linter.unusedFintypeInType false in
open Classical in
/-- EU in the mixed extension equals expectation of pure-profile EU
    under the independent product distribution. -/
theorem mixedExtension_eu (G : KernelGame ι)
    [Fintype ι]
    [∀ i, Fintype (G.Strategy i)] [Fintype G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) :
    G.mixedExtension.eu σ who =
      expect (pmfPi σ) (fun s => G.eu s who) := by
  simp only [mixedExtension, eu, expect_bind]; rfl

set_option linter.unusedFintypeInType false in
open Classical in
/-- EU when player `who` deviates to `τ` equals expectation of pure-deviation
    EUs under `τ`. -/
theorem mixedExtension_eu_update (G : KernelGame ι)
    [Fintype ι]
    [∀ i, Fintype (G.Strategy i)] [Fintype G.Outcome]
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) (τ : PMF (G.Strategy who)) :
    G.mixedExtension.eu (Function.update σ who τ) who =
      expect τ (fun a =>
        G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who) := by
  simp only [mixedExtension_eu, KernelGame.mixedExtension_Strategy]
  have hprod : pmfPi (Function.update σ who τ) =
      τ.bind (fun a => pmfPi (Function.update σ who (PMF.pure a))) := by
    ext s
    simp only [PMF.bind_apply, tsum_fintype]
    simp only [pmfPi_apply_update_family, PMF.pure_apply, ite_mul, one_mul, zero_mul,
      mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hprod, expect_bind]

-- ============================================================================
-- Gains and Nash characterization
-- ============================================================================

section NashGain

variable [Fintype ι]
variable (G : KernelGame ι)
variable [∀ i, Fintype (G.Strategy i)]
variable [Fintype G.Outcome]

set_option linter.unusedFintypeInType false in
open Classical in
/-- The gain of player `who` from a pure deviation to action `a`. -/
def mixedGain (σ : ∀ i, PMF (G.Strategy i)) (who : ι) (a : G.Strategy who) : ℝ :=
  G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who -
  G.mixedExtension.eu σ who

set_option linter.unusedFintypeInType false in
open Classical in
/-- Weighted gain sum is zero: the expectation of gain under the current
    mixed strategy is zero. -/
theorem weighted_gain_sum_zero
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) :
    expect (σ who) (fun a => G.mixedGain σ who a) = 0 := by
  simp only [mixedGain, expect_eq_sum]
  have hsum1 : ∑ a : G.Strategy who, ((σ who) a).toReal = 1 := by
    simpa using pmf_toReal_sum_one (σ who)
  have hdecomp : ∑ a : G.Strategy who, ((σ who) a).toReal *
      G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who =
    G.mixedExtension.eu σ who := by
    rw [← expect_eq_sum, ← G.mixedExtension_eu_update σ who (σ who)]
    congr 1
    exact Function.update_eq_self who σ
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, hdecomp]
  rw [show ∑ a : G.Strategy who, ((σ who) a).toReal * G.mixedExtension.eu σ who =
    G.mixedExtension.eu σ who from by
      rw [← Finset.sum_mul, hsum1, one_mul]]
  ring

variable [∀ i, Nonempty (G.Strategy i)]

set_option linter.unusedFintypeInType false in
open Classical in
/-- A mixed profile is Nash iff all pure-deviation gains are non-positive. -/
theorem isNash_iff_gains_nonpos
    (σ : ∀ i, PMF (G.Strategy i)) :
    G.mixedExtension.IsNash σ ↔
      ∀ who (a : G.Strategy who), G.mixedGain σ who a ≤ 0 := by
  constructor
  · intro hN who a
    have h := hN who (PMF.pure a)
    simp only [mixedGain]
    linarith
  · intro hgain who τ
    rw [ge_iff_le]
    have hdecomp := G.mixedExtension_eu_update σ who τ
    rw [hdecomp]
    conv_rhs => rw [show G.mixedExtension.eu σ who =
        expect τ (fun _ => G.mixedExtension.eu σ who) from by
      simp [expect_const]]
    apply Math.ProbabilityMassFunction.expect_mono_of_pointwise
    intro a
    have hga := hgain who a
    simp only [mixedGain] at hga
    linarith

end NashGain

end KernelGame

end GameTheory
