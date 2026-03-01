import GameTheory.SolutionConcepts
import GameTheory.PMFProduct
import GameTheory.ProductSimplexBrouwer

/-!
# Mixed-Strategy Nash Equilibrium Existence

Nash's theorem: every finite game has a mixed-strategy Nash equilibrium.

## Main definitions

- `KernelGame.mixedExtension` — the mixed extension of a kernel game

## Main results

- `KernelGame.mixed_nash_exists` — existence of mixed Nash equilibrium

## Proof structure

The algebraic core is fully proved: a fixed point of Nash's gain-based map
on the product of simplices is a Nash equilibrium. The fixed-point existence
relies on Brouwer's theorem (`ProductSimplexBrouwer`) applied to the
continuous Nash map.
-/

noncomputable section

open scoped BigOperators
namespace GameTheory

namespace KernelGame

variable {ι : Type}

-- ============================================================================
-- Mixed extension of a KernelGame
-- ============================================================================

open Classical in
/-- The mixed extension of a kernel game. Each player's strategy is lifted from
    `G.Strategy i` to `PMF (G.Strategy i)` (a mixed strategy). The outcome kernel
    samples from the independent product distribution over pure strategy profiles,
    then applies the original outcome kernel. -/
def mixedExtension (G : KernelGame ι) [Fintype ι]
    [∀ i, Fintype (G.Strategy i)] : KernelGame ι where
  Strategy := fun i => PMF (G.Strategy i)
  Outcome := G.Outcome
  utility := G.utility
  outcomeKernel := fun σ => (pmfPi σ).bind G.outcomeKernel

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
  simp only [mixedExtension, eu]
  rw [expect_bind]

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
  simp only [mixedExtension_eu]
  have hprod : pmfPi (Function.update σ who τ) =
      τ.bind (fun a => pmfPi (Function.update σ who (PMF.pure a))) := by
    ext s
    simp only [PMF.bind_apply, tsum_fintype]
    rw [pmfPi_apply_update_family]
    simp only [pmfPi_apply_update_family, PMF.pure_apply, ite_mul, one_mul, zero_mul,
      mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [hprod, expect_bind]

-- ============================================================================
-- Gains and Nash characterization
-- ============================================================================

section NashGain

variable [Fintype ι]
variable (G : KernelGame ι)
variable [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
variable [Fintype G.Outcome]

set_option linter.unusedFintypeInType false in
open Classical in
/-- The gain of player `who` from a pure deviation to action `a`. -/
def mixedGain (σ : ∀ i, PMF (G.Strategy i)) (who : ι) (a : G.Strategy who) : ℝ :=
  G.mixedExtension.eu (Function.update σ who (PMF.pure a)) who -
  G.mixedExtension.eu σ who

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
    simp only [expect_eq_sum]
    apply Finset.sum_le_sum
    intro a _
    have hga := hgain who a
    simp only [mixedGain] at hga
    apply mul_le_mul_of_nonneg_left
    · linarith
    · exact ENNReal.toReal_nonneg

set_option linter.unusedFintypeInType false in
open Classical in
omit [∀ (i : ι), Nonempty (G.Strategy i)] in
/-- Weighted gain sum is zero: the expectation of gain under the current
    mixed strategy is zero. -/
theorem weighted_gain_sum_zero
    (σ : ∀ i, PMF (G.Strategy i)) (who : ι) :
    expect (σ who) (fun a => G.mixedGain σ who a) = 0 := by
  simp only [mixedGain, expect_eq_sum]
  have hsum1 : ∑ a : G.Strategy who, ((σ who) a).toReal = 1 := by
    have h := PMF.tsum_coe (σ who)
    rw [tsum_fintype] at h
    rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top (σ who) a)]
    simp [h]
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

end NashGain

-- ============================================================================
-- Positive part helper
-- ============================================================================

/-- The positive part of a real number. -/
def pospart (x : ℝ) : ℝ := max x 0

theorem pospart_nonneg (x : ℝ) : 0 ≤ pospart x := le_max_right x 0

theorem pospart_eq_zero_iff (x : ℝ) : pospart x = 0 ↔ x ≤ 0 := by
  simp only [pospart]
  constructor
  · intro h; by_contra hgt; push_neg at hgt
    have : max x 0 = x := max_eq_left (le_of_lt hgt)
    linarith
  · intro h; exact max_eq_right h

theorem pospart_mul_self (x : ℝ) : x * pospart x = pospart x ^ 2 := by
  simp only [pospart]
  by_cases h : x ≤ 0
  · have : max x 0 = 0 := max_eq_right h; simp [this]
  · push_neg at h
    have : max x 0 = x := max_eq_left (le_of_lt h)
    simp [this, sq]

theorem continuous_pospart : Continuous pospart := by
  simpa [pospart] using (continuous_id.max continuous_const)

-- ============================================================================
-- Fixed point of Nash's map implies Nash equilibrium
-- ============================================================================

section NashMapAlgebra

variable [Fintype ι]
variable (G : KernelGame ι)
variable [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
variable [Fintype G.Outcome]

set_option linter.unusedFintypeInType false in
open Classical in
/-- The sum of positive gains for player `who`. -/
def gainSum (σ : ∀ i, PMF (G.Strategy i)) (who : ι) : ℝ :=
  ∑ a : G.Strategy who, pospart (G.mixedGain σ who a)

set_option linter.unusedFintypeInType false in
omit [∀ (i : ι), Nonempty (G.Strategy i)] [Fintype G.Outcome] in
open Classical in
theorem gainSum_nonneg (σ : ∀ i, PMF (G.Strategy i)) (who : ι) :
    0 ≤ G.gainSum σ who :=
  Finset.sum_nonneg (fun _ _ => pospart_nonneg _)

set_option linter.unusedFintypeInType false in
open Classical in
/-- If σ satisfies the Nash map fixed-point identity, then σ is Nash.
    This is the core algebraic content of Nash's existence proof. -/
theorem nash_fp_is_nash
    (σ : ∀ i, PMF (G.Strategy i))
    (hfp : ∀ who (a : G.Strategy who),
      (σ who a).toReal * (1 + G.gainSum σ who) =
        (σ who a).toReal + pospart (G.mixedGain σ who a)) :
    G.mixedExtension.IsNash σ := by
  rw [G.isNash_iff_gains_nonpos σ]
  suffices hS : ∀ who, G.gainSum σ who = 0 by
    intro who a
    have hident : (σ who a).toReal * G.gainSum σ who =
        pospart (G.mixedGain σ who a) := by have h := hfp who a; linarith
    rw [hS who, mul_zero] at hident
    rw [← pospart_eq_zero_iff]; exact hident.symm
  intro who
  have hident : ∀ a : G.Strategy who,
      (σ who a).toReal * G.gainSum σ who =
        pospart (G.mixedGain σ who a) := by
    intro a; have h := hfp who a; linarith
  have hwg_sum : ∑ a : G.Strategy who,
      (σ who a).toReal * G.mixedGain σ who a = 0 := by
    have hwg := G.weighted_gain_sum_zero σ who
    rwa [expect_eq_sum] at hwg
  have hsum_sq : ∑ a : G.Strategy who,
      pospart (G.mixedGain σ who a) * G.mixedGain σ who a = 0 := by
    have : G.gainSum σ who *
        (∑ a : G.Strategy who, (σ who a).toReal * G.mixedGain σ who a) =
      ∑ a : G.Strategy who, pospart (G.mixedGain σ who a) * G.mixedGain σ who a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _; have h := hident a
      calc G.gainSum σ who * ((σ who a).toReal * G.mixedGain σ who a)
          _ = (σ who a).toReal * G.gainSum σ who * G.mixedGain σ who a := by ring
          _ = pospart (G.mixedGain σ who a) * G.mixedGain σ who a := by rw [h]
    rw [hwg_sum, mul_zero] at this; linarith
  have hnn : ∀ a : G.Strategy who,
      0 ≤ pospart (G.mixedGain σ who a) * G.mixedGain σ who a := by
    intro a
    have := pospart_mul_self (G.mixedGain σ who a)
    nlinarith [sq_nonneg (pospart (G.mixedGain σ who a))]
  have hall_zero := Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a) |>.mp hsum_sq
  have hpospart_zero : ∀ a : G.Strategy who, pospart (G.mixedGain σ who a) = 0 := by
    intro a
    have h0 := hall_zero a (Finset.mem_univ a)
    have hsq : pospart (G.mixedGain σ who a) ^ 2 = 0 := by
      have := pospart_mul_self (G.mixedGain σ who a); nlinarith
    exact pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hsq
  simp [gainSum, hpospart_zero]

end NashMapAlgebra

-- ============================================================================
-- Encoding between PMF and real weight vectors
-- ============================================================================

section Encoding

variable {α : Type} [Fintype α] [Nonempty α]

/-- Convert a PMF on a finite type to a real-valued weight vector. -/
def pmfToReal (μ : PMF α) : α → ℝ := fun a => (μ a).toReal

set_option linter.unusedFintypeInType false in
omit [Fintype α] [Nonempty α] in
theorem pmfToReal_nonneg (μ : PMF α) (a : α) : 0 ≤ pmfToReal μ a :=
  ENNReal.toReal_nonneg

omit [Nonempty α] in
theorem pmfToReal_sum_one (μ : PMF α) : ∑ a : α, pmfToReal μ a = 1 := by
  simp only [pmfToReal]
  have h := PMF.tsum_coe μ
  rw [tsum_fintype] at h
  rw [← ENNReal.toReal_sum (fun a _ => PMF.apply_ne_top μ a)]
  simp [h]

/-- Convert a non-negative weight vector summing to 1 to a PMF. -/
def realToPmf (w : α → ℝ) (hw_nn : ∀ a, 0 ≤ w a) (hw_sum : ∑ a, w a = 1) : PMF α :=
  PMF.ofFintype (fun a => ENNReal.ofReal (w a)) (by
    rw [← ENNReal.ofReal_one, ← hw_sum]
    exact (ENNReal.ofReal_sum_of_nonneg (fun i _ => hw_nn i)).symm)

omit [Nonempty α] in
theorem realToPmf_apply (w : α → ℝ) (hw_nn : ∀ a, 0 ≤ w a) (hw_sum : ∑ a, w a = 1) (a : α) :
    (realToPmf w hw_nn hw_sum) a = ENNReal.ofReal (w a) := by
  simp [realToPmf, PMF.ofFintype_apply]

omit [Nonempty α] in
theorem realToPmf_toReal (w : α → ℝ) (hw_nn : ∀ a, 0 ≤ w a) (hw_sum : ∑ a, w a = 1) (a : α) :
    ((realToPmf w hw_nn hw_sum) a).toReal = w a := by
  rw [realToPmf_apply]
  exact ENNReal.toReal_ofReal (hw_nn a)

end Encoding

-- ============================================================================
-- Nash's map on real weight vectors
-- ============================================================================

section NashMapReal

variable [Fintype ι]
variable (G : KernelGame ι)
variable [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
variable [Fintype G.Outcome]

set_option linter.unusedFintypeInType false in
open Classical in
/-- Convert a real weight profile to a PMF profile. -/
def profileFromWeights
    (w : ∀ i, G.Strategy i → ℝ)
    (hw_nn : ∀ i a, 0 ≤ w i a)
    (hw_sum : ∀ i, ∑ a, w i a = 1) : ∀ i, PMF (G.Strategy i) :=
  fun i => realToPmf (w i) (hw_nn i) (hw_sum i)

set_option linter.unusedFintypeInType false in
open Classical in
/-- Nash's map on real weight vectors. -/
def nashMap
    (w : ∀ i, G.Strategy i → ℝ)
    (hw_nn : ∀ i a, 0 ≤ w i a)
    (hw_sum : ∀ i, ∑ a, w i a = 1) :
    ∀ i, G.Strategy i → ℝ :=
  fun i a =>
    let σ := G.profileFromWeights w hw_nn hw_sum
    let g := pospart (G.mixedGain σ i a)
    let S := G.gainSum σ i
    (w i a + g) / (1 + S)

set_option linter.unusedFintypeInType false in
open Classical in
omit [∀ (i : ι), Nonempty (G.Strategy i)] [Fintype G.Outcome] in
/-- Nash's map preserves non-negativity of weights. -/
theorem nashMap_nonneg
    (w : ∀ i, G.Strategy i → ℝ)
    (hw_nn : ∀ i a, 0 ≤ w i a)
    (hw_sum : ∀ i, ∑ a, w i a = 1) (i : ι) (a : G.Strategy i) :
    0 ≤ G.nashMap w hw_nn hw_sum i a := by
  simp only [nashMap]
  apply div_nonneg
  · linarith [hw_nn i a, pospart_nonneg (G.mixedGain
      (G.profileFromWeights w hw_nn hw_sum) i a)]
  · linarith [G.gainSum_nonneg (G.profileFromWeights w hw_nn hw_sum) i]

set_option linter.unusedFintypeInType false in
open Classical in
omit [∀ (i : ι), Nonempty (G.Strategy i)] [Fintype G.Outcome] in
/-- Nash's map preserves the sum-to-one property. -/
theorem nashMap_sum_one
    (w : ∀ i, G.Strategy i → ℝ)
    (hw_nn : ∀ i a, 0 ≤ w i a)
    (hw_sum : ∀ i, ∑ a, w i a = 1) (i : ι) :
    ∑ a, G.nashMap w hw_nn hw_sum i a = 1 := by
  simp only [nashMap]
  have hS := G.gainSum_nonneg (G.profileFromWeights w hw_nn hw_sum) i
  have hden_pos : 0 < 1 + G.gainSum (G.profileFromWeights w hw_nn hw_sum) i := by linarith
  have hden_ne : (1 + G.gainSum (G.profileFromWeights w hw_nn hw_sum) i) ≠ 0 := ne_of_gt hden_pos
  simp_rw [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← div_eq_mul_inv]
  rw [show ∑ a : G.Strategy i,
      (w i a + pospart (G.mixedGain (G.profileFromWeights w hw_nn hw_sum) i a)) =
    (∑ a, w i a) + ∑ a, pospart (G.mixedGain
      (G.profileFromWeights w hw_nn hw_sum) i a) from
      Finset.sum_add_distrib]
  rw [hw_sum i]; simp only [gainSum]
  exact div_self hden_ne

set_option linter.unusedFintypeInType false in
open Classical in
omit [∀ (i : ι), Nonempty (G.Strategy i)] [Fintype G.Outcome] in
/-- A fixed point of Nash's map satisfies the algebraic identity for `nash_fp_is_nash`. -/
theorem nashMap_fp_identity
    (w : ∀ i, G.Strategy i → ℝ)
    (hw_nn : ∀ i a, 0 ≤ w i a)
    (hw_sum : ∀ i, ∑ a, w i a = 1)
    (hfp : G.nashMap w hw_nn hw_sum = w) :
    let σ := G.profileFromWeights w hw_nn hw_sum
    ∀ who (a : G.Strategy who),
      (σ who a).toReal * (1 + G.gainSum σ who) =
        (σ who a).toReal + pospart (G.mixedGain σ who a) := by
  intro σ who a
  have hw_eq : (σ who a).toReal = w who a :=
    realToPmf_toReal (w who) (hw_nn who) (hw_sum who) a
  rw [hw_eq]
  have hfp_a : w who a = (w who a + pospart (G.mixedGain σ who a)) /
      (1 + G.gainSum σ who) := (congr_fun (congr_fun hfp who) a).symm
  have hS_pos : 0 < 1 + G.gainSum σ who := by
    linarith [G.gainSum_nonneg σ who]
  field_simp at hfp_a ⊢
  linarith [mul_comm (w who a) (1 + G.gainSum σ who),
    mul_div_cancel₀ (w who a + pospart (G.mixedGain σ who a)) (ne_of_gt hS_pos)]

end NashMapReal

-- ============================================================================
-- Mixed-simplex bridge (non-axiomatic route)
-- ============================================================================

section NashMapMixedSimplex

variable [Fintype ι]
variable (G : KernelGame ι)
variable [∀ i, Fintype (G.Strategy i)]

section  -- Definitions require [Nonempty] and [Fintype Outcome]
variable [∀ i, Nonempty (G.Strategy i)] [Fintype G.Outcome]

/-- Convert a mixed-simplex profile to PMF profile (same coordinates, repackaged). -/
noncomputable def profileFromMixedSimplex
    (x : MixedSimplex ι (fun i => G.Strategy i)) :
    ∀ i, PMF (G.Strategy i) := by
  let w : ∀ j, G.Strategy j → ℝ := fun j a => x j a
  have hw_nn : ∀ j a, 0 ≤ w j a := by
    intro j a
    exact stdSimplex.zero_le (x j) a
  have hw_sum : ∀ j, ∑ a, w j a = 1 := by
    intro j
    simp [w]
  exact G.profileFromWeights w hw_nn hw_sum

/-- Gain viewed on the mixed-simplex domain. -/
noncomputable def mixedGainOnMixedSimplex
    (x : MixedSimplex ι (fun i => G.Strategy i))
    (who : ι) (a : G.Strategy who) : ℝ :=
  G.mixedGain (G.profileFromMixedSimplex x) who a

/-- Positive-gain sum viewed on the mixed-simplex domain. -/
noncomputable def gainSumOnMixedSimplex
    (x : MixedSimplex ι (fun i => G.Strategy i)) (who : ι) : ℝ :=
  G.gainSum (G.profileFromMixedSimplex x) who

/-- Nash map viewed as a self-map of the mixed-profile product simplex. -/
noncomputable def nashMapOnMixedSimplex :
    MixedSimplex ι (fun i => G.Strategy i) →
      MixedSimplex ι (fun i => G.Strategy i) := by
  intro x i
  let w : ∀ j, G.Strategy j → ℝ := fun j a => x j a
  have hw_nn : ∀ j a, 0 ≤ w j a := by
    intro j a
    exact stdSimplex.zero_le (x j) a
  have hw_sum : ∀ j, ∑ a, w j a = 1 := by
    intro j
    simp [w]
  refine ⟨(fun a => G.nashMap w hw_nn hw_sum i a), ?_, ?_⟩
  · intro a
    exact G.nashMap_nonneg w hw_nn hw_sum i a
  · simpa using G.nashMap_sum_one w hw_nn hw_sum i

end  -- definitions section

theorem gainSumOnMixedSimplex_nonneg
    (x : MixedSimplex ι (fun i => G.Strategy i)) (who : ι) :
    0 ≤ G.gainSumOnMixedSimplex x who := by
  exact G.gainSum_nonneg (G.profileFromMixedSimplex x) who

@[simp] theorem nashMapOnMixedSimplex_apply
    (x : MixedSimplex ι (fun i => G.Strategy i))
    (i : ι) (a : G.Strategy i) :
    ((G.nashMapOnMixedSimplex x i : stdSimplex ℝ (G.Strategy i)) a) =
      (x i a + pospart (G.mixedGainOnMixedSimplex x i a)) /
        (1 + G.gainSumOnMixedSimplex x i) := by
  rfl

/--
If baseline mixed EU and all pure-deviation mixed EU maps are continuous on the mixed simplex,
then mixed gains are continuous on the mixed simplex.
-/
theorem continuous_mixedGainOnMixedSimplex_of_continuous_mixedEu
    (hbase : ∀ who,
      Continuous (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
        G.mixedExtension.eu (G.profileFromMixedSimplex x) who))
    (hdev : ∀ who (a : G.Strategy who),
      Continuous (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
        G.mixedExtension.eu
          (@Function.update ι G.mixedExtension.Strategy
            (fun u v => Classical.propDecidable (u = v))
            (G.profileFromMixedSimplex x) who (PMF.pure a)) who)) :
    ∀ who (a : G.Strategy who),
      Continuous (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
        G.mixedGainOnMixedSimplex x who a) := by
  intro who a
  simpa [mixedGainOnMixedSimplex, mixedGain] using (hdev who a).sub (hbase who)

/-- Weight-level fixed-point witness extracted from a mixed-simplex fixed point. -/
theorem nashMap_weightFixedPoint_of_mixedSimplexFixedPoint
    (hfix : ∃ x, Function.IsFixedPt (G.nashMapOnMixedSimplex) x) :
    ∃ (w : ∀ i, G.Strategy i → ℝ)
      (hw_nn : ∀ i a, 0 ≤ w i a) (hw_sum : ∀ i, ∑ a, w i a = 1),
      G.nashMap w hw_nn hw_sum = w := by
  rcases hfix with ⟨x, hfx⟩
  let w : ∀ j, G.Strategy j → ℝ := fun j a => x j a
  have hw_nn : ∀ j a, 0 ≤ w j a := by
    intro j a
    exact stdSimplex.zero_le (x j) a
  have hw_sum : ∀ j, ∑ a, w j a = 1 := by
    intro j
    simp [w]
  have hfp_weights : G.nashMap w hw_nn hw_sum = w := by
    funext who a
    have hwho : ((G.nashMapOnMixedSimplex x who : stdSimplex ℝ (G.Strategy who)) :
        G.Strategy who → ℝ) = (x who : G.Strategy who → ℝ) := by
      exact congrArg Subtype.val (congr_fun hfx who)
    have h := congr_fun hwho a
    simpa [nashMapOnMixedSimplex, w, hw_nn, hw_sum] using h
  exact ⟨w, hw_nn, hw_sum, hfp_weights⟩

section  -- EU continuity needs [Fintype Outcome]
variable [Fintype G.Outcome]

set_option linter.unusedFintypeInType false in
/--
Baseline mixed-EU continuity on the mixed-simplex domain.
This is the `hbase` premise used by
`continuous_nashMapOnMixedSimplex_of_continuous_mixedEu`.
-/
theorem continuous_mixedExtension_eu_profileFromMixedSimplex
    (who : ι) :
    Continuous (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
      G.mixedExtension.eu (G.profileFromMixedSimplex x) who) := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  -- Expand EU under mixed extension into a finite weighted sum over pure profiles.
  have hsum :
      (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
        G.mixedExtension.eu (G.profileFromMixedSimplex x) who)
      =
      (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
        ∑ s : (∀ i, G.Strategy i), (∏ i, x i (s i)) * G.eu s who) := by
    funext x
    rw [G.mixedExtension_eu (σ := G.profileFromMixedSimplex x) who]
    rw [expect_eq_sum]
    refine Finset.sum_congr rfl ?_
    intro s hs
    have hcoef :
        ((pmfPi (G.profileFromMixedSimplex x) s).toReal) =
          ∏ i, x i (s i) := by
      simp [pmfPi_apply, profileFromMixedSimplex, profileFromWeights, realToPmf_toReal]
    rw [hcoef]
  rw [hsum]
  refine continuous_finset_sum (s := (Finset.univ : Finset (∀ i, G.Strategy i))) ?_
  intro s hs
  refine (continuous_finset_prod (s := (Finset.univ : Finset ι)) ?_).mul continuous_const
  intro i hi
  exact (continuous_apply (s i)).comp (continuous_subtype_val.comp (continuous_apply i))

set_option linter.unusedFintypeInType false in
/--
Pure-deviation mixed-EU continuity on the mixed-simplex domain.
This is the `hdev` premise used by
`continuous_nashMapOnMixedSimplex_of_continuous_mixedEu`.
-/
theorem continuous_mixedExtension_eu_update_profileFromMixedSimplex
    (who : ι) (a : G.Strategy who) :
    Continuous (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
      G.mixedExtension.eu
        (@Function.update ι G.mixedExtension.Strategy
          (fun u v => Classical.propDecidable (u = v))
          (G.profileFromMixedSimplex x) who (PMF.pure a)) who) := by
  classical
  letI : DecidableEq ι := Classical.decEq ι
  have hsum :
      (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
        G.mixedExtension.eu
          (@Function.update ι G.mixedExtension.Strategy
            (fun u v => Classical.propDecidable (u = v))
            (G.profileFromMixedSimplex x) who (PMF.pure a)) who)
      =
      (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
        ∑ s : (∀ i, G.Strategy i),
          ((((PMF.pure a) (s who)).toReal) *
            (∏ i ∈ (Finset.univ.erase who), x i (s i))) * G.eu s who) := by
    funext x
    rw [G.mixedExtension_eu
      (σ := @Function.update ι G.mixedExtension.Strategy
        (fun u v => Classical.propDecidable (u = v))
        (G.profileFromMixedSimplex x) who (PMF.pure a)) who]
    rw [expect_eq_sum]
    refine Finset.sum_congr rfl ?_
    intro s hs
    have hcoef :
        ((pmfPi
          (@Function.update ι G.mixedExtension.Strategy
            (fun u v => Classical.propDecidable (u = v))
            (G.profileFromMixedSimplex x) who (PMF.pure a)) s).toReal)
          =
        (((PMF.pure a) (s who)).toReal) *
          (∏ i ∈ (Finset.univ.erase who), x i (s i)) := by
      rw [pmfPi_apply_update_family]
      by_cases hsa : s who = a
      · subst hsa
        simp [PMF.pure_apply, profileFromMixedSimplex, profileFromWeights,
          realToPmf_toReal]
      · simp [PMF.pure_apply, hsa]
    rw [hcoef]
  rw [hsum]
  refine continuous_finset_sum (s := (Finset.univ : Finset (∀ i, G.Strategy i))) ?_
  intro s hs
  have hprod :
      Continuous (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
        ∏ i ∈ (Finset.univ.erase who), x i (s i)) := by
    refine continuous_finset_prod (s := (Finset.univ.erase who)) ?_
    intro i hi
    exact (continuous_apply (s i)).comp (continuous_subtype_val.comp (continuous_apply i))
  exact (continuous_const.mul hprod).mul continuous_const

end  -- [Fintype Outcome] section

/--
Continuity reduction: if all coordinate mixed gains are continuous on the mixed simplex,
then Nash's map on the mixed simplex is continuous.
-/
theorem continuous_nashMapOnMixedSimplex_of_continuous_mixedGainOnMixedSimplex
    (hmg : ∀ who (a : G.Strategy who),
      Continuous (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
        G.mixedGainOnMixedSimplex x who a)) :
    Continuous (G.nashMapOnMixedSimplex) := by
  classical
  -- Coordinatewise continuity for the codomain function values.
  have hcoord :
      ∀ i (a : G.Strategy i),
      Continuous (fun x : MixedSimplex ι (fun j => G.Strategy j) =>
        (x i a + pospart (G.mixedGainOnMixedSimplex x i a)) /
          (1 + G.gainSumOnMixedSimplex x i)) := by
    intro i a
    have hxia : Continuous (fun x : MixedSimplex ι (fun j => G.Strategy j) => x i a) := by
      exact (continuous_apply a).comp (continuous_subtype_val.comp (continuous_apply i))
    have hsum :
        Continuous (fun x : MixedSimplex ι (fun j => G.Strategy j) =>
          G.gainSumOnMixedSimplex x i) := by
      simpa [gainSumOnMixedSimplex, gainSum] using
        (continuous_finset_sum (s := (Finset.univ : Finset (G.Strategy i)))
          (fun a _ => continuous_pospart.comp (hmg i a)))
    have hden_nz :
        ∀ x : MixedSimplex ι (fun j => G.Strategy j),
          (1 + G.gainSumOnMixedSimplex x i) ≠ 0 := by
      intro x
      have hnonneg : 0 ≤ G.gainSumOnMixedSimplex x i := G.gainSumOnMixedSimplex_nonneg x i
      linarith
    exact (hxia.add (continuous_pospart.comp (hmg i a))).div
      (continuous_const.add hsum) hden_nz
  -- Lift coordinate continuity to continuity into product of simplices.
  refine continuous_pi (fun i => ?_)
  exact Continuous.subtype_mk
    (by
      simpa [nashMapOnMixedSimplex_apply] using
        (continuous_pi (fun a => hcoord i a)))
    (fun x => (G.nashMapOnMixedSimplex x i).property)

/-- Approximate fixed points imply a weight-level fixed-point witness for `nashMap`. -/
theorem nashMap_weightFixedPoint_of_nashMapOnMixedSimplex_approx
    (hcont : Continuous (G.nashMapOnMixedSimplex))
    (happrox : ∀ n : ℕ, ∃ x : MixedSimplex ι (fun i => G.Strategy i),
      dist (G.nashMapOnMixedSimplex x) x ≤ (1 : ℝ) / (n + 1)) :
    ∃ (w : ∀ i, G.Strategy i → ℝ)
      (hw_nn : ∀ i a, 0 ≤ w i a) (hw_sum : ∀ i, ∑ a, w i a = 1),
      G.nashMap w hw_nn hw_sum = w := by
  rcases exists_fixedPoint_of_approx_on_mixedSimplex
      (f := G.nashMapOnMixedSimplex) hcont happrox with ⟨x, hxfix⟩
  exact G.nashMap_weightFixedPoint_of_mixedSimplexFixedPoint ⟨x, hxfix⟩

/--
Continuity reduction all the way to EU maps:
continuity of baseline and pure-deviation mixed EU maps implies continuity of Nash's map
on the mixed simplex.
-/
theorem continuous_nashMapOnMixedSimplex_of_continuous_mixedEu
    (hbase : ∀ who,
      Continuous (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
        G.mixedExtension.eu (G.profileFromMixedSimplex x) who))
    (hdev : ∀ who (a : G.Strategy who),
      Continuous (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
        G.mixedExtension.eu
          (@Function.update ι G.mixedExtension.Strategy
            (fun u v => Classical.propDecidable (u = v))
            (G.profileFromMixedSimplex x) who (PMF.pure a)) who)) :
    Continuous (G.nashMapOnMixedSimplex) := by
  refine G.continuous_nashMapOnMixedSimplex_of_continuous_mixedGainOnMixedSimplex ?_
  exact G.continuous_mixedGainOnMixedSimplex_of_continuous_mixedEu hbase hdev

section  -- Game-side continuity closure (needs [Fintype Outcome] only)
variable [Fintype G.Outcome]

set_option linter.unusedFintypeInType false in
/-- Unconditional continuity of Nash's map on mixed simplex (game-side closure). -/
theorem continuous_nashMapOnMixedSimplex :
    Continuous (G.nashMapOnMixedSimplex) := by
  refine G.continuous_nashMapOnMixedSimplex_of_continuous_mixedEu
    (hbase := fun who => G.continuous_mixedExtension_eu_profileFromMixedSimplex who)
    (hdev := fun who a => G.continuous_mixedExtension_eu_update_profileFromMixedSimplex who a)

set_option linter.unusedFintypeInType false in
/--
Nash-map continuity reduced to pure-deviation mixed-EU continuity only
(baseline mixed-EU continuity is provided by
`continuous_mixedExtension_eu_profileFromMixedSimplex`).
-/
theorem continuous_nashMapOnMixedSimplex_of_continuous_mixedEu_deviation
    (hdev : ∀ who (a : G.Strategy who),
      Continuous (fun x : MixedSimplex ι (fun i => G.Strategy i) =>
        G.mixedExtension.eu
          (@Function.update ι G.mixedExtension.Strategy
            (fun u v => Classical.propDecidable (u = v))
            (G.profileFromMixedSimplex x) who (PMF.pure a)) who)) :
    Continuous (G.nashMapOnMixedSimplex) := by
  refine G.continuous_nashMapOnMixedSimplex_of_continuous_mixedEu ?_ hdev
  exact G.continuous_mixedExtension_eu_profileFromMixedSimplex

set_option linter.unusedFintypeInType false in
/--
Approximation-only extraction of a weight-level fixed point for `nashMap`:
continuity is discharged by `continuous_nashMapOnMixedSimplex`.
-/
theorem nashMap_weightFixedPoint_of_nashMapOnMixedSimplex_approxOnly
    (happrox : ∀ n : ℕ, ∃ x : MixedSimplex ι (fun i => G.Strategy i),
      dist (G.nashMapOnMixedSimplex x) x ≤ (1 : ℝ) / (n + 1)) :
    ∃ (w : ∀ i, G.Strategy i → ℝ)
      (hw_nn : ∀ i a, 0 ≤ w i a) (hw_sum : ∀ i, ∑ a, w i a = 1),
      G.nashMap w hw_nn hw_sum = w := by
  exact G.nashMap_weightFixedPoint_of_nashMapOnMixedSimplex_approx
    (hcont := G.continuous_nashMapOnMixedSimplex) happrox

end  -- [Fintype Outcome] game-side closure

section  -- Full continuity and existence theorems
variable [∀ i, Nonempty (G.Strategy i)] [Fintype G.Outcome]

set_option linter.unusedFintypeInType false in
/-- A fixed point of `nashMapOnMixedSimplex` yields a mixed Nash equilibrium. -/
theorem mixed_nash_exists_of_nashMapOnMixedSimplex_fixed_point
    (hfix : ∃ x, Function.IsFixedPt (G.nashMapOnMixedSimplex) x) :
    ∃ σ : ∀ i, PMF (G.Strategy i), G.mixedExtension.IsNash σ := by
  rcases hfix with ⟨x, hfx⟩
  let w : ∀ j, G.Strategy j → ℝ := fun j a => x j a
  have hw_nn : ∀ j a, 0 ≤ w j a := by
    intro j a
    exact stdSimplex.zero_le (x j) a
  have hw_sum : ∀ j, ∑ a, w j a = 1 := by
    intro j
    simp [w]
  have hfp_weights : G.nashMap w hw_nn hw_sum = w := by
    funext who a
    have hwho : ((G.nashMapOnMixedSimplex x who : stdSimplex ℝ (G.Strategy who)) :
        G.Strategy who → ℝ) = (x who : G.Strategy who → ℝ) := by
      exact congrArg Subtype.val (congr_fun hfx who)
    have h := congr_fun hwho a
    simpa [nashMapOnMixedSimplex, w, hw_nn, hw_sum] using h
  exact ⟨G.profileFromWeights w hw_nn hw_sum,
    G.nash_fp_is_nash _ (G.nashMap_fp_identity w hw_nn hw_sum hfp_weights)⟩

set_option linter.unusedFintypeInType false in
/--
Approximate fixed points for `nashMapOnMixedSimplex` imply existence of a mixed Nash equilibrium.
This removes any need for a fixed-point axiom; the only remaining obligations are:
continuity of `nashMapOnMixedSimplex` and approximate fixed points at all scales.
-/
theorem mixed_nash_exists_of_nashMapOnMixedSimplex_approx
    (hcont : Continuous (G.nashMapOnMixedSimplex))
    (happrox : ∀ n : ℕ, ∃ x : MixedSimplex ι (fun i => G.Strategy i),
      dist (G.nashMapOnMixedSimplex x) x ≤ (1 : ℝ) / (n + 1)) :
    ∃ σ : ∀ i, PMF (G.Strategy i), G.mixedExtension.IsNash σ := by
  rcases exists_fixedPoint_of_approx_on_mixedSimplex
      (f := G.nashMapOnMixedSimplex) hcont happrox with ⟨x, hxfix⟩
  exact G.mixed_nash_exists_of_nashMapOnMixedSimplex_fixed_point ⟨x, hxfix⟩

set_option linter.unusedFintypeInType false in
/--
Approximation-only mixed Nash existence:
continuity is discharged by `continuous_nashMapOnMixedSimplex`.
-/
theorem mixed_nash_exists_of_nashMapOnMixedSimplex_approxOnly
    (happrox : ∀ n : ℕ, ∃ x : MixedSimplex ι (fun i => G.Strategy i),
      dist (G.nashMapOnMixedSimplex x) x ≤ (1 : ℝ) / (n + 1)) :
    ∃ σ : ∀ i, PMF (G.Strategy i), G.mixedExtension.IsNash σ := by
  exact G.mixed_nash_exists_of_nashMapOnMixedSimplex_approx
    (hcont := G.continuous_nashMapOnMixedSimplex) happrox

end  -- [Nonempty] + [Fintype Outcome] section

end NashMapMixedSimplex

-- ============================================================================
-- Main theorem
-- ============================================================================

set_option linter.unusedFintypeInType false in
open Classical in
/-- **Nash's Existence Theorem (Mixed Strategies).**

    Every finite kernel game (finite players, finite nonempty strategy sets,
    finite outcomes) admits a mixed-strategy Nash equilibrium. -/
theorem mixed_nash_exists (G : KernelGame ι)
    [Fintype ι]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    [Fintype G.Outcome] :
    ∃ σ : ∀ i, PMF (G.Strategy i), G.mixedExtension.IsNash σ :=
  G.mixed_nash_exists_of_nashMapOnMixedSimplex_fixed_point
    (brouwer_mixedSimplex G.nashMapOnMixedSimplex
      G.continuous_nashMapOnMixedSimplex)

end KernelGame

end GameTheory
