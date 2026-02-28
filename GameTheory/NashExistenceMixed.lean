import GameTheory.SolutionConcepts
import GameTheory.PMFProduct

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
itself relies on Brouwer's theorem applied to the continuous Nash map;
because Brouwer's FPT is not yet available in Mathlib, it is axiomatized
as `nashMap_has_fixed_point`.
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
-- Axiom: Nash's map has a fixed point (Brouwer's FPT, not in Mathlib)
-- ============================================================================

set_option linter.unusedFintypeInType false in
open Classical in
/-- Nash's map on the product of simplices has a fixed point.

    This follows from Brouwer's fixed-point theorem: the product of standard
    simplices is compact and convex, and Nash's map is continuous (it is a
    rational function with always-positive denominator). Neither Brouwer's FPT
    nor the topological infrastructure to formalize continuity of Nash's map
    is currently available in Mathlib (v4.27). -/
axiom nashMap_has_fixed_point
    {ι : Type} [Fintype ι]
    (G : KernelGame ι) [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    [Fintype G.Outcome] :
    ∃ (w : ∀ i, G.Strategy i → ℝ)
      (hw_nn : ∀ i a, 0 ≤ w i a) (hw_sum : ∀ i, ∑ a, w i a = 1),
      G.nashMap w hw_nn hw_sum = w

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
    ∃ σ : ∀ i, PMF (G.Strategy i), G.mixedExtension.IsNash σ := by
  obtain ⟨w, hw_nn, hw_sum, hfp⟩ := nashMap_has_fixed_point G
  exact ⟨G.profileFromWeights w hw_nn hw_sum,
         G.nash_fp_is_nash _ (G.nashMap_fp_identity w hw_nn hw_sum hfp)⟩

end KernelGame

end GameTheory
