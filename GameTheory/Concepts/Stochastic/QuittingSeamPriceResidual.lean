/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingCycleIsolatedCoordinate
import GameTheory.Concepts.Stochastic.QuittingSurvivalPrefixBridge
import GameTheory.Concepts.Stochastic.QuittingMarkedTimeAdvance
import GameTheory.Concepts.Stochastic.QuittingNashBellmanClockReduction
import Math.SurvivalProduct

/-!
# The seam price: exact residual formula, transport factor, and the deviation no-go

A `δ / ρ` "seam price" law is exact for one object, a sharp bound for a
second, and **false** for a third.  This file audits and formalizes that
law against the three contraction deficits it names:

* `ρ = 1 - ∏_{t<m} c(x_t)` -- the ordinary **value** recursion's deficit;
* `ρ⁻ᵢ = 1 - ∏_{t<m} c_{-i}(x_t)` -- coordinate `i`'s **deviation**
  recursion deficit, built from the *deleted* (opponents-only) product;
* a prefix **survival** factor, which enters every closed form
  multiplicatively and is never a denominator.

## What is proved

1. **The exact residual formula** (`orbit_eq_blockSurvival_mul_add_blockConstant`,
   `sub_blockFixedPoint_eq_div`, `sub_transportedFixedPoint_eq`, and their
   grounded forms `quitting_sub_blockFixedPoint_eq_div` /
   `quitting_sub_transportedFixedPoint_eq`).  For a coordinate `who` and *any*
   sequence obeying the raw value recursion `z t = quittingRootSuccessorPayoff
   reward (z (t+1)) (roots t)` -- no Nash exactness needed, the recursion
   alone is unconditionally affine at each coordinate
   (`quittingRootSuccessorPayoff_apply_eq_affine`) -- the block value map is
   affine with slope the *full* continue-mass product, and
   `z (start+fuel) who - v = d / ρ` exactly, where `d` is the boundary gap and
   `v = B / ρ` is the window's own fixed point.
2. **The transport factor is multiplicative, not a denominator**
   (`one_sub_blockSurvival_eq_sum`,
   `one_sub_blockSurvival_add_eq_prefix_add_transported`,
   `quittingSurvivalPrefix_deficit_eq_prefix_add_transported`).  Splitting a
   window at a prefix of length `a` gives the *exact* decomposition
   `ρ = ρ_prefix + S(a) · ρ_block`: the local block's contribution to the
   whole window's deficit is `S(a) · ρ_block`, strictly smaller than `ρ`
   itself whenever the prefix carries any loss of its own
   (`blockSurvival_mul_deficit_lt_total_deficit_of_prefix_pos`).
3. **The seam-price law is false for the deviation objective under the full
   deficit** (`QuittingSeamPriceDeviationFalsity.seamPriceLaw_fails_for_deviation_via_fullDeficit`).
   At an isolated coordinate the deviation mismatch is the constant
   `max {0, -r_i({i})}`, independent of the absorption rate; the full deficit
   `ρ` is not.  Two explicit rates exhibit a mismatch that no single `δ / ρ`
   law can reproduce.  The correct denominator is the *deleted* deficit
   `1 - ∏ c_{-i}`, which is exactly `0` at an isolated coordinate
   (`quittingRootDeletedContinueMass_eq_one_of_isolated`), not `ρ`.
4. **No pole at zero absorption**
   (`quittingRootSuccessorPayoff_eq_of_continueMass_eq_one`,
   `quitting_orbit_eq_of_blockSurvival_eq_one`).  Full continue mass one
   forces the absorbing contribution to zero as well, so the block value map
   is the literal identity: exact closure still exists at `ρ = 0`, it simply
   cannot alter an externally prescribed mismatch.

## Verification note

The prose formula was checked against the repository's actual Bellman
definitions before formalizing.  `quittingRootSuccessorPayoff`'s coordinate
`who` reads the continuation *only* at `continuation who`
(`quittingRootExpectedPayoff_eq_absorbingContribution_add`), with slope the
*full* joint continue mass -- the same scalar at every coordinate -- which is
exactly the hypothesis the prose's `Φ(z)_i = B_i + C · z_i` needed.  The
formula survived checking intact; no unstated hypothesis was found.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

/-! ## Part 1: abstract affine block composites

Purely real-valued: a sequence of one-step affine maps `w ↦ B t + C t * w`,
composed over a window `[start, start + fuel)`.  No game structure is used
here, only that the composite of affine maps is affine. -/

/-- The product of the per-stage coefficients `C` over the window
`[start, start + fuel)`: the window's survival factor. -/
def blockSurvival (C : ℕ → ℝ) (start fuel : ℕ) : ℝ :=
  ∏ offset ∈ Finset.range fuel, C (start + offset)

/-- **Bridge to the canonical survival product.**  `blockSurvival` is
`Math.survivalProduct` by the identical defining formula -- see the module
docstring of `Math.SurvivalProduct` for the full census this bridges into. -/
theorem blockSurvival_eq_survivalProduct (C : ℕ → ℝ) (start fuel : ℕ) :
    blockSurvival C start fuel = Math.survivalProduct C start fuel := rfl

@[simp] theorem blockSurvival_zero (C : ℕ → ℝ) (start : ℕ) :
    blockSurvival C start 0 = 1 := by
  simp [blockSurvival]

/-- Appending one more stage at the far end multiplies survival by that
stage's coefficient. -/
theorem blockSurvival_succ (C : ℕ → ℝ) (start fuel : ℕ) :
    blockSurvival C start (fuel + 1) =
      blockSurvival C start fuel * C (start + fuel) := by
  simp [blockSurvival, Finset.prod_range_succ]

/-- Survival over a concatenated window splits multiplicatively into the
survival of its two pieces. -/
theorem blockSurvival_add (C : ℕ → ℝ) (start a b : ℕ) :
    blockSurvival C start (a + b) =
      blockSurvival C start a * blockSurvival C (start + a) b := by
  induction b with
  | zero => simp
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 by omega, blockSurvival_succ, ih,
        blockSurvival_succ, show start + a + b = start + (a + b) by omega]
      ring

/-- The unrolled affine constant term over `[start, start + fuel)`: the
composite one-step maps `w ↦ B t + C t * w`, applied in sequence from
`start + fuel` down to `start`, evaluated at continuation `0`. -/
def blockConstant (B C : ℕ → ℝ) (start fuel : ℕ) : ℝ :=
  ∑ offset ∈ Finset.range fuel, blockSurvival C start offset * B (start + offset)

@[simp] theorem blockConstant_zero (B C : ℕ → ℝ) (start : ℕ) :
    blockConstant B C start 0 = 0 := by
  simp [blockConstant]

/-- Appending one more stage at the far end adds that stage's own additive
term, transported by the survival already accumulated. -/
theorem blockConstant_succ (B C : ℕ → ℝ) (start fuel : ℕ) :
    blockConstant B C start (fuel + 1) =
      blockConstant B C start fuel + blockSurvival C start fuel * B (start + fuel) := by
  unfold blockConstant
  rw [Finset.sum_range_succ]

/-- **The exact closed form of an affine backward orbit.**  If `z` obeys the
one-step affine recursion `z t = B t + C t * z (t+1)` at every stage,
running it through the window `[start, start + fuel)` transports the far
end `z (start + fuel)` by the window's survival factor and adds the
window's unrolled constant term.  This is the block-value-map affinity
`Φ(z)_i = B_i + C · z_i` of the seam-price no-go, made exact and finite. -/
theorem orbit_eq_blockSurvival_mul_add_blockConstant
    (B C z : ℕ → ℝ) (hz : ∀ t, z t = B t + C t * z (t + 1)) (start fuel : ℕ) :
    z start = blockSurvival C start fuel * z (start + fuel) + blockConstant B C start fuel := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      have hnext : z (start + fuel) = B (start + fuel) + C (start + fuel) * z (start + fuel + 1) :=
        hz (start + fuel)
      rw [show start + (fuel + 1) = start + fuel + 1 by omega, ih, hnext, blockSurvival_succ,
        blockConstant_succ]
      ring

/-- The window's own fixed point `v = B / ρ`, where `ρ = 1 - blockSurvival`.
Well posed regardless of `ρ`; it is the correct affine fixed point exactly
when `ρ ≠ 0` (`blockFixedPoint_isFixedPt`). -/
def blockFixedPoint (B C : ℕ → ℝ) (start fuel : ℕ) : ℝ :=
  blockConstant B C start fuel / (1 - blockSurvival C start fuel)

/-- **The fixed-point equation.**  Whenever the window's deficit is
positive, `blockFixedPoint` really is a fixed point of the window's affine
composite. -/
theorem blockFixedPoint_isFixedPt (B C : ℕ → ℝ) (start fuel : ℕ)
    (hρ : 0 < 1 - blockSurvival C start fuel) :
    blockFixedPoint B C start fuel =
      blockSurvival C start fuel * blockFixedPoint B C start fuel +
        blockConstant B C start fuel := by
  have hne : (1 - blockSurvival C start fuel) ≠ 0 := hρ.ne'
  unfold blockFixedPoint
  field_simp
  ring

/-- **Deliverable 1, headline.**  `z (start+fuel) - v = d / ρ`, where
`d = z (start+fuel) - z start` is the boundary gap and `v` is the window's
own fixed point.  An exact identity, not an estimate. -/
theorem sub_blockFixedPoint_eq_div (B C z : ℕ → ℝ)
    (hz : ∀ t, z t = B t + C t * z (t + 1)) (start fuel : ℕ)
    (hρ : 0 < 1 - blockSurvival C start fuel) :
    z (start + fuel) - blockFixedPoint B C start fuel =
      (z (start + fuel) - z start) / (1 - blockSurvival C start fuel) := by
  have hclosed := orbit_eq_blockSurvival_mul_add_blockConstant B C z hz start fuel
  have hfix := blockFixedPoint_isFixedPt B C start fuel hρ
  rw [eq_div_iff hρ.ne']
  linear_combination hclosed - hfix

/-- **Deliverable 1, general position.**  At any interior time `t` of the
window, the orbit's deviation from the transported boundary value
`blockSurvival C t (start+fuel-t) · v + blockConstant B C t (start+fuel-t)`
is the tail survival factor times the same boundary ratio `d / ρ`:
`z_t - v_t = (∏_{u=t}^{m-1} c_u) · (d / ρ)`. -/
theorem sub_transportedFixedPoint_eq (B C z : ℕ → ℝ)
    (hz : ∀ t, z t = B t + C t * z (t + 1)) (start fuel t : ℕ)
    (_ht : start ≤ t) (ht' : t ≤ start + fuel) (hρ : 0 < 1 - blockSurvival C start fuel) :
    z t - (blockSurvival C t (start + fuel - t) * blockFixedPoint B C start fuel +
        blockConstant B C t (start + fuel - t)) =
      blockSurvival C t (start + fuel - t) *
        ((z (start + fuel) - z start) / (1 - blockSurvival C start fuel)) := by
  have hclosed := orbit_eq_blockSurvival_mul_add_blockConstant B C z hz t (start + fuel - t)
  rw [show t + (start + fuel - t) = start + fuel by omega] at hclosed
  rw [← sub_blockFixedPoint_eq_div B C z hz start fuel hρ]
  linear_combination hclosed

/-! ## Part 2: the transport factor is multiplicative, not a denominator -/

/-- **The exact telescoping decomposition of the deficit.**  The window's
total deficit is the sum, over every stage, of that stage's *own* local
deficit weighted by the prefix survival reaching it -- never a
denominator.  The finite-difference form of
`1 - ∏ x_k = Σ_k (∏_{j<k} x_j)(1 - x_k)`. -/
theorem one_sub_blockSurvival_eq_sum (C : ℕ → ℝ) (start fuel : ℕ) :
    1 - blockSurvival C start fuel =
      ∑ offset ∈ Finset.range fuel, blockSurvival C start offset * (1 - C (start + offset)) := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      rw [Finset.sum_range_succ, ← ih, blockSurvival_succ]
      ring

/-- **Deliverable 2, headline.**  Splitting a window at a prefix of length
`a` gives the exact decomposition `ρ = ρ_prefix + S(a) · ρ_block`: the
local block's contribution to the whole window's deficit is
`S(a) · ρ_block`, damped multiplicatively by the prefix survival, and
distinguished from `ρ` itself by the prefix's own loss `ρ_prefix`. -/
theorem one_sub_blockSurvival_add_eq_prefix_add_transported (C : ℕ → ℝ) (start a len : ℕ) :
    1 - blockSurvival C start (a + len) =
      (1 - blockSurvival C start a) +
        blockSurvival C start a * (1 - blockSurvival C (start + a) len) := by
  rw [blockSurvival_add]
  ring

/-- **The two differ by orders of magnitude.**  Whenever the prefix carries
any loss of its own, the local block's transported contribution
`S(a) · ρ_block` is strictly less than the whole window's deficit `ρ`. -/
theorem blockSurvival_mul_deficit_lt_total_deficit_of_prefix_pos (C : ℕ → ℝ) (start a len : ℕ)
    (hprefix_pos : 0 < 1 - blockSurvival C start a) :
    blockSurvival C start a * (1 - blockSurvival C (start + a) len) <
      1 - blockSurvival C start (a + len) := by
  rw [one_sub_blockSurvival_add_eq_prefix_add_transported]
  linarith

/-! ## Part 3: game instantiation of the value recursion -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **The value recursion is unconditionally affine at each coordinate.**
`quittingRootSuccessorPayoff` reads the continuation at coordinate `who`
only through `tail who`, with slope the *full* joint continue mass -- the
same scalar at every coordinate.  No Nash exactness is used; this is a raw
property of the Bellman map. -/
theorem quittingRootSuccessorPayoff_apply_eq_affine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward tail root who =
      quittingRootAbsorbingContribution reward root who +
        quittingStationaryContinueMass root * tail who :=
  quittingRootExpectedPayoff_eq_absorbingContribution_add reward tail root who

omit [DecidableEq ι] in
/-- **Deliverable 1, grounded (headline).**  For any sequence obeying the
raw value recursion, the residual formula `z (start+fuel) who - v = d / ρ`
holds exactly at every coordinate `who`, with `ρ` the *full* continue-mass
deficit over the window. -/
theorem quitting_sub_blockFixedPoint_eq_div
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (z : ℕ → Payoff ι)
    (hz : ∀ t, z t = quittingRootSuccessorPayoff reward (z (t + 1)) (roots t))
    (who : ι) (start fuel : ℕ)
    (hρ : 0 < 1 - blockSurvival (fun t => quittingStationaryContinueMass (roots t)) start fuel) :
    z (start + fuel) who -
        blockFixedPoint (fun t => quittingRootAbsorbingContribution reward (roots t) who)
          (fun t => quittingStationaryContinueMass (roots t)) start fuel =
      (z (start + fuel) who - z start who) /
        (1 - blockSurvival (fun t => quittingStationaryContinueMass (roots t)) start fuel) := by
  apply sub_blockFixedPoint_eq_div
    (fun t => quittingRootAbsorbingContribution reward (roots t) who)
    (fun t => quittingStationaryContinueMass (roots t)) (fun t => z t who) ?_ start fuel hρ
  intro t
  rw [congrFun (hz t) who, quittingRootSuccessorPayoff_apply_eq_affine]

omit [DecidableEq ι] in
/-- **Deliverable 1, grounded (general position).**  The same residual
formula at every interior time `t` of the window, transported by the tail
survival factor `∏_{u=t}^{m-1} c_u`. -/
theorem quitting_sub_transportedFixedPoint_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (z : ℕ → Payoff ι)
    (hz : ∀ t, z t = quittingRootSuccessorPayoff reward (z (t + 1)) (roots t))
    (who : ι) (start fuel t : ℕ) (ht : start ≤ t) (ht' : t ≤ start + fuel)
    (hρ : 0 < 1 - blockSurvival (fun s => quittingStationaryContinueMass (roots s)) start fuel) :
    z t who -
        (blockSurvival (fun s => quittingStationaryContinueMass (roots s)) t (start + fuel - t) *
            blockFixedPoint (fun s => quittingRootAbsorbingContribution reward (roots s) who)
              (fun s => quittingStationaryContinueMass (roots s)) start fuel +
          blockConstant (fun s => quittingRootAbsorbingContribution reward (roots s) who)
            (fun s => quittingStationaryContinueMass (roots s)) t (start + fuel - t)) =
      blockSurvival (fun s => quittingStationaryContinueMass (roots s)) t (start + fuel - t) *
        ((z (start + fuel) who - z start who) /
          (1 - blockSurvival (fun s => quittingStationaryContinueMass (roots s)) start fuel)) := by
  apply sub_transportedFixedPoint_eq
    (fun s => quittingRootAbsorbingContribution reward (roots s) who)
    (fun s => quittingStationaryContinueMass (roots s)) (fun s => z s who) ?_ start fuel t ht ht' hρ
  intro s
  rw [congrFun (hz s) who, quittingRootSuccessorPayoff_apply_eq_affine]

omit [DecidableEq ι] in
/-- **Deliverable 2, grounded.**  The survival-prefix's exact telescoping
decomposition: the full-window deficit splits into the prefix's own loss
plus the block's local deficit, damped by the prefix survival that reaches
it. -/
theorem quittingSurvivalPrefix_deficit_eq_prefix_add_transported
    (roots : ℕ → ι → PMF Bool) (a len : ℕ) :
    1 - quittingSurvivalPrefix roots (a + len) =
      (1 - quittingSurvivalPrefix roots a) +
        quittingSurvivalPrefix roots a *
          (1 - blockSurvival (fun t => quittingStationaryContinueMass (roots t)) a len) := by
  have heq : ∀ N, quittingSurvivalPrefix roots N =
      blockSurvival (fun t => quittingStationaryContinueMass (roots t)) 0 N := by
    intro N
    simp [quittingSurvivalPrefix, blockSurvival]
  rw [heq, heq]
  have := one_sub_blockSurvival_add_eq_prefix_add_transported
    (fun t => quittingStationaryContinueMass (roots t)) 0 a len
  simpa using this

/-! ## Part 4: no pole at zero absorption -/

omit [DecidableEq ι] in
/-- Continue mass exactly one forces the all-Continue root: each factor of
the joint product is at most one, so a product equal to one forces every
factor to be one. -/
theorem eq_quittingAllContinueRoot_of_continueMass_eq_one
    (root : ι → PMF Bool) (hmass : quittingStationaryContinueMass root = 1) :
    root = quittingAllContinueRoot := by
  funext who
  apply eq_pure_false_of_continueProbability_eq_one
  rw [quittingStationaryContinueMass_eq_prod_continueProbability] at hmass
  exact eq_one_of_prod_eq_one_of_mem (fun _ _ => ENNReal.toReal_nonneg)
    (fun player _ => ENNReal.toReal_mono ENNReal.one_ne_top
      (PMF.coe_le_one (root player) false)) hmass (Finset.mem_univ who)

omit [DecidableEq ι] in
/-- **Deliverable 4.**  Full continue mass one makes the one-step value map
the identity: absorption zero means there is no event to price, so the map
cannot alter an externally prescribed continuation. -/
theorem quittingRootSuccessorPayoff_eq_of_continueMass_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (root : ι → PMF Bool) (hmass : quittingStationaryContinueMass root = 1) :
    quittingRootSuccessorPayoff reward tail root = tail := by
  rw [eq_quittingAllContinueRoot_of_continueMass_eq_one root hmass]
  exact quittingRootSuccessorPayoff_allContinueRoot_eq reward tail

omit [DecidableEq ι] in
/-- The absorbing contribution vanishes wherever continue mass is one: with
probability one nobody quits, so the one-stage absorbed reward is exactly
zero. -/
theorem quittingRootAbsorbingContribution_eq_zero_of_continueMass_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (hmass : quittingStationaryContinueMass root = 1) (who : ι) :
    quittingRootAbsorbingContribution reward root who = 0 := by
  have h' := congrFun
    (quittingRootSuccessorPayoff_eq_of_continueMass_eq_one reward (0 : Payoff ι) root hmass) who
  unfold quittingRootAbsorbingContribution
  exact h'

omit [DecidableEq ι] in
/-- Every factor of a window's survival product is itself one whenever the
product is: continue masses lie in `[0,1]`. -/
theorem quittingStationaryContinueMass_eq_one_of_blockSurvival_eq_one
    (roots : ℕ → ι → PMF Bool) (start fuel : ℕ)
    (hρ : blockSurvival (fun t => quittingStationaryContinueMass (roots t)) start fuel = 1)
    (offset : ℕ) (hoffset : offset < fuel) :
    quittingStationaryContinueMass (roots (start + offset)) = 1 := by
  unfold blockSurvival at hρ
  exact eq_one_of_prod_eq_one_of_mem
    (fun t _ => quittingStationaryContinueMass_nonneg (roots (start + t)))
    (fun t _ => quittingStationaryContinueMass_le_one (roots (start + t)))
    hρ (Finset.mem_range.mpr hoffset)

omit [DecidableEq ι] in
/-- **Deliverable 4, windowed.**  Zero deficit over a whole window forces
every stage's absorbing contribution to zero, hence the window's unrolled
constant term to zero, hence the block value map is the literal identity:
`z start = z (start+fuel)`.  Absorption zero means there is nothing to
price, at every scale -- exact closure still exists, it simply cannot
alter an externally prescribed mismatch. -/
theorem quitting_orbit_eq_of_blockSurvival_eq_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots : ℕ → ι → PMF Bool) (z : ℕ → Payoff ι)
    (hz : ∀ t, z t = quittingRootSuccessorPayoff reward (z (t + 1)) (roots t))
    (who : ι) (start fuel : ℕ)
    (hρ : blockSurvival (fun t => quittingStationaryContinueMass (roots t)) start fuel = 1) :
    z start who = z (start + fuel) who := by
  have hclosed := orbit_eq_blockSurvival_mul_add_blockConstant
    (fun t => quittingRootAbsorbingContribution reward (roots t) who)
    (fun t => quittingStationaryContinueMass (roots t)) (fun t => z t who)
    (fun t => by rw [congrFun (hz t) who, quittingRootSuccessorPayoff_apply_eq_affine])
    start fuel
  have hBzero : blockConstant
      (fun t => quittingRootAbsorbingContribution reward (roots t) who)
      (fun t => quittingStationaryContinueMass (roots t)) start fuel = 0 := by
    unfold blockConstant
    apply Finset.sum_eq_zero
    intro offset hoffset
    have hone := quittingStationaryContinueMass_eq_one_of_blockSurvival_eq_one
      roots start fuel hρ offset (Finset.mem_range.mp hoffset)
    simp [quittingRootAbsorbingContribution_eq_zero_of_continueMass_eq_one reward _ hone who]
  rw [hclosed, hρ, hBzero]
  ring

/-! ## Part 5: the falsity witness for the deviation objective

At an isolated coordinate `who = true` -- opponents pure-continue, only
`who` may quit -- the deviation companion map collapses to
`w ↦ max {r_who({who}), w}` (`quittingRootCompanionMap_of_isolated`), with
deleted continue mass identically `1` regardless of the absorption rate
(`quittingRootDeletedContinueMass_eq_one_of_isolated`).  So the *correct*
denominator for deviation closure there, `1 - ∏ c_{-i}`, is exactly `0`.
Pricing the deviation mismatch by the *full* deficit `ρ` instead is false:
the true mismatch does not depend on `ρ` at all, while `ρ` itself is freely
tunable via the absorption rate. -/

namespace QuittingSeamPriceDeviationFalsity

/-- The witness reward: the isolated deviator `true` is paid `-1` at every
terminal coalition; `false` is paid nothing. -/
def reward : {S : Finset Bool // S.Nonempty} → Payoff Bool :=
  fun _ who ↦ if who then (-1 : ℝ) else 0

/-- The isolated hazard root at rate `p`: only `true` may quit, at rate
`p`; `false` continues surely. -/
def root (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Bool → PMF Bool :=
  quittingSoloStationaryRoot true (quittingHazardCoin p hp0 hp1)

/-- The self-consistent value at the isolated hazard root: `(0, -1)`,
indexed `(false, true)`, at every rate. -/
def value : Payoff Bool := quittingSoloReward reward true

/-- The deviator's own coordinate of the self-consistent value is `-1`. -/
@[simp] theorem value_true : value true = -1 := by
  simp [value, quittingSoloReward, reward]

/-- The non-owner coordinate is not the deviator. -/
theorem ne_owner : (false : Bool) ≠ true := by decide

/-- The root reproduces its own value at every rate. -/
theorem value_eq_successor (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    value = quittingRootSuccessorPayoff reward value (root p hp0 hp1) :=
  (quittingRootSuccessorPayoff_soloStationaryRoot_self reward true
    (quittingHazardCoin p hp0 hp1)).symm

/-- The root is exactly endpoint Nash against its own value, at every rate:
`reward` never reads the terminal coalition, so the non-owner's inequality
collapses to `0 ≤ 0`. -/
theorem isEndpointNash (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsεQuittingRootEndpointNash reward value 0 (root p hp0 hp1) := by
  refine isεQuittingRootEndpointNash_soloStationaryRoot reward true
    (quittingHazardCoin p hp0 hp1) ?_
  intro other hother
  cases other with
  | false => norm_num [quittingSoloReward, quittingSingletonCollisionReward, reward]
  | true => exact absurd rfl hother

/-- Every coordinate of the value is within the canonical reward bound. -/
theorem abs_value_le : ∀ who, |value who| ≤ quittingRewardBound reward :=
  fun who ↦ abs_reward_le_quittingRewardBound reward (quittingSingletonTerminal true) who

/-- The root absorbs at exactly rate `p`. -/
theorem absorptionMass_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    quittingRootAbsorptionMass (root p hp0 hp1) = p := by
  rw [root, quittingRootAbsorptionMass_soloStationaryRoot, quittingHazardCoin_true_toReal]

/-- **The period-one cyclic continuation block, at every strictly positive
rate.** -/
theorem isCyclicContinuationBlock (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    IsQuittingCyclicContinuationBlock reward value 1 (quittingRowBlock value (root p hp0.le hp1)) :=
  quittingRowBlock_isQuittingCyclicContinuationBlock reward value (root p hp0.le hp1)
    abs_value_le (value_eq_successor p hp0.le hp1) (isEndpointNash p hp0.le hp1)
    (by rw [absorptionMass_eq]; exact hp0)

/-- The block's operational root at time zero is the witness root. -/
theorem pathRoots_zero_eq (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    quittingFiniteNashBellmanPathRoots 1 (quittingRowBlock value (root p hp0.le hp1)) 0 =
      root p hp0.le hp1 := by
  rw [quittingFiniteNashBellmanPathRoots_of_lt 1 _ 0 Nat.one_pos,
    quittingRootOfSimplex_quittingRowBlock]

/-- The block is isolated at `true`: `false` never quits, at every rate. -/
theorem isIsolatedWindow (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    IsQuittingIsolatedWindow
      (quittingFiniteNashBellmanPathRoots 1 (quittingRowBlock value (root p hp0.le hp1)))
      true 1 := by
  intro time htime
  have htime0 : time = 0 := by omega
  subst htime0
  rw [pathRoots_zero_eq p hp0 hp1]
  intro other hother
  cases other with
  | false => rw [root, quittingSoloStationaryRoot_apply_other ne_owner]
  | true => exact absurd rfl hother

/-- **The isolated deviation mismatch is exactly `1`, at every strictly
positive rate `p`.**  The witness reward has `r_true({true}) = -1`, so the
mismatch `max {0, -r_true({true})}` is a fixed constant, independent of the
rate that controls the full deficit. -/
theorem mismatch_eq_one (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    quittingPositiveSingletonDebtCap reward true - value true = 1 := by
  have hmismatch := quittingCyclicContinuationBlock_mismatch_eq_of_isolated reward value 1
    (quittingRowBlock value (root p hp0.le hp1)) (isCyclicContinuationBlock p hp0 hp1)
    (isIsolatedWindow p hp0 hp1) (quittingPositiveSingletonDebtCap reward true)
    (tendsto_iterate_soloQuitAnchor_of_isolated reward
      (quittingFiniteNashBellmanPathRoots 1 (quittingRowBlock value (root p hp0.le hp1))) true 1
      (isIsolatedWindow p hp0 hp1))
  rw [hmismatch]
  norm_num [quittingSingletonTerminal, reward]

/-- The deleted (opponents-only) deficit is exactly `0` at every rate: this
is the correct denominator for deviation closure at an isolated
coordinate. -/
theorem deletedDeficit_eq_zero (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    1 - quittingRootDeletedContinueMass (root p hp0.le hp1) true = 0 := by
  have hiso : IsQuittingIsolatedRoot (root p hp0.le hp1) true := by
    have h := isIsolatedWindow p hp0 hp1 0 Nat.one_pos
    rwa [pathRoots_zero_eq p hp0 hp1] at h
  rw [quittingRootDeletedContinueMass_eq_one_of_isolated hiso]
  ring

/-- **Deliverable 3, the machine-checked no-go.**  No single `δ` prices the
isolated deviation mismatch as `δ / ρ_full` across two different rates:
halving the rate from `p = 1/2` to `p = 1/3` changes the full deficit from
`1/2` to `1/3`, yet the mismatch stays fixed at the constant `1`.  This
refutes transplanting the exact value-recursion law (deliverable 1) onto
the deviation objective with the *full* deficit in place of the *deleted*
one, which is what the deviation companion map's own slope actually is
(`deletedDeficit_eq_zero`: exactly `0` here, not `ρ_full`). -/
theorem seamPriceLaw_fails_for_deviation_via_fullDeficit :
    ¬ ∃ δ : ℝ,
      quittingPositiveSingletonDebtCap reward true - value true =
        δ / quittingRootAbsorptionMass (root (1 / 2) (by norm_num) (by norm_num)) ∧
      quittingPositiveSingletonDebtCap reward true - value true =
        δ / quittingRootAbsorptionMass (root (1 / 3) (by norm_num) (by norm_num)) := by
  rintro ⟨δ, h1, h2⟩
  rw [mismatch_eq_one (1 / 2) (by norm_num) (by norm_num)] at h1
  rw [mismatch_eq_one (1 / 3) (by norm_num) (by norm_num)] at h2
  rw [absorptionMass_eq] at h1 h2
  norm_num at h1 h2
  linarith

end QuittingSeamPriceDeviationFalsity

end GameTheory
