/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Analytic.SeamPriceResidual
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Cycles.Isolated.AnchorMaxAffine

/-!
# Transported leverage: the corrected surgery currency

This development replaces the refuted `δ / ρ` seam-price law — the reading
that a re-closing's cost is priced by absorbed mass, in the tradition of the
cyclic-repair estimates of R. S. Simon, *The structure of non-zero-sum
stochastic games*, Adv. Appl. Math. 38 (2007), Lemma 4 — with a constructive
currency: what controls a local block modification `B` inside an array `G`
is not absorbed mass but **transported leverage** -- the modification's
effect on the block map, amplified by the contraction deficit of the return
map being re-closed.

This file names both leverage quantities as definitions over objects already
in the repository, proves the coarse absorption bound and the exact
re-closing identity for the value channel, states and proves the corrected
obstruction, exhibits the incomparability of "leverage" and "support size",
and records where the deviation channel's leverage is undefined.

## Verification against the repository's own objects

Every quantity the source names already has a home:

* `C_P`, the prefix transport factor, is `blockSurvival` of
  `QuittingSeamPriceResidual.lean` restricted to the prefix window;
* `ρ̃_G`, the post-modification full deficit, is `1 - blockSurvival` over the
  whole (modified) cycle;
* `Q_{P,i}`, the deviation prefix transport factor, is
  `quittingOpponentSurvivalWeight` of `QuittingCycleMismatchContraction.lean`
  restricted to the prefix;
* `1 - Q̃_{G,i}`, the deleted deficit, is `1 - quittingOpponentSurvivalWeight`
  over the whole (modified) cycle;
* the block deviation operator `H_{t,i}(w) = max {Σ_i, A_i + c_{-i} w}` is
  *exactly* `quittingRootCompanionMap`, and its multi-stage composite is
  *exactly* `quittingCompanionComposite` -- no new machinery is built for
  either.

No quantity had to be introduced that is not already one of these repository
objects; the abstract value-channel machinery (`blockValueMap`,
`blockConstant_add`) is new *composition algebra* over the existing
`blockSurvival` / `blockConstant` primitives, not a new modeling choice.

## Main definitions

* `blockValueMap` -- the block value map `Φ_B(z) = blockConstant + blockSurvival · z`,
  literally the transport law of `orbit_eq_blockSurvival_mul_add_blockConstant`
  read as a function of the boundary value.
* `valueLeverage` -- `L^val(B;G)`, deliverable (1), value channel.
* `quittingRootSystem` / `quittingRootCompanionMap_eq_quittingRootSystem_Φ` --
  the **crucial reuse**: the block deviation operator is the abstract
  max-affine system of `Math.MaxAffineStoppingValue`, at *every* root, not
  only isolated ones.
* `deviationLeverage` -- `L^dev_i(B;G)`, deliverable (1), deviation channel.

## Main results

* `valueLeverage_eq_mul_add_abs` -- the leverage's `sSup` definition agrees
  with its closed form, verifying (29).
* `valueLeverage_le_coarse_absorption_bound` -- deliverable (2), the coarse
  bound `L^val ≤ 2 C_P (ρ_B + ρ̃_B) / ρ̃_G`, reproducing (30).
* `sub_blockFixedPoint_eq_transportedLeverageTerm` -- the exact re-closing
  identity `ṽ - v = (C_P / ρ̃_G)(Φ̃_B(z) - Φ_B(z))`, reproducing (26), derived
  from the composition law `blockValueMap_add` and the existing
  `blockFixedPoint_isFixedPt` -- not re-imported as a hypothesis.
* `not_eventually_ge_of_tendsto_leverage_zero` -- deliverable (3), the
  corrected obstruction stated generically, directly usable as a no-go.
* `valueLeverage_smallSupport_eq_one` /
  `tendsto_valueLeverage_largeSupport_atTop_nhds_zero` -- deliverable (4),
  the incomparability witnesses.
* `one_sub_quittingOpponentSurvivalWeight_eq_zero_iff_isQuittingIsolatedWindow`
  -- the honesty finding: the deviation leverage's denominator vanishes
  *exactly* at the isolated configuration, the same `P = 1` regime fenced in
  `Math.MaxAffineStoppingValue`.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.MaxAffineStopping

/-! ## Part 0: the block deviation operator is the max-affine system

`quittingRootCompanionMap` is *already* `max {A, T + P·w}` with
`A = Σ_who`, `T = A_who`, `P = c_{-who}` -- this is definitional, and no
isolation hypothesis is needed to see it.  `QuittingIsolatedAnchorMaxAffine.lean`
only records the special case `P = 1`; the general bridge below is the
"crucial reuse" the dispatch asks for. -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The general max-affine system attached to a root at `who`.**  Stop
payoff the fixed-opponents quit value `Σ_who`, stage reward the
fixed-opponents continue reward `A_who`, survival the fixed-opponents
(deleted) continue mass `c_{-who}`.  No isolation hypothesis: `P` need not be
`1`. -/
def quittingRootSystem
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (root : ι → PMF Bool) (who : ι) : System where
  A := quittingRootDeletedQuitValue reward root who
  T := quittingRootDeletedContinueReward reward root who
  P := quittingRootDeletedContinueMass root who
  P_nonneg := quittingRootDeletedContinueMass_nonneg root who
  P_le_one := quittingRootDeletedContinueMass_le_one root who

/-- **Crucial reuse.**  The companion map -- the source's block deviation
operator `H_{t,who}` -- is *exactly* the abstract max-affine operator `Φ` of
`Math.MaxAffineStoppingValue`, at every root: no isolation needed, and no
rebuilding of the max-affine machinery. -/
theorem quittingRootCompanionMap_eq_quittingRootSystem_Φ
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootCompanionMap reward root who = (quittingRootSystem reward root who).Φ := by
  funext w
  rfl

/-! ## Part 1: the value channel -- the block value map -/

/-- **The block value map** `Φ_B(z) = blockConstant B C start fuel + blockSurvival C start
fuel · z`: transporting a boundary value `z` through the window `[start, start + fuel)`
under the affine recursion `w ↦ B t + C t · w`.  Exactly the right-hand side of
`orbit_eq_blockSurvival_mul_add_blockConstant`, read as a function of the far
end value. -/
def blockValueMap (B C : ℕ → ℝ) (start fuel : ℕ) (z : ℝ) : ℝ :=
  blockConstant B C start fuel + blockSurvival C start fuel * z

/-- `blockValueMap` really does transport the orbit: this is
`orbit_eq_blockSurvival_mul_add_blockConstant` restated as a `blockValueMap`
application. -/
theorem orbit_eq_blockValueMap
    (B C z : ℕ → ℝ) (hz : ∀ t, z t = B t + C t * z (t + 1)) (start fuel : ℕ) :
    z start = blockValueMap B C start fuel (z (start + fuel)) := by
  unfold blockValueMap
  rw [orbit_eq_blockSurvival_mul_add_blockConstant B C z hz start fuel]
  ring

/-- **Composition law for `blockConstant`.**  Splitting a window at a prefix
of length `a` decomposes the constant term the same way the survival factor
decomposes in `blockSurvival_add`: the block's own constant, plus the
prefix-transported constant of the rest. -/
theorem blockConstant_add (B C : ℕ → ℝ) (start a b : ℕ) :
    blockConstant B C start (a + b) =
      blockConstant B C start a +
        blockSurvival C start a * blockConstant B C (start + a) b := by
  induction b with
  | zero => simp
  | succ b ih =>
      have h1 : a + (b + 1) = a + b + 1 := by omega
      have h2 : start + (a + b) = start + a + b := by omega
      rw [h1, blockConstant_succ, ih, blockSurvival_add, h2]
      have h3 : blockConstant B C (start + a) (b + 1) =
          blockConstant B C (start + a) b + blockSurvival C (start + a) b * B (start + a + b) := by
        rw [blockConstant_succ]
      rw [h3]
      ring

/-- **Composition law for `blockValueMap`.**  Transporting through a window
of length `a + b` is transporting through the first `a` stages of the
transport through the last `b`: `Φ_{P;B} = Φ_P ∘ Φ_B`.  This is the algebraic
heart of the `G = PBR` decomposition (25)-(26): no game structure is used,
only that affine maps compose. -/
theorem blockValueMap_add (B C : ℕ → ℝ) (start a b : ℕ) (z : ℝ) :
    blockValueMap B C start (a + b) z =
      blockValueMap B C start a (blockValueMap B C (start + a) b z) := by
  unfold blockValueMap
  rw [blockConstant_add, blockSurvival_add]
  ring

/-- **Three-way composition, `Φ_G = Φ_P ∘ Φ_B ∘ Φ_R`.**  The window
`[0, p + ℓ + r)`, split into prefix (`p`), block (`ℓ`) and rest (`r`),
transports a boundary value by composing the three sub-window maps in order.
Specialized from `blockValueMap_add` at `start = 0` so the `G = PBR`
decomposition never has to fight `Nat` associativity by hand. -/
theorem blockValueMap_add3 (B C : ℕ → ℝ) (p ℓ r : ℕ) (z : ℝ) :
    blockValueMap B C 0 (p + ℓ + r) z =
      blockValueMap B C 0 p (blockValueMap B C p ℓ (blockValueMap B C (p + ℓ) r z)) := by
  have h1 := blockValueMap_add B C 0 (p + ℓ) r z
  rw [Nat.zero_add] at h1
  have h2 := blockValueMap_add B C 0 p ℓ (blockValueMap B C (p + ℓ) r z)
  rw [Nat.zero_add] at h2
  rw [h1, h2]

/-- Agreement of the coefficients on a window forces agreement of
`blockSurvival` there. -/
theorem blockSurvival_congr {C C' : ℕ → ℝ} {start fuel : ℕ}
    (hC : ∀ offset, offset < fuel → C' (start + offset) = C (start + offset)) :
    blockSurvival C' start fuel = blockSurvival C start fuel := by
  unfold blockSurvival
  exact Finset.prod_congr rfl fun offset hoffset => hC offset (Finset.mem_range.mp hoffset)

/-- Agreement of the coefficients on a window forces agreement of
`blockConstant` there. -/
theorem blockConstant_congr {B C B' C' : ℕ → ℝ} {start fuel : ℕ}
    (hB : ∀ offset, offset < fuel → B' (start + offset) = B (start + offset))
    (hC : ∀ offset, offset < fuel → C' (start + offset) = C (start + offset)) :
    blockConstant B' C' start fuel = blockConstant B C start fuel := by
  unfold blockConstant
  refine Finset.sum_congr rfl fun offset hoffset => ?_
  have hoffset' := Finset.mem_range.mp hoffset
  rw [hB offset hoffset', blockSurvival_congr (start := start) (fuel := offset)
    (fun o ho => hC o (by omega))]

/-- Agreement of the coefficients on a window forces agreement of the whole
`blockValueMap`. -/
theorem blockValueMap_congr {B C B' C' : ℕ → ℝ} {start fuel : ℕ}
    (hB : ∀ offset, offset < fuel → B' (start + offset) = B (start + offset))
    (hC : ∀ offset, offset < fuel → C' (start + offset) = C (start + offset)) (z : ℝ) :
    blockValueMap B' C' start fuel z = blockValueMap B C start fuel z := by
  unfold blockValueMap
  rw [blockConstant_congr hB hC, blockSurvival_congr hC]

/-! ### The exact sup formula and the named leverage quantity -/

/-- **The exact supremum of an affine function over `[-1, 1]`.**  Attained at
one of the two endpoints, matching the classical identity
`max {|c + d|, |c - d|} = |c| + |d|`. -/
theorem isGreatest_abs_add_mul_image_Icc (c d : ℝ) :
    IsGreatest ((fun z => |c + d * z|) '' Set.Icc (-1 : ℝ) 1) (|c| + |d|) := by
  constructor
  · rcases le_total 0 c with hc | hc <;> rcases le_total 0 d with hd | hd
    · exact ⟨1, by norm_num, by
        change |c + d * 1| = |c| + |d|
        rw [abs_of_nonneg hc, abs_of_nonneg hd, abs_of_nonneg (by linarith : (0:ℝ) ≤ c + d * 1)]
        ring⟩
    · exact ⟨-1, by norm_num, by
        change |c + d * (-1)| = |c| + |d|
        rw [abs_of_nonneg hc, abs_of_nonpos hd,
          abs_of_nonneg (by linarith : (0:ℝ) ≤ c + d * (-1))]
        ring⟩
    · exact ⟨-1, by norm_num, by
        change |c + d * (-1)| = |c| + |d|
        rw [abs_of_nonpos hc, abs_of_nonneg hd,
          abs_of_nonpos (by linarith : c + d * (-1) ≤ (0:ℝ))]
        ring⟩
    · exact ⟨1, by norm_num, by
        change |c + d * 1| = |c| + |d|
        rw [abs_of_nonpos hc, abs_of_nonpos hd, abs_of_nonpos (by linarith : c + d * 1 ≤ (0:ℝ))]
        ring⟩
  · rintro x ⟨z, hz, rfl⟩
    rw [Set.mem_Icc] at hz
    calc |c + d * z| ≤ |c| + |d * z| := abs_add_le c (d * z)
      _ = |c| + |d| * |z| := by rw [abs_mul]
      _ ≤ |c| + |d| * 1 := by
          gcongr
          exact abs_le.mpr hz
      _ = |c| + |d| := by ring

/-- The image set of the block-value-map discrepancy over `[-1, 1]` is
exactly the affine image set of the exact sup formula, so its greatest
element is the closed form `|ΔB| + |ΔC|`. -/
theorem isGreatest_abs_blockValueMap_sub_image (B C B' C' : ℕ → ℝ) (start fuel : ℕ) :
    IsGreatest
      ((fun z => |blockValueMap B' C' start fuel z - blockValueMap B C start fuel z|) ''
        Set.Icc (-1 : ℝ) 1)
      (|blockConstant B' C' start fuel - blockConstant B C start fuel| +
        |blockSurvival C' start fuel - blockSurvival C start fuel|) := by
  have hfun : (fun z => |blockValueMap B' C' start fuel z - blockValueMap B C start fuel z|) =
      (fun z => |(blockConstant B' C' start fuel - blockConstant B C start fuel) +
        (blockSurvival C' start fuel - blockSurvival C start fuel) * z|) := by
    funext z
    unfold blockValueMap
    ring_nf
  rw [hfun]
  exact isGreatest_abs_add_mul_image_Icc _ _

/-- **The value-channel transported leverage**, `L^val(B;G)`, deliverable
(1).  The prefix transport factor `C_P`, divided by the post-modification
**whole-window** deficit `ρ̃_G` -- a quantity of the enclosing array `G`, and
in general *not* the block `B`'s own deficit `1 - blockSurvival C' start
fuel`, whenever `B` is nested inside a strictly larger `G = PBR` (the
distinction the source insists on in `A2`) -- times the supremum over `z ∈
[-1, 1]` of the discrepancy between the new and old block value maps over
`B`'s own window `[start, start + fuel)` -- literally formula (29). -/
def valueLeverage (C_P rhoTildeG : ℝ) (B C B' C' : ℕ → ℝ) (start fuel : ℕ) : ℝ :=
  (C_P / rhoTildeG) *
    sSup ((fun z => |blockValueMap B' C' start fuel z - blockValueMap B C start fuel z|) ''
      Set.Icc (-1 : ℝ) 1)

/-- `valueLeverage`'s `sSup` agrees with the closed form: the value channel's
leverage is `(C_P / ρ̃_G) · (|ΔB| + |ΔC|)`. -/
theorem valueLeverage_eq_mul_add_abs (C_P rhoTildeG : ℝ) (B C B' C' : ℕ → ℝ) (start fuel : ℕ) :
    valueLeverage C_P rhoTildeG B C B' C' start fuel =
      (C_P / rhoTildeG) *
        (|blockConstant B' C' start fuel - blockConstant B C start fuel| +
          |blockSurvival C' start fuel - blockSurvival C start fuel|) := by
  unfold valueLeverage
  rw [(isGreatest_abs_blockValueMap_sub_image B C B' C' start fuel).csSup_eq]

/-! ## Part 2: the coarse absorption bound, deliverable (2) -/

/-- **The affine coefficients are bounded by the deficit they generate.**
The row bound `|B t| ≤ 1 - C t` at every stage of the window -- inequality
(4) of the source, itself a property of the reward/probability data -- forces
`|blockConstant| ≤ ρ_B` over the whole window, by the same telescoping
argument as `one_sub_blockSurvival_eq_sum`. -/
theorem abs_blockConstant_le_one_sub_blockSurvival (B C : ℕ → ℝ) (start fuel : ℕ)
    (hrow : ∀ offset, offset < fuel → |B (start + offset)| ≤ 1 - C (start + offset))
    (hCnonneg : ∀ offset, offset < fuel → 0 ≤ C (start + offset)) :
    |blockConstant B C start fuel| ≤ 1 - blockSurvival C start fuel := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
      have hSnonneg : 0 ≤ blockSurvival C start fuel := by
        unfold blockSurvival
        refine Finset.prod_nonneg fun offset hoffset => hCnonneg offset ?_
        have := Finset.mem_range.mp hoffset
        omega
      have ihs := ih (fun o ho => hrow o (by omega)) (fun o ho => hCnonneg o (by omega))
      rw [blockConstant_succ, blockSurvival_succ]
      calc |blockConstant B C start fuel + blockSurvival C start fuel * B (start + fuel)|
          ≤ |blockConstant B C start fuel| +
              |blockSurvival C start fuel * B (start + fuel)| := abs_add_le _ _
        _ = |blockConstant B C start fuel| +
              blockSurvival C start fuel * |B (start + fuel)| := by
              rw [abs_mul, abs_of_nonneg hSnonneg]
        _ ≤ (1 - blockSurvival C start fuel) +
              blockSurvival C start fuel * (1 - C (start + fuel)) := by
              gcongr
              exact hrow fuel (by omega)
        _ = 1 - blockSurvival C start fuel * C (start + fuel) := by ring

/-- The block-survival deficit of a window with pointwise-`[0,1]` coefficients
is itself in `[0, 1]`. -/
theorem blockSurvival_le_one (C : ℕ → ℝ) (start fuel : ℕ)
    (hC0 : ∀ offset, offset < fuel → 0 ≤ C (start + offset))
    (hC1 : ∀ offset, offset < fuel → C (start + offset) ≤ 1) :
    blockSurvival C start fuel ≤ 1 := by
  unfold blockSurvival
  refine Finset.prod_le_one (fun offset hoffset => hC0 offset (Finset.mem_range.mp hoffset))
    (fun offset hoffset => hC1 offset (Finset.mem_range.mp hoffset))

/-- **The coarse absorption bound, deliverable (2).**  `L^val ≤ 2 C_P (ρ_B +
ρ̃_B) / ρ̃_G`, reproducing (30): the leverage is controlled coarsely by the
old and new block's own absorption, at the cost of factor `2` and losing the
sign cancellation the exact `sSup` formula keeps. -/
theorem valueLeverage_le_coarse_absorption_bound
    (C_P rhoTildeG : ℝ) (B C B' C' : ℕ → ℝ) (start fuel : ℕ)
    (hCP : 0 ≤ C_P) (hRhoTildeG : 0 < rhoTildeG)
    (hrow : ∀ offset, offset < fuel → |B (start + offset)| ≤ 1 - C (start + offset))
    (hrow' : ∀ offset, offset < fuel → |B' (start + offset)| ≤ 1 - C' (start + offset))
    (hC0 : ∀ offset, offset < fuel → 0 ≤ C (start + offset))
    (hC0' : ∀ offset, offset < fuel → 0 ≤ C' (start + offset))
    (hC1 : ∀ offset, offset < fuel → C (start + offset) ≤ 1)
    (hC1' : ∀ offset, offset < fuel → C' (start + offset) ≤ 1) :
    valueLeverage C_P rhoTildeG B C B' C' start fuel ≤
      2 * C_P * ((1 - blockSurvival C start fuel) + (1 - blockSurvival C' start fuel)) /
        rhoTildeG := by
  rw [valueLeverage_eq_mul_add_abs, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hRhoTildeG]
  have hB := abs_blockConstant_le_one_sub_blockSurvival B C start fuel hrow hC0
  have hB' := abs_blockConstant_le_one_sub_blockSurvival B' C' start fuel hrow' hC0'
  have hSle : blockSurvival C start fuel ≤ 1 := blockSurvival_le_one C start fuel hC0 hC1
  have hSle' : blockSurvival C' start fuel ≤ 1 := blockSurvival_le_one C' start fuel hC0' hC1'
  have hΔB : |blockConstant B' C' start fuel - blockConstant B C start fuel| ≤
      (1 - blockSurvival C start fuel) + (1 - blockSurvival C' start fuel) :=
    (abs_sub _ _).trans (by linarith)
  have hΔC : |blockSurvival C' start fuel - blockSurvival C start fuel| ≤
      (1 - blockSurvival C start fuel) + (1 - blockSurvival C' start fuel) := by
    rw [abs_le]; constructor <;> linarith
  nlinarith [hCP, hΔB, hΔC]

/-! ## Part 3: the exact re-closing identity and the corrected obstruction -/

/-- **The exact re-closing identity, deliverable (3)'s bridge, reproducing
(26).**  Splitting the whole window `[0, p + ℓ + r)` into prefix `[0, p)`,
block `[p, p + ℓ)` and rest `[p + ℓ, p + ℓ + r)`, with the modification
confined to the block (prefix and rest coefficients agree), the movement of
the whole window's own fixed point is the prefix transport factor over the
post-modification whole-window deficit, times the block map's discrepancy at
`z = Φ_R(v)`.  Derived entirely from `blockValueMap_add`,
`blockValueMap_congr` and `blockFixedPoint_isFixedPt` -- no new hypothesis
beyond the source's own `G = PBR` decomposition. -/
theorem sub_blockFixedPoint_eq_transportedLeverageTerm
    (B C B' C' : ℕ → ℝ) (p ℓ r : ℕ)
    (hBeqP : ∀ offset, offset < p → B' offset = B offset)
    (hCeqP : ∀ offset, offset < p → C' offset = C offset)
    (hBeqR : ∀ offset, offset < r → B' (p + ℓ + offset) = B (p + ℓ + offset))
    (hCeqR : ∀ offset, offset < r → C' (p + ℓ + offset) = C (p + ℓ + offset))
    (hρG : 0 < 1 - blockSurvival C 0 (p + ℓ + r))
    (hρG' : 0 < 1 - blockSurvival C' 0 (p + ℓ + r)) :
    blockFixedPoint B' C' 0 (p + ℓ + r) - blockFixedPoint B C 0 (p + ℓ + r) =
      (blockSurvival C 0 p / (1 - blockSurvival C' 0 (p + ℓ + r))) *
        (blockValueMap B' C' p ℓ
            (blockValueMap B C (p + ℓ) r (blockFixedPoint B C 0 (p + ℓ + r))) -
          blockValueMap B C p ℓ
            (blockValueMap B C (p + ℓ) r (blockFixedPoint B C 0 (p + ℓ + r)))) := by
  set v := blockFixedPoint B C 0 (p + ℓ + r) with hv
  set v' := blockFixedPoint B' C' 0 (p + ℓ + r) with hv'
  set z := blockValueMap B C (p + ℓ) r v with hz
  -- The old fixed point decomposes through the P;B;R window.
  have hvFix : v = blockValueMap B C 0 (p + ℓ + r) v := by
    have h := blockFixedPoint_isFixedPt B C 0 (p + ℓ + r) hρG
    rw [← hv] at h
    rw [show blockValueMap B C 0 (p + ℓ + r) v =
        blockSurvival C 0 (p + ℓ + r) * v + blockConstant B C 0 (p + ℓ + r) from by
      unfold blockValueMap; ring]
    exact h
  have hvP : v = blockValueMap B C 0 p (blockValueMap B C p ℓ z) := by
    conv_lhs => rw [hvFix, blockValueMap_add3]
  -- The new full map applied to the *old* fixed point.
  have hv'Fix : v' = blockValueMap B' C' 0 (p + ℓ + r) v' := by
    have h := blockFixedPoint_isFixedPt B' C' 0 (p + ℓ + r) hρG'
    rw [← hv'] at h
    rw [show blockValueMap B' C' 0 (p + ℓ + r) v' =
        blockSurvival C' 0 (p + ℓ + r) * v' + blockConstant B' C' 0 (p + ℓ + r) from by
      unfold blockValueMap; ring]
    exact h
  have hBeqP0 : ∀ offset, offset < p → B' (0 + offset) = B (0 + offset) := by
    intro o ho; simpa using hBeqP o ho
  have hCeqP0 : ∀ offset, offset < p → C' (0 + offset) = C (0 + offset) := by
    intro o ho; simpa using hCeqP o ho
  have hnewAtOld : blockValueMap B' C' 0 (p + ℓ + r) v =
      blockValueMap B C 0 p (blockValueMap B' C' p ℓ z) := by
    rw [blockValueMap_add3,
      blockValueMap_congr (start := p + ℓ) (fuel := r) hBeqR hCeqR, ← hz,
      blockValueMap_congr (start := 0) (fuel := p) hBeqP0 hCeqP0]
  have hPaffine : ∀ w₁ w₂ : ℝ,
      blockValueMap B C 0 p w₁ - blockValueMap B C 0 p w₂ = blockSurvival C 0 p * (w₁ - w₂) := by
    intro w₁ w₂; unfold blockValueMap; ring
  have hd : blockValueMap B' C' 0 (p + ℓ + r) v - v =
      blockSurvival C 0 p * (blockValueMap B' C' p ℓ z - blockValueMap B C p ℓ z) := by
    rw [hnewAtOld, hvP]
    exact hPaffine _ _
  -- Re-close: both fixed points solve the same affine equation over `[0, p+ℓ+r)`.
  have hEqOld : blockConstant B C 0 (p + ℓ + r) = v * (1 - blockSurvival C 0 (p + ℓ + r)) := by
    have h := hvFix
    rw [show blockValueMap B C 0 (p + ℓ + r) v =
        blockConstant B C 0 (p + ℓ + r) + blockSurvival C 0 (p + ℓ + r) * v from rfl] at h
    linear_combination -h
  have hEqNew : blockConstant B' C' 0 (p + ℓ + r) = v' * (1 - blockSurvival C' 0 (p + ℓ + r)) := by
    have h := hv'Fix
    rw [show blockValueMap B' C' 0 (p + ℓ + r) v' =
        blockConstant B' C' 0 (p + ℓ + r) + blockSurvival C' 0 (p + ℓ + r) * v' from rfl] at h
    linear_combination -h
  have hdUnfold : blockConstant B' C' 0 (p + ℓ + r) +
      blockSurvival C' 0 (p + ℓ + r) * v - v =
      blockSurvival C 0 p * (blockValueMap B' C' p ℓ z - blockValueMap B C p ℓ z) := by
    rw [show blockConstant B' C' 0 (p + ℓ + r) + blockSurvival C' 0 (p + ℓ + r) * v =
        blockValueMap B' C' 0 (p + ℓ + r) v from rfl]
    exact hd
  rw [hEqNew] at hdUnfold
  have hfinal : (v' - v) * (1 - blockSurvival C' 0 (p + ℓ + r)) =
      blockSurvival C 0 p * (blockValueMap B' C' p ℓ z - blockValueMap B C p ℓ z) := by
    linear_combination hdUnfold
  rw [div_mul_eq_mul_div, eq_div_iff hρG'.ne']
  exact hfinal

/-- **The corrected obstruction, deliverable (3), generic form.**  A family
of modifications whose transported leverage tends to zero cannot change the
origin objective by a fixed positive amount: if the change at index `n` is
dominated by a leverage that tends to `0`, the change cannot stay `≥ c` for
any fixed `c > 0`, eventually.  Stated with no reference to the game so it is
directly usable as a no-go against *any* leverage bound of this shape. -/
theorem not_eventually_ge_of_tendsto_leverage_zero
    {leverage change : ℕ → ℝ} (hbound : ∀ n, |change n| ≤ leverage n)
    (hL : Filter.Tendsto leverage Filter.atTop (nhds 0)) {c : ℝ} (hc : 0 < c) :
    ¬ ∀ᶠ n in Filter.atTop, c ≤ |change n| := by
  intro hev
  have hlt : ∀ᶠ n in Filter.atTop, leverage n < c := (tendsto_order.mp hL).2 c hc
  have hboth : ∀ᶠ n in Filter.atTop, c ≤ |change n| ∧ leverage n < c := hev.and hlt
  obtain ⟨n, hn1, hn2⟩ := hboth.exists
  exact absurd (hn1.trans (hbound n)) (not_le.mpr hn2)

/-- **The obstruction, connected to the value channel.**  For a family of
`G = PBR` decompositions satisfying the re-closing hypotheses at every index,
if the value-channel leverage tends to `0`, the induced movement of the
window's own fixed point -- the origin objective, in the source's language --
cannot stay `≥ c` for any fixed `c > 0`, eventually. Combines
`sub_blockFixedPoint_eq_transportedLeverageTerm` with
`not_eventually_ge_of_tendsto_leverage_zero`. -/
theorem not_eventually_ge_of_tendsto_valueLeverage_zero
    {B C B' C' : ℕ → ℕ → ℝ} {p ℓ r : ℕ → ℕ}
    (hBeqP : ∀ n offset, offset < p n → B' n offset = B n offset)
    (hCeqP : ∀ n offset, offset < p n → C' n offset = C n offset)
    (hBeqR : ∀ n offset, offset < r n →
      B' n (p n + ℓ n + offset) = B n (p n + ℓ n + offset))
    (hCeqR : ∀ n offset, offset < r n →
      C' n (p n + ℓ n + offset) = C n (p n + ℓ n + offset))
    (hρG : ∀ n, 0 < 1 - blockSurvival (C n) 0 (p n + ℓ n + r n))
    (hρG' : ∀ n, 0 < 1 - blockSurvival (C' n) 0 (p n + ℓ n + r n))
    (hCPnn : ∀ n, 0 ≤ blockSurvival (C n) 0 (p n))
    (hz1 : ∀ n, |blockValueMap (B n) (C n) (p n + ℓ n) (r n)
        (blockFixedPoint (B n) (C n) 0 (p n + ℓ n + r n))| ≤ 1)
    (hL : Filter.Tendsto
      (fun n => valueLeverage (blockSurvival (C n) 0 (p n))
        (1 - blockSurvival (C' n) 0 (p n + ℓ n + r n)) (B n) (C n) (B' n) (C' n) (p n) (ℓ n))
      Filter.atTop (nhds 0))
    {c : ℝ} (hc : 0 < c) :
    ¬ ∀ᶠ n in Filter.atTop,
        c ≤ |blockFixedPoint (B' n) (C' n) 0 (p n + ℓ n + r n) -
              blockFixedPoint (B n) (C n) 0 (p n + ℓ n + r n)| := by
  refine not_eventually_ge_of_tendsto_leverage_zero (fun n => ?_) hL hc
  rw [sub_blockFixedPoint_eq_transportedLeverageTerm (B n) (C n) (B' n) (C' n) (p n) (ℓ n) (r n)
    (hBeqP n) (hCeqP n) (hBeqR n) (hCeqR n) (hρG n) (hρG' n),
    valueLeverage_eq_mul_add_abs, abs_mul,
    abs_of_nonneg (div_nonneg (hCPnn n) (hρG' n).le)]
  exact mul_le_mul_of_nonneg_left
    ((isGreatest_abs_blockValueMap_sub_image (B n) (C n) (B' n) (C' n) (p n) (ℓ n)).2
      ⟨blockValueMap (B n) (C n) (p n + ℓ n) (r n)
          (blockFixedPoint (B n) (C n) 0 (p n + ℓ n + r n)),
        Set.mem_Icc.mpr (abs_le.mp (hz1 n)), rfl⟩)
    (div_nonneg (hCPnn n) (hρG' n).le)

/-! ## Part 4: incomparability -- deliverable (4)

Bounded support and vanishing leverage are incomparable conditions.  A
support of size `1` can already carry leverage `1` (order-one); a support of
size `n → ∞` can carry leverage `(1/2)^n → 0`. -/

/-- **Small support, order-one leverage.**  A single stage (`fuel = 1`) whose
constant term jumps from `0` to `1`, no prefix loss, full block absorption:
the leverage is exactly `1`. -/
theorem valueLeverage_smallSupport_eq_one :
    valueLeverage 1 1 (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
      (fun t => if t = 0 then (1 : ℝ) else 0) (fun _ => (0 : ℝ)) 0 1 = 1 := by
  rw [valueLeverage_eq_mul_add_abs]
  unfold blockConstant blockSurvival
  simp

/-- **Large support, vanishing leverage.**  A window of growing length `n`
with the *same* single jump at its first stage, but prefixed by an
`n`-stage, rate-`1/2` receding row: the prefix transport factor is `(1/2)^n`,
and the leverage tends to `0` even as the block's own length (its support)
grows without bound. -/
theorem tendsto_valueLeverage_largeSupport_atTop_nhds_zero :
    Filter.Tendsto
      (fun n : ℕ => valueLeverage (blockSurvival (fun _ => (1 / 2 : ℝ)) 0 n) 1
        (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ))
        (fun t => if t = 0 then (1 : ℝ) else 0) (fun _ => (0 : ℝ)) 0 n)
      Filter.atTop (nhds 0) := by
  have hCP : ∀ n : ℕ, blockSurvival (fun _ => (1 / 2 : ℝ)) 0 n = (1 / 2 : ℝ) ^ n := by
    intro n
    unfold blockSurvival
    rw [Finset.prod_const, Finset.card_range]
  have hBC : ∀ n : ℕ, 0 < n →
      blockConstant (fun t => if t = 0 then (1 : ℝ) else 0) (fun _ => (0 : ℝ)) 0 n = 1 := by
    intro n hn
    unfold blockConstant
    have hpt : ∀ offset, blockSurvival (fun _ => (0 : ℝ)) 0 offset *
        (fun t => if t = 0 then (1 : ℝ) else 0) (0 + offset) =
        if offset = 0 then blockSurvival (fun _ => (0 : ℝ)) 0 offset else 0 := by
      intro offset
      rw [Nat.zero_add]
      by_cases h0 : offset = 0 <;> simp [h0]
    simp_rw [hpt]
    rw [Finset.sum_ite_eq' (Finset.range n) 0 (blockSurvival (fun _ => (0 : ℝ)) 0)]
    simp [Finset.mem_range.mpr hn]
  have hBS : ∀ n : ℕ, 0 < n → blockSurvival (fun _ => (0 : ℝ)) 0 n = 0 := by
    intro n hn
    unfold blockSurvival
    exact Finset.prod_eq_zero (Finset.mem_range.mpr hn) rfl
  have hBC0 : ∀ n : ℕ, blockConstant (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 n = 0 := by
    intro n
    unfold blockConstant
    simp
  have hval : ∀ n : ℕ, 0 < n → valueLeverage (blockSurvival (fun _ => (1 / 2 : ℝ)) 0 n) 1
      (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) (fun t => if t = 0 then (1 : ℝ) else 0)
      (fun _ => (0 : ℝ)) 0 n = (1 / 2 : ℝ) ^ n := by
    intro n hn
    rw [valueLeverage_eq_mul_add_abs, hCP, hBC n hn, hBC0, hBS n hn]
    norm_num
  refine (Filter.tendsto_congr' ?_).mpr
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num) : Filter.Tendsto
      (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0))
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact hval n hn

/-! ## Part 5: the deviation channel, and the isolated-configuration fence -/

variable {ι' : Type} [Fintype ι'] [DecidableEq ι']

/-- **The deviation-channel transported leverage**, `L^dev_i(B;G)`,
deliverable (1).  The prefix deleted-survival transport factor `Q_{P,i}`,
divided by the post-modification **whole-window** deleted deficit
`1 - Q̃_{G,i}` -- a quantity of the enclosing array `G`, kept as an explicit
parameter rather than recomputed from `B`'s own `(start, fuel)` window, for
the same reason `valueLeverage` takes its `rhoTildeG` explicitly: `G` may be
strictly larger than `B` (`A2`) -- times the supremum over `w ∈ [-1, 1]` of
the discrepancy between the new and old block deviation operators over `B`'s
own window `[start, start + fuel)` -- `quittingCompanionComposite`, reused
without modification.  Meaningful only when `Q̃_{G,i} < 1`. -/
def deviationLeverage
    (reward : {S : Finset ι' // S.Nonempty} → Payoff ι')
    (Q_P oneSubQtildeG : ℝ) (roots roots' : ℕ → ι' → PMF Bool) (who : ι') (start fuel : ℕ) : ℝ :=
  (Q_P / oneSubQtildeG) *
    sSup ((fun w => |quittingCompanionComposite reward roots' who start fuel w -
        quittingCompanionComposite reward roots who start fuel w|) '' Set.Icc (-1 : ℝ) 1)

/-- **The honesty finding.**  The deviation leverage's denominator vanishes
*exactly* at the isolated configuration: `Q̃_{G,i} = 1` iff `who` is isolated
throughout the (post-modification) window `[0, fuel)`.  This is the same
`P = 1` regime `Math.MaxAffineStoppingValue.System`'s fence singles out
(`naiveClosedForm_eq_anchoredValue_iff_of_P_eq_one_of_T_eq_zero`): the
deviation leverage is undefined exactly where this program's obstructions --
the isolated coordinate of `QuittingSeamPriceDeviationFalsity` -- concentrate.
It is not merely large there; division by `1 - Q̃_{G,i}` is division by `0`,
and Lean's convention silently returns `0` rather than signaling the failure,
exactly as `naiveClosedForm_eq_anchoredValue_iff_of_P_eq_one_of_T_eq_zero`
warns for the value-channel closed form at `P = 1`. -/
theorem one_sub_quittingOpponentSurvivalWeight_eq_zero_iff_isQuittingIsolatedWindow
    (roots : ℕ → ι' → PMF Bool) (who : ι') (fuel : ℕ) :
    1 - quittingOpponentSurvivalWeight roots who 0 fuel = 0 ↔
      IsQuittingIsolatedWindow roots who fuel := by
  rw [sub_eq_zero, eq_comm]
  exact (isQuittingIsolatedWindow_iff_opponentSurvivalWeight_eq_one roots who fuel).symm

end GameTheory
