/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.WeightedRowMotionSeparation

/-!
# Face-circulation certificates and their microsteps

A **face-circulation certificate** for a weight `r` and a floor vector
`floor` is a closed cycle of feasible vectors `z^0, …, z^{L-1}` together
with mixing distributions `λ^ℓ` over the coordinates and contraction ratios
`α_ℓ ∈ (0,1)`, such that

* `z^{ℓ+1} = α_ℓ z^ℓ + (1 - α_ℓ) u^ℓ`, where `u^ℓ = ∑_k λ^ℓ_k w({k})` mixes
  the solo rows;
* every `z^ℓ` is above the floor;
* every coordinate in the support of `λ^ℓ` is **pinned**: `z^ℓ_i = d_i` and
  `u^ℓ_i = d_i`, where `d_i = w({i})_i` is the solo value of `i`.

This file proves the microstep half of the construction the certificate is
for, in the case where the phase distribution is a point mass at an owner
`i` -- which is the case the calibration instance below uses.

The two facts that drive everything are exact, not approximate:

* at the hazard row `h e_i` the one-stage successor is
  `f(r, h e_i) = (1 - h) r + h w({i})` at *every* coordinate
  (`oneStageNext_singletonRow`);
* consequently the discretised phase never leaves the ideal segment: the
  states are exactly `β^t z^ℓ + (1 - β^t) w({i})` with `β = 1 - h`, and the
  owner coordinate is exactly `d_i` throughout, so its stop-minus-continue
  difference is exactly `0`.

Hence the tolerance needed for the support-perfect condition along a
singleton-support phase is exactly `2 M h`: only the *inactive* coordinates
pay, and only through the one-stage reward swing `2M` they see when the
owner quits.  No averaging error, no balanced owner word and no fixed-point
correction enter, because the one-letter word is already balanced.

## Contents

* `singletonRow`, and its `sigmaValue` / `excludedValue` / `gammaValue` /
  `gainValue` / `oneStageNext` / quit-mass identities.
* `isSupportPerfectRow_singletonRow`, `isWeightedRow_singletonRow`: the
  one-stage inequalities at tolerance `2 M h`, from pinning at the owner and
  the solo floor elsewhere.
* `mixTarget`, `FaceCirculationCertificate`: the certificate (deliverable
  2a), over an arbitrary finite index type.
* `segmentPoint`, `oneStageNext_singletonRow_segmentPoint`,
  `segmentPoint_ge_floor`, `isSupportPerfectRow_segmentPoint`,
  `sub_le_nsmul_one_sub_of_pow_eq`: the one-phase step (deliverable 2b) for a
  singleton-support phase, with the tolerance recomputed.
* `cyclicCirculation`: the calibration instance for `scaledCyclicWeight`
  (deliverable 2c), with the three convex-combination identities checked.

## Scope

The floor vector is carried abstractly.  In the intended reading it is
`max{d_i, χ_i}` with `χ` the min-max level, so that "above the floor" is
rationality; nothing here formalizes `χ`, and `solo_le_floor` is the part of
that reading the microsteps actually consume.  The gluing of phases into a
single orbit of arbitrary quit mass is not built here.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Finset Math.PMFProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The singleton hazard row -/

/-- The microstep row `h e_i`: coordinate `i` quits with probability `h` and
every other coordinate is silent. -/
def singletonRow (h : ℝ) (i : ι) : ι → ℝ := fun j => if j = i then h else 0

omit [Fintype ι] in
@[simp] theorem singletonRow_self (h : ℝ) (i : ι) : singletonRow h i i = h := by
  simp [singletonRow]

omit [Fintype ι] in
@[simp] theorem singletonRow_of_ne (h : ℝ) {i j : ι} (hj : j ≠ i) :
    singletonRow h i j = 0 := by
  simp [singletonRow, hj]

omit [Fintype ι] in
/-- Every entry of a singleton row with `h ∈ [0,1]` lies in `[0,1]`. -/
theorem singletonRow_mem_unitInterval (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (i j : ι) :
    0 ≤ singletonRow h i j ∧ singletonRow h i j ≤ 1 := by
  unfold singletonRow
  split <;> constructor <;> first | exact hh0 | exact hh1 | norm_num

omit [Fintype ι] in
/-- The survival product of a singleton row over a finset: it drops the
factor `1 - h` exactly when the active coordinate belongs to the finset. -/
theorem prod_one_sub_singletonRow (t : Finset ι) (i : ι) (h : ℝ) :
    ∏ j ∈ t, (1 - singletonRow h i j) = if i ∈ t then 1 - h else 1 := by
  by_cases hi : i ∈ t
  · rw [if_pos hi]
    refine (Finset.prod_eq_single i (fun j _ hj => ?_) (fun hcon => absurd hi hcon)).trans ?_
    · rw [singletonRow_of_ne h hj]; ring
    · rw [singletonRow_self]
  · rw [if_neg hi]
    refine Finset.prod_eq_one fun j hj => ?_
    have hne : j ≠ i := fun hcon => hi (hcon ▸ hj)
    rw [singletonRow_of_ne h hne]; ring

omit [Fintype ι] in
/-- **Coalition sums against a singleton row, active coordinate absent.**
Every nonempty coalition inside the ground set has zero mass. -/
theorem sum_powerset_singletonRow_of_notMem (t : Finset ι) (i : ι) (h : ℝ) (hi : i ∉ t)
    (g : Finset ι → ℝ) :
    ∑ J ∈ t.powerset, (∏ j ∈ J, singletonRow h i j) *
        (∏ j ∈ t \ J, (1 - singletonRow h i j)) * g J = g ∅ := by
  refine (Finset.sum_eq_single ∅ (fun J hJ hJne => ?_)
    (fun hcon => absurd (Finset.empty_mem_powerset t) hcon)).trans ?_
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hJne
    have hjt : j ∈ t := (Finset.mem_powerset.mp hJ) hj
    have hjne : j ≠ i := fun hcon => hi (hcon ▸ hjt)
    rw [Finset.prod_eq_zero hj (singletonRow_of_ne h hjne)]
    ring
  · rw [Finset.prod_empty, Finset.sdiff_empty, prod_one_sub_singletonRow, if_neg hi]
    ring

omit [Fintype ι] in
/-- **Coalition sums against a singleton row, active coordinate present.**
Only the empty coalition and the singleton `{i}` carry mass. -/
theorem sum_powerset_singletonRow_of_mem (t : Finset ι) (i : ι) (h : ℝ) (hi : i ∈ t)
    (g : Finset ι → ℝ) :
    ∑ J ∈ t.powerset, (∏ j ∈ J, singletonRow h i j) *
        (∏ j ∈ t \ J, (1 - singletonRow h i j)) * g J = (1 - h) * g ∅ + h * g {i} := by
  have hsub : ({∅, {i}} : Finset (Finset ι)) ⊆ t.powerset := by
    intro J hJ
    rcases Finset.mem_insert.mp hJ with rfl | hJ
    · exact Finset.empty_mem_powerset t
    · rw [Finset.mem_singleton] at hJ
      subst hJ
      exact Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hi)
  have hzero : ∀ J ∈ t.powerset, J ∉ ({∅, {i}} : Finset (Finset ι)) →
      (∏ j ∈ J, singletonRow h i j) *
        (∏ j ∈ t \ J, (1 - singletonRow h i j)) * g J = 0 := by
    intro J _ hJ
    have hne : ¬ J ⊆ {i} := by
      intro hcon
      rcases Finset.subset_singleton_iff.mp hcon with rfl | rfl
      · exact hJ (Finset.mem_insert_self _ _)
      · exact hJ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    obtain ⟨j, hjJ, hji⟩ := Finset.not_subset.mp hne
    rw [Finset.prod_eq_zero hjJ (singletonRow_of_ne h (by simpa using hji))]
    ring
  rw [← Finset.sum_subset hsub hzero,
    Finset.sum_pair (by simp : (∅ : Finset ι) ≠ {i})]
  have hemp : (∏ j ∈ (∅ : Finset ι), singletonRow h i j) *
      (∏ j ∈ t \ (∅ : Finset ι), (1 - singletonRow h i j)) * g ∅ = (1 - h) * g ∅ := by
    rw [Finset.prod_empty, Finset.sdiff_empty, prod_one_sub_singletonRow, if_pos hi]
    ring
  have hsing : (∏ j ∈ ({i} : Finset ι), singletonRow h i j) *
      (∏ j ∈ t \ ({i} : Finset ι), (1 - singletonRow h i j)) * g {i} = h * g {i} := by
    rw [Finset.prod_singleton, singletonRow_self, prod_one_sub_singletonRow,
      if_neg (by simp)]
    ring
  rw [hemp, hsing]

/-! ## The one-stage objects at a singleton row -/

/-- At the owner's own coordinate the stop payoff is the solo value: every
opponent is silent. -/
theorem sigmaValue_singletonRow_self (r : Finset ι → ι → ℝ) (h : ℝ) (i : ι) :
    sigmaValue r (singletonRow h i) i = r {i} i := by
  unfold sigmaValue
  rw [sum_powerset_singletonRow_of_notMem _ i h (Finset.notMem_erase i _)]
  simp

/-- At the owner's own coordinate no nonempty opponent coalition has mass. -/
theorem excludedValue_singletonRow_self (r : Finset ι → ι → ℝ) (h : ℝ) (i : ι) :
    excludedValue r (singletonRow h i) i = 0 := by
  refine Finset.sum_eq_zero fun J hJ => ?_
  obtain ⟨hJne, hJsub⟩ := Finset.mem_erase.mp hJ
  obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hJne
  have hjt : j ∈ Finset.univ.erase i := (Finset.mem_powerset.mp hJsub) hj
  have hjne : j ≠ i := (Finset.mem_erase.mp hjt).1
  rw [Finset.prod_eq_zero hj (singletonRow_of_ne h hjne)]
  ring

/-- At the owner's own coordinate the continue payoff is the continuation
value itself. -/
theorem gammaValue_singletonRow_self (r : Finset ι → ι → ℝ) (h : ℝ) (i : ι) (next : ℝ) :
    gammaValue r (singletonRow h i) i next = next := by
  unfold gammaValue continueMassExcl
  rw [excludedValue_singletonRow_self, prod_one_sub_singletonRow,
    if_neg (Finset.notMem_erase i _)]
  ring

/-- **The owner's stop-minus-continue difference is the pinning gap.** -/
theorem gainValue_singletonRow_self (r : Finset ι → ι → ℝ) (h : ℝ) (i : ι) (next : ℝ) :
    gainValue r (singletonRow h i) i next = r {i} i - next := by
  unfold gainValue
  rw [sigmaValue_singletonRow_self, gammaValue_singletonRow_self]

/-- At an inactive coordinate the stop payoff splits on whether the owner
quits. -/
theorem sigmaValue_singletonRow_of_ne (r : Finset ι → ι → ℝ) (h : ℝ) {i k : ι} (hk : k ≠ i) :
    sigmaValue r (singletonRow h i) k = (1 - h) * r {k} k + h * r {k, i} k := by
  unfold sigmaValue
  rw [sum_powerset_singletonRow_of_mem _ i h
    (Finset.mem_erase.mpr ⟨fun hcon => hk hcon.symm, Finset.mem_univ i⟩)]
  simp

/-- At an inactive coordinate only the owner's solo coalition carries
mass. -/
theorem excludedValue_singletonRow_of_ne (r : Finset ι → ι → ℝ) (h : ℝ) {i k : ι} (hk : k ≠ i) :
    excludedValue r (singletonRow h i) k = h * r {i} k := by
  have hik : i ∈ Finset.univ.erase k :=
    Finset.mem_erase.mpr ⟨fun hcon => hk hcon.symm, Finset.mem_univ i⟩
  have hmem : (∅ : Finset ι) ∈ (Finset.univ.erase k).powerset := Finset.empty_mem_powerset _
  have hfull := sum_powerset_singletonRow_of_mem (Finset.univ.erase k) i h hik
    (fun J => r J k)
  rw [← Finset.add_sum_erase _ _ hmem] at hfull
  have hemp : (∏ j ∈ (∅ : Finset ι), singletonRow h i j) *
      (∏ j ∈ Finset.univ.erase k \ (∅ : Finset ι), (1 - singletonRow h i j)) * r ∅ k =
      (1 - h) * r ∅ k := by
    rw [Finset.prod_empty, Finset.sdiff_empty, prod_one_sub_singletonRow, if_pos hik]
    ring
  rw [hemp] at hfull
  unfold excludedValue
  linarith

/-- At an inactive coordinate the continue payoff mixes the owner's solo row
with the continuation. -/
theorem gammaValue_singletonRow_of_ne (r : Finset ι → ι → ℝ) (h : ℝ) {i k : ι} (hk : k ≠ i)
    (next : ℝ) :
    gammaValue r (singletonRow h i) k next = h * r {i} k + (1 - h) * next := by
  unfold gammaValue continueMassExcl
  rw [excludedValue_singletonRow_of_ne r h hk, prod_one_sub_singletonRow,
    if_pos (Finset.mem_erase.mpr ⟨fun hcon => hk hcon.symm, Finset.mem_univ i⟩)]

/-- **An inactive coordinate's stop-minus-continue difference**: its own
pinning gap, damped by survival, plus the owner-quit reward swing. -/
theorem gainValue_singletonRow_of_ne (r : Finset ι → ι → ℝ) (h : ℝ) {i k : ι} (hk : k ≠ i)
    (next : ℝ) :
    gainValue r (singletonRow h i) k next =
      (1 - h) * (r {k} k - next) + h * (r {k, i} k - r {i} k) := by
  unfold gainValue
  rw [sigmaValue_singletonRow_of_ne r h hk, gammaValue_singletonRow_of_ne r h hk]
  ring

/-- **The microstep recursion**, equation (45): a singleton row moves the
state a fraction `h` of the way towards the owner's solo row, at every
coordinate at once. -/
theorem oneStageNext_singletonRow (r : Finset ι → ι → ℝ) (h : ℝ) (i : ι) (rest : ι → ℝ)
    (j : ι) :
    oneStageNext r (singletonRow h i) rest j = (1 - h) * rest j + h * r {i} j := by
  unfold oneStageNext oneStageMixPayoff
  by_cases hj : j = i
  · subst hj
    rw [sigmaValue_singletonRow_self, gammaValue_singletonRow_self, singletonRow_self]
    ring
  · rw [gammaValue_singletonRow_of_ne r h hj, singletonRow_of_ne h hj]
    ring

/-- The quit mass of a singleton row is its hazard. -/
theorem quitMass_singletonRow (h : ℝ) (i : ι) :
    1 - continueMass (singletonRow h i) = h := by
  rw [continueMass]
  have := prod_one_sub_singletonRow (Finset.univ : Finset ι) i h
  rw [if_pos (Finset.mem_univ i)] at this
  rw [this]
  ring

/-! ## The one-stage inequalities at a singleton row -/

/-- **The support-perfect condition along a pinned microstep.**  If the
owner's coordinate is pinned at its solo value and every coordinate is at
or above its solo value, then the singleton row `h e_i` satisfies the
support-perfect condition at tolerance `2 M h`.

The owner is exactly indifferent; an inactive coordinate is only ever asked
for the upper clause, and it loses at most the one-stage reward swing `2M`
on the owner-quits event, which has probability `h`. -/
theorem isSupportPerfectRow_singletonRow (r : Finset ι → ι → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ S j, |r S j| ≤ M) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (i : ι) (rest : ι → ℝ)
    (hpin : rest i = r {i} i) (hsolo : ∀ k, r {k} k ≤ rest k)
    (ε : ℝ) (hε : 2 * M * h ≤ ε) :
    IsSupportPerfectRow r (singletonRow h i) rest ε := by
  have hε0 : 0 ≤ ε := le_trans (by positivity) hε
  intro j
  by_cases hj : j = i
  · subst hj
    rw [gainValue_singletonRow_self, hpin]
    constructor <;> intro _ <;> simp [hε0]
  · rw [gainValue_singletonRow_of_ne r h hj]
    refine ⟨fun hpos => absurd hpos ?_, fun _ => ?_⟩
    · rw [singletonRow_of_ne h hj]
      exact lt_irrefl 0
    · have hswing : r {j, i} j - r {i} j ≤ 2 * M := by
        have h1 := abs_le.mp (hM {j, i} j)
        have h2 := abs_le.mp (hM {i} j)
        linarith [h1.2, h2.1]
      have hgap : r {j} j - rest j ≤ 0 := by linarith [hsolo j]
      nlinarith [mul_nonneg hh0 (by linarith : (0 : ℝ) ≤ 2 * M - (r {j, i} j - r {i} j))]

/-- The same microstep satisfies the weighted condition, by the
one-directional conversion. -/
theorem isWeightedRow_singletonRow (r : Finset ι → ι → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ S j, |r S j| ≤ M) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (i : ι) (rest : ι → ℝ)
    (hpin : rest i = r {i} i) (hsolo : ∀ k, r {k} k ≤ rest k)
    (ε : ℝ) (hε : 2 * M * h ≤ ε) :
    IsWeightedRow r (singletonRow h i) rest ε :=
  isWeightedRow_of_isSupportPerfectRow r _ _ _
    (fun j => (singletonRow_mem_unitInterval h hh0 hh1 i j).1)
    (fun j => (singletonRow_mem_unitInterval h hh0 hh1 i j).2)
    (le_trans (by positivity) hε)
    (isSupportPerfectRow_singletonRow r M hM0 hM h hh0 hh1 i rest hpin hsolo ε hε)

/-! ## The certificate -/

/-- The mixed singleton target `u = ∑_k λ_k w({k})`. -/
def mixTarget (r : Finset ι → ι → ℝ) (lam : ι → ℝ) : ι → ℝ :=
  fun j => ∑ k, lam k * r {k} j

/-- A point-mass distribution mixes to the corresponding solo row. -/
theorem mixTarget_single (r : Finset ι → ι → ℝ) (i : ι) :
    mixTarget r (fun k => if k = i then 1 else 0) = fun j => r {i} j := by
  funext j
  unfold mixTarget
  refine (Finset.sum_eq_single i (fun b _ hb => by simp [hb])
    (fun hcon => absurd (Finset.mem_univ i) hcon)).trans ?_
  simp

/-- **A singleton-face circulation certificate** (deliverable 2a), over an
arbitrary finite index type.  The phases are indexed by `ZMod L`, so the
cycle closes by construction.

`vertex` is the ideal cycle `z^ℓ`, `mixWeight` is the distribution `λ^ℓ`,
and `ratio` is the contraction `α_ℓ`.  The last three fields are the pinning
and floor conditions: every ideal state is above the floor, every coordinate
in the support of `λ^ℓ` sits exactly at its solo value both on the ideal
state and on the phase target, and the floor itself dominates the solo
values. -/
structure FaceCirculationCertificate (r : Finset ι → ι → ℝ) (floor : ι → ℝ)
    (L : ℕ) [NeZero L] where
  /-- The ideal cycle of feasible vectors. -/
  vertex : ZMod L → ι → ℝ
  /-- The mixing distribution of each phase. -/
  mixWeight : ZMod L → ι → ℝ
  /-- The contraction ratio of each phase. -/
  ratio : ZMod L → ℝ
  /-- The mixing weights are nonnegative. -/
  mixWeight_nonneg : ∀ l j, 0 ≤ mixWeight l j
  /-- The mixing weights sum to one. -/
  mixWeight_sum : ∀ l, ∑ j, mixWeight l j = 1
  /-- The contraction ratios are positive. -/
  ratio_pos : ∀ l, 0 < ratio l
  /-- The contraction ratios are below one. -/
  ratio_lt_one : ∀ l, ratio l < 1
  /-- Each phase is a convex step towards its own mixed target. -/
  step : ∀ l j, vertex (l + 1) j =
    ratio l * vertex l j + (1 - ratio l) * mixTarget r (mixWeight l) j
  /-- Every ideal state is above the floor. -/
  vertex_ge_floor : ∀ l j, floor j ≤ vertex l j
  /-- Every owner of a phase is pinned on the ideal state. -/
  vertex_pinned : ∀ l j, 0 < mixWeight l j → vertex l j = r {j} j
  /-- Every owner of a phase is pinned on the phase target. -/
  target_pinned : ∀ l j, 0 < mixWeight l j → mixTarget r (mixWeight l) j = r {j} j
  /-- The floor dominates the solo values. -/
  solo_le_floor : ∀ j, r {j} j ≤ floor j

/-! ## The one-phase step, for a singleton-support phase -/

/-- The point `μ z + (1 - μ) v` of the segment from `v` to `z`. -/
def segmentPoint (z v : ι → ℝ) (μ : ℝ) : ι → ℝ := fun j => μ * z j + (1 - μ) * v j

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem segmentPoint_one (z v : ι → ℝ) : segmentPoint z v 1 = z := by
  funext j; simp [segmentPoint]

/-- **The phase trajectory stays on the ideal segment.**  One microstep of
hazard `1 - β` at owner `i` multiplies the segment parameter by `β`; no
error term appears, so the discretised phase is exactly the ideal edge
traversed geometrically. -/
theorem oneStageNext_singletonRow_segmentPoint (r : Finset ι → ι → ℝ) (β : ℝ) (i : ι)
    (z : ι → ℝ) (μ : ℝ) (j : ι) :
    oneStageNext r (singletonRow (1 - β) i) (segmentPoint z (fun k => r {i} k) μ) j =
      segmentPoint z (fun k => r {i} k) (μ * β) j := by
  rw [oneStageNext_singletonRow]
  unfold segmentPoint
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- The owner's coordinate is pinned all along its own phase segment. -/
theorem segmentPoint_pinned (r : Finset ι → ι → ℝ) (i : ι) (z : ι → ℝ) (μ : ℝ)
    (hz : z i = r {i} i) :
    segmentPoint z (fun k => r {i} k) μ i = r {i} i := by
  unfold segmentPoint
  rw [hz]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- **Every intermediate state of a phase is above the floor.**  The segment
parameter runs between the phase's contraction ratio and `1`, so the state
is a convex combination of the phase's two endpoints, both of which are
above the floor.  This is the exact form of the source argument's
rationality step for a singleton-support phase. -/
theorem segmentPoint_ge_floor (z v floor : ι → ℝ) (α μ : ℝ) (hα1 : α < 1) (hαμ : α ≤ μ)
    (hμ1 : μ ≤ 1) (hz : ∀ j, floor j ≤ z j)
    (hnext : ∀ j, floor j ≤ α * z j + (1 - α) * v j) (j : ι) :
    floor j ≤ segmentPoint z v μ j := by
  unfold segmentPoint
  have hA : 0 ≤ z j - floor j := by linarith [hz j]
  have hB : 0 ≤ α * z j + (1 - α) * v j - floor j := by linarith [hnext j]
  have hkey : (1 - α) * (μ * z j + (1 - μ) * v j - floor j) =
      (μ - α) * (z j - floor j) + (1 - μ) * (α * z j + (1 - α) * v j - floor j) := by
    ring
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ μ - α) hA,
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - μ) hB]

/-- **The one-stage inequalities along a singleton-support phase**
(deliverable 2b).  At every intermediate state of the phase, the microstep
row `(1 - β) e_i` satisfies the support-perfect condition at tolerance
`2 M (1 - β)`.

The tolerance carries no averaging term: the owner word of a
singleton-support phase is the constant word, which is already balanced, so
the actual trajectory equals the averaged one and the fixed-point correction
of the general argument is empty.  Compare the general bound
`ε / (2M + 6MC/(1-A))` of the source argument, whose second summand comes
from a word-imbalance estimate that is not tight at support size one. -/
theorem isSupportPerfectRow_segmentPoint (r : Finset ι → ι → ℝ) (floor : ι → ℝ) (M : ℝ)
    (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M) (i : ι) (z : ι → ℝ) (α β μ : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hα1 : α < 1) (hαμ : α ≤ μ) (hμ1 : μ ≤ 1)
    (hz : ∀ j, floor j ≤ z j) (hnext : ∀ j, floor j ≤ α * z j + (1 - α) * r {i} j)
    (hzpin : z i = r {i} i) (hfloor : ∀ j, r {j} j ≤ floor j)
    (ε : ℝ) (hε : 2 * M * (1 - β) ≤ ε) :
    IsSupportPerfectRow r (singletonRow (1 - β) i)
      (segmentPoint z (fun k => r {i} k) μ) ε :=
  isSupportPerfectRow_singletonRow r M hM0 hM (1 - β) (by linarith) (by linarith) i _
    (segmentPoint_pinned r i z μ hzpin)
    (fun k => le_trans (hfloor k)
      (segmentPoint_ge_floor z (fun k => r {i} k) floor α μ hα1 hαμ hμ1 hz hnext k))
    ε hε

/-- The segment parameter of a phase never drops below the phase's
contraction ratio. -/
theorem pow_le_pow_of_pow_eq (α β : ℝ) (N t : ℕ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβN : β ^ N = α) (htN : t ≤ N) : α ≤ β ^ t := by
  rw [← hβN]
  exact pow_le_pow_of_le_one hβ0 hβ1 htN

/-- **The phase quit mass**, equation (54): `N` microsteps of hazard
`1 - β` with `β ^ N = α` release at least `1 - α` of quit mass.  This is
Bernoulli's inequality. -/
theorem sub_le_nsmul_one_sub_of_pow_eq (α β : ℝ) (N : ℕ) (hβ0 : 0 ≤ β) (hβN : β ^ N = α) :
    1 - α ≤ N * (1 - β) := by
  have hbern : 1 + (N : ℝ) * (β - 1) ≤ (1 + (β - 1)) ^ N :=
    one_add_mul_le_pow (by linarith) N
  rw [show (1 : ℝ) + (β - 1) = β by ring, hβN] at hbern
  linarith

/-! ## Calibration on the scaled cyclic weight -/

/-- The owner word of the calibration cycle: phase `0` is owned by
coordinate `0`, phase `1` by coordinate `2`, phase `2` by coordinate `1`. -/
def cyclicCirculationOwner (l : ZMod 3) : CyclicIndex :=
  if l = 0 then 0 else if l = 1 then 2 else 1

/-- The rotated triangle of the calibration cycle: `(1/3, 1/3, 2/3)`,
`(1/3, 2/3, 1/3)`, `(2/3, 1/3, 1/3)`. -/
def cyclicCirculationVertex (l : ZMod 3) : CyclicIndex → ℝ :=
  if l = 0 then ![1 / 3, 1 / 3, 2 / 3]
  else if l = 1 then ![1 / 3, 2 / 3, 1 / 3]
  else ![2 / 3, 1 / 3, 1 / 3]

/-- The floor of the calibration cycle: every coordinate's solo value
`d_i = 1/3`.  The source argument's floor is `max{d_i, χ_i}`, and it records
`χ_i ≤ 1/3` for this weight; that min-max bound is quoted, not formalized
here, so `1/3` is used directly. -/
def cyclicCirculationFloor : CyclicIndex → ℝ := fun _ => 1 / 3

/-- **The three convex-combination identities** of the calibration cycle,
equation (58): each vertex is the midpoint of the previous vertex and the
solo row of the phase owner. -/
theorem cyclicCirculationVertex_step (l : ZMod 3) (j : CyclicIndex) :
    cyclicCirculationVertex (l + 1) j =
      (1 / 2) * cyclicCirculationVertex l j +
        (1 - 1 / 2) * scaledCyclicWeight {cyclicCirculationOwner l} j := by
  rcases zmod_three_cases l with rfl | rfl | rfl <;> fin_cases j <;>
    simp +decide [cyclicCirculationVertex, cyclicCirculationOwner,
      scaledCyclicWeight_zero, scaledCyclicWeight_one, scaledCyclicWeight_two] <;>
    norm_num

/-- Every vertex of the calibration cycle is above the floor. -/
theorem cyclicCirculationVertex_ge_floor (l : ZMod 3) (j : CyclicIndex) :
    cyclicCirculationFloor j ≤ cyclicCirculationVertex l j := by
  rcases zmod_three_cases l with rfl | rfl | rfl <;> fin_cases j <;>
    simp +decide [cyclicCirculationVertex, cyclicCirculationFloor] <;> norm_num

/-- Each phase owner is pinned at its solo value `1/3` on the ideal
state. -/
theorem cyclicCirculationVertex_pinned (l : ZMod 3) :
    cyclicCirculationVertex l (cyclicCirculationOwner l) =
      scaledCyclicWeight {cyclicCirculationOwner l} (cyclicCirculationOwner l) := by
  rw [scaledCyclicWeight_diagonal]
  rcases zmod_three_cases l with rfl | rfl | rfl <;>
    simp +decide [cyclicCirculationVertex, cyclicCirculationOwner]

/-- **The calibration certificate** (deliverable 2c): the scaled cyclic
weight admits a face-circulation certificate of length three, with point-mass
distributions, owners `0, 2, 1` and all contraction ratios `1/2`. -/
def cyclicCirculation :
    FaceCirculationCertificate scaledCyclicWeight cyclicCirculationFloor 3 where
  vertex := cyclicCirculationVertex
  mixWeight := fun l k => if k = cyclicCirculationOwner l then 1 else 0
  ratio := fun _ => 1 / 2
  mixWeight_nonneg := by
    intro l j
    split <;> norm_num
  mixWeight_sum := by
    intro l
    simp
  ratio_pos := by intro l; norm_num
  ratio_lt_one := by intro l; norm_num
  step := by
    intro l j
    simp only [mixTarget_single]
    exact cyclicCirculationVertex_step l j
  vertex_ge_floor := cyclicCirculationVertex_ge_floor
  vertex_pinned := by
    intro l j hj
    have hjl : j = cyclicCirculationOwner l := by
      by_contra hcon
      simp [hcon] at hj
    subst hjl
    exact cyclicCirculationVertex_pinned l
  target_pinned := by
    intro l j hj
    have hjl : j = cyclicCirculationOwner l := by
      by_contra hcon
      simp [hcon] at hj
    subst hjl
    rw [mixTarget_single]
  solo_le_floor := by
    intro j
    rw [scaledCyclicWeight_diagonal]
    norm_num [cyclicCirculationFloor]

/-- **The calibrated one-phase step.**  For the scaled cyclic weight, at
every intermediate state of the phase owned by `i` starting from a vertex
`z` of the calibration cycle, the microstep row `(1 - β) e_i` satisfies the
support-perfect condition at tolerance `2 (1 - β)`: the reward bound is
`M = 1`, and the phase contraction is `α = 1/2`. -/
theorem isSupportPerfectRow_cyclicCirculation (l : ZMod 3) (β μ : ℝ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hαμ : (1 : ℝ) / 2 ≤ μ) (hμ1 : μ ≤ 1) (ε : ℝ)
    (hε : 2 * (1 - β) ≤ ε) :
    IsSupportPerfectRow scaledCyclicWeight
      (singletonRow (1 - β) (cyclicCirculationOwner l))
      (segmentPoint (cyclicCirculationVertex l)
        (fun k => scaledCyclicWeight {cyclicCirculationOwner l} k) μ) ε := by
  refine isSupportPerfectRow_segmentPoint scaledCyclicWeight cyclicCirculationFloor 1
    (by norm_num) abs_scaledCyclicWeight_le_one (cyclicCirculationOwner l)
    (cyclicCirculationVertex l) (1 / 2) β μ hβ0 hβ1 (by norm_num) hαμ hμ1
    (cyclicCirculationVertex_ge_floor l) (fun j => ?_)
    (cyclicCirculationVertex_pinned l)
    (fun j => by rw [scaledCyclicWeight_diagonal]; norm_num [cyclicCirculationFloor])
    ε (by linarith)
  have hstep := cyclicCirculationVertex_step l j
  have hge := cyclicCirculationVertex_ge_floor (l + 1) j
  linarith

end GameTheory
