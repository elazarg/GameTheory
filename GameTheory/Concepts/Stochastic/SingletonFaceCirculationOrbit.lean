/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.SingletonFaceCirculation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gluing the phases: orbits of unbounded quit mass from a circulation

`SingletonFaceCirculation.lean` proves the one-phase step: along the ideal
edge of a singleton-support phase, the microstep row `(1 - β) e_i` satisfies
the support-perfect condition at tolerance `2 M (1 - β)` and keeps the state
above the floor.  This file glues the phases into a single infinite forward
chain and reads off its quit mass.

The schedule is the obvious one: spend `N` microsteps in each phase, then
advance.  Because a singleton-support phase is traversed *exactly* -- the
state is `β^t z^ℓ + (1 - β^t) w({i_ℓ})` and the phase ends at
`β^N z^ℓ + (1 - β^N) w({i_ℓ}) = α_ℓ z^ℓ + (1 - α_ℓ) w({i_ℓ}) = z^{ℓ+1}` --
the chain closes on the ideal cycle with no error and no fixed-point
correction.

Consequently the whole chain lives in the `2 M (1 - β)`-support-perfect
correspondence, stays above the floor forever, and releases quit mass
`1 - β` per microstep, so any prescribed total quit mass is reached by a
long enough finite prefix.

## Contents

* `phaseSchedule`, `phaseSchedule_snd_lt`: the microstep schedule and its
  invariant.
* `SingletonSupport`: the point-mass presentation of a certificate's phases.
* `circulationRow`, `circulationState`, `circulationState_succ`: the chain
  and its one-stage recursion `R_{n+1} = f(R_n, x_n)`.
* `circulationState_ge_floor`, `isSupportPerfectRow_circulation`,
  `isWeightedRow_circulation`: rationality and the one-stage inequalities.
* `exists_prefix_quitMass_ge`: for every target `Q` a finite prefix of the
  chain has quit mass at least `Q`.

## Reading the chain as an orbit

The chain runs forward, `R_{n+1} = f(R_n, x_n)`; the backward orbit
convention of the source question is obtained by reversing a finite prefix,
`r^{(t)} = R_{m - t}`, which turns `circulationState_succ` into
`r^{(t)} = f(r^{(t+1)}, x^{(t)})` with no change of content.  Feasibility of
the states is inherited from the certificate's vertices, which is a property
of the certificate and is not re-derived here.
-/

noncomputable section

namespace GameTheory

open Finset Math.PMFProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The microstep schedule -/

/-- The microstep schedule: `N` steps in each phase, then advance the
phase.  The pair is (current phase, steps already spent in it). -/
def phaseSchedule (L N : ℕ) [NeZero L] : ℕ → ZMod L × ℕ
  | 0 => (0, 0)
  | n + 1 =>
      if (phaseSchedule L N n).2 + 1 < N then
        ((phaseSchedule L N n).1, (phaseSchedule L N n).2 + 1)
      else ((phaseSchedule L N n).1 + 1, 0)

/-- The schedule's successor equation. -/
theorem phaseSchedule_succ (L N : ℕ) [NeZero L] (n : ℕ) :
    phaseSchedule L N (n + 1) =
      if (phaseSchedule L N n).2 + 1 < N then
        ((phaseSchedule L N n).1, (phaseSchedule L N n).2 + 1)
      else ((phaseSchedule L N n).1 + 1, 0) := rfl

/-- **The schedule invariant**: the step counter never reaches the phase
length. -/
theorem phaseSchedule_snd_lt (L N : ℕ) [NeZero L] (hN : 0 < N) (n : ℕ) :
    (phaseSchedule L N n).2 < N := by
  induction n with
  | zero => simpa [phaseSchedule] using hN
  | succ n ih =>
      rw [phaseSchedule_succ]
      split
      · rename_i hcase
        simpa using hcase
      · simpa using hN

/-! ## Singleton-support certificates -/

/-- A **singleton-support presentation** of a certificate: each phase's
mixing distribution is a point mass at an owner coordinate. -/
structure SingletonSupport {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]
    (C : FaceCirculationCertificate r floor L) where
  /-- The owner of each phase. -/
  owner : ZMod L → ι
  /-- The phase distribution is the point mass at the owner. -/
  mixWeight_eq : ∀ l, C.mixWeight l = fun k => if k = owner l then 1 else 0

namespace SingletonSupport

variable {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]
  {C : FaceCirculationCertificate r floor L} (S : SingletonSupport C)

/-- The phase target of a singleton-support phase is the owner's solo
row. -/
theorem mixTarget_eq (l : ZMod L) :
    mixTarget r (C.mixWeight l) = fun j => r {S.owner l} j := by
  rw [S.mixWeight_eq l, mixTarget_single]

/-- The certificate's convex step, read through the point mass. -/
theorem step_owner (l : ZMod L) (j : ι) :
    C.vertex (l + 1) j =
      C.ratio l * C.vertex l j + (1 - C.ratio l) * r {S.owner l} j := by
  have h := C.step l j
  rw [S.mixTarget_eq l] at h
  exact h

/-- The owner of a phase is pinned at its solo value on the phase's ideal
vertex. -/
theorem vertex_pinned_owner (l : ZMod L) :
    C.vertex l (S.owner l) = r {S.owner l} (S.owner l) := by
  refine C.vertex_pinned l (S.owner l) ?_
  rw [S.mixWeight_eq l]
  norm_num

end SingletonSupport

/-! ## The glued chain -/

variable {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]
  {C : FaceCirculationCertificate r floor L}

/-- The microstep row at chain position `n`: the owner of the current phase
quits with hazard `1 - β` of that phase. -/
def circulationRow (S : SingletonSupport C) (β : ZMod L → ℝ) (N : ℕ) (n : ℕ) : ι → ℝ :=
  singletonRow (1 - β (phaseSchedule L N n).1) (S.owner (phaseSchedule L N n).1)

/-- The chain state at position `n`: the point of the current phase's ideal
edge reached after the steps already spent in that phase. -/
def circulationState (S : SingletonSupport C) (β : ZMod L → ℝ) (N : ℕ) (n : ℕ) : ι → ℝ :=
  segmentPoint (C.vertex (phaseSchedule L N n).1)
    (fun k => r {S.owner (phaseSchedule L N n).1} k)
    (β (phaseSchedule L N n).1 ^ (phaseSchedule L N n).2)

/-- **The chain obeys the one-stage recursion** `R_{n+1} = f(R_n, x_n)`.
Inside a phase this is the geometric traversal of the ideal edge; at a phase
boundary it is the certificate's own convex step, because `β^N` is exactly
the phase's contraction ratio. -/
theorem circulationState_succ (S : SingletonSupport C) (β : ZMod L → ℝ) (N : ℕ)
    (hN : 0 < N) (hβN : ∀ l, β l ^ N = C.ratio l) (n : ℕ) (j : ι) :
    circulationState S β N (n + 1) j =
      oneStageNext r (circulationRow S β N n) (circulationState S β N n) j := by
  unfold circulationState circulationRow
  rw [oneStageNext_singletonRow_segmentPoint, phaseSchedule_succ]
  split
  · dsimp only
    rw [pow_succ]
  · have hlt := phaseSchedule_snd_lt L N hN n
    have heq : (phaseSchedule L N n).2 + 1 = N := by omega
    dsimp only
    rw [pow_zero, segmentPoint_one, ← pow_succ, heq, hβN]
    simpa [segmentPoint] using S.step_owner _ j

omit [DecidableEq ι] in
/-- The chain's segment parameter lies between the phase's contraction ratio
and one. -/
theorem circulationState_param_mem (β : ZMod L → ℝ) (N : ℕ)
    (hN : 0 < N) (hβ0 : ∀ l, 0 ≤ β l) (hβ1 : ∀ l, β l ≤ 1) (hβN : ∀ l, β l ^ N = C.ratio l)
    (n : ℕ) :
    C.ratio (phaseSchedule L N n).1 ≤
        β (phaseSchedule L N n).1 ^ (phaseSchedule L N n).2 ∧
      β (phaseSchedule L N n).1 ^ (phaseSchedule L N n).2 ≤ 1 := by
  refine ⟨pow_le_pow_of_pow_eq _ _ N _ (hβ0 _) (hβ1 _) (hβN _)
    (le_of_lt (phaseSchedule_snd_lt L N hN n)), ?_⟩
  exact pow_le_one₀ (hβ0 _) (hβ1 _)

/-- The ideal edge of a phase ends above the floor: its endpoint is the next
vertex. -/
theorem circulation_edge_ge_floor (S : SingletonSupport C) (l : ZMod L) (j : ι) :
    floor j ≤ C.ratio l * C.vertex l j + (1 - C.ratio l) * r {S.owner l} j := by
  rw [← S.step_owner l j]
  exact C.vertex_ge_floor (l + 1) j

/-- **Rationality along the chain**: every state is above the floor, because
it is a convex combination of the two ideal endpoints of its phase. -/
theorem circulationState_ge_floor (S : SingletonSupport C) (β : ZMod L → ℝ) (N : ℕ)
    (hN : 0 < N) (hβ0 : ∀ l, 0 ≤ β l) (hβ1 : ∀ l, β l ≤ 1) (hβN : ∀ l, β l ^ N = C.ratio l)
    (n : ℕ) (j : ι) :
    floor j ≤ circulationState S β N n j := by
  obtain ⟨hlow, hhigh⟩ := circulationState_param_mem β N hN hβ0 hβ1 hβN n
  exact segmentPoint_ge_floor _ _ _ _ _ (C.ratio_lt_one _) hlow hhigh
    (C.vertex_ge_floor _) (circulation_edge_ge_floor S _) j

/-- **The one-stage inequalities along the chain**: every microstep row of
the chain satisfies the support-perfect condition at tolerance
`2 M (1 - β)`. -/
theorem isSupportPerfectRow_circulation (S : SingletonSupport C) (β : ZMod L → ℝ) (N : ℕ)
    (hN : 0 < N) (hβ0 : ∀ l, 0 ≤ β l) (hβ1 : ∀ l, β l ≤ 1) (hβN : ∀ l, β l ^ N = C.ratio l)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S' j, |r S' j| ≤ M) (ε : ℝ)
    (hε : ∀ l, 2 * M * (1 - β l) ≤ ε) (n : ℕ) :
    IsSupportPerfectRow r (circulationRow S β N n) (circulationState S β N n) ε := by
  obtain ⟨hlow, hhigh⟩ := circulationState_param_mem β N hN hβ0 hβ1 hβN n
  exact isSupportPerfectRow_segmentPoint r floor M hM0 hM _ _ _ _ _
    (hβ0 _) (hβ1 _) (C.ratio_lt_one _) hlow hhigh (C.vertex_ge_floor _)
    (circulation_edge_ge_floor S _) (S.vertex_pinned_owner _) C.solo_le_floor ε (hε _)

/-- The same rows satisfy the weighted condition. -/
theorem isWeightedRow_circulation (S : SingletonSupport C) (β : ZMod L → ℝ) (N : ℕ)
    (hN : 0 < N) (hβ0 : ∀ l, 0 ≤ β l) (hβ1 : ∀ l, β l ≤ 1) (hβN : ∀ l, β l ^ N = C.ratio l)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S' j, |r S' j| ≤ M) (ε : ℝ)
    (hε : ∀ l, 2 * M * (1 - β l) ≤ ε) (n : ℕ) :
    IsWeightedRow r (circulationRow S β N n) (circulationState S β N n) ε := by
  have hrow := isSupportPerfectRow_circulation S β N hN hβ0 hβ1 hβN M hM0 hM ε hε n
  have hε0 : 0 ≤ ε := le_trans (by
    have := hβ1 (phaseSchedule L N n).1
    positivity) (hε (phaseSchedule L N n).1)
  exact isWeightedRow_of_isSupportPerfectRow r _ _ _
    (fun j => (singletonRow_mem_unitInterval _ (by linarith [hβ1 (phaseSchedule L N n).1])
      (by linarith [hβ0 (phaseSchedule L N n).1]) _ j).1)
    (fun j => (singletonRow_mem_unitInterval _ (by linarith [hβ1 (phaseSchedule L N n).1])
      (by linarith [hβ0 (phaseSchedule L N n).1]) _ j).2)
    hε0 hrow

/-! ## Quit mass -/

/-- The quit mass of a chain microstep is its hazard. -/
theorem quitMass_circulationRow (S : SingletonSupport C) (β : ZMod L → ℝ) (N : ℕ) (n : ℕ) :
    1 - continueMass (circulationRow S β N n) = 1 - β (phaseSchedule L N n).1 :=
  quitMass_singletonRow _ _

/-- **The prefix quit mass grows linearly.**  With every phase hazard at
least `1 - b`, the first `T` microsteps release at least `T (1 - b)` of quit
mass. -/
theorem quitMass_prefix_ge (S : SingletonSupport C) (β : ZMod L → ℝ) (N : ℕ) (b : ℝ)
    (hb : ∀ l, β l ≤ b) (T : ℕ) :
    (T : ℝ) * (1 - b) ≤
      ∑ n ∈ Finset.range T, (1 - continueMass (circulationRow S β N n)) := by
  have hterm : ∀ n ∈ Finset.range T,
      (1 - b) ≤ 1 - continueMass (circulationRow S β N n) := by
    intro n _
    rw [quitMass_circulationRow]
    linarith [hb (phaseSchedule L N n).1]
  calc (T : ℝ) * (1 - b) = ∑ _n ∈ Finset.range T, (1 - b) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hterm

/-- **Orbits of unbounded quit mass** (the goal of the construction): for
every target `Q`, a long enough prefix of the chain releases quit mass at
least `Q`, while every one of its rows stays support-perfect at tolerance
`ε` and every one of its states stays above the floor.

Nothing in the statement or its proof uses a motion constant: the quit mass
is produced directly, which is what the downstream compiler consumes. -/
theorem exists_prefix_quitMass_ge (S : SingletonSupport C) (β : ZMod L → ℝ) (N : ℕ)
    (b : ℝ) (hb : ∀ l, β l ≤ b) (hb1 : b < 1) (Q : ℝ) :
    ∃ T : ℕ, Q ≤ ∑ n ∈ Finset.range T, (1 - continueMass (circulationRow S β N n)) := by
  obtain ⟨T, hT⟩ := exists_nat_ge (Q / (1 - b))
  refine ⟨T, le_trans ?_ (quitMass_prefix_ge S β N b hb T)⟩
  rw [div_le_iff₀ (by linarith)] at hT
  linarith

/-! ## Hazards of prescribed smallness -/

/-- **A phase can be discretised at any prescribed hazard budget.**  For a
contraction ratio `α ∈ (0,1)` and a budget `H > 0` there is a phase length
`N` and a survival factor `β` with `β ^ N = α` and hazard `1 - β ≤ H`.  This
is the only place the construction leaves the rationals: `β = α ^ (1/N)`. -/
theorem exists_pow_eq_and_one_sub_le (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (H : ℝ)
    (hH0 : 0 < H) :
    ∃ (N : ℕ) (β : ℝ), 0 < N ∧ 0 ≤ β ∧ β < 1 ∧ β ^ N = α ∧ 1 - β ≤ H := by
  set c : ℝ := 1 - min H (1 / 2) with hc
  have hmin0 : 0 < min H (1 / 2) := lt_min hH0 (by norm_num)
  have hmin2 : min H (1 / 2) ≤ 1 / 2 := min_le_right _ _
  have hc0 : 0 ≤ c := by simp only [hc]; linarith
  have hc1 : c < 1 := by simp only [hc]; linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hα0 hc1
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hN
    linarith
  refine ⟨N, α ^ ((N : ℝ)⁻¹), Nat.pos_of_ne_zero hN0, Real.rpow_nonneg hα0.le _, ?_, ?_, ?_⟩
  · by_contra hcon
    have h1 : (1 : ℝ) ≤ α ^ ((N : ℝ)⁻¹) := not_lt.mp hcon
    have h2 : (1 : ℝ) ≤ (α ^ ((N : ℝ)⁻¹)) ^ N := one_le_pow₀ h1
    rw [Real.rpow_inv_natCast_pow hα0.le hN0] at h2
    linarith
  · exact Real.rpow_inv_natCast_pow hα0.le hN0
  · have hlt : c ^ N < (α ^ ((N : ℝ)⁻¹)) ^ N := by
      rw [Real.rpow_inv_natCast_pow hα0.le hN0]
      exact hN
    have hcb : c < α ^ ((N : ℝ)⁻¹) :=
      lt_of_pow_lt_pow_left₀ N (Real.rpow_nonneg hα0.le _) hlt
    have := min_le_left H (1 / 2)
    simp only [hc] at hcb
    linarith

/-! ## The calibrated orbit -/

/-- The calibration certificate, presented with its point-mass supports. -/
def cyclicCirculationSupport : SingletonSupport cyclicCirculation where
  owner := cyclicCirculationOwner
  mixWeight_eq := fun _ => rfl

/-- **Orbits of arbitrarily large quit mass for the scaled cyclic weight.**
For every tolerance `ε > 0` and every target quit mass `Q` there is a
discretisation of the calibration cycle whose every microstep row is
support-perfect at tolerance `ε` against its own state, whose every state
stays at or above the solo floor `1/3`, whose states obey the one-stage
recursion, and a finite prefix of which has quit mass at least `Q`.

No motion constant is used anywhere: quit mass is produced directly. -/
theorem exists_cyclicCirculation_orbit (ε : ℝ) (hε : 0 < ε) (Q : ℝ) :
    ∃ (N : ℕ) (β : ZMod 3 → ℝ), 0 < N ∧
      (∀ n j, circulationState cyclicCirculationSupport β N (n + 1) j =
        oneStageNext scaledCyclicWeight (circulationRow cyclicCirculationSupport β N n)
          (circulationState cyclicCirculationSupport β N n) j) ∧
      (∀ n, IsSupportPerfectRow scaledCyclicWeight
        (circulationRow cyclicCirculationSupport β N n)
        (circulationState cyclicCirculationSupport β N n) ε) ∧
      (∀ n j, cyclicCirculationFloor j ≤
        circulationState cyclicCirculationSupport β N n j) ∧
      ∃ T : ℕ, Q ≤ ∑ n ∈ Finset.range T,
        (1 - continueMass (circulationRow cyclicCirculationSupport β N n)) := by
  obtain ⟨N, b, hN, hb0, hb1, hbN, hbH⟩ :=
    exists_pow_eq_and_one_sub_le (1 / 2) (by norm_num) (by norm_num) (ε / 2) (by linarith)
  have hratio : ∀ l : ZMod 3, (fun _ : ZMod 3 => b) l ^ N = cyclicCirculation.ratio l :=
    fun _ => hbN
  have hb1' : ∀ l : ZMod 3, (fun _ : ZMod 3 => b) l ≤ 1 := fun _ => hb1.le
  have hb0' : ∀ l : ZMod 3, 0 ≤ (fun _ : ZMod 3 => b) l := fun _ => hb0
  refine ⟨N, fun _ => b, hN, ?_, ?_, ?_, ?_⟩
  · exact fun n j => circulationState_succ cyclicCirculationSupport _ N hN hratio n j
  · exact fun n => isSupportPerfectRow_circulation cyclicCirculationSupport _ N hN hb0' hb1'
      hratio 1 (by norm_num) abs_scaledCyclicWeight_le_one ε (fun _ => by linarith) n
  · exact fun n j => circulationState_ge_floor cyclicCirculationSupport _ N hN hb0' hb1'
      hratio n j
  · exact exists_prefix_quitMass_ge cyclicCirculationSupport _ N b (fun _ => le_rfl) hb1 Q

end GameTheory
