/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Circulation.SingletonFaceCirculationOrbit

/-!
# Multi-owner face circulations steer orbits

`SingletonFaceCirculationOrbit.lean` glues a face-circulation certificate
into an orbit of unbounded quit mass when every phase mixture `λ^ℓ` is a
point mass.  This file removes that restriction: the phases may have
arbitrary support, and the microstep owners inside a phase are chosen by a
**balanced owner word**.

## The three moving parts

* **Balanced words.**  `balancedWord` emits, at each step, a support
  coordinate whose running deficit `T λ_i - N_i(T)` is nonnegative.  The
  deficits sum to zero, vanish off the support and never fall below `-1`
  (`mixDeficit_invariant`), so the total absolute deficit is at most
  `2 (s - 1)` (`mixDeficit_abs_sum_le`) and the word's drift against its own
  target is at most `B = 2 M (s - 1)` (`abs_wordDrift_balancedWord_le`).
* **The envelope.**  The actual chain deviates from the ideal segment, but
  the deviation *corrected by the outstanding word drift* obeys
  `P ↦ β P - (1-β)² G` inside a phase and pays the full-phase drift once at a
  boundary.  The envelope `β^t K + (1-β) B (1 - β^t)` is carried exactly
  (`envelope_step_within`, `envelope_step_boundary`,
  `abs_multiCorrected_le`), so the chain never leaves a `K + H B`
  neighbourhood of the ideal cycle (`abs_multiActual_sub_multiIdeal_le`).
* **The one-stage inequalities.**  Approximate pinning suffices:
  `isSupportPerfectRow_singletonRow_approx` gives support-perfection at
  tolerance `E + 2 M h` from `|rest_i - d_i| ≤ E` and `d_k - E ≤ rest_k`.

## The recomputed tolerance

The argument this file formalizes was first derived with the tolerance

`H ≤ ε / (2M + 6MC/(1-A))`, `C = ∑_ℓ |J_ℓ|(|J_ℓ|+1)`, `A = ∏_ℓ α_ℓ`.

The condition actually needed is `K + H B + 2 M H ≤ ε`, and it is met by
`K = 2 H B/(1-a)` with `B = 2M(s-1)`, `a = max_ℓ α_ℓ` and `s` a bound on the
support sizes -- that is, by

`H (2M + 2M(s-1)(3-a)/(1-a)) ≤ ε`.

Two things change.  The imbalance constant is `2M(s-1)` rather than
`M s(s+1)`: the greedy word's deficits are bounded below by `-1` and at least
one support coordinate has none, so at most `s - 1` of them carry a unit
deficit.  And no macrocycle product `A` is needed at all: each phase
contracts by its own `α_ℓ`, so a *uniform* steady-state level `K` exists as
soon as `α_ℓ K + (1-β_ℓ) B (2 - α_ℓ) ≤ K` phase by phase.  At `s = 1` the
imbalance constant is `0`, hence `K = 0` and the condition is exactly
`2 M H ≤ ε`, the singleton file's recomputed tolerance -- so the published
bound's second summand is spurious there, as that file already found by
direct computation.  (The witness constructed in
`exists_multiCirculation_orbit` divides by `2M + 2M(s-1)(3-a)/(1-a) + 1`
instead, the `+ 1` only to keep the quotient defined at `M = 0`.)

## Where the support size enters

Only through `B = 2 M (s - 1)`, and `B` enters the tolerance only through
`K + H B`.  The pinning clause of the certificate
(`vertex_pinned`, `target_pinned`) is what makes the owner's own gain
`d_i - R_i` small: the ideal segment is exactly `d_i` at every owner of the
phase (`multiIdeal_pinned`), so the owner's gain is bounded by the tracking
error alone, with no reward swing.

## Contents

* `mixSupport`, `deficitPick`, `mixDeficit`, `balancedWord`,
  `mixDeficit_invariant`, `balancedWord_mem_support`,
  `mixDeficit_abs_sum_le` -- deliverable 1.
* `wordDrift`, `wordDrift_balancedWord`, `abs_wordDrift_balancedWord_le` --
  the imbalance bookkeeping.
* `isSupportPerfectRow_singletonRow_approx`, `multiIdeal_pinned`,
  `isSupportPerfectRow_multi` -- deliverable 2, the multi-owner one-phase
  step.
* `multiRow`, `multiActual`, `multiIdeal`, `multiCorrected`,
  `abs_multiCorrected_le`, `multiActual_ge_floor_sub`,
  `exists_prefix_quitMass_multi_ge`, `exists_multiCirculation_orbit`,
  `exists_multiCirculation_orbit_of_singletonSupport` -- deliverable 3.

## Scope

As in the singleton file the floor vector is abstract; `solo_le_floor` is
the part of the intended reading `r̲_i = max{d_i, χ_i}` that the microsteps
consume, and the min-max level `χ` is not formalized.  Feasibility of the
states is inherited from the certificate's vertices and is not re-derived.
The chain runs forward, `R_{n+1} = f(R_n, x_n)`; reversing a finite prefix
gives the backward orbit convention of the source question.
-/

noncomputable section

namespace GameTheory

open Finset Math.PMFProduct

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Balanced owner words -/

/-- The support of a mixing distribution. -/
def mixSupport (lam : ι → ℝ) : Finset ι := Finset.univ.filter fun i => 0 < lam i

omit [DecidableEq ι] in
theorem mem_mixSupport {lam : ι → ℝ} {i : ι} : i ∈ mixSupport lam ↔ 0 < lam i := by
  simp [mixSupport]

omit [DecidableEq ι] in
/-- The support of a distribution is nonempty. -/
theorem mixSupport_nonempty (lam : ι → ℝ) (hlam0 : ∀ i, 0 ≤ lam i) (hlam1 : ∑ i, lam i = 1) :
    (mixSupport lam).Nonempty := by
  rcases Finset.eq_empty_or_nonempty (mixSupport lam) with hemp | h
  · exfalso
    have hzero : ∀ i ∈ (Finset.univ : Finset ι), lam i = 0 := by
      intro i _
      by_contra hi
      have hmem : i ∈ mixSupport lam :=
        mem_mixSupport.mpr (lt_of_le_of_ne (hlam0 i) (Ne.symm hi))
      rw [hemp] at hmem
      exact absurd hmem (Finset.notMem_empty i)
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hlam1
    exact absurd hlam1 (by norm_num)
  · exact h

omit [DecidableEq ι] in
/-- **Some support coordinate carries a nonnegative deficit.**  The deficits
sum to zero and vanish off the support, so their maximum over the (nonempty)
support cannot be negative. -/
theorem exists_nonneg_of_sum_eq_zero (lam e : ι → ℝ) (hlam0 : ∀ i, 0 ≤ lam i)
    (hlam1 : ∑ i, lam i = 1) (hsum : ∑ i, e i = 0) (hoff : ∀ i, lam i = 0 → e i = 0) :
    ∃ k, 0 < lam k ∧ 0 ≤ e k := by
  have hne := mixSupport_nonempty lam hlam0 hlam1
  have hsumS : ∑ i ∈ mixSupport lam, e i = 0 := by
    rw [Finset.sum_subset (Finset.subset_univ _) ?_, hsum]
    intro i _ hi
    exact hoff i (le_antisymm (not_lt.mp fun hc => hi (mem_mixSupport.mpr hc)) (hlam0 i))
  by_contra hc
  have hneg : ∀ i ∈ mixSupport lam, e i < (fun _ : ι => (0 : ℝ)) i := by
    intro i hi
    by_contra hc2
    exact hc ⟨i, mem_mixSupport.mp hi, not_lt.mp hc2⟩
  have hlt := Finset.sum_lt_sum_of_nonempty hne hneg
  rw [hsumS, Finset.sum_const_zero] at hlt
  exact absurd hlt (lt_irrefl 0)

omit [Fintype ι] [DecidableEq ι] in
/-- The choice underlying the greedy word: a support coordinate of
nonnegative deficit whenever one exists. -/
theorem exists_deficitPick [Nonempty ι] (lam e : ι → ℝ) :
    ∃ i : ι, (∃ k, 0 < lam k ∧ 0 ≤ e k) → 0 < lam i ∧ 0 ≤ e i := by
  by_cases h : ∃ k, 0 < lam k ∧ 0 ≤ e k
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, fun _ => hk⟩
  · exact ⟨Classical.arbitrary ι, fun hc => absurd hc h⟩

/-- The letter the greedy word emits at deficit vector `e`. -/
def deficitPick [Nonempty ι] (lam e : ι → ℝ) : ι := Classical.choose (exists_deficitPick lam e)

omit [Fintype ι] [DecidableEq ι] in
/-- The greedy letter is a support coordinate of nonnegative deficit. -/
theorem deficitPick_spec [Nonempty ι] (lam e : ι → ℝ) (h : ∃ k, 0 < lam k ∧ 0 ≤ e k) :
    0 < lam (deficitPick lam e) ∧ 0 ≤ e (deficitPick lam e) :=
  Classical.choose_spec (exists_deficitPick lam e) h

/-- The running deficit `T λ_i - N_i(T)` of the greedy balanced word. -/
def mixDeficit [Nonempty ι] (lam : ι → ℝ) : ℕ → ι → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun i =>
      mixDeficit lam n i + lam i -
        (if i = deficitPick lam (mixDeficit lam n) then 1 else 0)

/-- **The greedy balanced word**: at every step emit a support letter whose
running deficit is nonnegative. -/
def balancedWord [Nonempty ι] (lam : ι → ℝ) (n : ℕ) : ι := deficitPick lam (mixDeficit lam n)

omit [Fintype ι] in
@[simp] theorem mixDeficit_zero [Nonempty ι] (lam : ι → ℝ) (i : ι) :
    mixDeficit lam 0 i = 0 := rfl

omit [Fintype ι] in
/-- The deficit recursion: every coordinate gains its own weight, and the
emitted letter pays one. -/
theorem mixDeficit_succ [Nonempty ι] (lam : ι → ℝ) (n : ℕ) (i : ι) :
    mixDeficit lam (n + 1) i =
      mixDeficit lam n i + lam i - (if i = balancedWord lam n then 1 else 0) := rfl

/-- **The deficit invariant.**  Along the greedy word the deficits sum to
zero, vanish off the support, and never fall below `-1`. -/
theorem mixDeficit_invariant [Nonempty ι] (lam : ι → ℝ) (hlam0 : ∀ i, 0 ≤ lam i)
    (hlam1 : ∑ i, lam i = 1) (n : ℕ) :
    (∑ i, mixDeficit lam n i = 0) ∧ (∀ i, lam i = 0 → mixDeficit lam n i = 0) ∧
      (∀ i, -1 ≤ mixDeficit lam n i) := by
  induction n with
  | zero => exact ⟨by simp, fun _ _ => rfl, fun i => by norm_num⟩
  | succ n ih =>
      obtain ⟨hsum, hoff, hlow⟩ := ih
      obtain ⟨hppos, hpnonneg⟩ :
          0 < lam (balancedWord lam n) ∧ 0 ≤ mixDeficit lam n (balancedWord lam n) :=
        deficitPick_spec lam (mixDeficit lam n)
          (exists_nonneg_of_sum_eq_zero lam _ hlam0 hlam1 hsum hoff)
      refine ⟨?_, ?_, ?_⟩
      · rw [Finset.sum_congr rfl (fun i _ => mixDeficit_succ lam n i),
          Finset.sum_sub_distrib, Finset.sum_add_distrib, hsum, hlam1,
          Finset.sum_ite_eq' Finset.univ (balancedWord lam n) (fun _ => (1 : ℝ))]
        simp
      · intro i hi
        have hne : i ≠ balancedWord lam n := fun hcon => by
          rw [hcon] at hi; exact absurd hi (ne_of_gt hppos)
        rw [mixDeficit_succ, if_neg hne, hoff i hi, hi]
        ring
      · intro i
        rw [mixDeficit_succ]
        by_cases hi : i = balancedWord lam n
        · rw [if_pos hi, hi]
          linarith [hlam0 (balancedWord lam n)]
        · rw [if_neg hi]
          linarith [hlam0 i, hlow i]

/-- **Every letter of the greedy word lies in the support**, so the word is
usable as an owner word for the phase. -/
theorem balancedWord_mem_support [Nonempty ι] (lam : ι → ℝ) (hlam0 : ∀ i, 0 ≤ lam i)
    (hlam1 : ∑ i, lam i = 1) (n : ℕ) : 0 < lam (balancedWord lam n) := by
  obtain ⟨hsum, hoff, _⟩ := mixDeficit_invariant lam hlam0 hlam1 n
  exact (deficitPick_spec lam (mixDeficit lam n)
    (exists_nonneg_of_sum_eq_zero lam _ hlam0 hlam1 hsum hoff)).1

/-- **The imbalance lemma**: the total absolute deficit of the greedy word
never exceeds `2 (s - 1)`, where `s` is the support size.  At `s = 1` the
bound is `0`: a one-letter alphabet is exactly balanced.

The proof is the two-line one.  The deficits sum to zero, so the total
absolute deficit is twice the total negative part; every negative part is
below `1` by the invariant, and at least one support coordinate has none. -/
theorem mixDeficit_abs_sum_le [Nonempty ι] (lam : ι → ℝ) (hlam0 : ∀ i, 0 ≤ lam i)
    (hlam1 : ∑ i, lam i = 1) (n : ℕ) :
    ∑ i, |mixDeficit lam n i| ≤ 2 * (((mixSupport lam).card : ℝ) - 1) := by
  obtain ⟨hsum, hoff, hlow⟩ := mixDeficit_invariant lam hlam0 hlam1 n
  obtain ⟨i₀, hi₀lam, hi₀def⟩ := exists_nonneg_of_sum_eq_zero lam _ hlam0 hlam1 hsum hoff
  have hi₀mem : i₀ ∈ mixSupport lam := mem_mixSupport.mpr hi₀lam
  have habs : ∀ i ∈ (Finset.univ : Finset ι), |mixDeficit lam n i| =
      mixDeficit lam n i + 2 * max 0 (-mixDeficit lam n i) := by
    intro i _
    rcases le_total 0 (mixDeficit lam n i) with h | h
    · rw [abs_of_nonneg h, max_eq_left (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_right (by linarith)]; ring
  have hsplit : ∑ i, |mixDeficit lam n i| = 2 * ∑ i, max 0 (-mixDeficit lam n i) := by
    rw [Finset.sum_congr rfl habs, Finset.sum_add_distrib, hsum, ← Finset.mul_sum]
    ring
  have hsub : ∑ i ∈ mixSupport lam, max 0 (-mixDeficit lam n i) =
      ∑ i, max 0 (-mixDeficit lam n i) := by
    refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => ?_
    have hlam : lam i = 0 :=
      le_antisymm (not_lt.mp fun hc => hi (mem_mixSupport.mpr hc)) (hlam0 i)
    rw [hoff i hlam]
    simp
  have hone : 1 ≤ (mixSupport lam).card := Finset.card_pos.mpr ⟨i₀, hi₀mem⟩
  have hbound : ∑ i ∈ (mixSupport lam).erase i₀, max 0 (-mixDeficit lam n i) ≤
      ((((mixSupport lam).erase i₀).card : ℝ)) * 1 := by
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ 1 fun i _ => ?_
    rcases le_total 0 (-mixDeficit lam n i) with h | h
    · rw [max_eq_right h]; linarith [hlow i]
    · rw [max_eq_left h]; norm_num
  rw [Finset.card_erase_of_mem hi₀mem, Nat.cast_sub hone] at hbound
  have hneg : ∑ i, max 0 (-mixDeficit lam n i) ≤ ((mixSupport lam).card : ℝ) - 1 := by
    rw [← hsub, ← Finset.add_sum_erase _ _ hi₀mem, max_eq_left (by linarith)]
    push_cast at hbound
    linarith
  rw [hsplit]
  linarith

/-! ## The drift of a word against its mixed target -/

/-- The accumulated drift of the first `T` letters of a word against the
phase target `u = ∑_i λ_i w({i})`. -/
def wordDrift (r : Finset ι → ι → ℝ) (lam : ι → ℝ) (word : ℕ → ι) (T : ℕ) (j : ι) : ℝ :=
  ∑ t ∈ Finset.range T, (r {word t} j - mixTarget r lam j)

omit [DecidableEq ι] in
@[simp] theorem wordDrift_zero (r : Finset ι → ι → ℝ) (lam : ι → ℝ) (word : ℕ → ι) (j : ι) :
    wordDrift r lam word 0 j = 0 := by simp [wordDrift]

omit [DecidableEq ι] in
/-- The drift's own recursion. -/
theorem wordDrift_succ (r : Finset ι → ι → ℝ) (lam : ι → ℝ) (word : ℕ → ι) (T : ℕ) (j : ι) :
    wordDrift r lam word (T + 1) j =
      wordDrift r lam word T j + (r {word T} j - mixTarget r lam j) := by
  unfold wordDrift
  rw [Finset.sum_range_succ]

/-- **The drift of the greedy word is the deficit-weighted solo mixture.**
This is the bookkeeping identity behind the imbalance estimate: the drift
after `T` letters records exactly the deficits `T λ_i - N_i(T)`. -/
theorem wordDrift_balancedWord [Nonempty ι] (r : Finset ι → ι → ℝ) (lam : ι → ℝ)
    (T : ℕ) (j : ι) :
    wordDrift r lam (balancedWord lam) T j = -∑ i, mixDeficit lam T i * r {i} j := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hexp : ∀ i ∈ (Finset.univ : Finset ι), mixDeficit lam (T + 1) i * r {i} j =
          mixDeficit lam T i * r {i} j + lam i * r {i} j -
            (if i = balancedWord lam T then r {i} j else 0) := by
        intro i _
        rw [mixDeficit_succ]
        by_cases hi : i = balancedWord lam T
        · rw [if_pos hi, if_pos hi]; ring
        · rw [if_neg hi, if_neg hi]; ring
      rw [wordDrift_succ, ih, Finset.sum_congr rfl hexp, Finset.sum_sub_distrib,
        Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ (balancedWord lam T) (fun i => r {i} j)]
      have hmix : ∑ i, lam i * r {i} j = mixTarget r lam j := rfl
      rw [hmix]
      simp
      ring

/-- **The imbalance bound on the drift.**  The greedy word's drift against
its own target never exceeds `2 M (s - 1)` in absolute value, with `s` the
support size and `M` the reward bound.

This is the recomputed form of the source argument's `M s (s+1)`: at `s = 1`
it is `0`, matching the exact singleton computation, and it is smaller than
`M s (s+1)` at every support size. -/
theorem abs_wordDrift_balancedWord_le [Nonempty ι] (r : Finset ι → ι → ℝ) (lam : ι → ℝ)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M) (hlam0 : ∀ i, 0 ≤ lam i)
    (hlam1 : ∑ i, lam i = 1) (T : ℕ) (j : ι) :
    |wordDrift r lam (balancedWord lam) T j| ≤
      2 * M * (((mixSupport lam).card : ℝ) - 1) := by
  rw [wordDrift_balancedWord, abs_neg]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      |mixDeficit lam T i * r {i} j| ≤ M * |mixDeficit lam T i| := by
    intro i _
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hM {i} j) (abs_nonneg _)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left (mixDeficit_abs_sum_le lam hlam0 hlam1 T) hM0]

/-! ## The one-stage inequalities at an approximately pinned state -/

/-- **The support-perfect condition at an approximately pinned state.**  If
the owner's coordinate sits within `E` of its solo value and no coordinate is
more than `E` below its own solo value, then the singleton row `h e_i` is
support-perfect at tolerance `E + 2 M h`.

This is the multi-owner replacement for `isSupportPerfectRow_singletonRow`,
whose hypotheses are the `E = 0` case: with two or more owners in a phase the
actual state only tracks the pinned ideal segment up to the word-imbalance
error `E`. -/
theorem isSupportPerfectRow_singletonRow_approx (r : Finset ι → ι → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ S j, |r S j| ≤ M) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (i : ι) (rest : ι → ℝ)
    (E : ℝ) (hE0 : 0 ≤ E) (hpin : |rest i - r {i} i| ≤ E)
    (hsolo : ∀ k, r {k} k - E ≤ rest k) (ε : ℝ) (hε : E + 2 * M * h ≤ ε) :
    IsSupportPerfectRow r (singletonRow h i) rest ε := by
  have hMh : 0 ≤ 2 * M * h := by positivity
  intro j
  by_cases hj : j = i
  · subst hj
    rw [gainValue_singletonRow_self]
    obtain ⟨hlo, hhi⟩ := abs_le.mp hpin
    exact ⟨fun _ => by linarith, fun _ => by linarith⟩
  · rw [gainValue_singletonRow_of_ne r h hj]
    refine ⟨fun hpos => absurd hpos ?_, fun _ => ?_⟩
    · rw [singletonRow_of_ne h hj]
      exact lt_irrefl 0
    · have hswing : r {j, i} j - r {i} j ≤ 2 * M := by
        have h1 := abs_le.mp (hM {j, i} j)
        have h2 := abs_le.mp (hM {i} j)
        linarith [h1.2, h2.1]
      have hgap : r {j} j - rest j ≤ E := by linarith [hsolo j]
      have hslack : (0 : ℝ) ≤ E - (r {j} j - rest j) := by linarith
      nlinarith [mul_nonneg hh0 (by linarith : (0 : ℝ) ≤ 2 * M - (r {j, i} j - r {i} j)),
        mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - h) hslack]

/-! ## The glued multi-owner chain -/

variable {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]

/-- The phase index at chain position `n`. -/
def chainPhase (L : ℕ) [NeZero L] (N n : ℕ) : ZMod L := (phaseSchedule L N n).1

/-- The number of microsteps already spent in the current phase. -/
def chainStep (L : ℕ) [NeZero L] (N n : ℕ) : ℕ := (phaseSchedule L N n).2

@[simp] theorem chainPhase_zero (L : ℕ) [NeZero L] (N : ℕ) : chainPhase L N 0 = 0 := rfl

@[simp] theorem chainStep_zero (L : ℕ) [NeZero L] (N : ℕ) : chainStep L N 0 = 0 := rfl

/-- Inside a phase the schedule keeps the phase and advances the counter. -/
theorem chain_succ_of_lt (L : ℕ) [NeZero L] (N n : ℕ) (hlt : chainStep L N n + 1 < N) :
    chainPhase L N (n + 1) = chainPhase L N n ∧ chainStep L N (n + 1) = chainStep L N n + 1 := by
  unfold chainPhase chainStep at *
  rw [phaseSchedule_succ, if_pos hlt]
  exact ⟨rfl, rfl⟩

/-- At a phase boundary the schedule advances the phase and resets the
counter. -/
theorem chain_succ_of_boundary (L : ℕ) [NeZero L] (N n : ℕ) (hlt : ¬ chainStep L N n + 1 < N) :
    chainPhase L N (n + 1) = chainPhase L N n + 1 ∧ chainStep L N (n + 1) = 0 := by
  unfold chainPhase chainStep at *
  rw [phaseSchedule_succ, if_neg hlt]
  exact ⟨rfl, rfl⟩

/-- The microstep row at chain position `n`: the current phase's owner word
letter quits with the phase hazard `1 - β_ℓ`. -/
def multiRow (word : ZMod L → ℕ → ι) (β : ZMod L → ℝ) (N n : ℕ) : ι → ℝ :=
  singletonRow (1 - β (chainPhase L N n)) (word (chainPhase L N n) (chainStep L N n))

/-- **The actual chain**: start at the certificate's first vertex and apply
the one-stage successor at every microstep row. -/
def multiActual (C : FaceCirculationCertificate r floor L) (word : ZMod L → ℕ → ι)
    (β : ZMod L → ℝ) (N : ℕ) : ℕ → ι → ℝ
  | 0 => C.vertex 0
  | n + 1 => oneStageNext r (multiRow word β N n) (multiActual C word β N n)

/-- **The ideal chain**: the point of the current phase's ideal edge reached
after the microsteps already spent, the edge running from the phase vertex to
the phase's *mixed* target. -/
def multiIdeal (C : FaceCirculationCertificate r floor L) (β : ZMod L → ℝ) (N n : ℕ) : ι → ℝ :=
  segmentPoint (C.vertex (chainPhase L N n))
    (mixTarget r (C.mixWeight (chainPhase L N n))) (β (chainPhase L N n) ^ chainStep L N n)

/-- The actual chain obeys the one-stage recursion by construction. -/
theorem multiActual_succ (C : FaceCirculationCertificate r floor L) (word : ZMod L → ℕ → ι)
    (β : ZMod L → ℝ) (N n : ℕ) :
    multiActual C word β N (n + 1) =
      oneStageNext r (multiRow word β N n) (multiActual C word β N n) := rfl

/-- The actual chain in closed form: a microstep moves the state a fraction
`1 - β_ℓ` of the way towards the emitted letter's solo row. -/
theorem multiActual_succ_apply (C : FaceCirculationCertificate r floor L)
    (word : ZMod L → ℕ → ι) (β : ZMod L → ℝ) (N n : ℕ) (j : ι) :
    multiActual C word β N (n + 1) j =
      β (chainPhase L N n) * multiActual C word β N n j +
        (1 - β (chainPhase L N n)) *
          r {word (chainPhase L N n) (chainStep L N n)} j := by
  rw [multiActual_succ]
  unfold multiRow
  rw [oneStageNext_singletonRow]
  ring

omit [DecidableEq ι] in
/-- **The ideal chain obeys the averaged recursion**, globally: inside a
phase it is the geometric traversal of the ideal edge, and at a boundary the
certificate's own convex step closes it on the next vertex. -/
theorem multiIdeal_succ_apply (C : FaceCirculationCertificate r floor L) (β : ZMod L → ℝ)
    (N : ℕ) (hN : 0 < N) (hβN : ∀ l, β l ^ N = C.ratio l) (n : ℕ) (j : ι) :
    multiIdeal C β N (n + 1) j =
      β (chainPhase L N n) * multiIdeal C β N n j +
        (1 - β (chainPhase L N n)) * mixTarget r (C.mixWeight (chainPhase L N n)) j := by
  have hb : chainStep L N n < N := phaseSchedule_snd_lt L N hN n
  unfold multiIdeal
  by_cases hlt : chainStep L N n + 1 < N
  · obtain ⟨hp, hs⟩ := chain_succ_of_lt L N n hlt
    rw [hp, hs, pow_succ]
    unfold segmentPoint
    ring
  · obtain ⟨hp, hs⟩ := chain_succ_of_boundary L N n hlt
    have hlen : chainStep L N n + 1 = N := by omega
    have hpowN : β (chainPhase L N n) ^ chainStep L N n * β (chainPhase L N n) =
        C.ratio (chainPhase L N n) := by
      rw [← pow_succ, hlen]
      exact hβN _
    have hstep := C.step (chainPhase L N n) j
    rw [hp, hs, pow_zero]
    unfold segmentPoint
    rw [hstep]
    linear_combination
      (mixTarget r (C.mixWeight (chainPhase L N n)) j - C.vertex (chainPhase L N n) j) * hpowN

/-- The chain's deviation from the ideal segment, corrected by the current
phase's accumulated word drift.  This corrected deviation, not the raw one,
is what contracts step by step. -/
def multiCorrected (C : FaceCirculationCertificate r floor L) (word : ZMod L → ℕ → ι)
    (β : ZMod L → ℝ) (N n : ℕ) (j : ι) : ℝ :=
  multiActual C word β N n j - multiIdeal C β N n j -
    (1 - β (chainPhase L N n)) *
      wordDrift r (C.mixWeight (chainPhase L N n)) (word (chainPhase L N n))
        (chainStep L N n) j

/-! ## The envelope of the corrected deviation -/

/-- **The envelope step inside a phase.**  The corrected deviation obeys
`P ↦ β P - (1-β)² G`, and the envelope `m K + (1-β) B (1 - m)` at segment
parameter `m` is carried to the envelope at `m β`.  The step is exact
because `β + (1 - β) = 1`; no slack is lost. -/
theorem envelope_step_within (b K B P G m : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hP : |P| ≤ m * K + (1 - b) * B * (1 - m)) (hG : |G| ≤ B) :
    |b * P - (1 - b) * (1 - b) * G| ≤ m * b * K + (1 - b) * B * (1 - m * b) := by
  obtain ⟨hPlo, hPhi⟩ := abs_le.mp hP
  obtain ⟨hGlo, hGhi⟩ := abs_le.mp hG
  refine abs_le.mpr ⟨?_, ?_⟩ <;>
    nlinarith [mul_nonneg hb0 (by linarith : (0 : ℝ) ≤ m * K + (1 - b) * B * (1 - m) - P),
      mul_nonneg hb0 (by linarith : (0 : ℝ) ≤ P + (m * K + (1 - b) * B * (1 - m))),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - b) (by linarith : (0 : ℝ) ≤ 1 - b))
        (by linarith : (0 : ℝ) ≤ B + G),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - b) (by linarith : (0 : ℝ) ≤ 1 - b))
        (by linarith : (0 : ℝ) ≤ B - G)]

/-- **The envelope step at a phase boundary.**  Here the full-phase drift
`F` is paid once, on top of the contraction by the phase ratio `α = m b`.
The resulting requirement on the steady-state level `K` is exactly
`α K + (1-β) B (2 - α) ≤ K`; the summand `2 - α` -- not the source
argument's macrocycle constant -- is what a boundary costs. -/
theorem envelope_step_boundary (b K B P G F m : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hP : |P| ≤ m * K + (1 - b) * B * (1 - m)) (hG : |G| ≤ B) (hF : |F| ≤ B)
    (hK : m * b * K + (1 - b) * B * (2 - m * b) ≤ K) :
    |b * P - (1 - b) * (1 - b) * G + (1 - b) * F| ≤ K := by
  obtain ⟨hPlo, hPhi⟩ := abs_le.mp hP
  obtain ⟨hGlo, hGhi⟩ := abs_le.mp hG
  obtain ⟨hFlo, hFhi⟩ := abs_le.mp hF
  refine abs_le.mpr ⟨?_, ?_⟩ <;>
    nlinarith [mul_nonneg hb0 (by linarith : (0 : ℝ) ≤ m * K + (1 - b) * B * (1 - m) - P),
      mul_nonneg hb0 (by linarith : (0 : ℝ) ≤ P + (m * K + (1 - b) * B * (1 - m))),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - b) (by linarith : (0 : ℝ) ≤ 1 - b))
        (by linarith : (0 : ℝ) ≤ B + G),
      mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - b) (by linarith : (0 : ℝ) ≤ 1 - b))
        (by linarith : (0 : ℝ) ≤ B - G),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - b) (by linarith : (0 : ℝ) ≤ B + F),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - b) (by linarith : (0 : ℝ) ≤ B - F)]

omit [DecidableEq ι] in
/-- The steady-state error level is nonnegative and dominates one phase's
hazard-weighted imbalance. -/
theorem multiError_bounds (C : FaceCirculationCertificate r floor L) (β : ZMod L → ℝ)
    (hβ1 : ∀ l, β l ≤ 1) (B K : ℝ) (hB0 : 0 ≤ B)
    (hK : ∀ l, C.ratio l * K + (1 - β l) * B * (2 - C.ratio l) ≤ K) :
    0 ≤ K ∧ ∀ l, (1 - β l) * B ≤ K := by
  have hK0 : 0 ≤ K := by
    have h0 := hK 0
    have hr0 := C.ratio_pos 0
    have hr1 := C.ratio_lt_one 0
    nlinarith [mul_nonneg (mul_nonneg (by linarith [hβ1 0] : (0 : ℝ) ≤ 1 - β 0) hB0)
      (by linarith : (0 : ℝ) ≤ 2 - C.ratio 0)]
  refine ⟨hK0, fun l => ?_⟩
  have hl := hK l
  have hr0 := C.ratio_pos l
  have hr1 := C.ratio_lt_one l
  nlinarith [mul_nonneg (by linarith [hβ1 l] : (0 : ℝ) ≤ 1 - β l) hB0]

/-- **The error invariant of the multi-owner chain.**  The corrected
deviation stays inside the phase's geometric envelope `β^t K + h B (1 - β^t)`
for the steady-state level `K`, where `h = 1 - β` is the phase hazard.

The two branches are the whole of the general estimate: inside a phase the
envelope is carried exactly, and at a boundary the full-phase drift is paid
once. -/
theorem abs_multiCorrected_le (C : FaceCirculationCertificate r floor L)
    (word : ZMod L → ℕ → ι) (β : ZMod L → ℝ) (N : ℕ) (hN : 0 < N)
    (hβ0 : ∀ l, 0 ≤ β l) (hβ1 : ∀ l, β l ≤ 1) (hβN : ∀ l, β l ^ N = C.ratio l)
    (B K : ℝ) (hB0 : 0 ≤ B)
    (hdrift : ∀ l T j, |wordDrift r (C.mixWeight l) (word l) T j| ≤ B)
    (hK : ∀ l, C.ratio l * K + (1 - β l) * B * (2 - C.ratio l) ≤ K)
    (n : ℕ) (j : ι) :
    |multiCorrected C word β N n j| ≤
      β (chainPhase L N n) ^ chainStep L N n * K +
        (1 - β (chainPhase L N n)) * B * (1 - β (chainPhase L N n) ^ chainStep L N n) := by
  obtain ⟨hK0, hKB⟩ := multiError_bounds C β hβ1 B K hB0 hK
  induction n with
  | zero =>
      have h0 : multiCorrected C word β N 0 j = 0 := by
        unfold multiCorrected multiIdeal
        rw [chainPhase_zero, chainStep_zero, pow_zero, segmentPoint_one, wordDrift_zero]
        change C.vertex 0 j - C.vertex 0 j - (1 - β 0) * 0 = 0
        ring
      rw [h0, chainPhase_zero, chainStep_zero, pow_zero]
      simpa using hK0
  | succ n ih =>
      have hb : chainStep L N n < N := phaseSchedule_snd_lt L N hN n
      have hold : multiCorrected C word β N n j =
          multiActual C word β N n j - multiIdeal C β N n j -
            (1 - β (chainPhase L N n)) *
              wordDrift r (C.mixWeight (chainPhase L N n)) (word (chainPhase L N n))
                (chainStep L N n) j := rfl
      by_cases hlt : chainStep L N n + 1 < N
      · obtain ⟨hp, hs⟩ := chain_succ_of_lt L N n hlt
        have hnew : multiCorrected C word β N (n + 1) j =
            β (chainPhase L N n) * multiCorrected C word β N n j -
              (1 - β (chainPhase L N n)) * (1 - β (chainPhase L N n)) *
                wordDrift r (C.mixWeight (chainPhase L N n)) (word (chainPhase L N n))
                  (chainStep L N n) j := by
          have e1 : multiCorrected C word β N (n + 1) j =
              multiActual C word β N (n + 1) j - multiIdeal C β N (n + 1) j -
                (1 - β (chainPhase L N n)) *
                  wordDrift r (C.mixWeight (chainPhase L N n)) (word (chainPhase L N n))
                    (chainStep L N n + 1) j := by
            unfold multiCorrected
            rw [hp, hs]
          rw [e1, hold, wordDrift_succ, multiActual_succ_apply,
            multiIdeal_succ_apply C β N hN hβN]
          ring
        rw [hnew, hp, hs, pow_succ]
        exact envelope_step_within _ K B _ _ _ (hβ0 _) (hβ1 _) ih (hdrift _ _ j)
      · obtain ⟨hp, hs⟩ := chain_succ_of_boundary L N n hlt
        have hlen : chainStep L N n + 1 = N := by omega
        have hpowN : β (chainPhase L N n) ^ chainStep L N n * β (chainPhase L N n) =
            C.ratio (chainPhase L N n) := by
          rw [← pow_succ, hlen]
          exact hβN _
        have hnew : multiCorrected C word β N (n + 1) j =
            β (chainPhase L N n) * multiCorrected C word β N n j -
              (1 - β (chainPhase L N n)) * (1 - β (chainPhase L N n)) *
                wordDrift r (C.mixWeight (chainPhase L N n)) (word (chainPhase L N n))
                  (chainStep L N n) j +
              (1 - β (chainPhase L N n)) *
                wordDrift r (C.mixWeight (chainPhase L N n)) (word (chainPhase L N n))
                  (chainStep L N n + 1) j := by
          have e1 : multiCorrected C word β N (n + 1) j =
              multiActual C word β N (n + 1) j - multiIdeal C β N (n + 1) j := by
            unfold multiCorrected
            rw [hp, hs, wordDrift_zero]
            ring
          rw [e1, hold, wordDrift_succ, multiActual_succ_apply,
            multiIdeal_succ_apply C β N hN hβN]
          ring
        rw [hnew, hp, hs, pow_zero]
        have hgoal : (1 : ℝ) * K + (1 - β (chainPhase L N n + 1)) * B * (1 - 1) = K := by ring
        rw [hgoal]
        exact envelope_step_boundary _ K B _ _ _ _ (hβ0 _) (hβ1 _) ih (hdrift _ _ j)
          (hdrift _ _ j) (by rw [hpowN]; exact hK _)


/-! ## Rationality and the one-stage inequalities along the chain -/

/-- **The chain tracks the ideal segment to within `K + H B`.**  The
corrected deviation is inside the envelope, which the phase hazard bound
flattens to `K`, and the outstanding word drift adds at most `H B`. -/
theorem abs_multiActual_sub_multiIdeal_le (C : FaceCirculationCertificate r floor L)
    (word : ZMod L → ℕ → ι) (β : ZMod L → ℝ) (N : ℕ) (hN : 0 < N)
    (hβ0 : ∀ l, 0 ≤ β l) (hβ1 : ∀ l, β l ≤ 1) (hβN : ∀ l, β l ^ N = C.ratio l)
    (B K H : ℝ) (hB0 : 0 ≤ B)
    (hdrift : ∀ l T j, |wordDrift r (C.mixWeight l) (word l) T j| ≤ B)
    (hK : ∀ l, C.ratio l * K + (1 - β l) * B * (2 - C.ratio l) ≤ K)
    (hH : ∀ l, 1 - β l ≤ H) (n : ℕ) (j : ι) :
    |multiActual C word β N n j - multiIdeal C β N n j| ≤ K + H * B := by
  obtain ⟨hK0, hKB⟩ := multiError_bounds C β hβ1 B K hB0 hK
  have hmain := abs_multiCorrected_le C word β N hN hβ0 hβ1 hβN B K hB0 hdrift hK n j
  have hdr := hdrift (chainPhase L N n) (chainStep L N n) j
  have hpow0 : 0 ≤ β (chainPhase L N n) ^ chainStep L N n := pow_nonneg (hβ0 _) _
  have hpow1 : β (chainPhase L N n) ^ chainStep L N n ≤ 1 := pow_le_one₀ (hβ0 _) (hβ1 _)
  have hh0 : 0 ≤ 1 - β (chainPhase L N n) := by linarith [hβ1 (chainPhase L N n)]
  have hhH : 1 - β (chainPhase L N n) ≤ H := hH _
  have henv : β (chainPhase L N n) ^ chainStep L N n * K +
      (1 - β (chainPhase L N n)) * B * (1 - β (chainPhase L N n) ^ chainStep L N n) ≤ K := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - β (chainPhase L N n) ^ chainStep L N n)
      (by linarith [hKB (chainPhase L N n)] :
        (0 : ℝ) ≤ K - (1 - β (chainPhase L N n)) * B)]
  have hdecomp : multiActual C word β N n j - multiIdeal C β N n j =
      multiCorrected C word β N n j +
        (1 - β (chainPhase L N n)) *
          wordDrift r (C.mixWeight (chainPhase L N n)) (word (chainPhase L N n))
            (chainStep L N n) j := by
    unfold multiCorrected
    ring
  obtain ⟨hclo, hchi⟩ := abs_le.mp hmain
  obtain ⟨hglo, hghi⟩ := abs_le.mp hdr
  rw [hdecomp]
  refine abs_le.mpr ⟨?_, ?_⟩ <;>
    nlinarith [mul_nonneg hh0 (by linarith : (0 : ℝ) ≤ B -
        wordDrift r (C.mixWeight (chainPhase L N n)) (word (chainPhase L N n))
          (chainStep L N n) j),
      mul_nonneg hh0 (by linarith : (0 : ℝ) ≤
        wordDrift r (C.mixWeight (chainPhase L N n)) (word (chainPhase L N n))
          (chainStep L N n) j + B),
      mul_nonneg (by linarith : (0 : ℝ) ≤ H - (1 - β (chainPhase L N n))) hB0]

omit [DecidableEq ι] in
/-- **Rationality of the ideal chain**: every ideal state is above the floor,
being a convex combination of the phase's two ideal endpoints. -/
theorem multiIdeal_ge_floor (C : FaceCirculationCertificate r floor L) (β : ZMod L → ℝ)
    (N : ℕ) (hN : 0 < N) (hβ0 : ∀ l, 0 ≤ β l) (hβ1 : ∀ l, β l ≤ 1)
    (hβN : ∀ l, β l ^ N = C.ratio l) (n : ℕ) (j : ι) :
    floor j ≤ multiIdeal C β N n j := by
  have hlow : C.ratio (chainPhase L N n) ≤ β (chainPhase L N n) ^ chainStep L N n :=
    pow_le_pow_of_pow_eq _ _ N _ (hβ0 _) (hβ1 _) (hβN _)
      (le_of_lt (phaseSchedule_snd_lt L N hN n))
  have hhigh : β (chainPhase L N n) ^ chainStep L N n ≤ 1 := pow_le_one₀ (hβ0 _) (hβ1 _)
  refine segmentPoint_ge_floor _ _ _ _ _ (C.ratio_lt_one _) hlow hhigh
    (C.vertex_ge_floor _) (fun k => ?_) j
  rw [← C.step (chainPhase L N n) k]
  exact C.vertex_ge_floor _ k

omit [DecidableEq ι] in
/-- **The owner of a microstep is exactly pinned on the ideal chain.**  Both
endpoints of the phase segment carry the owner's solo value, so the whole
segment does. -/
theorem multiIdeal_pinned (C : FaceCirculationCertificate r floor L) (β : ZMod L → ℝ)
    (N n : ℕ) (i : ι) (hi : 0 < C.mixWeight (chainPhase L N n) i) :
    multiIdeal C β N n i = r {i} i := by
  unfold multiIdeal segmentPoint
  rw [C.vertex_pinned _ i hi, C.target_pinned _ i hi]
  ring

/-- **The one-stage inequalities along the multi-owner chain.**  Every
microstep row is support-perfect at tolerance `ε` as soon as
`K + H B + 2 M H ≤ ε`.

This is where the support size enters the error: through `B`, the word
imbalance, and only there.  With singleton supports `B = 0`, hence `K = 0`,
and the condition collapses to the singleton file's `2 M H ≤ ε`. -/
theorem isSupportPerfectRow_multi (C : FaceCirculationCertificate r floor L)
    (word : ZMod L → ℕ → ι) (β : ZMod L → ℝ) (N : ℕ) (hN : 0 < N)
    (hβ0 : ∀ l, 0 ≤ β l) (hβ1 : ∀ l, β l ≤ 1) (hβN : ∀ l, β l ^ N = C.ratio l)
    (hword : ∀ l t, 0 < C.mixWeight l (word l t))
    (M B K H : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M) (hB0 : 0 ≤ B)
    (hdrift : ∀ l T j, |wordDrift r (C.mixWeight l) (word l) T j| ≤ B)
    (hK : ∀ l, C.ratio l * K + (1 - β l) * B * (2 - C.ratio l) ≤ K)
    (hH : ∀ l, 1 - β l ≤ H) (ε : ℝ) (hεbound : K + H * B + 2 * M * H ≤ ε) (n : ℕ) :
    IsSupportPerfectRow r (multiRow word β N n) (multiActual C word β N n) ε := by
  obtain ⟨hK0, _⟩ := multiError_bounds C β hβ1 B K hB0 hK
  have habs := abs_multiActual_sub_multiIdeal_le C word β N hN hβ0 hβ1 hβN B K H hB0
    hdrift hK hH
  have hh0 : 0 ≤ 1 - β (chainPhase L N n) := by linarith [hβ1 (chainPhase L N n)]
  have hh1 : 1 - β (chainPhase L N n) ≤ 1 := by linarith [hβ0 (chainPhase L N n)]
  have hH0 : 0 ≤ H := le_trans hh0 (hH _)
  have hE0 : 0 ≤ K + H * B := add_nonneg hK0 (mul_nonneg hH0 hB0)
  have hpinid : multiIdeal C β N n (word (chainPhase L N n) (chainStep L N n)) =
      r {word (chainPhase L N n) (chainStep L N n)}
        (word (chainPhase L N n) (chainStep L N n)) :=
    multiIdeal_pinned C β N n _ (hword _ _)
  refine isSupportPerfectRow_singletonRow_approx r M hM0 hM (1 - β (chainPhase L N n))
    hh0 hh1 (word (chainPhase L N n) (chainStep L N n)) (multiActual C word β N n)
    (K + H * B) hE0 ?_ (fun k => ?_) ε ?_
  · rw [← hpinid]
    exact habs n _
  · have h1 : r {k} k ≤ floor k := C.solo_le_floor k
    have h2 : floor k ≤ multiIdeal C β N n k :=
      multiIdeal_ge_floor C β N hN hβ0 hβ1 hβN n k
    have h3 := abs_le.mp (habs n k)
    linarith [h3.1]
  · nlinarith [hH (chainPhase L N n), mul_le_mul_of_nonneg_left (hH (chainPhase L N n))
      (by linarith : (0 : ℝ) ≤ 2 * M)]

/-- **Rationality along the multi-owner chain**: every actual state is within
`ε` of the floor. -/
theorem multiActual_ge_floor_sub (C : FaceCirculationCertificate r floor L)
    (word : ZMod L → ℕ → ι) (β : ZMod L → ℝ) (N : ℕ) (hN : 0 < N)
    (hβ0 : ∀ l, 0 ≤ β l) (hβ1 : ∀ l, β l ≤ 1) (hβN : ∀ l, β l ^ N = C.ratio l)
    (M B K H : ℝ) (hM0 : 0 ≤ M) (hB0 : 0 ≤ B)
    (hdrift : ∀ l T j, |wordDrift r (C.mixWeight l) (word l) T j| ≤ B)
    (hK : ∀ l, C.ratio l * K + (1 - β l) * B * (2 - C.ratio l) ≤ K)
    (hH : ∀ l, 1 - β l ≤ H) (ε : ℝ) (hεbound : K + H * B + 2 * M * H ≤ ε) (n : ℕ) (j : ι) :
    floor j - ε ≤ multiActual C word β N n j := by
  have hh0 : 0 ≤ 1 - β 0 := by linarith [hβ1 0]
  have hH0 : 0 ≤ H := le_trans hh0 (hH 0)
  have habs := abs_multiActual_sub_multiIdeal_le C word β N hN hβ0 hβ1 hβN B K H hB0
    hdrift hK hH n j
  have h2 : floor j ≤ multiIdeal C β N n j := multiIdeal_ge_floor C β N hN hβ0 hβ1 hβN n j
  have h3 := abs_le.mp habs
  nlinarith [h3.1, mul_nonneg hH0 hB0, mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hM0) hH0]

/-! ## Quit mass -/

/-- The quit mass of a chain microstep is its phase hazard. -/
theorem quitMass_multiRow (word : ZMod L → ℕ → ι) (β : ZMod L → ℝ) (N n : ℕ) :
    1 - continueMass (multiRow word β N n) = 1 - β (chainPhase L N n) :=
  quitMass_singletonRow _ _

/-- **The prefix quit mass grows linearly.**  Bernoulli's inequality bounds
each phase hazard below by `(1 - α_ℓ)/N`, so `T` microsteps release at least
`T (1 - a)/N` of quit mass when every contraction ratio is at most `a`. -/
theorem quitMass_prefix_multi_ge (C : FaceCirculationCertificate r floor L)
    (word : ZMod L → ℕ → ι) (β : ZMod L → ℝ) (N : ℕ) (hN : 0 < N) (hβ0 : ∀ l, 0 ≤ β l)
    (hβN : ∀ l, β l ^ N = C.ratio l) (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (T : ℕ) :
    (T : ℝ) * ((1 - a) / N) ≤
      ∑ n ∈ Finset.range T, (1 - continueMass (multiRow word β N n)) := by
  have hterm : ∀ n ∈ Finset.range T,
      (1 - a) / N ≤ 1 - continueMass (multiRow word β N n) := by
    intro n _
    rw [quitMass_multiRow]
    have hbern := sub_le_nsmul_one_sub_of_pow_eq (C.ratio (chainPhase L N n))
      (β (chainPhase L N n)) N (hβ0 _) (hβN _)
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_iff₀ hNpos]
    nlinarith [ha (chainPhase L N n)]
  calc (T : ℝ) * ((1 - a) / N) = ∑ _n ∈ Finset.range T, (1 - a) / N := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ _ := Finset.sum_le_sum hterm

/-- **Unbounded quit mass**: for every target `Q` a long enough prefix of the
chain releases quit mass at least `Q`. -/
theorem exists_prefix_quitMass_multi_ge (C : FaceCirculationCertificate r floor L)
    (word : ZMod L → ℕ → ι) (β : ZMod L → ℝ) (N : ℕ) (hN : 0 < N) (hβ0 : ∀ l, 0 ≤ β l)
    (hβN : ∀ l, β l ^ N = C.ratio l) (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (Q : ℝ) :
    ∃ T : ℕ, Q ≤ ∑ n ∈ Finset.range T, (1 - continueMass (multiRow word β N n)) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hpos : 0 < (1 - a) / N := div_pos (by linarith) hNpos
  obtain ⟨T, hT⟩ := exists_nat_ge (Q / ((1 - a) / N))
  refine ⟨T, le_trans ?_ (quitMass_prefix_multi_ge C word β N hN hβ0 hβN a ha T)⟩
  rw [div_le_iff₀ hpos] at hT
  linarith

/-! ## The general certificate-to-orbit theorem -/

/-- **From a face-circulation certificate to orbits of unbounded quit mass,
multi-owner phases included.**

For every tolerance `ε > 0` and every target quit mass `Q` there is a
discretisation of the certificate -- a common phase length `N`, per-phase
survival factors `β_ℓ` with `β_ℓ^N = α_ℓ`, and per-phase balanced owner
words -- whose chain obeys the one-stage recursion, whose every microstep row
is support-perfect at tolerance `ε`, whose every state stays within `ε` of
the floor, and a finite prefix of which has quit mass at least `Q`.

The hypotheses are the reward bound `M`, a support-size bound `s` on the
phase mixtures, and an upper bound `a < 1` on the contraction ratios.  The
witness taken here is the hazard budget

`H = ε / (2 M + 2 M (s - 1)(3 - a)/(1 - a) + 1)`,

the trailing `+ 1` only so the quotient is defined at `M = 0`; the condition
`isSupportPerfectRow_multi` actually consumes is `K + H B + 2 M H ≤ ε` with
`B = 2 M (s - 1)` and `K = 2 H B/(1 - a)`.  The support size enters only
through `B`.  This is the recomputed replacement for the source argument's
`H ≤ ε / (2M + 6MC/(1-A))` with `C = ∑_ℓ |J_ℓ|(|J_ℓ|+1)` and
`A = ∏_ℓ α_ℓ`: no macrocycle product is needed, and the support-size factor
is `s - 1` rather than `s(s+1)`. -/
theorem exists_multiCirculation_orbit [Nonempty ι]
    (C : FaceCirculationCertificate r floor L)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (s : ℕ) (hs : ∀ l, (mixSupport (C.mixWeight l)).card ≤ s)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (ε : ℝ) (hε : 0 < ε) (Q : ℝ) :
    ∃ (N : ℕ) (β : ZMod L → ℝ) (word : ZMod L → ℕ → ι), 0 < N ∧
      (∀ n j, multiActual C word β N (n + 1) j =
        oneStageNext r (multiRow word β N n) (multiActual C word β N n) j) ∧
      (∀ n, IsSupportPerfectRow r (multiRow word β N n) (multiActual C word β N n) ε) ∧
      (∀ n j, floor j - ε ≤ multiActual C word β N n j) ∧
      ∃ T : ℕ, Q ≤ ∑ n ∈ Finset.range T,
        (1 - continueMass (multiRow word β N n)) := by
  -- the word-imbalance constant and the hazard budget
  have hs1 : 1 ≤ s :=
    le_trans (Finset.card_pos.mpr
      (mixSupport_nonempty _ (C.mixWeight_nonneg 0) (C.mixWeight_sum 0))) (hs 0)
  have hs1' : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  set B : ℝ := 2 * M * ((s : ℝ) - 1) with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; nlinarith
  have ha0 : (0 : ℝ) < 1 - a := by linarith
  set D : ℝ := 2 * M + B * (3 - a) / (1 - a) + 1 with hDdef
  have hD0 : 0 < D := by
    have hfrac : 0 ≤ B * (3 - a) / (1 - a) :=
      div_nonneg (mul_nonneg hB0 (by linarith)) ha0.le
    rw [hDdef]; linarith
  set H : ℝ := ε / D with hHdef
  have hH0 : 0 < H := by rw [hHdef]; exact div_pos hε hD0
  have hHD : H * D = ε := by rw [hHdef]; field_simp
  set K : ℝ := 2 * H * B / (1 - a) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    exact div_nonneg (by nlinarith [hH0.le]) ha0.le
  -- a common phase length, from the smallest contraction ratio
  have hne : (Finset.univ : Finset (ZMod L)).Nonempty := ⟨0, Finset.mem_univ 0⟩
  set amin : ℝ := Finset.univ.inf' hne C.ratio with hamindef
  have hamin_le : ∀ l, amin ≤ C.ratio l := fun l => Finset.inf'_le _ (Finset.mem_univ l)
  have hamin0 : 0 < amin := by
    rw [hamindef, Finset.lt_inf'_iff]
    exact fun l _ => C.ratio_pos l
  have hamin1 : amin < 1 := lt_of_le_of_lt (hamin_le 0) (C.ratio_lt_one 0)
  obtain ⟨N, b, hN, hb0, hb1, hbN, hbH⟩ :=
    exists_pow_eq_and_one_sub_le amin hamin0 hamin1 H hH0
  have hN0 : N ≠ 0 := hN.ne'
  set β : ZMod L → ℝ := fun l => C.ratio l ^ ((N : ℝ)⁻¹) with hβdef
  have hβ0 : ∀ l, 0 ≤ β l := fun l => Real.rpow_nonneg (C.ratio_pos l).le _
  have hβN : ∀ l, β l ^ N = C.ratio l := fun l =>
    Real.rpow_inv_natCast_pow (C.ratio_pos l).le hN0
  have hβlt : ∀ l, β l < 1 := fun l =>
    Real.rpow_lt_one (C.ratio_pos l).le (C.ratio_lt_one l) (by positivity)
  have hβ1 : ∀ l, β l ≤ 1 := fun l => (hβlt l).le
  have hbβ : ∀ l, b ≤ β l := by
    intro l
    refine le_of_pow_le_pow_left₀ hN0 (hβ0 l) ?_
    rw [hbN, hβN]
    exact hamin_le l
  have hH : ∀ l, 1 - β l ≤ H := fun l => by linarith [hbβ l, hbH]
  -- the greedy balanced owner words
  set word : ZMod L → ℕ → ι := fun l => balancedWord (C.mixWeight l) with hworddef
  have hword : ∀ l t, 0 < C.mixWeight l (word l t) := fun l t =>
    balancedWord_mem_support _ (C.mixWeight_nonneg l) (C.mixWeight_sum l) t
  have hdrift : ∀ l T j, |wordDrift r (C.mixWeight l) (word l) T j| ≤ B := by
    intro l T j
    refine le_trans (abs_wordDrift_balancedWord_le r (C.mixWeight l) M hM0 hM
      (C.mixWeight_nonneg l) (C.mixWeight_sum l) T j) ?_
    have : ((mixSupport (C.mixWeight l)).card : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs l
    rw [hBdef]
    nlinarith
  -- the steady-state level absorbs one phase boundary
  have hK : ∀ l, C.ratio l * K + (1 - β l) * B * (2 - C.ratio l) ≤ K := by
    intro l
    have h1 : (1 - β l) * B * (2 - C.ratio l) ≤ H * B * 2 := by
      have h2 : (0 : ℝ) ≤ 2 - C.ratio l := by linarith [C.ratio_lt_one l]
      nlinarith [hH l, C.ratio_pos l, mul_nonneg (by linarith [hβ1 l] : (0:ℝ) ≤ 1 - β l) hB0]
    have h3 : (1 - a) * K = 2 * H * B := by
      rw [hKdef]
      field_simp
    nlinarith [ha l]
  -- the tolerance
  have hεbound : K + H * B + 2 * M * H ≤ ε := by
    have hsum : K + H * B + 2 * M * H = H * (D - 1) := by
      rw [hKdef, hDdef]
      field_simp
      ring
    rw [hsum]
    nlinarith [hHD]
  refine ⟨N, β, word, hN, fun n j => rfl, ?_, ?_, ?_⟩
  · exact fun n => isSupportPerfectRow_multi C word β N hN hβ0 hβ1 hβN hword M B K H hM0 hM
      hB0 hdrift hK hH ε hεbound n
  · exact fun n j => multiActual_ge_floor_sub C word β N hN hβ0 hβ1 hβN M B K H hM0 hB0
      hdrift hK hH ε hεbound n j
  · exact exists_prefix_quitMass_multi_ge C word β N hN hβ0 hβN a ha ha1 Q

/-- **The singleton case, recovered.**  When every phase mixture is a point
mass the support-size bound is `s = 1`, so the imbalance constant `B` and the
steady-state level `K` both vanish and the tolerance condition collapses to
`2 M H ≤ ε`, exactly as `SingletonFaceCirculationOrbit.lean` finds by direct
computation. -/
theorem exists_multiCirculation_orbit_of_singletonSupport [Nonempty ι]
    (C : FaceCirculationCertificate r floor L) (S : SingletonSupport C)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S' j, |r S' j| ≤ M)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (ε : ℝ) (hε : 0 < ε) (Q : ℝ) :
    ∃ (N : ℕ) (β : ZMod L → ℝ) (word : ZMod L → ℕ → ι), 0 < N ∧
      (∀ n j, multiActual C word β N (n + 1) j =
        oneStageNext r (multiRow word β N n) (multiActual C word β N n) j) ∧
      (∀ n, IsSupportPerfectRow r (multiRow word β N n) (multiActual C word β N n) ε) ∧
      (∀ n j, floor j - ε ≤ multiActual C word β N n j) ∧
      ∃ T : ℕ, Q ≤ ∑ n ∈ Finset.range T,
        (1 - continueMass (multiRow word β N n)) := by
  refine exists_multiCirculation_orbit C M hM0 hM 1 (fun l => ?_) a ha ha1 ε hε Q
  have hsub : mixSupport (C.mixWeight l) ⊆ {S.owner l} := by
    intro i hi
    have hpos := mem_mixSupport.mp hi
    rw [S.mixWeight_eq l] at hpos
    by_contra hcon
    rw [Finset.mem_singleton] at hcon
    simp [hcon] at hpos
  exact le_trans (Finset.card_le_card hsub) (by simp)

/-- **The certificate class is not empty**: the general theorem applied to
the calibration certificate on the scaled cyclic weight, with `M = 1`,
support size `1` and all contraction ratios `1/2`.  Every conclusion of
`exists_multiCirculation_orbit` therefore holds at a concrete weight, which
is what keeps the hypothesis package from being vacuous. -/
theorem exists_multiCirculation_cyclicOrbit (ε : ℝ) (hε : 0 < ε) (Q : ℝ) :
    ∃ (N : ℕ) (β : ZMod 3 → ℝ) (word : ZMod 3 → ℕ → CyclicIndex), 0 < N ∧
      (∀ n j, multiActual cyclicCirculation word β N (n + 1) j =
        oneStageNext scaledCyclicWeight (multiRow word β N n)
          (multiActual cyclicCirculation word β N n) j) ∧
      (∀ n, IsSupportPerfectRow scaledCyclicWeight (multiRow word β N n)
        (multiActual cyclicCirculation word β N n) ε) ∧
      (∀ n j, cyclicCirculationFloor j - ε ≤ multiActual cyclicCirculation word β N n j) ∧
      ∃ T : ℕ, Q ≤ ∑ n ∈ Finset.range T, (1 - continueMass (multiRow word β N n)) :=
  exists_multiCirculation_orbit_of_singletonSupport cyclicCirculation cyclicCirculationSupport
    1 (by norm_num) abs_scaledCyclicWeight_le_one (1 / 2) (fun _ => le_rfl) (by norm_num) ε hε Q

end GameTheory
