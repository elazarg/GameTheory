/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation.Exact
import GameTheory.Core.GameProperties
import GameTheory.Concepts.Equilibrium.ApproximateNash

/-!
# Singleton k-implementation

The constructive core of Monderer--Tennenholtz Theorem 1. For a target profile
`z`, the interested party pays player `i` only when `i` plays `z i`. The payment
matches the maximal one-shot gain against the current opponents, with a unit
off-target bump to make every non-target action dominated. On the surviving
profile `z`, the total transfer is exactly the sum of the target-profile gaps.
-/

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι]

/-- Nondegeneracy needed by the paper's strict-witness construction: for every
player there is another player with an alternative to the target action. This
packages "at least two players, and every player has at least two strategies" in
the exact form used by the proof. -/
def SingletonNondegenerate (G : KernelGame ι) (z : Profile G) : Prop :=
  ∀ i : ι, ∃ j : ι, j ≠ i ∧ ∃ a : G.Strategy j, a ≠ z j

/-- If a transfer scheme implements the singleton `{z}`, then `z` itself is an
undominated profile in the subsidized game. -/
theorem singleton_target_undominated_of_isImplementation
    {G : KernelGame ι} {V : Profile G → Payoff ι} {z : Profile G}
    (h : G.IsImplementation V ({z} : Set (Profile G))) :
    z ∈ (G.subsidize V).undominatedProfiles := by
  obtain ⟨σ, hσ⟩ := h.nonempty
  have hσz : (σ : Profile G) = z := by
    have hmem : (σ : Profile G) ∈ ({z} : Set (Profile G)) :=
      h.subset (σ : Profile G) hσ
    exact Set.mem_singleton_iff.mp hmem
  intro i
  have hi : σ i = z i := congrFun hσz i
  simpa [hi] using hσ i

omit [DecidableEq ι] in
/-- The paper's usual finite-game hypotheses imply the nondegeneracy condition
used by the strict-witness construction: for every player there is another
player, and that other player has an alternative to the target action. -/
theorem singletonNondegenerate_of_one_lt_card [Fintype ι]
    (G : KernelGame ι) (z : Profile G) [∀ i, Nontrivial (G.Strategy i)]
    (hι : 1 < Fintype.card ι) :
    G.SingletonNondegenerate z := by
  intro i
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hι i
  obtain ⟨a, ha⟩ := exists_ne (z j)
  exact ⟨j, hji, a, ha⟩

section Construction

variable {G : KernelGame ι}

/-- Maximal gain player `i` can get by deviating from the target action while
opponents are as in `σ`. -/
noncomputable def implementationGapAt (G : KernelGame ι) (z : Profile G)
    [strategyFintype : ∀ i, Fintype (G.Strategy i)]
    [strategyNonempty : ∀ i, Nonempty (G.Strategy i)]
    (i : ι) (σ : Profile G) : ℝ :=
  letI : Fintype (G.Strategy i) := strategyFintype i
  letI : Nonempty (G.Strategy i) := strategyNonempty i
  Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy i))
    (fun s : G.Strategy i =>
      G.eu (Function.update σ i s) i -
        G.eu (Function.update σ i (z i)) i)

/-- The implementation cost contribution of player `i` at the target profile. -/
noncomputable def implementationGap (G : KernelGame ι) (z : Profile G)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] (i : ι) : ℝ :=
  G.implementationGapAt z i z

/-- The largest one-player gain available at the target profile. This is the
least `ε` for which the target is an `ε`-Nash equilibrium. -/
noncomputable def maxImplementationGap (G : KernelGame ι) (z : Profile G)
    [Fintype ι] [Nonempty ι]
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)] : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty (α := ι))
    (fun i : ι => G.implementationGap z i)

variable [strategyFintype : ∀ i, Fintype (G.Strategy i)]
variable [strategyNonempty : ∀ i, Nonempty (G.Strategy i)]

theorem implementationGapAt_ge (z : Profile G) (i : ι) (σ : Profile G)
    (s : G.Strategy i) :
    G.eu (Function.update σ i s) i -
        G.eu (Function.update σ i (z i)) i ≤
      G.implementationGapAt z i σ := by
  letI : Fintype (G.Strategy i) := strategyFintype i
  letI : Nonempty (G.Strategy i) := strategyNonempty i
  simpa [implementationGapAt] using
    (Finset.le_sup' (s := Finset.univ)
      (f := fun s : G.Strategy i =>
        G.eu (Function.update σ i s) i -
          G.eu (Function.update σ i (z i)) i)
      (Finset.mem_univ s))

theorem implementationGapAt_nonneg (z : Profile G) (i : ι) (σ : Profile G) :
    0 ≤ G.implementationGapAt z i σ := by
  have h := implementationGapAt_ge (G := G) z i σ (z i)
  simpa using h

theorem implementationGap_ge (z : Profile G) (i : ι) (s : G.Strategy i) :
    G.eu (Function.update z i s) i - G.eu z i ≤
      G.implementationGap z i := by
  simpa [implementationGap, Function.update_eq_self] using
    implementationGapAt_ge (G := G) z i z s

theorem implementationGap_nonneg (z : Profile G) (i : ι) :
    0 ≤ G.implementationGap z i := by
  simpa [implementationGap] using implementationGapAt_nonneg (G := G) z i z

theorem implementationGap_le_maxImplementationGap [Fintype ι] [Nonempty ι]
    (z : Profile G) (i : ι) :
    G.implementationGap z i ≤ G.maxImplementationGap z := by
  simpa [maxImplementationGap] using
    (Finset.le_sup' (s := Finset.univ)
      (f := fun i : ι => G.implementationGap z i)
      (Finset.mem_univ i))

theorem maxImplementationGap_nonneg [Fintype ι] [Nonempty ι]
    (z : Profile G) :
    0 ≤ G.maxImplementationGap z := by
  obtain ⟨i⟩ := (inferInstance : Nonempty ι)
  exact (implementationGap_nonneg (G := G) z i).trans
    (G.implementationGap_le_maxImplementationGap z i)

theorem isεNash_iff_maxImplementationGap_le [Fintype ι] [Nonempty ι]
    (z : Profile G) {ε : ℝ} :
    G.IsεNash ε z ↔ G.maxImplementationGap z ≤ ε := by
  classical
  constructor
  · intro hε
    unfold maxImplementationGap
    apply Finset.sup'_le
    intro i _
    unfold implementationGap implementationGapAt
    apply Finset.sup'_le
    intro s _
    have h := hε i s
    have hle : G.eu (Function.update z i s) i - G.eu z i ≤ ε := by
      linarith
    simpa [Function.update_eq_self] using hle
  · intro hgap i s
    have hdev := implementationGap_ge (G := G) z i s
    have hi : G.implementationGap z i ≤ ε :=
      (G.implementationGap_le_maxImplementationGap z i).trans hgap
    have hdev' : G.eu (Function.update z i s) i - G.eu z i ≤ ε := by
      simpa [Function.update_eq_self] using hdev.trans hi
    linarith

/-- The transfer scheme used for singleton implementation. A player is paid
only on profiles where they play the target action. Off the target profile the
extra unit creates the strict witness required by dominance. -/
noncomputable def singletonTransfer (G : KernelGame ι)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (z : Profile G) : Profile G → Payoff ι :=
  open Classical in
  fun σ i =>
    if σ i = z i then
      G.implementationGapAt z i σ + if σ = z then 0 else 1
    else 0

@[simp] theorem singletonTransfer_target (z : Profile G) (i : ι) :
    G.singletonTransfer z z i = G.implementationGap z i := by
  classical
  simp [singletonTransfer, implementationGap]

open Classical in
@[simp] theorem singletonTransfer_update_target (z : Profile G)
    (i : ι) (σ : Profile G) :
    G.singletonTransfer z (Function.update σ i (z i)) i =
      G.implementationGapAt z i (Function.update σ i (z i)) +
        if Function.update σ i (z i) = z then 0 else 1 := by
  classical
  simp [singletonTransfer]

theorem singletonTransfer_update_ne (z : Profile G)
    (i : ι) (σ : Profile G) {s : G.Strategy i} (hs : s ≠ z i) :
    G.singletonTransfer z (Function.update σ i s) i = 0 := by
  classical
  unfold singletonTransfer
  rw [if_neg]
  simpa using hs

theorem singletonTransfer_nonneg (z : Profile G) :
    ∀ σ i, 0 ≤ G.singletonTransfer z σ i := by
  classical
  intro σ i
  by_cases hi : σ i = z i
  · have hgap := implementationGapAt_nonneg (G := G) z i σ
    by_cases hσ : σ = z
    · subst hσ
      simpa [singletonTransfer] using hgap
    · simp [singletonTransfer, hi, hσ]
      linarith
  · simp [singletonTransfer, hi]

theorem singletonTransfer_target_isDominant [Finite G.Outcome]
    (z : Profile G) (i : ι) :
    (G.subsidize (G.singletonTransfer z)).IsDominant i (z i) := by
  classical
  intro σ s
  let τ : Profile G := σ
  let t : G.Strategy i := s
  change (G.subsidize (G.singletonTransfer z)).eu (Function.update τ i (z i)) i ≥
    (G.subsidize (G.singletonTransfer z)).eu (Function.update τ i t) i
  by_cases hs : t = z i
  · simp [t, hs]
  · have hgap := implementationGapAt_ge (G := G) z i
      (Function.update τ i (z i)) t
    have hgap' :
        G.eu (Function.update τ i t) i -
            G.eu (Function.update τ i (z i)) i ≤
          G.implementationGapAt z i (Function.update τ i (z i)) := by
      simpa [Function.update_idem] using hgap
    have hbump :
        0 ≤ if Function.update τ i (z i) = z then (0 : ℝ) else 1 := by
      split <;> norm_num
    rw [subsidize_eu, subsidize_eu]
    simp only [subsidize_Strategy, singletonTransfer_update_target, ge_iff_le]
    rw [singletonTransfer_update_ne (G := G) z i τ hs]
    simp only [add_zero]
    have hdev_le :
        G.eu (Function.update τ i t) i ≤
          G.eu (Function.update τ i (z i)) i +
            G.implementationGapAt z i (Function.update τ i (z i)) := by
      linarith
    have hpay_le :
        G.eu (Function.update τ i (z i)) i +
            G.implementationGapAt z i (Function.update τ i (z i)) ≤
          G.eu (Function.update τ i (z i)) i +
            (G.implementationGapAt z i (Function.update τ i (z i)) +
              (if Function.update τ i (z i) = z then (0 : ℝ) else 1)) := by
      linarith
    exact le_trans hdev_le hpay_le

theorem singletonTransfer_weaklyStrictlyDominates_ne [Finite G.Outcome]
    (z : Profile G) (hnd : G.SingletonNondegenerate z)
    {i : ι} {s : G.Strategy i} (hs : s ≠ z i) :
    (G.subsidize (G.singletonTransfer z)).WeaklyStrictlyDominates i (z i) s := by
  classical
  refine ⟨(singletonTransfer_target_isDominant (G := G) z i).weaklyDominates s, ?_⟩
  obtain ⟨j, hji, a, ha⟩ := hnd i
  let σ : Profile G := Function.update z j a
  have htarget_ne : Function.update σ i (z i) ≠ z := by
    intro hEq
    have hcoord := congrFun hEq j
    simp [σ, Function.update_of_ne hji, ha] at hcoord
  have hgap := implementationGapAt_ge (G := G) z i
    (Function.update σ i (z i)) s
  have hgap' :
      G.eu (Function.update σ i s) i -
          G.eu (Function.update σ i (z i)) i ≤
        G.implementationGapAt z i (Function.update σ i (z i)) := by
    simpa [Function.update_idem] using hgap
  refine ⟨σ, ?_⟩
  rw [subsidize_eu, subsidize_eu]
  change G.eu (Function.update σ i (z i)) i +
      G.singletonTransfer z (Function.update σ i (z i)) i >
    G.eu (Function.update σ i s) i +
      G.singletonTransfer z (Function.update σ i s) i
  simp [singletonTransfer, hs, htarget_ne]
  linarith

theorem singletonTransfer_target_undominated [Finite G.Outcome]
    (z : Profile G) (i : ι) :
    (G.subsidize (G.singletonTransfer z)).IsUndominated i (z i) :=
  (singletonTransfer_target_isDominant (G := G) z i).isUndominated

theorem singletonTransfer_z_mem_undominated [Finite G.Outcome]
    (z : Profile G) :
    z ∈ (G.subsidize (G.singletonTransfer z)).undominatedProfiles := by
  intro i
  exact singletonTransfer_target_undominated (G := G) z i

theorem singletonTransfer_undominated_subset_singleton [Finite G.Outcome]
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    ∀ σ : Profile G,
      σ ∈ (G.subsidize (G.singletonTransfer z)).undominatedProfiles →
        σ ∈ ({z} : Set (Profile G)) := by
  classical
  intro σ hσ
  have hcoord : ∀ i, σ i = z i := by
    intro i
    by_contra hne
    have hdom := singletonTransfer_weaklyStrictlyDominates_ne (G := G) z hnd (i := i)
      (s := σ i) hne
    exact (hσ i (z i) hdom).elim
  exact Set.mem_singleton_iff.mpr (funext hcoord)

theorem singletonTransfer_isImplementation [Finite G.Outcome]
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    G.IsImplementation (G.singletonTransfer z) ({z} : Set (Profile G)) := by
  refine ⟨singletonTransfer_nonneg (G := G) z, ?_, ?_⟩
  · exact ⟨z, singletonTransfer_z_mem_undominated (G := G) z⟩
  · exact singletonTransfer_undominated_subset_singleton (G := G) z hnd

/-- The explicit singleton transfer is a k-implementation at the paper's target
cost `Σ_i max_{s_i} (u_i(s_i,z_-i)-u_i(z))`. -/
theorem singletonTransfer_isKImplementation [Fintype ι] [Finite G.Outcome]
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    G.IsKImplementation (G.singletonTransfer z) ({z} : Set (Profile G))
      (∑ i, G.implementationGap z i) := by
  refine ⟨singletonTransfer_isImplementation (G := G) z hnd, ?_⟩
  intro σ hσ
  have hσz : σ = z := by
    have hmem := singletonTransfer_undominated_subset_singleton (G := G) z hnd σ hσ
    simpa using hmem
  subst hσz
  simp

/-- A variant of the singleton transfer with a positive bump at the target
profile itself. This does not attain the singleton price in degenerate games,
but it implements `{z}` at every budget strictly above the price. -/
noncomputable def singletonApproxTransfer (G : KernelGame ι)
    [∀ i, Fintype (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    (z : Profile G) (ε : ι → ℝ) : Profile G → Payoff ι :=
  open Classical in
  fun σ i => if σ i = z i then G.implementationGapAt z i σ + ε i else 0

@[simp] theorem singletonApproxTransfer_target (z : Profile G) (ε : ι → ℝ)
    (i : ι) :
    G.singletonApproxTransfer z ε z i = G.implementationGap z i + ε i := by
  classical
  simp [singletonApproxTransfer, implementationGap]

@[simp] theorem singletonApproxTransfer_update_target (z : Profile G)
    (ε : ι → ℝ) (i : ι) (σ : Profile G) :
    G.singletonApproxTransfer z ε (Function.update σ i (z i)) i =
      G.implementationGapAt z i (Function.update σ i (z i)) + ε i := by
  classical
  simp [singletonApproxTransfer]

theorem singletonApproxTransfer_update_ne (z : Profile G) (ε : ι → ℝ)
    (i : ι) (σ : Profile G) {s : G.Strategy i} (hs : s ≠ z i) :
    G.singletonApproxTransfer z ε (Function.update σ i s) i = 0 := by
  classical
  unfold singletonApproxTransfer
  rw [if_neg]
  simpa using hs

theorem singletonApproxTransfer_nonneg (z : Profile G) {ε : ι → ℝ}
    (hε : ∀ i, 0 ≤ ε i) :
    ∀ σ i, 0 ≤ G.singletonApproxTransfer z ε σ i := by
  classical
  intro σ i
  by_cases hi : σ i = z i
  · have hgap := implementationGapAt_nonneg (G := G) z i σ
    simp [singletonApproxTransfer, hi]
    linarith [hε i]
  · simp [singletonApproxTransfer, hi]

theorem singletonApproxTransfer_target_isDominant [Finite G.Outcome]
    (z : Profile G) {ε : ι → ℝ} (hε : ∀ i, 0 ≤ ε i) (i : ι) :
    (G.subsidize (G.singletonApproxTransfer z ε)).IsDominant i (z i) := by
  classical
  intro σ s
  let τ : Profile G := σ
  let t : G.Strategy i := s
  change (G.subsidize (G.singletonApproxTransfer z ε)).eu
      (Function.update τ i (z i)) i ≥
    (G.subsidize (G.singletonApproxTransfer z ε)).eu (Function.update τ i t) i
  by_cases hs : t = z i
  · simp [t, hs]
  · have hgap := implementationGapAt_ge (G := G) z i
      (Function.update τ i (z i)) t
    have hgap' :
        G.eu (Function.update τ i t) i -
            G.eu (Function.update τ i (z i)) i ≤
          G.implementationGapAt z i (Function.update τ i (z i)) := by
      simpa [Function.update_idem] using hgap
    rw [subsidize_eu, subsidize_eu]
    simp only [subsidize_Strategy, singletonApproxTransfer_update_target, ge_iff_le]
    rw [singletonApproxTransfer_update_ne (G := G) z ε i τ hs]
    simp only [add_zero]
    have hdev_le :
        G.eu (Function.update τ i t) i ≤
          G.eu (Function.update τ i (z i)) i +
            G.implementationGapAt z i (Function.update τ i (z i)) := by
      linarith
    have hpay_le :
        G.eu (Function.update τ i (z i)) i +
            G.implementationGapAt z i (Function.update τ i (z i)) ≤
          G.eu (Function.update τ i (z i)) i +
            (G.implementationGapAt z i (Function.update τ i (z i)) + ε i) := by
      linarith [hε i]
    exact le_trans hdev_le hpay_le

theorem singletonApproxTransfer_weaklyStrictlyDominates_ne [Finite G.Outcome]
    (z : Profile G) {ε : ι → ℝ} (hεpos : ∀ i, 0 < ε i)
    {i : ι} {s : G.Strategy i} (hs : s ≠ z i) :
    (G.subsidize (G.singletonApproxTransfer z ε)).WeaklyStrictlyDominates i
      (z i) s := by
  classical
  refine ⟨singletonApproxTransfer_target_isDominant (G := G) z
    (fun i => le_of_lt (hεpos i)) i |>.weaklyDominates s, ?_⟩
  refine ⟨z, ?_⟩
  have hgap := implementationGap_ge (G := G) z i s
  have hgap' :
      G.eu (Function.update z i s) i - G.eu z i ≤
        G.implementationGapAt z i z := by
    simpa [implementationGap, Function.update_eq_self] using hgap
  rw [subsidize_eu, subsidize_eu]
  change G.eu (Function.update z i (z i)) i +
      G.singletonApproxTransfer z ε (Function.update z i (z i)) i >
    G.eu (Function.update z i s) i +
      G.singletonApproxTransfer z ε (Function.update z i s) i
  simp [singletonApproxTransfer, hs, Function.update_eq_self]
  linarith [hgap', hεpos i]

theorem singletonApproxTransfer_target_undominated [Finite G.Outcome]
    (z : Profile G) {ε : ι → ℝ} (hε : ∀ i, 0 ≤ ε i) (i : ι) :
    (G.subsidize (G.singletonApproxTransfer z ε)).IsUndominated i (z i) :=
  (singletonApproxTransfer_target_isDominant (G := G) z hε i).isUndominated

theorem singletonApproxTransfer_z_mem_undominated [Finite G.Outcome]
    (z : Profile G) {ε : ι → ℝ} (hε : ∀ i, 0 ≤ ε i) :
    z ∈ (G.subsidize (G.singletonApproxTransfer z ε)).undominatedProfiles := by
  intro i
  exact singletonApproxTransfer_target_undominated (G := G) z hε i

theorem singletonApproxTransfer_undominated_subset_singleton [Finite G.Outcome]
    (z : Profile G) {ε : ι → ℝ} (hεpos : ∀ i, 0 < ε i) :
    ∀ σ : Profile G,
      σ ∈ (G.subsidize (G.singletonApproxTransfer z ε)).undominatedProfiles →
        σ ∈ ({z} : Set (Profile G)) := by
  classical
  intro σ hσ
  have hcoord : ∀ i, σ i = z i := by
    intro i
    by_contra hne
    have hdom := singletonApproxTransfer_weaklyStrictlyDominates_ne
      (G := G) z hεpos (i := i) (s := σ i) hne
    exact (hσ i (z i) hdom).elim
  exact Set.mem_singleton_iff.mpr (funext hcoord)

theorem singletonApproxTransfer_isImplementation [Finite G.Outcome]
    (z : Profile G) {ε : ι → ℝ} (hεpos : ∀ i, 0 < ε i) :
    G.IsImplementation (G.singletonApproxTransfer z ε) ({z} : Set (Profile G)) := by
  refine ⟨singletonApproxTransfer_nonneg (G := G) z
      (fun i => le_of_lt (hεpos i)), ?_, ?_⟩
  · exact ⟨z, singletonApproxTransfer_z_mem_undominated (G := G) z
      (fun i => le_of_lt (hεpos i))⟩
  · exact singletonApproxTransfer_undominated_subset_singleton (G := G) z hεpos

/-- The positive-bump singleton transfer implements `{z}` at the sum of gaps
plus the total positive bump. -/
theorem singletonApproxTransfer_isKImplementation [Fintype ι] [Finite G.Outcome]
    (z : Profile G) {ε : ι → ℝ} (hεpos : ∀ i, 0 < ε i) :
    G.IsKImplementation (G.singletonApproxTransfer z ε) ({z} : Set (Profile G))
      (∑ i, (G.implementationGap z i + ε i)) := by
  refine ⟨singletonApproxTransfer_isImplementation (G := G) z hεpos, ?_⟩
  intro σ hσ
  have hσz : σ = z := by
    have hmem :=
      singletonApproxTransfer_undominated_subset_singleton (G := G) z hεpos σ hσ
    simpa using hmem
  subst hσz
  simp

/-- Lower-bound component of the singleton theorem: in any implementation of
`{z}`, player `i`'s transfer at `z` is at least their one-shot deviation gap at
`z`. -/
theorem implementationGap_le_transfer_of_singletonImplementation [Finite G.Outcome]
    {V : Profile G → Payoff ι} {z : Profile G}
    (h : G.IsImplementation V ({z} : Set (Profile G))) (i : ι) :
    G.implementationGap z i ≤ V z i := by
  classical
  have hzundom := singleton_target_undominated_of_isImplementation (G := G) h
  have hgain_le : ∀ s : G.Strategy i,
      G.eu (Function.update z i s) i - G.eu z i ≤ V z i := by
    intro s
    by_cases hs : s = z i
    · subst s
      have hV := h.nonneg z i
      simpa [Function.update_eq_self] using hV
    · have hs_not_undom : ¬ (G.subsidize V).IsUndominated i s := by
        intro hsundom
        have hprof : Function.update z i s ∈ (G.subsidize V).undominatedProfiles := by
          intro j
          by_cases hji : j = i
          · subst hji
            simpa using hsundom
          · simpa [Function.update_of_ne hji] using hzundom j
        have hmem := h.subset (Function.update z i s) hprof
        have heq : Function.update z i s = z := by
          simpa using hmem
        have hcoord : s = z i := by
          simpa using congrFun heq i
        exact hs hcoord
      have hsdominated :
          ∃ t : (G.subsidize V).Strategy i,
            (G.subsidize V).WeaklyStrictlyDominates i t s := by
        by_contra hnone
        exact hs_not_undom (by
          intro t ht
          exact hnone ⟨t, ht⟩)
      letI : Fintype ((G.subsidize V).Strategy i) := strategyFintype i
      obtain ⟨t, htundom, htdom⟩ :=
        exists_undominated_dominator (G := G.subsidize V) (who := i) hsdominated
      have htprof : Function.update z i t ∈ (G.subsidize V).undominatedProfiles := by
        intro j
        by_cases hji : j = i
        · subst hji
          simpa using htundom
        · simpa [Function.update_of_ne hji] using hzundom j
      have ht_eq : t = z i := by
        have hmem := h.subset (Function.update z i t) htprof
        have heq : Function.update z i t = z := by
          simpa using hmem
        have hcoord := congrFun heq i
        simpa using hcoord
      have hdom_z : (G.subsidize V).WeaklyStrictlyDominates i (z i) s := by
        simpa [ht_eq] using htdom
      have hweak := hdom_z.toWeaklyDominates
      have hsub_ge :
          (G.subsidize V).eu z i ≥
            (G.subsidize V).eu (Function.update z i s) i := by
        have hw := hweak z
        simpa [Function.update_eq_self] using hw
      rw [subsidize_eu, subsidize_eu] at hsub_ge
      have hVdev := h.nonneg (Function.update z i s) i
      have hdev_le : G.eu (Function.update z i s) i ≤ G.eu z i + V z i := by
        calc
          G.eu (Function.update z i s) i
              = G.eu (Function.update z i s) i + 0 := by ring
          _ ≤ G.eu (Function.update z i s) i +
              V (Function.update z i s) i := by linarith
          _ ≤ G.eu z i + V z i := hsub_ge
      linarith
  letI : Fintype (G.Strategy i) := strategyFintype i
  letI : Nonempty (G.Strategy i) := strategyNonempty i
  unfold implementationGap implementationGapAt
  apply Finset.sup'_le
  intro s _
  simpa [Function.update_eq_self] using hgain_le s

/-- Lower bound on the budget of any k-implementation of a singleton. -/
theorem singletonKImplementation_lower_bound [Fintype ι] [Finite G.Outcome]
    {V : Profile G → Payoff ι} {z : Profile G} {k : ℝ}
    (h : G.IsKImplementation V ({z} : Set (Profile G)) k) :
    (∑ i, G.implementationGap z i) ≤ k := by
  have hzundom :=
    singleton_target_undominated_of_isImplementation (G := G) h.implementation
  calc
    (∑ i, G.implementationGap z i) ≤ ∑ i, V z i := by
      exact Finset.sum_le_sum fun i _ =>
        implementationGap_le_transfer_of_singletonImplementation (G := G)
          (V := V) (z := z) h.implementation i
    _ ≤ k := h.cost_bound z hzundom

/-- Every budget strictly above the singleton deviation-gap sum is feasible.
Unlike `singletonTransfer_isKImplementation`, this uses a positive bump at the
target profile and therefore needs no nondegenerate opponent profile. -/
theorem singletonKImplementation_of_gap_sum_lt [Fintype ι] [Nonempty ι]
    [Finite G.Outcome] (z : Profile G) {k : ℝ}
    (hk : (∑ i, G.implementationGap z i) < k) :
    ∃ V : Profile G → Payoff ι,
      G.IsKImplementation V ({z} : Set (Profile G)) k := by
  classical
  let gapSum : ℝ := ∑ i, G.implementationGap z i
  let δ : ℝ := (k - gapSum) / (Fintype.card ι : ℝ)
  let ε : ι → ℝ := fun _ => δ
  have hcard_pos_nat : 0 < Fintype.card ι :=
    Fintype.card_pos_iff.mpr inferInstance
  have hcard_pos : (0 : ℝ) < (Fintype.card ι : ℝ) := by
    exact_mod_cast hcard_pos_nat
  have hcard_ne : (Fintype.card ι : ℝ) ≠ 0 := hcard_pos.ne'
  have hslack_pos : 0 < k - gapSum := sub_pos.mpr (by simpa [gapSum] using hk)
  have hεpos : ∀ i, 0 < ε i := by
    intro i
    exact div_pos hslack_pos hcard_pos
  have hsumε : (∑ i, ε i) = k - gapSum := by
    simp [ε, δ, gapSum, Finset.sum_const, nsmul_eq_mul]
    field_simp [hcard_ne]
  have hbudget : (∑ i, (G.implementationGap z i + ε i)) = k := by
    rw [Finset.sum_add_distrib, hsumε]
    simp [gapSum]
  exact ⟨G.singletonApproxTransfer z ε, by
    simpa [hbudget] using
      singletonApproxTransfer_isKImplementation (G := G) z hεpos⟩

/-- Feasible-budget form of `singletonKImplementation_of_gap_sum_lt`. -/
theorem implementationCosts_singleton_mem_of_gap_sum_lt [Fintype ι] [Nonempty ι]
    [Finite G.Outcome] (z : Profile G) {k : ℝ}
    (hk : (∑ i, G.implementationGap z i) < k) :
    k ∈ G.implementationCosts ({z} : Set (Profile G)) :=
  singletonKImplementation_of_gap_sum_lt (G := G) z hk

/-- Cost characterization for singleton implementation: `{z}` is
`k`-implementable iff `k` is at least the sum of the target-profile deviation
gaps. -/
theorem singletonKImplementation_iff [Fintype ι] [Finite G.Outcome]
    (z : Profile G) (hnd : G.SingletonNondegenerate z) (k : ℝ) :
    (∃ V : Profile G → Payoff ι,
      G.IsKImplementation V ({z} : Set (Profile G)) k) ↔
      (∑ i, G.implementationGap z i) ≤ k := by
  constructor
  · rintro ⟨V, hV⟩
    exact singletonKImplementation_lower_bound (G := G) (V := V) (z := z) hV
  · intro hk
    exact ⟨G.singletonTransfer z,
      (singletonTransfer_isKImplementation (G := G) z hnd).mono_cost hk⟩

/-- Exact singleton k-implementation has the same cost characterization as
ordinary singleton k-implementation. -/
theorem exactSingletonKImplementation_iff [Fintype ι] [Finite G.Outcome]
    (z : Profile G) (hnd : G.SingletonNondegenerate z) (k : ℝ) :
    (∃ V : Profile G → Payoff ι,
      G.IsExactKImplementation V ({z} : Set (Profile G)) k) ↔
      (∑ i, G.implementationGap z i) ≤ k := by
  constructor
  · rintro ⟨V, hV⟩
    exact (singletonKImplementation_iff (G := G) z hnd k).mp
      ⟨V, hV.toKImplementation ⟨z, by simp⟩⟩
  · intro hk
    obtain ⟨V, hV⟩ := (singletonKImplementation_iff (G := G) z hnd k).mpr hk
    exact ⟨V, hV.toExactKImplementation_singleton⟩

/-- The feasible budgets for singleton implementation are exactly the interval
above the singleton deviation-gap sum. -/
theorem implementationCosts_singleton_eq_Ici [Fintype ι] [Finite G.Outcome]
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    G.implementationCosts ({z} : Set (Profile G)) =
      Set.Ici (∑ i, G.implementationGap z i) := by
  ext k
  simp [implementationCosts, singletonKImplementation_iff (G := G) z hnd k]

/-- Singleton implementation price: the infimum feasible budget is the sum of
target-profile deviation gaps. This interval proof is useful when the optimum
is attained by `singletonTransfer`; the price formula itself is unconditional
for nonempty player sets, see `implPrice_singleton`. -/
theorem implPrice_singleton_of_singletonNondegenerate [Fintype ι] [Finite G.Outcome]
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    G.implPrice ({z} : Set (Profile G)) = ∑ i, G.implementationGap z i := by
  rw [implPrice, implementationCosts_singleton_eq_Ici (G := G) z hnd]
  exact csInf_Ici

/-- Singleton implementation price: the infimum feasible budget is always the
sum of target-profile deviation gaps. Degenerate games may fail to attain this
infimum, but every strictly larger budget is feasible. -/
theorem implPrice_singleton [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) = ∑ i, G.implementationGap z i := by
  classical
  let gapSum : ℝ := ∑ i, G.implementationGap z i
  have hcosts_nonempty :
      (G.implementationCosts ({z} : Set (Profile G))).Nonempty := by
    refine ⟨gapSum + 1, ?_⟩
    exact implementationCosts_singleton_mem_of_gap_sum_lt (G := G) z
      (k := gapSum + 1) (by linarith)
  have hlower : gapSum ≤ G.implPrice ({z} : Set (Profile G)) := by
    rw [implPrice]
    exact le_csInf hcosts_nonempty fun k hk => by
      obtain ⟨V, hV⟩ := hk
      exact singletonKImplementation_lower_bound (G := G) (V := V) (z := z) hV
  have hupper : G.implPrice ({z} : Set (Profile G)) ≤ gapSum := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    obtain ⟨V, hV⟩ :=
      singletonKImplementation_of_gap_sum_lt (G := G) z
        (k := gapSum + δ) (by linarith)
    exact implPrice_le_of_isKImplementation (G := G) (V := V)
      (O := ({z} : Set (Profile G))) hV
  exact le_antisymm hupper hlower

/-- The singleton implementation price dominates the largest one-player
deviation gain, i.e. the `ε`-Nash threshold. -/
theorem maxImplementationGap_le_implPrice_singleton
    [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    (z : Profile G) :
    G.maxImplementationGap z ≤ G.implPrice ({z} : Set (Profile G)) := by
  rw [implPrice_singleton (G := G) z]
  unfold maxImplementationGap
  apply Finset.sup'_le
  intro i _
  exact Finset.single_le_sum
    (fun j _ => implementationGap_nonneg (G := G) z j)
    (Finset.mem_univ i)

/-- The singleton implementation price is at most the number of players times
the largest one-player deviation gain. -/
theorem implPrice_singleton_le_card_mul_maxImplementationGap
    [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) ≤
      (Fintype.card ι : ℝ) * G.maxImplementationGap z := by
  rw [implPrice_singleton (G := G) z]
  calc
    (∑ i, G.implementationGap z i)
        ≤ ∑ _i : ι, G.maxImplementationGap z := by
          exact Finset.sum_le_sum fun i _ =>
            G.implementationGap_le_maxImplementationGap z i
    _ = (Fintype.card ι : ℝ) * G.maxImplementationGap z := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- Singleton implementation price is the `ℓ¹` norm of the nonnegative
deviation-gap vector, so it lies between the `ℓ∞` threshold for `ε`-Nash and
`n` times that threshold. -/
theorem implPrice_singleton_linf_lone_sandwich
    [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    (z : Profile G) :
    G.maxImplementationGap z ≤ G.implPrice ({z} : Set (Profile G)) ∧
      G.implPrice ({z} : Set (Profile G)) ≤
        (Fintype.card ι : ℝ) * G.maxImplementationGap z :=
  ⟨G.maxImplementationGap_le_implPrice_singleton z,
    G.implPrice_singleton_le_card_mul_maxImplementationGap z⟩

omit strategyFintype in
theorem implPrice_singleton_le_card_mul_of_isεNash
    [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {z : Profile G} {ε : ℝ} (hε : G.IsεNash ε z) :
    G.implPrice ({z} : Set (Profile G)) ≤ (Fintype.card ι : ℝ) * ε := by
  letI : ∀ i, Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  have hgap : G.maxImplementationGap z ≤ ε :=
    (G.isεNash_iff_maxImplementationGap_le z).mp hε
  have hprice := G.implPrice_singleton_le_card_mul_maxImplementationGap z
  exact hprice.trans (mul_le_mul_of_nonneg_left hgap (by positivity))

omit strategyFintype in
theorem isεNash_of_implPrice_singleton_le
    [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    {z : Profile G} {ε : ℝ}
    (hprice : G.implPrice ({z} : Set (Profile G)) ≤ ε) :
    G.IsεNash ε z := by
  letI : ∀ i, Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  rw [G.isεNash_iff_maxImplementationGap_le z]
  exact (G.maxImplementationGap_le_implPrice_singleton z).trans hprice

/-- In an exact potential game, a player's singleton implementation gap is the
maximum one-step increase of the potential available to that player. -/
theorem implementationGap_eq_potentialGap
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ)
    (z : Profile G) (i : ι) :
    G.implementationGap z i =
      Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy i))
        (fun s : G.Strategy i => Φ (Function.update z i s) - Φ z) := by
  classical
  unfold implementationGap implementationGapAt
  apply congrArg
    (fun f : G.Strategy i → ℝ =>
      Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy i)) f)
  funext s
  simpa [Function.update_eq_self] using hΦ i z s

/-- In an exact potential game, the singleton implementation price is the sum
of the positive one-player potential-gradient coordinates at the target. -/
theorem implPrice_singleton_eq_sum_potentialGaps
    [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ) (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) =
      ∑ i, Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy i))
        (fun s : G.Strategy i => Φ (Function.update z i s) - Φ z) := by
  rw [implPrice_singleton (G := G) z]
  apply Finset.sum_congr rfl
  intro i _
  exact implementationGap_eq_potentialGap (G := G) hΦ z i

/-- In an exact potential game, the singleton implementation price is bounded
by the number of players times the gap from the target potential to the global
maximum potential. -/
theorem implPrice_singleton_le_card_mul_potentialGap
    [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ) (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) ≤
      (Fintype.card ι : ℝ) *
        (Finset.univ.sup' (Finset.univ_nonempty (α := Profile G)) Φ - Φ z) := by
  classical
  let Φmax : ℝ := Finset.univ.sup' (Finset.univ_nonempty (α := Profile G)) Φ
  have hcoord : ∀ i, G.implementationGap z i ≤ Φmax - Φ z := by
    intro i
    rw [implementationGap_eq_potentialGap (G := G) hΦ z i]
    apply Finset.sup'_le
    intro s _
    have hmax :
        Φ (Function.update z i s) ≤ Φmax := by
      simpa [Φmax] using
        (Finset.le_sup' (s := Finset.univ) (f := Φ)
          (Finset.mem_univ (Function.update z i s)))
    linarith
  calc
    G.implPrice ({z} : Set (Profile G))
        = ∑ i, G.implementationGap z i := implPrice_singleton (G := G) z
    _ ≤ ∑ _i : ι, (Φmax - Φ z) := by
          exact Finset.sum_le_sum fun i _ => hcoord i
    _ = (Fintype.card ι : ℝ) * (Φmax - Φ z) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = (Fintype.card ι : ℝ) *
        (Finset.univ.sup' (Finset.univ_nonempty (α := Profile G)) Φ - Φ z) := by
          rfl

omit strategyFintype strategyNonempty in
/-- In an exact potential game, singleton implementation has zero price exactly
at local maxima of the potential with respect to one-player deviations. -/
theorem implPrice_singleton_eq_zero_iff_potential_localMax
    [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)] [∀ i, Nonempty (G.Strategy i)]
    {Φ : Profile G → ℝ} (hΦ : G.IsExactPotential Φ) (z : Profile G) :
    G.implPrice ({z} : Set (Profile G)) = 0 ↔
      ∀ i (s : G.Strategy i), Φ (Function.update z i s) ≤ Φ z := by
  classical
  letI : ∀ i, Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  constructor
  · intro hprice i s
    have hsum : (∑ j, G.implementationGap z j) = 0 := by
      simpa [implPrice_singleton (G := G) z] using hprice
    have hgap_i_le : G.implementationGap z i ≤ 0 := by
      have hterm_le_sum :
          G.implementationGap z i ≤ ∑ j, G.implementationGap z j :=
        Finset.single_le_sum
          (fun j _ => implementationGap_nonneg (G := G) z j)
          (Finset.mem_univ i)
      rwa [hsum] at hterm_le_sum
    have hdev := implementationGap_ge (G := G) z i s
    have hpot_nonpos : Φ (Function.update z i s) - Φ z ≤ 0 := by
      rw [← hΦ i z s]
      exact hdev.trans hgap_i_le
    linarith
  · intro hlocal
    rw [implPrice_singleton (G := G) z]
    apply Finset.sum_eq_zero
    intro i _
    apply le_antisymm
    · unfold implementationGap implementationGapAt
      apply Finset.sup'_le
      intro s _
      have hle : G.eu (Function.update z i s) i - G.eu z i ≤ 0 := by
        rw [hΦ i z s]
        exact sub_nonpos.mpr (hlocal i s)
      simpa [Function.update_eq_self] using hle
    · exact implementationGap_nonneg (G := G) z i

/-- Exact singleton implementation costs coincide with the ordinary singleton
cost interval. -/
theorem exactImplementationCosts_singleton_eq_Ici [Fintype ι] [Finite G.Outcome]
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    G.exactImplementationCosts ({z} : Set (Profile G)) =
      Set.Ici (∑ i, G.implementationGap z i) := by
  rw [exactImplementationCosts_singleton_eq_implementationCosts,
    implementationCosts_singleton_eq_Ici (G := G) z hnd]

/-- Exact singleton implementation price: exactness costs no more for singleton
targets under the nondegenerate hypotheses that attain the ordinary singleton
price. -/
theorem exactImplPrice_singleton_of_singletonNondegenerate [Fintype ι]
    [Finite G.Outcome]
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    G.exactImplPrice ({z} : Set (Profile G)) = ∑ i, G.implementationGap z i := by
  rw [exactImplPrice_singleton_eq_implPrice,
    implPrice_singleton_of_singletonNondegenerate (G := G) z hnd]

/-- Exact singleton implementation price: exactness has the same infimum price
as ordinary implementation for singleton targets. -/
theorem exactImplPrice_singleton [Fintype ι] [Nonempty ι] [Finite G.Outcome]
    (z : Profile G) :
    G.exactImplPrice ({z} : Set (Profile G)) = ∑ i, G.implementationGap z i := by
  rw [exactImplPrice_singleton_eq_implPrice, implPrice_singleton (G := G) z]

theorem implementationGap_eq_zero_of_isNash
    (z : Profile G) (hN : G.IsNash z) (i : ι) :
    G.implementationGap z i = 0 := by
  apply le_antisymm
  · letI : Fintype (G.Strategy i) := strategyFintype i
    letI : Nonempty (G.Strategy i) := strategyNonempty i
    unfold implementationGap implementationGapAt
    apply Finset.sup'_le
    intro s _
    have hdev := hN i s
    simpa [Function.update_eq_self] using sub_nonpos.mpr hdev
  · exact implementationGap_nonneg (G := G) z i

theorem isNash_of_implementationGap_sum_nonpos
    [Fintype ι]
    (z : Profile G) (hgap : (∑ i, G.implementationGap z i) ≤ 0) :
    G.IsNash z := by
  intro i s
  have hterm_le_sum :
      G.implementationGap z i ≤ ∑ j, G.implementationGap z j :=
    Finset.single_le_sum
      (fun j _ => implementationGap_nonneg (G := G) z j)
      (Finset.mem_univ i)
  have hgap_i : G.implementationGap z i ≤ 0 := hterm_le_sum.trans hgap
  have hdev := implementationGap_ge (G := G) z i s
  linarith

omit strategyFintype in
/-- Any zero-budget singleton implementation forces the target profile to be a
Nash equilibrium. This direction needs no nondegenerate strict witness. -/
theorem isNash_of_exists_zero_singletonKImplementation
    [Fintype ι] [Finite G.Outcome] [∀ i, Finite (G.Strategy i)]
    (z : Profile G) :
    (∃ V : Profile G → Payoff ι,
      G.IsKImplementation V ({z} : Set (Profile G)) 0) → G.IsNash z := by
  letI : ∀ i, Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  rintro ⟨V, hV⟩
  have hsum :
      (∑ i, G.implementationGap z i) ≤ 0 :=
    singletonKImplementation_lower_bound (G := G) (V := V) (z := z) hV
  exact isNash_of_implementationGap_sum_nonpos (G := G) z hsum

omit strategyFintype in
/-- Corollary 1 for singleton targets: `z` is Nash iff `{z}` is
0-implementable. -/
theorem exists_zero_singletonKImplementation_iff_isNash [Fintype ι] [Finite G.Outcome]
    [∀ i, Finite (G.Strategy i)]
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    (∃ V : Profile G → Payoff ι,
      G.IsKImplementation V ({z} : Set (Profile G)) 0) ↔ G.IsNash z := by
  letI : ∀ i, Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  constructor
  · intro h
    exact isNash_of_exists_zero_singletonKImplementation (G := G) z h
  · intro hN
    have hsum : (∑ i, G.implementationGap z i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact implementationGap_eq_zero_of_isNash (G := G) z hN i
    exact (singletonKImplementation_iff (G := G) z hnd 0).mpr (by
      rw [hsum])

omit strategyFintype in
/-- Exact zero-budget singleton implementation also forces Nash, without any
nondegeneracy hypothesis. -/
theorem isNash_of_exists_zero_exactSingletonKImplementation
    [Fintype ι] [Finite G.Outcome] [∀ i, Finite (G.Strategy i)]
    (z : Profile G) :
    (∃ V : Profile G → Payoff ι,
      G.IsExactKImplementation V ({z} : Set (Profile G)) 0) → G.IsNash z := by
  intro h
  exact isNash_of_exists_zero_singletonKImplementation (G := G) z <| by
    obtain ⟨V, hV⟩ := h
    exact ⟨V, hV.toKImplementation ⟨z, by simp⟩⟩

omit strategyFintype in
/-- Exact version of the singleton zero-implementation/Nash equivalence. -/
theorem exists_zero_exactSingletonKImplementation_iff_isNash
    [Fintype ι] [Finite G.Outcome] [∀ i, Finite (G.Strategy i)]
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    (∃ V : Profile G → Payoff ι,
      G.IsExactKImplementation V ({z} : Set (Profile G)) 0) ↔ G.IsNash z := by
  constructor
  · rintro ⟨V, hV⟩
    exact isNash_of_exists_zero_exactSingletonKImplementation (G := G) z
      ⟨V, hV⟩
  · intro hN
    obtain ⟨V, hV⟩ :=
      (exists_zero_singletonKImplementation_iff_isNash (G := G) z hnd).mpr hN
    exact ⟨V, hV.toExactKImplementation_singleton⟩

end Construction

end KernelGame

end GameTheory
