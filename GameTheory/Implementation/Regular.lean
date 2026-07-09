/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation.Singleton
import Math.Topology.WeakDominance
import GameTheory.Concepts.Equilibrium.SolutionConcepts
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Regular-game k-implementation

This file packages the analytic version of Monderer--Tennenholtz Theorem 2.
For compact own-strategy spaces, upper-semicontinuity replaces the finite ascent
lemma used in finite games: every best response has an undominated weak
dominator.  Under the corresponding transfer admissibility condition, singleton
implementation has the same price formula as in finite games, with the finite
maximum replaced by a compact supremum.

The theorem is intentionally stated for kernel games whose subsidies separate
expected utility additively.  Finite-outcome kernels satisfy this automatically,
and direct normal-form games built by `KernelGame.ofEU` satisfy it because their
outcome kernels are point masses.
-/

noncomputable section

namespace GameTheory

open Math.Probability

namespace KernelGame

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- A kernel game has additive profile-observed subsidies when expected utility
in the subsidized game is the original expected utility plus the transfer at
the played profile.  This is automatic for finite-outcome kernels and for
direct `ofEU` games. -/
class HasAdditiveSubsidyEU (G : KernelGame ι) : Prop where
  subsidize_eu :
    ∀ (V : Profile G → Payoff ι) (σ : Profile G) (i : ι),
      (G.subsidize V).eu σ i = G.eu σ i + V σ i

instance hasAdditiveSubsidyEU_of_finiteOutcome (G : KernelGame ι)
    [Finite G.Outcome] : G.HasAdditiveSubsidyEU where
  subsidize_eu := fun V σ i => KernelGame.subsidize_eu G V σ i

omit [DecidableEq ι] [Fintype ι] in
@[simp] theorem ofEU_subsidize_eu (S : ι → Type) (u : (∀ i, S i) → Payoff ι)
    (V : Profile (KernelGame.ofEU S u) → Payoff ι)
    (σ : Profile (KernelGame.ofEU S u)) (i : ι) :
    (((KernelGame.ofEU S u).subsidize V).eu σ i) =
      (KernelGame.ofEU S u).eu σ i + V σ i := by
  change
    expect (PMF.map (fun ω : Payoff ι => (σ, ω)) (PMF.pure (u σ)))
        (fun p : Profile (KernelGame.ofEU S u) × Payoff ι => p.2 i + V p.1 i) =
      expect (PMF.pure (u σ)) (fun ω : Payoff ι => ω i) + V σ i
  rw [PMF.pure_map]
  simp [expect_pure]

instance hasAdditiveSubsidyEU_ofEU (S : ι → Type)
    (u : (∀ i, S i) → Payoff ι) :
    (KernelGame.ofEU S u).HasAdditiveSubsidyEU where
  subsidize_eu := ofEU_subsidize_eu S u

/-- Own upper-semicontinuity of payoffs: with opponents fixed, each player's
payoff is upper-semicontinuous in that player's own strategy. -/
def RegularOwnUpperSemicontinuous (G : KernelGame ι)
    [∀ i, TopologicalSpace (G.Strategy i)] : Prop :=
  ∀ i : ι, ∀ σ : Profile G,
    UpperSemicontinuousOn
      (fun s : G.Strategy i => G.eu (Function.update σ i s) i) Set.univ

omit [Fintype ι] in
/-- In a compact own-USC game, every strategy is weakly dominated by an
undominated strategy, with weak dominance understood pointwise over opponent
profiles. -/
theorem RegularOwnUpperSemicontinuous.exists_undominated_dominator
    {G : KernelGame ι} [∀ i, TopologicalSpace (G.Strategy i)]
    [∀ i, CompactSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (i : ι) (s : G.Strategy i) :
    ∃ t : G.Strategy i, G.WeaklyDominates i t s ∧ G.IsUndominated i t := by
  classical
  let W : G.Strategy i → Profile G → ℝ := fun t σ =>
    G.eu (Function.update σ i t) i
  have hWusc : ∀ σ : Profile G,
      UpperSemicontinuousOn (fun t : G.Strategy i => W t σ) Set.univ := by
    intro σ
    exact husc i σ
  obtain ⟨t, hweak, hundom⟩ :=
    Math.Topology.exists_pointwiseUndominated_dominator_of_compact_usc
      W hWusc s
  refine ⟨t, hweak, ?_⟩
  intro u hu
  apply hundom u
  refine ⟨?_, ?_⟩
  · intro σ
    exact hu.toWeaklyDominates σ
  · obtain ⟨σ, hstrict⟩ := hu.strict_witness
    exact ⟨σ, hstrict⟩

omit [Fintype ι] in
/-- Compact own-USC games have an undominated strategy for every nonempty
player strategy space. -/
theorem RegularOwnUpperSemicontinuous.exists_undominated_strategy
    {G : KernelGame ι} [∀ i, TopologicalSpace (G.Strategy i)]
    [∀ i, CompactSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (i : ι) [Nonempty (G.Strategy i)] :
    ∃ t : G.Strategy i, G.IsUndominated i t := by
  obtain ⟨t, _hweak, hundom⟩ :=
    husc.exists_undominated_dominator i (Classical.arbitrary (G.Strategy i))
  exact ⟨t, hundom⟩

omit [Fintype ι] in
/-- Compact own-USC games with nonempty strategy spaces have nonempty
undominated-profile sets. -/
theorem RegularOwnUpperSemicontinuous.undominatedProfiles_nonempty
    {G : KernelGame ι} [∀ i, TopologicalSpace (G.Strategy i)]
    [∀ i, CompactSpace (G.Strategy i)]
    [∀ i, Nonempty (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous) :
    G.undominatedProfiles.Nonempty := by
  choose s hs using fun i => husc.exists_undominated_strategy i
  exact ⟨s, fun i => hs i⟩

/-- Semantic admissibility condition for regular singleton implementation:
against the target opponents, every player has an undominated best response in
the subsidized game.  Compact own-USC hypotheses imply this condition. -/
def RegularSelectionAdmissibleAt (G : KernelGame ι)
    (V : Profile G → Payoff ι) (z : Profile G) : Prop :=
  ∀ i : ι, ∃ s : G.Strategy i,
    (∀ t : G.Strategy i,
      (G.subsidize V).eu (Function.update z i s) i ≥
        (G.subsidize V).eu (Function.update z i t) i) ∧
      (G.subsidize V).IsUndominated i s

/-- Analytic admissibility for regular singleton implementation: the subsidized
game has own upper-semicontinuous payoffs. -/
def RegularAnalyticAdmissible (G : KernelGame ι)
    [∀ i, TopologicalSpace (G.Strategy i)]
    (V : Profile G → Payoff ι) : Prop :=
  ∀ i : ι, ∀ σ : Profile G,
    UpperSemicontinuousOn
      (fun s : G.Strategy i =>
        (G.subsidize V).eu (Function.update σ i s) i) Set.univ

omit [Fintype ι] in
theorem RegularSelectionAdmissibleAt.of_dominant
    {G : KernelGame ι} {V : Profile G → Payoff ι} {z : Profile G}
    (hdom : ∀ i, (G.subsidize V).IsDominant i (z i)) :
    G.RegularSelectionAdmissibleAt V z := by
  intro i
  refine ⟨z i, ?_, (hdom i).isUndominated⟩
  intro t
  simpa [Function.update_eq_self] using hdom i z t

omit [Fintype ι] in
/-- Analytic admissibility implies the semantic selection condition on compact
own-strategy spaces. -/
theorem RegularAnalyticAdmissible.selectionAdmissible
    {G : KernelGame ι} [∀ i, TopologicalSpace (G.Strategy i)]
    [∀ i, CompactSpace (G.Strategy i)]
    {V : Profile G → Payoff ι} {z : Profile G}
    (husc : G.RegularAnalyticAdmissible V) :
    G.RegularSelectionAdmissibleAt V z := by
  classical
  intro i
  let f : G.Strategy i → ℝ := fun s =>
    (G.subsidize V).eu (Function.update z i s) i
  obtain ⟨s₀, -, hs₀max⟩ :=
    (husc i z).exists_isMaxOn (s := Set.univ)
      ⟨z i, Set.mem_univ _⟩ isCompact_univ
  have hbest₀ : ∀ t : G.Strategy i,
      (G.subsidize V).eu (Function.update z i s₀) i ≥
        (G.subsidize V).eu (Function.update z i t) i := by
    intro t
    exact hs₀max (Set.mem_univ t)
  let W : G.Strategy i → Profile G → ℝ := fun s σ =>
    (G.subsidize V).eu (Function.update σ i s) i
  have hWusc : ∀ σ : Profile G,
      UpperSemicontinuousOn (fun s : G.Strategy i => W s σ) Set.univ := by
    intro σ
    exact husc i σ
  obtain ⟨s, hsdom, hsundom⟩ :=
    Math.Topology.exists_pointwiseUndominated_dominator_of_compact_usc
      W hWusc s₀
  refine ⟨s, ?_, ?_⟩
  · intro t
    exact (hbest₀ t).trans (hsdom z)
  · intro t ht
    have hpoint :
        Math.Topology.PointwiseWeaklyStrictlyDominates W t s := by
      refine ⟨?_, ?_⟩
      · intro σ
        exact ht.toWeaklyDominates σ
      · obtain ⟨σ, hstrict⟩ := ht.strict_witness
        exact ⟨σ, hstrict⟩
    exact hsundom t hpoint

section CompactSupremum

variable {G : KernelGame ι}
variable [∀ i, TopologicalSpace (G.Strategy i)]
variable [∀ i, CompactSpace (G.Strategy i)]

/-- Compact-strategy implementation gap.  It is the supremum one player can
gain by deviating while opponents are held fixed at `σ`, measured relative to
the target action `z i`. -/
noncomputable def regularImplementationGapAt
    (G : KernelGame ι) (z : Profile G) (i : ι) (σ : Profile G) : ℝ :=
  sSup (Set.range fun s : G.Strategy i =>
    G.eu (Function.update σ i s) i -
      G.eu (Function.update σ i (z i)) i)

/-- The target-profile contribution to the regular singleton price. -/
noncomputable def regularImplementationGap
    (G : KernelGame ι) (z : Profile G) (i : ι) : ℝ :=
  G.regularImplementationGapAt z i z

omit [Fintype ι] in
theorem regularImplementationGapAt_bddAbove
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (i : ι) (σ : Profile G) :
    BddAbove (Set.range fun s : G.Strategy i =>
      G.eu (Function.update σ i s) i -
        G.eu (Function.update σ i (z i)) i) := by
  classical
  let f : G.Strategy i → ℝ := fun s => G.eu (Function.update σ i s) i
  obtain ⟨s₀, -, hs₀max⟩ :=
    (husc i σ).exists_isMaxOn (s := Set.univ)
      ⟨z i, Set.mem_univ _⟩ isCompact_univ
  refine ⟨f s₀ - f (z i), ?_⟩
  rintro x ⟨s, rfl⟩
  have hs := hs₀max (Set.mem_univ s)
  dsimp [f] at hs ⊢
  linarith

omit [Fintype ι] in
theorem regularImplementationGapAt_ge
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (i : ι) (σ : Profile G) (s : G.Strategy i) :
    G.eu (Function.update σ i s) i -
        G.eu (Function.update σ i (z i)) i ≤
      G.regularImplementationGapAt z i σ := by
  classical
  exact le_csSup
    (regularImplementationGapAt_bddAbove (G := G) husc z i σ)
    (Set.mem_range_self s)

omit [Fintype ι] in
theorem regularImplementationGapAt_nonneg
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (i : ι) (σ : Profile G) :
    0 ≤ G.regularImplementationGapAt z i σ := by
  have h := regularImplementationGapAt_ge (G := G) husc z i σ (z i)
  simpa using h

omit [Fintype ι] in
theorem regularImplementationGap_nonneg
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (i : ι) :
    0 ≤ G.regularImplementationGap z i := by
  simpa [regularImplementationGap] using
    regularImplementationGapAt_nonneg (G := G) husc z i z

omit [Fintype ι] [∀ i, TopologicalSpace (G.Strategy i)]
  [∀ i, CompactSpace (G.Strategy i)] in
theorem regularImplementationGapAt_le_transfer_of_admissibleImplementation
    [G.HasAdditiveSubsidyEU]
    {V : Profile G → Payoff ι} {z : Profile G}
    (hV : G.IsImplementation V ({z} : Set (Profile G)))
    (hadm : G.RegularSelectionAdmissibleAt V z) (i : ι) :
    G.regularImplementationGapAt z i z ≤ V z i := by
  classical
  obtain ⟨s, hbest, hsundom⟩ := hadm i
  have hzundom := singleton_target_undominated_of_isImplementation (G := G) hV
  have hprof : Function.update z i s ∈
      (G.subsidize V).undominatedProfiles := by
    intro j
    by_cases hji : j = i
    · subst hji
      simpa using hsundom
    · simpa [Function.update_of_ne hji] using hzundom j
  have hseq : s = z i := by
    have hmem := hV.subset (Function.update z i s) hprof
    have heq : Function.update z i s = z := Set.mem_singleton_iff.mp hmem
    simpa using congrFun heq i
  have hgain_le : ∀ t : G.Strategy i,
      G.eu (Function.update z i t) i - G.eu z i ≤ V z i := by
    intro t
    have hbest_t := hbest t
    rw [hseq] at hbest_t
    rw [HasAdditiveSubsidyEU.subsidize_eu,
      HasAdditiveSubsidyEU.subsidize_eu] at hbest_t
    simp only [Function.update_eq_self, ge_iff_le] at hbest_t
    have hbest_le :
        G.eu (Function.update z i t) i + V (Function.update z i t) i ≤
          G.eu z i + V z i := hbest_t
    have hVdev : 0 ≤ V (Function.update z i t) i := hV.nonneg _ _
    have hsub1 :
        G.eu (Function.update z i t) i - G.eu z i ≤
          (G.eu (Function.update z i t) i +
              V (Function.update z i t) i) - G.eu z i :=
      sub_le_sub_right (le_add_of_nonneg_right hVdev) _
    have hsub2 :
        (G.eu (Function.update z i t) i + V (Function.update z i t) i) -
            G.eu z i ≤ V z i := by
      rw [sub_le_iff_le_add]
      simpa [add_comm, add_left_comm, add_assoc] using hbest_le
    exact hsub1.trans hsub2
  rw [regularImplementationGapAt]
  apply csSup_le
  · exact ⟨0, by
      refine ⟨z i, ?_⟩
      simp [Function.update_eq_self]⟩
  · rintro x ⟨t, rfl⟩
    simpa [Function.update_eq_self] using hgain_le t

omit [∀ i, TopologicalSpace (G.Strategy i)]
  [∀ i, CompactSpace (G.Strategy i)] in
theorem regularSingletonKImplementation_lower_bound_of_admissible
    [G.HasAdditiveSubsidyEU]
    {V : Profile G → Payoff ι} {z : Profile G} {k : ℝ}
    (hadm : G.RegularSelectionAdmissibleAt V z)
    (hV : G.IsKImplementation V ({z} : Set (Profile G)) k) :
    (∑ i, G.regularImplementationGap z i) ≤ k := by
  have hzundom := singleton_target_undominated_of_isImplementation (G := G)
    hV.implementation
  calc
    (∑ i, G.regularImplementationGap z i) ≤ ∑ i, V z i := by
      exact Finset.sum_le_sum fun i _ =>
        regularImplementationGapAt_le_transfer_of_admissibleImplementation
          (G := G) (V := V) (z := z) hV.implementation hadm i
    _ ≤ k := hV.cost_bound z hzundom

theorem regularSingletonKImplementation_lower_bound_of_analytic
    [G.HasAdditiveSubsidyEU]
    {V : Profile G → Payoff ι} {z : Profile G} {k : ℝ}
    (han : G.RegularAnalyticAdmissible V)
    (hV : G.IsKImplementation V ({z} : Set (Profile G)) k) :
    (∑ i, G.regularImplementationGap z i) ≤ k :=
  regularSingletonKImplementation_lower_bound_of_admissible
    (G := G) (V := V) (z := z)
    han.selectionAdmissible hV

/-- Positive-slack transfer for regular singleton implementation. -/
noncomputable def regularSingletonApproxTransfer
    (G : KernelGame ι) (z : Profile G) (ε : ι → ℝ) :
    Profile G → Payoff ι :=
  open Classical in
  fun σ i => if σ i = z i then G.regularImplementationGapAt z i σ + ε i else 0

omit [Fintype ι] [∀ i, TopologicalSpace (G.Strategy i)]
  [∀ i, CompactSpace (G.Strategy i)] in
@[simp] theorem regularSingletonApproxTransfer_target
    (z : Profile G) (ε : ι → ℝ) (i : ι) :
    G.regularSingletonApproxTransfer z ε z i =
      G.regularImplementationGap z i + ε i := by
  classical
  simp [regularSingletonApproxTransfer, regularImplementationGap]

omit [Fintype ι] [∀ i, TopologicalSpace (G.Strategy i)]
  [∀ i, CompactSpace (G.Strategy i)] in
@[simp] theorem regularSingletonApproxTransfer_update_target
    (z : Profile G) (ε : ι → ℝ) (i : ι) (σ : Profile G) :
    G.regularSingletonApproxTransfer z ε (Function.update σ i (z i)) i =
      G.regularImplementationGapAt z i (Function.update σ i (z i)) + ε i := by
  classical
  simp [regularSingletonApproxTransfer]

omit [Fintype ι] [∀ i, TopologicalSpace (G.Strategy i)]
  [∀ i, CompactSpace (G.Strategy i)] in
theorem regularSingletonApproxTransfer_update_ne
    (z : Profile G) (ε : ι → ℝ) (i : ι) (σ : Profile G)
    {s : G.Strategy i} (hs : s ≠ z i) :
    G.regularSingletonApproxTransfer z ε (Function.update σ i s) i = 0 := by
  classical
  rw [regularSingletonApproxTransfer, if_neg]
  simpa using hs

omit [Fintype ι] in
theorem regularSingletonApproxTransfer_nonneg
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) {ε : ι → ℝ} (hε : ∀ i, 0 ≤ ε i) :
    ∀ σ i, 0 ≤ G.regularSingletonApproxTransfer z ε σ i := by
  classical
  intro σ i
  by_cases hi : σ i = z i
  · have hgap := regularImplementationGapAt_nonneg (G := G) husc z i σ
    rw [regularSingletonApproxTransfer, if_pos hi]
    exact add_nonneg hgap (hε i)
  · rw [regularSingletonApproxTransfer, if_neg hi]

omit [Fintype ι] in
theorem regularSingletonApproxTransfer_target_isDominant
    [G.HasAdditiveSubsidyEU]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) {ε : ι → ℝ} (hε : ∀ i, 0 ≤ ε i) (i : ι) :
    (G.subsidize (G.regularSingletonApproxTransfer z ε)).IsDominant
      i (z i) := by
  classical
  intro σ s
  let τ : Profile G := σ
  let t : G.Strategy i := s
  change (G.subsidize (G.regularSingletonApproxTransfer z ε)).eu
      (Function.update τ i (z i)) i ≥
    (G.subsidize (G.regularSingletonApproxTransfer z ε)).eu
      (Function.update τ i t) i
  by_cases hs : t = z i
  · simp [t, hs]
  · have hgap := regularImplementationGapAt_ge (G := G) husc z i
      (Function.update τ i (z i)) t
    have hgap' :
        G.eu (Function.update τ i t) i -
            G.eu (Function.update τ i (z i)) i ≤
          G.regularImplementationGapAt z i (Function.update τ i (z i)) := by
      simpa [Function.update_idem] using hgap
    rw [HasAdditiveSubsidyEU.subsidize_eu,
      HasAdditiveSubsidyEU.subsidize_eu]
    simp only [subsidize_Strategy, regularSingletonApproxTransfer_update_target,
      ge_iff_le]
    rw [regularSingletonApproxTransfer_update_ne (G := G) z ε i τ hs]
    simp only [add_zero]
    linarith [hgap', hε i]

omit [Fintype ι] in
theorem regularSingletonApproxTransfer_weaklyStrictlyDominates_ne
    [G.HasAdditiveSubsidyEU]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) {ε : ι → ℝ} (hεpos : ∀ i, 0 < ε i)
    {i : ι} {s : G.Strategy i} (hs : s ≠ z i) :
    (G.subsidize (G.regularSingletonApproxTransfer z ε)).WeaklyStrictlyDominates
      i (z i) s := by
  classical
  refine ⟨(regularSingletonApproxTransfer_target_isDominant (G := G) husc z
    (fun i => le_of_lt (hεpos i)) i).weaklyDominates s, ?_⟩
  refine ⟨z, ?_⟩
  have hgap := regularImplementationGapAt_ge (G := G) husc z i z s
  have hgap' :
      G.eu (Function.update z i s) i - G.eu z i ≤
        G.regularImplementationGapAt z i z := by
    simpa [Function.update_eq_self] using hgap
  rw [HasAdditiveSubsidyEU.subsidize_eu,
    HasAdditiveSubsidyEU.subsidize_eu]
  change G.eu (Function.update z i (z i)) i +
      G.regularSingletonApproxTransfer z ε (Function.update z i (z i)) i >
    G.eu (Function.update z i s) i +
      G.regularSingletonApproxTransfer z ε (Function.update z i s) i
  simp [regularSingletonApproxTransfer, hs, Function.update_eq_self]
  linarith [hgap', hεpos i]

omit [Fintype ι] in
theorem regularSingletonApproxTransfer_isImplementation
    [G.HasAdditiveSubsidyEU]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) {ε : ι → ℝ} (hεpos : ∀ i, 0 < ε i) :
    G.IsImplementation (G.regularSingletonApproxTransfer z ε)
      ({z} : Set (Profile G)) := by
  refine ⟨regularSingletonApproxTransfer_nonneg (G := G) husc z
    (fun i => le_of_lt (hεpos i)), ?_, ?_⟩
  · exact ⟨z, fun i =>
      (regularSingletonApproxTransfer_target_isDominant (G := G) husc z
        (fun i => le_of_lt (hεpos i)) i).isUndominated⟩
  · intro σ hσ
    apply Set.mem_singleton_iff.mpr
    funext i
    by_contra hne
    exact (hσ i (z i)
      (regularSingletonApproxTransfer_weaklyStrictlyDominates_ne
        (G := G) husc z hεpos hne)).elim

theorem regularSingletonApproxTransfer_isKImplementation
    [G.HasAdditiveSubsidyEU]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) {ε : ι → ℝ} (hεpos : ∀ i, 0 < ε i) :
    G.IsKImplementation (G.regularSingletonApproxTransfer z ε)
      ({z} : Set (Profile G))
      (∑ i, (G.regularImplementationGap z i + ε i)) := by
  refine ⟨regularSingletonApproxTransfer_isImplementation
    (G := G) husc z hεpos, ?_⟩
  intro σ hσ
  have hσz : σ = z := Set.mem_singleton_iff.mp
    ((regularSingletonApproxTransfer_isImplementation
      (G := G) husc z hεpos).subset σ hσ)
  subst σ
  simp [regularSingletonApproxTransfer, regularImplementationGap]

omit [Fintype ι] in
theorem regularSingletonApproxTransfer_analyticAdmissible
    [G.HasAdditiveSubsidyEU] [∀ i, T1Space (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (ε : ι → ℝ) (hε : ∀ i, 0 ≤ ε i) :
    G.RegularAnalyticAdmissible (G.regularSingletonApproxTransfer z ε) := by
  classical
  intro i σ
  let y : G.Strategy i := z i
  let base : G.Strategy i → ℝ := fun s => G.eu (Function.update σ i s) i
  let top : ℝ :=
    base y +
      G.regularImplementationGapAt z i (Function.update σ i y) + ε i
  have hbase : UpperSemicontinuous base :=
    upperSemicontinuousOn_univ_iff.mp (husc i σ)
  have hbase_le_top : base y ≤ top := by
    have hgap :
        0 ≤ G.regularImplementationGapAt z i (Function.update σ i y) :=
      regularImplementationGapAt_nonneg (G := G) husc z i (Function.update σ i y)
    dsimp [top]
    linarith [hgap, hε i]
  have hspike :
      UpperSemicontinuous (fun s : G.Strategy i =>
        if s = y then top else base s) :=
    Math.Topology.UpperSemicontinuous.update_of_le hbase hbase_le_top
  have heq :
      (fun s : G.Strategy i =>
        (G.subsidize (G.regularSingletonApproxTransfer z ε)).eu
          (Function.update σ i s) i)
      =
        (fun s : G.Strategy i => if s = y then top else base s) := by
    funext s
    rw [HasAdditiveSubsidyEU.subsidize_eu]
    change G.eu (Function.update σ i s) i +
        G.regularSingletonApproxTransfer z ε (Function.update σ i s) i =
      if s = y then top else base s
    by_cases hs : s = y
    · subst hs
      rw [regularSingletonApproxTransfer_update_target]
      simp [base, top, y]
      ring
    · have hs' : s ≠ z i := by simpa [y] using hs
      rw [regularSingletonApproxTransfer_update_ne (G := G) z ε i σ hs']
      simp [base, hs, y]
  rw [heq]
  exact upperSemicontinuousOn_univ_iff.mpr hspike

/-- Distance from the target on all opponents of player `i`. -/
noncomputable def regularOpponentDist
    [∀ i, PseudoMetricSpace (G.Strategy i)]
    (z σ : Profile G) (i : ι) : ℝ :=
  (Finset.univ.erase i).sum fun j => dist (σ j) (z j)

omit [∀ i, TopologicalSpace (G.Strategy i)]
  [∀ i, CompactSpace (G.Strategy i)] in
theorem regularOpponentDist_nonneg
    [∀ i, PseudoMetricSpace (G.Strategy i)]
    (z σ : Profile G) (i : ι) :
    0 ≤ G.regularOpponentDist z σ i := by
  exact Finset.sum_nonneg fun j _ => dist_nonneg

omit [∀ i, TopologicalSpace (G.Strategy i)]
  [∀ i, CompactSpace (G.Strategy i)] in
@[simp] theorem regularOpponentDist_target
    [∀ i, PseudoMetricSpace (G.Strategy i)]
    (z : Profile G) (i : ι) :
    G.regularOpponentDist z z i = 0 := by
  simp [regularOpponentDist]

omit [∀ i, TopologicalSpace (G.Strategy i)]
  [∀ i, CompactSpace (G.Strategy i)] in
theorem regularOpponentDist_update_pos
    [∀ i, MetricSpace (G.Strategy i)]
    (z : Profile G) {i j : ι} (hji : j ≠ i)
    {a : G.Strategy j} (ha : a ≠ z j) :
    0 < G.regularOpponentDist z (Function.update z j a) i := by
  classical
  have hjmem : j ∈ Finset.univ.erase i :=
    Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
  have hterm :
      0 < dist ((Function.update z j a) j) (z j) := by
    simpa using (dist_pos.mpr ha)
  exact hterm.trans_le
    (Finset.single_le_sum
      (s := Finset.univ.erase i)
      (f := fun l => dist ((Function.update z j a) l) (z l))
      (fun _ _ => dist_nonneg)
      hjmem)

/-- Exact regular transfer.  It pays the compact gap when the player chooses the
target action and adds an opponent-distance bump that vanishes at the target. -/
noncomputable def regularSingletonDistanceTransfer
    (G : KernelGame ι) [∀ i, PseudoMetricSpace (G.Strategy i)]
    (z : Profile G) : Profile G → Payoff ι :=
  open Classical in
  fun σ i =>
    if σ i = z i then
      G.regularImplementationGapAt z i σ + G.regularOpponentDist z σ i
    else 0

omit [∀ i, TopologicalSpace (G.Strategy i)]
  [∀ i, CompactSpace (G.Strategy i)] in
@[simp] theorem regularSingletonDistanceTransfer_target
    [∀ i, PseudoMetricSpace (G.Strategy i)]
    (z : Profile G) (i : ι) :
    G.regularSingletonDistanceTransfer z z i =
      G.regularImplementationGap z i := by
  classical
  simp [regularSingletonDistanceTransfer, regularImplementationGap]

omit [∀ i, TopologicalSpace (G.Strategy i)]
  [∀ i, CompactSpace (G.Strategy i)] in
@[simp] theorem regularSingletonDistanceTransfer_update_target
    [∀ i, PseudoMetricSpace (G.Strategy i)]
    (z : Profile G) (i : ι) (σ : Profile G) :
    G.regularSingletonDistanceTransfer z (Function.update σ i (z i)) i =
      G.regularImplementationGapAt z i (Function.update σ i (z i)) +
        G.regularOpponentDist z (Function.update σ i (z i)) i := by
  classical
  simp [regularSingletonDistanceTransfer]

omit [∀ i, TopologicalSpace (G.Strategy i)]
  [∀ i, CompactSpace (G.Strategy i)] in
theorem regularSingletonDistanceTransfer_update_ne
    [∀ i, PseudoMetricSpace (G.Strategy i)]
    (z : Profile G) (i : ι) (σ : Profile G)
    {s : G.Strategy i} (hs : s ≠ z i) :
    G.regularSingletonDistanceTransfer z (Function.update σ i s) i = 0 := by
  classical
  rw [regularSingletonDistanceTransfer, if_neg]
  simpa using hs

theorem regularSingletonDistanceTransfer_nonneg
    [∀ i, PseudoMetricSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) :
    ∀ σ i, 0 ≤ G.regularSingletonDistanceTransfer z σ i := by
  classical
  intro σ i
  by_cases hi : σ i = z i
  · have hgap := regularImplementationGapAt_nonneg (G := G) husc z i σ
    have hdist := regularOpponentDist_nonneg (G := G) z σ i
    rw [regularSingletonDistanceTransfer, if_pos hi]
    exact add_nonneg hgap hdist
  · rw [regularSingletonDistanceTransfer, if_neg hi]

theorem regularSingletonDistanceTransfer_target_isDominant
    [G.HasAdditiveSubsidyEU] [∀ i, PseudoMetricSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (i : ι) :
    (G.subsidize (G.regularSingletonDistanceTransfer z)).IsDominant
      i (z i) := by
  classical
  intro σ s
  let τ : Profile G := σ
  let t : G.Strategy i := s
  change (G.subsidize (G.regularSingletonDistanceTransfer z)).eu
      (Function.update τ i (z i)) i ≥
    (G.subsidize (G.regularSingletonDistanceTransfer z)).eu
      (Function.update τ i t) i
  by_cases hs : t = z i
  · simp [t, hs]
  · have hgap := regularImplementationGapAt_ge (G := G) husc z i
      (Function.update τ i (z i)) t
    have hgap' :
        G.eu (Function.update τ i t) i -
            G.eu (Function.update τ i (z i)) i ≤
          G.regularImplementationGapAt z i (Function.update τ i (z i)) := by
      simpa [Function.update_idem] using hgap
    rw [HasAdditiveSubsidyEU.subsidize_eu,
      HasAdditiveSubsidyEU.subsidize_eu]
    simp only [subsidize_Strategy, regularSingletonDistanceTransfer_update_target,
      ge_iff_le]
    rw [regularSingletonDistanceTransfer_update_ne (G := G) z i τ hs]
    simp only [add_zero]
    have hdist :
        0 ≤ G.regularOpponentDist z (Function.update τ i (z i)) i :=
      regularOpponentDist_nonneg (G := G) z (Function.update τ i (z i)) i
    linarith [hgap', hdist]

theorem regularSingletonDistanceTransfer_weaklyStrictlyDominates_ne
    [G.HasAdditiveSubsidyEU] [∀ i, MetricSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (hnd : G.SingletonNondegenerate z)
    {i : ι} {s : G.Strategy i} (hs : s ≠ z i) :
    (G.subsidize (G.regularSingletonDistanceTransfer z)).WeaklyStrictlyDominates
      i (z i) s := by
  classical
  refine ⟨(regularSingletonDistanceTransfer_target_isDominant
    (G := G) husc z i).weaklyDominates s, ?_⟩
  obtain ⟨j, hji, a, ha⟩ := hnd i
  let σ : Profile G := Function.update z j a
  have hdist_pos :
      0 < G.regularOpponentDist z (Function.update σ i (z i)) i := by
    have hupdate : Function.update σ i (z i) = Function.update z j a := by
      funext l
      by_cases hli : l = i
      · subst hli
        simp [σ, Function.update_of_ne hji.symm]
      · simp [σ, Function.update_of_ne hli]
    rw [hupdate]
    exact regularOpponentDist_update_pos (G := G) z hji ha
  have hgap := regularImplementationGapAt_ge (G := G) husc z i
    (Function.update σ i (z i)) s
  have hgap' :
      G.eu (Function.update σ i s) i -
          G.eu (Function.update σ i (z i)) i ≤
        G.regularImplementationGapAt z i (Function.update σ i (z i)) := by
    simpa [Function.update_idem] using hgap
  refine ⟨σ, ?_⟩
  rw [HasAdditiveSubsidyEU.subsidize_eu,
    HasAdditiveSubsidyEU.subsidize_eu]
  change G.eu (Function.update σ i (z i)) i +
      G.regularSingletonDistanceTransfer z (Function.update σ i (z i)) i >
    G.eu (Function.update σ i s) i +
      G.regularSingletonDistanceTransfer z (Function.update σ i s) i
  rw [regularSingletonDistanceTransfer_update_target]
  rw [regularSingletonDistanceTransfer_update_ne (G := G) z i σ hs]
  simp only [add_zero]
  linarith

theorem regularSingletonDistanceTransfer_isImplementation
    [G.HasAdditiveSubsidyEU] [∀ i, MetricSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    G.IsImplementation (G.regularSingletonDistanceTransfer z)
      ({z} : Set (Profile G)) := by
  refine ⟨regularSingletonDistanceTransfer_nonneg (G := G) husc z, ?_, ?_⟩
  · exact ⟨z, fun i =>
      (regularSingletonDistanceTransfer_target_isDominant
        (G := G) husc z i).isUndominated⟩
  · intro σ hσ
    apply Set.mem_singleton_iff.mpr
    funext i
    by_contra hne
    exact (hσ i (z i)
      (regularSingletonDistanceTransfer_weaklyStrictlyDominates_ne
        (G := G) husc z hnd hne)).elim

theorem regularSingletonDistanceTransfer_isKImplementation
    [G.HasAdditiveSubsidyEU] [∀ i, MetricSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    G.IsKImplementation (G.regularSingletonDistanceTransfer z)
      ({z} : Set (Profile G))
      (∑ i, G.regularImplementationGap z i) := by
  refine ⟨regularSingletonDistanceTransfer_isImplementation
    (G := G) husc z hnd, ?_⟩
  intro σ hσ
  have hσz : σ = z := Set.mem_singleton_iff.mp
    ((regularSingletonDistanceTransfer_isImplementation
      (G := G) husc z hnd).subset σ hσ)
  subst σ
  simp [regularSingletonDistanceTransfer, regularImplementationGap]

theorem regularSingletonDistanceTransfer_selectionAdmissible
    [G.HasAdditiveSubsidyEU] [∀ i, MetricSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) :
    G.RegularSelectionAdmissibleAt (G.regularSingletonDistanceTransfer z) z :=
  RegularSelectionAdmissibleAt.of_dominant (G := G)
    (V := G.regularSingletonDistanceTransfer z) (z := z)
    (regularSingletonDistanceTransfer_target_isDominant (G := G) husc z)

theorem regularSingletonDistanceTransfer_analyticAdmissible
    [G.HasAdditiveSubsidyEU] [∀ i, MetricSpace (G.Strategy i)]
    [∀ i, T1Space (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) :
    G.RegularAnalyticAdmissible (G.regularSingletonDistanceTransfer z) := by
  classical
  intro i σ
  let y : G.Strategy i := z i
  let base : G.Strategy i → ℝ := fun s => G.eu (Function.update σ i s) i
  let top : ℝ :=
    base y +
      G.regularImplementationGapAt z i (Function.update σ i y) +
        G.regularOpponentDist z (Function.update σ i y) i
  have hbase : UpperSemicontinuous base :=
    upperSemicontinuousOn_univ_iff.mp (husc i σ)
  have hbase_le_top : base y ≤ top := by
    have hgap :
        0 ≤ G.regularImplementationGapAt z i (Function.update σ i y) :=
      regularImplementationGapAt_nonneg (G := G) husc z i (Function.update σ i y)
    have hdist :
        0 ≤ G.regularOpponentDist z (Function.update σ i y) i :=
      regularOpponentDist_nonneg (G := G) z (Function.update σ i y) i
    dsimp [top]
    linarith
  have hspike :
      UpperSemicontinuous (fun s : G.Strategy i =>
        if s = y then top else base s) :=
    Math.Topology.UpperSemicontinuous.update_of_le hbase hbase_le_top
  have heq :
      (fun s : G.Strategy i =>
        (G.subsidize (G.regularSingletonDistanceTransfer z)).eu
          (Function.update σ i s) i)
      =
        (fun s : G.Strategy i => if s = y then top else base s) := by
    funext s
    rw [HasAdditiveSubsidyEU.subsidize_eu]
    change G.eu (Function.update σ i s) i +
        G.regularSingletonDistanceTransfer z (Function.update σ i s) i =
      if s = y then top else base s
    by_cases hs : s = y
    · subst hs
      rw [regularSingletonDistanceTransfer_update_target]
      simp [base, top, y]
      ring
    · have hs' : s ≠ z i := by simpa [y] using hs
      rw [regularSingletonDistanceTransfer_update_ne (G := G) z i σ hs']
      simp [base, hs, y]
  rw [heq]
  exact upperSemicontinuousOn_univ_iff.mpr hspike

/-- Feasible budgets for regular singleton implementation under semantic
selection admissibility. -/
def regularAdmissibleImplementationCosts
    (G : KernelGame ι) (z : Profile G) : Set ℝ :=
  {k | ∃ V : Profile G → Payoff ι,
    G.RegularSelectionAdmissibleAt V z ∧
      G.IsKImplementation V ({z} : Set (Profile G)) k}

/-- Infimum regular singleton implementation cost under semantic admissibility. -/
noncomputable def regularAdmissibleImplPrice
    (G : KernelGame ι) (z : Profile G) : ℝ :=
  sInf (G.regularAdmissibleImplementationCosts z)

/-- Feasible budgets for regular singleton implementation under analytic
own-USC admissibility. -/
def regularAnalyticImplementationCosts
    (G : KernelGame ι) [∀ i, TopologicalSpace (G.Strategy i)]
    (z : Profile G) : Set ℝ :=
  {k | ∃ V : Profile G → Payoff ι,
    G.RegularAnalyticAdmissible V ∧
      G.IsKImplementation V ({z} : Set (Profile G)) k}

/-- Infimum regular singleton implementation cost under analytic admissibility. -/
noncomputable def regularAnalyticImplPrice
    (G : KernelGame ι) [∀ i, TopologicalSpace (G.Strategy i)]
    (z : Profile G) : ℝ :=
  sInf (G.regularAnalyticImplementationCosts z)

omit [∀ i, TopologicalSpace (G.Strategy i)]
  [∀ i, CompactSpace (G.Strategy i)] in
theorem regularAdmissibleImplementationCosts_bddBelow
    (z : Profile G) :
    BddBelow (G.regularAdmissibleImplementationCosts z) := by
  refine ⟨0, ?_⟩
  intro k hk
  obtain ⟨V, _, hV⟩ := hk
  exact hV.cost_nonneg

omit [∀ i, CompactSpace (G.Strategy i)] in
theorem regularAnalyticImplementationCosts_bddBelow
    (z : Profile G) :
    BddBelow (G.regularAnalyticImplementationCosts z) := by
  refine ⟨0, ?_⟩
  intro k hk
  obtain ⟨V, _, hV⟩ := hk
  exact hV.cost_nonneg

theorem regularAdmissibleImplementationCosts_mem_of_gap_sum_lt
    [G.HasAdditiveSubsidyEU] [Nonempty ι]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) {k : ℝ}
    (hk : (∑ i, G.regularImplementationGap z i) < k) :
    k ∈ G.regularAdmissibleImplementationCosts z := by
  classical
  let gapSum : ℝ := ∑ i, G.regularImplementationGap z i
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
  have hbudget : (∑ i, (G.regularImplementationGap z i + ε i)) = k := by
    rw [Finset.sum_add_distrib, hsumε]
    simp [gapSum]
  refine ⟨G.regularSingletonApproxTransfer z ε, ?_, ?_⟩
  · exact RegularSelectionAdmissibleAt.of_dominant (G := G)
      (V := G.regularSingletonApproxTransfer z ε) (z := z)
      (regularSingletonApproxTransfer_target_isDominant (G := G) husc z
        (fun i => le_of_lt (hεpos i)))
  · simpa [hbudget] using regularSingletonApproxTransfer_isKImplementation
      (G := G) husc z hεpos

theorem regularAnalyticImplementationCosts_mem_of_gap_sum_lt
    [G.HasAdditiveSubsidyEU] [Nonempty ι]
    [∀ i, T1Space (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) {k : ℝ}
    (hk : (∑ i, G.regularImplementationGap z i) < k) :
    k ∈ G.regularAnalyticImplementationCosts z := by
  classical
  let gapSum : ℝ := ∑ i, G.regularImplementationGap z i
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
  have hbudget : (∑ i, (G.regularImplementationGap z i + ε i)) = k := by
    rw [Finset.sum_add_distrib, hsumε]
    simp [gapSum]
  refine ⟨G.regularSingletonApproxTransfer z ε, ?_, ?_⟩
  · exact regularSingletonApproxTransfer_analyticAdmissible
      (G := G) husc z ε (fun i => le_of_lt (hεpos i))
  · simpa [hbudget] using regularSingletonApproxTransfer_isKImplementation
      (G := G) husc z hεpos

theorem regularAdmissibleImplementationCosts_mem_gap_sum_of_nondegenerate
    [G.HasAdditiveSubsidyEU] [∀ i, MetricSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    (∑ i, G.regularImplementationGap z i) ∈
      G.regularAdmissibleImplementationCosts z := by
  exact ⟨G.regularSingletonDistanceTransfer z,
    regularSingletonDistanceTransfer_selectionAdmissible (G := G) husc z,
    regularSingletonDistanceTransfer_isKImplementation (G := G) husc z hnd⟩

theorem regularAnalyticImplementationCosts_mem_gap_sum_of_nondegenerate
    [G.HasAdditiveSubsidyEU] [∀ i, MetricSpace (G.Strategy i)]
    [∀ i, T1Space (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    (∑ i, G.regularImplementationGap z i) ∈
      G.regularAnalyticImplementationCosts z := by
  exact ⟨G.regularSingletonDistanceTransfer z,
    regularSingletonDistanceTransfer_analyticAdmissible (G := G) husc z,
    regularSingletonDistanceTransfer_isKImplementation (G := G) husc z hnd⟩

private theorem sInf_eq_of_forall_lt_mem_of_forall_le
    {Costs : Set ℝ} {Price L : ℝ}
    (hPrice : Price = sInf Costs)
    (hbdd : BddBelow Costs)
    (hmem_lt : ∀ {k : ℝ}, L < k → k ∈ Costs)
    (hlower : ∀ k : ℝ, k ∈ Costs → L ≤ k) :
    Price = L := by
  have hnonempty : Costs.Nonempty := ⟨L + 1, hmem_lt (by linarith)⟩
  have hlowerPrice : L ≤ Price := by
    rw [hPrice]
    exact le_csInf hnonempty hlower
  have hupperPrice : Price ≤ L := by
    rw [hPrice]
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    exact csInf_le hbdd (hmem_lt (by linarith))
  exact le_antisymm hupperPrice hlowerPrice

private theorem sInf_eq_of_mem_of_forall_le
    {Costs : Set ℝ} {Price L : ℝ}
    (hPrice : Price = sInf Costs)
    (hbdd : BddBelow Costs)
    (hmem : L ∈ Costs)
    (hlower : ∀ k : ℝ, k ∈ Costs → L ≤ k) :
    Price = L := by
  have hnonempty : Costs.Nonempty := ⟨L, hmem⟩
  have hlowerPrice : L ≤ Price := by
    rw [hPrice]
    exact le_csInf hnonempty hlower
  have hupperPrice : Price ≤ L := by
    rw [hPrice]
    exact csInf_le hbdd hmem
  exact le_antisymm hupperPrice hlowerPrice

theorem regularAdmissibleImplPrice_singleton
    [G.HasAdditiveSubsidyEU] [Nonempty ι]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) :
    G.regularAdmissibleImplPrice z = ∑ i, G.regularImplementationGap z i := by
  classical
  let gapSum : ℝ := ∑ i, G.regularImplementationGap z i
  exact sInf_eq_of_forall_lt_mem_of_forall_le
    (Costs := G.regularAdmissibleImplementationCosts z)
    (Price := G.regularAdmissibleImplPrice z)
    (L := gapSum)
    rfl
    (regularAdmissibleImplementationCosts_bddBelow (G := G) z)
    (fun {k} hk =>
      regularAdmissibleImplementationCosts_mem_of_gap_sum_lt
        (G := G) husc z (k := k) (by simpa [gapSum] using hk))
    (fun k hk => by
      obtain ⟨V, hadm, hV⟩ := hk
      simpa [gapSum] using
        regularSingletonKImplementation_lower_bound_of_admissible
          (G := G) (V := V) (z := z) hadm hV)

theorem regularAnalyticImplPrice_singleton
    [G.HasAdditiveSubsidyEU] [Nonempty ι]
    [∀ i, T1Space (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) :
    G.regularAnalyticImplPrice z = ∑ i, G.regularImplementationGap z i := by
  classical
  let gapSum : ℝ := ∑ i, G.regularImplementationGap z i
  exact sInf_eq_of_forall_lt_mem_of_forall_le
    (Costs := G.regularAnalyticImplementationCosts z)
    (Price := G.regularAnalyticImplPrice z)
    (L := gapSum)
    rfl
    (regularAnalyticImplementationCosts_bddBelow (G := G) z)
    (fun {k} hk =>
      regularAnalyticImplementationCosts_mem_of_gap_sum_lt
        (G := G) husc z (k := k) (by simpa [gapSum] using hk))
    (fun k hk => by
      obtain ⟨V, han, hV⟩ := hk
      simpa [gapSum] using
        regularSingletonKImplementation_lower_bound_of_analytic
          (G := G) (V := V) (z := z) han hV)

theorem regularAdmissibleImplPrice_singleton_of_nondegenerate
    [G.HasAdditiveSubsidyEU] [∀ i, MetricSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    G.regularAdmissibleImplPrice z = ∑ i, G.regularImplementationGap z i := by
  classical
  let gapSum : ℝ := ∑ i, G.regularImplementationGap z i
  exact sInf_eq_of_mem_of_forall_le
    (Costs := G.regularAdmissibleImplementationCosts z)
    (Price := G.regularAdmissibleImplPrice z)
    (L := gapSum)
    rfl
    (regularAdmissibleImplementationCosts_bddBelow (G := G) z)
    (by
      simpa [gapSum] using
        regularAdmissibleImplementationCosts_mem_gap_sum_of_nondegenerate
          (G := G) husc z hnd)
    (fun k hk => by
      obtain ⟨V, hadm, hV⟩ := hk
      simpa [gapSum] using
        regularSingletonKImplementation_lower_bound_of_admissible
          (G := G) (V := V) (z := z) hadm hV)

theorem regularAnalyticImplPrice_singleton_of_nondegenerate
    [G.HasAdditiveSubsidyEU] [∀ i, MetricSpace (G.Strategy i)]
    [∀ i, T1Space (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    G.regularAnalyticImplPrice z = ∑ i, G.regularImplementationGap z i := by
  classical
  let gapSum : ℝ := ∑ i, G.regularImplementationGap z i
  exact sInf_eq_of_mem_of_forall_le
    (Costs := G.regularAnalyticImplementationCosts z)
    (Price := G.regularAnalyticImplPrice z)
    (L := gapSum)
    rfl
    (regularAnalyticImplementationCosts_bddBelow (G := G) z)
    (by
      simpa [gapSum] using
        regularAnalyticImplementationCosts_mem_gap_sum_of_nondegenerate
          (G := G) husc z hnd)
    (fun k hk => by
      obtain ⟨V, han, hV⟩ := hk
      simpa [gapSum] using
        regularSingletonKImplementation_lower_bound_of_analytic
          (G := G) (V := V) (z := z) han hV)

theorem regularAnalyticImplPrice_mem_analyticImplementationCosts_of_nondegenerate
    [G.HasAdditiveSubsidyEU] [∀ i, MetricSpace (G.Strategy i)]
    [∀ i, T1Space (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) (hnd : G.SingletonNondegenerate z) :
    G.regularAnalyticImplPrice z ∈ G.regularAnalyticImplementationCosts z := by
  rw [regularAnalyticImplPrice_singleton_of_nondegenerate
    (G := G) husc z hnd]
  exact regularAnalyticImplementationCosts_mem_gap_sum_of_nondegenerate
    (G := G) husc z hnd

omit [Fintype ι] in
theorem regularImplementationGapAt_eq_zero_of_isNash
    (husc : G.RegularOwnUpperSemicontinuous)
    {z : Profile G} (hN : G.IsNash z) (i : ι) :
    G.regularImplementationGap z i = 0 := by
  classical
  apply le_antisymm
  · rw [regularImplementationGap, regularImplementationGapAt]
    apply csSup_le
    · exact ⟨0, by
        refine ⟨z i, ?_⟩
        simp [Function.update_eq_self]⟩
    · rintro x ⟨s, rfl⟩
      have hdev := hN i s
      simpa [Function.update_eq_self] using sub_nonpos.mpr hdev
  · exact regularImplementationGap_nonneg (G := G) husc z i

theorem regularImplementationGap_sum_nonpos_isNash
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G)
    (hgap : (∑ i, G.regularImplementationGap z i) ≤ 0) :
    G.IsNash z := by
  intro i s
  have hterm_le_sum :
      G.regularImplementationGap z i ≤ ∑ j, G.regularImplementationGap z j :=
    Finset.single_le_sum
      (fun j _ => regularImplementationGap_nonneg (G := G) husc z j)
      (Finset.mem_univ i)
  have hgap_i : G.regularImplementationGap z i ≤ 0 := hterm_le_sum.trans hgap
  have hdev := regularImplementationGapAt_ge (G := G) husc z i z s
  simpa [regularImplementationGap, Function.update_eq_self] using
    sub_nonpos.mp (hdev.trans hgap_i)

theorem regularAdmissibleImplPrice_singleton_eq_zero_iff_isNash
    [G.HasAdditiveSubsidyEU] [Nonempty ι]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) :
    G.regularAdmissibleImplPrice z = 0 ↔ G.IsNash z := by
  rw [regularAdmissibleImplPrice_singleton (G := G) husc z]
  constructor
  · intro hprice
    exact regularImplementationGap_sum_nonpos_isNash (G := G) husc z (by
      simp [hprice])
  · intro hN
    apply Finset.sum_eq_zero
    intro i _
    exact regularImplementationGapAt_eq_zero_of_isNash (G := G) husc hN i

theorem regularAnalyticImplPrice_singleton_eq_zero_iff_isNash
    [G.HasAdditiveSubsidyEU] [Nonempty ι]
    [∀ i, T1Space (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    (z : Profile G) :
    G.regularAnalyticImplPrice z = 0 ↔ G.IsNash z := by
  rw [regularAnalyticImplPrice_singleton (G := G) husc z]
  constructor
  · intro hprice
    exact regularImplementationGap_sum_nonpos_isNash (G := G) husc z (by
      simp [hprice])
  · intro hN
    apply Finset.sum_eq_zero
    intro i _
    exact regularImplementationGapAt_eq_zero_of_isNash (G := G) husc hN i

theorem isNash_of_exists_zero_regularAdmissibleKImplementation
    [G.HasAdditiveSubsidyEU]
    (husc : G.RegularOwnUpperSemicontinuous)
    {z : Profile G} :
    (∃ V : Profile G → Payoff ι,
      G.RegularSelectionAdmissibleAt V z ∧
        G.IsKImplementation V ({z} : Set (Profile G)) 0) →
      G.IsNash z := by
  rintro ⟨V, hadm, hV⟩
  exact regularImplementationGap_sum_nonpos_isNash (G := G) husc z
    (regularSingletonKImplementation_lower_bound_of_admissible
      (G := G) (V := V) (z := z) hadm hV)

theorem exists_zero_regularAdmissibleKImplementation_iff_isNash
    [G.HasAdditiveSubsidyEU] [∀ i, MetricSpace (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    {z : Profile G} (hnd : G.SingletonNondegenerate z) :
    (∃ V : Profile G → Payoff ι,
      G.RegularSelectionAdmissibleAt V z ∧
        G.IsKImplementation V ({z} : Set (Profile G)) 0) ↔
      G.IsNash z := by
  constructor
  · exact isNash_of_exists_zero_regularAdmissibleKImplementation (G := G) husc
  · intro hN
    have hgap :
        (∑ i, G.regularImplementationGap z i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact regularImplementationGapAt_eq_zero_of_isNash (G := G) husc hN i
    refine ⟨G.regularSingletonDistanceTransfer z,
      regularSingletonDistanceTransfer_selectionAdmissible (G := G) husc z, ?_⟩
    simpa [hgap] using
      regularSingletonDistanceTransfer_isKImplementation (G := G) husc z hnd

theorem isNash_of_exists_zero_regularAnalyticKImplementation
    [G.HasAdditiveSubsidyEU]
    (husc : G.RegularOwnUpperSemicontinuous)
    {z : Profile G} :
    (∃ V : Profile G → Payoff ι,
      G.RegularAnalyticAdmissible V ∧
        G.IsKImplementation V ({z} : Set (Profile G)) 0) →
      G.IsNash z := by
  rintro ⟨V, han, hV⟩
  exact regularImplementationGap_sum_nonpos_isNash (G := G) husc z
    (regularSingletonKImplementation_lower_bound_of_analytic
      (G := G) (V := V) (z := z) han hV)

theorem exists_zero_regularAnalyticKImplementation_iff_isNash
    [G.HasAdditiveSubsidyEU] [∀ i, MetricSpace (G.Strategy i)]
    [∀ i, T1Space (G.Strategy i)]
    (husc : G.RegularOwnUpperSemicontinuous)
    {z : Profile G} (hnd : G.SingletonNondegenerate z) :
    (∃ V : Profile G → Payoff ι,
      G.RegularAnalyticAdmissible V ∧
        G.IsKImplementation V ({z} : Set (Profile G)) 0) ↔
      G.IsNash z := by
  constructor
  · exact isNash_of_exists_zero_regularAnalyticKImplementation (G := G) husc
  · intro hN
    have hgap :
        (∑ i, G.regularImplementationGap z i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact regularImplementationGapAt_eq_zero_of_isNash (G := G) husc hN i
    refine ⟨G.regularSingletonDistanceTransfer z,
      regularSingletonDistanceTransfer_analyticAdmissible (G := G) husc z, ?_⟩
    simpa [hgap] using
      regularSingletonDistanceTransfer_isKImplementation (G := G) husc z hnd

end CompactSupremum

end KernelGame

end GameTheory
