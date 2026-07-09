/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Implementation.Basic
import GameTheory.Concepts.Mixed.MixedExtension
import Math.ProbabilityMassFunction.Simplex
import Math.Topology.WeakDominance
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Mixed-extension k-implementation

The safe, constructive direction of Monderer--Tennenholtz Theorem 3: if a mixed
profile is Nash, then the singleton consisting of that mixed profile is
0-implementable in the mixed extension, assuming the interested party can observe
the mixed strategies themselves.

The converse direction for unrestricted transfers is false.  The concrete
counterexample is in `GameTheory.Implementation.Examples` as
`mixedConverse_zeroKImplementation_and_not_nash`: a mixed profile is
0-implementable in the mixed extension while not being Nash.  A valid converse
therefore needs additional admissibility hypotheses on transfers.
-/

namespace GameTheory

open Math.Probability
open Math.ProbabilityMassFunction

namespace KernelGame

variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- Mixed-strategy nondegeneracy needed for the strict witness in the direct
singleton construction: every player has an opponent with some mixed strategy
different from the target mixed strategy. -/
def MixedSingletonNondegenerate (G : KernelGame ι)
    (p : Profile G.mixedExtension) : Prop :=
  ∀ i : ι, ∃ j : ι, j ≠ i ∧ ∃ q : PMF (G.Strategy j), q ≠ p j

private theorem exists_pmf_ne_of_nontrivial {α : Type*} [Nontrivial α] (p : PMF α) :
    ∃ q : PMF α, q ≠ p := by
  classical
  obtain ⟨a⟩ := (inferInstance : Nonempty α)
  obtain ⟨b, hba⟩ := exists_ne a
  by_cases hp : PMF.pure a = p
  · refine ⟨PMF.pure b, ?_⟩
    intro hb
    have hpure : PMF.pure a = PMF.pure b := hp.trans hb.symm
    have happ := congrArg (fun q : PMF α => q a) hpure
    exfalso
    simp [PMF.pure_apply, hba.symm] at happ
  · exact ⟨PMF.pure a, hp⟩

omit [DecidableEq ι] in
/-- The paper's usual finite-player and nontrivial-action hypotheses imply the
mixed-strategy nondegeneracy needed by the observable mixed-extension
construction. -/
theorem mixedSingletonNondegenerate_of_one_lt_card
    (G : KernelGame ι) [∀ i, Nontrivial (G.Strategy i)]
    (p : Profile G.mixedExtension) (hι : 1 < Fintype.card ι) :
    G.MixedSingletonNondegenerate p := by
  intro i
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card hι i
  obtain ⟨q, hq⟩ := exists_pmf_ne_of_nontrivial (p j)
  exact ⟨j, hji, q, hq⟩

section ObservableMixed

variable {G : KernelGame ι}
variable [strategyFintype : ∀ i, Fintype (G.Strategy i)]
variable [strategyNonempty : ∀ i, Nonempty (G.Strategy i)]

/-- Pure-deviation gain bound in the mixed extension. The `max 0` keeps the
transfer nonnegative even away from equilibrium profiles. -/
noncomputable def mixedImplementationGapAt
    (p : Profile G.mixedExtension) (i : ι) (σ : Profile G.mixedExtension) : ℝ :=
  letI : Fintype (G.Strategy i) := strategyFintype i
  letI : Nonempty (G.Strategy i) := strategyNonempty i
  max 0 <|
    Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy i))
      (fun a : G.Strategy i =>
        G.mixedExtension.eu (Function.update σ i (PMF.pure a)) i -
          G.mixedExtension.eu (Function.update σ i (p i)) i)

theorem mixedImplementationGapAt_nonneg
    (p : Profile G.mixedExtension) (i : ι) (σ : Profile G.mixedExtension) :
    0 ≤ G.mixedImplementationGapAt p i σ := by
  classical
  simp [mixedImplementationGapAt]

theorem mixedImplementationGapAt_ge_pure
    (p : Profile G.mixedExtension) (i : ι) (σ : Profile G.mixedExtension)
    (a : G.Strategy i) :
    G.mixedExtension.eu (Function.update σ i (PMF.pure a)) i -
        G.mixedExtension.eu (Function.update σ i (p i)) i ≤
      G.mixedImplementationGapAt p i σ := by
  classical
  let raw : ℝ :=
    Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy i))
      (fun a : G.Strategy i =>
        G.mixedExtension.eu (Function.update σ i (PMF.pure a)) i -
          G.mixedExtension.eu (Function.update σ i (p i)) i)
  have hle_raw :
      G.mixedExtension.eu (Function.update σ i (PMF.pure a)) i -
          G.mixedExtension.eu (Function.update σ i (p i)) i ≤ raw := by
    simpa [raw] using
      (Finset.le_sup' (s := Finset.univ)
        (f := fun a : G.Strategy i =>
          G.mixedExtension.eu (Function.update σ i (PMF.pure a)) i -
            G.mixedExtension.eu (Function.update σ i (p i)) i)
        (Finset.mem_univ a))
  exact hle_raw.trans (by simp [mixedImplementationGapAt, raw])

/-- The gap also bounds arbitrary mixed deviations, by linearity in the deviating
player's mixed strategy. -/
theorem mixedImplementationGapAt_ge_mixed [Finite G.Outcome]
    (p : Profile G.mixedExtension) (i : ι) (σ : Profile G.mixedExtension)
    (τ : PMF (G.Strategy i)) :
    G.mixedExtension.eu (Function.update σ i τ) i -
        G.mixedExtension.eu (Function.update σ i (p i)) i ≤
      G.mixedImplementationGapAt p i σ := by
  classical
  let target : ℝ := G.mixedExtension.eu (Function.update σ i (p i)) i
  let gap : ℝ := G.mixedImplementationGapAt p i σ
  have hpure_le : ∀ a : G.Strategy i,
      G.mixedExtension.eu (Function.update σ i (PMF.pure a)) i ≤ target + gap := by
    intro a
    have h := mixedImplementationGapAt_ge_pure (G := G) p i σ a
    linarith
  have hle :
      expect τ (fun a : G.Strategy i =>
          G.mixedExtension.eu (Function.update σ i (PMF.pure a)) i) ≤
        expect τ (fun _ : G.Strategy i => target + gap) := by
    exact expect_mono τ _ _ hpure_le
  rw [expect_const] at hle
  rw [G.mixedExtension_eu_update σ i τ]
  linarith

omit [DecidableEq ι] strategyFintype strategyNonempty in
/-- `subsidize_eu` specialized to the mixed extension. This avoids fragile
rewriting through the nested `mixedExtension` strategy-field abbreviation. -/
@[simp] theorem mixedExtension_subsidize_eu [Finite G.Outcome]
    (V : Profile G.mixedExtension → Payoff ι)
    (σ : Profile G.mixedExtension) (i : ι) :
    (G.mixedExtension.subsidize V).eu σ i = G.mixedExtension.eu σ i + V σ i := by
  haveI : Finite G.mixedExtension.Outcome := by
    change Finite G.Outcome
    infer_instance
  exact subsidize_eu (G := G.mixedExtension) V σ i

/-- Semantic admissibility condition for the corrected mixed-extension
converse: for each player, the perturbed mixed game has an undominated best
response against the target opponents.  Topological admissibility hypotheses
such as own upper-semicontinuity are intended to imply this selection property;
the price theorem below only needs this abstract consequence. -/
def MixedSelectionAdmissibleAt [Finite G.Outcome]
    (V : Profile G.mixedExtension → Payoff ι) (p : Profile G.mixedExtension) : Prop :=
  ∀ i : ι, ∃ τ : PMF (G.Strategy i),
    (∀ q : PMF (G.Strategy i),
      (G.mixedExtension.subsidize V).eu (Function.update p i τ) i ≥
        (G.mixedExtension.subsidize V).eu (Function.update p i q) i) ∧
      (G.mixedExtension.subsidize V).IsUndominated i τ

omit strategyFintype strategyNonempty in
theorem MixedSelectionAdmissibleAt.of_dominant [Finite G.Outcome]
    {V : Profile G.mixedExtension → Payoff ι} {p : Profile G.mixedExtension}
    (hdom : ∀ i, (G.mixedExtension.subsidize V).IsDominant i (p i)) :
    G.MixedSelectionAdmissibleAt V p := by
  intro i
  refine ⟨p i, ?_, (hdom i).isUndominated⟩
  intro q
  simpa [Function.update_eq_self] using hdom i p q

omit strategyFintype strategyNonempty in
theorem mixedSingleton_target_undominated_of_isImplementation
    {V : Profile G.mixedExtension → Payoff ι} {p : Profile G.mixedExtension}
    (h : G.mixedExtension.IsImplementation V ({p} : Set (Profile G.mixedExtension))) :
    p ∈ (G.mixedExtension.subsidize V).undominatedProfiles := by
  obtain ⟨σ, hσ⟩ := h.nonempty
  have hσp : σ = p := by
    exact Set.mem_singleton_iff.mp (h.subset σ hσ)
  subst σ
  exact hσ

theorem mixedImplementationGapAt_le_transfer_of_admissibleImplementation
    [Finite G.Outcome]
    {V : Profile G.mixedExtension → Payoff ι} {p : Profile G.mixedExtension}
    (hV : G.mixedExtension.IsImplementation V ({p} : Set (Profile G.mixedExtension)))
    (hadm : G.MixedSelectionAdmissibleAt V p) (i : ι) :
    G.mixedImplementationGapAt p i p ≤ V p i := by
  classical
  obtain ⟨τ, hbest, hτundom⟩ := hadm i
  have hpundom := mixedSingleton_target_undominated_of_isImplementation (G := G) hV
  have hprof : Function.update p i τ ∈
      (G.mixedExtension.subsidize V).undominatedProfiles := by
    intro j
    by_cases hji : j = i
    · subst hji
      simpa using hτundom
    · simpa [Function.update_of_ne hji] using hpundom j
  have hτeq : τ = p i := by
    have hmem := hV.subset (Function.update p i τ) hprof
    have heq : Function.update p i τ = p := Set.mem_singleton_iff.mp hmem
    simpa using congrFun heq i
  have hgain_le : ∀ a : G.Strategy i,
      G.mixedExtension.eu (Function.update p i (PMF.pure a)) i -
          G.mixedExtension.eu p i ≤ V p i := by
    intro a
    have hbest_a := hbest (PMF.pure a)
    rw [hτeq] at hbest_a
    rw [mixedExtension_subsidize_eu, mixedExtension_subsidize_eu] at hbest_a
    simp only [Function.update_eq_self, ge_iff_le] at hbest_a
    have hbest_le :
        G.mixedExtension.eu (Function.update p i (PMF.pure a)) i +
            V (Function.update p i (PMF.pure a)) i ≤
          G.mixedExtension.eu p i + V p i := by
      exact hbest_a
    have hVdev : 0 ≤ V (Function.update p i (PMF.pure a)) i := hV.nonneg _ _
    have hsub1 :
        G.mixedExtension.eu (Function.update p i (PMF.pure a)) i -
            G.mixedExtension.eu p i
          ≤ (G.mixedExtension.eu (Function.update p i (PMF.pure a)) i +
              V (Function.update p i (PMF.pure a)) i) -
              G.mixedExtension.eu p i :=
      sub_le_sub_right (le_add_of_nonneg_right hVdev) _
    have hsub2 :
        (G.mixedExtension.eu (Function.update p i (PMF.pure a)) i +
            V (Function.update p i (PMF.pure a)) i) -
            G.mixedExtension.eu p i ≤ V p i := by
      rw [sub_le_iff_le_add]
      simpa [add_comm, add_left_comm, add_assoc] using hbest_le
    exact hsub1.trans hsub2
  rw [mixedImplementationGapAt]
  apply max_le
  · exact hV.nonneg p i
  · apply Finset.sup'_le
    intro a _
    simpa [Function.update_eq_self] using hgain_le a

theorem mixedSingletonKImplementation_lower_bound_of_admissible
    [Finite G.Outcome]
    {V : Profile G.mixedExtension → Payoff ι} {p : Profile G.mixedExtension}
    {k : ℝ}
    (hadm : G.MixedSelectionAdmissibleAt V p)
    (hV : G.mixedExtension.IsKImplementation V ({p} : Set (Profile G.mixedExtension)) k) :
    (∑ i, G.mixedImplementationGapAt p i p) ≤ k := by
  have hpundom := mixedSingleton_target_undominated_of_isImplementation (G := G)
    hV.implementation
  calc
    (∑ i, G.mixedImplementationGapAt p i p) ≤ ∑ i, V p i := by
      exact Finset.sum_le_sum fun i _ =>
        mixedImplementationGapAt_le_transfer_of_admissibleImplementation
          (G := G) (V := V) (p := p) hV.implementation hadm i
    _ ≤ k := hV.cost_bound p hpundom

/-- Update a mixed target profile by reading one player's mixed strategy from a
finite simplex point.  This is the local topology bridge used for analytic
admissibility of mixed-extension transfers. -/
noncomputable def mixedProfileUpdateFromSimplex
    (p : Profile G.mixedExtension) (i : ι) (x : stdSimplex ℝ (G.Strategy i)) :
    Profile G.mixedExtension :=
  Function.update p i (ofVector x x.property)

omit strategyNonempty in
@[simp] theorem mixedProfileUpdateFromSimplex_toVector
    (σ : Profile G.mixedExtension) (i : ι) (q : PMF (G.Strategy i)) :
    G.mixedProfileUpdateFromSimplex σ i
        ⟨toVector q, toVector_mem_stdSimplex q⟩ =
      Function.update σ i q := by
  change Function.update σ i (ofVector (toVector q) (toVector_mem_stdSimplex q)) =
    Function.update σ i q
  rw [Math.ProbabilityMassFunction.ofVector_toVector q]

omit strategyNonempty in
/-- In finite games, mixed-extension payoff is continuous as a function of one
player's finite-simplex coordinates, with opponents held fixed. -/
theorem continuous_mixedExtension_eu_updateFromSimplex [Finite G.Outcome]
    (σ : Profile G.mixedExtension) (i : ι) :
    Continuous fun x : stdSimplex ℝ (G.Strategy i) =>
      G.mixedExtension.eu (G.mixedProfileUpdateFromSimplex σ i x) i := by
  classical
  have heq :
      (fun x : stdSimplex ℝ (G.Strategy i) =>
        G.mixedExtension.eu (G.mixedProfileUpdateFromSimplex σ i x) i)
      =
        (fun x : stdSimplex ℝ (G.Strategy i) =>
          ∑ a : G.Strategy i,
            (x : G.Strategy i → ℝ) a *
              G.mixedExtension.eu (Function.update σ i (PMF.pure a)) i) := by
    funext x
    rw [mixedProfileUpdateFromSimplex]
    rw [G.mixedExtension_eu_update σ i
      (ofVector (x : G.Strategy i → ℝ) x.property)]
    rw [expect_eq_sum]
    apply Finset.sum_congr rfl
    intro a _
    simp
  rw [heq]
  refine continuous_finsetSum (s := (Finset.univ : Finset (G.Strategy i))) ?_
  intro a _
  exact ((continuous_apply a).comp continuous_subtype_val).mul continuous_const

/-- Own upper-semicontinuity of a mixed-extension transfer at the target
opponent profile.  The topology is the finite standard-simplex topology on the
deviating player's mixed strategy. -/
def MixedOwnUpperSemicontinuousAt [Finite G.Outcome]
    (V : Profile G.mixedExtension → Payoff ι) (p : Profile G.mixedExtension) : Prop :=
  ∀ i : ι,
    UpperSemicontinuousOn
      (fun x : stdSimplex ℝ (G.Strategy i) =>
        (G.mixedExtension.subsidize V).eu (G.mixedProfileUpdateFromSimplex p i x) i)
      Set.univ

/-- Own upper-semicontinuity of a mixed-extension transfer at every opponent
profile.  Compactness then supplies undominated dominators, so no separate
target-detection hypothesis is needed. -/
def MixedOwnUpperSemicontinuous [Finite G.Outcome]
    (V : Profile G.mixedExtension → Payoff ι) : Prop :=
  ∀ i : ι, ∀ σ : Profile G.mixedExtension,
    UpperSemicontinuousOn
      (fun x : stdSimplex ℝ (G.Strategy i) =>
        (G.mixedExtension.subsidize V).eu (G.mixedProfileUpdateFromSimplex σ i x) i)
      Set.univ

omit strategyNonempty in
theorem MixedOwnUpperSemicontinuous.target [Finite G.Outcome]
    {V : Profile G.mixedExtension → Payoff ι} {p : Profile G.mixedExtension}
    (h : G.MixedOwnUpperSemicontinuous V) :
    G.MixedOwnUpperSemicontinuousAt V p := fun i => h i p

/-- Analytic sufficient condition for the corrected mixed-extension converse:
own upper-semicontinuity at every opponent profile.  Unlike the semantic
selection condition, this is not target-indexed. -/
def MixedAnalyticAdmissible [Finite G.Outcome]
    (V : Profile G.mixedExtension → Payoff ι) : Prop :=
  G.MixedOwnUpperSemicontinuous V

theorem exists_mixedTarget_bestResponse_of_own_upperSemicontinuous
    [Finite G.Outcome]
    {V : Profile G.mixedExtension → Payoff ι} {p : Profile G.mixedExtension}
    (husc : G.MixedOwnUpperSemicontinuousAt V p) (i : ι) :
    ∃ τ : PMF (G.Strategy i),
      ∀ q : PMF (G.Strategy i),
        (G.mixedExtension.subsidize V).eu (Function.update p i τ) i ≥
          (G.mixedExtension.subsidize V).eu (Function.update p i q) i := by
  classical
  let f : stdSimplex ℝ (G.Strategy i) → ℝ := fun x =>
    (G.mixedExtension.subsidize V).eu (G.mixedProfileUpdateFromSimplex p i x) i
  obtain ⟨x, -, hxmax⟩ :=
    (husc i).exists_isMaxOn (s := Set.univ)
      (Set.univ_nonempty : (Set.univ : Set (stdSimplex ℝ (G.Strategy i))).Nonempty)
      (isCompact_univ)
  refine ⟨ofVector x x.property, ?_⟩
  intro q
  let y : stdSimplex ℝ (G.Strategy i) :=
    ⟨toVector q, toVector_mem_stdSimplex q⟩
  have hy_pmf : ofVector (y : G.Strategy i → ℝ) y.property = q := by
    change ofVector (toVector q) (toVector_mem_stdSimplex q) = q
    exact Math.ProbabilityMassFunction.ofVector_toVector q
  have hmax_y : f y ≤ f x := hxmax (Set.mem_univ y)
  have hfy :
      f y =
        (G.mixedExtension.subsidize V).eu (Function.update p i q) i := by
    simp [f, mixedProfileUpdateFromSimplex, hy_pmf]
  rw [hfy] at hmax_y
  simpa [f, mixedProfileUpdateFromSimplex] using hmax_y

theorem MixedOwnUpperSemicontinuous.selectionAdmissible
    [Finite G.Outcome]
    {V : Profile G.mixedExtension → Payoff ι} {p : Profile G.mixedExtension}
    (husc : G.MixedOwnUpperSemicontinuous V) :
    G.MixedSelectionAdmissibleAt V p := by
  classical
  intro i
  obtain ⟨τ, hbest⟩ :=
    exists_mixedTarget_bestResponse_of_own_upperSemicontinuous
      (G := G) (V := V) (p := p) husc.target i
  let yτ : stdSimplex ℝ (G.Strategy i) :=
    ⟨toVector τ, toVector_mem_stdSimplex τ⟩
  let W : stdSimplex ℝ (G.Strategy i) → Profile G.mixedExtension → ℝ :=
    fun x σ => (G.mixedExtension.subsidize V).eu
      (G.mixedProfileUpdateFromSimplex σ i x) i
  have hWusc : ∀ σ : Profile G.mixedExtension,
      UpperSemicontinuousOn (fun x : stdSimplex ℝ (G.Strategy i) => W x σ) Set.univ := by
    intro σ
    exact husc i σ
  obtain ⟨x, hxdom, hxundom⟩ :=
    Math.Topology.exists_pointwiseUndominated_dominator_of_compact_usc
      W hWusc yτ
  let τ' : PMF (G.Strategy i) := ofVector (x : G.Strategy i → ℝ) x.property
  refine ⟨τ', ?_, ?_⟩
  · intro q
    have hττ'_raw :
        (G.mixedExtension.subsidize V).eu (Function.update p i τ) i ≤
          (G.mixedExtension.subsidize V).eu (G.mixedProfileUpdateFromSimplex p i x) i := by
      simpa [W, yτ] using hxdom p
    have hττ' :
        (G.mixedExtension.subsidize V).eu (Function.update p i τ) i ≤
          (G.mixedExtension.subsidize V).eu (Function.update p i τ') i := by
      simpa [τ', mixedProfileUpdateFromSimplex] using hττ'_raw
    exact (hbest q).trans hττ'
  · intro q hq
    let yq : stdSimplex ℝ (G.Strategy i) :=
      ⟨toVector q, toVector_mem_stdSimplex q⟩
    have hyq : ofVector (yq : G.Strategy i → ℝ) yq.property = q := by
      change ofVector (toVector q) (toVector_mem_stdSimplex q) = q
      exact Math.ProbabilityMassFunction.ofVector_toVector q
    have hpoint :
        Math.Topology.PointwiseWeaklyStrictlyDominates W yq x := by
      refine ⟨?_, ?_⟩
      · intro σ
        have hweak := hq.toWeaklyDominates σ
        simpa [W, yq, τ', hyq, mixedProfileUpdateFromSimplex] using hweak
      · obtain ⟨σ, hstrict⟩ := hq.strict_witness
        refine ⟨σ, ?_⟩
        simpa [W, yq, τ', hyq, mixedProfileUpdateFromSimplex, gt_iff_lt] using hstrict
    exact hxundom yq hpoint

theorem MixedAnalyticAdmissible.selectionAdmissible
    [Finite G.Outcome]
    {V : Profile G.mixedExtension → Payoff ι} {p : Profile G.mixedExtension}
    (h : G.MixedAnalyticAdmissible V) :
    G.MixedSelectionAdmissibleAt V p :=
  MixedOwnUpperSemicontinuous.selectionAdmissible (G := G) h

/-- Finite-coordinate L1 distance between two PMFs.  This is used only as a
strict off-target bump for mixed strategies, not as a global topology. -/
noncomputable def pmfL1Dist {α : Type*} [Fintype α] (p q : PMF α) : ℝ :=
  ∑ a : α, |(p a).toReal - (q a).toReal|

theorem pmfL1Dist_nonneg {α : Type*} [Fintype α] (p q : PMF α) :
    0 ≤ pmfL1Dist p q :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem pmfL1Dist_pos_of_ne {α : Type*} [Fintype α] {p q : PMF α}
    (hpq : p ≠ q) : 0 < pmfL1Dist p q := by
  classical
  have hdiff : ∃ a : α, (p a).toReal ≠ (q a).toReal := by
    by_contra hnone
    push Not at hnone
    exact hpq (eq_of_forall_toReal_eq p q hnone)
  obtain ⟨a, ha⟩ := hdiff
  have hterm : 0 < |(p a).toReal - (q a).toReal| := abs_pos.mpr (sub_ne_zero.mpr ha)
  exact hterm.trans_le
    (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun a : α => |(p a).toReal - (q a).toReal|)
      (fun _ _ => abs_nonneg _)
      (Finset.mem_univ a))

theorem pmfL1Dist_le_two {α : Type*} [Fintype α] (p q : PMF α) :
    pmfL1Dist p q ≤ 2 := by
  classical
  calc
    pmfL1Dist p q ≤
        ∑ a : α, ((p a).toReal + (q a).toReal) := by
      unfold pmfL1Dist
      exact Finset.sum_le_sum fun a _ => by
        have hq : 0 ≤ (q a).toReal := ENNReal.toReal_nonneg
        have hp : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
        exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
    _ = 2 := by
      rw [Finset.sum_add_distrib, Math.Probability.pmf_toReal_sum_one,
        Math.Probability.pmf_toReal_sum_one]
      norm_num

theorem continuous_pmfL1Dist_ofVector {α : Type*} [Fintype α] (p : PMF α) :
    Continuous fun x : stdSimplex ℝ α =>
      pmfL1Dist (ofVector (x : α → ℝ) x.property) p := by
  classical
  unfold pmfL1Dist
  refine continuous_finsetSum (s := (Finset.univ : Finset α)) ?_
  intro a _
  have hcoord :
      Continuous fun x : stdSimplex ℝ α =>
        ((ofVector (x : α → ℝ) x.property) a).toReal := by
    have hcoord' : Continuous fun x : stdSimplex ℝ α => (x : α → ℝ) a :=
      (continuous_apply a).comp continuous_subtype_val
    simpa using hcoord'
  exact (hcoord.sub continuous_const).abs

@[simp] theorem pmfL1Dist_self {α : Type*} [Fintype α] (p : PMF α) :
    pmfL1Dist p p = 0 := by
  simp [pmfL1Dist]

/-- L1 distance from the target on all opponents of player `i`. -/
noncomputable def mixedOpponentL1Dist
    (p σ : Profile G.mixedExtension) (i : ι) : ℝ :=
  (Finset.univ.erase i).sum fun j => pmfL1Dist (σ j) (p j)

omit strategyNonempty in
theorem mixedOpponentL1Dist_nonneg
    (p σ : Profile G.mixedExtension) (i : ι) :
    0 ≤ mixedOpponentL1Dist (G := G) p σ i := by
  exact Finset.sum_nonneg fun j _ => pmfL1Dist_nonneg (σ j) (p j)

omit strategyNonempty in
theorem mixedOpponentL1Dist_update_pos
    (p : Profile G.mixedExtension) {i j : ι} (hji : j ≠ i)
    {q : G.mixedExtension.Strategy j} (hq : q ≠ p j) :
    0 < mixedOpponentL1Dist (G := G) p (Function.update p j q) i := by
  classical
  have hjmem : j ∈ Finset.univ.erase i := by
    exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
  have hterm :
      0 < pmfL1Dist ((Function.update p j q) j) (p j) := by
    simpa using pmfL1Dist_pos_of_ne (p := q) (q := p j) hq
  exact hterm.trans_le
    (Finset.single_le_sum
      (s := Finset.univ.erase i)
      (f := fun l => pmfL1Dist ((Function.update p j q) l) (p l))
      (fun l _ => pmfL1Dist_nonneg ((Function.update p j q) l) (p l))
      hjmem)

/-- Positive-slack admissible transfer for mixed singleton implementation.
Player `i` is paid only when choosing `p i`, and then receives the mixed
deviation gap plus a player-specific slack `ε i`. -/
noncomputable def mixedSingletonApproxTransfer
    (p : Profile G.mixedExtension) (ε : ι → ℝ) :
    Profile G.mixedExtension → Payoff ι :=
  open Classical in
  fun σ i => if σ i = p i then G.mixedImplementationGapAt p i σ + ε i else 0

@[simp] theorem mixedSingletonApproxTransfer_target
    (p : Profile G.mixedExtension) (ε : ι → ℝ) (i : ι) :
    G.mixedSingletonApproxTransfer p ε p i =
      G.mixedImplementationGapAt p i p + ε i := by
  classical
  simp [mixedSingletonApproxTransfer]

@[simp] theorem mixedSingletonApproxTransfer_update_target
    (p : Profile G.mixedExtension) (ε : ι → ℝ)
    (i : ι) (σ : Profile G.mixedExtension) :
    G.mixedSingletonApproxTransfer p ε (Function.update σ i (p i)) i =
      G.mixedImplementationGapAt p i (Function.update σ i (p i)) + ε i := by
  classical
  simp [mixedSingletonApproxTransfer]

theorem mixedSingletonApproxTransfer_update_ne
    (p : Profile G.mixedExtension) (ε : ι → ℝ)
    (i : ι) (σ : Profile G.mixedExtension)
    {τ : PMF (G.Strategy i)} (hτ : τ ≠ p i) :
    G.mixedSingletonApproxTransfer p ε (Function.update σ i τ) i = 0 := by
  classical
  rw [mixedSingletonApproxTransfer, if_neg]
  simpa using hτ

theorem mixedSingletonApproxTransfer_nonneg
    (p : Profile G.mixedExtension) {ε : ι → ℝ} (hε : ∀ i, 0 ≤ ε i) :
    ∀ σ i, 0 ≤ G.mixedSingletonApproxTransfer p ε σ i := by
  classical
  intro σ i
  by_cases hi : σ i = p i
  · have hgap := mixedImplementationGapAt_nonneg (G := G) p i σ
    rw [mixedSingletonApproxTransfer, if_pos hi]
    exact add_nonneg hgap (hε i)
  · rw [mixedSingletonApproxTransfer, if_neg hi]

theorem mixedSingletonApproxTransfer_target_isDominant [Finite G.Outcome]
    (p : Profile G.mixedExtension) {ε : ι → ℝ} (hε : ∀ i, 0 ≤ ε i) (i : ι) :
    (G.mixedExtension.subsidize (G.mixedSingletonApproxTransfer p ε)).IsDominant
      i (p i) := by
  classical
  intro σ τ
  let σ' : Profile G.mixedExtension := σ
  by_cases hτ : τ = p i
  · subst τ
    simp
  · have hgap := mixedImplementationGapAt_ge_mixed (G := G) p i
      (Function.update σ' i (p i)) τ
    have hgap' :
        G.mixedExtension.eu (Function.update σ' i τ) i -
            G.mixedExtension.eu (Function.update σ' i (p i)) i ≤
          G.mixedImplementationGapAt p i (Function.update σ' i (p i)) := by
      simpa [Function.update_idem] using hgap
    rw [mixedExtension_subsidize_eu, mixedExtension_subsidize_eu]
    simp only [subsidize_Strategy, mixedSingletonApproxTransfer_update_target, ge_iff_le]
    rw [mixedSingletonApproxTransfer_update_ne (G := G) p ε i σ' hτ]
    simp only [add_zero]
    linarith [hε i]

theorem mixedSingletonApproxTransfer_weaklyStrictlyDominates_ne [Finite G.Outcome]
    (p : Profile G.mixedExtension) {ε : ι → ℝ} (hε : ∀ i, 0 < ε i)
    {i : ι} {τ : PMF (G.Strategy i)} (hτ : τ ≠ p i) :
    (G.mixedExtension.subsidize (G.mixedSingletonApproxTransfer p ε)).WeaklyStrictlyDominates
      i (p i) τ := by
  classical
  refine ⟨(mixedSingletonApproxTransfer_target_isDominant (G := G) p
    (fun i => le_of_lt (hε i)) i).weaklyDominates τ, ?_⟩
  refine ⟨p, ?_⟩
  have hgap := mixedImplementationGapAt_ge_mixed (G := G) p i p τ
  have hgap' :
      G.mixedExtension.eu (Function.update p i τ) i -
          G.mixedExtension.eu p i ≤ G.mixedImplementationGapAt p i p := by
    simpa [Function.update_eq_self] using hgap
  rw [mixedExtension_subsidize_eu, mixedExtension_subsidize_eu]
  change G.mixedExtension.eu (Function.update p i (p i)) i +
      G.mixedSingletonApproxTransfer p ε (Function.update p i (p i)) i >
    G.mixedExtension.eu (Function.update p i τ) i +
      G.mixedSingletonApproxTransfer p ε (Function.update p i τ) i
  rw [mixedSingletonApproxTransfer_update_target]
  rw [mixedSingletonApproxTransfer_update_ne (G := G) p ε i p hτ]
  simp only [add_zero]
  simp only [mixedExtension_Strategy, Function.update_eq_self, gt_iff_lt]
  have hle :
      G.mixedExtension.eu (Function.update p i τ) i ≤
        G.mixedExtension.eu p i + G.mixedImplementationGapAt p i p := by
    linarith [hgap']
  have hlt :
      G.mixedExtension.eu p i + G.mixedImplementationGapAt p i p <
        G.mixedExtension.eu p i +
          (G.mixedImplementationGapAt p i p + ε i) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      (add_lt_add_left
      (lt_add_of_pos_right (G.mixedImplementationGapAt p i p) (hε i))
      (G.mixedExtension.eu p i))
  exact lt_of_le_of_lt hle hlt

theorem mixedSingletonApproxTransfer_isImplementation [Finite G.Outcome]
    (p : Profile G.mixedExtension) {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) :
    G.mixedExtension.IsImplementation (G.mixedSingletonApproxTransfer p ε)
      ({p} : Set (Profile G.mixedExtension)) := by
  refine ⟨mixedSingletonApproxTransfer_nonneg (G := G) p
    (fun i => le_of_lt (hε i)), ?_, ?_⟩
  · exact ⟨p, fun i =>
      (mixedSingletonApproxTransfer_target_isDominant (G := G) p
        (fun i => le_of_lt (hε i)) i).isUndominated⟩
  · intro σ hσ
    apply Set.mem_singleton_iff.mpr
    funext i
    by_contra hne
    exact (hσ i (p i)
      (mixedSingletonApproxTransfer_weaklyStrictlyDominates_ne (G := G) p hε hne)).elim

theorem mixedSingletonApproxTransfer_isKImplementation [Finite G.Outcome]
    (p : Profile G.mixedExtension) {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) :
    G.mixedExtension.IsKImplementation (G.mixedSingletonApproxTransfer p ε)
      ({p} : Set (Profile G.mixedExtension))
      (∑ i, (G.mixedImplementationGapAt p i p + ε i)) := by
  refine ⟨mixedSingletonApproxTransfer_isImplementation (G := G) p hε, ?_⟩
  intro σ hσ
  have hσp : σ = p := Set.mem_singleton_iff.mp
    ((mixedSingletonApproxTransfer_isImplementation (G := G) p hε).subset σ hσ)
  subst hσp
  simp [mixedSingletonApproxTransfer]

/-- Continuous positive-slack transfer for analytic mixed singleton
implementation.  Player `i`'s target payoff is raised to the pure-deviation
gap plus slack, while non-target mixed strategies lose a small continuous L1
penalty. -/
noncomputable def mixedSingletonContinuousApproxTransfer
    (p : Profile G.mixedExtension) (ε : ι → ℝ) :
    Profile G.mixedExtension → Payoff ι :=
  fun σ i =>
    let σ₀ : Profile G.mixedExtension := Function.update σ i (p i)
    G.mixedExtension.eu σ₀ i + G.mixedImplementationGapAt p i σ₀ + ε i -
      G.mixedExtension.eu σ i - (ε i / 4) * pmfL1Dist (σ i) (p i)

theorem mixedSingletonContinuousApproxTransfer_subsidized_eu [Finite G.Outcome]
    (p : Profile G.mixedExtension) (ε : ι → ℝ)
    (σ : Profile G.mixedExtension) (i : ι) :
    (G.mixedExtension.subsidize
        (G.mixedSingletonContinuousApproxTransfer p ε)).eu σ i =
      G.mixedExtension.eu (Function.update σ i (p i)) i +
        G.mixedImplementationGapAt p i (Function.update σ i (p i)) + ε i -
          (ε i / 4) * pmfL1Dist (σ i) (p i) := by
  rw [mixedExtension_subsidize_eu]
  simp [mixedSingletonContinuousApproxTransfer, add_comm, add_left_comm,
    sub_eq_add_neg]

theorem mixedSingletonContinuousApproxTransfer_nonneg [Finite G.Outcome]
    (p : Profile G.mixedExtension) {ε : ι → ℝ} (hε : ∀ i, 0 ≤ ε i) :
    ∀ σ i, 0 ≤ G.mixedSingletonContinuousApproxTransfer p ε σ i := by
  classical
  intro σ i
  let σ₀ : Profile G.mixedExtension := Function.update σ i (p i)
  have hgap := mixedImplementationGapAt_ge_mixed (G := G) p i σ₀ (σ i)
  have hσ : Function.update σ₀ i (σ i) = σ := by
    simp [σ₀, Function.update_eq_self]
  have htarget : Function.update σ₀ i (p i) = σ₀ := by
    simp [σ₀]
  rw [hσ, htarget] at hgap
  have hbase :
      0 ≤ G.mixedExtension.eu σ₀ i +
          G.mixedImplementationGapAt p i σ₀ - G.mixedExtension.eu σ i := by
    linarith
  have hdist_nonneg : 0 ≤ pmfL1Dist (σ i) (p i) :=
    pmfL1Dist_nonneg (σ i) (p i)
  have hdist_le : pmfL1Dist (σ i) (p i) ≤ 2 :=
    pmfL1Dist_le_two (σ i) (p i)
  have hpenalty :
      (ε i / 4) * pmfL1Dist (σ i) (p i) ≤ ε i := by
    nlinarith [hε i, hdist_nonneg, hdist_le]
  have hbase' :
      0 ≤ G.mixedExtension.eu (Function.update σ i (p i)) i +
          G.mixedImplementationGapAt p i (Function.update σ i (p i)) -
            G.mixedExtension.eu σ i := by
    simpa [σ₀] using hbase
  change 0 ≤ G.mixedExtension.eu (Function.update σ i (p i)) i +
      G.mixedImplementationGapAt p i (Function.update σ i (p i)) + ε i -
        G.mixedExtension.eu σ i -
          (ε i / 4) * pmfL1Dist (σ i) (p i)
  linarith

theorem mixedSingletonContinuousApproxTransfer_target_strictlyDominates_ne
    [Finite G.Outcome]
    (p : Profile G.mixedExtension) {ε : ι → ℝ} (hε : ∀ i, 0 < ε i)
    {i : ι} {τ : PMF (G.Strategy i)} (hτ : τ ≠ p i) :
    (G.mixedExtension.subsidize
        (G.mixedSingletonContinuousApproxTransfer p ε)).StrictlyDominates
      i (p i) τ := by
  classical
  intro σ
  rw [mixedSingletonContinuousApproxTransfer_subsidized_eu,
    mixedSingletonContinuousApproxTransfer_subsidized_eu]
  have hdist_pos : 0 < pmfL1Dist τ (p i) :=
    pmfL1Dist_pos_of_ne hτ
  have hcoef_pos : 0 < ε i / 4 := by nlinarith [hε i]
  simp [Function.update_idem]
  nlinarith [mul_pos hcoef_pos hdist_pos]

theorem mixedSingletonContinuousApproxTransfer_target_isDominant [Finite G.Outcome]
    (p : Profile G.mixedExtension) {ε : ι → ℝ} (hε : ∀ i, 0 ≤ ε i) (i : ι) :
    (G.mixedExtension.subsidize
        (G.mixedSingletonContinuousApproxTransfer p ε)).IsDominant i (p i) := by
  classical
  intro σ τ
  by_cases hτ : τ = p i
  · subst τ
    simp
  · have hεpos_or_zero : 0 ≤ ε i := hε i
    rw [mixedSingletonContinuousApproxTransfer_subsidized_eu,
      mixedSingletonContinuousApproxTransfer_subsidized_eu]
    have hdist_nonneg : 0 ≤ pmfL1Dist τ (p i) :=
      pmfL1Dist_nonneg τ (p i)
    have hcoef_nonneg : 0 ≤ ε i / 4 := by nlinarith [hεpos_or_zero]
    have hpenalty_nonneg : 0 ≤ (ε i / 4) * pmfL1Dist τ (p i) :=
      mul_nonneg hcoef_nonneg hdist_nonneg
    simp [Function.update_idem]
    nlinarith

theorem mixedSingletonContinuousApproxTransfer_isImplementation [Finite G.Outcome]
    (p : Profile G.mixedExtension) {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) :
    G.mixedExtension.IsImplementation (G.mixedSingletonContinuousApproxTransfer p ε)
      ({p} : Set (Profile G.mixedExtension)) := by
  classical
  refine ⟨mixedSingletonContinuousApproxTransfer_nonneg (G := G) p
    (fun i => le_of_lt (hε i)), ?_, ?_⟩
  · exact ⟨p, fun i =>
      (mixedSingletonContinuousApproxTransfer_target_isDominant
        (G := G) p (fun i => le_of_lt (hε i)) i).isUndominated⟩
  · intro σ hσ
    apply Set.mem_singleton_iff.mpr
    funext i
    by_contra hne
    have hdom :=
      (mixedSingletonContinuousApproxTransfer_target_strictlyDominates_ne
        (G := G) p hε hne).toWeaklyStrictlyDominates
        (G := G.mixedExtension.subsidize
          (G.mixedSingletonContinuousApproxTransfer p ε))
        ⟨p⟩
    exact (hσ i (p i) hdom).elim

theorem mixedSingletonContinuousApproxTransfer_isKImplementation [Finite G.Outcome]
    (p : Profile G.mixedExtension) {ε : ι → ℝ} (hε : ∀ i, 0 < ε i) :
    G.mixedExtension.IsKImplementation
      (G.mixedSingletonContinuousApproxTransfer p ε)
      ({p} : Set (Profile G.mixedExtension))
      (∑ i, (G.mixedImplementationGapAt p i p + ε i)) := by
  refine ⟨mixedSingletonContinuousApproxTransfer_isImplementation (G := G) p hε, ?_⟩
  intro σ hσ
  have hσp : σ = p := Set.mem_singleton_iff.mp
    ((mixedSingletonContinuousApproxTransfer_isImplementation (G := G) p hε).subset σ hσ)
  subst σ
  calc
    (∑ i, G.mixedSingletonContinuousApproxTransfer p ε p i) =
        ∑ i, (G.mixedImplementationGapAt p i p + ε i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [mixedSingletonContinuousApproxTransfer, sub_eq_add_neg]
      ring
    _ ≤ ∑ i, (G.mixedImplementationGapAt p i p + ε i) := le_rfl

theorem mixedSingletonContinuousApproxTransfer_ownUpperSemicontinuous
    [Finite G.Outcome]
    (p : Profile G.mixedExtension) (ε : ι → ℝ) :
    G.MixedOwnUpperSemicontinuous
      (G.mixedSingletonContinuousApproxTransfer p ε) := by
  classical
  intro i σ
  let C : ℝ :=
    G.mixedExtension.eu (Function.update σ i (p i)) i +
      G.mixedImplementationGapAt p i (Function.update σ i (p i)) + ε i
  have hcont :
      Continuous fun x : stdSimplex ℝ (G.Strategy i) =>
        C - (ε i / 4) * pmfL1Dist (ofVector (x : G.Strategy i → ℝ) x.property) (p i) := by
    exact continuous_const.sub
      (continuous_const.mul (continuous_pmfL1Dist_ofVector (p i)))
  have heq :
      (fun x : stdSimplex ℝ (G.Strategy i) =>
        (G.mixedExtension.subsidize
          (G.mixedSingletonContinuousApproxTransfer p ε)).eu
            (G.mixedProfileUpdateFromSimplex σ i x) i)
      =
      (fun x : stdSimplex ℝ (G.Strategy i) =>
        C - (ε i / 4) * pmfL1Dist (ofVector (x : G.Strategy i → ℝ) x.property) (p i)) := by
    funext x
    rw [mixedSingletonContinuousApproxTransfer_subsidized_eu]
    simp [mixedProfileUpdateFromSimplex, C]
  rw [heq]
  exact hcont.continuousOn.upperSemicontinuousOn

theorem mixedSingletonContinuousApproxTransfer_analyticAdmissible
    [Finite G.Outcome]
    (p : Profile G.mixedExtension) (ε : ι → ℝ) :
    G.MixedAnalyticAdmissible
      (G.mixedSingletonContinuousApproxTransfer p ε) :=
  mixedSingletonContinuousApproxTransfer_ownUpperSemicontinuous (G := G) p ε

/-- Exact admissible transfer for mixed singleton implementation.  The slack is
zero at the target column and positive at any opponent profile differing from
the target, measured by finite-coordinate L1 distance. -/
noncomputable def mixedSingletonDistanceTransfer
    (p : Profile G.mixedExtension) : Profile G.mixedExtension → Payoff ι :=
  open Classical in
  fun σ i =>
    if σ i = p i then
      G.mixedImplementationGapAt p i σ + mixedOpponentL1Dist (G := G) p σ i
    else 0

@[simp] theorem mixedSingletonDistanceTransfer_target
    (p : Profile G.mixedExtension) (i : ι) :
    G.mixedSingletonDistanceTransfer p p i = G.mixedImplementationGapAt p i p := by
  classical
  simp [mixedSingletonDistanceTransfer, mixedOpponentL1Dist, pmfL1Dist]

@[simp] theorem mixedSingletonDistanceTransfer_update_target
    (p : Profile G.mixedExtension) (i : ι) (σ : Profile G.mixedExtension) :
    G.mixedSingletonDistanceTransfer p (Function.update σ i (p i)) i =
      G.mixedImplementationGapAt p i (Function.update σ i (p i)) +
        mixedOpponentL1Dist (G := G) p (Function.update σ i (p i)) i := by
  classical
  simp [mixedSingletonDistanceTransfer]

theorem mixedSingletonDistanceTransfer_update_ne
    (p : Profile G.mixedExtension) (i : ι) (σ : Profile G.mixedExtension)
    {τ : PMF (G.Strategy i)} (hτ : τ ≠ p i) :
    G.mixedSingletonDistanceTransfer p (Function.update σ i τ) i = 0 := by
  classical
  rw [mixedSingletonDistanceTransfer, if_neg]
  simpa using hτ

theorem mixedSingletonDistanceTransfer_nonneg
    (p : Profile G.mixedExtension) :
    ∀ σ i, 0 ≤ G.mixedSingletonDistanceTransfer p σ i := by
  classical
  intro σ i
  by_cases hi : σ i = p i
  · have hgap := mixedImplementationGapAt_nonneg (G := G) p i σ
    have hdist := mixedOpponentL1Dist_nonneg (G := G) p σ i
    rw [mixedSingletonDistanceTransfer, if_pos hi]
    linarith
  · rw [mixedSingletonDistanceTransfer, if_neg hi]

theorem mixedSingletonDistanceTransfer_target_isDominant [Finite G.Outcome]
    (p : Profile G.mixedExtension) (i : ι) :
    (G.mixedExtension.subsidize (G.mixedSingletonDistanceTransfer p)).IsDominant
      i (p i) := by
  classical
  intro σ τ
  let σ' : Profile G.mixedExtension := σ
  by_cases hτ : τ = p i
  · subst τ
    simp
  · have hgap := mixedImplementationGapAt_ge_mixed (G := G) p i
      (Function.update σ' i (p i)) τ
    have hgap' :
        G.mixedExtension.eu (Function.update σ' i τ) i -
            G.mixedExtension.eu (Function.update σ' i (p i)) i ≤
          G.mixedImplementationGapAt p i (Function.update σ' i (p i)) := by
      simpa [Function.update_idem] using hgap
    rw [mixedExtension_subsidize_eu, mixedExtension_subsidize_eu]
    simp only [subsidize_Strategy, mixedSingletonDistanceTransfer_update_target, ge_iff_le]
    rw [mixedSingletonDistanceTransfer_update_ne (G := G) p i σ' hτ]
    simp only [add_zero]
    have hdist :
        0 ≤ mixedOpponentL1Dist (G := G) p (Function.update σ' i (p i)) i :=
      mixedOpponentL1Dist_nonneg (G := G) p (Function.update σ' i (p i)) i
    linarith

theorem mixedSingletonDistanceTransfer_weaklyStrictlyDominates_ne [Finite G.Outcome]
    (p : Profile G.mixedExtension) (hnd : G.MixedSingletonNondegenerate p)
    {i : ι} {τ : PMF (G.Strategy i)} (hτ : τ ≠ p i) :
    (G.mixedExtension.subsidize (G.mixedSingletonDistanceTransfer p)).WeaklyStrictlyDominates
      i (p i) τ := by
  classical
  refine ⟨(mixedSingletonDistanceTransfer_target_isDominant (G := G) p i).weaklyDominates τ, ?_⟩
  obtain ⟨j, hji, q, hq⟩ := hnd i
  let σ : Profile G.mixedExtension := Function.update p j q
  have hdist_pos :
      0 < mixedOpponentL1Dist (G := G) p (Function.update σ i (p i)) i := by
    have hupdate : Function.update σ i (p i) = Function.update p j q := by
      funext l
      by_cases hli : l = i
      · subst hli
        simp [σ, Function.update_of_ne hji.symm]
      · simp [σ, Function.update_of_ne hli]
    rw [hupdate]
    exact mixedOpponentL1Dist_update_pos (G := G) p hji hq
  have hgap := mixedImplementationGapAt_ge_mixed (G := G) p i
    (Function.update σ i (p i)) τ
  have hgap' :
      G.mixedExtension.eu (Function.update σ i τ) i -
          G.mixedExtension.eu (Function.update σ i (p i)) i ≤
        G.mixedImplementationGapAt p i (Function.update σ i (p i)) := by
    simpa [Function.update_idem] using hgap
  refine ⟨σ, ?_⟩
  rw [mixedExtension_subsidize_eu, mixedExtension_subsidize_eu]
  change G.mixedExtension.eu (Function.update σ i (p i)) i +
      G.mixedSingletonDistanceTransfer p (Function.update σ i (p i)) i >
    G.mixedExtension.eu (Function.update σ i τ) i +
      G.mixedSingletonDistanceTransfer p (Function.update σ i τ) i
  rw [mixedSingletonDistanceTransfer_update_target]
  rw [mixedSingletonDistanceTransfer_update_ne (G := G) p i σ hτ]
  simp only [add_zero]
  linarith

theorem mixedSingletonDistanceTransfer_isImplementation [Finite G.Outcome]
    (p : Profile G.mixedExtension) (hnd : G.MixedSingletonNondegenerate p) :
    G.mixedExtension.IsImplementation (G.mixedSingletonDistanceTransfer p)
      ({p} : Set (Profile G.mixedExtension)) := by
  refine ⟨mixedSingletonDistanceTransfer_nonneg (G := G) p, ?_, ?_⟩
  · exact ⟨p, fun i =>
      (mixedSingletonDistanceTransfer_target_isDominant (G := G) p i).isUndominated⟩
  · intro σ hσ
    apply Set.mem_singleton_iff.mpr
    funext i
    by_contra hne
    exact (hσ i (p i)
      (mixedSingletonDistanceTransfer_weaklyStrictlyDominates_ne (G := G) p hnd hne)).elim

theorem mixedSingletonDistanceTransfer_isKImplementation [Finite G.Outcome]
    (p : Profile G.mixedExtension) (hnd : G.MixedSingletonNondegenerate p) :
    G.mixedExtension.IsKImplementation (G.mixedSingletonDistanceTransfer p)
      ({p} : Set (Profile G.mixedExtension))
      (∑ i, G.mixedImplementationGapAt p i p) := by
  refine ⟨mixedSingletonDistanceTransfer_isImplementation (G := G) p hnd, ?_⟩
  intro σ hσ
  have hσp : σ = p := Set.mem_singleton_iff.mp
    ((mixedSingletonDistanceTransfer_isImplementation (G := G) p hnd).subset σ hσ)
  subst hσp
  simp

theorem mixedSingletonApproxTransfer_selectionAdmissible [Finite G.Outcome]
    (p : Profile G.mixedExtension) {ε : ι → ℝ} (hε : ∀ i, 0 ≤ ε i) :
    G.MixedSelectionAdmissibleAt (G.mixedSingletonApproxTransfer p ε) p :=
  MixedSelectionAdmissibleAt.of_dominant (G := G)
    (V := G.mixedSingletonApproxTransfer p ε) (p := p)
    (mixedSingletonApproxTransfer_target_isDominant (G := G) p hε)

theorem mixedSingletonDistanceTransfer_selectionAdmissible [Finite G.Outcome]
    (p : Profile G.mixedExtension) :
    G.MixedSelectionAdmissibleAt (G.mixedSingletonDistanceTransfer p) p :=
  MixedSelectionAdmissibleAt.of_dominant (G := G)
    (V := G.mixedSingletonDistanceTransfer p) (p := p)
    (mixedSingletonDistanceTransfer_target_isDominant (G := G) p)

/-- The exact distance-bump transfer is analytically admissible.  In each
player's own mixed strategy it is a continuous payoff function with one upward
spike at the target mixed strategy; such point spikes preserve upper
semicontinuity. -/
theorem mixedSingletonDistanceTransfer_ownUpperSemicontinuous [Finite G.Outcome]
    (p : Profile G.mixedExtension) :
    G.MixedOwnUpperSemicontinuous (G.mixedSingletonDistanceTransfer p) := by
  classical
  intro i σ
  let y : stdSimplex ℝ (G.Strategy i) :=
    ⟨toVector (p i), toVector_mem_stdSimplex (p i)⟩
  let base : stdSimplex ℝ (G.Strategy i) → ℝ := fun x =>
    G.mixedExtension.eu (G.mixedProfileUpdateFromSimplex σ i x) i
  let top : ℝ :=
    base y +
      G.mixedImplementationGapAt p i (Function.update σ i (p i)) +
        mixedOpponentL1Dist (G := G) p (Function.update σ i (p i)) i
  have hbase_cont : Continuous base := by
    simpa [base] using
      continuous_mixedExtension_eu_updateFromSimplex (G := G) σ i
  have hbase_le_top : base y ≤ top := by
    have hgap :
        0 ≤ G.mixedImplementationGapAt p i (Function.update σ i (p i)) :=
      mixedImplementationGapAt_nonneg (G := G) p i (Function.update σ i (p i))
    have hdist :
        0 ≤ mixedOpponentL1Dist (G := G) p (Function.update σ i (p i)) i :=
      mixedOpponentL1Dist_nonneg (G := G) p (Function.update σ i (p i)) i
    calc
      base y ≤ base y +
          (G.mixedImplementationGapAt p i (Function.update σ i (p i)) +
            mixedOpponentL1Dist (G := G) p (Function.update σ i (p i)) i) :=
        le_add_of_nonneg_right (add_nonneg hgap hdist)
      _ = top := by ring
  have hspike :
      UpperSemicontinuous (fun x : stdSimplex ℝ (G.Strategy i) =>
        if x = y then top else base x) :=
    Math.Topology.UpperSemicontinuous.update_of_le
      hbase_cont.upperSemicontinuous hbase_le_top
  have heq :
      (fun x : stdSimplex ℝ (G.Strategy i) =>
        (G.mixedExtension.subsidize (G.mixedSingletonDistanceTransfer p)).eu
          (G.mixedProfileUpdateFromSimplex σ i x) i)
      =
        (fun x : stdSimplex ℝ (G.Strategy i) =>
          if x = y then top else base x) := by
    funext x
    rw [mixedExtension_subsidize_eu]
    by_cases hx : x = y
    · subst hx
      have hprofile :
          G.mixedProfileUpdateFromSimplex σ i y = Function.update σ i (p i) := by
        simp [y,
          mixedProfileUpdateFromSimplex_toVector (G := G) σ i (p i)
        ]
      rw [hprofile, mixedSingletonDistanceTransfer_update_target]
      simp [base, top, hprofile]
      ring
    · have hxpmf :
          ofVector (x : G.Strategy i → ℝ) x.property ≠ p i := by
        intro hpmf
        exact hx ((Math.ProbabilityMassFunction.ofVector_eq_iff_eq_toVector x (p i)).mp hpmf)
      have htransfer :
          G.mixedSingletonDistanceTransfer p
              (G.mixedProfileUpdateFromSimplex σ i x) i = 0 := by
        rw [mixedSingletonDistanceTransfer, if_neg]
        simpa [mixedProfileUpdateFromSimplex] using hxpmf
      simp [base, hx, htransfer]
  rw [heq]
  exact upperSemicontinuousOn_univ_iff.mpr hspike

theorem mixedSingletonDistanceTransfer_analyticAdmissible [Finite G.Outcome]
    (p : Profile G.mixedExtension) :
    G.MixedAnalyticAdmissible (G.mixedSingletonDistanceTransfer p) :=
  mixedSingletonDistanceTransfer_ownUpperSemicontinuous (G := G) p

/-- Feasible budgets for singleton implementation in the mixed extension, with
transfers restricted to the semantic admissibility condition above. -/
def mixedAdmissibleImplementationCosts [Finite G.Outcome]
    (p : Profile G.mixedExtension) : Set ℝ :=
  {k | ∃ V : Profile G.mixedExtension → Payoff ι,
    G.MixedSelectionAdmissibleAt V p ∧
      G.mixedExtension.IsKImplementation V ({p} : Set (Profile G.mixedExtension)) k}

/-- Infimum admissible implementation cost for a mixed singleton target. -/
noncomputable def mixedAdmissibleImplPrice [Finite G.Outcome]
    (p : Profile G.mixedExtension) : ℝ :=
  sInf (G.mixedAdmissibleImplementationCosts p)

/-- Feasible budgets for singleton implementation in the mixed extension, with
transfers restricted to the analytic admissibility condition. -/
def mixedAnalyticImplementationCosts [Finite G.Outcome]
    (p : Profile G.mixedExtension) : Set ℝ :=
  {k | ∃ V : Profile G.mixedExtension → Payoff ι,
    G.MixedAnalyticAdmissible V ∧
      G.mixedExtension.IsKImplementation V ({p} : Set (Profile G.mixedExtension)) k}

/-- Infimum analytically admissible implementation cost for a mixed singleton
target. -/
noncomputable def mixedAnalyticImplPrice [Finite G.Outcome]
    (p : Profile G.mixedExtension) : ℝ :=
  sInf (G.mixedAnalyticImplementationCosts p)

omit strategyFintype strategyNonempty in
theorem mixedAdmissibleImplementationCosts_bddBelow [Finite G.Outcome]
    (p : Profile G.mixedExtension) :
    BddBelow (G.mixedAdmissibleImplementationCosts p) := by
  refine ⟨0, ?_⟩
  intro k hk
  obtain ⟨V, _, hV⟩ := hk
  exact hV.cost_nonneg

omit strategyFintype strategyNonempty in
theorem mixedAnalyticImplementationCosts_bddBelow [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)]
    (p : Profile G.mixedExtension) :
    BddBelow (G.mixedAnalyticImplementationCosts p) := by
  refine ⟨0, ?_⟩
  intro k hk
  obtain ⟨V, _, hV⟩ := hk
  exact hV.cost_nonneg

theorem mixedAdmissibleImplementationCosts_mem_of_gap_sum_lt
    [Finite G.Outcome] [Nonempty ι]
    (p : Profile G.mixedExtension) {k : ℝ}
    (hk : (∑ i, G.mixedImplementationGapAt p i p) < k) :
    k ∈ G.mixedAdmissibleImplementationCosts p := by
  classical
  let gapSum : ℝ := ∑ i, G.mixedImplementationGapAt p i p
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
  have hbudget : (∑ i, (G.mixedImplementationGapAt p i p + ε i)) = k := by
    rw [Finset.sum_add_distrib, hsumε]
    simp [gapSum]
  refine ⟨G.mixedSingletonApproxTransfer p ε, ?_, ?_⟩
  · exact mixedSingletonApproxTransfer_selectionAdmissible (G := G) p
      (fun i => le_of_lt (hεpos i))
  · simpa [hbudget] using mixedSingletonApproxTransfer_isKImplementation
      (G := G) p hεpos

theorem mixedAnalyticImplementationCosts_mem_of_gap_sum_lt
    [Finite G.Outcome] [Nonempty ι]
    (p : Profile G.mixedExtension) {k : ℝ}
    (hk : (∑ i, G.mixedImplementationGapAt p i p) < k) :
    k ∈ G.mixedAnalyticImplementationCosts p := by
  classical
  let gapSum : ℝ := ∑ i, G.mixedImplementationGapAt p i p
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
  have hbudget : (∑ i, (G.mixedImplementationGapAt p i p + ε i)) = k := by
    rw [Finset.sum_add_distrib, hsumε]
    simp [gapSum]
  refine ⟨G.mixedSingletonContinuousApproxTransfer p ε, ?_, ?_⟩
  · exact mixedSingletonContinuousApproxTransfer_analyticAdmissible (G := G) p ε
  · simpa [hbudget] using mixedSingletonContinuousApproxTransfer_isKImplementation
      (G := G) p hεpos

theorem mixedAdmissibleImplementationCosts_mem_gap_sum_of_nondegenerate
    [Finite G.Outcome]
    (p : Profile G.mixedExtension) (hnd : G.MixedSingletonNondegenerate p) :
    (∑ i, G.mixedImplementationGapAt p i p) ∈
      G.mixedAdmissibleImplementationCosts p := by
  exact ⟨G.mixedSingletonDistanceTransfer p,
    mixedSingletonDistanceTransfer_selectionAdmissible (G := G) p,
    mixedSingletonDistanceTransfer_isKImplementation (G := G) p hnd⟩

theorem mixedAnalyticImplementationCosts_mem_gap_sum_of_nondegenerate
    [Finite G.Outcome]
    (p : Profile G.mixedExtension) (hnd : G.MixedSingletonNondegenerate p) :
    (∑ i, G.mixedImplementationGapAt p i p) ∈
      G.mixedAnalyticImplementationCosts p := by
  exact ⟨G.mixedSingletonDistanceTransfer p,
    mixedSingletonDistanceTransfer_analyticAdmissible (G := G) p,
    mixedSingletonDistanceTransfer_isKImplementation (G := G) p hnd⟩

omit strategyFintype strategyNonempty in
theorem mixedAdmissibleImplPrice_le_of_mem [Finite G.Outcome]
    {p : Profile G.mixedExtension} {k : ℝ}
    (hk : k ∈ G.mixedAdmissibleImplementationCosts p) :
    G.mixedAdmissibleImplPrice p ≤ k := by
  exact csInf_le (mixedAdmissibleImplementationCosts_bddBelow (G := G) p) hk

omit strategyFintype strategyNonempty in
theorem mixedAnalyticImplPrice_le_of_mem [Finite G.Outcome]
    [∀ i, Fintype (G.Strategy i)]
    {p : Profile G.mixedExtension} {k : ℝ}
    (hk : k ∈ G.mixedAnalyticImplementationCosts p) :
    G.mixedAnalyticImplPrice p ≤ k := by
  exact csInf_le (mixedAnalyticImplementationCosts_bddBelow (G := G) p) hk

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

theorem mixedAdmissibleImplPrice_singleton [Finite G.Outcome] [Nonempty ι]
    (p : Profile G.mixedExtension) :
    G.mixedAdmissibleImplPrice p = ∑ i, G.mixedImplementationGapAt p i p := by
  classical
  let gapSum : ℝ := ∑ i, G.mixedImplementationGapAt p i p
  exact sInf_eq_of_forall_lt_mem_of_forall_le
    (Costs := G.mixedAdmissibleImplementationCosts p)
    (Price := G.mixedAdmissibleImplPrice p)
    (L := gapSum)
    rfl
    (mixedAdmissibleImplementationCosts_bddBelow (G := G) p)
    (fun {k} hk =>
      mixedAdmissibleImplementationCosts_mem_of_gap_sum_lt (G := G) p
        (k := k) (by simpa [gapSum] using hk))
    (fun k hk => by
      obtain ⟨V, hadm, hV⟩ := hk
      simpa [gapSum] using
        mixedSingletonKImplementation_lower_bound_of_admissible
          (G := G) (V := V) (p := p) hadm hV)

theorem mixedSingletonKImplementation_lower_bound_of_analytic
    [Finite G.Outcome]
    {V : Profile G.mixedExtension → Payoff ι} {p : Profile G.mixedExtension}
    {k : ℝ}
    (han : G.MixedAnalyticAdmissible V)
    (hV : G.mixedExtension.IsKImplementation V ({p} : Set (Profile G.mixedExtension)) k) :
    (∑ i, G.mixedImplementationGapAt p i p) ≤ k :=
  mixedSingletonKImplementation_lower_bound_of_admissible (G := G) (V := V) (p := p)
    han.selectionAdmissible hV

theorem mixedAnalyticImplPrice_singleton [Finite G.Outcome] [Nonempty ι]
    (p : Profile G.mixedExtension) :
    G.mixedAnalyticImplPrice p = ∑ i, G.mixedImplementationGapAt p i p := by
  classical
  let gapSum : ℝ := ∑ i, G.mixedImplementationGapAt p i p
  exact sInf_eq_of_forall_lt_mem_of_forall_le
    (Costs := G.mixedAnalyticImplementationCosts p)
    (Price := G.mixedAnalyticImplPrice p)
    (L := gapSum)
    rfl
    (mixedAnalyticImplementationCosts_bddBelow (G := G) p)
    (fun {k} hk =>
      mixedAnalyticImplementationCosts_mem_of_gap_sum_lt (G := G) p
        (k := k) (by simpa [gapSum] using hk))
    (fun k hk => by
      obtain ⟨V, han, hV⟩ := hk
      simpa [gapSum] using
        mixedSingletonKImplementation_lower_bound_of_analytic
          (G := G) (V := V) (p := p) han hV)

theorem mixedAdmissibleImplPrice_singleton_of_nondegenerate [Finite G.Outcome]
    (p : Profile G.mixedExtension) (hnd : G.MixedSingletonNondegenerate p) :
    G.mixedAdmissibleImplPrice p = ∑ i, G.mixedImplementationGapAt p i p := by
  classical
  let gapSum : ℝ := ∑ i, G.mixedImplementationGapAt p i p
  exact sInf_eq_of_mem_of_forall_le
    (Costs := G.mixedAdmissibleImplementationCosts p)
    (Price := G.mixedAdmissibleImplPrice p)
    (L := gapSum)
    rfl
    (mixedAdmissibleImplementationCosts_bddBelow (G := G) p)
    (by
      simpa [gapSum] using
        mixedAdmissibleImplementationCosts_mem_gap_sum_of_nondegenerate
          (G := G) p hnd)
    (fun k hk => by
      obtain ⟨V, hadm, hV⟩ := hk
      simpa [gapSum] using
        mixedSingletonKImplementation_lower_bound_of_admissible
          (G := G) (V := V) (p := p) hadm hV)

theorem mixedAnalyticImplPrice_singleton_of_nondegenerate [Finite G.Outcome]
    (p : Profile G.mixedExtension) (hnd : G.MixedSingletonNondegenerate p) :
    G.mixedAnalyticImplPrice p = ∑ i, G.mixedImplementationGapAt p i p := by
  classical
  let gapSum : ℝ := ∑ i, G.mixedImplementationGapAt p i p
  exact sInf_eq_of_mem_of_forall_le
    (Costs := G.mixedAnalyticImplementationCosts p)
    (Price := G.mixedAnalyticImplPrice p)
    (L := gapSum)
    rfl
    (mixedAnalyticImplementationCosts_bddBelow (G := G) p)
    (by
      simpa [gapSum] using
        mixedAnalyticImplementationCosts_mem_gap_sum_of_nondegenerate
          (G := G) p hnd)
    (fun k hk => by
      obtain ⟨V, han, hV⟩ := hk
      simpa [gapSum] using
        mixedSingletonKImplementation_lower_bound_of_analytic
          (G := G) (V := V) (p := p) han hV)

theorem mixedAnalyticImplPrice_mem_analyticImplementationCosts_of_nondegenerate
    [Finite G.Outcome]
    (p : Profile G.mixedExtension) (hnd : G.MixedSingletonNondegenerate p) :
    G.mixedAnalyticImplPrice p ∈ G.mixedAnalyticImplementationCosts p := by
  rw [mixedAnalyticImplPrice_singleton_of_nondegenerate (G := G) p hnd]
  exact mixedAnalyticImplementationCosts_mem_gap_sum_of_nondegenerate (G := G) p hnd

theorem mixedImplementationGapAt_eq_zero_of_isNash [Finite G.Outcome]
    {p : Profile G.mixedExtension} (hN : G.mixedExtension.IsNash p) (i : ι) :
    G.mixedImplementationGapAt p i p = 0 := by
  classical
  have hsup_nonpos :
      Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy i))
        (fun a : G.Strategy i =>
          G.mixedExtension.eu (Function.update p i (PMF.pure a)) i -
            G.mixedExtension.eu (Function.update p i (p i)) i) ≤ 0 := by
    apply Finset.sup'_le
    intro a _
    have hdev := hN i (PMF.pure a)
    simpa [Function.update_eq_self] using sub_nonpos.mpr hdev
  rw [mixedImplementationGapAt]
  exact max_eq_left hsup_nonpos

theorem mixedImplementationGap_sum_nonpos_isNash [Finite G.Outcome]
    (p : Profile G.mixedExtension)
    (hgap : (∑ i, G.mixedImplementationGapAt p i p) ≤ 0) :
    G.mixedExtension.IsNash p := by
  intro i τ
  have hterm_le_sum :
      G.mixedImplementationGapAt p i p ≤ ∑ j, G.mixedImplementationGapAt p j p :=
    Finset.single_le_sum
      (fun j _ => mixedImplementationGapAt_nonneg (G := G) p j p)
      (Finset.mem_univ i)
  have hgap_i : G.mixedImplementationGapAt p i p ≤ 0 := hterm_le_sum.trans hgap
  have hdev := mixedImplementationGapAt_ge_mixed (G := G) p i p τ
  simpa [Function.update_eq_self] using sub_nonpos.mp (hdev.trans hgap_i)

omit strategyFintype in
theorem mixedAdmissibleImplPrice_singleton_eq_zero_iff_isNash
    [∀ i, Finite (G.Strategy i)] [Finite G.Outcome] [Nonempty ι]
    (p : Profile G.mixedExtension) :
    G.mixedAdmissibleImplPrice p = 0 ↔ G.mixedExtension.IsNash p := by
  classical
  letI : ∀ i, Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  rw [mixedAdmissibleImplPrice_singleton (G := G) p]
  constructor
  · intro hprice
    exact mixedImplementationGap_sum_nonpos_isNash (G := G) p (by
      simp [hprice])
  · intro hN
    apply Finset.sum_eq_zero
    intro i _
    exact mixedImplementationGapAt_eq_zero_of_isNash (G := G) hN i

omit strategyFintype in
theorem mixedAnalyticImplPrice_singleton_eq_zero_iff_isNash
    [∀ i, Fintype (G.Strategy i)] [Finite G.Outcome] [Nonempty ι]
    (p : Profile G.mixedExtension) :
    G.mixedAnalyticImplPrice p = 0 ↔ G.mixedExtension.IsNash p := by
  classical
  rw [mixedAnalyticImplPrice_singleton (G := G) p]
  constructor
  · intro hprice
    exact mixedImplementationGap_sum_nonpos_isNash (G := G) p (by
      simp [hprice])
  · intro hN
    apply Finset.sum_eq_zero
    intro i _
    exact mixedImplementationGapAt_eq_zero_of_isNash (G := G) hN i

omit strategyFintype in
theorem isNash_of_exists_zero_mixedAdmissibleKImplementation
    [∀ i, Finite (G.Strategy i)] [Finite G.Outcome]
    {p : Profile G.mixedExtension} :
    (∃ V : Profile G.mixedExtension → Payoff ι,
      G.MixedSelectionAdmissibleAt V p ∧
        G.mixedExtension.IsKImplementation V ({p} : Set (Profile G.mixedExtension)) 0) →
      G.mixedExtension.IsNash p := by
  classical
  letI : ∀ i, Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  rintro ⟨V, hadm, hV⟩
  have hsum : (∑ i, G.mixedImplementationGapAt p i p) ≤ 0 :=
    mixedSingletonKImplementation_lower_bound_of_admissible
      (G := G) (V := V) (p := p) hadm hV
  exact mixedImplementationGap_sum_nonpos_isNash (G := G) p hsum

theorem isNash_of_exists_zero_mixedAnalyticKImplementation
    [∀ i, Finite (G.Strategy i)] [Finite G.Outcome]
    {p : Profile G.mixedExtension} :
    (∃ V : Profile G.mixedExtension → Payoff ι,
      G.MixedAnalyticAdmissible V ∧
        G.mixedExtension.IsKImplementation V ({p} : Set (Profile G.mixedExtension)) 0) →
      G.mixedExtension.IsNash p := by
  rintro ⟨V, han, hV⟩
  exact isNash_of_exists_zero_mixedAdmissibleKImplementation (G := G)
    ⟨V, han.selectionAdmissible, hV⟩

omit strategyFintype in
theorem exists_zero_mixedAdmissibleKImplementation_iff_isNash
    [∀ i, Finite (G.Strategy i)] [Finite G.Outcome] {p : Profile G.mixedExtension}
    (hnd : G.MixedSingletonNondegenerate p) :
    (∃ V : Profile G.mixedExtension → Payoff ι,
      G.MixedSelectionAdmissibleAt V p ∧
        G.mixedExtension.IsKImplementation V ({p} : Set (Profile G.mixedExtension)) 0) ↔
      G.mixedExtension.IsNash p := by
  classical
  letI : ∀ i, Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  constructor
  · exact isNash_of_exists_zero_mixedAdmissibleKImplementation (G := G)
  · intro hN
    refine ⟨G.mixedSingletonDistanceTransfer p,
      mixedSingletonDistanceTransfer_selectionAdmissible (G := G) p, ?_⟩
    have hsum : (∑ i, G.mixedImplementationGapAt p i p) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact mixedImplementationGapAt_eq_zero_of_isNash (G := G) hN i
    exact (mixedSingletonDistanceTransfer_isKImplementation (G := G) p hnd).mono_cost
      (by rw [hsum])

theorem exists_zero_mixedAnalyticKImplementation_iff_isNash
    [Finite G.Outcome] {p : Profile G.mixedExtension}
    (hnd : G.MixedSingletonNondegenerate p) :
    (∃ V : Profile G.mixedExtension → Payoff ι,
      G.MixedAnalyticAdmissible V ∧
        G.mixedExtension.IsKImplementation V ({p} : Set (Profile G.mixedExtension)) 0) ↔
      G.mixedExtension.IsNash p := by
  classical
  constructor
  · rintro ⟨V, han, hV⟩
    have hsum : (∑ i, G.mixedImplementationGapAt p i p) ≤ 0 :=
      mixedSingletonKImplementation_lower_bound_of_analytic
        (G := G) (V := V) (p := p) han hV
    exact mixedImplementationGap_sum_nonpos_isNash (G := G) p hsum
  · intro hN
    refine ⟨G.mixedSingletonDistanceTransfer p,
      mixedSingletonDistanceTransfer_analyticAdmissible (G := G) p, ?_⟩
    have hsum : (∑ i, G.mixedImplementationGapAt p i p) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact mixedImplementationGapAt_eq_zero_of_isNash (G := G) hN i
    exact (mixedSingletonDistanceTransfer_isKImplementation (G := G) p hnd).mono_cost
      (by rw [hsum])

/-- Transfer scheme for observable mixed-strategy implementation. Player `i`
is paid only when choosing the target mixed strategy `p i`; the payment covers
the maximal pure-deviation gain against the current mixed opponents, with a
unit off-target bump for the strict dominance witness. -/
noncomputable def mixedSingletonTransfer
    (p : Profile G.mixedExtension) : Profile G.mixedExtension → Payoff ι :=
  open Classical in
  fun σ i =>
    if σ i = p i then
      G.mixedImplementationGapAt p i σ + if σ = p then 0 else 1
    else 0

@[simp] theorem mixedSingletonTransfer_target
    (p : Profile G.mixedExtension) (i : ι) :
    G.mixedSingletonTransfer p p i = G.mixedImplementationGapAt p i p := by
  classical
  simp [mixedSingletonTransfer]

open Classical in
@[simp] theorem mixedSingletonTransfer_update_target
    (p : Profile G.mixedExtension) (i : ι) (σ : Profile G.mixedExtension) :
    G.mixedSingletonTransfer p (Function.update σ i (p i)) i =
      G.mixedImplementationGapAt p i (Function.update σ i (p i)) +
        if Function.update σ i (p i) = p then 0 else 1 := by
  classical
  rw [mixedSingletonTransfer]
  have hself : Function.update σ i (p i) i = p i := by simp
  rw [if_pos hself]

theorem mixedSingletonTransfer_update_ne
    (p : Profile G.mixedExtension) (i : ι) (σ : Profile G.mixedExtension)
    {τ : PMF (G.Strategy i)} (hτ : τ ≠ p i) :
    G.mixedSingletonTransfer p (Function.update σ i τ) i = 0 := by
  classical
  unfold mixedSingletonTransfer
  rw [if_neg]
  simpa using hτ

theorem mixedSingletonTransfer_nonneg
    (p : Profile G.mixedExtension) :
    ∀ σ i, 0 ≤ G.mixedSingletonTransfer p σ i := by
  classical
  intro σ i
  by_cases hi : σ i = p i
  · have hgap := mixedImplementationGapAt_nonneg (G := G) p i σ
    by_cases hσ : σ = p
    · subst hσ
      simpa [mixedSingletonTransfer] using hgap
    · simp [mixedSingletonTransfer, hi, hσ]
      linarith
  · rw [mixedSingletonTransfer, if_neg hi]

theorem mixedSingletonTransfer_target_isDominant [Finite G.Outcome]
    (p : Profile G.mixedExtension) (i : ι) :
    (G.mixedExtension.subsidize (G.mixedSingletonTransfer p)).IsDominant i (p i) := by
  classical
  intro σ τ
  let σ' : Profile G.mixedExtension := σ
  let τ' : PMF (G.Strategy i) := τ
  change (G.mixedExtension.subsidize (G.mixedSingletonTransfer p)).eu
      (Function.update σ' i (p i)) i ≥
    (G.mixedExtension.subsidize (G.mixedSingletonTransfer p)).eu
      (Function.update σ' i τ') i
  by_cases hτ : τ' = p i
  · simp [hτ]
  · have hgap := mixedImplementationGapAt_ge_mixed (G := G) p i
      (Function.update σ' i (p i)) τ'
    have hgap' :
        G.mixedExtension.eu (Function.update σ' i τ') i -
            G.mixedExtension.eu (Function.update σ' i (p i)) i ≤
          G.mixedImplementationGapAt p i (Function.update σ' i (p i)) := by
      simpa [Function.update_idem] using hgap
    rw [mixedExtension_subsidize_eu, mixedExtension_subsidize_eu]
    simp only [subsidize_Strategy, mixedSingletonTransfer_update_target, ge_iff_le]
    rw [mixedSingletonTransfer_update_ne (G := G) p i σ' hτ]
    simp only [add_zero]
    have hbump :
        0 ≤ if Function.update σ' i (p i) = p then (0 : ℝ) else 1 := by
      split <;> norm_num
    linarith

theorem mixedSingletonTransfer_weaklyStrictlyDominates_ne [Finite G.Outcome]
    (p : Profile G.mixedExtension) (hnd : G.MixedSingletonNondegenerate p)
    {i : ι} {τ : PMF (G.Strategy i)} (hτ : τ ≠ p i) :
    (G.mixedExtension.subsidize (G.mixedSingletonTransfer p)).WeaklyStrictlyDominates
      i (p i) τ := by
  classical
  refine ⟨(mixedSingletonTransfer_target_isDominant (G := G) p i).weaklyDominates τ, ?_⟩
  obtain ⟨j, hji, q, hq⟩ := hnd i
  let σ : Profile G.mixedExtension := Function.update p j q
  have htarget_ne : Function.update σ i (p i) ≠ p := by
    intro hEq
    have hcoord := congrFun hEq j
    simp [σ, Function.update_of_ne hji, hq] at hcoord
  have hgap := mixedImplementationGapAt_ge_mixed (G := G) p i
    (Function.update σ i (p i)) τ
  have hgap' :
      G.mixedExtension.eu (Function.update σ i τ) i -
          G.mixedExtension.eu (Function.update σ i (p i)) i ≤
        G.mixedImplementationGapAt p i (Function.update σ i (p i)) := by
    simpa [Function.update_idem] using hgap
  refine ⟨σ, ?_⟩
  rw [mixedExtension_subsidize_eu, mixedExtension_subsidize_eu]
  change G.mixedExtension.eu (Function.update σ i (p i)) i +
      G.mixedSingletonTransfer p (Function.update σ i (p i)) i >
    G.mixedExtension.eu (Function.update σ i τ) i +
      G.mixedSingletonTransfer p (Function.update σ i τ) i
  rw [mixedSingletonTransfer_update_target]
  rw [mixedSingletonTransfer_update_ne (G := G) p i σ hτ]
  rw [if_neg htarget_ne]
  simp only [mixedExtension_Strategy, add_zero, gt_iff_lt]
  have hdev_le :
      G.mixedExtension.eu (Function.update σ i τ) i ≤
        G.mixedExtension.eu (Function.update σ i (p i)) i +
          G.mixedImplementationGapAt p i (Function.update σ i (p i)) := by
    linarith
  have hbump_strict :
      G.mixedExtension.eu (Function.update σ i (p i)) i +
          G.mixedImplementationGapAt p i (Function.update σ i (p i)) <
        G.mixedExtension.eu (Function.update σ i (p i)) i +
          (G.mixedImplementationGapAt p i (Function.update σ i (p i)) + 1) := by
    have hone : (0 : ℝ) < 1 := by norm_num
    calc
      G.mixedExtension.eu (Function.update σ i (p i)) i +
          G.mixedImplementationGapAt p i (Function.update σ i (p i))
          = (G.mixedExtension.eu (Function.update σ i (p i)) i +
              G.mixedImplementationGapAt p i (Function.update σ i (p i))) + 0 := by
            ring
      _ < (G.mixedExtension.eu (Function.update σ i (p i)) i +
              G.mixedImplementationGapAt p i (Function.update σ i (p i))) + 1 :=
            add_lt_add_right hone _
      _ = G.mixedExtension.eu (Function.update σ i (p i)) i +
            (G.mixedImplementationGapAt p i (Function.update σ i (p i)) + 1) := by
            ring
  exact lt_of_le_of_lt hdev_le hbump_strict

theorem mixedSingletonTransfer_target_undominated [Finite G.Outcome]
    (p : Profile G.mixedExtension) (i : ι) :
    (G.mixedExtension.subsidize (G.mixedSingletonTransfer p)).IsUndominated i (p i) :=
  (mixedSingletonTransfer_target_isDominant (G := G) p i).isUndominated

theorem mixedSingletonTransfer_p_mem_undominated [Finite G.Outcome]
    (p : Profile G.mixedExtension) :
    p ∈ (G.mixedExtension.subsidize (G.mixedSingletonTransfer p)).undominatedProfiles := by
  intro i
  exact mixedSingletonTransfer_target_undominated (G := G) p i

theorem mixedSingletonTransfer_undominated_subset_singleton [Finite G.Outcome]
    (p : Profile G.mixedExtension) (hnd : G.MixedSingletonNondegenerate p) :
    ∀ σ : Profile G.mixedExtension,
      σ ∈ (G.mixedExtension.subsidize (G.mixedSingletonTransfer p)).undominatedProfiles →
        σ ∈ ({p} : Set (Profile G.mixedExtension)) := by
  intro σ hσ
  have hcoord : ∀ i, σ i = p i := by
    intro i
    by_contra hne
    have hdom := mixedSingletonTransfer_weaklyStrictlyDominates_ne (G := G) p hnd
      (i := i) (τ := σ i) hne
    exact (hσ i (p i) hdom).elim
  exact Set.mem_singleton_iff.mpr (funext hcoord)

theorem mixedSingletonTransfer_isImplementation [Finite G.Outcome]
    (p : Profile G.mixedExtension) (hnd : G.MixedSingletonNondegenerate p) :
    G.mixedExtension.IsImplementation (G.mixedSingletonTransfer p)
      ({p} : Set (Profile G.mixedExtension)) := by
  refine ⟨mixedSingletonTransfer_nonneg (G := G) p, ?_, ?_⟩
  · exact ⟨p, mixedSingletonTransfer_p_mem_undominated (G := G) p⟩
  · exact mixedSingletonTransfer_undominated_subset_singleton (G := G) p hnd

theorem mixedImplementationGapAt_target_eq_zero_of_isNash [Finite G.Outcome]
    {p : Profile G.mixedExtension} (hN : G.mixedExtension.IsNash p) (i : ι) :
    G.mixedImplementationGapAt p i p = 0 := by
  classical
  have hsup_nonpos :
      Finset.univ.sup' (Finset.univ_nonempty (α := G.Strategy i))
        (fun a : G.Strategy i =>
          G.mixedExtension.eu (Function.update p i (PMF.pure a)) i -
            G.mixedExtension.eu (Function.update p i (p i)) i) ≤ 0 := by
    apply Finset.sup'_le
    intro a _
    have hdev := hN i (PMF.pure a)
    simpa [Function.update_eq_self] using sub_nonpos.mpr hdev
  rw [mixedImplementationGapAt]
  exact max_eq_left hsup_nonpos

omit strategyFintype in
/-- Constructive direction of Theorem 3: an observable mixed Nash profile is
0-implementable as a singleton in the mixed extension. -/
theorem mixedNash_exists_zero_singletonKImplementation
    [Finite G.Outcome] [∀ i, Finite (G.Strategy i)]
    {p : Profile G.mixedExtension} (hnd : G.MixedSingletonNondegenerate p)
    (hN : G.mixedExtension.IsNash p) :
    ∃ V : Profile G.mixedExtension → Payoff ι,
      G.mixedExtension.IsKImplementation V ({p} : Set (Profile G.mixedExtension)) 0 := by
  letI : ∀ i, Fintype (G.Strategy i) := fun i => Fintype.ofFinite (G.Strategy i)
  refine ⟨G.mixedSingletonTransfer p, ?_⟩
  refine ⟨mixedSingletonTransfer_isImplementation (G := G) p hnd, ?_⟩
  intro σ hσ
  have hσp : σ = p := by
    have hmem := mixedSingletonTransfer_undominated_subset_singleton (G := G) p hnd σ hσ
    simpa using hmem
  subst hσp
  simp [mixedImplementationGapAt_target_eq_zero_of_isNash (G := G) hN]

omit strategyFintype in
/-- Paper-shaped version of the constructive direction of Theorem 3: under the
usual finite-game hypotheses, every mixed Nash profile is 0-implementable as a
singleton in the mixed extension when mixed strategies are observable. -/
theorem mixedNash_exists_zero_singletonKImplementation_of_one_lt_card
    [Finite G.Outcome] [∀ i, Finite (G.Strategy i)]
    [∀ i, Nontrivial (G.Strategy i)]
    {p : Profile G.mixedExtension} (hι : 1 < Fintype.card ι)
    (hN : G.mixedExtension.IsNash p) :
    ∃ V : Profile G.mixedExtension → Payoff ι,
      G.mixedExtension.IsKImplementation V ({p} : Set (Profile G.mixedExtension)) 0 := by
  let hnd := G.mixedSingletonNondegenerate_of_one_lt_card p hι
  exact mixedNash_exists_zero_singletonKImplementation (G := G) hnd hN

end ObservableMixed

end KernelGame

end GameTheory
