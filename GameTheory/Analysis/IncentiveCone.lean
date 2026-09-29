/-
# Exact implication between incentive constraints

An incentive comparison orders two outcome laws: keeping a prescribed plan is
weakly preferred to one alternative. On a finite outcome carrier, every utility
respecting a family of source comparisons respects a target comparison exactly
when the target's probability difference lies in the least closed convex cone
containing the source differences. The target need not match either outcome
law of any source comparison, and nonnegative coefficients need not sum to one.
The family of comparisons may be infinite; the criterion asserts no decision
procedure.

When utilities are restricted to a linear subspace, only the orthogonal
projections of the incentive differences onto that subspace matter, and the
same closed-cone criterion is exact within the subspace. A finite nonnegative
combination of projected comparisons also bounds regret for the original
utility: its residual interacts only with the utility's component outside the
retained subspace.

Equilibrium predicates are families of such comparisons, one family per
deviating unit. Preservation of an equilibrium predicate for every utility is
therefore exactly playerwise cone inclusion. Utility classes coupling different
units' payoffs, such as zero-sum restrictions, are handled in the joint space
of unit-tagged outcomes; projecting each unit separately would lose them.
-/

import GameTheory.Core.Equilibrium
import GameTheory.Core.ExpectedUtility
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability
open scoped RealInnerProductSpace

universe u v w us ut

/-- Keeping a prescribed plan must be at least as good as its alternative. -/
structure IncentiveComparison (Outcome : Type u) where
  /-- The outcome law of the prescribed plan. -/
  prescribed : PMF Outcome
  /-- The outcome law of the alternative. -/
  alternative : PMF Outcome

namespace IncentiveComparison

variable {Outcome : Type u}

/-- The comparison holds when the prescribed law is weakly expected-utility
preferred to the alternative, both expectations being defined. -/
def Holds (comparison : IncentiveComparison Outcome) (utility : Outcome → ℝ) : Prop :=
  euPreference (fun outcome (_ : Unit) => utility outcome) ()
    comparison.prescribed comparison.alternative

/-- Expected-utility preference between two laws is the comparison of those
laws. -/
theorem euPreference_iff_holds {Unit' : Type v} (utility : Outcome → Unit' → ℝ)
    (who : Unit') (prescribed alternative : PMF Outcome) :
    euPreference utility who prescribed alternative ↔
      (IncentiveComparison.mk prescribed alternative).Holds (utility · who) :=
  Iff.rfl

/-- Observing outcomes through a map compares the pushed-forward laws. -/
theorem holds_map_iff {Source : Type v} (observe : Source → Outcome)
    (prescribed alternative : PMF Source) (utility : Outcome → ℝ) :
    (IncentiveComparison.mk (prescribed.map observe) (alternative.map observe)).Holds utility ↔
      (IncentiveComparison.mk prescribed alternative).Holds (utility ∘ observe) := by
  constructor
  · rintro ⟨hprescribed, halternative, hle⟩
    have hp := (payoffIntegrable_map_iff observe prescribed utility).1 hprescribed
    have ha := (payoffIntegrable_map_iff observe alternative utility).1 halternative
    refine ⟨hp, ha, ?_⟩
    have hpe := expect_map observe prescribed utility
    have hae := expect_map observe alternative utility
    simp only [expectedUtility] at hle ⊢
    rw [hpe, hae] at hle
    exact hle
  · rintro ⟨hp, ha, hle⟩
    have hprescribed := (payoffIntegrable_map_iff observe prescribed utility).2 hp
    have halternative := (payoffIntegrable_map_iff observe alternative utility).2 ha
    refine ⟨hprescribed, halternative, ?_⟩
    have hpe := expect_map observe prescribed utility
    have hae := expect_map observe alternative utility
    simp only [expectedUtility] at hle ⊢
    rw [hpe, hae]
    exact hle

variable [Fintype Outcome]

/-- On a finite carrier every expectation is defined, so a comparison is the
inequality of its two expectations. -/
theorem holds_iff (comparison : IncentiveComparison Outcome) (utility : Outcome → ℝ) :
    comparison.Holds utility ↔
      expect comparison.alternative utility ≤
        expect comparison.prescribed utility :=
  euPreference_iff _ () _ _ (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)

/-- Signed mass of keeping the prescribed plan rather than deviating. -/
def difference (comparison : IncentiveComparison Outcome) : EuclideanSpace ℝ Outcome :=
  WithLp.toLp 2 fun outcome =>
    (comparison.prescribed outcome).toReal - (comparison.alternative outcome).toReal

theorem inner_difference (comparison : IncentiveComparison Outcome) (utility : Outcome → ℝ) :
    ⟪comparison.difference, WithLp.toLp 2 utility⟫ =
      expect comparison.prescribed utility -
        expect comparison.alternative utility := by
  simp only [difference, EuclideanSpace.inner_toLp_toLp, dotProduct, Pi.star_apply,
    star_trivial, expect_eq_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro outcome _ <;> exact mul_comm _ _

theorem holds_iff_inner (comparison : IncentiveComparison Outcome) (utility : Outcome → ℝ) :
    comparison.Holds utility ↔ 0 ≤ ⟪comparison.difference, WithLp.toLp 2 utility⟫ := by
  rw [holds_iff, inner_difference, sub_nonneg]

/-- The zero utility respects every comparison. -/
theorem holds_zero (comparison : IncentiveComparison Outcome) :
    comparison.Holds fun _ => 0 := by
  rw [holds_iff, expect_zero, expect_zero]

variable {Index : Type v}

/-- The closed convex cone generated by all source incentive differences. -/
def cone (comparisons : Index → IncentiveComparison Outcome) :
    ProperCone ℝ (EuclideanSpace ℝ Outcome) :=
  ProperCone.innerDual (ProperCone.innerDual (Set.range fun index =>
    (comparisons index).difference) : Set (EuclideanSpace ℝ Outcome))

theorem difference_mem_cone (comparisons : Index → IncentiveComparison Outcome) (index : Index) :
    (comparisons index).difference ∈ cone comparisons := by
  intro utility nonnegative
  change 0 ≤ ⟪utility, (comparisons index).difference⟫
  rw [real_inner_comm]
  exact nonnegative ⟨index, rfl⟩

/-- This is the least closed convex cone containing the comparisons. -/
theorem cone_le_iff (comparisons : Index → IncentiveComparison Outcome)
    (C : ProperCone ℝ (EuclideanSpace ℝ Outcome)) :
    cone comparisons ≤ C ↔ ∀ index, (comparisons index).difference ∈ C := by
  refine ⟨fun below index => below (difference_mem_cone comparisons index), ?_⟩
  intro contains
  have included : Set.range (fun index => (comparisons index).difference) ⊆ C := by
    rintro _ ⟨index, rfl⟩
    exact contains index
  have dual := ProperCone.innerDual_le_innerDual included
  have doubleDual := ProperCone.innerDual_le_innerDual dual
  simpa only [cone, ProperCone.innerDual_innerDual] using doubleDual

/-- **Exact, utility-independent implication** of one target incentive
constraint by a family of source constraints. -/
theorem mem_cone_iff (comparisons : Index → IncentiveComparison Outcome)
    (target : IncentiveComparison Outcome) :
    target.difference ∈ cone comparisons ↔
      ∀ utility, (∀ index, (comparisons index).Holds utility) → target.Holds utility := by
  constructor
  · intro included utility respected
    rw [holds_iff_inner, real_inner_comm]
    apply included
    rintro _ ⟨index, rfl⟩
    exact ((comparisons index).holds_iff_inner utility).mp (respected index)
  · intro preserves utility respected
    have each (index : Index) : (comparisons index).Holds (WithLp.ofLp utility) := by
      rw [holds_iff_inner]
      exact respected ⟨index, rfl⟩
    change 0 ≤ ⟪utility, target.difference⟫
    rw [real_inner_comm]
    exact (target.holds_iff_inner _).mp (preserves _ each)

/-- A failed cone inclusion supplies a separating utility. -/
theorem separating_utility (comparisons : Index → IncentiveComparison Outcome)
    (target : IncentiveComparison Outcome) (outside : target.difference ∉ cone comparisons) :
    ∃ utility, (∀ index, (comparisons index).Holds utility) ∧
      expect target.prescribed utility <
        expect target.alternative utility := by
  rw [mem_cone_iff] at outside
  push Not at outside
  obtain ⟨utility, respected, fails⟩ := outside
  exact ⟨utility, respected, not_le.mp fun hle => fails ((holds_iff _ _).2 hle)⟩

/-- Finite nonnegative combinations give checkable sufficient certificates;
the coefficients need not sum to one. -/
theorem mem_cone_of_nonnegative_combination
    (comparisons : Index → IncentiveComparison Outcome) (target : IncentiveComparison Outcome)
    {Terms : Type w} (terms : Finset Terms) (index : Terms → Index) (weight : Terms → ℝ)
    (nonnegative : ∀ term ∈ terms, 0 ≤ weight term)
    (represents : target.difference = ∑ term ∈ terms,
      weight term • (comparisons (index term)).difference) :
    target.difference ∈ cone comparisons := by
  rw [represents]
  apply (cone comparisons).sum_mem
  intro term member
  exact (cone comparisons).smul_mem (difference_mem_cone comparisons (index term))
    (nonnegative term member)

section UtilitySubspace

variable (utilities : Submodule ℝ (EuclideanSpace ℝ Outcome))

/-- The least closed convex cone containing the source incentive differences,
after projecting onto the specified class of utilities. -/
def coneWithin (comparisons : Index → IncentiveComparison Outcome) :
    ProperCone ℝ utilities :=
  ProperCone.innerDual (ProperCone.innerDual (Set.range fun index =>
    utilities.orthogonalProjectionOnto (comparisons index).difference) : Set utilities)

theorem projected_difference_mem_coneWithin
    (comparisons : Index → IncentiveComparison Outcome) (index : Index) :
    utilities.orthogonalProjectionOnto (comparisons index).difference ∈
      coneWithin utilities comparisons := by
  intro utility nonnegative
  change 0 ≤ ⟪utility, utilities.orthogonalProjectionOnto (comparisons index).difference⟫
  rw [real_inner_comm]
  exact nonnegative ⟨index, rfl⟩

theorem coneWithin_le_iff (comparisons : Index → IncentiveComparison Outcome)
    (C : ProperCone ℝ utilities) :
    coneWithin utilities comparisons ≤ C ↔
      ∀ index, utilities.orthogonalProjectionOnto (comparisons index).difference ∈ C := by
  refine ⟨fun below index =>
    below (projected_difference_mem_coneWithin utilities comparisons index), ?_⟩
  intro contains
  have included : Set.range (fun index =>
      utilities.orthogonalProjectionOnto (comparisons index).difference) ⊆ C := by
    rintro _ ⟨index, rfl⟩
    exact contains index
  have dual := ProperCone.innerDual_le_innerDual included
  have doubleDual := ProperCone.innerDual_le_innerDual dual
  simpa only [coneWithin, ProperCone.innerDual_innerDual] using doubleDual

/-- Projection preserves exactly the incentive margin of every utility in the
subspace. -/
theorem inner_projected_difference (comparison : IncentiveComparison Outcome)
    (utility : utilities) :
    ⟪utilities.orthogonalProjectionOnto comparison.difference, utility⟫ =
      expect comparison.prescribed (WithLp.ofLp utility.val) -
        expect comparison.alternative (WithLp.ofLp utility.val) := by
  rw [utilities.inner_orthogonalProjectionOnto_eq_of_mem_right]
  exact comparison.inner_difference (WithLp.ofLp utility.val)

theorem holds_iff_inner_projected (comparison : IncentiveComparison Outcome)
    (utility : utilities) :
    comparison.Holds (WithLp.ofLp utility.val) ↔
      0 ≤ ⟪utilities.orthogonalProjectionOnto comparison.difference, utility⟫ := by
  rw [holds_iff, inner_projected_difference, sub_nonneg]

/-- **Exact incentive implication for every utility in a linear subspace.** -/
theorem mem_coneWithin_iff (comparisons : Index → IncentiveComparison Outcome)
    (target : IncentiveComparison Outcome) :
    utilities.orthogonalProjectionOnto target.difference ∈ coneWithin utilities comparisons ↔
      ∀ utility : utilities,
        (∀ index, (comparisons index).Holds (WithLp.ofLp utility.val)) →
          target.Holds (WithLp.ofLp utility.val) := by
  constructor
  · intro included utility respected
    rw [holds_iff_inner_projected, real_inner_comm]
    apply included
    rintro _ ⟨index, rfl⟩
    exact ((comparisons index).holds_iff_inner_projected utilities utility).1 (respected index)
  · intro preserves utility respected
    have each (index : Index) : (comparisons index).Holds (WithLp.ofLp utility.val) :=
      ((comparisons index).holds_iff_inner_projected utilities utility).2
        (respected ⟨index, rfl⟩)
    change 0 ≤ ⟪utility, utilities.orthogonalProjectionOnto target.difference⟫
    rw [real_inner_comm]
    exact (target.holds_iff_inner_projected utilities utility).1 (preserves utility each)

/-- Failure of projected cone inclusion supplies a counterexample utility within
the class. -/
theorem separating_utilityWithin (comparisons : Index → IncentiveComparison Outcome)
    (target : IncentiveComparison Outcome)
    (outside : utilities.orthogonalProjectionOnto target.difference ∉
      coneWithin utilities comparisons) :
    ∃ utility : utilities,
      (∀ index, (comparisons index).Holds (WithLp.ofLp utility.val)) ∧
        ¬ target.Holds (WithLp.ofLp utility.val) := by
  rw [mem_coneWithin_iff] at outside
  push Not at outside
  exact outside

/-- Projected differences agree exactly when every utility in the subspace
assigns the two comparisons the same margin. -/
theorem projected_difference_eq_iff (first second : IncentiveComparison Outcome) :
    utilities.orthogonalProjectionOnto first.difference =
        utilities.orthogonalProjectionOnto second.difference ↔
      ∀ utility : utilities,
        expect first.prescribed (WithLp.ofLp utility.val) -
            expect first.alternative (WithLp.ofLp utility.val) =
          expect second.prescribed (WithLp.ofLp utility.val) -
            expect second.alternative (WithLp.ofLp utility.val) := by
  constructor
  · intro same utility
    rw [← inner_projected_difference utilities first utility,
      ← inner_projected_difference utilities second utility, same]
  · intro same
    apply ext_inner_right ℝ
    intro utility
    rw [inner_projected_difference, inner_projected_difference]
    exact same utility

/-- **A projected certificate bounds regret in the original game.** Only the
utility component outside the retained subspace contributes to the bound; the
source comparisons must hold for the full utility, not its projection. -/
theorem regret_le_norm_comparison_residual
    (comparisons : Index → IncentiveComparison Outcome) (target : IncentiveComparison Outcome)
    {Terms : Type w} (terms : Finset Terms) (index : Terms → Index) (weight : Terms → ℝ)
    (nonnegative : ∀ term ∈ terms, 0 ≤ weight term)
    (represents : utilities.orthogonalProjectionOnto target.difference =
      ∑ term ∈ terms,
        weight term • utilities.orthogonalProjectionOnto (comparisons (index term)).difference)
    (utility : Outcome → ℝ)
    (respected : ∀ term ∈ terms, (comparisons (index term)).Holds utility) :
    expect target.alternative utility -
        expect target.prescribed utility ≤
      ‖target.difference - ∑ term ∈ terms,
        weight term • (comparisons (index term)).difference‖ *
      ‖WithLp.toLp 2 utility -
        (utilities.orthogonalProjectionOnto (WithLp.toLp 2 utility)).val‖ := by
  let vector : EuclideanSpace ℝ Outcome := WithLp.toLp 2 utility
  let combination : EuclideanSpace ℝ Outcome :=
    ∑ term ∈ terms, weight term • (comparisons (index term)).difference
  let residual := target.difference - combination
  have projected_zero : utilities.orthogonalProjectionOnto residual = 0 := by
    simp only [residual, combination, map_sub, map_sum, map_smul, represents, sub_self]
  have orthogonal :
      ⟪residual, (utilities.orthogonalProjectionOnto vector).val⟫ = 0 := by
    rw [← utilities.inner_orthogonalProjectionOnto_eq_of_mem_right,
      projected_zero, inner_zero_left]
  have discards :
      ⟪residual, vector - (utilities.orthogonalProjectionOnto vector).val⟫ =
        ⟪residual, vector⟫ := by
    rw [inner_sub_right, orthogonal, sub_zero]
  have combination_nonnegative : 0 ≤ ⟪combination, vector⟫ := by
    simp only [combination, sum_inner, real_inner_smul_left]
    apply Finset.sum_nonneg
    intro term member
    exact mul_nonneg (nonnegative term member)
      (((comparisons (index term)).holds_iff_inner utility).mp (respected term member))
  have lower := (abs_le.mp (abs_real_inner_le_norm residual
    (vector - (utilities.orthogonalProjectionOnto vector).val))).1
  have residual_margin : ⟪residual, vector⟫ =
      expect target.prescribed utility -
        expect target.alternative utility -
          ⟪combination, vector⟫ := by
    change ⟪target.difference - combination, vector⟫ = _
    rw [inner_sub_left, target.inner_difference utility]
  rw [discards, residual_margin] at lower
  change _ ≤ ‖residual‖ * ‖vector - (utilities.orthogonalProjectionOnto vector).val‖
  linarith

end UtilitySubspace

/-- The orthogonal complement of the span of comparison errors is precisely the
largest utility subspace on which all the prescribed margins are unchanged. -/
theorem mem_comparison_error_orthogonal_iff
    (first second : Index → IncentiveComparison Outcome) (utility : Outcome → ℝ) :
    WithLp.toLp 2 utility ∈
        (Submodule.span ℝ (Set.range fun index =>
          (first index).difference - (second index).difference))ᗮ ↔
      ∀ index, ⟪(first index).difference, WithLp.toLp 2 utility⟫ =
        ⟪(second index).difference, WithLp.toLp 2 utility⟫ := by
  rw [Submodule.mem_orthogonal]
  constructor
  · intro vanishes index
    have atError := vanishes ((first index).difference - (second index).difference)
      (Submodule.subset_span ⟨index, rfl⟩)
    rwa [inner_sub_left, sub_eq_zero] at atError
  · intro same vector member
    induction member using Submodule.span_induction with
    | mem vector member =>
      obtain ⟨index, rfl⟩ := member
      rw [inner_sub_left, same index, sub_self]
    | zero => exact inner_zero_left _
    | add left right _ _ leftZero rightZero =>
      rw [inner_add_left, leftZero, rightZero, add_zero]
    | smul scalar vector _ vanishes =>
      rw [real_inner_smul_left, vanishes, mul_zero]

/-! ## Families indexed by deviating units -/

section Families

variable {ι : Type v} {Source : ι → Type us} {Target : ι → Type ut}

/-- **Playerwise cone criterion.** Every utility profile respecting all source
comparisons respects all target comparisons exactly when each target
difference lies in the cone of the same unit's source differences. Other
units' payoffs cannot help: they can be set to zero. -/
theorem forall_holds_imp_iff_cone [DecidableEq ι]
    (source : (who : ι) → Source who → IncentiveComparison Outcome)
    (target : (who : ι) → Target who → IncentiveComparison Outcome) :
    (∀ utility : Outcome → ι → ℝ,
        (∀ who deviation, (source who deviation).Holds (utility · who)) →
          ∀ who deviation, (target who deviation).Holds (utility · who)) ↔
      ∀ who deviation, (target who deviation).difference ∈ cone (source who) := by
  constructor
  · intro preserves who deviation
    rw [mem_cone_iff]
    intro utility respected
    let utilities : Outcome → ι → ℝ := fun outcome player =>
      if player = who then utility outcome else 0
    have hsource : ∀ player replacement,
        (source player replacement).Holds (utilities · player) := by
      intro player replacement
      by_cases same : player = who
      · subst player
        simpa only [utilities, ↓reduceIte] using respected replacement
      · simpa only [utilities, same, ↓reduceIte] using (source player replacement).holds_zero
    simpa only [utilities, ↓reduceIte] using preserves utilities hsource who deviation
  · intro included utility respected who deviation
    exact (mem_cone_iff _ _).mp (included who deviation) (utility · who) (respected who)

/-- Place a comparison in the joint outcome space of one deviating unit. -/
def tag (who : ι) (comparison : IncentiveComparison Outcome) :
    IncentiveComparison (ι × Outcome) where
  prescribed := comparison.prescribed.map fun outcome => (who, outcome)
  alternative := comparison.alternative.map fun outcome => (who, outcome)

omit [Fintype Outcome] in
theorem tag_holds_iff (who : ι) (comparison : IncentiveComparison Outcome)
    (utility : ι × Outcome → ℝ) :
    (comparison.tag who).Holds utility ↔ comparison.Holds fun outcome => utility (who, outcome) :=
  holds_map_iff _ comparison.prescribed comparison.alternative utility

/-- **Cone criterion for coupled utility classes.** For a linear class of joint
utilities on unit-tagged outcomes, preservation is exactly inclusion of each
projected tagged target difference in the projected cone of all tagged source
differences. -/
theorem forall_holds_imp_iff_coneWithin [Fintype ι]
    (utilities : Submodule ℝ (EuclideanSpace ℝ (ι × Outcome)))
    (source : (who : ι) → Source who → IncentiveComparison Outcome)
    (target : (who : ι) → Target who → IncentiveComparison Outcome) :
    (∀ utility : utilities,
        (∀ who deviation,
          (source who deviation).Holds fun outcome => WithLp.ofLp utility.val (who, outcome)) →
          ∀ who deviation,
            (target who deviation).Holds fun outcome => WithLp.ofLp utility.val (who, outcome)) ↔
      ∀ deviation : Σ who, Target who,
        utilities.orthogonalProjectionOnto
            ((target deviation.1 deviation.2).tag deviation.1).difference ∈
          coneWithin utilities fun deviation : Σ who, Source who =>
            (source deviation.1 deviation.2).tag deviation.1 := by
  simp only [mem_coneWithin_iff, tag_holds_iff, Sigma.forall]
  exact ⟨fun preserves who deviation utility respected =>
      preserves utility respected who deviation,
    fun included utility respected who deviation =>
      included who deviation utility respected⟩

end Families

end IncentiveComparison

/-! ## Equilibrium predicates as comparison families -/

section Equilibrium

variable {ι : Type u} [DecidableEq ι] {Deviator : Type v} {Observation : Type w}

/-- The comparison behind one deviation from a status quo, as seen through an
observation of outcomes. -/
def equilibriumComparison (F : GameForm ι) (statusQuo : PMF (Profile F.sig))
    (D : DeviationScheme F.sig Deviator) (observe : F.sig.Outcome → Observation)
    (who : Deviator) (deviation : D.Dev who) : IncentiveComparison Observation where
  prescribed := (F.outcomeLaw statusQuo).map observe
  alternative := (F.outcomeLaw (D.apply statusQuo who deviation)).map observe

/-- An expected-utility equilibrium of observed payoffs is its comparison
family. No finiteness is needed. -/
theorem isEquilibrium_iff_holds (F : GameForm ι) (statusQuo : PMF (Profile F.sig))
    (D : DeviationScheme F.sig Deviator) (observe : F.sig.Outcome → Observation)
    (utility : Observation → Deviator → ℝ) :
    IsEquilibrium F (euPreference fun outcome who => utility (observe outcome) who)
        statusQuo D ↔
      ∀ who deviation,
        (equilibriumComparison F statusQuo D observe who deviation).Holds (utility · who) := by
  refine forall_congr' fun who => forall_congr' fun deviation => ?_
  rw [IncentiveComparison.euPreference_iff_holds, equilibriumComparison,
    IncentiveComparison.holds_map_iff]
  rfl

/-- **Exact equilibrium transfer for every utility.** For any two games,
status quos, and deviation schemes over the same deviating units and a finite
observation carrier, every observed-utility equilibrium of the source is one of
the target exactly when each target deviation's incentive difference lies in
the cone of the same unit's source differences. This covers Nash, coarse
correlated, and correlated equilibrium alike. -/
theorem isEquilibrium_preservation_iff_cone [DecidableEq Deviator] [Fintype Observation]
    {ι' : Type u} [DecidableEq ι'] (F : GameForm ι) (F' : GameForm ι')
    (statusQuo : PMF (Profile F.sig)) (statusQuo' : PMF (Profile F'.sig))
    (D : DeviationScheme F.sig Deviator) (D' : DeviationScheme F'.sig Deviator)
    (observe : F.sig.Outcome → Observation) (observe' : F'.sig.Outcome → Observation) :
    (∀ utility : Observation → Deviator → ℝ,
      IsEquilibrium F (euPreference fun outcome who => utility (observe outcome) who)
          statusQuo D →
        IsEquilibrium F' (euPreference fun outcome who => utility (observe' outcome) who)
          statusQuo' D') ↔
      ∀ who deviation,
        (equilibriumComparison F' statusQuo' D' observe' who deviation).difference ∈
          IncentiveComparison.cone (equilibriumComparison F statusQuo D observe who) := by
  simp only [isEquilibrium_iff_holds]
  exact IncentiveComparison.forall_holds_imp_iff_cone _ _

end Equilibrium

end GameTheory
