module

/-
# Shared-resource feasible choice

Opponent-dependent menus satisfy the simultaneous feasible-choice theorem
and recover the native guarded quantity judgments.
-/

public import GameTheory.Analysis.FeasibleChoiceFixedPoint
public import GameTheory.Experimental.Exp182.SharedCapacity
public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Topology.Order.Compact
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

@[expose] public section

noncomputable section

namespace GameTheory.Tests.FeasibleMenus

open Set Filter Topology
open GameTheory.Experimental

def outer (_player : Bool) : Set ℝ := Icc 0 1

abbrev Domain := {profile : Bool → ℝ // profile ∈ Set.pi Set.univ outer}

def capacity (player : Bool) (profile : Domain) : ℝ := 1 - profile.val (!player)

def feasible (player : Bool) (profile : Domain) : Set ℝ := Icc 0 (capacity player profile)

def score (_player : Bool) (point : Domain × ℝ) : ℝ := point.2

theorem outer_convex (player : Bool) : Convex ℝ (outer player) := convex_Icc 0 1

theorem outer_compact (player : Bool) : IsCompact (outer player) := isCompact_Icc

theorem outer_nonempty (player : Bool) : (outer player).Nonempty :=
  ⟨0, by norm_num [outer]⟩

theorem capacity_nonnegative (player : Bool) (profile : Domain) :
    0 ≤ capacity player profile := by
  have upper := (profile.property (!player) (Set.mem_univ _)).2
  exact sub_nonneg.mpr upper

theorem capacity_le_one (player : Bool) (profile : Domain) : capacity player profile ≤ 1 := by
  have lower := (profile.property (!player) (Set.mem_univ _)).1
  dsimp [capacity]
  linarith

theorem capacity_continuous (player : Bool) : Continuous (capacity player) :=
  continuous_const.sub ((continuous_apply (!player)).comp continuous_subtype_val)

theorem feasible_subset (player : Bool) (profile : Domain) :
    feasible player profile ⊆ outer player :=
  fun _ offered => ⟨offered.1, offered.2.trans (capacity_le_one player profile)⟩

theorem feasible_nonempty (player : Bool) (profile : Domain) :
    (feasible player profile).Nonempty :=
  ⟨0, le_rfl, capacity_nonnegative player profile⟩

theorem feasible_convex (player : Bool) (profile : Domain) :
    Convex ℝ (feasible player profile) := convex_Icc 0 _

theorem feasible_graph_closed (player : Bool) :
    IsClosed {point : Domain × ℝ | point.2 ∈ feasible player point.1} := by
  have nonnegative : IsClosed {point : Domain × ℝ | 0 ≤ point.2} :=
    isClosed_le continuous_const continuous_snd
  have capped : IsClosed {point : Domain × ℝ | point.2 ≤ capacity player point.1} :=
    isClosed_le continuous_snd ((capacity_continuous player).comp continuous_fst)
  exact nonnegative.inter capped

/-- The opposite player's quantity determines the cap. Clipping at its new
value recovers every limiting feasible alternative continuously. -/
theorem feasible_lowerHemicontinuous (player : Bool) :
    LowerHemicontinuous (feasible player) := by
  intro profile
  apply (lowerHemicontinuousAt_iff (f := feasible player) (x := profile)).mpr
  rintro openSet isOpenSet ⟨quantity, offered, inOpen⟩
  have recovery : Continuous (fun next : Domain => min quantity (capacity player next)) :=
    continuous_const.min (capacity_continuous player)
  have atCurrent : min quantity (capacity player profile) = quantity := min_eq_left offered.2
  have inOpenCurrent : min quantity (capacity player profile) ∈ openSet := by
    rwa [atCurrent]
  filter_upwards [(recovery.tendsto profile).eventually
    (isOpenSet.mem_nhds inOpenCurrent)] with next inOpenNext
  exact ⟨min quantity (capacity player next),
    ⟨le_min offered.1 (capacity_nonnegative player next), min_le_right _ _⟩, inOpenNext⟩

theorem score_continuous (player : Bool) : Continuous (score player) := continuous_snd

theorem score_quasiconcave (player : Bool) (profile : Domain) :
    QuasiconcaveOn ℝ (feasible player profile) (fun quantity => score player (profile, quantity)) :=
  (concaveOn_id (feasible_convex player profile)).quasiconcaveOn

def half : Domain :=
  ⟨fun _ => 1 / 2, by intro player _; norm_num [outer]⟩

theorem half_optimal (player : Bool) :
    half.val player ∈ feasible player half ∧
      IsMaxOn (fun quantity => score player (half, quantity)) (feasible player half)
        (half.val player) := by
  refine ⟨by norm_num [half, feasible, capacity], ?_⟩
  intro quantity offered
  have upper := offered.2
  norm_num [score, half, capacity] at upper ⊢
  exact upper

/-- Every simultaneous feasible maximizer exhausts the shared resource.
This concerns feasible local comparisons rather than unrestricted Nash. -/
theorem optimal_profile_sum_one (profile : Domain)
    (optimal : ∀ player, profile.val player ∈ feasible player profile ∧
      IsMaxOn (fun quantity => score player (profile, quantity))
        (feasible player profile) (profile.val player)) :
    profile.val false + profile.val true = 1 := by
  have upper := (optimal false).1.2
  have lower := (isMaxOn_iff.mp (optimal false).2) (capacity false profile)
    ⟨capacity_nonnegative false profile, le_rfl⟩
  change profile.val false ≤ 1 - profile.val true at upper
  change 1 - profile.val true ≤ profile.val false at lower
  linarith

/-- The common fixed-point theorem constructs a simultaneous affordable
optimum for arbitrary continuous quasiconcave objectives on these changing
menus. The parameter stays fixed during comparison. -/
theorem exists_feasible_maximizers_for (objective : Bool → Domain × ℝ → ℝ)
    (continuous_objective : ∀ player, Continuous (objective player))
    (quasiconcave_objective : ∀ player profile,
      QuasiconcaveOn ℝ (feasible player profile)
        (fun quantity => objective player (profile, quantity))) :
    ∃ profile : Domain, ∀ player,
      profile.val player ∈ feasible player profile ∧
        IsMaxOn (fun quantity => objective player (profile, quantity))
          (feasible player profile) (profile.val player) :=
  exists_feasibleChoice_fixedPoint outer outer_convex outer_compact outer_nonempty
    feasible feasible_subset feasible_graph_closed feasible_lowerHemicontinuous feasible_nonempty
    objective continuous_objective quasiconcave_objective

/-- Own-quantity objectives instantiate the changing-menu family without a
summed interpersonal objective. -/
theorem exists_optimal : ∃ profile : Domain, ∀ player,
    profile.val player ∈ feasible player profile ∧
      IsMaxOn (fun quantity => score player (profile, quantity))
        (feasible player profile) (profile.val player) :=
  exists_feasible_maximizers_for score score_continuous score_quasiconcave

/-- The analytic point provides the same interval-valued strategies as the
canonical deterministic game, with their actual bounds attached. -/
def toProfile (profile : Domain) : Profile SharedCapacity.signature :=
  fun player => ⟨profile.val player, profile.property player (Set.mem_univ player)⟩

theorem affordable_iff_feasible (profile : Domain) (player : Bool)
    (alternative : SharedCapacity.Qty) :
    SharedCapacity.affordable player (toProfile profile) alternative ↔
      alternative.val ∈ feasible player profile := by
  change alternative.val + profile.val (!player) ≤ 1 ↔
    0 ≤ alternative.val ∧ alternative.val ≤ 1 - profile.val (!player)
  constructor
  · intro affordable
    exact ⟨alternative.property.1, by linarith⟩
  · intro offered
    linarith [offered.2]

/-- Feasible maximizer membership is exactly the admissibility and comparison
needed by the native guarded local judgment. -/
theorem optimal_to_local (profile : Domain)
    (optimal : ∀ player, profile.val player ∈ feasible player profile ∧
      IsMaxOn (fun quantity => score player (profile, quantity))
        (feasible player profile) (profile.val player)) :
    SharedCapacity.localOptimal (toProfile profile) := by
  intro player
  refine ⟨(affordable_iff_feasible profile player _).mpr (optimal player).1,
    fun _ offered => offered, ?_⟩
  intro alternative affordable
  exact (isMaxOn_iff.mp (optimal player).2) alternative.val
    ((affordable_iff_feasible profile player alternative).mp affordable)

/-- The existence theorem reaches a canonical strategy profile that satisfies
the coupled judgments, while ordinary-Nash filtering rejects every such point. -/
theorem exists_local_optimum_not_ordinary_nash :
    ∃ profile : Profile SharedCapacity.signature,
      SharedCapacity.localOptimal profile ∧ SharedCapacity.sharedFeasible profile ∧
        ¬ IsNash SharedCapacity.form (euPreference SharedCapacity.utility) profile := by
  obtain ⟨profile, optimal⟩ := exists_optimal
  have local_optimal := optimal_to_local profile optimal
  have feasible := SharedCapacity.localOptimal_sharedFeasible local_optimal
  exact ⟨toProfile profile, local_optimal, feasible,
    fun nash => SharedCapacity.no_feasible_ordinary_nash ⟨toProfile profile, nash, feasible⟩⟩

/-! Continuous scores alone do not make the maximizing set convex. -/

def squareMaximizers : Set ℝ :=
  {quantity | quantity ∈ Icc (-1) 1 ∧ IsMaxOn (fun alternative => alternative ^ 2)
    (Icc (-1) 1) quantity}

theorem square_score_continuous : Continuous (fun quantity : ℝ => quantity ^ 2) :=
  continuous_id.pow 2

theorem square_endpoint_maximizes (endpoint : ℝ) (boundary : endpoint = -1 ∨ endpoint = 1) :
    endpoint ∈ squareMaximizers := by
  rcases boundary with rfl | rfl
  all_goals
    refine ⟨by norm_num, ?_⟩
    intro quantity offered
    have bound : quantity ^ 2 ≤ 1 :=
      (sq_le_one_iff_abs_le_one quantity).mpr (abs_le.mpr offered)
    simpa using bound

theorem square_maximizers_not_convex : ¬ Convex ℝ squareMaximizers := by
  intro convex
  have midpoint := convex (square_endpoint_maximizes (-1) (Or.inl rfl))
    (square_endpoint_maximizes 1 (Or.inr rfl))
    (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have zero : (0 : ℝ) ∈ squareMaximizers := by
    convert midpoint using 1
    norm_num
  have bound := (isMaxOn_iff.mp zero.2) 1 (by norm_num)
  norm_num at bound

end GameTheory.Tests.FeasibleMenus
