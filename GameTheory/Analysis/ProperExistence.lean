module

/-
# Existence of proper equilibria

Payoff-ranked response lotteries satisfy the relative error inequalities on a
compact product of strictly positive simplices. Their correspondence has a
closed graph even at payoff ties. A fixed point gives an epsilon-proper
profile; finite-law compactness supplies a proper limit as epsilon vanishes.
-/

public import GameTheory.Analysis.Proper
public import GameTheory.Analysis.Nash
public import GameTheory.Math.Probability.Compactness
public import GameTheory.Math.Probability.GeometricRanking

@[expose] public section

noncomputable section

namespace GameTheory.GameForm

open Filter GameTheory.Math.Probability
open scoped BigOperators

variable {ι : Type*} (F : GameForm ι)
    [∀ i, Fintype (F.sig.Strategy i)]

private def ratioFloor (epsilon : ℝ) (i : ι) : ℝ :=
  epsilon ^ Fintype.card (F.sig.Strategy i) / (Fintype.card (F.sig.Strategy i) : ℝ)

private def ratioDomain (epsilon : ℝ) : Set (Profile F.sig.weights) :=
  mixedPolytope F.sig ∩ {x | ∀ i a, ratioFloor F epsilon i ≤ x i a}

private theorem convex_ratioDomain (epsilon : ℝ) : Convex ℝ (ratioDomain F epsilon) := by
  intro x hx y hy a b ha hb hab
  refine ⟨convex_mixedPolytope F.sig hx.1 hy.1 ha hb hab, ?_⟩
  intro i action
  change ratioFloor F epsilon i ≤ a * x i action + b * y i action
  calc
    ratioFloor F epsilon i = a * ratioFloor F epsilon i + b * ratioFloor F epsilon i := by
      rw [← add_mul, hab, one_mul]
    _ ≤ a * x i action + b * y i action :=
      add_le_add (mul_le_mul_of_nonneg_left (hx.2 i action) ha)
        (mul_le_mul_of_nonneg_left (hy.2 i action) hb)

private theorem isClosed_ratioBounds (epsilon : ℝ) :
    IsClosed {x : Profile F.sig.weights | ∀ i a, ratioFloor F epsilon i ≤ x i a} := by
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_iInter fun a =>
    isClosed_le continuous_const ((continuous_apply a).comp (continuous_apply i))

private theorem isCompact_ratioDomain (epsilon : ℝ) : IsCompact (ratioDomain F epsilon) :=
  (isCompact_mixedPolytope F.sig).inter_right (isClosed_ratioBounds F epsilon)

private theorem isClosed_ratioDomain (epsilon : ℝ) : IsClosed (ratioDomain F epsilon) :=
  (isCompact_ratioDomain F epsilon).isClosed

variable [Fintype ι] [DecidableEq ι]

private def actionScore (utility : F.sig.Outcome → ι → ℝ)
    (x : Profile F.sig.weights) (i : ι) (action : F.sig.Strategy i) : ℝ :=
  payoff F utility i (Profile.update x i fun other => ((PMF.pure action) other).toReal)

private theorem continuous_actionScore (utility : F.sig.Outcome → ι → ℝ)
    (i : ι) (action : F.sig.Strategy i) :
    Continuous (fun x => actionScore F utility x i action) :=
  (continuous_payoff i).comp
    (continuous_update_profile i (fun other => ((PMF.pure action) other).toReal))

private def ratioReplies (utility : F.sig.Outcome → ι → ℝ) (epsilon : ℝ)
    (x : ratioDomain F epsilon) : Set (Profile F.sig.weights) :=
  ratioDomain F epsilon ∩ {y | ∀ i a b,
    actionScore F utility x.1 i a < actionScore F utility x.1 i b →
      y i a ≤ epsilon * y i b}

private theorem convex_ratioReplies (utility : F.sig.Outcome → ι → ℝ) (epsilon : ℝ)
    (x : ratioDomain F epsilon) : Convex ℝ (ratioReplies F utility epsilon x) := by
  intro y hy z hz a b ha hb hab
  refine ⟨convex_ratioDomain F epsilon hy.1 hz.1 ha hb hab, ?_⟩
  intro i worse better strict
  change a * y i worse + b * z i worse ≤ epsilon * (a * y i better + b * z i better)
  calc
    a * y i worse + b * z i worse ≤
        a * (epsilon * y i better) + b * (epsilon * z i better) :=
      add_le_add (mul_le_mul_of_nonneg_left (hy.2 i worse better strict) ha)
        (mul_le_mul_of_nonneg_left (hz.2 i worse better strict) hb)
    _ = epsilon * (a * y i better + b * z i better) := by ring

private theorem closedGraph_ratioReplies (utility : F.sig.Outcome → ι → ℝ) (epsilon : ℝ) :
    closedGraph (ratioReplies F utility epsilon) := by
  show IsClosed _
  have graph : {z : ratioDomain F epsilon × Profile F.sig.weights |
        z.2 ∈ ratioReplies F utility epsilon z.1} =
      {z | z.2 ∈ ratioDomain F epsilon} ∩
        ⋂ i, ⋂ a, ⋂ b,
          ({z | actionScore F utility z.1.1 i b ≤ actionScore F utility z.1.1 i a} ∪
            {z | z.2 i a ≤ epsilon * z.2 i b}) := by
    ext z
    simp only [ratioReplies, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter,
      Set.mem_union, imp_iff_not_or, not_lt]
  rw [graph]
  refine ((isClosed_ratioDomain F epsilon).preimage continuous_snd).inter
    (isClosed_iInter fun i => isClosed_iInter fun a => isClosed_iInter fun b => ?_)
  have scoreContinuous (i : ι) (action : F.sig.Strategy i) :
      Continuous (fun z : ratioDomain F epsilon × Profile F.sig.weights =>
        actionScore F utility z.1.1 i action) :=
    (continuous_actionScore F utility i action).comp
      (continuous_subtype_val.comp continuous_fst)
  refine (isClosed_le (scoreContinuous i b) (scoreContinuous i a)).union ?_
  have coordinateContinuous (action : F.sig.Strategy i) :
      Continuous (fun z : ratioDomain F epsilon × Profile F.sig.weights => z.2 i action) :=
    (continuous_apply action).comp ((continuous_apply i).comp continuous_snd)
  exact isClosed_le (coordinateContinuous a) ((coordinateContinuous b).const_mul epsilon)

private theorem actionScore_probs (utility : F.sig.Outcome → ι → ℝ)
    (integrable : F.HasIntegrableUtility utility) (profile : Profile F.sig.mixed)
    (i : ι) (action : F.sig.Strategy i) :
    actionScore F utility (probs F.sig profile) i action =
      expectedUtility utility i (F.mixed.play (Profile.update profile i (PMF.pure action))) := by
  unfold actionScore
  rw [← probs_update, payoff_probs integrable]

private theorem ratioReplies_nonempty [∀ i, Nonempty (F.sig.Strategy i)]
    (utility : F.sig.Outcome → ι → ℝ) (epsilon : ℝ) (positive : 0 < epsilon)
    (small : epsilon ≤ 1) (x : ratioDomain F epsilon) :
    (ratioReplies F utility epsilon x).Nonempty := by
  choose weights simplex lower ratios using fun i =>
    exists_simplexWeights_geometric_ranking (actionScore F utility x.1 i) epsilon positive small
  refine ⟨weights, ⟨(mem_mixedPolytope F.sig).mpr simplex, lower⟩, ratios⟩

omit [∀ i, Fintype (F.sig.Strategy i)] in
/-- Epsilon-proper profiles exist for every positive ratio below one in a
finite game. Only actual pure-play integrability is needed for stochastic
outcomes, whose carrier need not be finite. -/
theorem exists_isεProper [∀ i, Finite (F.sig.Strategy i)]
    [∀ i, Nonempty (F.sig.Strategy i)]
    (utility : F.sig.Outcome → ι → ℝ) (integrable : F.HasIntegrableUtility utility)
    (epsilon : ℝ) (positive : 0 < epsilon) (small : epsilon < 1) :
    ∃ profile : Profile F.sig.mixed, F.IsεProper utility epsilon profile := by
  classical
  let _ : ∀ i, Fintype (F.sig.Strategy i) := fun _ => Fintype.ofFinite _
  have domainNonempty : (ratioDomain F epsilon).Nonempty := by
    choose weights simplex lower _ using fun i : ι =>
      exists_simplexWeights_geometric_ranking (fun _ : F.sig.Strategy i => (0 : ℝ))
        epsilon positive small.le
    exact ⟨weights, (mem_mixedPolytope F.sig).mpr simplex, lower⟩
  obtain ⟨x, fixed⟩ := kakutani_fixed_point (ratioDomain F epsilon)
    (convex_ratioDomain F epsilon) (isCompact_ratioDomain F epsilon) domainNonempty
    (ratioReplies F utility epsilon) (closedGraph_ratioReplies F utility epsilon)
    (fun x => ⟨fun _ member => member.1, convex_ratioReplies F utility epsilon x,
      ratioReplies_nonempty F utility epsilon positive small.le x⟩)
  let profile : Profile F.sig.mixed := ofPolytope F.sig x.2.1
  have weights : probs F.sig profile = x.1 := probs_ofPolytope F.sig x.2.1
  have probability (i : ι) (action : F.sig.Strategy i) :
      (profile i action).toReal = x.1 i action := by
    exact congrFun (congrFun weights i) action
  refine ⟨profile, positive, ?_, ?_, ?_⟩
  · intro i action
    have lowerPositive : 0 < ratioFloor F epsilon i := by
      unfold ratioFloor
      exact div_pos (pow_pos positive _) (Nat.cast_pos.mpr Fintype.card_pos)
    have positiveMass : 0 < (profile i action).toReal := by
      rw [probability]
      exact lowerPositive.trans_le (x.2.2 i action)
    exact (profile i).mem_support_iff action |>.mpr
      (ne_of_gt (ENNReal.toReal_pos_iff.mp positiveMass).1)
  · intro i action
    exact integrable.mixed_of_finite i (Profile.update profile i (PMF.pure action))
  · intro i worse better strict
    have scoreStrict : actionScore F utility x.1 i worse < actionScore F utility x.1 i better := by
      rw [← weights, actionScore_probs F utility integrable,
        actionScore_probs F utility integrable]
      exact strict
    rw [probability, probability]
    exact fixed.2 i worse better scoreStrict

omit [∀ i, Fintype (F.sig.Strategy i)] in
/-- **Myerson's existence theorem.** Every game with finitely many players,
finite nonempty strategy carriers and integrable pure play has a proper
equilibrium. No finiteness assumption is made on outcomes. -/
theorem exists_isProper [∀ i, Finite (F.sig.Strategy i)]
    [∀ i, Nonempty (F.sig.Strategy i)]
    (utility : F.sig.Outcome → ι → ℝ) (integrable : F.HasIntegrableUtility utility) :
    ∃ profile : Profile F.sig.mixed, F.IsProper utility profile := by
  let epsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have positive (n : ℕ) : 0 < epsilon n := by
    dsimp only [epsilon]
    positivity
  have small (n : ℕ) : epsilon n < 1 := by
    dsimp only [epsilon]
    rw [div_lt_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have vanishes : Tendsto epsilon atTop (nhds 0) := by
    have limit := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    convert limit using 1
    funext n
    simp only [epsilon, Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  choose approximating proper using fun n => F.exists_isεProper utility integrable
    (epsilon n) (positive n) (small n)
  obtain ⟨profile, subsequence, increasing, converges⟩ :=
    exists_subseq_pmfConvergesPointwise_pi (A := F.sig.Strategy) approximating
  exact ⟨profile, epsilon ∘ subsequence, approximating ∘ subsequence,
    fun n => proper (subsequence n), vanishes.comp increasing.tendsto_atTop, converges⟩

end GameTheory.GameForm
