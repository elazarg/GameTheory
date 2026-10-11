/- Copyright (c) 2026 VegasCore contributors. Released under MIT; see NOTICE. -/

import GameTheory.Core.StrategySubstitution
import GameTheory.Analysis.Nash
import GameTheory.Analysis.LocalChoiceFixedPoint
import GameTheory.Math.Probability.AggregateComparison

/-! # Optimal component mixtures with shared mixture weights

Finite menus of stochastic strategy components admit simultaneous best-response
mixtures. Group members may share a weight vector, and a fixed point makes each
group maximize the continuously weighted sum of its members' unilateral gains.
Underlying strategies and outcomes may be infinite; only component plays need
integrable utilities. The stochastic substitution and update laws come from
the utility-free core, with no extra strategic semantics or dependent casts.

Sharing weights is a constraint on policy parameters. Components remain
agent-specific and their random draws are independent; equal weights imply
neither identical action laws nor protection of hidden information.

Aggregate optimality does not imply every member's optimality. The independent
probability bound for a common near-maximizing action controls individual regret,
including weighted and approximate aggregate comparisons.
-/

noncomputable section
namespace GameTheory
open Math.Probability
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : GameForm ι}

omit [DecidableEq ι] in
/-- A player's payoff polynomial, averaged over point masses at its own
strategies, is its payoff at the averaged weights. -/
private theorem expect_payoff_point [∀ who, Fintype (F.sig.Strategy who)] [DecidableEq ι]
    (utility : F.sig.Outcome → ι → ℝ) (y : Profile F.sig.weights) (who : ι)
    (law : PMF (F.sig.Strategy who)) :
    expect law (fun choice => payoff F utility who
        (Profile.update y who fun other => ((PMF.pure choice) other).toReal)) =
      payoff F utility who (Profile.update y who fun other => (law other).toReal) := by
  classical
  rw [expect_eq_sum]
  simp only [payoff_update, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun profile _ => ?_
  simp only [PMF.pure_apply, ← mul_assoc, ← Finset.sum_mul]
  simp only [apply_ite ENNReal.toReal, ENNReal.toReal_one, ENNReal.toReal_zero, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

/-- **Best component mixtures with shared weights.** Players are partitioned into groups, and all
members of a group mix their own components with one common weight vector over
the group's parts. A fixed point chooses the weights of all groups together so
that no common replacement of a group's weights raises the sum, over its
members, of each member's own expected utility gain weighted by its
`importance`, each member deviating alone against the same play of everybody
else. The importance of a member may depend continuously on the weights of all
players, for instance as the inverse of the probability of reaching it, which
turns the sum into a sum of conditional gains. With one player per group and
unit importance this is Nash existence among component mixtures. -/
theorem exists_bestResponses_with_shared_mixture_weights
    {WeightGroup : Type*} [Finite WeightGroup] [DecidableEq WeightGroup] (groupOf : ι → WeightGroup)
    {Part : WeightGroup → Type*} [∀ p, Finite (Part p)] [∀ p, Nonempty (Part p)]
    (utility : F.sig.Outcome → ι → ℝ)
    (component : ∀ who, Part (groupOf who) → PMF (F.sig.Strategy who))
    (componentIntegrable : ∀ choice : (∀ who, Part (groupOf who)), ∀ who,
      PayoffIntegrable (F.mixed.play fun player => component player (choice player))
        (fun outcome => utility outcome who))
    (importance : (∀ who, Part (groupOf who) → ℝ) → ι → ℝ)
    (importanceContinuous : ∀ who, ContinuousOn (fun weights => importance weights who)
      {weights | ∀ player, weights player ∈ simplexWeights (Part (groupOf player))}) :
    ∃ weights : ∀ p, PMF (Part p), ∀ (alternative : ∀ p, PMF (Part p)) (p : WeightGroup),
      ∑ who ∈ Finset.univ.filter (fun who => groupOf who = p),
        importance (fun player part => (weights (groupOf player) part).toReal) who *
        (expectedUtility utility who (F.mixed.play
            (Profile.update (sig := F.sig.mixed)
              (fun player => (weights (groupOf player)).bind (component player))
              who ((alternative (groupOf who)).bind (component who)))) -
          expectedUtility utility who
            (F.mixed.play fun player => (weights (groupOf player)).bind (component player))) ≤
        0 := by
  classical
  let _ : Fintype WeightGroup := Fintype.ofFinite WeightGroup
  let G := F.substituteStrategies component
  let _ (p : WeightGroup) : Fintype (Part p) := Fintype.ofFinite _
  let _ (who : ι) : Fintype (G.sig.Strategy who) := Fintype.ofFinite (Part (groupOf who))
  have integrable : G.HasIntegrableUtility utility :=
    fun who choice => componentIntegrable choice who
  let spread (x : ∀ p, Part p → ℝ) : Profile G.sig.weights := fun who => x (groupOf who)
  have spreadContinuous : Continuous spread :=
    continuous_pi fun who => continuous_apply (groupOf who)
  have spreadInside (x : Set.pi Set.univ fun p => simplexWeights (Part p)) :
      spread x.1 ∈ {weights : ∀ who, Part (groupOf who) → ℝ |
        ∀ player, weights player ∈ simplexWeights (Part (groupOf player))} :=
    fun player => x.2 (groupOf player) (Set.mem_univ _)
  let groupSig : GameSignature WeightGroup := { Strategy := Part, Outcome := Unit }
  let point (p : WeightGroup) (choice : Part p) : Part p → ℝ :=
    fun other => ((PMF.pure choice) other).toReal
  let score (x : Set.pi Set.univ fun p => simplexWeights (Part p)) (p : WeightGroup) (choice : Part p) :
      ℝ :=
    ∑ who, if groupOf who = p then
      importance (spread x.1) who * payoff G utility who (Profile.update (spread x.1) who
        ((Profile.update (sig := groupSig.weights) x.1 p (point p choice)) (groupOf who)))
    else 0
  have scoreContinuous (p : WeightGroup) (choice : Part p) :
      Continuous fun x => score x p choice := by
    refine continuous_finsetSum _ fun who _ => ?_
    split
    · rename_i same
      subst p
      simp only [Profile.update_same]
      exact ((importanceContinuous who).comp_continuous
        (spreadContinuous.comp continuous_subtype_val) spreadInside).mul
        (((continuous_payoff who).comp (continuous_update_profile who _)).comp
          (spreadContinuous.comp continuous_subtype_val))
    · exact continuous_const
  obtain ⟨x, optimal⟩ := exists_localChoice_fixedPoint score scoreContinuous
  let weights (p : WeightGroup) : PMF (Part p) := PMF.ofSimplex (x.property p (Set.mem_univ p))
  let laws : Profile G.sig.mixed := fun who => weights (groupOf who)
  have spreadLaws : spread x.1 = probs G.sig laws := by
    funext who
    exact (PMF.ofSimplex_toReal (x.property (groupOf who) (Set.mem_univ _))).symm
  have spreadWeights : spread x.1 = fun player part => (weights (groupOf player) part).toReal :=
    spreadLaws
  have member (who : ι) (p : WeightGroup) (h : groupOf who = p) (alternative : ∀ p, PMF (Part p)) :
      expect (alternative p) (fun choice => importance (spread x.1) who *
          payoff G utility who
          (Profile.update (spread x.1) who ((Profile.update (sig := groupSig.weights) x.1 p (point p choice)) (groupOf who)))) =
        importance (spread x.1) who * expectedUtility utility who (F.mixed.play
          (Profile.update (sig := F.sig.mixed)
            (fun player => (weights (groupOf player)).bind (component player))
            who ((alternative (groupOf who)).bind (component who)))) := by
    subst h
    simp only [Profile.update_same]
    rw [expect_const_mul, expect_payoff_point (F := G) utility (spread x.1) who
      (alternative (groupOf who)), spreadLaws, ← probs_update, payoff_probs integrable,
      GameForm.substituteStrategies_mixed_play, GameForm.substituteStrategies_update]
  have total (alternative : ∀ p, PMF (Part p)) (p : WeightGroup) :
      expect (alternative p) (score x p) =
        ∑ who ∈ Finset.univ.filter (fun who => groupOf who = p),
          importance (spread x.1) who * expectedUtility utility who (F.mixed.play
            (Profile.update (sig := F.sig.mixed)
              (fun player => (weights (groupOf player)).bind (component player))
              who ((alternative (groupOf who)).bind (component who)))) := by
    rw [Finset.sum_filter, expect_eq_sum]
    simp only [score, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun who _ => ?_
    by_cases h : groupOf who = p
    · rw [← member who p h alternative, expect_eq_sum]
      simp only [h, ite_true]
    · simp [h]
  refine ⟨weights, fun alternative p => ?_⟩
  have compared := optimal p (alternative p)
  rw [total alternative p, show PMF.ofSimplex (x.property p (Set.mem_univ p)) = weights p from rfl,
    total weights p] at compared
  have same (who : ι) :
      Profile.update (sig := F.sig.mixed)
          (fun player => (weights (groupOf player)).bind (component player))
          who ((weights (groupOf who)).bind (component who)) =
        fun player => (weights (groupOf player)).bind (component player) := by
    funext player
    by_cases equal : player = who
    · subst player
      simp only [Profile.update_same]
    · simp only [Profile.update_of_ne _ _ equal]
  simp only [same] at compared
  rw [← spreadWeights]
  simp only [mul_sub, Finset.sum_sub_distrib]
  linarith


/-- Simultaneous best mixtures of finitely many components follow from finite Nash,
with arbitrary underlying strategies and outcomes whose component plays are integrable. -/
theorem exists_component_bestResponses
    {Component : ι → Type*} [∀ who, Finite (Component who)] [∀ who, Nonempty (Component who)]
    (utility : F.sig.Outcome → ι → ℝ)
    (component : ∀ who, Component who → PMF (F.sig.Strategy who))
    (componentIntegrable : ∀ choice : (∀ who, Component who), ∀ who,
      PayoffIntegrable (F.mixed.play fun player => component player (choice player))
        (fun outcome => utility outcome who)) :
    ∃ weights : ∀ who, PMF (Component who), ∀ who (alternative : PMF (Component who)),
      expectedUtility utility who (F.mixed.play
        (Profile.update (sig := F.sig.mixed) (fun player => (weights player).bind (component player))
          who (alternative.bind (component who)))) ≤
        expectedUtility utility who (F.mixed.play fun player => (weights player).bind (component player)) := by
  classical
  let G := F.substituteStrategies component
  let _ (who : ι) : Fintype (G.sig.Strategy who) := Fintype.ofFinite (Component who)
  have integrable : G.HasIntegrableUtility utility := fun who choice => componentIntegrable choice who
  obtain ⟨weights, optimal⟩ := exists_isNash_mixed (F := G) utility integrable
  refine ⟨weights, fun who alternative => ?_⟩
  have comparison := (isNash_iff (F := G.mixed) (weaklyPrefers := euPreference utility) weights).mp optimal who alternative
  have values := (euPreference_iff utility who _ _
    (integrable.mixed_of_finite who weights)
    (integrable.mixed_of_finite who (Profile.update weights who alternative))).mp comparison
  rw [GameForm.substituteStrategies_mixed_play, GameForm.substituteStrategies_mixed_play, GameForm.substituteStrategies_update] at values
  exact values

end GameTheory
