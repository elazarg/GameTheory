/-
# Probability domination and the stability of conditional laws

A law dominates another up to a factor when every point keeps at least that
fraction of its mass. Domination passes to events, to expectations of
nonnegative payoffs, through a common kernel, along iterated execution and to
independent products of perturbed coordinates.

Domination also controls conditioning. When the dominated law keeps nearly all
its mass, each conditional probability moves by at most the missing mass
divided by the conditioning event's mass, however rare that event is.
Enlarging an event moves its conditional law by at most the ratio of the added
mass to the retained mass. No carrier is assumed finite.
-/

import GameTheory.Math.Probability.Bounds
import GameTheory.Math.Probability.Conditioning
import GameTheory.Math.Probability.Convergence

noncomputable section

namespace GameTheory.Math.Probability

open Filter

section Domination

variable {α β : Type*}

/-- Pointwise probability domination bounds every integrable nonnegative
expectation. -/
theorem mul_expect_le_of_prob_le (source target : PMF α) (factor : ℝ)
    (lower : ∀ a, factor * (source a).toReal ≤ (target a).toReal)
    (utility : α → ℝ) (nonnegative : ∀ a, 0 ≤ utility a)
    (integrable : PayoffIntegrable target utility) :
    factor * expect source utility ≤ expect target utility := by
  rcases le_or_gt factor 0 with hnonpos | hpos
  · exact (mul_nonpos_of_nonpos_of_nonneg hnonpos
      (expect_nonneg _ _ fun a _ => nonnegative a)).trans
        (expect_nonneg _ _ fun a _ => nonnegative a)
  · have hsource := payoffIntegrable_of_scaled_weight_le source target utility factor hpos lower
      integrable
    rw [expect, expect, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun a => ?_) (hsource.summable.mul_left factor)
      integrable.summable
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (lower a) (nonnegative a)

/-- Pointwise domination carries over to every event. -/
theorem probOf_domination (source target : PMF α) (factor : ℝ)
    (lower : ∀ a, factor * (source a).toReal ≤ (target a).toReal) (event : Set α) :
    factor * (source.toOuterMeasure event).toReal ≤ (target.toOuterMeasure event).toReal := by
  classical
  rw [← expect_indicator, ← expect_indicator]
  exact mul_expect_le_of_prob_le source target factor lower _
    (fun a => by split_ifs <;> norm_num)
    (payoffIntegrable_of_bounded _ _ (C := 1) fun a => by split_ifs <;> norm_num)

private theorem probOf_add_compl (law : PMF α) (event : Set α) :
    (law.toOuterMeasure event).toReal + (law.toOuterMeasure eventᶜ).toReal = 1 := by
  classical
  rw [← expect_indicator, ← expect_indicator,
    ← expect_add (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => by split_ifs <;> norm_num)
      (payoffIntegrable_of_bounded _ _ (C := 1) fun _ => by split_ifs <;> norm_num)]
  calc
    _ = expect law (fun _ => (1 : ℝ)) := by
      apply expect_congr_on_support
      intro a _
      by_cases member : a ∈ event <;> simp [member]
    _ = 1 := expect_constant _ _

/-- All mass in excess of the dominated source component is at most its
missing normalization mass, including after restricting to an event. -/
theorem probOf_domination_excess (source target : PMF α) (factor : ℝ)
    (lower : ∀ a, factor * (source a).toReal ≤ (target a).toReal) (event : Set α) :
    (target.toOuterMeasure event).toReal - factor * (source.toOuterMeasure event).toReal ≤
      1 - factor := by
  have complement := probOf_domination source target factor lower eventᶜ
  have sourceTotal := probOf_add_compl source event
  have targetTotal := probOf_add_compl target event
  have scaled := congrArg (fun value => factor * value) sourceTotal
  rw [mul_add, mul_one] at scaled
  linarith

private theorem ratio_domination_bound (point mass changed total factor : ℝ)
    (massPositive : 0 < mass) (totalPositive : 0 < total)
    (pointNonnegative : 0 ≤ point) (pointWithin : point ≤ mass)
    (factorPositive : 0 < factor) (factorAtMostOne : factor ≤ 1)
    (pointLower : factor * point ≤ changed)
    (pointExcess : changed - factor * point ≤ 1 - factor)
    (massLower : factor * mass ≤ total)
    (massExcess : total - factor * mass ≤ 1 - factor) :
    |changed / total - point / mass| ≤ (1 - factor) / (factor * mass) := by
  have fractionNonnegative : 0 ≤ point / mass := div_nonneg pointNonnegative massPositive.le
  have fractionAtMostOne : point / mass ≤ 1 := (div_le_one massPositive).mpr pointWithin
  have excessNonnegative : 0 ≤ total - factor * mass := sub_nonneg.mpr massLower
  have missingNonnegative : 0 ≤ 1 - factor := sub_nonneg.mpr factorAtMostOne
  have scaledNonnegative := mul_nonneg fractionNonnegative excessNonnegative
  have scaledUpper : (point / mass) * (total - factor * mass) ≤ 1 - factor :=
    (mul_le_mul_of_nonneg_left massExcess fractionNonnegative).trans
      (mul_le_of_le_one_left missingNonnegative fractionAtMostOne)
  have numerator : |(changed - factor * point) -
      (point / mass) * (total - factor * mass)| ≤ 1 - factor := by
    apply abs_le.mpr
    constructor <;> linarith
  have difference : changed / total - point / mass =
      ((changed - factor * point) - (point / mass) * (total - factor * mass)) / total := by
    field_simp
    ring
  rw [difference, abs_div, abs_of_pos totalPositive]
  exact (div_le_div_of_nonneg_right numerator totalPositive.le).trans
    (div_le_div_of_nonneg_left missingNonnegative (mul_pos factorPositive massPositive)
      massLower)

/-- Domination by a near-unit source component bounds each posterior error by
the missing mass divided by the retained source event mass. -/
theorem conditional_domination_bound (source target : PMF α) (event : Set α)
    (sourceMeet : ∃ a ∈ event, a ∈ source.support)
    (targetMeet : ∃ a ∈ event, a ∈ target.support)
    (factor : ℝ) (positive : 0 < factor) (atMostOne : factor ≤ 1)
    (lower : ∀ a, factor * (source a).toReal ≤ (target a).toReal) (a : α) :
    |((target.filter event targetMeet) a).toReal -
      ((source.filter event sourceMeet) a).toReal| ≤
        (1 - factor) / (factor * (source.toOuterMeasure event).toReal) := by
  classical
  have sourcePositive := toOuterMeasure_toReal_pos source sourceMeet
  have targetPositive := toOuterMeasure_toReal_pos target targetMeet
  rw [toReal_filter_apply, toReal_filter_apply]
  by_cases member : a ∈ event
  · rw [ite_eq_left member, ite_eq_left member]
    have pointWithin : (source a).toReal ≤ (source.toOuterMeasure event).toReal := by
      have normalized := pmf_toReal_apply_le_one (source.filter event sourceMeet) a
      rw [toReal_filter_apply, ite_eq_left member] at normalized
      exact (div_le_one sourcePositive).mp normalized
    have pointExcess : (target a).toReal - factor * (source a).toReal ≤ 1 - factor := by
      simpa only [PMF.toOuterMeasure_apply_singleton] using
        probOf_domination_excess source target factor lower {a}
    exact ratio_domination_bound _ _ _ _ _ sourcePositive targetPositive
      ENNReal.toReal_nonneg pointWithin positive atMostOne (lower a) pointExcess
      (probOf_domination source target factor lower event)
      (probOf_domination_excess source target factor lower event)
  · rw [ite_eq_right member, ite_eq_right member, sub_self, abs_zero]
    exact div_nonneg (sub_nonneg.mpr atMostOne) (mul_pos positive sourcePositive).le

/-- A vanishing relative loss transports conditioned laws without any lower
bound on the limiting probability of the conditioning event. -/
theorem conditional_domination_converges (source target : ℕ → PMF α) (event : Set α)
    (sourceMeet : ∀ n, ∃ a ∈ event, a ∈ (source n).support)
    (targetMeet : ∀ n, ∃ a ∈ event, a ∈ (target n).support)
    (factor : ℕ → ℝ) (positive : ∀ n, 0 < factor n) (atMostOne : ∀ n, factor n ≤ 1)
    (lower : ∀ n a, factor n * ((source n) a).toReal ≤ ((target n) a).toReal)
    (negligible : Tendsto (fun n =>
      (1 - factor n) / (factor n * ((source n).toOuterMeasure event).toReal)) atTop (nhds 0))
    (limit : PMF α)
    (converges : PMFConvergesPointwise
      (fun n => (source n).filter event (sourceMeet n)) limit) :
    PMFConvergesPointwise (fun n => (target n).filter event (targetMeet n)) limit := by
  rw [pmfConvergesPointwise_iff_toReal]
  intro a
  apply (converges.toReal a).congr_dist
  apply squeeze_zero (fun _ => dist_nonneg) _ negligible
  intro n
  simpa only [Real.dist_eq, abs_sub_comm] using
    conditional_domination_bound (source n) (target n) event
      (sourceMeet n) (targetMeet n) (factor n) (positive n) (atMostOne n) (lower n) a

/-- Conditioning commutes with an injective encoding when the two events
correspond on encoded values. Extra target values need not have source names. -/
theorem map_filter_embedding (law : PMF α) (embed : α ↪ β) (sourceEvent : Set α)
    (targetEvent : Set β) (corresponds : ∀ a, embed a ∈ targetEvent ↔ a ∈ sourceEvent)
    (sourceMeet : ∃ a ∈ sourceEvent, a ∈ law.support)
    (targetMeet : ∃ b ∈ targetEvent, b ∈ (law.map embed).support) :
    (law.filter sourceEvent sourceMeet).map embed =
      (law.map embed).filter targetEvent targetMeet := by
  classical
  have preimage : embed ⁻¹' targetEvent = sourceEvent := Set.ext corresponds
  have mass : (law.map embed).toOuterMeasure targetEvent = law.toOuterMeasure sourceEvent := by
    rw [PMF.toOuterMeasure_map_apply, preimage]
  ext value
  by_cases encoded : value ∈ Set.range embed
  · obtain ⟨original, rfl⟩ := encoded
    rw [pmf_map_apply_of_injective _ embed.injective, PMF.filter_apply, PMF.filter_apply,
      ← PMF.toOuterMeasure_apply, ← PMF.toOuterMeasure_apply, mass]
    by_cases member : original ∈ sourceEvent
    · rw [Set.indicator_of_mem member, Set.indicator_of_mem ((corresponds original).mpr member),
        pmf_map_apply_of_injective _ embed.injective]
    · rw [Set.indicator_of_notMem member,
        Set.indicator_of_notMem fun inside => member ((corresponds original).mp inside)]
  · have unsupported (distribution : PMF α) : (distribution.map embed) value = 0 := by
      apply (PMF.apply_eq_zero_iff _ _).mpr
      rw [PMF.support_map]
      rintro ⟨original, _, same⟩
      exact encoded ⟨original, same⟩
    rw [unsupported, PMF.filter_apply, Set.indicator_apply]
    split_ifs <;> simp [unsupported]

end Domination

section Kernel

variable {α β : Type*}

/-- A common kernel preserves pointwise domination. -/
theorem prob_bind_ge_mul (source target : PMF α) (factor : ℝ)
    (dominates : ∀ a, factor * (source a).toReal ≤ (target a).toReal)
    (kernel : α → PMF β) (b : β) :
    factor * ((source.bind kernel) b).toReal ≤ ((target.bind kernel) b).toReal := by
  rw [toReal_bind_apply, toReal_bind_apply]
  exact mul_expect_le_of_prob_le source target factor dominates _
    (fun _ => ENNReal.toReal_nonneg) (payoffIntegrable_toReal_apply target kernel b)

/-- A lower bound on the current law and a lower bound on the next-step kernel
multiply. The embedding need not be surjective or injective. -/
theorem bind_prob_domination (source : PMF α) (target : PMF β)
    (embed : α → β) (sourceStep : α → PMF α) (targetStep : β → PMF β)
    (initialFactor stepFactor : ℝ) (initialNonnegative : 0 ≤ initialFactor)
    (initialLower : ∀ b, initialFactor * ((source.map embed) b).toReal ≤ (target b).toReal)
    (stepLower : ∀ a b,
      stepFactor * (((sourceStep a).map embed) b).toReal ≤ ((targetStep (embed a)) b).toReal)
    (b : β) :
    (initialFactor * stepFactor) * (((source.bind sourceStep).map embed) b).toReal ≤
      ((target.bind targetStep) b).toReal := by
  rw [PMF.map_bind, toReal_bind_apply, toReal_bind_apply]
  calc
    _ = initialFactor * expect source
        (fun a => stepFactor * (((sourceStep a).map embed) b).toReal) := by
      rw [expect_const_mul]
      ring
    _ ≤ initialFactor * expect source (fun a => ((targetStep (embed a)) b).toReal) :=
      mul_le_mul_of_nonneg_left (expect_mono (fun a _ => stepLower a b)
        (payoffIntegrable_of_bounded _ _ (C := |stepFactor|) fun a => by
          rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          exact mul_le_of_le_one_right (abs_nonneg _) (pmf_toReal_apply_le_one _ _))
        (payoffIntegrable_toReal_apply source (fun a => targetStep (embed a)) b))
        initialNonnegative
    _ = initialFactor * expect (source.map embed)
        (fun state => ((targetStep state) b).toReal) := by rw [expect_map]; rfl
    _ ≤ expect target (fun state => ((targetStep state) b).toReal) :=
      mul_expect_le_of_prob_le (source.map embed) target initialFactor initialLower
        _ (fun _ => ENNReal.toReal_nonneg) (payoffIntegrable_toReal_apply target targetStep b)

/-- Iterated one-step domination preserves every source outcome with at least
the product of the step factors. Other target outcomes remain unrestricted. -/
theorem iterate_prob_domination (initial : PMF α) (embed : α → β)
    (sourceStep : α → PMF α) (targetStep : β → PMF β)
    (factor : ℝ) (nonnegative : 0 ≤ factor)
    (stepLower : ∀ a b,
      factor * (((sourceStep a).map embed) b).toReal ≤ ((targetStep (embed a)) b).toReal)
    (steps : ℕ) (b : β) :
    factor ^ steps *
        ((((fun law => law.bind sourceStep)^[steps] initial).map embed) b).toReal ≤
      (((fun law => law.bind targetStep)^[steps] (initial.map embed)) b).toReal := by
  induction steps generalizing b with
  | zero => simp
  | succ steps ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ]
      exact bind_prob_domination
        ((fun law => law.bind sourceStep)^[steps] initial)
        ((fun law => law.bind targetStep)^[steps] (initial.map embed))
        embed sourceStep targetStep (factor ^ steps) factor (pow_nonneg nonnegative _)
        (fun b => ih b) stepLower b

end Kernel

section Product

variable {Index : Type*} [Fintype Index] {Action : Index → Type*}

/-- Coordinate lower bounds multiply under independent sampling. -/
theorem prob_pi_ge_prod_mul (source target : ∀ index, PMF (Action index))
    (factor : Index → ℝ) (nonnegative : ∀ index, 0 ≤ factor index)
    (dominates : ∀ index action,
      factor index * ((source index) action).toReal ≤ ((target index) action).toReal)
    (actions : ∀ index, Action index) :
    (∏ index, factor index) * ((independentProduct source) actions).toReal ≤
      ((independentProduct target) actions).toReal := by
  simp only [independentProduct_apply, ENNReal.toReal_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro index _
    exact mul_nonneg (nonnegative index) ENNReal.toReal_nonneg
  · intro index _
    exact dominates index (actions index)

/-- Every original joint action retains the probability of choosing the
original branch independently at all coordinates. -/
theorem prob_pi_mix_lower (source reference : ∀ index, PMF (Action index))
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (actions : ∀ index, Action index) :
    (1 - epsilon) ^ Fintype.card Index * ((independentProduct source) actions).toReal ≤
      ((independentProduct fun index =>
        mix epsilon nonnegative small (reference index) (source index)) actions).toReal := by
  have bound := prob_pi_ge_prod_mul source
    (fun index => mix epsilon nonnegative small (reference index) (source index))
    (fun _ => 1 - epsilon) (fun _ => sub_nonneg.mpr small) (fun index action => by
      rw [mix_apply_toReal]
      exact le_add_of_nonneg_left (mul_nonneg nonnegative ENNReal.toReal_nonneg)) actions
  simpa only [Finset.prod_const, Finset.card_univ] using bound

/-- The product bound applies after any common transition kernel. -/
theorem prob_pi_mix_bind_lower {Next : Type*}
    (source reference : ∀ index, PMF (Action index))
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (kernel : (∀ index, Action index) → PMF Next) (next : Next) :
    (1 - epsilon) ^ Fintype.card Index * (((independentProduct source).bind kernel) next).toReal ≤
      (((independentProduct fun index =>
        mix epsilon nonnegative small (reference index) (source index)).bind kernel)
          next).toReal :=
  prob_bind_ge_mul _ _ _ (prob_pi_mix_lower source reference epsilon nonnegative small) kernel next

end Product

section Contamination

variable {α : Type*}

private theorem point_mass_le_event (law : PMF α) (event : Set α)
    (value : α) (member : value ∈ event) :
    (law value).toReal ≤ (law.toOuterMeasure event).toReal := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  exact outerMeasure_toReal_mono law (Set.singleton_subset_iff.mpr member)

private theorem event_mass_split (law : PMF α) (whole good : Set α) (subset : good ⊆ whole) :
    (law.toOuterMeasure whole).toReal =
      (law.toOuterMeasure good).toReal + (law.toOuterMeasure (whole \ good)).toReal := by
  rw [← ENNReal.toReal_add (outerMeasure_ne_top law good) (outerMeasure_ne_top law _),
    PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_add]
  congr 1
  apply tsum_congr
  intro value
  by_cases inGood : value ∈ good
  · simp [Set.indicator, inGood, subset inGood]
  · by_cases inWhole : value ∈ whole <;> simp [Set.indicator, inGood, inWhole]

/-- Enlarging an event moves each conditional probability by at most the
ratio of the added mass to the retained mass. No positive lower bound on the
event's mass is required. -/
theorem conditional_contamination_bound (law : PMF α) (whole good : Set α)
    (subset : good ⊆ whole)
    (wholeMeet : ∃ value ∈ whole, value ∈ law.support)
    (goodMeet : ∃ value ∈ good, value ∈ law.support) (value : α) :
    |((law.filter whole wholeMeet) value).toReal - ((law.filter good goodMeet) value).toReal| ≤
      (law.toOuterMeasure (whole \ good)).toReal / (law.toOuterMeasure good).toReal := by
  classical
  have goodPositive := toOuterMeasure_toReal_pos law goodMeet
  have wholePositive := toOuterMeasure_toReal_pos law wholeMeet
  have badNonnegative : 0 ≤ (law.toOuterMeasure (whole \ good)).toReal := ENNReal.toReal_nonneg
  have splitMass := event_mass_split law whole good subset
  have massLe : (law.toOuterMeasure good).toReal ≤ (law.toOuterMeasure whole).toReal := by
    linarith
  rw [toReal_filter_apply, toReal_filter_apply]
  by_cases inGood : value ∈ good
  · rw [ite_eq_left inGood, ite_eq_left (subset inGood)]
    have pointLe := point_mass_le_event law whole value (subset inGood)
    have fractionLe : (law value).toReal / (law.toOuterMeasure whole).toReal ≤ 1 :=
      (div_le_one wholePositive).mpr pointLe
    have ordered : (law value).toReal / (law.toOuterMeasure whole).toReal ≤
        (law value).toReal / (law.toOuterMeasure good).toReal :=
      div_le_div_of_nonneg_left ENNReal.toReal_nonneg goodPositive massLe
    rw [abs_of_nonpos (sub_nonpos.mpr ordered), neg_sub]
    apply (le_div_iff₀ goodPositive).mpr
    calc
      ((law value).toReal / (law.toOuterMeasure good).toReal -
          (law value).toReal / (law.toOuterMeasure whole).toReal) *
          (law.toOuterMeasure good).toReal =
          (law value).toReal - ((law value).toReal / (law.toOuterMeasure whole).toReal) *
            (law.toOuterMeasure good).toReal := by
        rw [sub_mul, div_mul_cancel₀ _ goodPositive.ne']
      _ = ((law value).toReal / (law.toOuterMeasure whole).toReal) *
          (law.toOuterMeasure (whole \ good)).toReal := by
        have cancellation := div_mul_cancel₀ ((law value).toReal) wholePositive.ne'
        calc
          _ = ((law value).toReal / (law.toOuterMeasure whole).toReal) *
              ((law.toOuterMeasure whole).toReal - (law.toOuterMeasure good).toReal) := by
            rw [mul_sub, cancellation]
          _ = _ := by congr 1; linarith
      _ ≤ (law.toOuterMeasure (whole \ good)).toReal :=
        mul_le_of_le_one_left badNonnegative fractionLe
  · rw [ite_eq_right inGood]
    by_cases inWhole : value ∈ whole
    · rw [ite_eq_left inWhole, sub_zero,
        abs_of_nonneg (div_nonneg ENNReal.toReal_nonneg wholePositive.le)]
      have pointLe := point_mass_le_event law (whole \ good) value ⟨inWhole, inGood⟩
      exact (div_le_div_of_nonneg_right pointLe wholePositive.le).trans
        (div_le_div_of_nonneg_left badNonnegative goodPositive massLe)
    · rw [ite_eq_right inWhole, sub_zero, abs_zero]
      exact div_nonneg badNonnegative goodPositive.le

/-- The retained event may lose all mass in the limit. Its conditional law is
still preserved when the added mass is negligible relative to the retained
mass of that same event. -/
theorem conditional_contamination_converges (sequence : ℕ → PMF α) (whole good : Set α)
    (subset : good ⊆ whole)
    (wholeMeet : ∀ n, ∃ value ∈ whole, value ∈ (sequence n).support)
    (goodMeet : ∀ n, ∃ value ∈ good, value ∈ (sequence n).support)
    (limit : PMF α)
    (compliant : PMFConvergesPointwise
      (fun n => (sequence n).filter good (goodMeet n)) limit)
    (negligible : Tendsto (fun n =>
      ((sequence n).toOuterMeasure (whole \ good)).toReal /
        ((sequence n).toOuterMeasure good).toReal) atTop (nhds 0)) :
    PMFConvergesPointwise (fun n => (sequence n).filter whole (wholeMeet n)) limit := by
  rw [pmfConvergesPointwise_iff_toReal]
  intro value
  apply (compliant.toReal value).congr_dist
  apply squeeze_zero (fun _ => dist_nonneg) _ negligible
  intro n
  simpa only [Real.dist_eq, abs_sub_comm] using
    conditional_contamination_bound (sequence n) whole good subset
      (wholeMeet n) (goodMeet n) value

/-- A lower bound on the retained mass and an upper bound on the added mass
suffice when their ratio vanishes. -/
theorem conditional_contamination_converges_of_bound (sequence : ℕ → PMF α)
    (whole good : Set α) (subset : good ⊆ whole)
    (wholeMeet : ∀ n, ∃ value ∈ whole, value ∈ (sequence n).support)
    (goodMeet : ∀ n, ∃ value ∈ good, value ∈ (sequence n).support)
    (limit : PMF α)
    (compliant : PMFConvergesPointwise
      (fun n => (sequence n).filter good (goodMeet n)) limit)
    (lower upper : ℕ → ℝ) (positive : ∀ n, 0 < lower n)
    (goodBound : ∀ n, lower n ≤ ((sequence n).toOuterMeasure good).toReal)
    (badBound : ∀ n, ((sequence n).toOuterMeasure (whole \ good)).toReal ≤ upper n)
    (negligible : Tendsto (fun n => upper n / lower n) atTop (nhds 0)) :
    PMFConvergesPointwise (fun n => (sequence n).filter whole (wholeMeet n)) limit := by
  apply conditional_contamination_converges sequence whole good subset wholeMeet goodMeet limit
    compliant
  apply squeeze_zero _ _ negligible
  · intro n
    exact div_nonneg ENNReal.toReal_nonneg (toOuterMeasure_toReal_pos _ (goodMeet n)).le
  · intro n
    have nonnegative : 0 ≤ ((sequence n).toOuterMeasure (whole \ good)).toReal :=
      ENNReal.toReal_nonneg
    exact (div_le_div_of_nonneg_right (badBound n)
      (toOuterMeasure_toReal_pos _ (goodMeet n)).le).trans
        (div_le_div_of_nonneg_left (nonnegative.trans (badBound n))
          (positive n) (goodBound n))

end Contamination

end GameTheory.Math.Probability
