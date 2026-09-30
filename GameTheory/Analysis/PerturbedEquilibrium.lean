/-
# Perturbed equilibria and the existence of trembling-hand perfection

Some players have prescribed mixed laws. Each remaining player reserves the
same positive weight for a reference law and chooses its residual law. Finite
Nash existence in an induced game selects all residual laws together, each
optimal against the same perturbed opponents, so completions of several
players are compatible by construction.

When every player trembles, the construction is an equilibrium of the
perturbation whose lower bound is the tremble weight times the reference:
the strategies respecting that bound are exactly its reference mixtures.
Letting the weight vanish and extracting a convergent subsequence gives
Selten's theorem: every finite game has a trembling-hand perfect equilibrium.
-/

import GameTheory.Analysis.Nash
import GameTheory.Analysis.TremblingHand
import GameTheory.Math.Probability.Compactness
import Mathlib.Probability.Distributions.Uniform

noncomputable section

namespace GameTheory

open Filter Math.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : GameForm ι}

/-- Prescribed players keep their laws; free players add an independent
tremble toward a reference law. -/
def pinnedTremble (free : Finset ι) (pinned reference residual : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) :
    Profile F.sig.mixed := fun who =>
  if who ∈ free then mix epsilon nonnegative small (reference who) (residual who)
  else pinned who

private def responseKernel (free : Finset ι) (pinned reference : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (who : ι) (action : F.sig.Strategy who) : PMF (F.sig.Strategy who) :=
  if who ∈ free then mix epsilon nonnegative small (reference who) (PMF.pure action)
  else pinned who

private def responseGame (free : Finset ι) (pinned reference : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) : GameForm ι where
  sig := F.sig
  play profile := F.mixed.play
    (fun who => responseKernel free pinned reference epsilon nonnegative small who (profile who))

omit [Fintype ι] in
private theorem response_kernel_law (free : Finset ι)
    (pinned reference residual : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) (who : ι) :
    (residual who).bind (responseKernel free pinned reference epsilon nonnegative small who) =
      pinnedTremble free pinned reference residual epsilon nonnegative small who := by
  change (residual who).bind (fun action =>
    if who ∈ free then mix epsilon nonnegative small (reference who) (PMF.pure action)
    else pinned who) = _
  by_cases active : who ∈ free
  · simp only [pinnedTremble, active, ↓reduceIte]
    ext action
    have pure : ∑' choice, (residual who) choice * (PMF.pure choice) action =
        (residual who) action := by
      rw [← PMF.bind_apply, PMF.bind_pure]
    simp only [PMF.bind_apply, mix_apply, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right,
      PMF.tsum_coe, one_mul, mul_left_comm _ (ENNReal.ofReal (1 - epsilon)),
      ENNReal.tsum_mul_left, pure]
  · simp only [pinnedTremble, active, ↓reduceIte, PMF.bind_const]

private theorem response_game_law (free : Finset ι)
    (pinned reference residual : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1) :
    (responseGame free pinned reference epsilon nonnegative small).mixed.play residual =
      F.mixed.play (pinnedTremble free pinned reference residual epsilon nonnegative small) := by
  change ((independentProduct residual).bind fun profile =>
    (independentProduct fun who =>
      responseKernel free pinned reference epsilon nonnegative small who (profile who)).bind
        F.play) = _
  rw [← PMF.bind_bind, independentProduct_bind]
  simp only [response_kernel_law]

omit [Fintype ι] in
private theorem pinned_tremble_update (free : Finset ι)
    (pinned reference residual : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (who : ι) (active : who ∈ free) (alternative : PMF (F.sig.Strategy who)) :
    pinnedTremble free pinned reference (Profile.update residual who alternative)
        epsilon nonnegative small =
      Profile.update (pinnedTremble free pinned reference residual epsilon nonnegative small)
        who (mix epsilon nonnegative small (reference who) alternative) := by
  funext player
  by_cases same : player = who
  · subst player
    simp only [pinnedTremble, active, ↓reduceIte, Profile.update_same]
  · simp only [pinnedTremble, Profile.update_of_ne _ _ same]

/-- Expected utility is affine in one player's mixture of two laws. -/
theorem expectedUtility_mixed_update_mix [∀ who, Finite (F.sig.Strategy who)]
    (utility : F.sig.Outcome → ι → ℝ) (integrable : F.HasIntegrableUtility utility)
    (profile : Profile F.sig.mixed) (who : ι)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon ≤ 1)
    (first second : PMF (F.sig.Strategy who)) :
    expectedUtility utility who (F.mixed.play
      (Profile.update profile who (mix epsilon nonnegative small first second))) =
      epsilon * expectedUtility utility who (F.mixed.play (Profile.update profile who first)) +
        (1 - epsilon) *
          expectedUtility utility who (F.mixed.play (Profile.update profile who second)) := by
  have mixed := integrable.mixed_of_finite (F := F)
  rw [F.mixed_play_update profile who (mix epsilon nonnegative small first second), mix_bind,
    ← F.mixed_play_update profile who first, ← F.mixed_play_update profile who second]
  exact expect_mix _ _ _ _ _ _ (mixed who _) (mixed who _)

/-- **Simultaneous residual best responses.** Finite Nash existence selects the
residual laws of all free players together; each residual is optimal against
the same perturbed opponents. The played profile includes the compulsory
trembles, so it is not claimed to be an unconstrained equilibrium. -/
theorem exists_pinned_tremble_bestResponses [∀ who, Finite (F.sig.Strategy who)]
    [∀ who, Nonempty (F.sig.Strategy who)]
    (utility : F.sig.Outcome → ι → ℝ) (integrable : F.HasIntegrableUtility utility)
    (free : Finset ι) (pinned reference : Profile F.sig.mixed)
    (epsilon : ℝ) (nonnegative : 0 ≤ epsilon) (small : epsilon < 1) :
    ∃ residual : Profile F.sig.mixed, ∀ who ∈ free,
      ∀ alternative : PMF (F.sig.Strategy who),
        expectedUtility utility who (F.mixed.play
          (Profile.update
            (pinnedTremble free pinned reference residual epsilon nonnegative small.le)
            who alternative)) ≤
        expectedUtility utility who (F.mixed.play
          (Profile.update
            (pinnedTremble free pinned reference residual epsilon nonnegative small.le)
            who (residual who))) := by
  let _ (who : ι) : Fintype (F.sig.Strategy who) := Fintype.ofFinite _
  let _ (who : ι) : Fintype
      ((responseGame free pinned reference epsilon nonnegative small.le).sig.Strategy who) :=
    inferInstanceAs (Fintype (F.sig.Strategy who))
  let _ (who : ι) : Nonempty
      ((responseGame free pinned reference epsilon nonnegative small.le).sig.Strategy who) :=
    inferInstanceAs (Nonempty (F.sig.Strategy who))
  have responseIntegrable :
      (responseGame free pinned reference epsilon nonnegative small.le).HasIntegrableUtility
        utility := fun who profile => integrable.mixed_of_finite who _
  obtain ⟨residual, optimal⟩ := exists_isNash_mixed
    (F := responseGame free pinned reference epsilon nonnegative small.le) utility
    responseIntegrable
  refine ⟨residual, fun who active alternative => ?_⟩
  have comparison := (isNash_iff
    (F := (responseGame free pinned reference epsilon nonnegative small.le).mixed)
    (weaklyPrefers := euPreference utility) residual).mp optimal who alternative
  replace comparison := (euPreference_iff _ _ _ _ (responseIntegrable.mixed_of_finite who _)
    (responseIntegrable.mixed_of_finite who _)).mp comparison
  change expectedUtility utility who
    ((responseGame free pinned reference epsilon nonnegative small.le).mixed.play
      (Profile.update residual who alternative)) ≤
    expectedUtility utility who
      ((responseGame free pinned reference epsilon nonnegative small.le).mixed.play residual)
    at comparison
  replace comparison : expectedUtility utility who (F.mixed.play
      (pinnedTremble free pinned reference (Profile.update residual who alternative)
        epsilon nonnegative small.le)) ≤
      expectedUtility utility who (F.mixed.play
        (pinnedTremble free pinned reference residual epsilon nonnegative small.le)) := by
    rw [← response_game_law free pinned reference (Profile.update residual who alternative),
      ← response_game_law free pinned reference residual]
    exact comparison
  rw [pinned_tremble_update free pinned reference residual epsilon nonnegative small.le
      who active alternative] at comparison
  have self : pinnedTremble free pinned reference residual epsilon nonnegative small.le =
      Profile.update (pinnedTremble free pinned reference residual epsilon nonnegative small.le)
        who (mix epsilon nonnegative small.le (reference who) (residual who)) := by
    conv_lhs => rw [← Profile.update_eq_self residual who]
    exact pinned_tremble_update free pinned reference residual epsilon nonnegative small.le
      who active (residual who)
  let played := pinnedTremble free pinned reference residual epsilon nonnegative small.le
  have left := expectedUtility_mixed_update_mix utility integrable played who epsilon
    nonnegative small.le (reference who) alternative
  have right := expectedUtility_mixed_update_mix utility integrable played who epsilon
    nonnegative small.le (reference who) (residual who)
  have selfValue : expectedUtility utility who (F.mixed.play played) =
      expectedUtility utility who (F.mixed.play (Profile.update played who
        (mix epsilon nonnegative small.le (reference who) (residual who)))) :=
    congrArg (fun profile => expectedUtility utility who (F.mixed.play profile)) self
  have combined : expectedUtility utility who (F.mixed.play (Profile.update played who
        (mix epsilon nonnegative small.le (reference who) alternative))) ≤
      expectedUtility utility who (F.mixed.play (Profile.update played who
        (mix epsilon nonnegative small.le (reference who) (residual who)))) :=
    comparison.trans_eq selfValue
  rw [left, right] at combined
  exact (mul_le_mul_iff_right₀ (sub_pos.mpr small)).mp (by linarith)

omit [Fintype ι] in
/-- Pinned trembles are fully mixed when the pinned laws of prescribed players
and the references of free players are. -/
theorem pinnedTremble_fullSupport (free : Finset ι)
    (pinned reference residual : Profile F.sig.mixed)
    (epsilon : ℝ) (positive : 0 < epsilon) (small : epsilon ≤ 1)
    (pinnedFull : ∀ who, who ∉ free → FullSupport (pinned who))
    (referenceFull : ∀ who, who ∈ free → FullSupport (reference who)) :
    ∀ who,
      FullSupport (pinnedTremble free pinned reference residual epsilon positive.le small who) := by
  intro who action
  by_cases active : who ∈ free
  · simp only [pinnedTremble, active, ↓reduceIte]
    exact mem_support_mix_left _ _ _ positive (referenceFull who active action)
  · simpa only [pinnedTremble, active, ↓reduceIte] using pinnedFull who active action

/-- **Perturbed equilibria exist.** With finite strategy sets, every tremble
weight in `[0, 1)` and every reference profile, some profile is an equilibrium
of the perturbation whose lower bounds are the weight times the reference. -/
theorem exists_isPerturbedEq [∀ who, Finite (F.sig.Strategy who)]
    [∀ who, Nonempty (F.sig.Strategy who)]
    (utility : F.sig.Outcome → ι → ℝ) (integrable : F.HasIntegrableUtility utility)
    (reference : Profile F.sig.mixed) (epsilon : ℝ) (nonnegative : 0 ≤ epsilon)
    (small : epsilon < 1) :
    ∃ profile : Profile F.sig.mixed,
      F.IsPerturbedEq (euPreference utility)
        (fun who action => epsilon * (reference who action).toReal) profile := by
  obtain ⟨residual, optimal⟩ := exists_pinned_tremble_bestResponses utility integrable
    Finset.univ reference reference epsilon nonnegative small
  let played := pinnedTremble Finset.univ reference reference residual epsilon nonnegative
    small.le
  have mixed := integrable.mixed_of_finite (F := F)
  have playedAt (who : ι) :
      played who = mix epsilon nonnegative small.le (reference who) (residual who) :=
    ite_eq_left (Finset.mem_univ who)
  refine ⟨played, (F.isPerturbedEq_iff _ _ _).mpr ⟨fun who action => ?_, ?_⟩⟩
  · rw [playedAt, mix_apply_toReal]
    exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr small.le) ENNReal.toReal_nonneg)
  · intro who replacement respects
    obtain ⟨alternative, rfl⟩ := exists_mix_eq_of_le replacement (reference who) epsilon
      nonnegative small respects
    refine (euPreference_iff _ _ _ _ (mixed who _) (mixed who _)).mpr ?_
    have bound := optimal who (Finset.mem_univ who) alternative
    calc
      _ = epsilon * expectedUtility utility who
            (F.mixed.play (Profile.update played who (reference who))) +
          (1 - epsilon) * expectedUtility utility who
            (F.mixed.play (Profile.update played who alternative)) :=
        expectedUtility_mixed_update_mix utility integrable _ _ _ _ _ _ _
      _ ≤ epsilon * expectedUtility utility who
            (F.mixed.play (Profile.update played who (reference who))) +
          (1 - epsilon) * expectedUtility utility who
            (F.mixed.play (Profile.update played who (residual who))) :=
        add_le_add_right (mul_le_mul_of_nonneg_left bound (sub_nonneg.mpr small.le)) _
      _ = expectedUtility utility who (F.mixed.play (Profile.update played who
            (mix epsilon nonnegative small.le (reference who) (residual who)))) :=
        (expectedUtility_mixed_update_mix utility integrable _ _ _ _ _ _ _).symm
      _ = _ := by rw [← playedAt, Profile.update_eq_self]

/-- **Selten's existence theorem.** Every game with finitely many players and
finite nonempty strategy sets, and with integrable pure play, has a
trembling-hand perfect equilibrium. -/
theorem exists_isTremblingHandPerfect [∀ who, Fintype (F.sig.Strategy who)]
    [∀ who, Nonempty (F.sig.Strategy who)]
    (utility : F.sig.Outcome → ι → ℝ) (integrable : F.HasIntegrableUtility utility) :
    ∃ profile : Profile F.sig.mixed, F.IsTremblingHandPerfect (euPreference utility) profile := by
  let weight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)
  have positive (n : ℕ) : 0 < weight n := by
    dsimp only [weight]
    positivity
  have small (n : ℕ) : weight n < 1 := by
    dsimp only [weight]
    rw [div_lt_one (by positivity)]
    linarith [Nat.cast_nonneg (α := ℝ) n]
  have vanishes : Tendsto weight atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    convert h using 1
    funext n
    simp only [weight, Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  let reference : Profile F.sig.mixed := fun _ => PMF.uniformOfFintype _
  choose approximating equilibrium using fun n => exists_isPerturbedEq utility integrable
    reference (weight n) (positive n).le (small n)
  obtain ⟨limit, subseq, increasing, converges⟩ :=
    exists_subseq_pmfConvergesPointwise_pi (A := fun who => F.sig.Strategy who) approximating
  refine ⟨limit, fun n who action => weight (subseq n) * (reference who action).toReal,
    fun n => approximating (subseq n), fun n => ⟨fun who action => ?_, equilibrium (subseq n)⟩,
    fun who action => ?_, converges⟩
  · refine mul_pos (positive _) (ENNReal.toReal_pos ?_ (PMF.apply_ne_top _ _))
    simp [reference]
  · have limit := (vanishes.comp increasing.tendsto_atTop).mul_const (reference who action).toReal
    rw [zero_mul] at limit
    exact limit

end GameTheory
