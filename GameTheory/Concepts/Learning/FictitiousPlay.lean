/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.Foundations.Convergence
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Fictitious play

Fictitious play (Brown 1951): each player repeatedly plays a best response to the **empirical
frequency** of opponents' past pure actions. This is the belief-learning counterpart of the
payoff-learning no-regret dynamics (`NoRegretToCCE`).

This file gives the structural core: the empirical-marginal belief state and the fictitious-play
predicate on a play sequence (modelled as a predicate, in the library's `IsNash`/`IsStable` style,
rather than a tie-broken construction). The headline convergence theorems (Robinson for zero-sum,
Monderer–Shapley for potential games) are separate, harder developments; what is proved here is the
"limits of fictitious play are Nash" direction.

## Main definitions

* `KernelGame.empiricalMarginal` — player `j`'s empirical action distribution over the first `t`
  rounds
* `KernelGame.belief` — the profile of opponents' empirical marginals entering a round
* `KernelGame.IsFictitiousPlay` — the play sequence best-responds to the empirical beliefs each
  round
-/

namespace GameTheory

open Math.Probability
open scoped BigOperators

namespace KernelGame

variable {ι : Type} [DecidableEq ι] [Fintype ι] (M : KernelGame ι)

/-- The empirical distribution of player `j`'s pure actions over the first `t` rounds: the uniform
    average of the point masses at `a 0 j, …, a (t-1) j`. -/
noncomputable def empiricalMarginal (a : ℕ → M.Profile) (j : ι) (t : ℕ) [NeZero t] :
    PMF (M.Strategy j) :=
  (PMF.uniformOfFintype (Fin t)).bind (fun s => PMF.pure (a (s : ℕ) j))

omit [DecidableEq ι] [Fintype ι] in
open Classical in
/-- The empirical marginal weight is the count of matching past plays divided by
the averaging horizon. -/
theorem empiricalMarginal_apply_toReal
    (a : ℕ → M.Profile) (j : ι) (t : ℕ) [NeZero t] (s : M.Strategy j) :
    ((M.empiricalMarginal a j t) s).toReal =
      ((Finset.univ.filter fun k : Fin t => a (k : ℕ) j = s).card : ℝ) / t := by
  classical
  rw [empiricalMarginal, PMF.bind_apply, tsum_fintype]
  simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, PMF.pure_apply]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    rw [← Finset.mul_sum]
    have hsum :
        (∑ x : Fin t, (if s = a (x : ℕ) j then (1 : ENNReal) else 0).toReal) =
          ((Finset.univ.filter fun k : Fin t => s = a (k : ℕ) j).card : ℝ) := by
      have htoReal :
          (∑ x : Fin t, (if s = a (x : ℕ) j then (1 : ENNReal) else 0).toReal) =
            ∑ x : Fin t, if s = a (x : ℕ) j then (1 : ℝ) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        by_cases hxs : s = a (x : ℕ) j <;> simp [hxs]
      rw [htoReal]
      simp
    change (↑t)⁻¹ *
        (∑ x : Fin t, (if s = a (x : ℕ) j then (1 : ENNReal) else 0).toReal) =
      ((Finset.univ.filter fun k : Fin t => a (k : ℕ) j = s).card : ℝ) / t
    rw [hsum]
    have hcard :
        ((Finset.univ.filter fun k : Fin t => s = a (k : ℕ) j).card : ℝ) =
          ((Finset.univ.filter fun k : Fin t => a (k : ℕ) j = s).card : ℝ) := by
      have hfilter :
          (Finset.univ.filter fun k : Fin t => s = a (k : ℕ) j) =
            (Finset.univ.filter fun k : Fin t => a (k : ℕ) j = s) := by
        ext k
        simp [eq_comm]
      rw [hfilter]
    rw [hcard, div_eq_inv_mul]
  · intro k hk
    by_cases hks : s = a (k : ℕ) j
    · simp [hks, NeZero.ne t]
    · simp [hks]

omit [DecidableEq ι] [Fintype ι] in
open Classical in
/-- The empirical marginal weight can equivalently be counted over `Finset.range t`. -/
theorem empiricalMarginal_apply_toReal_range
    (a : ℕ → M.Profile) (j : ι) (t : ℕ) [NeZero t] (s : M.Strategy j) :
    ((M.empiricalMarginal a j t) s).toReal =
      (((Finset.range t).filter fun k : ℕ => a k j = s).card : ℝ) / t := by
  rw [M.empiricalMarginal_apply_toReal a j t s]
  congr 1
  norm_num
  have himage :
      (Finset.univ.filter fun k : Fin t => a (k : ℕ) j = s).image Fin.val =
        (Finset.range t).filter fun k : ℕ => a k j = s := by
    ext k
    simp [Fin.exists_iff, and_comm]
  have hcard := congrArg Finset.card himage
  rw [Finset.card_image_of_injective _ Fin.val_injective] at hcard
  exact_mod_cast hcard

omit [DecidableEq ι] [Fintype ι] in
open Classical in
/-- Successor recursion for empirical marginal weights, stated pointwise after
coercion to `ℝ`. -/
theorem empiricalMarginal_succ_apply_toReal
    (a : ℕ → M.Profile) (j : ι) (t : ℕ) (s : M.Strategy j) :
    ((M.empiricalMarginal a j (t + 2)) s).toReal =
      ((t + 1 : ℝ) / (t + 2 : ℝ)) *
          ((M.empiricalMarginal a j (t + 1)) s).toReal +
        (if a (t + 1) j = s then (1 : ℝ) / (t + 2 : ℝ) else 0) := by
  rw [M.empiricalMarginal_apply_toReal_range a j (t + 2) s,
    M.empiricalMarginal_apply_toReal_range a j (t + 1) s]
  let c := ((Finset.range (t + 1)).filter fun k : ℕ => a k j = s).card
  have hcard :
      ((Finset.range (t + 2)).filter fun k : ℕ => a k j = s).card =
        c + if a (t + 1) j = s then 1 else 0 := by
    dsimp [c]
    rw [show t + 2 = (t + 1) + 1 by omega, Finset.range_add_one]
    by_cases hlast : a (t + 1) j = s
    · have hfilter :
          (insert (t + 1) (Finset.range (t + 1))).filter (fun k : ℕ => a k j = s) =
            insert (t + 1) ((Finset.range (t + 1)).filter fun k : ℕ => a k j = s) := by
        rw [Finset.filter_insert]
        exact if_pos hlast
      have hnot :
          t + 1 ∉ ((Finset.range (t + 1)).filter fun k : ℕ => a k j = s) := by
        simp [Finset.mem_range]
      rw [hfilter, Finset.card_insert_of_notMem hnot]
      simp [hlast]
    · have hfilter :
          (insert (t + 1) (Finset.range (t + 1))).filter (fun k : ℕ => a k j = s) =
            (Finset.range (t + 1)).filter fun k : ℕ => a k j = s := by
        rw [Finset.filter_insert]
        exact if_neg hlast
      rw [hfilter]
      simp [hlast]
  have ht1 : (t + 1 : ℝ) ≠ 0 := by positivity
  have ht2 : (t + 2 : ℝ) ≠ 0 := by positivity
  by_cases hlast : a (t + 1) j = s
  · have hcard' :
        (((Finset.range (t + 2)).filter fun k : ℕ => a k j = s).card : ℝ) =
          (c : ℝ) + 1 := by
      have hcard_nat :
          ((Finset.range (t + 2)).filter fun k : ℕ => a k j = s).card = c + 1 := by
        simpa [hlast] using hcard
      exact_mod_cast hcard_nat
    simp [hlast, hcard', c]
    field_simp [ht1, ht2]
  · have hcard' :
        (((Finset.range (t + 2)).filter fun k : ℕ => a k j = s).card : ℝ) =
          (c : ℝ) := by
      have hcard_nat :
          ((Finset.range (t + 2)).filter fun k : ℕ => a k j = s).card = c := by
        simpa [hlast] using hcard
      exact_mod_cast hcard_nat
    simp [hlast, hcard', c]
    field_simp [ht1, ht2]

omit [DecidableEq ι] [Fintype ι] in
open Classical in
/-- Successor recursion for expectations under empirical marginals. -/
theorem empiricalMarginal_succ_expect
    (a : ℕ → M.Profile) (j : ι) [Finite (M.Strategy j)]
    (t : ℕ) (f : M.Strategy j → ℝ) :
    expect (M.empiricalMarginal a j (t + 2)) f =
      ((t + 1 : ℝ) / (t + 2 : ℝ)) *
          expect (M.empiricalMarginal a j (t + 1)) f +
        (1 / (t + 2 : ℝ)) * f (a (t + 1) j) := by
  letI : Fintype (M.Strategy j) := Fintype.ofFinite (M.Strategy j)
  rw [expect_eq_sum, expect_eq_sum]
  simp_rw [M.empiricalMarginal_succ_apply_toReal a j t]
  simp_rw [add_mul, mul_assoc]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hδ :
      (∑ s : M.Strategy j,
          (if a (t + 1) j = s then (1 : ℝ) / (t + 2 : ℝ) else 0) * f s) =
        (1 / (t + 2 : ℝ)) * f (a (t + 1) j) := by
    simp_rw [ite_mul, zero_mul]
    rw [Fintype.sum_ite_eq]
  rw [hδ]

/-- The belief profile entering round `t`: each player's empirical marginal over the first `t`
    rounds, viewed as a mixed-strategy profile. -/
noncomputable def belief (a : ℕ → M.Profile) (t : ℕ) [NeZero t] : M.mixedExtension.Profile :=
  fun j => M.empiricalMarginal a j t

/-- A play sequence `a` is **fictitious play** if at every round the pure action played by each
    player is a best response, in the mixed extension, to the opponents' empirical marginals. The
    belief is indexed at `t + 1` (over rounds `0 … t`), so the averaging horizon is always positive;
    round `0` is the unconstrained initial play. -/
def IsFictitiousPlay (a : ℕ → M.Profile) : Prop :=
  ∀ (t : ℕ) (i : ι) (s' : M.Strategy i),
    M.mixedExtension.eu (Function.update (M.belief a (t + 1)) i (PMF.pure (a (t + 1) i))) i
      ≥ M.mixedExtension.eu (Function.update (M.belief a (t + 1)) i (PMF.pure s')) i

open Filter in
omit [DecidableEq ι] [Fintype ι] in
/-- If the empirical marginal of player `who` converges to `x` and `x` assigns positive probability
to a pure action `b`, then `b` is played in infinitely many rounds. (If it were played only finitely
often, its empirical frequency `≤ (N+1)/(t+1) → 0` would contradict the positive limit.) -/
theorem frequently_play_eq_of_belief_converges
    (a : ℕ → M.Profile) (who : ι) (b : M.Strategy who) {x : PMF (M.Strategy who)}
    (hconv : PMFConvergesPointwise (fun t => M.empiricalMarginal a who (t + 1)) x) (hb : x b ≠ 0) :
    ∃ᶠ t in atTop, a (t + 1) who = b := by
  classical
  have hc : (0 : ℝ) < (x b).toReal := ENNReal.toReal_pos hb (PMF.apply_ne_top x b)
  have htend : Tendsto (fun t => ((M.empiricalMarginal a who (t + 1)) b).toReal) atTop
      (nhds ((x b).toReal)) :=
    Math.Probability.pmf_apply_toReal_tendsto_of_tendsto (hconv.apply b)
  by_contra hcon
  rw [not_frequently] at hcon
  obtain ⟨N, hN⟩ := eventually_atTop.1 hcon
  have hbound : ∀ t : ℕ,
      ((M.empiricalMarginal a who (t + 1)) b).toReal ≤ ((N : ℝ) + 1) / ((t + 1 : ℕ) : ℝ) := by
    intro t
    have hcard :
        (Finset.univ.filter fun k : Fin (t + 1) => a (k : ℕ) who = b).card ≤ N + 1 := by
      have hsub : (Finset.univ.filter fun k : Fin (t + 1) => a (k : ℕ) who = b) ⊆
          (Finset.univ.filter fun k : Fin (t + 1) => (k : ℕ) < N + 1) := by
        intro k hk
        rw [Finset.mem_filter] at hk ⊢
        refine ⟨hk.1, ?_⟩
        by_contra hge
        have hge' : N + 1 ≤ (k : ℕ) := not_lt.1 hge
        have hk1 : N ≤ (k : ℕ) - 1 := by omega
        have hne := hN _ hk1
        rw [Nat.sub_add_cancel (by omega)] at hne
        exact hne hk.2
      refine (Finset.card_le_card hsub).trans ?_
      have : (Finset.univ.filter fun k : Fin (t + 1) => (k : ℕ) < N + 1).card
          ≤ (Finset.range (N + 1)).card :=
        Finset.card_le_card_of_injOn (fun k => (k : ℕ))
          (fun k hk => Finset.mem_range.2 (Finset.mem_filter.1 hk).2)
          (fun k1 _ k2 _ h => Fin.val_injective h)
      simpa using this
    rw [M.empiricalMarginal_apply_toReal a who (t + 1) b]
    gcongr
    exact_mod_cast hcard
  have hzero : Tendsto (fun t : ℕ => ((N : ℝ) + 1) / ((t + 1 : ℕ) : ℝ)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat ((N : ℝ) + 1)).comp (tendsto_add_atTop_nat 1)
  have hle : (x b).toReal ≤ 0 :=
    le_of_tendsto_of_tendsto htend hzero (Eventually.of_forall hbound)
  linarith

open Filter in
/-- **Limits of fictitious play are Nash.** If the empirical beliefs of a fictitious-play sequence
converge (pointwise as PMFs) to a mixed profile `x`, then `x` is a Nash equilibrium of the mixed
extension. Fictitious play need not converge in general (Shapley), but *when it does* the limit is a
Nash equilibrium: every action in the support of `x` is played infinitely often, hence (by EU
continuity in the converging beliefs) is a best response to `x`, so `x` mixes only over best
responses. -/
theorem isFictitiousPlay_limit_isNash [∀ i, Finite (M.Strategy i)] [Finite M.Outcome]
    {a : ℕ → M.Profile} (hfp : M.IsFictitiousPlay a) {x : ∀ i, PMF (M.Strategy i)}
    (hconv : ∀ i, PMFConvergesPointwise (fun t => M.belief a (t + 1) i) (x i)) :
    M.mixedExtension.IsNash x := by
  -- every action in the support of `x who` is a best response to `x`
  have hbr : ∀ (who : ι) (b : M.Strategy who), x who b ≠ 0 → ∀ a' : M.Strategy who,
      M.mixedExtension.eu (Function.update x who (PMF.pure a')) who
        ≤ M.mixedExtension.eu (Function.update x who (PMF.pure b)) who := by
    intro who b hb a'
    have hfreq : ∃ᶠ t in atTop, a (t + 1) who = b :=
      M.frequently_play_eq_of_belief_converges a who b (hconv who) hb
    have htb := M.mixedExtension_eu_update_pure_tendsto_of_forall_pmfConvergesPointwise
      (σs := fun t => M.belief a (t + 1)) (σ := x) hconv who b
    have hta := M.mixedExtension_eu_update_pure_tendsto_of_forall_pmfConvergesPointwise
      (σs := fun t => M.belief a (t + 1)) (σ := x) hconv who a'
    by_contra hlt
    rw [not_le] at hlt
    have hDtend := htb.sub hta
    have hneg : M.mixedExtension.eu (Function.update x who (PMF.pure b)) who
        - M.mixedExtension.eu (Function.update x who (PMF.pure a')) who < 0 := by linarith
    have hev := hDtend.eventually (eventually_lt_nhds hneg)
    have hfr : ∃ᶠ t in atTop,
        0 ≤ M.mixedExtension.eu (Function.update (M.belief a (t + 1)) who (PMF.pure b)) who
          - M.mixedExtension.eu (Function.update (M.belief a (t + 1)) who (PMF.pure a')) who := by
      refine hfreq.mono (fun t ht => ?_)
      have hf := hfp t who a'
      rw [ht] at hf
      linarith
    obtain ⟨t, h1, h2⟩ := (hfr.and_eventually hev).exists
    linarith
  -- own-strategy linearity: `eu x who` is the `x who`-average of pure-deviation payoffs
  rw [M.isNash_iff_gains_nonpos]
  intro who a'
  letI : Fintype (M.Strategy who) := Fintype.ofFinite _
  have heu : expect (x who)
      (fun b => M.mixedExtension.eu (Function.update x who (PMF.pure b)) who)
      = M.mixedExtension.eu x who := by
    have h := M.weighted_gain_sum_zero x who
    simp only [mixedGain] at h
    rw [expect_sub, expect_const] at h
    linarith
  rw [mixedGain]
  have hge : M.mixedExtension.eu (Function.update x who (PMF.pure a')) who
      ≤ M.mixedExtension.eu x who := by
    rw [← heu, expect_eq_sum,
      show M.mixedExtension.eu (Function.update x who (PMF.pure a')) who
          = ∑ b, (x who b).toReal *
              M.mixedExtension.eu (Function.update x who (PMF.pure a')) who from by
        rw [← Finset.sum_mul, pmf_toReal_sum_one, one_mul]]
    refine Finset.sum_le_sum (fun b _ => ?_)
    rcases eq_or_ne (x who b) 0 with h0 | h0
    · simp [h0]
    · exact mul_le_mul_of_nonneg_left (hbr who b h0 a') ENNReal.toReal_nonneg
  linarith

end KernelGame

end GameTheory
