/-
# Multiplicative-weights self-play

This opt-in analytic consumer assembles the finite multiplicative-weights bound
with Core's finite independent-self-play bridge.
`GameTheory.Math.OnlineLearning` owns the exponential-potential algebra and
`GameTheory.Math.Probability.OnlineLearning` is the sole adapter that turns its
normalized vectors into canonical ordinary PMF laws.  No second regret or CCE
predicate is introduced here. The module also supplies the finite-law limit
theorem taking convergent fictitious-play empirical beliefs to mixed Nash.
-/

import GameTheory.Core.Learning
import GameTheory.Core.FictitiousPlay
import GameTheory.Analysis.FictitiousPlayPotential
import GameTheory.Math.Probability.Convergence
import GameTheory.Analysis.ExpectedUtility
import GameTheory.Math.Probability.OnlineLearning
import GameTheory.Math.OnlineLearning

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability
open GameTheory.Math
open Filter

universe uι us uo

variable {ι : Type uι} [DecidableEq ι] [Fintype ι]

namespace UtilityGame

variable (G : UtilityGame.{uι, us, uo} ι)
variable [∀ i, Fintype (G.form.sig.Strategy i)] [∀ i, Nonempty (G.form.sig.Strategy i)]
variable (eta : ℝ) (lo : ι → ℝ) (width : ℝ)

/-- Cumulative normalized-gain score of independent multiplicative-weights
self-play.  The recurrence is structural: the round profile is read only from
the preceding score. -/
noncomputable def mwScore (G : UtilityGame.{uι, us, uo} ι)
    [∀ i, Fintype (G.form.sig.Strategy i)] [∀ i, Nonempty (G.form.sig.Strategy i)]
    (eta : ℝ) (lo : ι → ℝ) (width : ℝ)
    (hband : ∀ who outcome,
      G.utility outcome who ∈ Set.Icc (lo who) (lo who + width)) :
    ℕ → ∀ i, G.form.sig.Strategy i → ℝ
  | 0 => fun _ _ => 0
  | t + 1 => fun i action =>
      mwScore G eta lo width hband t i action +
        G.normGain lo width hband
          (fun j => GameTheory.Math.Probability.OnlineLearning.exponentialWeights eta
            (mwScore G eta lo width hband t j)) i action

/-- The independent profile played at a round: each player applies the
canonical finite-law exponential-weights adapter to their score. -/
noncomputable def mwProfile (G : UtilityGame.{uι, us, uo} ι)
    [∀ i, Fintype (G.form.sig.Strategy i)] [∀ i, Nonempty (G.form.sig.Strategy i)]
    (eta : ℝ) (lo : ι → ℝ) (width : ℝ)
    (hband : ∀ who outcome,
      G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (t : ℕ) : Profile G.form.sig.mixed :=
  fun i => GameTheory.Math.Probability.OnlineLearning.exponentialWeights eta
    (mwScore G eta lo width hband t i)

/-- The structural score is the cumulative gain of the trajectory it induces. -/
theorem mwScore_eq_cumGain
    (hband : ∀ who outcome,
      G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (t : ℕ) (who : ι) (action : G.form.sig.Strategy who) :
    mwScore G eta lo width hband t who action =
      OnlineLearning.cumGain
        (fun round => G.normGain lo width hband
          (mwProfile G eta lo width hband round) who) t action := by
  induction t with
  | zero => simp [mwScore, OnlineLearning.cumGain]
  | succ t ih =>
    rw [OnlineLearning.cumGain_succ, ← ih]
    rfl

/-- The round law is exactly the canonical finite-law multiplicative-weights
law on the normalized-gain sequence. -/
theorem mwProfile_eq_multiplicativeWeights
    (hband : ∀ who outcome,
      G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (t : ℕ) (who : ι) :
    mwProfile G eta lo width hband t who =
      GameTheory.Math.Probability.OnlineLearning.multiplicativeWeights eta
        (fun round => G.normGain lo width hband
          (mwProfile G eta lo width hband round) who) t := by
  rw [mwProfile,
    GameTheory.Math.Probability.OnlineLearning.multiplicativeWeights_eq_exponentialWeights]
  congr 1
  funext action
  exact mwScore_eq_cumGain G eta lo width hband t who action

/-- **Finite multiplicative-weights self-play yields an approximate CCE.**
The result is an explicit finite-horizon bound, not a limit assertion. -/
theorem mwSelfPlay_timeAverage_isεCoarseCorrelatedEq {L : ℝ} (heta : 0 < eta)
    (hwidth : 0 < width)
    (hband : ∀ who outcome, G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (hL : ∀ who, Real.log (Fintype.card (G.form.sig.Strategy who)) ≤ L)
    (T : ℕ) [NeZero T] :
    IsεCoarseCorrelatedEq G.form G.utility
      (width * (L / eta + (Real.exp eta - 1 - eta) / eta * T) / T)
      (G.form.timeAverage fun round : Fin T =>
        independentProduct (mwProfile G eta lo width hband (round : ℕ))) := by
  apply G.selfPlay_timeAverage_isεCoarseCorrelatedEq lo width hband
  intro who action
  let gain : ℕ → G.form.sig.Strategy who → ℝ :=
    fun round => G.normGain lo width hband
      (mwProfile G eta lo width hband round) who
  have halgorithm : (∑ round ∈ Finset.range T,
      expect (mwProfile G eta lo width hband round who) (gain round)
        (normGain_integrable G hwidth hband
          (mwProfile G eta lo width hband round) who)) =
      OnlineLearning.algorithmGain eta gain T := by
    rw [OnlineLearning.algorithmGain]
    apply Finset.sum_congr rfl
    intro round _
    let law := mwProfile G eta lo width hband round who
    let f := G.normGain lo width hband (mwProfile G eta lo width hband round) who
    have hlaw := mwProfile_eq_multiplicativeWeights G eta lo width hband round who
    have hguard : PayoffIntegrable law f := normGain_integrable G hwidth hband
      (mwProfile G eta lo width hband round) who
    have hguard' : PayoffIntegrable
        (GameTheory.Math.Probability.OnlineLearning.multiplicativeWeights eta gain round) f :=
      payoffIntegrable_congr_law hlaw hguard
    calc
      expect law f hguard = expect
          (GameTheory.Math.Probability.OnlineLearning.multiplicativeWeights eta gain round)
          f hguard' := expect_congr_law hlaw f hguard hguard'
      _ = OnlineLearning.expected eta gain round f :=
        GameTheory.Math.Probability.OnlineLearning.expect_multiplicativeWeights
          eta gain round f (h := hguard')
  have hscale :
      (∑ round : Fin T,
        (expectedUtility G.utility who
        (G.form.mixed.play
              (Profile.update (mwProfile G eta lo width hband (round : ℕ)) who
                (PMF.pure action)))
            (utilityIntegrable_of_band G lo width hband who _) -
          expectedUtility G.utility who
            (G.form.mixed.play (mwProfile G eta lo width hband (round : ℕ)))
            (utilityIntegrable_of_band G lo width hband who _))) =
      width * (OnlineLearning.cumGain gain T action -
        OnlineLearning.algorithmGain eta gain T) := by
    rw [Fin.sum_univ_eq_sum_range (fun round =>
        expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update (mwProfile G eta lo width hband round) who
              (PMF.pure action)))
          (utilityIntegrable_of_band G lo width hband who _) -
        expectedUtility G.utility who
          (G.form.mixed.play (mwProfile G eta lo width hband round))
          (utilityIntegrable_of_band G lo width hband who _)) T]
    rw [Finset.sum_congr rfl (fun round _ =>
      G.expectedUtility_deviation_eq_width_mul_normGain hwidth hband
        (mwProfile G eta lo width hband round) who action)]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, halgorithm]
    rfl
  rw [hscale]
  have hbound : OnlineLearning.cumGain gain T action - OnlineLearning.algorithmGain eta gain T ≤
      L / eta + (Real.exp eta - 1 - eta) / eta * T := by
    calc
      OnlineLearning.cumGain gain T action - OnlineLearning.algorithmGain eta gain T ≤
          OnlineLearning.externalRegret eta gain T :=
        OnlineLearning.fixedActionRegret_le_externalRegret eta gain T action
      _ ≤ Real.log (Fintype.card (G.form.sig.Strategy who)) / eta +
          (Real.exp eta - 1 - eta) / eta * T :=
        OnlineLearning.externalRegret_le heta
          (fun round candidate =>
            G.normGain_mem_Icc hwidth hband
              (mwProfile G eta lo width hband round) who candidate) T
      _ ≤ L / eta + (Real.exp eta - 1 - eta) / eta * T := by
        have hfirst : Real.log (Fintype.card (G.form.sig.Strategy who)) / eta ≤ L / eta :=
          (div_le_div_iff_of_pos_right heta).2 (hL who)
        linarith
  exact mul_le_mul_of_nonneg_left hbound hwidth.le

/-- **Square-root multiplicative-weights rate.** Choosing the learning rate
`sqrt (L / T)` turns a common positive upper bound `L` on log action counts
into the explicit average-regret rate `2 * width * sqrt (L * T) / T`. -/
theorem mwSelfPlay_timeAverage_isεCoarseCorrelatedEq_sqrt {L : ℝ}
    (T : ℕ) [NeZero T] (hLpos : 0 < L) (hLT : L ≤ (T : ℝ))
    (hwidth : 0 < width)
    (hband : ∀ who outcome, G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (hL : ∀ who, Real.log (Fintype.card (G.form.sig.Strategy who)) ≤ L) :
    IsεCoarseCorrelatedEq G.form G.utility
      (width * (2 * Real.sqrt (L * T)) / T)
      (G.form.timeAverage fun round : Fin T =>
        independentProduct
          (mwProfile G (Real.sqrt (L / T)) lo width hband (round : ℕ))) := by
  apply G.selfPlay_timeAverage_isεCoarseCorrelatedEq lo width hband
  intro who action
  let gain : ℕ → G.form.sig.Strategy who → ℝ :=
    fun round => G.normGain lo width hband
      (mwProfile G (Real.sqrt (L / T)) lo width hband round) who
  have halgorithm :
      (∑ round ∈ Finset.range T,
        expect (mwProfile G (Real.sqrt (L / T)) lo width hband round who)
          (gain round) (normGain_integrable G hwidth hband
            (mwProfile G (Real.sqrt (L / T)) lo width hband round) who)) =
        OnlineLearning.algorithmGain (Real.sqrt (L / T)) gain T := by
    rw [OnlineLearning.algorithmGain]
    apply Finset.sum_congr rfl
    intro round _
    let law := mwProfile G (Real.sqrt (L / T)) lo width hband round who
    let f := G.normGain lo width hband
      (mwProfile G (Real.sqrt (L / T)) lo width hband round) who
    have hlaw := mwProfile_eq_multiplicativeWeights G
      (Real.sqrt (L / T)) lo width hband round who
    have hguard : PayoffIntegrable law f := normGain_integrable G hwidth hband
      (mwProfile G (Real.sqrt (L / T)) lo width hband round) who
    have hguard' : PayoffIntegrable
        (GameTheory.Math.Probability.OnlineLearning.multiplicativeWeights
          (Real.sqrt (L / T)) gain round) f := payoffIntegrable_congr_law hlaw hguard
    calc
      expect law f hguard = expect
          (GameTheory.Math.Probability.OnlineLearning.multiplicativeWeights
            (Real.sqrt (L / T)) gain round) f hguard' :=
        expect_congr_law hlaw f hguard hguard'
      _ = OnlineLearning.expected (Real.sqrt (L / T)) gain round f :=
        GameTheory.Math.Probability.OnlineLearning.expect_multiplicativeWeights
          (Real.sqrt (L / T)) gain round f (h := hguard')
  have hscale :
      (∑ round : Fin T,
        (expectedUtility G.utility who
        (G.form.mixed.play
              (Profile.update
                (mwProfile G (Real.sqrt (L / T)) lo width hband (round : ℕ)) who
                (PMF.pure action)))
            (utilityIntegrable_of_band G lo width hband who _) -
          expectedUtility G.utility who
            (G.form.mixed.play
              (mwProfile G (Real.sqrt (L / T)) lo width hband (round : ℕ)))
            (utilityIntegrable_of_band G lo width hband who _))) =
        width * (OnlineLearning.cumGain gain T action -
          OnlineLearning.algorithmGain (Real.sqrt (L / T)) gain T) := by
    rw [Fin.sum_univ_eq_sum_range (fun round =>
        expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update
              (mwProfile G (Real.sqrt (L / T)) lo width hband round) who
              (PMF.pure action)))
          (utilityIntegrable_of_band G lo width hband who _) -
        expectedUtility G.utility who
          (G.form.mixed.play
            (mwProfile G (Real.sqrt (L / T)) lo width hband round))
          (utilityIntegrable_of_band G lo width hband who _)) T]
    rw [Finset.sum_congr rfl (fun round _ =>
      G.expectedUtility_deviation_eq_width_mul_normGain hwidth hband
        (mwProfile G (Real.sqrt (L / T)) lo width hband round) who action)]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, halgorithm]
    rfl
  rw [hscale]
  have hbound :
      OnlineLearning.cumGain gain T action -
          OnlineLearning.algorithmGain (Real.sqrt (L / T)) gain T ≤
        2 * Real.sqrt (L * T) := by
    calc
      OnlineLearning.cumGain gain T action -
          OnlineLearning.algorithmGain (Real.sqrt (L / T)) gain T ≤
          OnlineLearning.externalRegret (Real.sqrt (L / T)) gain T :=
        OnlineLearning.fixedActionRegret_le_externalRegret
          (Real.sqrt (L / T)) gain T action
      _ ≤ 2 * Real.sqrt (L * T) :=
        OnlineLearning.externalRegret_le_sqrt hLpos T hLT (hL who)
          (fun round candidate =>
            G.normGain_mem_Icc hwidth hband
              (mwProfile G (Real.sqrt (L / T)) lo width hband round) who candidate)
  exact mul_le_mul_of_nonneg_left hbound hwidth.le

/-- The finite MW trajectory exhibits a canonical approximate CCE at every
positive horizon. -/
theorem exists_mwSelfPlay_isεCoarseCorrelatedEq {L : ℝ} (heta : 0 < eta)
    (hwidth : 0 < width)
    (hband : ∀ who outcome, G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (hL : ∀ who, Real.log (Fintype.card (G.form.sig.Strategy who)) ≤ L)
    (T : ℕ) [NeZero T] :
    ∃ law : PMF (Profile G.form.sig),
      IsεCoarseCorrelatedEq G.form G.utility
        (width * (L / eta + (Real.exp eta - 1 - eta) / eta * T) / T) law := by
  exact ⟨_, mwSelfPlay_timeAverage_isεCoarseCorrelatedEq G eta lo width
    heta hwidth hband hL T⟩

/-- **Arbitrarily accurate finite MW self-play.** For any positive tolerance,
a concrete rate and finite horizon yield a canonical approximate CCE.  The
proof uses only a finite-horizon exponential remainder estimate. -/
theorem mwSelfPlay_exists_isεCoarseCorrelatedEq_of_pos {L : ℝ}
    (hwidth : 0 < width)
    (hband : ∀ who outcome, G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (hL : ∀ who, Real.log (Fintype.card (G.form.sig.Strategy who)) ≤ L)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ law : PMF (Profile G.form.sig),
      IsεCoarseCorrelatedEq G.form G.utility epsilon law := by
  have htwiceWidth : (0 : ℝ) < 2 * width := by linarith
  set eta₀ : ℝ := min 1 (epsilon / (2 * width)) with heta₀
  have heta₀pos : 0 < eta₀ := lt_min one_pos (by positivity)
  have heta₀one : eta₀ ≤ 1 := min_le_left _ _
  have heta₀epsilon : eta₀ ≤ epsilon / (2 * width) := min_le_right _ _
  have heta₀epsilon' : eta₀ * (2 * width) ≤ epsilon :=
    (le_div_iff₀ htwiceWidth).1 heta₀epsilon
  obtain ⟨T', hT'⟩ := exists_nat_ge (2 * width * L / (eta₀ * epsilon))
  have : NeZero (T' + 1) := ⟨Nat.succ_ne_zero _⟩
  have hTpos : (0 : ℝ) < ((T' + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos T'
  refine ⟨G.form.timeAverage (fun round : Fin (T' + 1) =>
    independentProduct (mwProfile G eta₀ lo width hband (round : ℕ))), ?_⟩
  have hMW := mwSelfPlay_timeAverage_isεCoarseCorrelatedEq G eta₀ lo width heta₀pos hwidth
    hband hL (T' + 1)
  rw [G.isεCoarseCorrelatedEq_iff_externalRegret_le] at hMW ⊢
  intro who action
  obtain ⟨hbase, hdeviation, hregret⟩ := hMW who action
  refine ⟨hbase, hdeviation, ?_⟩
  apply le_trans hregret
  have hremainder : (Real.exp eta₀ - 1 - eta₀) / eta₀ ≤ eta₀ := by
    rw [div_le_iff₀ heta₀pos]
    have hsq := OnlineLearning.exp_sub_one_sub_self_le_sq heta₀pos.le heta₀one
    rw [pow_two] at hsq
    linarith
  have hTlarge : 2 * width * L ≤ ((T' + 1 : ℕ) : ℝ) * (eta₀ * epsilon) := by
    have h : 2 * width * L / (eta₀ * epsilon) ≤ ((T' + 1 : ℕ) : ℝ) :=
      le_trans hT' (by exact_mod_cast Nat.le_succ T')
    rwa [div_le_iff₀ (by positivity)] at h
  have hfirst : width * L / (eta₀ * ((T' + 1 : ℕ) : ℝ)) ≤ epsilon / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hTlarge]
  have hsecond : width * eta₀ ≤ epsilon / 2 := by
    nlinarith [heta₀epsilon']
  have hsplit :
      width * (L / eta₀ + (Real.exp eta₀ - 1 - eta₀) / eta₀ * ((T' + 1 : ℕ) : ℝ)) /
          ((T' + 1 : ℕ) : ℝ) =
        width * L / (eta₀ * ((T' + 1 : ℕ) : ℝ)) +
          width * ((Real.exp eta₀ - 1 - eta₀) / eta₀) := by
    have heta₀ne : eta₀ ≠ 0 := heta₀pos.ne'
    have hTne : ((T' + 1 : ℕ) : ℝ) ≠ 0 := hTpos.ne'
    field_simp
  rw [hsplit]
  have hscaledRemainder : width * ((Real.exp eta₀ - 1 - eta₀) / eta₀) ≤
      width * eta₀ :=
    mul_le_mul_of_nonneg_left hremainder hwidth.le
  linarith [hfirst, hsecond, hscaledRemainder]

end UtilityGame

/-! ## Fictitious-play limits -/

namespace UtilityGame

variable {G : UtilityGame.{uι, us, uo} ι}
variable [∀ i, Fintype (G.form.sig.Strategy i)]

omit [DecidableEq ι] [Fintype ι] [∀ i, Fintype (G.form.sig.Strategy i)] in
/-- If an empirical marginal converges to a law that gives an action positive
mass, that action occurs in infinitely many positive-index rounds. -/
theorem frequently_play_eq_of_empiricalMarginal_converges
    (history : ℕ → Profile G.form.sig) (who : ι)
    (action : G.form.sig.Strategy who) (target : PMF (G.form.sig.Strategy who))
    (hconverges : PMFConvergesPointwise
      (fun t => G.form.empiricalMarginal history who (t + 1)) target)
    (haction : action ∈ target.support) :
    ∃ᶠ t in atTop, history (t + 1) who = action := by
  classical
  have hpositive : 0 < (target action).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨
      (PMF.apply_pos_iff target action).2 haction,
      lt_top_iff_ne_top.mpr (PMF.apply_ne_top target action)⟩
  by_contra hnot
  rw [not_frequently] at hnot
  obtain ⟨N, hN⟩ := eventually_atTop.1 hnot
  have hbound : ∀ t : ℕ,
      (G.form.empiricalMarginal history who (t + 1) action).toReal ≤
        ((N : ℝ) + 1) / ((t + 1 : ℕ) : ℝ) := by
    intro t
    have hcard :
        (Finset.univ.filter fun k : Fin (t + 1) => history k who = action).card ≤ N + 1 := by
      have hsub :
          (Finset.univ.filter fun k : Fin (t + 1) => history k who = action) ⊆
            (Finset.univ.filter fun k : Fin (t + 1) => k.val < N + 1) := by
        intro k hk
        rw [Finset.mem_filter] at hk ⊢
        refine ⟨hk.1, ?_⟩
        by_contra hge
        have hge' : N + 1 ≤ k.val := not_lt.1 hge
        have hk1 : N ≤ k.val - 1 := by omega
        have hne := hN _ hk1
        rw [Nat.sub_add_cancel (by omega)] at hne
        exact hne hk.2
      refine (Finset.card_le_card hsub).trans ?_
      have hinjected :
          (Finset.univ.filter fun k : Fin (t + 1) => k.val < N + 1).card ≤
            (Finset.range (N + 1)).card :=
        Finset.card_le_card_of_injOn (fun k => k.val)
          (fun k hk => Finset.mem_range.2 (Finset.mem_filter.1 hk).2)
          (fun _ _ _ _ h => Fin.val_injective h)
      simpa using hinjected
    rw [G.form.empiricalMarginal_prob, ENNReal.toReal_div]
    simp only [ENNReal.toReal_natCast]
    gcongr
    exact_mod_cast hcard
  have hzero : Tendsto
      (fun t : ℕ => ((N : ℝ) + 1) / ((t + 1 : ℕ) : ℝ))
      atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat ((N : ℝ) + 1)).comp
      (tendsto_add_atTop_nat 1)
  have hle : (target action).toReal ≤ 0 :=
    le_of_tendsto_of_tendsto (hconverges.toReal action) hzero
      (Eventually.of_forall hbound)
  linarith

/-- **Every pointwise limit of fictitious-play empirical beliefs is a mixed
Nash equilibrium.** Positive limiting mass forces an action to occur
infinitely often; the roundwise best-response inequalities then pass to the
limit by finite-law continuity. -/
theorem expectedUtility_update_pure_tendsto_of_actual_guards
    {sequence : ℕ → Profile G.form.sig.mixed}
    {target : Profile G.form.sig.mixed}
    (hconverges : ∀ i, PMFConvergesPointwise
      (fun n => sequence n i) (target i))
    (who : ι) (action : G.form.sig.Strategy who)
    (hsequence : ∀ n, UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update (sequence n) who (PMF.pure action)))) :
    ∃ htarget : UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update target who (PMF.pure action))),
      Tendsto
        (fun n => expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update (sequence n) who (PMF.pure action)))
          (hsequence n)) atTop
        (nhds (expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update target who (PMF.pure action))) htarget)) := by
  let source : ℕ → PMF (Profile G.form.sig) :=
    fun n => independentProduct (sequence n)
  let targetSource : PMF (Profile G.form.sig) := independentProduct target
  let kernel : Profile G.form.sig → PMF G.form.sig.Outcome := fun profile =>
    G.form.play (Profile.update profile who action)
  have hsource : PMFConvergesPointwise source targetSource :=
    PMFConvergesPointwise.independentProduct hconverges
  have hlaw (n : ℕ) :
      G.form.mixed.play (Profile.update (sequence n) who (PMF.pure action)) =
        (source n).bind kernel := by
    simpa only [source, kernel] using
      mixed_play_update_pure_eq_bind (F := G.form) (sequence n) who action
  have hbind (n : ℕ) : UtilityIntegrable G.utility who ((source n).bind kernel) :=
    payoffIntegrable_congr_law (hlaw n) (hsequence n)
  have htargetBind : UtilityIntegrable G.utility who (targetSource.bind kernel) :=
    hsource.payoffIntegrable_bind_finite kernel (fun outcome => G.utility outcome who)
      hbind
  have hlawTarget : G.form.mixed.play (Profile.update target who (PMF.pure action)) =
      targetSource.bind kernel := by
    simpa only [targetSource, kernel] using
      mixed_play_update_pure_eq_bind (F := G.form) target who action
  have htarget := payoffIntegrable_congr_law hlawTarget.symm htargetBind
  have hlimit := hsource.expect_bind_finite_of_sequence_integrable kernel
    (fun outcome => G.utility outcome who) hbind
  have hseqEq : (fun n => expectedUtility G.utility who
      (G.form.mixed.play (Profile.update (sequence n) who (PMF.pure action)))
      (hsequence n)) =
      (fun n => expect ((source n).bind kernel)
        (fun outcome => G.utility outcome who) (hbind n)) := by
    funext n
    exact expectedUtility_congr_law G.utility who (hlaw n)
      (hsequence n) (hbind n)
  have htargetEq : expectedUtility G.utility who
      (G.form.mixed.play (Profile.update target who (PMF.pure action))) htarget =
      expect (targetSource.bind kernel) (fun outcome => G.utility outcome who) htargetBind :=
    expectedUtility_congr_law G.utility who hlawTarget htarget htargetBind
  refine ⟨htarget, ?_⟩
  rw [hseqEq, htargetEq]
  exact hlimit

theorem IsFictitiousPlay.limit_isNash
    {history : ℕ → Profile G.form.sig} (hplay : G.IsFictitiousPlay history)
    {target : Profile G.form.sig.mixed}
    (hconverges : ∀ i, PMFConvergesPointwise
      (fun t => G.form.empiricalBelief history (t + 1) i) (target i)) :
    IsNash G.form.mixed (euPreference G.utility) target := by
  have hbest : ∀ (who : ι) (action : G.form.sig.Strategy who),
      action ∈ (target who).support → ∀ alternative : G.form.sig.Strategy who,
        euPreference G.utility who
          (G.form.mixed.play
            (Profile.update target who (PMF.pure action)))
          (G.form.mixed.play
            (Profile.update target who (PMF.pure alternative))) := by
    intro who action haction alternative
    have hcoordinate : PMFConvergesPointwise
        (fun t => G.form.empiricalMarginal history who (t + 1)) (target who) := by
      simpa only [GameForm.empiricalBelief] using hconverges who
    have hfrequent : ∃ᶠ t in atTop, history (t + 1) who = action :=
      G.frequently_play_eq_of_empiricalMarginal_converges
        history who action (target who) hcoordinate haction
    have hsequence (candidate : G.form.sig.Strategy who) (t : ℕ) :
        UtilityIntegrable G.utility who
          (G.form.mixed.play
            (Profile.update (G.form.empiricalBelief history (t + 1)) who
              (PMF.pure candidate))) :=
      UtilityGame.IsFictitiousPlay.deviation_integrable (G := G) hplay t who
        (PMF.pure candidate)
    obtain ⟨hactionGuard, hactionTendsto⟩ :=
      G.expectedUtility_update_pure_tendsto_of_actual_guards
        (fun i => hconverges i) who action (hsequence action)
    obtain ⟨haltGuard, halternativeTendsto⟩ :=
      G.expectedUtility_update_pure_tendsto_of_actual_guards
        (fun i => hconverges i) who alternative (hsequence alternative)
    by_contra hpreferred
    have hnotle : ¬ expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update target who (PMF.pure alternative))) haltGuard ≤
        expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update target who (PMF.pure action))) hactionGuard :=
      fun hle => hpreferred ((euPreference_iff G.utility who
        (G.form.mixed.play (Profile.update target who (PMF.pure action)))
        (G.form.mixed.play (Profile.update target who (PMF.pure alternative)))
        hactionGuard haltGuard).2 hle)
    have hdifference := hactionTendsto.sub halternativeTendsto
    have hnegative :
        expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update target who (PMF.pure action))) hactionGuard -
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update target who (PMF.pure alternative))) haltGuard < 0 := by
      have hlt := not_le.mp hnotle
      linarith
    have heventuallyNegative :=
      hdifference.eventually (eventually_lt_nhds hnegative)
    have hfrequentlyNonnegative : ∃ᶠ t in atTop,
        0 ≤ expectedUtility G.utility who
              (G.form.mixed.play
                (Profile.update (G.form.empiricalBelief history (t + 1)) who
                  (PMF.pure action))) (hsequence action t) -
            expectedUtility G.utility who
              (G.form.mixed.play
                (Profile.update (G.form.empiricalBelief history (t + 1)) who
                  (PMF.pure alternative))) (hsequence alternative t) := by
      refine hfrequent.mono fun t ht => ?_
      have hround :=
        (UtilityGame.IsFictitiousPlay.isBestResponse (G := G) hplay t who)
          (PMF.pure alternative)
      rw [euPreference_apply, ht] at hround
      rcases hround with ⟨_, _, hround⟩
      linarith
    obtain ⟨t, hnonnegative, hnegativeAt⟩ :=
      (hfrequentlyNonnegative.and_eventually heventuallyNegative).exists
    linarith
  have hpure : ∀ who action, UtilityIntegrable G.utility who
      (G.form.mixed.play (Profile.update target who (PMF.pure action))) := by
    intro who action
    obtain ⟨hguard, -⟩ := G.expectedUtility_update_pure_tendsto_of_actual_guards
      (fun i => hconverges i) who action
        (fun t => UtilityGame.IsFictitiousPlay.deviation_integrable (G := G)
          hplay t who (PMF.pure action))
    exact hguard
  have hbase : ∀ who, UtilityIntegrable G.utility who (G.form.mixed.play target) :=
    G.mixedUtilityIntegrable_of_finite_actions target hpure
  have hdeviation : ∀ who replacement, UtilityIntegrable G.utility who
      (G.form.mixed.play (Profile.update target who replacement)) :=
    G.mixedDeviationIntegrable_of_finite_actions target hpure
  rw [isNash_mixed_iff target hdeviation]
  intro who alternative
  let value : G.form.sig.Strategy who → ℝ := fun action =>
    expectedUtility G.utility who
      (G.form.mixed.play (Profile.update target who (PMF.pure action)))
      (hpure who action)
  have houter : PayoffIntegrable (target who) value :=
    payoffIntegrable_bind_conditionalExpectation (target who)
      (fun action => G.form.mixed.play
        (Profile.update target who (PMF.pure action)))
      (fun outcome => G.utility outcome who)
      (by
        have hlaw : G.form.mixed.play target = (target who).bind fun action =>
            G.form.mixed.play (Profile.update target who (PMF.pure action)) := by
          simpa only using mixed_play_update_self G.form target who
        rw [← hlaw]
        exact hbase who)
      (hpure who)
  have hconstant : PayoffIntegrable (target who) (fun _ =>
      expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update target who (PMF.pure alternative)))
        (hpure who alternative)) := payoffIntegrable_constant _ _
  have hle : expectedUtility G.utility who
      (G.form.mixed.play
        (Profile.update target who (PMF.pure alternative)))
      (hpure who alternative) ≤
      expectedUtility G.utility who (G.form.mixed.play target) (hbase who) := by
    calc
      _ = expect (target who) (fun _ =>
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update target who (PMF.pure alternative)))
            (hpure who alternative)) hconstant :=
          (expect_constant (target who) _ hconstant).symm
      _ ≤ expect (target who) value houter :=
          expect_mono (fun action ha =>
            (euPreference_iff G.utility who
              (G.form.mixed.play
                (Profile.update target who (PMF.pure action)))
              (G.form.mixed.play
                (Profile.update target who (PMF.pure alternative)))
              (hpure who action) (hpure who alternative)).mp
                (hbest who action ha alternative)) hconstant houter
      _ = expectedUtility G.utility who (G.form.mixed.play target) (hbase who) := by
        exact (expectedUtility_mixed_eq_expect G.form G.utility target who
          (hbase who) (hpure who)).symm
  exact (euPreference_iff G.utility who (G.form.mixed.play target)
    (G.form.mixed.play (Profile.update target who (PMF.pure alternative)))
    (hbase who) (hpure who alternative)).2 hle

end UtilityGame

end GameTheory
