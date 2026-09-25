/-
# Finite no-regret learning

External regret is defined from the canonical unilateral profile update and the
accepted `GameForm` play law. Approximate coarse correlated equilibrium is the
same utility comparison with an additive tolerance; it is not a second
deviation or correlation model.

The finite-horizon theorem is pure averaging. No strategy carrier, outcome
carrier, or player type needs to be finite. Only the averaging index `Fin T`
is enumerated; the actual laws carry operation-local integration guards.

Primary references: Y. Freund and R. E. Schapire, “A Decision-Theoretic
Generalization of On-Line Learning,” EuroCOLT 1995; S. Hart and A. Mas-Colell,
“A Simple Adaptive Procedure Leading to Correlated Equilibrium,”
*Econometrica* 68 (2000).
-/

import GameTheory.Core.Utility
import GameTheory.Core.Mixed
import GameTheory.Math.Probability.Uniform

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι}

/-- An `ε`-coarse correlated equilibrium is the canonical coarse correlated
equilibrium predicate for expected utility relaxed by `ε`. -/
def IsεCoarseCorrelatedEq [DecidableEq ι]
    (F : GameForm.{uι, us, uo} ι) (utility : Utility F.sig) (ε : ℝ)
    (statusQuo : PMF (Profile F.sig)) : Prop :=
  IsCoarseCorrelatedEq F (euPreferenceWithin ε utility) statusQuo

namespace UtilityGame

variable [DecidableEq ι]

/-- Expected gain from replacing one player's recommendation by a fixed
strategy. Positive values mean that the constant deviation is profitable. -/
def externalRegret (G : UtilityGame.{uι, us, uo} ι)
    (statusQuo : PMF (Profile G.form.sig)) (who : ι)
    (replacement : G.form.sig.Strategy who)
    (hbase : UtilityIntegrable G.utility who (G.form.outcomeLaw statusQuo))
    (hdeviation : UtilityIntegrable G.utility who
      (statusQuo.bind fun profile =>
        G.form.play (Profile.update profile who replacement))) : ℝ :=
  expectedUtility G.utility who
      (statusQuo.bind fun profile =>
        G.form.play (Profile.update profile who replacement)) hdeviation -
    expectedUtility G.utility who (G.form.outcomeLaw statusQuo) hbase

/-- External regret is the status-quo expectation of pointwise deviation
gain. This is the affine form used by finite time averaging. -/
theorem externalRegret_eq_expect_gain (G : UtilityGame.{uι, us, uo} ι)
    (statusQuo : PMF (Profile G.form.sig)) (who : ι)
    (replacement : G.form.sig.Strategy who)
    (hbase : UtilityIntegrable G.utility who (G.form.outcomeLaw statusQuo))
    (hdeviation : UtilityIntegrable G.utility who
      (statusQuo.bind fun profile =>
        G.form.play (Profile.update profile who replacement)))
    (hbaseCond : ∀ profile,
      UtilityIntegrable G.utility who (G.form.play profile))
    (hdevCond : ∀ profile, UtilityIntegrable G.utility who
      (G.form.play (Profile.update profile who replacement))) :
    G.externalRegret statusQuo who replacement hbase hdeviation =
      expect statusQuo (fun profile =>
        expectedUtility G.utility who
            (G.form.play (Profile.update profile who replacement))
            (hdevCond profile) -
          expectedUtility G.utility who (G.form.play profile)
            (hbaseCond profile))
    (payoffIntegrable_sub
          (payoffIntegrable_bind_conditionalExpectation statusQuo
            (fun profile => G.form.play
              (Profile.update profile who replacement))
            (fun outcome => G.utility outcome who) hdeviation hdevCond)
          (payoffIntegrable_bind_conditionalExpectation statusQuo G.form.play
            (fun outcome => G.utility outcome who)
            (by simpa only [GameForm.outcomeLaw] using hbase) hbaseCond)) := by
  calc
    G.externalRegret statusQuo who replacement hbase hdeviation =
        expectedUtility G.utility who
          (statusQuo.bind fun profile => G.form.play
            (Profile.update profile who replacement)) hdeviation -
          expectedUtility G.utility who (G.form.outcomeLaw statusQuo) hbase := rfl
    _ = expect statusQuo (fun profile =>
          expectedUtility G.utility who
            (G.form.play (Profile.update profile who replacement))
            (hdevCond profile))
          (payoffIntegrable_bind_conditionalExpectation statusQuo
            (fun profile => G.form.play
              (Profile.update profile who replacement))
            (fun outcome => G.utility outcome who) hdeviation hdevCond) -
        expect statusQuo (fun profile =>
          expectedUtility G.utility who (G.form.play profile)
            (hbaseCond profile))
          (payoffIntegrable_bind_conditionalExpectation statusQuo G.form.play
            (fun outcome => G.utility outcome who)
            (by simpa only [GameForm.outcomeLaw] using hbase) hbaseCond) := by
        rw [expectedUtility_bind, expectedUtility_outcomeLaw]
    _ = expect statusQuo (fun profile =>
          expectedUtility G.utility who
            (G.form.play (Profile.update profile who replacement))
            (hdevCond profile) -
          expectedUtility G.utility who (G.form.play profile)
            (hbaseCond profile)) _ := by
        symm
        exact expect_sub _ _

/-- The learning-facing external-regret characterization of the canonical
approximate coarse-correlated-equilibrium predicate. -/
theorem isεCoarseCorrelatedEq_iff_externalRegret_le
    (G : UtilityGame.{uι, us, uo} ι) {ε : ℝ}
    {statusQuo : PMF (Profile G.form.sig)} :
    IsεCoarseCorrelatedEq G.form G.utility ε statusQuo ↔
      ∀ who replacement,
        ∃ hbase : UtilityIntegrable G.utility who
            (G.form.outcomeLaw statusQuo),
          ∃ hdeviation : UtilityIntegrable G.utility who
              (statusQuo.bind fun profile =>
                G.form.play (Profile.update profile who replacement)),
            G.externalRegret statusQuo who replacement hbase hdeviation ≤ ε := by
  unfold IsεCoarseCorrelatedEq
  rw [isCoarseCorrelatedEq_iff]
  constructor
  · intro h who replacement
    obtain ⟨hbase, hdeviation, hle⟩ := by
      simpa only [euPreferenceWithin_apply] using h who replacement
    refine ⟨hbase, hdeviation, ?_⟩
    unfold externalRegret
    dsimp only [expectedUtility]
    dsimp only [expectedUtility] at hle
    linarith
  · intro h who replacement
    obtain ⟨hbase, hdeviation, hle⟩ := h who replacement
    refine ⟨hbase, hdeviation, ?_⟩
    dsimp only [externalRegret, expectedUtility] at hle
    dsimp only [expectedUtility]
    linarith

/-- Exact CCE is the zero-tolerance case of the regret formulation. -/
theorem isCoarseCorrelatedEq_iff_isεCoarseCorrelatedEq_zero
    (G : UtilityGame.{uι, us, uo} ι)
    {statusQuo : PMF (Profile G.form.sig)} :
    IsCoarseCorrelatedEq G.form G.preference statusQuo ↔
      IsεCoarseCorrelatedEq G.form G.utility 0 statusQuo := by
  rw [isCoarseCorrelatedEq_iff]
  unfold IsεCoarseCorrelatedEq
  rw [isCoarseCorrelatedEq_iff]
  simp only [UtilityGame.preference, euPreference_apply,
    euPreferenceWithin_apply]
  constructor
  · intro h who replacement
    obtain ⟨hbase, hdev, hle⟩ := by
      simpa only [euPreference_apply] using h who replacement
    refine ⟨hbase, hdev, ?_⟩
    simpa using hle
  · intro h who replacement
    obtain ⟨hbase, hdev, hle⟩ := by
      simpa only [euPreferenceWithin_apply] using h who replacement
    refine ⟨hbase, hdev, ?_⟩
    simpa using hle

end UtilityGame

namespace GameForm

/-- The uniform time average of finitely many laws over pure profiles. -/
def timeAverage (F : GameForm.{uι, us, uo} ι) {T : ℕ} [NeZero T]
    (roundLaw : Fin T → PMF (Profile F.sig)) :
    PMF (Profile F.sig) :=
  (PMF.uniformOfFintype (Fin T)).bind roundLaw

end GameForm

namespace UtilityGame

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- A finite round average preserves integrability of the actual base laws. -/
theorem timeAverage_base_integrable
    (G : UtilityGame.{uι, us, uo} ι) {T : ℕ} [NeZero T]
    (roundLaw : Fin T → PMF (Profile G.form.sig)) (who : ι)
    (hbase : ∀ t, UtilityIntegrable G.utility who
      (G.form.outcomeLaw (roundLaw t))) :
    UtilityIntegrable G.utility who (G.form.outcomeLaw
      (G.form.timeAverage roundLaw)) := by
  simpa only [GameForm.timeAverage, GameForm.outcomeLaw_bind,
    UtilityIntegrable] using
    (payoffIntegrable_bind_of_finite
      (PMF.uniformOfFintype (Fin T))
      (fun t => G.form.outcomeLaw (roundLaw t))
      (fun outcome => G.utility outcome who) hbase)

/-- A finite round average preserves integrability of the actual deviation laws. -/
theorem timeAverage_deviation_integrable
    (G : UtilityGame.{uι, us, uo} ι) {T : ℕ} [NeZero T]
    (roundLaw : Fin T → PMF (Profile G.form.sig)) (who : ι)
    (replacement : G.form.sig.Strategy who)
    (hdev : ∀ t, UtilityIntegrable G.utility who
      ((roundLaw t).bind fun profile =>
        G.form.play (Profile.update profile who replacement))) :
    UtilityIntegrable G.utility who
      ((G.form.timeAverage roundLaw).bind fun profile =>
        G.form.play (Profile.update profile who replacement)) := by
  have h := payoffIntegrable_bind_of_finite
    (PMF.uniformOfFintype (Fin T))
    (fun t => (roundLaw t).bind fun profile =>
      G.form.play (Profile.update profile who replacement))
    (fun outcome => G.utility outcome who) hdev
  simpa only [GameForm.timeAverage, PMF.bind_bind, UtilityIntegrable] using h

/-- External regret of a finite time average is average external regret. -/
theorem externalRegret_timeAverage (G : UtilityGame.{uι, us, uo} ι)
    {T : ℕ} [NeZero T]
    (roundLaw : Fin T → PMF (Profile G.form.sig)) (who : ι)
    (replacement : G.form.sig.Strategy who)
    (hbase : ∀ t, UtilityIntegrable G.utility who
      (G.form.outcomeLaw (roundLaw t)))
    (hdev : ∀ t, UtilityIntegrable G.utility who
      ((roundLaw t).bind fun profile =>
        G.form.play (Profile.update profile who replacement))) :
    G.externalRegret (G.form.timeAverage roundLaw) who replacement
        (timeAverage_base_integrable G roundLaw who hbase)
        (timeAverage_deviation_integrable G roundLaw who replacement hdev) =
      (∑ t, G.externalRegret (roundLaw t) who replacement
        (hbase t) (hdev t)) / T := by
  let times := PMF.uniformOfFintype (Fin T)
  let devKernel := fun profile =>
    G.form.play (Profile.update profile who replacement)
  let devValue := fun t =>
    expectedUtility G.utility who ((roundLaw t).bind devKernel) (hdev t)
  let baseValue := fun t =>
    expectedUtility G.utility who (G.form.outcomeLaw (roundLaw t)) (hbase t)
  have hdevOuter : PayoffIntegrable times devValue := by
    exact payoffIntegrable_bind_conditionalExpectation times
      (fun t => (roundLaw t).bind devKernel)
      (fun outcome => G.utility outcome who)
      (by
        simpa only [times, GameForm.timeAverage, PMF.bind_bind,
          GameForm.outcomeLaw, devKernel, UtilityIntegrable] using
          (timeAverage_deviation_integrable G roundLaw who replacement hdev))
      hdev
  have hbaseOuter : PayoffIntegrable times baseValue := by
    exact payoffIntegrable_bind_conditionalExpectation times
      (fun t => G.form.outcomeLaw (roundLaw t))
      (fun outcome => G.utility outcome who)
      (by
        simpa only [times, GameForm.timeAverage, GameForm.outcomeLaw_bind,
          UtilityIntegrable] using
          (timeAverage_base_integrable G roundLaw who hbase))
      hbase
  have hdevTower : expectedUtility G.utility who
      ((G.form.timeAverage roundLaw).bind devKernel)
      (timeAverage_deviation_integrable G roundLaw who replacement hdev) =
      expect times devValue hdevOuter := by
    simpa only [GameForm.timeAverage, devKernel, times, PMF.bind_bind,
      UtilityIntegrable, devValue] using
        expectedUtility_bind G.utility who times
          (fun t => (roundLaw t).bind devKernel)
          (by
            simpa only [times, GameForm.timeAverage, PMF.bind_bind,
              UtilityIntegrable, devKernel] using
              (timeAverage_deviation_integrable G roundLaw who replacement hdev))
          hdev
  have hbaseTower : expectedUtility G.utility who
      (G.form.outcomeLaw (G.form.timeAverage roundLaw))
      (timeAverage_base_integrable G roundLaw who hbase) =
      expect times baseValue hbaseOuter := by
    simpa only [GameForm.timeAverage, GameForm.outcomeLaw_bind, times,
      UtilityIntegrable, baseValue] using
        expectedUtility_bind G.utility who times
          (fun t => G.form.outcomeLaw (roundLaw t))
          (by
            simpa only [times, GameForm.timeAverage,
              GameForm.outcomeLaw_bind, UtilityIntegrable] using
              (timeAverage_base_integrable G roundLaw who hbase)) hbase
  unfold externalRegret
  rw [hdevTower, hbaseTower]
  calc
    expect times devValue hdevOuter - expect times baseValue hbaseOuter =
        expect times (fun t => devValue t - baseValue t)
          (payoffIntegrable_sub hdevOuter hbaseOuter) :=
      (expect_sub hdevOuter hbaseOuter).symm
    _ = (∑ t, (devValue t - baseValue t)) / T := expect_uniformFin _
    _ = (∑ t, G.externalRegret (roundLaw t) who replacement
          (hbase t) (hdev t)) / T := by
        apply congrArg (fun x : ℝ => x / T)
        apply Finset.sum_congr rfl
        intro t _
        rfl

/-- **Finite no-regret implies approximate coarse correlated equilibrium.**
If every player's cumulative external regret against every fixed strategy is
at most `R`, the time average is an `(R / T)`-CCE. -/
theorem timeAverage_isεCoarseCorrelatedEq_of_regret_le
    (G : UtilityGame.{uι, us, uo} ι) {T : ℕ} [NeZero T]
    {roundLaw : Fin T → PMF (Profile G.form.sig)} {R : ℝ}
    (hbase : ∀ t who, UtilityIntegrable G.utility who
      (G.form.outcomeLaw (roundLaw t)))
    (hdev : ∀ t who replacement, UtilityIntegrable G.utility who
      ((roundLaw t).bind fun profile =>
        G.form.play (Profile.update profile who replacement)))
    (hregret :
      ∀ who replacement,
        (∑ t, G.externalRegret (roundLaw t) who replacement
          (hbase t who) (hdev t who replacement)) ≤ R) :
    IsεCoarseCorrelatedEq G.form G.utility (R / T)
      (G.form.timeAverage roundLaw) := by
  rw [G.isεCoarseCorrelatedEq_iff_externalRegret_le]
  intro who replacement
  refine ⟨timeAverage_base_integrable G roundLaw who (fun t => hbase t who),
    timeAverage_deviation_integrable G roundLaw who replacement
      (fun t => hdev t who replacement), ?_⟩
  rw [externalRegret_timeAverage G roundLaw who replacement
    (fun t => hbase t who) (fun t => hdev t who replacement)]
  have hT : (0 : ℝ) < T := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne T)
  exact (div_le_div_iff_of_pos_right hT).2 (hregret who replacement)

/-! ## Independent self-play

The learning reduction above accepts an arbitrary law over pure profiles.
Independent self-play is the special case in which each round is a product
of players' mixed actions. Only the round-index average is finite; strategy
carriers and round laws need not have finite support.

The multiplicative-weights recurrence is provided by
`GameTheory.Math.OnlineLearning`; this section exposes the finite-law bridge.
-/

variable [Fintype ι]

omit [DecidableEq ι] [Fintype ι] in
/-- A finite outcome utility band certifies absolute integrability under any law. -/
theorem utilityIntegrable_of_band (G : UtilityGame.{uι, us, uo} ι)
    (lo : ι → ℝ) (width : ℝ)
    (hband : ∀ who outcome,
      G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (who : ι) (law : PMF G.form.sig.Outcome) :
    UtilityIntegrable G.utility who law := by
  apply payoffIntegrable_of_bounded law (fun outcome => G.utility outcome who)
    (C := |lo who| + |width|)
  intro outcome
  have hb := hband who outcome
  rcases hb with ⟨hlo, hhi⟩
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (lo who), abs_nonneg width]
  · linarith [le_abs_self (lo who), le_abs_self width]

/-- The external regret of an independent profile law is exactly the gain from
replacing that player's mixed action by a point mass in the mixed extension. -/
theorem externalRegret_pi (G : UtilityGame.{uι, us, uo} ι)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (replacement : G.form.sig.Strategy who)
    (hbase : UtilityIntegrable G.utility who
      (G.form.mixed.play mixedProfile))
    (hdeviation : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure replacement)))) :
    G.externalRegret (independentProduct mixedProfile) who replacement
      hbase
      (payoffIntegrable_congr_law
        (mixed_play_update_pure_eq_bind (F := G.form) mixedProfile who replacement)
        hdeviation) =
      expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update mixedProfile who (PMF.pure replacement)))
          hdeviation -
      expectedUtility G.utility who (G.form.mixed.play mixedProfile) hbase := by
  unfold externalRegret
  apply congrArg₂ (· - ·)
  · exact expectedUtility_congr_law G.utility who
      (mixed_play_update_pure_eq_bind (F := G.form) mixedProfile who replacement).symm
      (payoffIntegrable_congr_law
        (mixed_play_update_pure_eq_bind (F := G.form) mixedProfile who replacement)
        hdeviation)
      hdeviation
  · rfl

/-- Mixing a player's pure-action values against their own mixed action gives
their status-quo utility. -/
theorem expect_expectedUtility_update (G : UtilityGame.{uι, us, uo} ι)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (hmixed : UtilityIntegrable G.utility who
      (G.form.mixed.play mixedProfile))
    (hpure : ∀ action, UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action)))) :
    expect (mixedProfile who)
      (fun action => expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action))) (hpure action))
      (payoffIntegrable_bind_conditionalExpectation (mixedProfile who)
        (fun action => G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))
        (fun outcome => G.utility outcome who)
        (by
          have heq : G.form.mixed.play mixedProfile =
              (mixedProfile who).bind fun action =>
                G.form.mixed.play
                  (Profile.update mixedProfile who (PMF.pure action)) := by
            calc
              G.form.mixed.play mixedProfile = G.form.mixed.play
                  (Profile.update mixedProfile who (mixedProfile who)) := by
                    rw [Profile.update_eq_self]
              _ = _ := GameForm.mixed_play_update G.form mixedProfile who
                (mixedProfile who)
          rw [← heq]
          exact hmixed) hpure) =
      expectedUtility G.utility who (G.form.mixed.play mixedProfile) hmixed :=
  (expectedUtility_mixed_eq_expect G.form G.utility mixedProfile who hmixed
    hpure).symm

/-- A pure-action payoff in independent play, normalized to the unit interval
using a player-specific payoff band.  It is the unit-range input consumed by
the multiplicative-weights construction in `GameTheory.Analysis.Learning`. -/
def normGain (G : UtilityGame.{uι, us, uo} ι) (lo : ι → ℝ) (width : ℝ)
    (hband : ∀ who outcome,
      G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) : ℝ :=
  (expectedUtility G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action)))
      (utilityIntegrable_of_band G lo width hband who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))) - lo who) / width

/-- Normalized pure-action gains lie in `[0, 1]` whenever every outcome
utility lies in the advertised player-specific band. -/
theorem normGain_mem_Icc (G : UtilityGame.{uι, us, uo} ι)
    {lo : ι → ℝ} {width : ℝ} (hwidth : 0 < width)
    (hband : ∀ who outcome, G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) :
    G.normGain lo width hband mixedProfile who action ∈ Set.Icc (0 : ℝ) 1 := by
  have hlower : lo who ≤ expectedUtility G.utility who
      (G.form.mixed.play (Profile.update mixedProfile who (PMF.pure action)))
      (utilityIntegrable_of_band G lo width hband who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))) := by
    let law := G.form.mixed.play
      (Profile.update mixedProfile who (PMF.pure action))
    have h := expect_mono (μ := law) (f := fun _ => lo who)
      (g := fun outcome => G.utility outcome who)
      (fun outcome _ => (hband who outcome).1)
      (payoffIntegrable_constant law (lo who))
      (utilityIntegrable_of_band G lo width hband who law)
    simpa [expectedUtility, expect_constant] using h
  have hupper : expectedUtility G.utility who
      (G.form.mixed.play (Profile.update mixedProfile who (PMF.pure action)))
      (utilityIntegrable_of_band G lo width hband who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))) ≤
        lo who + width := by
    let law := G.form.mixed.play
      (Profile.update mixedProfile who (PMF.pure action))
    have h := expect_mono (μ := law) (f := fun outcome => G.utility outcome who)
      (g := fun _ => lo who + width)
      (fun outcome _ => (hband who outcome).2)
      (utilityIntegrable_of_band G lo width hband who law)
      (payoffIntegrable_constant law (lo who + width))
    simpa [expectedUtility, expect_constant] using h
  refine Set.mem_Icc.mpr ⟨?_, ?_⟩
  · rw [normGain]
    exact div_nonneg (sub_nonneg.mpr hlower) hwidth.le
  · rw [normGain, div_le_one hwidth]
    linarith

/-- A normalized gain in `[0, 1]` is integrable under the player's mixed law. -/
theorem normGain_integrable (G : UtilityGame.{uι, us, uo} ι)
    {lo : ι → ℝ} {width : ℝ} (hwidth : 0 < width)
    (hband : ∀ who outcome,
      G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) :
    PayoffIntegrable (mixedProfile who)
      (G.normGain lo width hband mixedProfile who) := by
  apply payoffIntegrable_of_bounded (mixedProfile who)
    (G.normGain lo width hband mixedProfile who) (C := 1)
  intro action
  have h := G.normGain_mem_Icc hwidth hband mixedProfile who action
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The expected normalized gain is the normalized status-quo utility. -/
theorem expect_normGain (G : UtilityGame.{uι, us, uo} ι)
    (lo : ι → ℝ) (width : ℝ) (hwidth : 0 < width)
    (hband : ∀ who outcome,
      G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) :
    expect (mixedProfile who) (G.normGain lo width hband mixedProfile who)
      (normGain_integrable G hwidth hband mixedProfile who) =
      (expectedUtility G.utility who (G.form.mixed.play mixedProfile)
        (utilityIntegrable_of_band G lo width hband who
          (G.form.mixed.play mixedProfile)) - lo who) / width := by
  let conditional := fun action =>
    expectedUtility G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action)))
      (utilityIntegrable_of_band G lo width hband who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action))))
  have hmixed := utilityIntegrable_of_band G lo width hband who
    (G.form.mixed.play mixedProfile)
  have hpure : ∀ action, UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action))) :=
    fun action => utilityIntegrable_of_band G lo width hband who _
  have houter : PayoffIntegrable (mixedProfile who) conditional := by
    exact payoffIntegrable_bind_conditionalExpectation (mixedProfile who)
      (fun action => G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action)))
      (fun outcome => G.utility outcome who)
      (by
        have heq : G.form.mixed.play mixedProfile =
            (mixedProfile who).bind fun action =>
              G.form.mixed.play
                (Profile.update mixedProfile who (PMF.pure action)) := by
          calc
            G.form.mixed.play mixedProfile = G.form.mixed.play
                (Profile.update mixedProfile who (mixedProfile who)) := by
                  rw [Profile.update_eq_self]
            _ = _ := GameForm.mixed_play_update G.form mixedProfile who
              (mixedProfile who)
        rw [← heq]
        exact hmixed) hpure
  have hmean := G.expect_expectedUtility_update mixedProfile who hmixed hpure
  have hconst := payoffIntegrable_constant (mixedProfile who) (lo who)
  have hsub := payoffIntegrable_sub houter hconst
  calc
    expect (mixedProfile who) (G.normGain lo width hband mixedProfile who)
        (normGain_integrable G hwidth hband mixedProfile who) =
      expect (mixedProfile who) (fun action =>
        (1 / width) * (conditional action - lo who))
        (payoffIntegrable_const_mul hsub) := by
          apply expect_congr_on_support
          · intro action _
            rw [normGain]
            dsimp only [conditional]
            rw [div_eq_mul_inv]
            ring
    _ = (1 / width) * expect (mixedProfile who)
        (fun action => conditional action - lo who) hsub :=
      expect_const_mul hsub
    _ = (1 / width) *
        (expectedUtility G.utility who (G.form.mixed.play mixedProfile) hmixed -
          lo who) := by
          rw [expect_sub houter hconst, hmean, expect_constant]
    _ = _ := by ring

/-- Scaling normalized gains back by the width recovers a pure-deviation gain. -/
theorem expectedUtility_deviation_eq_width_mul_normGain
    (G : UtilityGame.{uι, us, uo} ι) {lo : ι → ℝ} {width : ℝ}
    (hwidth : 0 < width)
    (hband : ∀ who outcome,
      G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (mixedProfile : Profile G.form.sig.mixed) (who : ι)
    (action : G.form.sig.Strategy who) :
    expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))
        (utilityIntegrable_of_band G lo width hband who _)-
      expectedUtility G.utility who (G.form.mixed.play mixedProfile)
        (utilityIntegrable_of_band G lo width hband who _) =
      width * (G.normGain lo width hband mixedProfile who action -
        expect (mixedProfile who) (G.normGain lo width hband mixedProfile who)
          (normGain_integrable G hwidth hband mixedProfile who)) := by
  rw [G.expect_normGain lo width hwidth hband mixedProfile who]
  simp only [normGain]
  have hne : width ≠ 0 := hwidth.ne'
  field_simp
  ring

/-- **Independent no-regret self-play yields an approximate CCE.** A bound on
every pure deviation's cumulative mixed-extension gain is transferred through
the finite product law at every round. -/
theorem selfPlay_timeAverage_isεCoarseCorrelatedEq
    (G : UtilityGame.{uι, us, uo} ι) {T : ℕ} [NeZero T]
    (lo : ι → ℝ) (width : ℝ)
    (hband : ∀ who outcome,
      G.utility outcome who ∈ Set.Icc (lo who) (lo who + width))
    (mixedProfile : Fin T → Profile G.form.sig.mixed) {bound : ℝ}
    (hregret : ∀ who (action : G.form.sig.Strategy who),
      ((Finset.univ : Finset (Fin T)).sum (fun round =>
        expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update (mixedProfile round) who (PMF.pure action)))
            (utilityIntegrable_of_band G lo width hband who _) -
        expectedUtility G.utility who (G.form.mixed.play (mixedProfile round))
          (utilityIntegrable_of_band G lo width hband who _))) ≤ bound) :
    IsεCoarseCorrelatedEq G.form G.utility (bound / T)
      (G.form.timeAverage fun round => independentProduct (mixedProfile round)) := by
  have hdeviation_mixed (round : Fin T) (who : ι)
      (action : G.form.sig.Strategy who) :
      UtilityIntegrable G.utility who
        (G.form.mixed.play
          (Profile.update (mixedProfile round) who (PMF.pure action))) :=
    utilityIntegrable_of_band G lo width hband who _
  have hdeviation_law (round : Fin T) (who : ι)
      (action : G.form.sig.Strategy who) :
      G.form.mixed.play
          (Profile.update (mixedProfile round) who (PMF.pure action)) =
        (independentProduct (mixedProfile round)).bind fun profile =>
          G.form.play (Profile.update profile who action) :=
    mixed_play_update_pure_eq_bind (F := G.form) (mixedProfile round)
      who action
  have hdeviation_independent (round : Fin T) (who : ι)
      (action : G.form.sig.Strategy who) :
      UtilityIntegrable G.utility who
        ((independentProduct (mixedProfile round)).bind fun profile =>
          G.form.play (Profile.update profile who action)) := by
    exact payoffIntegrable_congr_law
      (α := G.form.sig.Outcome)
      (f := fun outcome => G.utility outcome who)
      (hdeviation_law round who action)
      (hdeviation_mixed round who action)
  apply G.timeAverage_isεCoarseCorrelatedEq_of_regret_le
    (hbase := fun round who => by
      simpa only [GameForm.outcomeLaw, GameForm.mixed_play] using
        (utilityIntegrable_of_band G lo width hband who
          (G.form.mixed.play (mixedProfile round))))
    (hdev := fun round who action => by
      exact hdeviation_independent round who action)
  intro who action
  rw [show (∑ round, G.externalRegret
      (independentProduct (mixedProfile round)) who action
      (by simpa only [GameForm.outcomeLaw, GameForm.mixed_play] using
        (utilityIntegrable_of_band G lo width hband who
          (G.form.mixed.play (mixedProfile round))))
      (by
        exact hdeviation_independent round who action)) =
      ∑ round ∈ (Finset.univ : Finset (Fin T)), (expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update (mixedProfile round) who (PMF.pure action)))
            (utilityIntegrable_of_band G lo width hband who _) -
        expectedUtility G.utility who (G.form.mixed.play (mixedProfile round))
          (utilityIntegrable_of_band G lo width hband who _)) by
      apply Finset.sum_congr rfl
      intro round _
      exact G.externalRegret_pi (mixedProfile round) who action
        (utilityIntegrable_of_band G lo width hband who _)
        (utilityIntegrable_of_band G lo width hband who _)]
  exact hregret who action

end UtilityGame

end GameTheory
