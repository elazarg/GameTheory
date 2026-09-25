/-
# Guarded PMF fictitious-play trajectories

Fictitious play repeatedly chooses a pure best response to the independent
PMF empirical marginals of past play. This file owns the topology-free state
and guarded expected-utility recurrence. Claims about limits of these beliefs
live in the analytic consumer.

Primary reference for the process: G. W. Brown, “Iterative Solution of Games
by Fictitious Play,” in T. C. Koopmans (ed.), *Activity Analysis of Production
and Allocation*, Cowles Commission Monograph 13 (1951), 374--376.
-/

import GameTheory.Core.MixedImprovement
import GameTheory.Core.Response
import GameTheory.Math.Probability.Uniform

noncomputable section

namespace GameTheory

open GameTheory.Math.Probability

universe uι us uo

namespace GameForm

variable {ι : Type uι}
variable (G : GameForm.{uι, us, uo} ι)

/-- The empirical law of one player's actions during the first `T` rounds. -/
def empiricalMarginal (history : ℕ → Profile G.sig) (who : ι)
    (T : ℕ) [NeZero T] : PMF (G.sig.Strategy who) :=
  (PMF.uniformOfFintype (Fin T)).map
    fun round : Fin T => history round.val who

theorem empiricalMarginal_integrable (history : ℕ → Profile G.sig)
    (who : ι) (T : ℕ) [NeZero T]
    (observable : G.sig.Strategy who → ℝ) :
    PayoffIntegrable (G.empiricalMarginal history who T) observable := by
  have hmap : PayoffIntegrable
      ((PMF.uniformOfFintype (Fin T)).map
        fun round : Fin T => history round.val who) observable :=
    (payoffIntegrable_map_iff _ _ _).2 (payoffIntegrable_of_finite _ _)
  simpa only [empiricalMarginal] using hmap

/-- An empirical marginal is the uniform finite average of the matching past
actions. -/
theorem empiricalMarginal_prob (history : ℕ → Profile G.sig) (who : ι)
    (T : ℕ) [NeZero T] [DecidableEq (G.sig.Strategy who)]
    (action : G.sig.Strategy who) :
    G.empiricalMarginal history who T action =
      ((Finset.univ.filter fun round : Fin T => history round who = action).card : ENNReal) /
        (T : ENNReal) := by
  unfold empiricalMarginal
  simpa only [Fintype.card_fin] using uniformOfFintype_map_apply
    (fun round : Fin T => history round.val who) action

/-- Expectation under an empirical marginal is the ordinary finite average. -/
theorem empiricalMarginal_expect (history : ℕ → Profile G.sig) (who : ι)
    (T : ℕ) [NeZero T] (observable : G.sig.Strategy who → ℝ) :
    expect (G.empiricalMarginal history who T) observable
        (G.empiricalMarginal_integrable history who T observable) =
      (∑ round : Fin T, observable (history round who)) / T := by
  have hmap := expect_map
    (fun round : Fin T => history round.val who)
    (PMF.uniformOfFintype (Fin T)) observable
    ((payoffIntegrable_map_iff _ _ _).mp
      (G.empiricalMarginal_integrable history who T observable))
    (G.empiricalMarginal_integrable history who T observable)
  simpa only [empiricalMarginal, expect_uniformFin, Function.comp_apply] using hmap

/-- Adding one observation is a mixture of the previous empirical law and the
new observed pure action. -/
theorem empiricalMarginal_succ_mix (history : ℕ → Profile G.sig)
    (who : ι) (T : ℕ) [NeZero T] :
    G.empiricalMarginal history who (T + 1) =
      mix ((T : ℝ) / (T + 1)) (by positivity) (by
        have hn : (0 : ℝ) < T + 1 := by positivity
        rw [div_le_iff₀ hn]
        norm_num) (G.empiricalMarginal history who T)
        (PMF.pure (history T who)) := by
  unfold empiricalMarginal
  simpa only [Fin.val_castSucc, Fin.val_last] using
    uniformOfFintype_map_fin_succ T (fun round : Fin (T + 1) => history round.val who)

/-- The product law after one empirical coordinate update is the same mixture
of the previous product law and the pure updated-coordinate product law. -/
theorem empiricalProduct_succ_mix [Fintype ι] [DecidableEq ι]
    (history : ℕ → Profile G.sig) (mixedProfile : Profile G.sig.mixed)
    (who : ι) (t : ℕ) :
    independentProduct
        (Profile.update mixedProfile who
          (G.empiricalMarginal history who (t + 2))) =
      mix ((t + 1 : ℝ) / (t + 2 : ℝ)) (by positivity) (by
        have hn : (0 : ℝ) < t + 2 := by positivity
        rw [div_le_iff₀ hn]
        norm_num)
        (independentProduct (Profile.update mixedProfile who
          (G.empiricalMarginal history who (t + 1))))
        (independentProduct (Profile.update mixedProfile who
          (PMF.pure (history (t + 1) who)))) := by
  let q := fun action =>
    independentProduct (Profile.update mixedProfile who (PMF.pure action))
  let w := (t + 1 : ℝ) / (t + 2 : ℝ)
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp [w]
    have hn : (0 : ℝ) < t + 2 := by positivity
    rw [div_le_iff₀ hn]
    norm_num
  calc
    _ = (G.empiricalMarginal history who (t + 2)).bind q :=
      pi_update_mixed G.sig mixedProfile who _
    _ = mix w hw0 hw1
        ((G.empiricalMarginal history who (t + 1)).bind q)
        ((PMF.pure (history (t + 1) who)).bind q) := by
      rw [@empiricalMarginal_succ_mix ι G history who (t + 1) ⟨by omega⟩,
        mix_bind]
      congr 1
      push_cast
      ring
    _ = _ := by
      rw [pi_update_mixed, PMF.pure_bind]

/-- Adding one observation updates every empirical expectation by the usual
running-average recurrence. -/
theorem empiricalMarginal_succ_expect (history : ℕ → Profile G.sig)
    (who : ι) (t : ℕ) (observable : G.sig.Strategy who → ℝ) :
    expect (G.empiricalMarginal history who (t + 2)) observable
        (G.empiricalMarginal_integrable history who (t + 2) observable) =
      ((t + 1 : ℝ) / (t + 2 : ℝ)) *
          expect (G.empiricalMarginal history who (t + 1)) observable
            (G.empiricalMarginal_integrable history who (t + 1) observable) +
        (1 / (t + 2 : ℝ)) * observable (history (t + 1) who) := by
  rw [G.empiricalMarginal_expect, G.empiricalMarginal_expect]
  have hsum :
      (∑ round : Fin (t + 2), observable (history round who)) =
        (∑ round : Fin (t + 1), observable (history round who)) +
          observable (history (t + 1) who) := by
    rw [show t + 2 = (t + 1) + 1 by omega, Fin.sum_univ_castSucc]
    rfl
  rw [hsum]
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp

/-- The independent empirical belief profile available after `T` rounds. -/
def empiricalBelief (history : ℕ → Profile G.sig) (T : ℕ) [NeZero T] :
    Profile G.sig.mixed :=
  fun who => G.empiricalMarginal history who T

/-- A profile law made from finitely many empirical marginals has finite
support, even when the pure strategy carriers are infinite. -/
theorem empiricalBelief_integrable [Fintype ι]
    (history : ℕ → Profile G.sig) (T : ℕ) [NeZero T]
    (observable : Profile G.sig → ℝ) :
    PayoffIntegrable
      (independentProduct (G.empiricalBelief history T)) observable := by
  let rounds : ∀ _ : ι, PMF (Fin T) := fun _ =>
    PMF.uniformOfFintype (Fin T)
  let sampleToProfile : (∀ _ : ι, Fin T) → Profile G.sig := fun sample who =>
    history (sample who).val who
  have hlaw :
      (independentProduct rounds).map sampleToProfile =
        independentProduct (G.empiricalBelief history T) := by
    calc
      _ = independentProduct
          (fun who => (rounds who).map
            (fun round => history round.val who)) :=
        independentProduct_map rounds
          (fun who round => history round.val who)
      _ = independentProduct (G.empiricalBelief history T) := by
        congr 1
  have hsource : PayoffIntegrable (independentProduct rounds)
      (observable ∘ sampleToProfile) :=
    payoffIntegrable_of_finite _ _
  exact payoffIntegrable_congr_law hlaw
    ((payoffIntegrable_map_iff sampleToProfile _ observable).2 hsource)

/-- Replacing one empirical coordinate by a pure action still gives a
finite-support profile law, regardless of strategy-carrier size. -/
theorem empiricalBelief_update_integrable [Fintype ι] [DecidableEq ι]
    (history : ℕ → Profile G.sig) (T : ℕ) [NeZero T]
    (who : ι) (action : G.sig.Strategy who)
    (observable : Profile G.sig → ℝ) :
    PayoffIntegrable
      (independentProduct
        (Profile.update (G.empiricalBelief history T) who (PMF.pure action)))
      observable := by
  let rounds : ∀ _ : ι, PMF (Fin T) := fun _ =>
    PMF.uniformOfFintype (Fin T)
  let sampleToProfile : (∀ _ : ι, Fin T) → Profile G.sig := fun sample =>
    Profile.update (fun player => history (sample player).val player) who
      action
  have hlaw :
      (independentProduct rounds).map sampleToProfile =
        independentProduct
          (Profile.update (G.empiricalBelief history T) who (PMF.pure action)) := by
    calc
      _ = independentProduct
          (fun player => (rounds player).map
            (fun round =>
              Profile.update (fun i => history round.val i) who
                action player)) :=
        independentProduct_map rounds
          (fun player round =>
            Profile.update (fun i => history round.val i) who
              action player)
      _ = independentProduct
          (Profile.update (G.empiricalBelief history T) who (PMF.pure action)) := by
        congr 1
        funext player
        by_cases h : player = who
        · subst player
          simp only [rounds, Profile.update_same]
          rw [show (fun _ : Fin T => action) =
            Function.const (Fin T) action from rfl, PMF.map_const]
        · simp [rounds, h, empiricalBelief,
            empiricalMarginal]
  have hsource : PayoffIntegrable (independentProduct rounds)
      (observable ∘ sampleToProfile) :=
    payoffIntegrable_of_finite _ _
  exact payoffIntegrable_congr_law hlaw
    ((payoffIntegrable_map_iff sampleToProfile _ observable).2 hsource)

end GameForm

namespace UtilityGame

variable (G : UtilityGame.{uι, us, uo} ι)

variable [Fintype ι] [DecidableEq ι]

/-- A history is fictitious play when every action after the initial round is
a pure best response to the empirical belief formed from all earlier rounds.
The predicate reuses the canonical mixed extension and `IsBestResponse`; it is
not a parallel equilibrium or payoff semantics. -/
def IsFictitiousPlay (history : ℕ → Profile G.form.sig) : Prop :=
  ∀ (t : ℕ) (who : ι),
    IsBestResponse G.form.mixed (euPreference G.utility) who
      (G.form.empiricalBelief history (t + 1))
      (PMF.pure (history (t + 1) who))

/-- The defining best-response obligation of fictitious play. -/
theorem IsFictitiousPlay.isBestResponse {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) (who : ι) :
    IsBestResponse G.form.mixed (euPreference G.utility) who
      (G.form.empiricalBelief history (t + 1))
      (PMF.pure (history (t + 1) who)) :=
  hplay t who

/-- Every actual replacement law compared by fictitious play is integrable. -/
theorem IsFictitiousPlay.deviation_integrable
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) (who : ι)
    (replacement : PMF (G.form.sig.Strategy who)) :
    UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update (G.form.empiricalBelief history (t + 1)) who
          replacement)) := by
  have hbest := hplay t who replacement
  rw [euPreference_apply] at hbest
  exact hbest.2.1

/-- Fictitious play's actual incumbent law is among the certified deviations. -/
theorem IsFictitiousPlay.incumbent_integrable
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) (who : ι) :
    UtilityIntegrable G.utility who
      (G.form.mixed.play (G.form.empiricalBelief history (t + 1))) := by
  let belief := G.form.empiricalBelief history (t + 1)
  have hdev := IsFictitiousPlay.deviation_integrable (G := G) hplay t who
    (belief who)
  have hprofile : Profile.update belief who (belief who) = belief :=
    Profile.update_eq_self _ _
  exact payoffIntegrable_congr_law
    (congrArg G.form.mixed.play hprofile) hdev

/-! ## Finite existence -/

/-- Select one pure best response to a mixed profile. Finiteness and
nonemptiness are required only by this selection operation. -/
noncomputable def pureBestResponse
    [∀ who, Finite (G.form.sig.Strategy who)]
    [∀ who, Nonempty (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed)
    (hpure : ∀ who action, UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action)))) : Profile G.form.sig := by
  let hpure' := hpure
  exact fun who => Classical.choose <| Finite.exists_max fun action =>
    expectedUtility G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who (PMF.pure action)))
      (hpure' who action)

/-- The selected pure action is a best response even against arbitrary mixed
replacements, because mixed replacement utility averages pure replacement
utilities. -/
theorem pureBestResponse_isBestResponse
    [∀ who, Finite (G.form.sig.Strategy who)]
    [∀ who, Nonempty (G.form.sig.Strategy who)]
    (mixedProfile : Profile G.form.sig.mixed)
    (hpure : ∀ player action, UtilityIntegrable G.utility player
      (G.form.mixed.play
        (Profile.update mixedProfile player (PMF.pure action)))) (who : ι) :
    IsBestResponse G.form.mixed (euPreference G.utility) who mixedProfile
      (PMF.pure (G.pureBestResponse mixedProfile hpure who)) := by
  intro alternative
  rw [euPreference_apply]
  let q := fun action => G.form.mixed.play
    (Profile.update mixedProfile who (PMF.pure action))
  have hcond : ∀ action, UtilityIntegrable G.utility who (q action) := by
    intro action
    exact hpure who action
  let chosen := G.pureBestResponse mixedProfile hpure who
  have hchosen : UtilityIntegrable G.utility who
      (G.form.mixed.play (Profile.update mixedProfile who (PMF.pure chosen))) :=
    hcond chosen
  have hmax : ∀ action, expectedUtility G.utility who (q action)
      (hcond action) ≤ expectedUtility G.utility who (q chosen) hchosen := by
    intro action
    dsimp [chosen, q]
    unfold pureBestResponse
    exact Classical.choose_spec (Finite.exists_max fun action =>
      expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who (PMF.pure action)))
      (hpure who action)) action
  have hpreferred : UtilityIntegrable G.utility who
      (G.form.mixed.play (Profile.update mixedProfile who (PMF.pure chosen))) :=
    hchosen
  have hpreferredEq :
      G.form.mixed.play (Profile.update mixedProfile who (PMF.pure chosen)) = q chosen := rfl
  have halternativeLaw :
      G.form.mixed.play (Profile.update mixedProfile who alternative) =
        alternative.bind q := by
    exact GameForm.mixed_play_update G.form mixedProfile who alternative
  have haltBind : UtilityIntegrable G.utility who (alternative.bind q) := by
    exact payoffIntegrable_bind_of_finite alternative q
      (fun outcome => G.utility outcome who) hcond
  have halt : UtilityIntegrable G.utility who
      (G.form.mixed.play (Profile.update mixedProfile who alternative)) :=
    payoffIntegrable_congr_law halternativeLaw.symm haltBind
  refine ⟨hpreferred, halt, ?_⟩
  have hconst : PayoffIntegrable alternative
      (fun _ => expectedUtility G.utility who (q chosen) hchosen) :=
    payoffIntegrable_constant _ _
  have houter := payoffIntegrable_bind_conditionalExpectation alternative q
    (fun outcome => G.utility outcome who) haltBind hcond
  have hineq := expect_mono (fun action _ => hmax action) houter hconst
  calc
    expectedUtility G.utility who
        (G.form.mixed.play (Profile.update mixedProfile who alternative)) halt
        = expectedUtility G.utility who (alternative.bind q) haltBind :=
      (expectedUtility_congr_law G.utility who halternativeLaw.symm haltBind halt).symm
    _ = expect alternative (fun action => expectedUtility G.utility who (q action)
        (hcond action))
        houter :=
      expectedUtility_bind G.utility who alternative q haltBind hcond
    _ ≤ expectedUtility G.utility who (q chosen) hchosen := by
      calc
        expect alternative (fun action => expectedUtility G.utility who
          (q action) (hcond action)) houter ≤
            expect alternative (fun _ => expectedUtility G.utility who
              (q chosen) hchosen) hconst := hineq
        _ = expectedUtility G.utility who (q chosen) hchosen :=
          expect_constant alternative _ hconst
    _ = expectedUtility G.utility who
        (G.form.mixed.play (Profile.update mixedProfile who (PMF.pure chosen)))
        hpreferred := by
      symm
      exact expectedUtility_congr_law G.utility who hpreferredEq hpreferred hchosen

/-- A canonical fictitious-play trajectory generated from an arbitrary
initial profile. At a positive round, recursive calls are made only for the
strictly earlier rounds inspected by the empirical belief. -/
noncomputable def generatedFictitiousPlay
    [∀ who, Finite (G.form.sig.Strategy who)]
    [∀ who, Nonempty (G.form.sig.Strategy who)]
    (hintegrable : GameForm.HasIntegrableUtility G.form G.utility)
    (initial : Profile G.form.sig) (round : ℕ) : Profile G.form.sig :=
  if hzero : round = 0 then initial
  else
    letI : NeZero round := ⟨hzero⟩
    let mixedProfile := G.form.empiricalBelief
        (fun earlier =>
          if _hbefore : earlier < round then
            generatedFictitiousPlay hintegrable initial earlier
          else initial)
        round
    G.pureBestResponse mixedProfile (fun who action =>
      hintegrable.mixed_of_finite who
        (Profile.update mixedProfile who (PMF.pure action)))
termination_by round
decreasing_by omega

/-- The recursively generated trajectory satisfies the fictitious-play
best-response recurrence. -/
theorem generatedFictitiousPlay_isFictitiousPlay
    [∀ who, Finite (G.form.sig.Strategy who)]
    [∀ who, Nonempty (G.form.sig.Strategy who)]
    (hintegrable : GameForm.HasIntegrableUtility G.form G.utility)
    (initial : Profile G.form.sig) :
    G.IsFictitiousPlay (G.generatedFictitiousPlay hintegrable initial) := by
  intro t who
  let past : ℕ → Profile G.form.sig := fun earlier =>
    if hbefore : earlier < t + 1 then
      G.generatedFictitiousPlay hintegrable initial earlier
    else initial
  let mixedProfile := G.form.empiricalBelief past (t + 1)
  have hpure : ∀ player action, UtilityIntegrable G.utility player
      (G.form.mixed.play
        (Profile.update mixedProfile player (PMF.pure action))) := by
    intro player action
    exact hintegrable.mixed_of_finite player
      (Profile.update mixedProfile player (PMF.pure action))
  have hnext :
      G.generatedFictitiousPlay hintegrable initial (t + 1) =
        G.pureBestResponse mixedProfile hpure := by
    rw [generatedFictitiousPlay]
    rw [dite_eq_right (by omega : t + 1 ≠ 0)]
  have hpast :
      G.form.empiricalBelief past (t + 1) =
        G.form.empiricalBelief (G.generatedFictitiousPlay hintegrable initial) (t + 1) := by
    funext player
    unfold GameForm.empiricalBelief GameForm.empiricalMarginal
    congr 1
    funext earlier
    show
      (if hbefore : (earlier : ℕ) < t + 1 then
          G.generatedFictitiousPlay hintegrable initial earlier
        else initial) player =
        G.generatedFictitiousPlay hintegrable initial earlier player
    rw [dite_eq_left earlier.isLt]
  rw [hnext, ← hpast]
  exact G.pureBestResponse_isBestResponse _ hpure who

/-- Every finite game with nonempty pure action carriers and integrable pure
play laws has an infinite fictitious-play history. -/
theorem exists_isFictitiousPlay
    [∀ who, Finite (G.form.sig.Strategy who)]
    [∀ who, Nonempty (G.form.sig.Strategy who)]
    (hintegrable : GameForm.HasIntegrableUtility G.form G.utility) :
    ∃ history : ℕ → Profile G.form.sig, G.IsFictitiousPlay history := by
  let initial : Profile G.form.sig := fun who =>
    Classical.choice (inferInstance : Nonempty (G.form.sig.Strategy who))
  exact ⟨G.generatedFictitiousPlay hintegrable initial,
    G.generatedFictitiousPlay_isFictitiousPlay hintegrable initial⟩

/-- The gain of the pure action actually played at the next round, measured
against the empirical belief entering that round. -/
def playedGain (history : ℕ → Profile G.form.sig) (t : ℕ) (who : ι)
    (hbase : UtilityIntegrable G.utility who
      (G.form.mixed.play (G.form.empiricalBelief history (t + 1))))
    (hplayed : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update (G.form.empiricalBelief history (t + 1)) who
          (PMF.pure (history (t + 1) who))))) : ℝ :=
  G.mixedGain (G.form.empiricalBelief history (t + 1)) who
    (history (t + 1) who) hbase hplayed

/-- Advancing one coordinate to its next empirical marginal is affine at the
expected-utility level. -/
theorem expectedUtility_update_empiricalMarginal_succ
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ)
    (hprev : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who
          (G.form.empiricalMarginal history who (t + 1)))))
    (hpure : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who
          (PMF.pure (history (t + 1) who))))) :
    ∃ hnext : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who
          (G.form.empiricalMarginal history who ((t + 1) + 1)))),
      expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who ((t + 1) + 1)))) hnext =
      ((t + 1 : ℝ) / ((t + 1) + 1 : ℝ)) *
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update mixedProfile who
                (G.form.empiricalMarginal history who (t + 1)))) hprev +
        (1 / ((t + 1) + 1 : ℝ)) *
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update mixedProfile who
                (PMF.pure (history (t + 1) who)))) hpure := by
  let q := fun action => G.form.mixed.play
    (Profile.update mixedProfile who (PMF.pure action))
  let μ := G.form.empiricalMarginal history who (t + 1)
  let ν := PMF.pure (history (t + 1) who)
  let w := (t + 1 : ℝ) / ((t + 1) + 1)
  have hw0 : 0 ≤ w := by dsimp [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp [w]
    have hn : (0 : ℝ) < (t + 1) + 1 := by positivity
    rw [div_le_iff₀ hn]
    norm_num
  have hlaw : G.form.mixed.play
      (Profile.update mixedProfile who
        (G.form.empiricalMarginal history who ((t + 1) + 1))) =
      mix w hw0 hw1
        (G.form.mixed.play (Profile.update mixedProfile who μ))
        (G.form.mixed.play (Profile.update mixedProfile who ν)) := by
    calc
      _ = (G.form.empiricalMarginal history who ((t + 1) + 1)).bind q :=
        GameForm.mixed_play_update G.form mixedProfile who _
      _ = mix w hw0 hw1 (μ.bind q) (ν.bind q) := by
        rw [@GameForm.empiricalMarginal_succ_mix ι G.form history who (t + 1)
          ⟨by omega⟩, mix_bind]
        simp [μ, ν, w]
      _ = _ := by
        rw [PMF.pure_bind, ← GameForm.mixed_play_update]
  have hmix := payoffIntegrable_mix w hw0 hw1
    (G.form.mixed.play (Profile.update mixedProfile who μ))
    (G.form.mixed.play (Profile.update mixedProfile who ν))
    (fun outcome => G.utility outcome who) hprev hpure
  have hnext := payoffIntegrable_congr_law hlaw.symm hmix
  refine ⟨hnext, ?_⟩
  calc
    expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who ((t + 1) + 1))))
        hnext = expectedUtility G.utility who
          (mix w hw0 hw1
            (G.form.mixed.play (Profile.update mixedProfile who μ))
            (G.form.mixed.play (Profile.update mixedProfile who ν))) hmix :=
      expectedUtility_congr_law G.utility who hlaw hnext hmix
    _ = w * expectedUtility G.utility who
          (G.form.mixed.play (Profile.update mixedProfile who μ)) hprev +
        (1 - w) * expectedUtility G.utility who
          (G.form.mixed.play (Profile.update mixedProfile who ν)) hpure := by
      exact expect_mix w hw0 hw1 _ _ (fun outcome => G.utility outcome who)
        hprev hpure
    _ = _ := by
      dsimp [w]
      rw [show 1 - (t + 1 : ℝ) / ((t + 1) + 1) =
        1 / ((t + 1) + 1) by field_simp; ring]

/-- The actual next empirical-update law is integrable whenever the previous
and newly played laws are. -/
theorem empirical_update_integrable
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ)
    (hprev : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who
          (G.form.empiricalMarginal history who (t + 1)))))
    (hpure : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who
          (PMF.pure (history (t + 1) who))))) :
    UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who
          (G.form.empiricalMarginal history who ((t + 1) + 1)))) := by
  exact Classical.choose
    (G.expectedUtility_update_empiricalMarginal_succ
      history mixedProfile who t hprev hpure)

/-- Difference form of the one-coordinate empirical expected-utility
recurrence. -/
theorem expectedUtility_update_empiricalMarginal_succ_sub
    (history : ℕ → Profile G.form.sig)
    (mixedProfile : Profile G.form.sig.mixed) (who : ι) (t : ℕ)
    (hprev : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who
          (G.form.empiricalMarginal history who (t + 1)))))
    (hnext : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who
          (G.form.empiricalMarginal history who ((t + 1) + 1)))))
    (hpure : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update mixedProfile who
          (PMF.pure (history (t + 1) who))))) :
      expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who ((t + 1) + 1)))) hnext -
      expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update mixedProfile who
            (G.form.empiricalMarginal history who (t + 1)))) hprev =
      (1 / ((t + 1) + 1 : ℝ)) *
        (expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update mixedProfile who
                (PMF.pure (history (t + 1) who)))) hpure -
          expectedUtility G.utility who
            (G.form.mixed.play
              (Profile.update mixedProfile who
                (G.form.empiricalMarginal history who (t + 1)))) hprev) := by
  obtain ⟨hnext', hrecurrence⟩ :=
    G.expectedUtility_update_empiricalMarginal_succ history mixedProfile who t
      hprev hpure
  have hnextEq : hnext' = hnext := Subsingleton.elim _ _
  rw [← hnextEq, hrecurrence]
  have hnonzero : ((t + 1) + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hnonzero]
  ring

/-- Against the current empirical belief, advancing one coordinate changes
that player's expected utility by the step size times its played gain. -/
theorem expectedUtility_belief_update_empiricalMarginal_succ_sub
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (who : ι) (t : ℕ) :
    ∃ hnext : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update (G.form.empiricalBelief history (t + 1)) who
          (G.form.empiricalMarginal history who ((t + 1) + 1)))),
    expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update (G.form.empiricalBelief history (t + 1)) who
            (G.form.empiricalMarginal history who ((t + 1) + 1)))) hnext -
      expectedUtility G.utility who
        (G.form.mixed.play (G.form.empiricalBelief history (t + 1)))
          (UtilityGame.IsFictitiousPlay.incumbent_integrable (G := G) hplay t who) =
      (1 / ((t + 1) + 1 : ℝ)) *
        G.playedGain history t who
          (UtilityGame.IsFictitiousPlay.incumbent_integrable (G := G)
            hplay t who)
          (IsFictitiousPlay.deviation_integrable (G := G) hplay t who
            (PMF.pure (history (t + 1) who))) := by
  let belief := G.form.empiricalBelief history (t + 1)
  let hbase := UtilityGame.IsFictitiousPlay.incumbent_integrable (G := G) hplay t who
  let hpure := IsFictitiousPlay.deviation_integrable (G := G) hplay t who
    (PMF.pure (history (t + 1) who))
  have hprev : UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update belief who (G.form.empiricalMarginal history who (t + 1)))) := by
    have heq : Profile.update belief who
        (G.form.empiricalMarginal history who (t + 1)) = belief :=
      Profile.update_eq_self _ _
    simpa only [heq] using hbase
  obtain ⟨hnext, hrecurrence⟩ :=
    G.expectedUtility_update_empiricalMarginal_succ history belief who t hprev hpure
  have hsame :
      Profile.update (G.form.empiricalBelief history (t + 1)) who
          (G.form.empiricalMarginal history who (t + 1)) =
        G.form.empiricalBelief history (t + 1) :=
    Profile.update_eq_self _ _
  refine ⟨hnext, ?_⟩
  have hplayed := IsFictitiousPlay.deviation_integrable (G := G) hplay t who
    (PMF.pure (history (t + 1) who))
  have hrecurrence' :
      expectedUtility G.utility who
          (G.form.mixed.play
            (Profile.update (G.form.empiricalBelief history (t + 1)) who
              (G.form.empiricalMarginal history who ((t + 1) + 1)))) hnext =
        ((t + 1 : ℝ) / ((t + 1) + 1)) *
            expectedUtility G.utility who
              (G.form.mixed.play (G.form.empiricalBelief history (t + 1))) hbase +
          (1 / ((t + 1) + 1 : ℝ)) *
            expectedUtility G.utility who
              (G.form.mixed.play
                (Profile.update (G.form.empiricalBelief history (t + 1)) who
                  (PMF.pure (history (t + 1) who)))) hpure := by
    simpa only [belief, hsame] using hrecurrence
  simp only [playedGain, mixedGain]
  rw [hrecurrence']
  field_simp
  ring_nf

/-- In a team game, the same empirical coordinate increment holds for every
observer's common payoff. -/
theorem IsTeamGame.expectedUtility_belief_update_empiricalMarginal_succ_sub
    (hteam : IsTeamGame G.utility)
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (observer who : ι) (t : ℕ) :
    ∃ hnext : UtilityIntegrable G.utility observer
      (G.form.mixed.play
        (Profile.update (G.form.empiricalBelief history (t + 1)) who
          (G.form.empiricalMarginal history who ((t + 1) + 1)))),
    expectedUtility G.utility observer
        (G.form.mixed.play
          (Profile.update (G.form.empiricalBelief history (t + 1)) who
            (G.form.empiricalMarginal history who ((t + 1) + 1)))) hnext -
      expectedUtility G.utility observer
        (G.form.mixed.play (G.form.empiricalBelief history (t + 1)))
        (payoffIntegrable_congr_on_support
          (fun outcome _ => hteam outcome who observer)
          (UtilityGame.IsFictitiousPlay.incumbent_integrable (G := G)
            hplay t who)) =
      (1 / ((t + 1) + 1 : ℝ)) * G.playedGain history t who
        (UtilityGame.IsFictitiousPlay.incumbent_integrable (G := G)
          hplay t who)
        (UtilityGame.IsFictitiousPlay.deviation_integrable (G := G)
          hplay t who (PMF.pure (history (t + 1) who))) := by
  obtain ⟨hnextWho, hresult⟩ :=
    G.expectedUtility_belief_update_empiricalMarginal_succ_sub hplay who t
  let hnextObserver := payoffIntegrable_congr_on_support
    (fun outcome _ => hteam outcome who observer) hnextWho
  refine ⟨hnextObserver, ?_⟩
  have hbaseWho :=
    UtilityGame.IsFictitiousPlay.incumbent_integrable (G := G) hplay t who
  have hbaseObserver := payoffIntegrable_congr_on_support
    (fun outcome _ => hteam outcome who observer) hbaseWho
  calc
    expectedUtility G.utility observer
        (G.form.mixed.play
          (Profile.update (G.form.empiricalBelief history (t + 1)) who
            (G.form.empiricalMarginal history who ((t + 1) + 1)))) hnextObserver -
      expectedUtility G.utility observer
        (G.form.mixed.play (G.form.empiricalBelief history (t + 1))) hbaseObserver =
      expectedUtility G.utility who
        (G.form.mixed.play
          (Profile.update (G.form.empiricalBelief history (t + 1)) who
            (G.form.empiricalMarginal history who ((t + 1) + 1)))) hnextWho -
      expectedUtility G.utility who
        (G.form.mixed.play (G.form.empiricalBelief history (t + 1))) hbaseWho := by
          rw [hteam.expectedUtility_eq _ observer who,
            hteam.expectedUtility_eq _ observer who]
    _ = _ := hresult

/-- The aggregate gain of the actions played at one fictitious-play round. -/
def aggregatePlayedGain (history : ℕ → Profile G.form.sig) (t : ℕ)
    (hbase : ∀ who, UtilityIntegrable G.utility who
      (G.form.mixed.play (G.form.empiricalBelief history (t + 1))))
    (hplayed : ∀ who, UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update (G.form.empiricalBelief history (t + 1)) who
          (PMF.pure (history (t + 1) who))))) : ℝ :=
  ∑ who, G.playedGain history t who (hbase who) (hplayed who)

/-- Played gain weighted by each player's number of pure actions. -/
def weightedPlayedGain [∀ who, Fintype (G.form.sig.Strategy who)]
    (history : ℕ → Profile G.form.sig) (t : ℕ)
    (hbase : ∀ who, UtilityIntegrable G.utility who
      (G.form.mixed.play (G.form.empiricalBelief history (t + 1))))
    (hplayed : ∀ who, UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update (G.form.empiricalBelief history (t + 1)) who
          (PMF.pure (history (t + 1) who))))) : ℝ :=
  ∑ who, (Fintype.card (G.form.sig.Strategy who) : ℝ) *
    G.playedGain history t who (hbase who) (hplayed who)

/-- Played gain with the incumbent and played-action certificates supplied by
the fictitious-play witness. -/
abbrev IsFictitiousPlay.playedGain
    {G₀ : UtilityGame.{uι, us, uo} ι}
    {history : ℕ → Profile G₀.form.sig}
    (hplay : G₀.IsFictitiousPlay history) (t : ℕ) (who : ι) : ℝ :=
  G₀.playedGain history t who
    (IsFictitiousPlay.incumbent_integrable (G := G₀) hplay t who)
    (IsFictitiousPlay.deviation_integrable (G := G₀) hplay t who
      (PMF.pure (history (t + 1) who)))

/-- Aggregate played gain using the integration certificates carried by a
fictitious-play witness. -/
abbrev IsFictitiousPlay.aggregatePlayedGain
    {G₀ : UtilityGame.{uι, us, uo} ι}
    {history : ℕ → Profile G₀.form.sig}
    (hplay : G₀.IsFictitiousPlay history) (t : ℕ) : ℝ :=
  G₀.aggregatePlayedGain history t
    (fun who => IsFictitiousPlay.incumbent_integrable (G := G₀) hplay t who)
    (fun who => IsFictitiousPlay.deviation_integrable (G := G₀) hplay t who
      (PMF.pure (history (t + 1) who)))

/-- Strategy-cardinality weighted played gain with certificates supplied by
fictitious play. -/
abbrev IsFictitiousPlay.weightedPlayedGain
    {G₀ : UtilityGame.{uι, us, uo} ι}
    [∀ who, Fintype (G₀.form.sig.Strategy who)]
    {history : ℕ → Profile G₀.form.sig}
    (hplay : G₀.IsFictitiousPlay history) (t : ℕ) : ℝ :=
  G₀.weightedPlayedGain history t
    (fun who => IsFictitiousPlay.incumbent_integrable (G := G₀) hplay t who)
    (fun who => IsFictitiousPlay.deviation_integrable (G := G₀) hplay t who
      (PMF.pure (history (t + 1) who)))

/-- A best-response action has nonnegative gain by averaging its guarded pure
deviations under the current mixed coordinate. -/
theorem IsFictitiousPlay.playedGain_nonneg
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) (who : ι) :
    0 ≤ G.playedGain history t who
      (UtilityGame.IsFictitiousPlay.incumbent_integrable (G := G) hplay t who)
      (UtilityGame.IsFictitiousPlay.deviation_integrable (G := G) hplay t who
        (PMF.pure (history (t + 1) who))) := by
  let belief := G.form.empiricalBelief history (t + 1)
  let played := history (t + 1) who
  let hbase := UtilityGame.IsFictitiousPlay.incumbent_integrable (G := G) hplay t who
  let hpure : ∀ action, UtilityIntegrable G.utility who
      (G.form.mixed.play
        (Profile.update belief who (PMF.pure action))) := fun action =>
    UtilityGame.IsFictitiousPlay.deviation_integrable (G := G) hplay t who (PMF.pure action)
  let hplayed := hpure played
  let q := fun action => G.form.mixed.play
    (Profile.update belief who (PMF.pure action))
  let values := fun action => expectedUtility G.utility who
    (q action) (hpure action)
  let playedValue := expectedUtility G.utility who (q played) hplayed
  have hlaw : G.form.mixed.play belief = (belief who).bind q := by
    calc
      G.form.mixed.play belief =
          G.form.mixed.play (Profile.update belief who (belief who)) := by
        rw [Profile.update_eq_self]
      _ = _ := GameForm.mixed_play_update G.form belief who (belief who)
  have hbind : UtilityIntegrable G.utility who ((belief who).bind q) :=
    payoffIntegrable_congr_law hlaw hbase
  have houter := payoffIntegrable_bind_conditionalExpectation
    (belief who) q (fun outcome => G.utility outcome who) hbind hpure
  have hvalues : PayoffIntegrable (belief who) values := by
    simpa only [values, expectedUtility] using houter
  have hconstant : PayoffIntegrable (belief who) (fun _ => playedValue) :=
    payoffIntegrable_constant (belief who) playedValue
  have hle : ∀ action ∈ (belief who).support, values action ≤ playedValue := by
    intro action _
    have hbest := hplay t who (PMF.pure action)
    rw [euPreference_apply] at hbest
    rcases hbest with ⟨_, _, hbest⟩
    simpa only [values, q, playedValue] using hbest
  have havg := expect_mono hle hvalues hconstant
  rw [expect_constant] at havg
  have hmean := expectedUtility_mixed_eq_expect
    G.form G.utility belief who hbase hpure
  have hbase_le : expectedUtility G.utility who
      (G.form.mixed.play belief) hbase ≤ playedValue := by
    rw [hmean]
    exact havg
  unfold UtilityGame.playedGain UtilityGame.mixedGain
  exact sub_nonneg.mpr hbase_le

theorem IsFictitiousPlay.aggregatePlayedGain_nonneg
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) :
    0 ≤ G.aggregatePlayedGain history t
      (fun who => UtilityGame.IsFictitiousPlay.incumbent_integrable (G := G) hplay t who)
      (fun who => UtilityGame.IsFictitiousPlay.deviation_integrable (G := G) hplay t who
        (PMF.pure (history (t + 1) who))) := by
  rw [UtilityGame.aggregatePlayedGain]
  exact Finset.sum_nonneg fun who _ =>
    UtilityGame.IsFictitiousPlay.playedGain_nonneg (G := G) hplay t who

/-- Under fictitious play, the total positive pure-deviation gap is bounded by
the strategy-cardinality-weighted gain of the actions actually played. -/
theorem IsFictitiousPlay.mixedImprovement_le_weightedPlayedGain
    [∀ who, Fintype (G.form.sig.Strategy who)]
    {history : ℕ → Profile G.form.sig}
    (hplay : G.IsFictitiousPlay history) (t : ℕ) :
    G.mixedImprovement (G.form.empiricalBelief history (t + 1))
        (fun who action =>
          UtilityGame.IsFictitiousPlay.deviation_integrable (G := G) hplay t who
            (PMF.pure action)) ≤
      G.weightedPlayedGain history t
        (fun who => UtilityGame.IsFictitiousPlay.incumbent_integrable (G := G)
          hplay t who)
        (fun who => UtilityGame.IsFictitiousPlay.deviation_integrable (G := G)
          hplay t who (PMF.pure (history (t + 1) who))) := by
  let hpure := fun who action =>
    UtilityGame.IsFictitiousPlay.deviation_integrable (G := G) hplay t who
      (PMF.pure action)
  rw [UtilityGame.mixedImprovement, UtilityGame.weightedPlayedGain]
  refine Finset.sum_le_sum fun who _ => ?_
  have hbase := UtilityGame.IsFictitiousPlay.incumbent_integrable
    (G := G) hplay t who
  have hplayedCert := UtilityGame.IsFictitiousPlay.deviation_integrable
    (G := G) hplay t who (PMF.pure (history (t + 1) who))
  have hplayed : 0 ≤ G.playedGain history t who hbase hplayedCert :=
    UtilityGame.IsFictitiousPlay.playedGain_nonneg (G := G) hplay t who
  have hpoint :
      ∀ action : G.form.sig.Strategy who,
        max (G.mixedGain (G.form.empiricalBelief history (t + 1)) who action
          hbase (hpure who action)) 0 ≤ G.playedGain history t who hbase hplayedCert := by
    intro action
    have hbest :=
      UtilityGame.IsFictitiousPlay.isBestResponse (G := G) hplay t who
        (PMF.pure action)
    rw [euPreference_apply] at hbest
    rcases hbest with ⟨_, _, hbest⟩
    apply max_le
    · unfold UtilityGame.playedGain UtilityGame.mixedGain
      linarith [hbest]
    · exact hplayed
  calc
    (∑ action : G.form.sig.Strategy who,
        max (G.mixedGain (G.form.empiricalBelief history (t + 1)) who action
          hbase (hpure who action)) 0) ≤
        ∑ _action : G.form.sig.Strategy who,
          G.playedGain history t who hbase hplayedCert :=
      Finset.sum_le_sum fun action _ => hpoint action
    _ = (Fintype.card (G.form.sig.Strategy who) : ℝ) *
        G.playedGain history t who hbase hplayedCert := by
      simp [Finset.sum_const, nsmul_eq_mul]

end UtilityGame

end GameTheory
