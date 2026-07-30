/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.AnalyticFinkPublicResponse

/-!
# Public action-frequency responses and the enforcement boundary

Joint actions and states are part of `StochasticGame.Hist`. Thus a selected
stage-response action has a direct public score: its realized indicator minus
its prescribed mixed-action probability. The score is bounded by one,
centered under prescribed mixing, and its drift under another mixed action is
exactly the amount by which that action is overweighted.

Contextual regret, stitched concentration, and sublinear charge ledgers can
control the statistical use of such bounded centered scores. They do not
choose a credible punishment profile, prove its sequential incentive
constraints, or preserve the node's target payoff. The final interface
therefore isolates the remaining strategic datum as a closer returning the
existing public-phase certificate. A finite one-state counterexample proves
that a positive public detector alone cannot supply this closer.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Filter Math Math.PMFProduct Math.Probability Set

variable {ι : Type} {G : StochasticGame ι}

/-- Public score of one selected action: its realized indicator minus its
probability under prescribed mixing. -/
def publicActionFrequencyScore
    (owner : ι) [DecidableEq (G.Act owner)]
    (baseline : PMF (G.Act owner)) (selected : G.Act owner)
    (jointAction : G.JointAct) : ℝ :=
  pmfCoordinateTestScore baseline selected true (jointAction owner)

/-- The action-frequency score has expectation equal to the selected
action's probability shift under any product mixed profile. -/
theorem expect_publicActionFrequencyScore_eq_difference
    [Fintype ι] [∀ i, Finite (G.Act i)]
    (owner : ι) [DecidableEq (G.Act owner)]
    (profile : ∀ i, PMF (G.Act i))
    (baseline : PMF (G.Act owner))
    (selected : G.Act owner) :
    expect (pmfPi profile)
        (G.publicActionFrequencyScore
          owner baseline selected) =
      (profile owner selected).toReal -
        (baseline selected).toReal := by
  calc
    expect (pmfPi profile)
        (G.publicActionFrequencyScore
          owner baseline selected) =
        expect
          (PMF.map (fun action : G.JointAct => action owner)
            (pmfPi profile))
          (pmfCoordinateTestScore baseline selected true) := by
            rw [expect_map]
            rfl
    _ = expect (profile owner)
          (pmfCoordinateTestScore baseline selected true) := by
        rw [show
          PMF.map (fun action : G.JointAct => action owner)
              (pmfPi profile) =
            profile owner by
          exact pmfPi_push_coord profile owner]
    _ = (profile owner selected).toReal -
          (baseline selected).toReal := by
        rw [expect_pmfCoordinateTestScore]
        simp

/-- Prescribed independent mixed play centers the public action-frequency
score exactly. -/
theorem expect_publicActionFrequencyScore_baseline_eq_zero
    [Fintype ι] [∀ i, Finite (G.Act i)]
    (owner : ι) [DecidableEq (G.Act owner)]
    (profile : ∀ i, PMF (G.Act i))
    (selected : G.Act owner) :
    expect (pmfPi profile)
        (G.publicActionFrequencyScore
          owner (profile owner) selected) = 0 := by
  rw [G.expect_publicActionFrequencyScore_eq_difference]
  exact sub_self _

/-- A deviation which overweights the selected action gives the public
frequency score strictly positive drift. -/
theorem expect_publicActionFrequencyScore_pos_of_overweight
    [Fintype ι] [∀ i, Finite (G.Act i)]
    (owner : ι) [DecidableEq (G.Act owner)]
    (prescribed comparison : ∀ i, PMF (G.Act i))
    (selected : G.Act owner)
    (hoverweight :
      (prescribed owner selected).toReal <
        (comparison owner selected).toReal) :
    0 <
      expect (pmfPi comparison)
        (G.publicActionFrequencyScore
          owner (prescribed owner) selected) := by
  rw [G.expect_publicActionFrequencyScore_eq_difference]
  exact sub_pos.mpr hoverweight

/-- The public action-frequency score is pointwise bounded by one. -/
theorem abs_publicActionFrequencyScore_le_one
    (owner : ι) [DecidableEq (G.Act owner)]
    (baseline : PMF (G.Act owner))
    (selected : G.Act owner)
    (jointAction : G.JointAct) :
    |G.publicActionFrequencyScore
      owner baseline selected jointAction| ≤ 1 := by
  exact abs_pmfCoordinateTestScore_le_one
    baseline selected true (jointAction owner)

/-- Removing the mass already assigned to a pure action quantitatively
limits the gain from switching to it. This elementary estimate is the bridge
from an analytic stage-gain margin to an action-frequency drift margin. -/
theorem sub_expect_le_two_mul_one_sub_apply
    {Ω : Type} [Finite Ω]
    (distribution : PMF Ω) (payoff : Ω → ℝ)
    (selected : Ω) (bound : ℝ)
    (hpayoff : ∀ action, |payoff action| ≤ bound) :
    payoff selected - expect distribution payoff ≤
      2 * bound * (1 - (distribution selected).toReal) := by
  classical
  have hdiff (action : Ω) :
      payoff selected - payoff action ≤ 2 * bound := by
    have hselected := abs_le.mp (hpayoff selected)
    have haction := abs_le.mp (hpayoff action)
    linarith
  have hindicator :
      expect distribution
          (fun action => if action = selected then (1 : ℝ) else 0) =
        (distribution selected).toReal := by
    letI : Fintype Ω := Fintype.ofFinite Ω
    rw [expect_eq_sum]
    simp
  calc
    payoff selected - expect distribution payoff =
        expect distribution
          (fun action => payoff selected - payoff action) := by
      rw [expect_sub, expect_const]
    _ ≤ expect distribution
          (fun action =>
            2 * bound *
              (1 - if action = selected then (1 : ℝ) else 0)) := by
      apply expect_mono
      intro action
      by_cases haction : action = selected
      · subst action
        simp
      · simpa [haction] using hdiff action
    _ = 2 * bound * (1 - (distribution selected).toReal) := by
      rw [expect_const_mul, expect_sub, expect_const, hindicator]

/-- A pure Fink stage gain is at most twice the payoff bound times the
probability mass missing from the selected action. -/
theorem finkStageGain_le_two_mul_one_sub_actionMass
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {V U : ℝ} (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain V) (s : G.State)
    (owner : ι) (selected : G.Act owner) :
    G.finkStageGain z s owner selected ≤
      2 * U *
        (1 -
          ((G.finkProfile z s owner) selected).toReal) := by
  classical
  let profile := G.finkProfile z s
  let purePayoff : G.Act owner → ℝ := fun action =>
    G.mixedStageEU s
      (Function.update profile owner (PMF.pure action)) owner
  have hpurePayoff (action : G.Act owner) :
      |purePayoff action| ≤ U := by
    exact abs_expect_le_of_abs_le _ _ fun jointAction =>
      hpay s jointAction owner
  haveI : Finite (G.stageGame s).Outcome :=
    inferInstanceAs (Finite G.JointAct)
  have hdecompose :
      G.mixedStageEU s profile owner =
        expect (profile owner) purePayoff := by
    have hupdate :=
      (G.stageGame s).mixedExtension_eu_update
        profile owner (profile owner)
    simpa [profile, purePayoff, mixedStageEU, stageGame,
      KernelGame.mixedExtension, KernelGame.eu,
      KernelGame.ofPureEU, GameForm.mixedExtension] using hupdate
  rw [finkStageGain]
  change purePayoff selected -
      G.mixedStageEU s profile owner ≤ _
  rw [hdecompose]
  exact sub_expect_le_two_mul_one_sub_apply
    (profile owner) purePayoff selected U hpurePayoff

/-- Under the unilateral pure comparison, action-frequency drift is exactly
the selected action's missing prescribed mass. -/
theorem expect_publicActionFrequencyScore_pureComparison_eq_missingMass
    [Fintype ι] [DecidableEq ι]
    [∀ i, Finite (G.Act i)]
    (owner : ι) [DecidableEq (G.Act owner)]
    (prescribed : ∀ i, PMF (G.Act i))
    (selected : G.Act owner) :
    expect
        (pmfPi
          (Function.update prescribed owner (PMF.pure selected)))
        (G.publicActionFrequencyScore
          owner (prescribed owner) selected) =
      1 - (prescribed owner selected).toReal := by
  rw [G.expect_publicActionFrequencyScore_eq_difference]
  simp

/-- A stage-gain lower margin transfers, with only the factor `2 * U`, to
the bounded public action-frequency detector. In particular, a power-law
stage margin retains the same exponent. -/
theorem div_two_mul_le_publicActionFrequencyDrift_of_le_finkStageGain
    [Fintype G.State] [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)]
    {V U margin : ℝ} (hU : 0 < U)
    (hpay : ∀ s a who, |G.stagePayoff s a who| ≤ U)
    (z : G.finkDomain V) (s : G.State)
    (owner : ι) [DecidableEq (G.Act owner)]
    (selected : G.Act owner)
    (hmargin : margin ≤ G.finkStageGain z s owner selected) :
    margin / (2 * U) ≤
      expect
        (pmfPi
          (Function.update (G.finkProfile z s)
            owner (PMF.pure selected)))
        (G.publicActionFrequencyScore
          owner (G.finkProfile z s owner) selected) := by
  rw [G.expect_publicActionFrequencyScore_pureComparison_eq_missingMass]
  have hgain :=
    G.finkStageGain_le_two_mul_one_sub_actionMass
      hpay z s owner selected
  apply (div_le_iff₀ (by positivity : 0 < 2 * U)).mpr
  simpa [mul_comm] using hmargin.trans hgain

namespace AnalyticFinkStagePublicResponse

/-- A stabilized analytic stage response is already an operational public
detector. At every sufficiently small valid parameter it is centered under
the prescribed Fink profile, bounded by one on every public joint action,
and has pure-comparison drift with the same power-law order as the stage
margin. The fixed payoff bound is independent of the varying Fink-domain
bound carried by `finkPointAt`. -/
theorem eventually_actionFrequencyDetector
    [Fintype G.State]
    [Fintype ι] [DecidableEq ι]
    [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)]
    {germ : G.AnalyticBellmanGerm}
    {response : Σ owner : ι, G.State × G.Act owner}
    (R : AnalyticFinkStagePublicResponse germ response)
    {U : ℝ} (hU : 0 < U)
    (hpay : ∀ s a owner, |G.stagePayoff s a owner| ≤ U) :
    ∀ᶠ t in nhdsWithin 0 (Ioi 0),
      ∀ ht : t ∈ Ioo (0 : ℝ) germ.radius,
        expect
            (pmfPi
              (G.finkProfile (germ.finkPointAt ht) response.2.1))
            (G.publicActionFrequencyScore
              response.1
              (G.finkProfile
                (germ.finkPointAt ht) response.2.1 response.1)
              response.2.2) = 0 ∧
          R.margin / (2 * U) * t ^ R.order ≤
            expect
              (pmfPi
                (Function.update
                  (G.finkProfile
                    (germ.finkPointAt ht) response.2.1)
                  response.1 (PMF.pure response.2.2)))
              (G.publicActionFrequencyScore
                response.1
                (G.finkProfile
                  (germ.finkPointAt ht) response.2.1 response.1)
                response.2.2) ∧
          ∀ jointAction,
            |G.publicActionFrequencyScore
                response.1
                (G.finkProfile
                  (germ.finkPointAt ht) response.2.1 response.1)
                response.2.2 jointAction| ≤ 1 := by
  classical
  filter_upwards [R.eventually_semanticMargin] with t hsemantic
  intro ht
  have hgain := hsemantic ht
  refine ⟨?_, ?_, ?_⟩
  · exact G.expect_publicActionFrequencyScore_baseline_eq_zero
      response.1
      (G.finkProfile (germ.finkPointAt ht) response.2.1)
      response.2.2
  · have hbridge :=
      G.div_two_mul_le_publicActionFrequencyDrift_of_le_finkStageGain
        hU hpay (germ.finkPointAt ht) response.2.1
        response.1 response.2.2 hgain.1
    calc
      R.margin / (2 * U) * t ^ R.order =
          (R.margin * t ^ R.order) / (2 * U) := by ring
      _ ≤ _ := hbridge
  · intro jointAction
    exact G.abs_publicActionFrequencyScore_le_one
      response.1
      (G.finkProfile
        (germ.finkPointAt ht) response.2.1 response.1)
      response.2.2 jointAction

end AnalyticFinkStagePublicResponse

/-- The same score read from a completed publicly observed stage of a game
history. -/
def historyActionFrequencyScore
    (owner : ι) [DecidableEq (G.Act owner)]
    (baseline : PMF (G.Act owner))
    (selected : G.Act owner)
    {t : ℕ} (history : G.Hist t) (stage : Fin t) : ℝ :=
  G.publicActionFrequencyScore
    owner baseline selected (history.1 stage).2

/-- The exact remaining strategic interface after detector construction.

The response may contain contextual learners, stitched boundaries, reset
budgets, and ledger proofs. A closer must additionally turn each such
response into a credible, target-preserving public-phase punishment system.
No weaker detector-only premise can imply this conclusion in general. -/
structure CredibleTargetPreservingPublicResponseCloserAt
    (G : StochasticGame ι) [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    (s₀ : G.State) (v : Payoff ι) (δ : ℝ)
    (Response : Type) where
  closeResponse :
    Response → G.IsPublicPhasePunishmentSystemAt s₀ v δ

/-- Detector accounting plus the explicit strategic closer yields exactly
the local certificate required by `PublicLocalResponseRecursionAt`. -/
theorem isPublicPhasePunishmentSystemAt_of_publicResponseCloser
    [Fintype ι] [DecidableEq ι]
    [Finite G.State] [∀ i, Finite (G.Act i)]
    {s₀ : G.State} {v : Payoff ι} {δ : ℝ}
    {Response : Type}
    (closer :
      G.CredibleTargetPreservingPublicResponseCloserAt
        s₀ v δ Response)
    (response : Response) :
    G.IsPublicPhasePunishmentSystemAt s₀ v δ :=
  closer.closeResponse response

namespace ActionDetectorNoAutomaticCloser

abbrev Player := Unit
abbrev State := Unit
abbrev Action := Bool

/-- A one-state decision problem with payoff one for action `true` and zero
for action `false`. -/
def game : StochasticGame Player where
  State := State
  Act := fun _ => Action
  stagePayoff := fun _ action _ => if action () then 1 else 0
  transition := fun _ _ => PMF.pure ()
  discount := 0
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

instance : Fintype game.State :=
  inferInstanceAs (Fintype State)

instance : DecidableEq game.State :=
  inferInstanceAs (DecidableEq State)

instance (who : Player) : Fintype (game.Act who) :=
  inferInstanceAs (Fintype Action)

instance (who : Player) : DecidableEq (game.Act who) :=
  inferInstanceAs (DecidableEq Action)

/-- Prescribed play mixes the two publicly observed actions equally. -/
def prescribedProfile : ∀ _ : Player, PMF Action :=
  fun _ => PMF.uniformOfFintype Action

/-- The comparison behavior puts all mass on the selected action. -/
def comparisonProfile : ∀ _ : Player, PMF Action :=
  fun _ => PMF.pure true

/-- The selected public action-frequency detector is centered under
prescribed play and has positive drift under the comparison behavior. -/
theorem centered_and_positive_action_detector :
    expect (pmfPi prescribedProfile)
        (game.publicActionFrequencyScore
          () (prescribedProfile ()) true) = 0 ∧
      0 <
        expect (pmfPi comparisonProfile)
          (game.publicActionFrequencyScore
            () (prescribedProfile ()) true) := by
  constructor
  · exact game.expect_publicActionFrequencyScore_baseline_eq_zero
      () prescribedProfile true
  · exact game.expect_publicActionFrequencyScore_pos_of_overweight
      () prescribedProfile comparisonProfile true (by
        change
          ((PMF.uniformOfFintype Bool) true).toReal <
            ((PMF.pure true) true).toReal
        norm_num [PMF.uniformOfFintype_apply, PMF.pure_apply])

/-- The out-of-range target used to show that detection alone cannot create
a target-preserving public-phase certificate. -/
def impossibleTarget : Payoff Player := fun _ => 3

/-- Despite the positive bounded public detector, there is no public-phase
punishment certificate at this target and positive accuracy. -/
theorem not_isPublicPhasePunishmentSystemAt_impossibleTarget :
    ¬game.IsPublicPhasePunishmentSystemAt
      () impossibleTarget (1 / 4 : ℝ) := by
  intro hphase
  have hcert :=
    game.isAdaptivePotentialCertificateAt_of_isPublicPhasePunishmentSystemAt
      () impossibleTarget (1 / 4 : ℝ) hphase
  obtain ⟨profile, horizon, lowerPotential, upperPotential,
      deviationPotential, lowerError, upperError, deviationError,
      hhorizon, hlowerInitial, _hupperInitial, _hdeviationInitial,
      hlowerMono, hlowerStage, _hupperMono, _hupperStage,
      _hdeviationMono, _hdeviationStage,
      hlowerCesaro, _hupperCesaro, _hdeviationCesaro⟩ := hcert
  have hhorizonPos : 0 < horizon := by omega
  have hlower :=
    game.finiteAveragePayoff_ge_of_expectedHistoryValue_submartingale_le
      profile () () (lowerPotential ()) (lowerError ())
      (hlowerMono ()) (hlowerStage ()) hhorizonPos
  rw [game.expectedHistoryValue_zero] at hlower
  have hinitial := hlowerInitial ()
  have hcesaro := hlowerCesaro () horizon le_rfl
  have hpayoffBound :
      |game.finiteAveragePayoff () horizon profile ()| ≤ 1 := by
    apply game.abs_finiteAveragePayoff_le (by norm_num)
    intro state action
    simp only [game]
    split <;> norm_num
  rw [abs_le] at hinitial hpayoffBound
  simp only [impossibleTarget] at hinitial
  linarith

/-- Concrete no-go statement: bounded centered positive drift does not imply
automatic public-phase closure, even in a one-state one-player game. -/
theorem detector_but_no_automatic_publicPhaseCloser :
    (expect (pmfPi prescribedProfile)
          (game.publicActionFrequencyScore
            () (prescribedProfile ()) true) = 0 ∧
        0 <
          expect (pmfPi comparisonProfile)
            (game.publicActionFrequencyScore
              () (prescribedProfile ()) true)) ∧
      ¬game.IsPublicPhasePunishmentSystemAt
        () impossibleTarget (1 / 4 : ℝ) :=
  ⟨centered_and_positive_action_detector,
    not_isPublicPhasePunishmentSystemAt_impossibleTarget⟩

end ActionDetectorNoAutomaticCloser

end StochasticGame
end GameTheory
