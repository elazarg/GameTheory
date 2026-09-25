/-
# Mixed versus pure rationalizability hostile fixture

The row player's third action pays `3/4` against every column.  Neither of the
first two actions purely dominates it, but their half/half mixture pays `1`
against every column. This separates the first mixed-elimination round from
the first pure round. No all-round inclusion between the survivor iterations
is assumed.
-/

import GameTheory.Finite.Correctness
import GameTheory.Core.Rationalizability

noncomputable section

namespace GameTheory.Tests.Rationalizability

open GameTheory GameTheory.Finite GameTheory.Math.Probability

/-- Row payoffs for the hostile three-action game. -/
def rowPayoff (row column : Fin 3) : ℚ :=
  if row = 0 then
    if column = 0 then 2 else if column = 1 then 0 else 1
  else if row = 1 then
    if column = 0 then 0 else if column = 1 then 2 else 1
  else 3 / 4

/-- Only player zero's incentives matter; player one's payoff is constant. -/
@[reducible]
def mixedDominanceGame : TableGame (Fin 2) where
  Action _ := Fin 3
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff profile player :=
    if player = 0 then rowPayoff (profile 0) (profile 1) else 0

/-- The half/half hedge between the first two row actions. -/
def hedge : PMF (Fin 3) :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure 0) (PMF.pure 1)

/-- The hedge strictly dominates the third action against every column. -/
theorem third_strictlyDominatedByMixed :
    StrictlyDominatedByMixed mixedDominanceGame.toForm
      (euPreference mixedDominanceGame.utility) 0 2 := by
  refine ⟨hedge, fun profile => ?_⟩
  have hpreferred : UtilityIntegrable mixedDominanceGame.utility 0
      (randomizedDeviationOutcome mixedDominanceGame.toForm profile 0 hedge) :=
    payoffIntegrable_of_finite _ _
  have halternative : UtilityIntegrable mixedDominanceGame.utility 0
      (mixedDominanceGame.toForm.play (Profile.update profile 0 2)) :=
    payoffIntegrable_of_finite _ _
  apply (euPreference_strict_iff _ _ _ _ hpreferred halternative).mpr
  have hlaw : randomizedDeviationOutcome mixedDominanceGame.toForm profile 0 hedge =
      mix (1 / 2) (by norm_num) (by norm_num)
        (mixedDominanceGame.toForm.play (Profile.update profile 0 0))
        (mixedDominanceGame.toForm.play (Profile.update profile 0 1)) := by
    rw [randomizedDeviationOutcome_eq_bind, hedge, mix_bind,
      PMF.pure_bind, PMF.pure_bind]
  have hfirst : UtilityIntegrable mixedDominanceGame.utility 0
      (mixedDominanceGame.toForm.play (Profile.update profile 0 0)) :=
    payoffIntegrable_pure _ _
  have hsecond : UtilityIntegrable mixedDominanceGame.utility 0
      (mixedDominanceGame.toForm.play (Profile.update profile 0 1)) :=
    payoffIntegrable_pure _ _
  have hmix : UtilityIntegrable mixedDominanceGame.utility 0
      (mix (1 / 2) (by norm_num) (by norm_num)
        (mixedDominanceGame.toForm.play (Profile.update profile 0 0))
        (mixedDominanceGame.toForm.play (Profile.update profile 0 1))) :=
    payoffIntegrable_mix _ _ _ _ _ _ hfirst hsecond
  have hvalue :
      expectedUtility mixedDominanceGame.utility 0
        (randomizedDeviationOutcome mixedDominanceGame.toForm profile 0 hedge)
        hpreferred =
      (1 / 2) * expectedUtility mixedDominanceGame.utility 0
        (mixedDominanceGame.toForm.play (Profile.update profile 0 0)) hfirst +
      (1 - 1 / 2) * expectedUtility mixedDominanceGame.utility 0
        (mixedDominanceGame.toForm.play (Profile.update profile 0 1)) hsecond := by
    calc
      _ = expectedUtility mixedDominanceGame.utility 0 _ hmix :=
        expectedUtility_congr_law _ _ hlaw hpreferred hmix
      _ = _ := expectedUtility_mix _ _ _ _ _ _ _ hfirst hsecond
  rw [hvalue]
  generalize hcolumn : profile (1 : Fin 2) = column
  fin_cases column
  all_goals simp [mixedDominanceGame, rowPayoff, hcolumn,
    expectedUtility_pure, Profile.update_same, Profile.update_of_ne]
  all_goals norm_num

/-- A profile exposing one selected column; the row coordinate is overwritten
by every dominance comparison. -/
def atColumn (column : Fin 3) : Profile mixedDominanceGame.sig :=
  fun player => if player = 0 then 2 else column

/-- No pure action strictly dominates the third action. -/
theorem third_not_strictlyDominatedByPure (preferred : Fin 3) :
    ¬ StrictlyDominates mixedDominanceGame.toForm
      (euPreference mixedDominanceGame.utility) 0 preferred 2 := by
  fin_cases preferred
  · intro hdom
    have h := hdom (atColumn 1) (fun _ => Set.mem_univ _)
    rw [euPreference_strict_iff _ _ _ _
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)] at h
    norm_num [mixedDominanceGame, rowPayoff, atColumn,
      expectedUtility_pure] at h
  · intro hdom
    have h := hdom (atColumn 0) (fun _ => Set.mem_univ _)
    rw [euPreference_strict_iff _ _ _ _
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)] at h
    norm_num [mixedDominanceGame, rowPayoff, atColumn,
      expectedUtility_pure] at h
  · intro hdom
    have h := hdom (atColumn 0) (fun _ => Set.mem_univ _)
    rw [euPreference_strict_iff _ _ _ _
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)] at h
    norm_num [mixedDominanceGame, rowPayoff, atColumn,
      expectedUtility_pure] at h

/-- The third action survives the first pure-elimination round. -/
theorem third_mem_pureSurvivors_one :
    (2 : Fin 3) ∈ pureSurvivors mixedDominanceGame.toForm
      (euPreference mixedDominanceGame.utility) 1 0 := by
  rw [mem_pureSurvivors_succ]
  refine ⟨Set.mem_univ _, ?_⟩
  intro preferred _ hdom
  exact third_not_strictlyDominatedByPure preferred hdom

/-- The executable checker computes that same pure survivor fact. -/
theorem third_mem_executable_pureSurvivors_one :
    (2 : Fin 3) ∈ mixedDominanceGame.pureSurvivors 1 0 :=
  (TableGame.mem_pureSurvivors_iff mixedDominanceGame 1 0 2).2
    third_mem_pureSurvivors_one

/-- Standard mixed elimination removes the third action in the first round. -/
theorem third_not_mem_correlatedSurvivors_one :
    (2 : Fin 3) ∉ correlatedSurvivors mixedDominanceGame.toForm
      (euPreference mixedDominanceGame.utility) 1 0 := by
  intro hsurvives
  apply hsurvives.2
  obtain ⟨replacement, hdominates⟩ := third_strictlyDominatedByMixed
  exact ⟨replacement, fun action _ => Set.mem_univ action,
    fun profile _ => hdominates profile⟩

/-- Consequently the third action is not correlated rationalizable. -/
theorem third_not_isCorrelatedRationalizable :
    ¬ IsCorrelatedRationalizable mixedDominanceGame.toForm
      (euPreference mixedDominanceGame.utility) 0 2 := by
  intro hrationalizable
  exact third_not_mem_correlatedSurvivors_one (hrationalizable 1)

/-! ## Very weak versus textbook weak dominance -/

@[reducible]
def constantGame : TableGame Unit where
  Action _ := Bool
  actionFintype _ := inferInstance
  actionDecEq _ := inferInstance
  payoff _ _ := 0

/-- Equal-payoff actions dominate one another only in the reflexive,
everywhere-weak sense used by dominant strategies. -/
theorem true_veryWeaklyDominates_false :
    VeryWeaklyDominates constantGame.toForm
      (euPreference constantGame.utility) () true false :=
  (TableGame.veryWeaklyDominates_eq_true_iff constantGame () true false).1
    (by decide)

/-- Textbook weak dominance additionally requires a strict witness, so it
correctly rejects two payoff-identical actions. -/
theorem true_not_weaklyDominates_false :
    ¬ WeaklyDominates constantGame.toForm
      (euPreference constantGame.utility) () true false := by
  rw [← TableGame.weaklyDominates_eq_true_iff]
  decide

/-- The Nash-survival theorem gives a positive independent-rationalizability
consumer on the payoff-constant control. -/
theorem false_isIndependentRationalizable :
    IsIndependentRationalizable constantGame.toForm
      (euPreference constantGame.utility) () false := by
  have hnash :
      IsNash constantGame.toForm (euPreference constantGame.utility)
        (fun _ => false) := by
    rw [TableGame.isNash_toForm_iff]
    simp [constantGame]
  exact hnash.isIndependentRationalizable ()

theorem false_isCorrelatedRationalizable_from_independent :
    IsCorrelatedRationalizable constantGame.toForm
      (euPreference constantGame.utility) () false :=
  false_isIndependentRationalizable.isCorrelatedRationalizable_of_finite
    (fun _ _ => payoffIntegrable_of_finite _ _)

/-! ## Independent versus correlated beliefs -/

namespace IndependentSeparation

/-- One focal player and two separately acting opponents. -/
abbrev Player := Option Bool

/-- The focal player has three actions; each opponent has two. -/
@[reducible]
def Strategy : Player → Type
  | none => Fin 3
  | some _ => Bool

@[reducible]
def sig : GameSignature Player where
  Strategy := Strategy
  Outcome := Fin 3 × Bool × Bool

def realizedOutcome (profile : Profile sig) : sig.Outcome :=
  (profile none, profile (some false), profile (some true))

abbrev form : GameForm Player :=
  GameForm.deterministic sig realizedOutcome

/-- The candidate action `0` pays zero. Actions `1` and `2` have opposite
diagonal payoffs and both reward mismatch between the opponents. -/
def focalPayoff (action : Fin 3) (left right : Bool) : ℝ :=
  if action = 0 then 0
  else if action = 1 then
    if left = right then (if left then -1 else 1) else 2
  else if left = right then (if left then 1 else -1) else 2

def utility : Utility sig :=
  fun outcome who => if who = none then focalPayoff outcome.1 outcome.2.1 outcome.2.2 else 0

/-- The two opponents are canonically indexed by their Boolean labels. -/
def opponentEquiv : Bool ≃ {who : Player // who ≠ none} where
  toFun bit := ⟨some bit, Option.some_ne_none bit⟩
  invFun who := who.1.get (Option.ne_none_iff_isSome.mp who.2)
  left_inv bit := Option.get_some bit _
  right_inv who :=
    Subtype.ext (Option.some_get (x := who.1) _)

abbrev OpponentStrategy (who : {who : Player // who ≠ none}) : Type :=
  Strategy who.1

abbrev opponentProfileEquiv :
    (∀ who, OpponentStrategy who) ≃
      (∀ bit : Bool, Strategy (some bit)) :=
  (Equiv.piCongrLeft OpponentStrategy opponentEquiv).symm

theorem mixed_play_eq_map (beliefs : Profile sig.mixed) :
    form.mixed.play beliefs = (independentProduct beliefs).map realizedOutcome :=
  rfl

/-- Overwriting the focal marginal exposes exactly the independent product of
the two opponent laws. -/
theorem mixed_play_update_focal (beliefs : Profile sig.mixed)
    (action : Fin 3) :
    form.mixed.play (Profile.update beliefs none (PMF.pure action)) =
      (independentProduct fun bit : Bool => beliefs (some bit)).map
        (fun opponents : ∀ bit : Bool, Strategy (some bit) =>
          (action, opponents false, opponents true)) := by
  rw [mixed_play_eq_map,
    independentProduct_splitAt (Profile.update beliefs none (PMF.pure action)) none,
    PMF.map_bind, Profile.update_same, PMF.pure_bind, PMF.map_comp]
  have hrest :
      (fun who : {who : Player // who ≠ none} =>
        Profile.update beliefs none (PMF.pure action) who.1) =
        fun who : {who : Player // who ≠ none} => beliefs who.1 := by
    funext who
    exact Profile.update_of_ne _ _ who.2
  rw [hrest]
  have hreindex := independentProduct_reindex
    (A := OpponentStrategy) opponentEquiv.symm
    (fun who : {who : Player // who ≠ none} => beliefs who.1)
  have htarget :
      (fun bit : Bool => beliefs (opponentEquiv bit).1) =
        fun bit => beliefs (some bit) := rfl
  simp only [Equiv.symm_symm] at hreindex
  rw [htarget] at hreindex
  have hreindex' :
      (independentProduct fun who : {who : Player // who ≠ none} =>
        beliefs who.1).map opponentProfileEquiv =
      independentProduct (fun bit : Bool => beliefs (some bit)) := by
    exact hreindex
  calc
    (independentProduct fun who : {who : Player // who ≠ none} => beliefs who.1).map
        (realizedOutcome ∘ fun rest =>
          (Equiv.piSplitAt none sig.Strategy).symm (action, rest)) =
      ((independentProduct fun who : {who : Player // who ≠ none} =>
          beliefs who.1).map opponentProfileEquiv).map
        (fun opponents => (action, opponents false, opponents true)) := by
      rw [PMF.map_comp]
      congr 1
    _ = _ := by rw [hreindex']

def probTrue (beliefs : Profile sig.mixed) (opponent : Bool) : ℝ :=
  ((beliefs (some opponent)) true).toReal

theorem probFalse (beliefs : Profile sig.mixed) (opponent : Bool) :
    ((beliefs (some opponent)) false).toReal = 1 - probTrue beliefs opponent := by
  have htotal := expect_constant (beliefs (some opponent)) (1 : ℝ)
    (payoffIntegrable_constant _ 1)
  simp only [expect, tsum_fintype, Fintype.sum_bool, mul_one] at htotal
  unfold probTrue
  linarith

private def opponentsTT : ∀ bit : Bool, Strategy (some bit) :=
  fun _ => true

private def opponentsFT : ∀ bit : Bool, Strategy (some bit) :=
  fun bit => !bit

private def opponentsTF : ∀ bit : Bool, Strategy (some bit) :=
  fun bit => bit

private def opponentsFF : ∀ bit : Bool, Strategy (some bit) :=
  fun _ => false

private theorem opponentProfiles :
    (Finset.univ : Finset (∀ bit : Bool, Strategy (some bit))) =
      {opponentsTT, opponentsFT, opponentsTF, opponentsFF} := by
  decide

/-- Expected payoff of the first alternative as a polynomial in the two
opponents' independent `true` probabilities. -/
theorem expectedUtility_action_one (beliefs : Profile sig.mixed) :
    expectedUtility utility none
        (form.mixed.play
          (Profile.update beliefs none (PMF.pure (1 : Fin 3))))
        (payoffIntegrable_of_finite _ _) =
      1 + probTrue beliefs false + probTrue beliefs true -
        4 * probTrue beliefs false * probTrue beliefs true := by
  have hmap : UtilityIntegrable utility none
      ((independentProduct fun bit : Bool => beliefs (some bit)).map
        (fun opponents : ∀ bit : Bool, Strategy (some bit) =>
          ((1 : Fin 3), opponents false, opponents true))) :=
    payoffIntegrable_of_finite _ _
  calc
    _ = expectedUtility utility none _ hmap :=
      expectedUtility_congr_law utility none (mixed_play_update_focal beliefs 1)
        (payoffIntegrable_of_finite _ _) hmap
    _ = _ := by
      rw [expectedUtility_map]
      simp only [expectedUtility]
      rw [expect_eq_sum, opponentProfiles,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [independentProduct_apply, Fintype.prod_bool,
        ENNReal.toReal_mul]
      simp only [opponentsTT, opponentsFT, opponentsTF, opponentsFF, Bool.not_true,
        Bool.not_false]
      rw [probFalse, probFalse]
      norm_num [utility, focalPayoff, probTrue]
      ring

/-- Expected payoff of the second alternative under the same product belief. -/
theorem expectedUtility_action_two (beliefs : Profile sig.mixed) :
    expectedUtility utility none
        (form.mixed.play
          (Profile.update beliefs none (PMF.pure (2 : Fin 3))))
        (payoffIntegrable_of_finite _ _) =
      -1 + 3 * probTrue beliefs false + 3 * probTrue beliefs true -
        4 * probTrue beliefs false * probTrue beliefs true := by
  have hmap : UtilityIntegrable utility none
      ((independentProduct fun bit : Bool => beliefs (some bit)).map
        (fun opponents : ∀ bit : Bool, Strategy (some bit) =>
          ((2 : Fin 3), opponents false, opponents true))) :=
    payoffIntegrable_of_finite _ _
  calc
    _ = expectedUtility utility none _ hmap :=
      expectedUtility_congr_law utility none (mixed_play_update_focal beliefs 2)
        (payoffIntegrable_of_finite _ _) hmap
    _ = _ := by
      rw [expectedUtility_map]
      simp only [expectedUtility]
      rw [expect_eq_sum, opponentProfiles,
        Finset.sum_insert (by decide), Finset.sum_insert (by decide),
        Finset.sum_insert (by decide), Finset.sum_singleton]
      simp only [independentProduct_apply, Fintype.prod_bool,
        ENNReal.toReal_mul]
      simp only [opponentsTT, opponentsFT, opponentsTF, opponentsFF, Bool.not_true,
        Bool.not_false]
      rw [probFalse, probFalse]
      norm_num [utility, focalPayoff, probTrue]
      ring

theorem expectedUtility_action_zero (beliefs : Profile sig.mixed) :
    expectedUtility utility none
        (form.mixed.play
          (Profile.update beliefs none (PMF.pure (0 : Fin 3))))
        (payoffIntegrable_of_finite _ _) = 0 := by
  have hmap : UtilityIntegrable utility none
      ((independentProduct fun bit : Bool => beliefs (some bit)).map
        (fun opponents : ∀ bit : Bool, Strategy (some bit) =>
          ((0 : Fin 3), opponents false, opponents true))) :=
    payoffIntegrable_of_finite _ _
  calc
    _ = expectedUtility utility none _ hmap :=
      expectedUtility_congr_law utility none (mixed_play_update_focal beliefs 0)
        (payoffIntegrable_of_finite _ _) hmap
    _ = 0 := by
      rw [expectedUtility_map]
      exact expect_constant _ 0 _

/-- No product of opponent beliefs makes the candidate a best response. -/
theorem zero_not_independentBestResponse (beliefs : Profile sig.mixed) :
    ¬ IsIndependentBestResponse form (euPreference utility) none
      (0 : Fin 3) beliefs := by
  intro best
  have hone := (euPreference_iff utility none _ _
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).mp
    (best (1 : Fin 3))
  have htwo := (euPreference_iff utility none _ _
    (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).mp
    (best (2 : Fin 3))
  rw [expectedUtility_action_zero, expectedUtility_action_one] at hone
  rw [expectedUtility_action_zero, expectedUtility_action_two] at htwo
  have hp_nonneg : 0 ≤ probTrue beliefs false := ENNReal.toReal_nonneg
  have hp_le : probTrue beliefs false ≤ 1 := by
    have hfalse := probFalse beliefs false
    have hnonneg : 0 ≤ ((beliefs (some false)) false).toReal :=
      ENNReal.toReal_nonneg
    linarith
  have hq_nonneg : 0 ≤ probTrue beliefs true := ENNReal.toReal_nonneg
  have hq_le : probTrue beliefs true ≤ 1 := by
    have hfalse := probFalse beliefs true
    have hnonneg : 0 ≤ ((beliefs (some true)) false).toReal :=
      ENNReal.toReal_nonneg
    linarith
  have hcross_left :
      0 ≤ probTrue beliefs false * (1 - probTrue beliefs true) :=
    mul_nonneg hp_nonneg (sub_nonneg.mpr hq_le)
  have hcross_right :
      0 ≤ (1 - probTrue beliefs false) * probTrue beliefs true :=
    mul_nonneg (sub_nonneg.mpr hp_le) hq_nonneg
  nlinarith

theorem zero_not_mem_independentSurvivors_one :
    (0 : Fin 3) ∉
      independentSurvivors form (euPreference utility) 1 none := by
  intro survives
  obtain ⟨_, beliefs, _, best⟩ := survives
  exact zero_not_independentBestResponse beliefs best

theorem zero_not_isIndependentRationalizable :
    ¬ IsIndependentRationalizable form (euPreference utility) none
      (0 : Fin 3) := by
  intro rationalizable
  exact zero_not_mem_independentSurvivors_one (rationalizable 1)

/-- A pure profile putting both opponents on the same Boolean action. -/
@[reducible]
def diagonalProfile (bit : Bool) : Profile sig :=
  fun who => match who with
    | none => 0
    | some _ => bit

theorem diagonal_randomized_law (replacement : PMF (Fin 3)) (bit : Bool) :
    randomizedDeviationOutcome form (diagonalProfile bit) none replacement =
      replacement.map (fun action => (action, bit, bit)) := by
  rw [randomizedDeviationOutcome_eq_bind]
  have hkernel :
      (fun action : Fin 3 =>
        form.play (Profile.update (diagonalProfile bit) none action)) =
        (PMF.pure ∘ fun action : Fin 3 => (action, bit, bit)) := by
    funext action
    simp [form, realizedOutcome, diagonalProfile, Profile.update_same,
      Profile.update_of_ne]
  rw [hkernel, PMF.bind_pure_comp]

theorem diagonal_randomized_value (replacement : PMF (Fin 3)) (bit : Bool) :
    expectedUtility utility none
      (randomizedDeviationOutcome form (diagonalProfile bit) none replacement)
      (payoffIntegrable_of_finite _ _) =
    expect replacement (fun action => focalPayoff action bit bit)
      (payoffIntegrable_of_finite _ _) := by
  have hmap : UtilityIntegrable utility none
      (replacement.map (fun action => (action, bit, bit))) :=
    payoffIntegrable_of_finite _ _
  calc
    _ = expectedUtility utility none _ hmap :=
      expectedUtility_congr_law utility none
        (diagonal_randomized_law replacement bit)
        (payoffIntegrable_of_finite _ _) hmap
    _ = _ := by
      rw [expectedUtility_map]
      rfl

/-- The focal candidate and every constant-utility opponent action survive
every correlated-elimination round. The focal proof uses both diagonal
profiles: every replacement's two diagonal expected payoffs sum to zero, so it
cannot improve strictly at both. -/
theorem zero_and_opponents_survive_correlated :
    ∀ round,
      (0 : Fin 3) ∈
          correlatedSurvivors form (euPreference utility) round none ∧
        ∀ label action,
          action ∈ correlatedSurvivors form (euPreference utility) round
            (some label) := by
  intro round
  induction round with
  | zero => exact ⟨Set.mem_univ _, fun _ _ => Set.mem_univ _⟩
  | succ round ih =>
      constructor
      · refine ⟨ih.1, ?_⟩
        rintro ⟨replacement, _, dominates⟩
        have hsurvives (bit : Bool) :
            ∀ player,
              diagonalProfile bit player ∈
                correlatedSurvivors form (euPreference utility) round player := by
          intro player
          cases player with
          | none => exact ih.1
          | some label => exact ih.2 label bit
        have hfalse := dominates (diagonalProfile false) (hsurvives false)
        have htrue := dominates (diagonalProfile true) (hsurvives true)
        rw [euPreference_strict_iff _ _ _ _
          (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
          at hfalse htrue
        have hbase (bit : Bool) :
            expectedUtility utility none
              (form.play (Profile.update (diagonalProfile bit) none 0))
              (payoffIntegrable_of_finite _ _) = 0 := by
          simp [form, realizedOutcome, diagonalProfile, utility, focalPayoff,
            expectedUtility_pure, Profile.update_same, Profile.update_of_ne]
        rw [hbase false, diagonal_randomized_value] at hfalse
        rw [hbase true, diagonal_randomized_value] at htrue
        have hf : PayoffIntegrable replacement
            (fun action => focalPayoff action false false) :=
          payoffIntegrable_of_finite _ _
        have hg : PayoffIntegrable replacement
            (fun action => focalPayoff action true true) :=
          payoffIntegrable_of_finite _ _
        have hsum :
            expect replacement (fun action => focalPayoff action false false) hf +
                expect replacement (fun action => focalPayoff action true true) hg = 0 := by
          rw [← expect_add hf hg]
          calc
            _ = expect replacement (fun _ => 0)
                (payoffIntegrable_constant replacement 0) := by
              apply expect_congr_on_support
              intro action _
              fin_cases action <;> norm_num [focalPayoff]
            _ = 0 := expect_constant replacement 0 _
        linarith
      · intro label action
        refine ⟨ih.2 label action, ?_⟩
        rintro ⟨replacement, _, dominates⟩
        have hsurvives :
            ∀ player,
              diagonalProfile false player ∈
                correlatedSurvivors form (euPreference utility) round player := by
          intro player
          cases player with
          | none => exact ih.1
          | some other => exact ih.2 other false
        have hstrict := dominates (diagonalProfile false) hsurvives
        rw [euPreference_strict_iff _ _ _ _
          (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)]
          at hstrict
        have hzero (law : PMF sig.Outcome)
            (hlaw : UtilityIntegrable utility (some label) law) :
            expectedUtility utility (some label) law hlaw = 0 :=
          expect_constant law 0 hlaw
        rw [hzero, hzero] at hstrict
        exact (lt_irrefl 0) hstrict

theorem zero_isCorrelatedRationalizable :
    IsCorrelatedRationalizable form (euPreference utility) none
      (0 : Fin 3) :=
  fun round => (zero_and_opponents_survive_correlated round).1

/-- Strict three-player separation: the candidate is rationalizable with
correlated opponent beliefs but not with independent ones. -/
theorem correlated_not_independent_separation :
    IsCorrelatedRationalizable form (euPreference utility) none (0 : Fin 3) ∧
      ¬ IsIndependentRationalizable form (euPreference utility) none
        (0 : Fin 3) :=
  ⟨zero_isCorrelatedRationalizable, zero_not_isIndependentRationalizable⟩

end IndependentSeparation

end GameTheory.Tests.Rationalizability
