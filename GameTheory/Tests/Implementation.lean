/-
# Profile-transfer implementation witnesses

Two players initially prefer `false`. Paying two units for choosing `true`
makes the all-true profile uniquely weakly undominated and implements both a
singleton target and a larger cylinder target. Zero transfer leaves the
all-false profile undominated and therefore fails both targets.
-/

import GameTheory.Mechanism.Implementation

noncomputable section

namespace GameTheory.Tests.Implementation

open GameTheory.Math.Probability

abbrev Player := Fin 2

@[reducible]
def signature : GameSignature Player where
  Strategy _ := Bool
  Outcome := Player → Bool

@[reducible]
def form : GameForm Player where
  sig := signature
  play profile := PMF.pure profile

def utility (outcome : Player → Bool) (who : Player) : ℝ :=
  if outcome who = true then 0 else 1

@[reducible]
def game : UtilityGame Player := ⟨form, utility⟩

def targetProfile : Profile signature := fun _ => true

def target : Set (Profile signature) := {targetProfile}

def transfer : game.ProfileTransfer := fun profile who =>
  if profile who = true then 2 else 0

@[reducible]
def transferred : UtilityGame Player := game.withProfileTransfer transfer

/-- The finite transferred fixture integrates every pure-play utility. -/
theorem transferredGuard (profile : Profile signature) (who : Player) :
    UtilityIntegrable transferred.utility who (transferred.form.play profile) :=
  payoffIntegrable_of_finite _ _

@[simp]
theorem transferred_payoff (profile : Profile signature) (who : Player) :
    expectedUtility transferred.utility who (transferred.form.play profile)
      (transferredGuard profile who) =
      if profile who = true then 2 else 1 := by
  rw [show expectedUtility transferred.utility who (transferred.form.play profile)
      (transferredGuard profile who) =
        expectedUtility transferred.utility who (transferred.form.play profile)
          (game.withProfileTransfer_integrable transfer profile who
            (payoffIntegrable_of_finite _ _)) from rfl,
    game.expectedUtility_withProfileTransfer transfer profile who
      (payoffIntegrable_of_finite _ _)]
  simp [game, form, utility, transfer]
  split <;> simp_all

private theorem transferred_preference_iff (who : Player)
    (preferred alternative : Profile signature) :
    transferred.preference who (transferred.form.play preferred)
      (transferred.form.play alternative) ↔
        (if alternative who then (2 : ℝ) else 1) ≤
          (if preferred who then (2 : ℝ) else 1) := by
  unfold UtilityGame.preference
  rw [euPreference_iff _ who _ _
    (transferredGuard preferred who) (transferredGuard alternative who)]
  rw [transferred_payoff, transferred_payoff]

private theorem transferred_strict_iff (who : Player)
    (preferred alternative : Profile signature) :
    Preference.strict transferred.preference who
      (transferred.form.play preferred) (transferred.form.play alternative) ↔
        (if alternative who then (2 : ℝ) else 1) <
          (if preferred who then (2 : ℝ) else 1) := by
  unfold UtilityGame.preference
  rw [euPreference_strict_iff _ who _ _
    (transferredGuard preferred who) (transferredGuard alternative who)]
  rw [transferred_payoff, transferred_payoff]

theorem true_weaklyDominates_false (who : Player) :
    WeaklyDominates transferred.form transferred.preference who true false := by
  constructor
  · intro profile
    rw [transferred_preference_iff]
    simp
  · refine ⟨targetProfile, ?_⟩
    rw [transferred_strict_iff]
    norm_num [targetProfile]

theorem true_isWeaklyUndominated (who : Player) :
    IsWeaklyUndominated transferred.form transferred.preference who true := by
  intro alternative hdom
  cases alternative with
  | false =>
      have hle := hdom.1 targetProfile
      rw [transferred_preference_iff] at hle
      norm_num [targetProfile] at hle
  | true =>
      obtain ⟨profile, hstrict⟩ := hdom.2
      rw [transferred_strict_iff] at hstrict
      simp at hstrict

theorem false_not_isWeaklyUndominated (who : Player) :
    ¬ IsWeaklyUndominated transferred.form transferred.preference who false := by
  intro hundominated
  exact hundominated true (true_weaklyDominates_false who)

theorem isWeaklyUndominatedProfile_iff (profile : Profile signature) :
    IsWeaklyUndominatedProfile transferred.form transferred.preference profile ↔
      profile = targetProfile := by
  constructor
  · intro hundominated
    funext who
    cases haction : profile who with
    | false =>
        exfalso
        exact false_not_isWeaklyUndominated who (by
          simpa [haction] using hundominated who)
    | true => simp [targetProfile]
  · rintro rfl who
    exact true_isWeaklyUndominated who

theorem transfer_nonneg (profile : Profile signature) (who : Player) :
    0 ≤ transfer profile who := by
  unfold transfer
  split <;> norm_num

theorem transfer_isKUndominatedImplementation :
    game.IsKUndominatedImplementation transfer target 4 := by
  refine ⟨⟨transfer_nonneg, ⟨targetProfile, ?_⟩, ?_⟩, ?_⟩
  · exact (isWeaklyUndominatedProfile_iff targetProfile).2 rfl
  · intro profile hundominated
    rw [target, Set.mem_singleton_iff]
    exact (isWeaklyUndominatedProfile_iff profile).1 hundominated
  · intro profile hundominated
    have hprofile := (isWeaklyUndominatedProfile_iff profile).1 hundominated
    subst profile
    norm_num [transfer, targetProfile, Fin.sum_univ_two]

def firstTrueTarget : Set (Profile signature) :=
  {profile | profile (0 : Player) = true}

theorem target_subset_firstTrueTarget : target ⊆ firstTrueTarget := by
  intro profile hprofile
  rw [target, Set.mem_singleton_iff] at hprofile
  subst profile
  simp [firstTrueTarget, targetProfile]

theorem transfer_isKUndominatedImplementation_firstTrueTarget :
    game.IsKUndominatedImplementation transfer firstTrueTarget 4 :=
  transfer_isKUndominatedImplementation.mono_target target_subset_firstTrueTarget

def zeroTransfer : game.ProfileTransfer := fun _profile _who => 0

@[reducible]
def untransferred : UtilityGame Player := game.withProfileTransfer zeroTransfer

/-- The finite untransferred fixture integrates every pure-play utility. -/
theorem untransferredGuard (profile : Profile signature) (who : Player) :
    UtilityIntegrable untransferred.utility who
      (untransferred.form.play profile) :=
  payoffIntegrable_of_finite _ _

@[simp]
theorem untransferred_payoff (profile : Profile signature) (who : Player) :
    expectedUtility untransferred.utility who (untransferred.form.play profile)
      (untransferredGuard profile who) =
      if profile who = true then 0 else 1 := by
  rw [show expectedUtility untransferred.utility who
      (untransferred.form.play profile) (untransferredGuard profile who) =
        expectedUtility untransferred.utility who
          (untransferred.form.play profile)
          (game.withProfileTransfer_integrable zeroTransfer profile who
            (payoffIntegrable_of_finite _ _)) from rfl,
    game.expectedUtility_withProfileTransfer zeroTransfer profile who
      (payoffIntegrable_of_finite _ _)]
  simp [game, form, utility, zeroTransfer]

private theorem untransferred_preference_iff (who : Player)
    (preferred alternative : Profile signature) :
    untransferred.preference who (untransferred.form.play preferred)
      (untransferred.form.play alternative) ↔
        (if alternative who then (0 : ℝ) else 1) ≤
          (if preferred who then (0 : ℝ) else 1) := by
  unfold UtilityGame.preference
  rw [euPreference_iff _ who _ _
    (untransferredGuard preferred who) (untransferredGuard alternative who)]
  rw [untransferred_payoff, untransferred_payoff]

private theorem untransferred_strict_iff (who : Player)
    (preferred alternative : Profile signature) :
    Preference.strict untransferred.preference who
      (untransferred.form.play preferred) (untransferred.form.play alternative) ↔
        (if alternative who then (0 : ℝ) else 1) <
          (if preferred who then (0 : ℝ) else 1) := by
  unfold UtilityGame.preference
  rw [euPreference_strict_iff _ who _ _
    (untransferredGuard preferred who) (untransferredGuard alternative who)]
  rw [untransferred_payoff, untransferred_payoff]

theorem false_isWeaklyUndominated_without_transfer (who : Player) :
    IsWeaklyUndominated untransferred.form untransferred.preference who false := by
  intro alternative hdom
  cases alternative with
  | false =>
      obtain ⟨profile, hstrict⟩ := hdom.2
      rw [untransferred_strict_iff] at hstrict
      simp at hstrict
  | true =>
      have hle := hdom.1 targetProfile
      rw [untransferred_preference_iff] at hle
      norm_num at hle

def offTargetProfile : Profile signature := fun _ => false

theorem offTargetProfile_isWeaklyUndominated_without_transfer :
    IsWeaklyUndominatedProfile untransferred.form untransferred.preference
      offTargetProfile :=
  fun who => false_isWeaklyUndominated_without_transfer who

theorem zeroTransfer_not_isUndominatedImplementation :
    ¬ game.IsUndominatedImplementation zeroTransfer target := by
  intro himplements
  have htarget := himplements.2.2 offTargetProfile
    offTargetProfile_isWeaklyUndominated_without_transfer
  have heq : offTargetProfile = targetProfile := by
    rw [target, Set.mem_singleton_iff] at htarget
    exact htarget
  have hfalse := congrFun heq (0 : Player)
  simp [offTargetProfile, targetProfile] at hfalse

theorem zeroTransfer_not_isUndominatedImplementation_firstTrueTarget :
    ¬ game.IsUndominatedImplementation zeroTransfer firstTrueTarget := by
  intro himplements
  have htarget := himplements.2.2 offTargetProfile
    offTargetProfile_isWeaklyUndominated_without_transfer
  simp [firstTrueTarget, offTargetProfile] at htarget

end GameTheory.Tests.Implementation
