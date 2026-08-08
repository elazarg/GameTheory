/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Public.PhaseCertificate

/-!
# Public-history suffixes

A certificate attached to a recurrent child is naturally stated from the
child's entry state at local time zero.  To use it after a finite public
history, the local suffix history must be embedded into the full public
history, and every strategy and history potential must be rebased along that
embedding.

This file supplies that exact bookkeeping.  It does not claim that an
unconditional history law from the root is invariant under rebasing.  Instead
`histDistAfter` is the conditional continuation law starting from a specified
completed public history.

The final transfer lemmas make the remaining splice interface explicit:
local public-phase inequalities transfer to a full-history profile only when
the rebased full profile and potentials agree with the child's local data.
This agreement is strategic data; it does not follow from a child certificate
alone.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability

variable {ι : Type} {G : StochasticGame ι}

/-- Append a local continuation history to a completed public base.

The current state of the result is the current state of the suffix.  A
strategically meaningful suffix starts from `base.2`; that compatibility is
imposed by the continuation laws below rather than by the history type. -/
def appendHist {prefixLength suffixLength : ℕ}
    (base : G.Hist prefixLength) (suffix : G.Hist suffixLength) :
    G.Hist (prefixLength + suffixLength) :=
  (Fin.append base.1 suffix.1, suffix.2)

@[simp] theorem appendHist_snd {prefixLength suffixLength : ℕ}
    (base : G.Hist prefixLength) (suffix : G.Hist suffixLength) :
    (G.appendHist base suffix).2 = suffix.2 :=
  rfl

/-- Appending the empty continuation at the base's current state recovers
the base. -/
@[simp] theorem appendHist_empty {prefixLength : ℕ}
    (base : G.Hist prefixLength) :
    G.appendHist base (G.emptyHist base.2) = base := by
  apply Prod.ext
  · funext index
    exact Fin.append_left base.1 Fin.elim0 index
  · rfl

/-- Appending a one-step extension of a suffix is the one-step extension of
the appended full history. -/
theorem appendHist_snoc {prefixLength suffixLength : ℕ}
    (base : G.Hist prefixLength) (suffix : G.Hist suffixLength)
    (action : G.JointAct) (next : G.State) :
    G.appendHist base
        ((Fin.snoc suffix.1 (suffix.2, action), next) :
          G.Hist (suffixLength + 1)) =
      (Fin.snoc (G.appendHist base suffix).1
          ((G.appendHist base suffix).2, action), next) := by
  apply Prod.ext
  · exact Fin.append_snoc base.1 suffix.1 (suffix.2, action)
  · rfl

/-- Rebase a full-history behavior profile after a completed public base. -/
def afterHistoryProfile (G : StochasticGame ι)
    (profile : G.BehaviorProfile) {prefixLength : ℕ}
    (base : G.Hist prefixLength) : G.BehaviorProfile :=
  fun who suffixLength suffix =>
    profile who (prefixLength + suffixLength)
      (G.appendHist base suffix)

/-- Rebase one player's full-history behavior strategy after a completed
public base. -/
def afterHistoryStrategy (G : StochasticGame ι) {who : ι}
    (strategy : G.BehaviorStrategy who) {prefixLength : ℕ}
    (base : G.Hist prefixLength) : G.BehaviorStrategy who :=
  fun suffixLength suffix =>
    strategy (prefixLength + suffixLength)
      (G.appendHist base suffix)

@[simp] theorem afterHistoryProfile_apply
    (profile : G.BehaviorProfile) {prefixLength suffixLength : ℕ}
    (base : G.Hist prefixLength) (who : ι)
    (suffix : G.Hist suffixLength) :
    G.afterHistoryProfile profile base who suffixLength suffix =
      profile who (prefixLength + suffixLength)
        (G.appendHist base suffix) :=
  rfl

@[simp] theorem afterHistoryStrategy_apply {who : ι}
    (strategy : G.BehaviorStrategy who) {prefixLength suffixLength : ℕ}
    (base : G.Hist prefixLength) (suffix : G.Hist suffixLength) :
    G.afterHistoryStrategy strategy base suffixLength suffix =
      strategy (prefixLength + suffixLength)
        (G.appendHist base suffix) :=
  rfl

/-- Rebasing commutes with replacing one player's behavior strategy. -/
theorem afterHistoryProfile_update [DecidableEq ι]
    (profile : G.BehaviorProfile) (who : ι)
    (strategy : G.BehaviorStrategy who) {prefixLength : ℕ}
    (base : G.Hist prefixLength) :
    G.afterHistoryProfile (Function.update profile who strategy) base =
      Function.update (G.afterHistoryProfile profile base) who
        (G.afterHistoryStrategy strategy base) := by
  funext player suffixLength suffix
  by_cases hplayer : player = who
  · subst hplayer
    simp
  · simp [Function.update_of_ne hplayer]

@[simp] theorem stageActionDist_afterHistoryProfile [Fintype ι]
    (profile : G.BehaviorProfile) {prefixLength suffixLength : ℕ}
    (base : G.Hist prefixLength) (suffix : G.Hist suffixLength) :
    G.stageActionDist (G.afterHistoryProfile profile base) suffix =
      G.stageActionDist profile (G.appendHist base suffix) :=
  rfl

/-- Rebase a full-history potential after a completed public base. -/
def afterHistoryPotential (G : StochasticGame ι)
    (potential : G.HistoryPotential) {prefixLength : ℕ}
    (base : G.Hist prefixLength) : G.HistoryPotential :=
  fun suffixLength suffix =>
    potential (prefixLength + suffixLength)
      (G.appendHist base suffix)

@[simp] theorem afterHistoryPotential_apply
    (potential : G.HistoryPotential) {prefixLength suffixLength : ℕ}
    (base : G.Hist prefixLength) (suffix : G.Hist suffixLength) :
    G.afterHistoryPotential potential base suffixLength suffix =
      potential (prefixLength + suffixLength)
        (G.appendHist base suffix) :=
  rfl

/-- Stage payoff expectations are unchanged by exact history rebasing. -/
theorem stageEUAt_afterHistoryProfile [Fintype ι]
    (profile : G.BehaviorProfile) {prefixLength suffixLength : ℕ}
    (base : G.Hist prefixLength) (suffix : G.Hist suffixLength)
    (who : ι) :
    G.stageEUAt (G.afterHistoryProfile profile base) suffix who =
      G.stageEUAt profile (G.appendHist base suffix) who :=
  rfl

/-- One-step continuation expectations are unchanged by exact rebasing of
both the profile and the history potential. -/
theorem historyContinuationEU_afterHistory [Fintype ι]
    (profile : G.BehaviorProfile) (potential : G.HistoryPotential)
    {prefixLength suffixLength : ℕ} (base : G.Hist prefixLength)
    (suffix : G.Hist suffixLength) :
    G.historyContinuationEU (G.afterHistoryProfile profile base)
        (G.afterHistoryPotential potential base) suffix =
      G.historyContinuationEU profile potential
        (G.appendHist base suffix) := by
  unfold historyContinuationEU
  apply congrArg (expect (G.stageActionDist profile
    (G.appendHist base suffix)))
  funext action
  apply congrArg (expect (G.transition suffix.2 action))
  funext next
  rw [afterHistoryPotential_apply, appendHist_snoc]
  rfl

/-- The conditional full-history law after a completed public base.

This is deliberately not identified with an unconditional root history law.
It is obtained by running the rebased profile from the base's current state
and then restoring the completed base. -/
def histDistAfter (G : StochasticGame ι) [Fintype ι]
    (profile : G.BehaviorProfile) {prefixLength : ℕ}
    (base : G.Hist prefixLength) (suffixLength : ℕ) :
    PMF (G.Hist (prefixLength + suffixLength)) :=
  (G.histDist (G.afterHistoryProfile profile base) base.2
    suffixLength).map (G.appendHist base)

@[simp] theorem histDistAfter_zero [Fintype ι]
    (profile : G.BehaviorProfile) {prefixLength : ℕ}
    (base : G.Hist prefixLength) :
    G.histDistAfter profile base 0 = PMF.pure base := by
  unfold histDistAfter
  rw [G.histDist_zero, PMF.pure_map, appendHist_empty]

/-- The conditional full-history law obeys the same one-step recursion as the
ordinary history law, but starts from the supplied completed base. -/
theorem histDistAfter_succ [Fintype ι]
    (profile : G.BehaviorProfile) {prefixLength : ℕ}
    (base : G.Hist prefixLength) (suffixLength : ℕ) :
    G.histDistAfter profile base (suffixLength + 1) =
      (G.histDistAfter profile base suffixLength).bind fun history =>
        (G.stageActionDist profile history).bind fun action =>
          (G.transition history.2 action).bind fun next =>
            PMF.pure
              ((Fin.snoc history.1 (history.2, action), next) :
                G.Hist (prefixLength + (suffixLength + 1))) := by
  unfold histDistAfter
  rw [G.histDist_succ, PMF.map_bind, PMF.bind_map]
  apply congrArg
  funext suffix
  simp only [Function.comp_apply,
    stageActionDist_afterHistoryProfile, PMF.map_bind]
  apply congrArg
  funext action
  apply congrArg
  funext next
  simp only [PMF.pure_map, appendHist_snoc]

/-- Expected values under a rebased local law are exactly expectations under
the corresponding conditional full-history law. -/
theorem expectedHistoryValue_afterHistory [Fintype ι]
    (profile : G.BehaviorProfile) (potential : G.HistoryPotential)
    {prefixLength : ℕ} (base : G.Hist prefixLength)
    (suffixLength : ℕ) :
    G.expectedHistoryValue (G.afterHistoryProfile profile base)
        base.2 (G.afterHistoryPotential potential base) suffixLength =
      expect (G.histDistAfter profile base suffixLength)
        (potential (prefixLength + suffixLength)) := by
  unfold expectedHistoryValue histDistAfter
  rw [expect_map]
  rfl

/-- Rebase a public-phase profile that is already defined on full histories.

This operation restricts existing full-history play to the suffix after a
base.  It is not the reverse operation of extending a child profile to all
off-branch histories. -/
def PublicPhaseProfile.afterHistory
    (profile : PublicPhaseProfile G) {prefixLength : ℕ}
    (base : G.Hist prefixLength) : PublicPhaseProfile G where
  Phase := profile.Phase
  phase := fun suffixLength suffix =>
    profile.phase (prefixLength + suffixLength)
      (G.appendHist base suffix)
  play := profile.play

@[simp] theorem PublicPhaseProfile.afterHistory_phase
    (profile : PublicPhaseProfile G) {prefixLength suffixLength : ℕ}
    (base : G.Hist prefixLength) (suffix : G.Hist suffixLength) :
    (profile.afterHistory base).phase suffixLength suffix =
      profile.phase (prefixLength + suffixLength)
        (G.appendHist base suffix) :=
  rfl

@[simp] theorem PublicPhaseProfile.behaviorProfile_afterHistory
    (profile : PublicPhaseProfile G) {prefixLength : ℕ}
    (base : G.Hist prefixLength) :
    (profile.afterHistory base).behaviorProfile =
      G.afterHistoryProfile profile.behaviorProfile base :=
  rfl

@[simp] theorem PublicPhaseProfile.historyPotential_afterHistory
    (profile : PublicPhaseProfile G) (value : profile.Phase → ℝ)
    {prefixLength : ℕ} (base : G.Hist prefixLength) :
    (profile.afterHistory base).historyPotential value =
      G.afterHistoryPotential (profile.historyPotential value) base :=
  rfl

/-! ## Explicit strategic interface for a child-certificate suffix -/

/-- Data asserting that one total full-history profile and its accounts
restrict, after a completed public history, to a child's local public-phase
certificate.

The total full-history objects remain explicit because a child certificate
does not prescribe behavior or potentials on histories outside its branch.
The deviation-charge equality also rebases the actual full-history
deviation; this is the interface needed for conditional charge accounting. -/
structure PublicPhaseSuffixInterface
    [Fintype ι] [DecidableEq ι] [Finite G.State]
    [∀ who, Finite (G.Act who)]
    (childProfile : PublicPhaseProfile G) (childState : G.State)
    (target : Payoff ι) (error : ℝ)
    (certificate :
      PublicPhasePunishmentSystemAt G childProfile childState target error)
    {prefixLength : ℕ} (base : G.Hist prefixLength) where
  profile : G.BehaviorProfile
  lowerPotential : ι → G.HistoryPotential
  upperPotential : ι → G.HistoryPotential
  deviationPotential : ι → G.HistoryPotential
  lowerCharge : ι → G.HistoryPotential
  upperCharge : ι → G.HistoryPotential
  deviationCharge :
    ∀ who, G.BehaviorStrategy who → G.HistoryPotential
  base_state : base.2 = childState
  profile_after :
    G.afterHistoryProfile profile base =
      childProfile.behaviorProfile
  lowerPotential_after : ∀ who,
    G.afterHistoryPotential (lowerPotential who) base =
      childProfile.historyPotential (certificate.lowerPotential who)
  upperPotential_after : ∀ who,
    G.afterHistoryPotential (upperPotential who) base =
      childProfile.historyPotential (certificate.upperPotential who)
  deviationPotential_after : ∀ who,
    G.afterHistoryPotential (deviationPotential who) base =
      childProfile.historyPotential (certificate.deviationPotential who)
  lowerCharge_after : ∀ who,
    G.afterHistoryPotential (lowerCharge who) base =
      certificate.lowerCharge who
  upperCharge_after : ∀ who,
    G.afterHistoryPotential (upperCharge who) base =
      certificate.upperCharge who
  deviationCharge_after : ∀ who (deviation : G.BehaviorStrategy who),
    G.afterHistoryPotential (deviationCharge who deviation) base =
      certificate.deviationCharge who
        (G.afterHistoryStrategy deviation base)

namespace PublicPhaseSuffixInterface

variable [Fintype ι] [DecidableEq ι] [Finite G.State]
  [∀ who, Finite (G.Act who)]
  {childProfile : PublicPhaseProfile G} {childState : G.State}
  {target : Payoff ι} {error : ℝ}
  {certificate :
    PublicPhasePunishmentSystemAt G childProfile childState target error}
  {prefixLength : ℕ} {base : G.Hist prefixLength}

/-- The child's lower initial value is the full-history value at the completed
base. -/
theorem lower_initial
    (interface :
      PublicPhaseSuffixInterface childProfile childState target error
        certificate base)
    (who : ι) :
    |interface.lowerPotential who prefixLength base - target who| ≤
      error := by
  have hlocal := certificate.lower_initial who
  change
    |childProfile.historyPotential (certificate.lowerPotential who)
        0 (G.emptyHist childState) - target who| ≤ error at hlocal
  rw [← interface.lowerPotential_after who] at hlocal
  have hempty :
      G.appendHist base (G.emptyHist childState) = base := by
    rw [← interface.base_state]
    exact G.appendHist_empty base
  simpa only [afterHistoryPotential_apply, Nat.add_zero,
    hempty] using hlocal

/-- The child's upper initial value is the full-history value at the completed
base. -/
theorem upper_initial
    (interface :
      PublicPhaseSuffixInterface childProfile childState target error
        certificate base)
    (who : ι) :
    |interface.upperPotential who prefixLength base - target who| ≤
      error := by
  have hlocal := certificate.upper_initial who
  change
    |childProfile.historyPotential (certificate.upperPotential who)
        0 (G.emptyHist childState) - target who| ≤ error at hlocal
  rw [← interface.upperPotential_after who] at hlocal
  have hempty :
      G.appendHist base (G.emptyHist childState) = base := by
    rw [← interface.base_state]
    exact G.appendHist_empty base
  simpa only [afterHistoryPotential_apply, Nat.add_zero,
    hempty] using hlocal

/-- The child's deviation initial value is the full-history value at the
completed base. -/
theorem deviation_initial
    (interface :
      PublicPhaseSuffixInterface childProfile childState target error
        certificate base)
    (who : ι) :
    |interface.deviationPotential who prefixLength base - target who| ≤
      error := by
  have hlocal := certificate.deviation_initial who
  change
    |childProfile.historyPotential (certificate.deviationPotential who)
        0 (G.emptyHist childState) - target who| ≤ error at hlocal
  rw [← interface.deviationPotential_after who] at hlocal
  have hempty :
      G.appendHist base (G.emptyHist childState) = base := by
    rw [← interface.base_state]
    exact G.appendHist_empty base
  simpa only [afterHistoryPotential_apply, Nat.add_zero,
    hempty] using hlocal

/-- A child's lower continuation inequality holds on every full history
extending the base when the suffix interface is satisfied. -/
theorem lower_subharmonic
    (interface :
      PublicPhaseSuffixInterface childProfile childState target error
        certificate base)
    (who : ι) (suffixLength : ℕ)
    (suffix : G.Hist suffixLength) :
    interface.lowerPotential who
        (prefixLength + suffixLength) (G.appendHist base suffix) ≤
      G.historyContinuationEU interface.profile
        (interface.lowerPotential who) (G.appendHist base suffix) := by
  have hlocal := certificate.lower_subharmonic who suffixLength suffix
  rw [← interface.profile_after,
    ← interface.lowerPotential_after who] at hlocal
  simpa only [afterHistoryPotential_apply,
    historyContinuationEU_afterHistory] using hlocal

/-- A child's lower stage inequality holds on every full history extending
the base. -/
theorem lower_stage
    (interface :
      PublicPhaseSuffixInterface childProfile childState target error
        certificate base)
    (who : ι) (suffixLength : ℕ)
    (suffix : G.Hist suffixLength) :
    interface.lowerPotential who
        (prefixLength + suffixLength) (G.appendHist base suffix) ≤
      G.stageEUAt interface.profile (G.appendHist base suffix) who +
        interface.lowerCharge who
          (prefixLength + suffixLength) (G.appendHist base suffix) := by
  have hlocal := certificate.lower_stage who suffixLength suffix
  rw [← interface.profile_after,
    ← interface.lowerPotential_after who,
    ← interface.lowerCharge_after who] at hlocal
  simpa only [afterHistoryPotential_apply,
    stageEUAt_afterHistoryProfile] using hlocal

/-- A child's upper continuation inequality holds on every full history
extending the base. -/
theorem upper_superharmonic
    (interface :
      PublicPhaseSuffixInterface childProfile childState target error
        certificate base)
    (who : ι) (suffixLength : ℕ)
    (suffix : G.Hist suffixLength) :
    G.historyContinuationEU interface.profile
        (interface.upperPotential who) (G.appendHist base suffix) ≤
      interface.upperPotential who
        (prefixLength + suffixLength) (G.appendHist base suffix) := by
  have hlocal :=
    certificate.upper_superharmonic who suffixLength suffix
  rw [← interface.profile_after,
    ← interface.upperPotential_after who] at hlocal
  simpa only [afterHistoryPotential_apply,
    historyContinuationEU_afterHistory] using hlocal

/-- A child's upper stage inequality holds on every full history extending
the base. -/
theorem upper_stage
    (interface :
      PublicPhaseSuffixInterface childProfile childState target error
        certificate base)
    (who : ι) (suffixLength : ℕ)
    (suffix : G.Hist suffixLength) :
    G.stageEUAt interface.profile (G.appendHist base suffix) who ≤
      interface.upperPotential who
          (prefixLength + suffixLength) (G.appendHist base suffix) +
        interface.upperCharge who
          (prefixLength + suffixLength) (G.appendHist base suffix) := by
  have hlocal := certificate.upper_stage who suffixLength suffix
  rw [← interface.profile_after,
    ← interface.upperPotential_after who,
    ← interface.upperCharge_after who] at hlocal
  simpa only [afterHistoryPotential_apply,
    stageEUAt_afterHistoryProfile] using hlocal

/-- A child's deviation continuation inequality transfers for an arbitrary
full-history unilateral deviation. -/
theorem deviation_superharmonic
    (interface :
      PublicPhaseSuffixInterface childProfile childState target error
        certificate base)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (suffixLength : ℕ) (suffix : G.Hist suffixLength) :
    G.historyContinuationEU
        (Function.update interface.profile who deviation)
        (interface.deviationPotential who)
        (G.appendHist base suffix) ≤
      interface.deviationPotential who
        (prefixLength + suffixLength) (G.appendHist base suffix) := by
  have hlocal := certificate.deviation_superharmonic who
    (G.afterHistoryStrategy deviation base) suffixLength suffix
  rw [← interface.profile_after,
    ← interface.deviationPotential_after who] at hlocal
  rw [← G.afterHistoryProfile_update] at hlocal
  simpa only [afterHistoryPotential_apply,
    historyContinuationEU_afterHistory] using hlocal

/-- A child's deviation stage inequality transfers for an arbitrary
full-history unilateral deviation. -/
theorem deviation_stage
    (interface :
      PublicPhaseSuffixInterface childProfile childState target error
        certificate base)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (suffixLength : ℕ) (suffix : G.Hist suffixLength) :
    G.stageEUAt
        (Function.update interface.profile who deviation)
        (G.appendHist base suffix) who ≤
      interface.deviationPotential who
          (prefixLength + suffixLength) (G.appendHist base suffix) +
        interface.deviationCharge who deviation
          (prefixLength + suffixLength) (G.appendHist base suffix) := by
  have hlocal := certificate.deviation_stage who
    (G.afterHistoryStrategy deviation base) suffixLength suffix
  rw [← interface.profile_after,
    ← interface.deviationPotential_after who,
    ← interface.deviationCharge_after who deviation] at hlocal
  rw [← G.afterHistoryProfile_update] at hlocal
  simpa only [afterHistoryPotential_apply,
    stageEUAt_afterHistoryProfile] using hlocal

/-- The child's lower charge bound becomes a conditional suffix charge bound
under the full-history profile. -/
theorem lower_charge_cesaro
    (interface :
      PublicPhaseSuffixInterface childProfile childState target error
        certificate base)
    (who : ι) (horizon : ℕ)
    (hhorizon : certificate.horizon ≤ horizon) :
    (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        G.expectedHistoryValue
          (G.afterHistoryProfile interface.profile base) base.2
          (G.afterHistoryPotential (interface.lowerCharge who) base)
          time ≤
      error := by
  rw [interface.profile_after, interface.base_state,
    interface.lowerCharge_after who]
  exact certificate.lower_charge_cesaro who horizon hhorizon

/-- The child's upper charge bound becomes a conditional suffix charge bound
under the full-history profile. -/
theorem upper_charge_cesaro
    (interface :
      PublicPhaseSuffixInterface childProfile childState target error
        certificate base)
    (who : ι) (horizon : ℕ)
    (hhorizon : certificate.horizon ≤ horizon) :
    (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        G.expectedHistoryValue
          (G.afterHistoryProfile interface.profile base) base.2
          (G.afterHistoryPotential (interface.upperCharge who) base)
          time ≤
      error := by
  rw [interface.profile_after, interface.base_state,
    interface.upperCharge_after who]
  exact certificate.upper_charge_cesaro who horizon hhorizon

/-- The child's deviation charge bound becomes a conditional suffix bound
for every full-history unilateral deviation. -/
theorem deviation_charge_cesaro
    (interface :
      PublicPhaseSuffixInterface childProfile childState target error
        certificate base)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (horizon : ℕ) (hhorizon : certificate.horizon ≤ horizon) :
    (horizon : ℝ)⁻¹ * ∑ time ∈ Finset.range horizon,
        G.expectedHistoryValue
          (G.afterHistoryProfile
            (Function.update interface.profile who deviation) base)
          base.2
          (G.afterHistoryPotential
            (interface.deviationCharge who deviation) base)
          time ≤
      error := by
  rw [G.afterHistoryProfile_update, interface.profile_after,
    interface.base_state,
    interface.deviationCharge_after who deviation]
  exact certificate.deviation_charge_cesaro who
    (G.afterHistoryStrategy deviation base) horizon hhorizon

end PublicPhaseSuffixInterface

end StochasticGame
end GameTheory
