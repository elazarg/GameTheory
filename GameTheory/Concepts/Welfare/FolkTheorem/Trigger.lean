/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SumOverResidueClass
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Math.SimplexApproximation
import GameTheory.Concepts.Mixed.MixedExtension
import GameTheory.Concepts.ZeroSum.SecurityStrategy
import GameTheory.Concepts.Welfare.FolkTheorem.Periodic

noncomputable section

open scoped BigOperators

namespace GameTheory

namespace KernelGame

variable {ι : Type}

/-- If two profiles differ, at least one player's coordinate differs. -/
theorem exists_profile_ne_coord (G : KernelGame ι) {σ τ : Profile G}
    (h : σ ≠ τ) :
    ∃ i, σ i ≠ τ i := by
  classical
  by_contra hnone
  apply h
  funext i
  exact not_not.mp (by
    intro hne
    exact hnone ⟨i, hne⟩)

/-- A chosen coordinate at which two profiles differ.  This is the deviator
selected when the trigger strategy first observes an off-path profile. -/
def profileMismatchPlayer (G : KernelGame ι) {σ τ : Profile G}
    (h : σ ≠ τ) : ι :=
  Classical.choose (G.exists_profile_ne_coord h)

theorem profileMismatchPlayer_spec (G : KernelGame ι) {σ τ : Profile G}
    (h : σ ≠ τ) :
    σ (G.profileMismatchPlayer h) ≠ τ (G.profileMismatchPlayer h) :=
  Classical.choose_spec (G.exists_profile_ne_coord h)

/-- If two profiles differ only possibly at `who`, the chosen mismatch player
is `who`. -/
theorem profileMismatchPlayer_eq_of_forall_ne_eq
    (G : KernelGame ι) {σ τ : Profile G}
    (who : ι) (h : σ ≠ τ)
    (hothers : ∀ j, j ≠ who → σ j = τ j) :
    G.profileMismatchPlayer h = who := by
  classical
  by_contra hne
  exact G.profileMismatchPlayer_spec h (hothers _ hne)

/-- Drop the last observation from a profile history. -/
def historyInit (G : KernelGame ι) {t : ℕ}
    (hist : G.ProfileHistory (t + 1)) : G.ProfileHistory t :=
  fun k => hist ⟨k.1, Nat.lt_trans k.2 (Nat.lt_succ_self t)⟩

@[simp] theorem historyInit_apply (G : KernelGame ι) {t : ℕ}
    (hist : G.ProfileHistory (t + 1)) (k : Fin t) :
    G.historyInit hist k =
      hist ⟨k.1, Nat.lt_trans k.2 (Nat.lt_succ_self t)⟩ :=
  rfl

/-- Trigger-strategy automaton state computed from a profile history.

`none` means no off-path profile has been observed.  `some who` means the
first off-path profile was attributed to `who`, and punishments should continue
against `who`. -/
def triggerStatus (G : KernelGame ι) (path : ℕ → Profile G) :
    (t : ℕ) → G.ProfileHistory t → Option ι
  | 0, _ => none
  | t + 1, hist => by
      classical
      exact
        match G.triggerStatus path t (G.historyInit hist) with
        | some who => some who
        | none =>
            if h : hist ⟨t, Nat.lt_succ_self t⟩ = path t then none
            else some (G.profileMismatchPlayer h)

/-- The one-period profile prescribed by the trigger automaton.

In punishment state, all players other than the identified deviator play the
chosen punishment opponent profile.  The identified deviator's own coordinate is
filled by an arbitrary action, because unilateral-deviation comparisons replace
that coordinate by the deviator's strategy.  This is enough for the Nash trigger
argument below; it is not meant to encode a sequentially credible punishment
assessment for every off-path subgame. -/
def triggerProfileAt (G : KernelGame ι) [DecidableEq ι]
    [∀ i, Nonempty (G.Strategy i)] (path : ℕ → Profile G)
    (punish : ∀ who, G.OpponentProfile who) (t : ℕ)
    (status : Option ι) : Profile G :=
  fun i =>
    match status with
    | none => path t i
    | some who =>
        if h : i = who then Classical.arbitrary (G.Strategy i)
        else punish who ⟨i, h⟩

/-- The trigger repeated profile: follow `path` until the first observed
mismatch, then punish the selected deviator forever. -/
def triggerRepeatedProfile (G : KernelGame ι) [DecidableEq ι]
    [∀ i, Nonempty (G.Strategy i)] (path : ℕ → Profile G)
    (punish : ∀ who, G.OpponentProfile who) :
    G.RepeatedProfile :=
  fun i t hist => G.triggerProfileAt path punish t (G.triggerStatus path t hist) i

theorem triggerStatus_eq_none_of_history_eq_path
    (G : KernelGame ι) (path : ℕ → Profile G) :
    ∀ {t : ℕ} (hist : G.ProfileHistory t),
      (∀ k : Fin t, hist k = path k) → G.triggerStatus path t hist = none
  | 0, _hist, _hhist => by
      simp [triggerStatus]
  | t + 1, hist, hhist => by
      have hprev : G.triggerStatus path t (G.historyInit hist) = none := by
        apply G.triggerStatus_eq_none_of_history_eq_path path
        intro k
        exact hhist ⟨k.1, Nat.lt_trans k.2 (Nat.lt_succ_self t)⟩
      have hlast : hist ⟨t, Nat.lt_succ_self t⟩ = path t :=
        hhist ⟨t, Nat.lt_succ_self t⟩
      simp [triggerStatus, hprev, hlast]

/-- The trigger profile generates the intended path when nobody deviates. -/
theorem repeatedPlay_triggerRepeatedProfile_eq_path
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who) :
    ∀ t : ℕ,
      G.repeatedPlay
          (G.triggerRepeatedProfile path punish) t = path t := by
  intro t
  induction t using Nat.strong_induction_on with
  | h t ih =>
      funext i
      rw [repeatedPlay]
      have hstatus :
          G.triggerStatus path t
              (fun k =>
                G.repeatedPlay
                  (G.triggerRepeatedProfile path punish) k) = none := by
        apply G.triggerStatus_eq_none_of_history_eq_path
        intro k
        exact ih k k.2
      simp [triggerRepeatedProfile, triggerProfileAt, hstatus]

/-- The trigger profile's discounted payoff is the discounted payoff of its
intended path, since no deviation occurs on its own generated play. -/
theorem discountedAveragePayoff_triggerRepeatedProfile_eq_path
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (δ : ℝ) (who : ι) :
    G.discountedAveragePayoff δ (G.triggerRepeatedProfile path punish) who =
      (1 - δ) * ∑' t : ℕ, δ ^ t * G.eu (path t) who := by
  simp [discountedAveragePayoff,
    G.repeatedPlay_triggerRepeatedProfile_eq_path path punish]

/-- For a periodic intended path, the trigger profile has the same discounted
payoff as the stationary periodic profile. -/
theorem discountedAveragePayoff_triggerPeriodicRepeatedProfile_eq
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    {n : ℕ} [NeZero n] (cycle : Fin n → Profile G)
    (punish : ∀ who, G.OpponentProfile who) (δ : ℝ) (who : ι) :
    G.discountedAveragePayoff δ
        (G.triggerRepeatedProfile (fun t => cycle (Fin.ofNat n t)) punish) who =
      G.discountedAveragePayoff δ (G.periodicRepeatedProfile cycle) who := by
  calc
    G.discountedAveragePayoff δ
        (G.triggerRepeatedProfile (fun t => cycle (Fin.ofNat n t)) punish) who =
        (1 - δ) * ∑' t : ℕ, δ ^ t * G.eu (cycle (Fin.ofNat n t)) who := by
      rw [G.discountedAveragePayoff_triggerRepeatedProfile_eq_path]
    _ = G.discountedAveragePayoff δ (G.periodicRepeatedProfile cycle) who := by
      simp [discountedAveragePayoff]

/-- Before the trigger has fired, a unilateral deviation by `who` leaves every
other player's realized action on the intended path. -/
theorem repeatedPlay_update_triggerRepeatedProfile_ne_of_status_none
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.RepeatedStrategy who) {t : ℕ}
    (hstatus :
      G.triggerStatus path t
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) = none)
    {j : ι} (hj : j ≠ who) :
    G.repeatedPlay
        (Function.update (G.triggerRepeatedProfile path punish) who dev) t j =
      path t j := by
  rw [repeatedPlay]
  simp [triggerRepeatedProfile, triggerProfileAt, Function.update, hj, hstatus]

/-- If the trigger is still off both before and after period `t`, then the
realized period-`t` profile is exactly the intended path profile. -/
theorem repeatedPlay_update_trigger_eq_path_of_status_none_succ
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.RepeatedStrategy who) {t : ℕ}
    (hstatus :
      G.triggerStatus path t
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          none)
    (hstatus_succ :
      G.triggerStatus path (t + 1)
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          none) :
    G.repeatedPlay
        (Function.update (G.triggerRepeatedProfile path punish) who dev) t =
      path t := by
  let σdev : G.RepeatedProfile :=
    Function.update (G.triggerRepeatedProfile path punish) who dev
  let ρ : Profile G := G.repeatedPlay σdev t
  by_contra hne
  have hs_ne : ρ ≠ path t := by
    intro heq
    exact hne (by
      subst ρ
      exact heq)
  let hist : G.ProfileHistory (t + 1) := fun k => G.repeatedPlay σdev k
  have hinit : G.historyInit hist =
      (fun k : Fin t => G.repeatedPlay σdev k) := by
    funext k
    rfl
  have hstatus' :
      G.triggerStatus path t (fun k : Fin t => G.repeatedPlay σdev k) =
        none := by
    simpa [σdev] using hstatus
  have hsucc_some :
      G.triggerStatus path (t + 1) hist = some (G.profileMismatchPlayer hs_ne) := by
    simp [triggerStatus, hinit, hstatus', hist, ρ, hs_ne]
  have hsucc_none' : G.triggerStatus path (t + 1) hist = none := by
    simpa [hist, σdev] using hstatus_succ
  rw [hsucc_some] at hsucc_none'
  simp at hsucc_none'

/-- If a unilateral deviation never fires the trigger, its realized play is the
intended path at every period. -/
theorem repeatedPlay_update_trigger_eq_path_of_forall_status_none
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.RepeatedStrategy who)
    (hstatus : ∀ t : ℕ,
      G.triggerStatus path t
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          none) :
    ∀ t : ℕ,
      G.repeatedPlay
          (Function.update (G.triggerRepeatedProfile path punish) who dev) t =
        path t := by
  intro t
  exact G.repeatedPlay_update_trigger_eq_path_of_status_none_succ
    path punish who dev (hstatus t) (hstatus (t + 1))

/-- If a unilateral deviation never fires the trigger, its discounted payoff is
the same as the trigger profile's on-path payoff. -/
theorem discountedAveragePayoff_update_trigger_eq_of_forall_status_none
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.RepeatedStrategy who) (δ : ℝ)
    (hstatus : ∀ t : ℕ,
      G.triggerStatus path t
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          none) :
    G.discountedAveragePayoff δ
        (Function.update (G.triggerRepeatedProfile path punish) who dev) who =
      G.discountedAveragePayoff δ (G.triggerRepeatedProfile path punish) who := by
  rw [discountedAveragePayoff, discountedAveragePayoff]
  congr 1
  apply tsum_congr
  intro t
  rw [G.repeatedPlay_update_trigger_eq_path_of_forall_status_none
    path punish who dev hstatus t]
  rw [G.repeatedPlay_triggerRepeatedProfile_eq_path path punish t]

/-- Along a unilateral deviation by `who`, the trigger status is either still
on-path or has identified `who` as the deviator. -/
theorem triggerStatus_update_triggerRepeatedProfile_eq_none_or_self
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.RepeatedStrategy who) :
    ∀ t : ℕ,
      G.triggerStatus path t
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) = none ∨
      G.triggerStatus path t
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          some who := by
  intro t
  induction t with
  | zero =>
      left
      simp [triggerStatus]
  | succ t ih =>
      let σdev : G.RepeatedProfile :=
        Function.update (G.triggerRepeatedProfile path punish) who dev
      let hist : G.ProfileHistory (t + 1) := fun k => G.repeatedPlay σdev k
      have hinit : G.historyInit hist =
          (fun k : Fin t => G.repeatedPlay σdev k) := by
        funext k
        rfl
      change G.triggerStatus path (t + 1) hist = none ∨
        G.triggerStatus path (t + 1) hist = some who
      rcases ih with hprev | hprev
      · have hprev' :
            G.triggerStatus path t
              (fun k : Fin t => G.repeatedPlay σdev k) = none := by
          simpa [σdev] using hprev
        by_cases hlast : hist ⟨t, Nat.lt_succ_self t⟩ = path t
        · left
          simp [triggerStatus, hinit, hprev', hlast]
        · right
          have hplayer : G.profileMismatchPlayer hlast = who := by
            apply G.profileMismatchPlayer_eq_of_forall_ne_eq who
            intro j hj
            change G.repeatedPlay σdev t j = path t j
            subst σdev
            exact G.repeatedPlay_update_triggerRepeatedProfile_ne_of_status_none
              path punish who dev hprev hj
          simp [triggerStatus, hinit, hprev', hlast, hplayer]
      · have hprev' :
            G.triggerStatus path t
              (fun k : Fin t => G.repeatedPlay σdev k) = some who := by
          simpa [σdev] using hprev
        right
        simp [triggerStatus, hinit, hprev']

/-- Every unilateral deviation either never fires the trigger, or has a least
period at which the trigger status is `some who`. -/
theorem triggerStatus_update_trigger_first_fire_or_never
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.RepeatedStrategy who) :
    (∀ t : ℕ,
      G.triggerStatus path t
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          none) ∨
    ∃ s : ℕ,
      G.triggerStatus path s
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          some who ∧
      ∀ t < s,
        G.triggerStatus path t
          (fun k =>
            G.repeatedPlay
              (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
            none := by
  classical
  let status : ℕ → Option ι := fun t =>
    G.triggerStatus path t
      (fun k =>
        G.repeatedPlay
          (Function.update (G.triggerRepeatedProfile path punish) who dev) k)
  by_cases hnever : ∀ t, status t = none
  · left
    exact hnever
  · right
    have hex : ∃ t, status t = some who := by
      push Not at hnever
      rcases hnever with ⟨t, ht⟩
      rcases G.triggerStatus_update_triggerRepeatedProfile_eq_none_or_self
          path punish who dev t with hnone | hsome
      · exact False.elim (ht hnone)
      · exact ⟨t, hsome⟩
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro t ht
    have hnot : ¬ status t = some who := Nat.find_min hex ht
    rcases G.triggerStatus_update_triggerRepeatedProfile_eq_none_or_self
        path punish who dev t with hnone | hsome
    · exact hnone
    · exact False.elim (hnot hsome)

/-- Once the trigger status is `some who` along a unilateral deviation, it
remains `some who` forever. -/
theorem triggerStatus_update_trigger_some_mono
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.RepeatedStrategy who) {t : ℕ}
    (hstatus :
      G.triggerStatus path t
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          some who) :
    ∀ k : ℕ,
      G.triggerStatus path (t + k)
        (fun m =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) m) =
        some who := by
  intro k
  induction k with
  | zero =>
      simpa using hstatus
  | succ k ih =>
      let σdev : G.RepeatedProfile :=
        Function.update (G.triggerRepeatedProfile path punish) who dev
      let hist : G.ProfileHistory (t + k + 1) := fun m => G.repeatedPlay σdev m
      have hinit : G.historyInit hist =
          (fun m : Fin (t + k) => G.repeatedPlay σdev m) := by
        funext m
        rfl
      have ih' :
          G.triggerStatus path (t + k)
            (fun m : Fin (t + k) => G.repeatedPlay σdev m) =
          some who := by
        simpa [σdev] using ih
      change G.triggerStatus path (t + (k + 1))
          (fun m : Fin (t + (k + 1)) => G.repeatedPlay σdev m) =
        some who
      have hnat : t + (k + 1) = t + k + 1 := by omega
      rw [hnat]
      change G.triggerStatus path (t + k + 1) hist = some who
      simp [triggerStatus, hinit, ih']

/-- After the trigger has identified `who`, every other player's realized action
is the chosen punishment action against `who`. -/
theorem repeatedPlay_update_triggerRepeatedProfile_ne_of_status_some
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.RepeatedStrategy who) {t : ℕ}
    (hstatus :
      G.triggerStatus path t
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          some who)
    {j : ι} (hj : j ≠ who) :
    G.repeatedPlay
        (Function.update (G.triggerRepeatedProfile path punish) who dev) t j =
      punish who ⟨j, hj⟩ := by
  rw [repeatedPlay]
  simp [triggerRepeatedProfile, triggerProfileAt, Function.update, hj, hstatus]

/-- Once the trigger has identified `who`, that player's realized stage payoff
is bounded by the best-response value against the selected punishment
opponents. -/
theorem eu_repeatedPlay_update_trigger_lt_of_status_some
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.RepeatedStrategy who) {t : ℕ} {b : ℝ}
    (hbdd : BddAbove (Set.range fun own : G.Strategy who =>
      G.eu (G.profileWithOpponent who own (punish who)) who))
    (hpunish : G.bestResponseValueAgainstOpponents who (punish who) < b)
    (hstatus :
      G.triggerStatus path t
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          some who) :
    G.eu
        (G.repeatedPlay
          (Function.update (G.triggerRepeatedProfile path punish) who dev) t) who <
      b := by
  let ρ : Profile G :=
    G.repeatedPlay
      (Function.update (G.triggerRepeatedProfile path punish) who dev) t
  have hρ : ρ = G.profileWithOpponent who (ρ who) (punish who) := by
    apply G.eq_profileWithOpponent_of_forall_ne who ρ (punish who)
    intro j hj
    exact G.repeatedPlay_update_triggerRepeatedProfile_ne_of_status_some
      path punish who dev hstatus hj
  rw [show G.repeatedPlay
          (Function.update (G.triggerRepeatedProfile path punish) who dev) t = ρ from rfl]
  rw [hρ]
  exact G.eu_profileWithOpponent_lt_of_bestResponseValue_lt
    who (punish who) hbdd hpunish (ρ who)

/-- If a unilateral deviation is in punishment status at `start`, its whole
continuation payoff is bounded by the selected punishment cap. -/
theorem discountedContinuationPayoff_update_trigger_le_const_of_status_some
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    {δ C b : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.RepeatedStrategy who) {start : ℕ}
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C)
    (hbdd : BddAbove (Set.range fun own : G.Strategy who =>
      G.eu (G.profileWithOpponent who own (punish who)) who))
    (hpunish : G.bestResponseValueAgainstOpponents who (punish who) < b)
    (hstatus :
      G.triggerStatus path start
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          some who) :
    G.discountedContinuationPayoff δ
        (fun t =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) t)
        start who ≤ b := by
  apply G.discountedContinuationPayoff_le_const_of_forall_stageEU_le hδ0 hδ1
      (fun t =>
        G.repeatedPlay
          (Function.update (G.triggerRepeatedProfile path punish) who dev) t)
      start who hbd
  intro k
  have hkstatus := G.triggerStatus_update_trigger_some_mono path punish who dev hstatus k
  exact le_of_lt (G.eu_repeatedPlay_update_trigger_lt_of_status_some
    path punish who dev hbdd hpunish hkstatus)

/-- Incentive comparison at the firing boundary.  If the deviation first puts
the trigger into punishment status after period `q`, then the deviating
continuation from `q` is dominated by the intended-path continuation from `q`,
provided the path tail has margin over the punishment cap and the discount
factor is patient enough. -/
theorem discountedContinuationPayoff_update_trigger_le_path_of_fire
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    {δ C b η : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.RepeatedStrategy who) {q : ℕ}
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C)
    (hbdd : BddAbove (Set.range fun own : G.Strategy who =>
      G.eu (G.profileWithOpponent who own (punish who)) who))
    (hpunish : G.bestResponseValueAgainstOpponents who (punish who) < b)
    (hfire :
      G.triggerStatus path (q + 1)
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          some who)
    (hpath_tail : b + η ≤ G.discountedContinuationPayoff δ path (q + 1) who)
    (hpatient : (1 - δ) * (2 * C) ≤ δ * η) :
    G.discountedContinuationPayoff δ
        (fun t =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) t)
        q who ≤
      G.discountedContinuationPayoff δ path q who := by
  let playDev : ℕ → Profile G := fun t =>
    G.repeatedPlay
      (Function.update (G.triggerRepeatedProfile path punish) who dev) t
  have hdev_split := G.discountedContinuationPayoff_eq_head_add
    hδ0 hδ1 playDev q who hbd
  have hpath_split := G.discountedContinuationPayoff_eq_head_add
    hδ0 hδ1 path q who hbd
  have hdev_tail : G.discountedContinuationPayoff δ playDev (q + 1) who ≤ b := by
    exact G.discountedContinuationPayoff_update_trigger_le_const_of_status_some
      hδ0 hδ1 path punish who dev hbd hbdd hpunish hfire
  have hdev_head : G.eu (playDev q) who ≤ C := (abs_le.mp (hbd (playDev q))).2
  have hpath_head : -C ≤ G.eu (path q) who := (abs_le.mp (hbd (path q))).1
  have hdev_upper :
      G.discountedContinuationPayoff δ playDev q who ≤ (1 - δ) * C + δ * b := by
    rw [hdev_split]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hdev_head (sub_nonneg.mpr hδ1.le))
      (mul_le_mul_of_nonneg_left hdev_tail hδ0)
  have hpath_lower :
      (1 - δ) * (-C) + δ * (b + η) ≤
        G.discountedContinuationPayoff δ path q who := by
    rw [hpath_split]
    exact add_le_add
      (mul_le_mul_of_nonneg_left hpath_head (sub_nonneg.mpr hδ1.le))
      (mul_le_mul_of_nonneg_left hpath_tail hδ0)
  have halg : (1 - δ) * C + δ * b ≤ (1 - δ) * (-C) + δ * (b + η) := by
    nlinarith
  exact hdev_upper.trans (halg.trans hpath_lower)

/-- Full first-fire branch of the trigger incentive proof. -/
theorem discountedContinuationPayoff_update_trigger_le_path_of_first_fire
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    {δ C b η : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (who : ι) (dev : G.RepeatedStrategy who) {s : ℕ}
    (hbd : ∀ ρ : Profile G, |G.eu ρ who| ≤ C)
    (hbdd : BddAbove (Set.range fun own : G.Strategy who =>
      G.eu (G.profileWithOpponent who own (punish who)) who))
    (hpunish : G.bestResponseValueAgainstOpponents who (punish who) < b)
    (hfire :
      G.triggerStatus path s
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          some who)
    (hmin : ∀ t < s,
      G.triggerStatus path t
        (fun k =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) k) =
          none)
    (hpath_tail : b + η ≤ G.discountedContinuationPayoff δ path s who)
    (hpatient : (1 - δ) * (2 * C) ≤ δ * η) :
    G.discountedContinuationPayoff δ
        (fun t =>
          G.repeatedPlay
            (Function.update (G.triggerRepeatedProfile path punish) who dev) t)
        0 who ≤
      G.discountedContinuationPayoff δ path 0 who := by
  cases s with
  | zero =>
      simp [triggerStatus] at hfire
  | succ q =>
      let playDev : ℕ → Profile G := fun t =>
        G.repeatedPlay
          (Function.update (G.triggerRepeatedProfile path punish) who dev) t
      have htail : G.discountedContinuationPayoff δ playDev q who ≤
          G.discountedContinuationPayoff δ path q who := by
        apply G.discountedContinuationPayoff_update_trigger_le_path_of_fire
          hδ0 hδ1 path punish who dev hbd hbdd hpunish
        · simpa [playDev] using hfire
        · simpa using hpath_tail
        · exact hpatient
      have hpref : ∀ k < q, playDev (0 + k) = path (0 + k) := by
        intro k hk
        have hstat_k :
            G.triggerStatus path k
              (fun m =>
                G.repeatedPlay
                  (Function.update (G.triggerRepeatedProfile path punish) who dev) m) =
              none :=
          hmin k (lt_trans hk (Nat.lt_succ_self q))
        have hstat_ksucc :
            G.triggerStatus path (k + 1)
              (fun m =>
                G.repeatedPlay
                  (Function.update (G.triggerRepeatedProfile path punish) who dev) m) =
              none :=
          hmin (k + 1) (Nat.succ_lt_succ hk)
        have hplay := G.repeatedPlay_update_trigger_eq_path_of_status_none_succ
          path punish who dev hstat_k hstat_ksucc
        simpa [playDev] using hplay
      have hres := G.discountedContinuationPayoff_le_of_prefix_eq_of_tail_le
        hδ0 hδ1 playDev path 0 q who hbd hpref ?_
      · simpa [playDev] using hres
      · simpa using htail

/-- Trigger-strategy Nash criterion.  Once the intended path has continuation
payoff uniformly above the punishment cap and the discount factor is patient
enough to dominate a one-period gain, the trigger profile is a discounted
repeated-game Nash equilibrium. -/
theorem triggerRepeatedProfile_isDiscountedRepeatedNash
    (G : KernelGame ι) [DecidableEq ι] [∀ i, Nonempty (G.Strategy i)]
    {δ C η : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (path : ℕ → Profile G) (punish : ∀ who, G.OpponentProfile who)
    (b : Payoff ι)
    (hbd : ∀ (who : ι) (ρ : Profile G), |G.eu ρ who| ≤ C)
    (hbdd : ∀ who, BddAbove (Set.range fun own : G.Strategy who =>
      G.eu (G.profileWithOpponent who own (punish who)) who))
    (hpunish : ∀ who, G.bestResponseValueAgainstOpponents who (punish who) < b who)
    (hpath_tail : ∀ who s, b who + η ≤ G.discountedContinuationPayoff δ path s who)
    (hpatient : (1 - δ) * (2 * C) ≤ δ * η) :
    G.IsDiscountedRepeatedNash δ (G.triggerRepeatedProfile path punish) := by
  intro who dev
  rcases G.triggerStatus_update_trigger_first_fire_or_never path punish who dev with
    hnever | hfirecase
  · rw [G.discountedAveragePayoff_update_trigger_eq_of_forall_status_none
      path punish who dev δ hnever]
  · rcases hfirecase with ⟨s, hs, hmin⟩
    let playDev : ℕ → Profile G := fun t =>
      G.repeatedPlay
        (Function.update (G.triggerRepeatedProfile path punish) who dev) t
    have hdev_le_path : G.discountedContinuationPayoff δ playDev 0 who ≤
        G.discountedContinuationPayoff δ path 0 who := by
      exact G.discountedContinuationPayoff_update_trigger_le_path_of_first_fire
        hδ0 hδ1 path punish who dev (hbd who) (hbdd who) (hpunish who)
        hs hmin (hpath_tail who s) hpatient
    have hleft :
        G.discountedAveragePayoff δ (G.triggerRepeatedProfile path punish) who =
          G.discountedContinuationPayoff δ path 0 who := by
      simp [discountedAveragePayoff, discountedContinuationPayoff,
        G.repeatedPlay_triggerRepeatedProfile_eq_path path punish]
    have hright :
        G.discountedAveragePayoff δ
            (Function.update (G.triggerRepeatedProfile path punish) who dev) who =
          G.discountedContinuationPayoff δ playDev 0 who := by
      simp [discountedAveragePayoff, discountedContinuationPayoff, playDev]
    rw [hleft, hright]
    exact hdev_le_path


end KernelGame

end GameTheory
