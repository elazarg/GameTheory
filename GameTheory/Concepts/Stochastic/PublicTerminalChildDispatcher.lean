/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicSuffixHistory

/-!
# Dispatching terminal public histories to child profiles

A finite public selection phase ends after one fixed number of stages.  Each
terminal public history can then select a child behavior profile.  This file
assembles those profiles into one behavior profile on the full history tree:
before the terminal depth it follows the selection profile, and afterwards it
runs the selected child's strategy on the rebased suffix.

The compatibility predicate `Hist.StartsAt` is essential.  `appendHist`
deliberately permits arbitrary suffix histories and therefore forgets the
base's current state when the suffix is nonempty.  Requiring the suffix to
start at that state makes fixed-depth branch cones disjoint and makes the
selected terminal history recoverable from every branch history.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}

/-- A local history genuinely starts at the supplied state. -/
def Hist.StartsAt (state : G.State) {length : ℕ}
    (history : G.Hist length) : Prop :=
  match length with
  | 0 => history.2 = state
  | _ + 1 => (history.1 0).1 = state

@[simp] theorem Hist.startsAt_empty (state : G.State) :
    (G.emptyHist state).StartsAt state := by
  rfl

/-- The fixed-depth prefix of a history whose length is presented as a sum. -/
def terminalPrefix {fuel suffixLength : ℕ}
    (history : G.Hist (fuel + suffixLength)) : G.Hist fuel :=
  (fun index => history.1 (Fin.castAdd suffixLength index),
    match suffixLength with
    | 0 => history.2
    | _ + 1 => (history.1 (Fin.natAdd fuel 0)).1)

/-- The suffix after a fixed-depth prefix. -/
def terminalSuffix {fuel suffixLength : ℕ}
    (history : G.Hist (fuel + suffixLength)) : G.Hist suffixLength :=
  (fun index => history.1 (Fin.natAdd fuel index), history.2)

@[simp] theorem terminalSuffix_appendHist {fuel suffixLength : ℕ}
    (base : G.Hist fuel) (suffix : G.Hist suffixLength) :
    G.terminalSuffix (G.appendHist base suffix) = suffix := by
  apply Prod.ext
  · funext index
    exact Fin.append_right base.1 suffix.1 index
  · rfl

@[simp] theorem terminalPrefix_appendHist {fuel suffixLength : ℕ}
    (base : G.Hist fuel) (suffix : G.Hist suffixLength)
    (hstart : suffix.StartsAt base.2) :
    G.terminalPrefix (G.appendHist base suffix) = base := by
  apply Prod.ext
  · funext index
    exact Fin.append_left base.1 suffix.1 index
  · cases suffixLength with
    | zero =>
        exact hstart
    | succ suffixLength =>
        simpa [Hist.StartsAt, terminalPrefix, appendHist] using hstart

/-- Two compatible suffix cones with the same terminal depth are disjoint. -/
theorem terminalBase_eq_of_appendHist_eq {fuel leftLength rightLength : ℕ}
    {leftBase rightBase : G.Hist fuel}
    {leftSuffix : G.Hist leftLength}
    {rightSuffix : G.Hist rightLength}
    (hleft : leftSuffix.StartsAt leftBase.2)
    (hright : rightSuffix.StartsAt rightBase.2)
    (hlength : leftLength = rightLength)
    (histories_eq :
      G.appendHist leftBase leftSuffix =
        hlength ▸ G.appendHist rightBase rightSuffix) :
    leftBase = rightBase := by
  subst hlength
  have hprefix := congrArg G.terminalPrefix histories_eq
  simpa [hleft, hright] using hprefix

/-- Recover the fixed-depth prefix directly from a longer history. -/
def terminalPrefixLE {fuel time : ℕ} (htime : fuel ≤ time)
    (history : G.Hist time) : G.Hist fuel :=
  (fun index => history.1 (Fin.castLE htime index),
    if hstrict : fuel < time then
      (history.1 ⟨fuel, hstrict⟩).1
    else
      history.2)

/-- Recover the suffix after a fixed depth directly from a longer history. -/
def terminalSuffixLE {fuel time : ℕ} (htime : fuel ≤ time)
    (history : G.Hist time) : G.Hist (time - fuel) :=
  (fun index =>
    history.1 ⟨fuel + index, by
      have hindex : index.val < time - fuel := index.isLt
      omega⟩,
    history.2)

@[simp] theorem terminalPrefixLE_appendHist {fuel suffixLength : ℕ}
    (base : G.Hist fuel) (suffix : G.Hist suffixLength)
    (hstart : suffix.StartsAt base.2) :
    G.terminalPrefixLE (Nat.le_add_right fuel suffixLength)
        (G.appendHist base suffix) =
      base := by
  apply Prod.ext
  · funext index
    exact Fin.append_left base.1 suffix.1 index
  · cases suffixLength with
    | zero =>
        unfold terminalPrefixLE
        simp only [Nat.add_zero, lt_self_iff_false, ↓reduceDIte,
          appendHist_snd]
        exact hstart
    | succ suffixLength =>
        unfold terminalPrefixLE
        simp only [Nat.lt_add_of_pos_right (Nat.zero_lt_succ _),
          ↓reduceDIte]
        change
          (Fin.append base.1 suffix.1
            ⟨fuel, Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)⟩).1 =
            base.2
        rw [show
          (⟨fuel, Nat.lt_add_of_pos_right (Nat.zero_lt_succ _)⟩ :
            Fin (fuel + (suffixLength + 1))) =
              Fin.natAdd fuel 0 by
            apply Fin.ext
            rfl]
        rw [Fin.append_right]
        exact hstart

theorem terminalSuffixLE_appendHist_heq {fuel suffixLength : ℕ}
    (base : G.Hist fuel) (suffix : G.Hist suffixLength) :
    G.terminalSuffixLE (Nat.le_add_right fuel suffixLength)
        (G.appendHist base suffix) ≍
      suffix := by
  have length_eq : fuel + suffixLength - fuel = suffixLength :=
    Nat.add_sub_cancel_left fuel suffixLength
  unfold terminalSuffixLE appendHist
  let sourceRecords :
      Fin (fuel + suffixLength - fuel) →
        G.State × G.JointAct :=
    fun index =>
      Fin.append base.1 suffix.1
        ⟨fuel + index, by
          have hindex : index.val < fuel + suffixLength - fuel :=
            index.isLt
          omega⟩
  change (sourceRecords, suffix.2) ≍ (suffix.1, suffix.2)
  have records_heq :
      sourceRecords ≍ suffix.1 := by
    apply Function.hfunext (congrArg Fin length_eq)
    intro left right hindex
    have packaged_eq :
        (⟨fuel + suffixLength - fuel, left⟩ :
          Σ length, Fin length) =
          ⟨suffixLength, right⟩ :=
      Sigma.ext length_eq hindex
    have value_eq : left.val = right.val :=
      congrArg (fun index : Σ length, Fin length => index.2.val)
        packaged_eq
    apply heq_of_eq
    unfold sourceRecords
    rw [show
      (⟨fuel + left, by
        have hleft : left.val < fuel + suffixLength - fuel :=
          left.isLt
        omega⟩ : Fin (fuel + suffixLength)) =
          Fin.natAdd fuel right by
        apply Fin.ext
        simpa using congrArg (fun value => fuel + value) value_eq]
    exact Fin.append_right base.1 suffix.1 right
  exact HEq.ndrec (motive := fun {recordsType} records =>
      (sourceRecords, suffix.2) ≍ (records, suffix.2))
    HEq.rfl records_heq

/-- One total behavior profile obtained by dispatching each fixed-depth
terminal public history to its child profile. -/
def terminalChildDispatcher (fuel : ℕ)
    (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile) :
    G.BehaviorProfile :=
  fun who time history =>
    if htime : fuel ≤ time then
      let base := G.terminalPrefixLE htime history
      let suffix := G.terminalSuffixLE htime history
      child base who (time - fuel) suffix
    else
      selection who time history

theorem terminalChildDispatcher_before {fuel time : ℕ}
    (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (htime : time < fuel) (who : ι) (history : G.Hist time) :
    G.terminalChildDispatcher fuel selection child who time history =
      selection who time history := by
  simp [terminalChildDispatcher, Nat.not_le_of_lt htime]

theorem terminalChildDispatcher_appendHist {fuel suffixLength : ℕ}
    (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) (suffix : G.Hist suffixLength)
    (hstart : suffix.StartsAt base.2) (who : ι) :
    G.terminalChildDispatcher fuel selection child who
        (fuel + suffixLength) (G.appendHist base suffix) =
      child base who suffixLength suffix := by
  rw [terminalChildDispatcher]
  simp only [dif_pos (Nat.le_add_right fuel suffixLength)]
  congr 3
  · exact G.terminalPrefixLE_appendHist base suffix hstart
  · exact Nat.add_sub_cancel_left fuel suffixLength
  · exact G.terminalSuffixLE_appendHist_heq base suffix

/-- Exact gluing condition for one terminal base.

The condition is automatic on suffixes that start at `base.2`.  It also
specifies the child's irrelevant off-path behavior on malformed suffixes,
where `appendHist` alone cannot retain the terminal state. -/
def TerminalChildCompatibleAt {fuel : ℕ}
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) : Prop :=
  ∀ (who : ι) (suffixLength : ℕ) (suffix : G.Hist suffixLength),
    child
        (G.terminalPrefixLE (Nat.le_add_right fuel suffixLength)
          (G.appendHist base suffix))
        who (fuel + suffixLength - fuel)
        (G.terminalSuffixLE (Nat.le_add_right fuel suffixLength)
          (G.appendHist base suffix)) =
      child base who suffixLength suffix

/-- A terminal child family has globally compatible off-path behavior. -/
def TerminalChildFamilyCompatible {fuel : ℕ}
    (child : G.Hist fuel → G.BehaviorProfile) : Prop :=
  ∀ base, TerminalChildCompatibleAt child base

/-- On a compatible terminal base, the global dispatcher is exactly the
selected child's behavior profile after rebasing. -/
theorem afterHistoryProfile_terminalChildDispatcher
    (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) (hcompatible : TerminalChildCompatibleAt child base) :
    G.afterHistoryProfile
        (G.terminalChildDispatcher fuel selection child) base =
      child base := by
  funext who suffixLength suffix
  rw [afterHistoryProfile_apply, terminalChildDispatcher]
  simp only [dif_pos (Nat.le_add_right fuel suffixLength)]
  exact hcompatible who suffixLength suffix

/-- Rebasing an arbitrary unilateral deviation from the global dispatcher
updates exactly the selected child with the rebased deviation. -/
theorem afterHistoryProfile_update_terminalChildDispatcher
    [DecidableEq ι] (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) (hcompatible : TerminalChildCompatibleAt child base)
    (who : ι) (deviation : G.BehaviorStrategy who) :
    G.afterHistoryProfile
        (Function.update
          (G.terminalChildDispatcher fuel selection child) who deviation)
        base =
      Function.update (child base) who
        (G.afterHistoryStrategy deviation base) := by
  rw [G.afterHistoryProfile_update,
    G.afterHistoryProfile_terminalChildDispatcher fuel selection child base
      hcompatible]

/-- The canonical globally consistent child profile obtained by restricting
the assembled dispatcher after one terminal base.

This agrees with the supplied child on every suffix that starts at the
terminal state, but canonically fills malformed off-path suffixes from the
one global dispatcher. -/
def canonicalTerminalChildProfile (fuel : ℕ)
    (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) : G.BehaviorProfile :=
  G.afterHistoryProfile
    (G.terminalChildDispatcher fuel selection child) base

@[simp] theorem afterHistoryProfile_terminalChildDispatcher_canonical
    (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) :
    G.afterHistoryProfile
        (G.terminalChildDispatcher fuel selection child) base =
      G.canonicalTerminalChildProfile fuel selection child base :=
  rfl

/-- Canonical off-path completion preserves the intended child strategy on
every suffix that genuinely starts at the selected terminal state. -/
theorem canonicalTerminalChildProfile_apply_of_startsAt
    (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) (who : ι) {suffixLength : ℕ}
    (suffix : G.Hist suffixLength) (hstart : suffix.StartsAt base.2) :
    G.canonicalTerminalChildProfile fuel selection child base who
        suffixLength suffix =
      child base who suffixLength suffix := by
  exact G.terminalChildDispatcher_appendHist selection child base suffix
    hstart who

/-- An arbitrary unilateral deviation rebases through the canonical
dispatcher exactly. -/
theorem afterHistoryProfile_update_terminalChildDispatcher_canonical
    [DecidableEq ι] (fuel : ℕ) (selection : G.BehaviorProfile)
    (child : G.Hist fuel → G.BehaviorProfile)
    (base : G.Hist fuel) (who : ι)
    (deviation : G.BehaviorStrategy who) :
    G.afterHistoryProfile
        (Function.update
          (G.terminalChildDispatcher fuel selection child) who deviation)
        base =
      Function.update
        (G.canonicalTerminalChildProfile fuel selection child base) who
        (G.afterHistoryStrategy deviation base) := by
  exact G.afterHistoryProfile_update
    (G.terminalChildDispatcher fuel selection child) who deviation base

end StochasticGame
end GameTheory
