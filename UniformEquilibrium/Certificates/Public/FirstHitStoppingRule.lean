/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Certificates.Public.CausalTerminalChildDispatcher
import UniformEquilibrium.Certificates.Public.CausalStoppingEventRatio

/-!
# Online rules from finite public first hits

A public first-hit region is specified by a predicate on bounded public
prefixes.  Along a finite public history, the first prefix satisfying the
predicate is selected; if none does, the fixed fuel endpoint is selected.  Before the
fuel endpoint the online view is absent until the first hit, and afterwards
it retains the first stopped prefix.

This construction supplies the reconstruction, occurrence, compatible
persistence, and canonical completion fields of
`OnlineCausalBoundedStoppingRule`.  It is purely pathwise and imposes no
probabilistic reachability or strategic condition on the stopping region.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}

/-- The finite set of times at which a completed public history enters the
prefix stopping region. -/
def publicHitTimes
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {time : ℕ} (history : G.Hist time) :
    Finset (Fin (time + 1)) :=
  Finset.univ.filter fun stage =>
    terminal stage.val (G.boundedHistoryPrefix history stage)

/-- The first public hit, when the history visits the stopping region. -/
def firstPublicHit?
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {time : ℕ} (history : G.Hist time) :
    Option (Fin (time + 1)) :=
  if hhit : (G.publicHitTimes terminal history).Nonempty then
    some ((G.publicHitTimes terminal history).min' hhit)
  else
    none

/-- A finite first-hit selector, with the fuel endpoint used when there is no
earlier hit. -/
def firstHitStopSelector
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    (fuel : ℕ) :
    G.BoundedPublicStopSelector fuel :=
  fun history =>
    (G.firstPublicHit? terminal history).getD (Fin.last fuel)

/-- The public-prefix region which never stops before the mandatory
selector endpoint. -/
def neverPublicStop (G : StochasticGame ι) :
    ∀ time, G.Hist time → Prop :=
  fun _ _ => False

instance neverPublicStop_decidable (time : ℕ) :
    DecidablePred (neverPublicStop G time) :=
  fun _ => isFalse id

@[simp] theorem publicHitTimes_never
    {time : ℕ} (history : G.Hist time) :
    G.publicHitTimes (neverPublicStop G) history = ∅ := by
  ext stage
  simp [publicHitTimes, neverPublicStop]

@[simp] theorem firstPublicHit?_never
    {time : ℕ} (history : G.Hist time) :
    G.firstPublicHit? (neverPublicStop G) history = none := by
  simp [firstPublicHit?, publicHitTimes_never]

@[simp] theorem firstHitStopSelector_never
    (fuel : ℕ) (history : G.Hist fuel) :
    G.firstHitStopSelector
        (neverPublicStop G) fuel history =
      Fin.last fuel := by
  simp [firstHitStopSelector]

@[simp] theorem boundedHistoryPrefix_last_eq
    {time : ℕ} (history : G.Hist time) :
    G.boundedHistoryPrefix history (Fin.last time) = history := by
  apply Prod.ext
  · funext index
    rfl
  · simp [boundedHistoryPrefix]

@[simp] theorem boundedHistoryPrefix_endpoint_eq
    {time : ℕ} (history : G.Hist time) :
    G.boundedHistoryPrefix history
        ⟨time, Nat.lt_succ_self time⟩ =
      history := by
  apply Prod.ext
  · funext index
    rfl
  · simp [boundedHistoryPrefix]

@[simp] theorem mem_publicHitTimes_iff
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {time : ℕ} (history : G.Hist time) (stage : Fin (time + 1)) :
    stage ∈ G.publicHitTimes terminal history ↔
      terminal stage.val
        (G.boundedHistoryPrefix history stage) := by
  simp [publicHitTimes]

theorem firstPublicHit?_eq_some_iff
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {time : ℕ} (history : G.Hist time) (stage : Fin (time + 1)) :
    G.firstPublicHit? terminal history = some stage ↔
      terminal stage.val
          (G.boundedHistoryPrefix history stage) ∧
        ∀ earlier : Fin (time + 1),
          terminal earlier.val
              (G.boundedHistoryPrefix history earlier) →
            stage ≤ earlier := by
  unfold firstPublicHit?
  split_ifs with hhit
  · simp only [Option.some.injEq]
    rw [Finset.min'_eq_iff]
    simp only [mem_publicHitTimes_iff]
  · constructor
    · intro h
      contradiction
    · rintro ⟨hstage, _⟩
      exact hhit
        ⟨stage, (G.mem_publicHitTimes_iff
          terminal history stage).2 hstage⟩

@[simp] theorem firstHitStopSelector_eq_of_hit
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {fuel : ℕ} (history : G.Hist fuel) (stage : Fin (fuel + 1))
    (hhit : G.firstPublicHit? terminal history = some stage) :
    G.firstHitStopSelector terminal fuel history = stage := by
  simp [firstHitStopSelector, hhit]

@[simp] theorem firstHitStopSelector_eq_last_of_no_hit
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {fuel : ℕ} (history : G.Hist fuel)
    (hno : G.firstPublicHit? terminal history = none) :
    G.firstHitStopSelector terminal fuel history = Fin.last fuel := by
  simp [firstHitStopSelector, hno]

/-- Equality of selected times transports the dependent stopped history in
the expected way. -/
theorem selectedStoppedHistory_eq_of_selector_eq
    {fuel : ℕ} (selector : G.BoundedPublicStopSelector fuel)
    (history : G.Hist fuel) (stage : Fin (fuel + 1))
    (hstage : selector history = stage) :
    G.selectedStoppedHistory selector history =
      (⟨stage, G.boundedHistoryPrefix history stage⟩ :
        G.BoundedStoppedHistory fuel) := by
  unfold selectedStoppedHistory
  apply Sigma.ext hstage
  have htransport :=
    G.cast_boundedHistoryPrefix history hstage
  exact
    (cast_heq
      (congrArg G.Hist (congrArg Fin.val hstage))
      (G.boundedHistoryPrefix history
        (selector history))).symm.trans
      (heq_of_eq htransport)

/-- Once a first hit occurs in a bounded prefix, the same time is the first
hit of every longer history carrying that prefix. -/
theorem firstPublicHit?_of_boundedPrefix
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {cut time : ℕ} (hcut : cut ≤ time) (history : G.Hist time)
    (stage : Fin (cut + 1))
    (hhit :
      G.firstPublicHit? terminal
          (G.boundedHistoryPrefix history
            ⟨cut, Nat.lt_succ_of_le hcut⟩) =
        some stage) :
    G.firstPublicHit? terminal history =
      some
        ⟨stage.val,
          lt_of_lt_of_le stage.isLt
            (Nat.succ_le_succ hcut)⟩ := by
  rw [G.firstPublicHit?_eq_some_iff] at hhit ⊢
  constructor
  · have hprefix :=
      G.boundedHistoryPrefix_nested history hcut stage
    simpa only [hprefix] using hhit.1
  · intro earlier hearlier
    by_cases hearlierCut : earlier.val < cut + 1
    · let earlierAtCut : Fin (cut + 1) :=
        ⟨earlier.val, hearlierCut⟩
      have hprefix :=
        G.boundedHistoryPrefix_nested history hcut earlierAtCut
      have hterminalAtCut :
          terminal earlierAtCut.val
            (G.boundedHistoryPrefix
              (G.boundedHistoryPrefix history
                ⟨cut, Nat.lt_succ_of_le hcut⟩)
              earlierAtCut) := by
        have hprefixTerminal :=
          congrArg (terminal earlierAtCut.val) hprefix
        exact hprefixTerminal.symm.mp hearlier
      have hle := hhit.2 earlierAtCut hterminalAtCut
      exact hle
    · have hstageLeCut : stage.val ≤ cut :=
        Nat.lt_succ_iff.mp stage.isLt
      change stage.val ≤ earlier.val
      omega

/-- If a full history has no hit, none of its bounded prefixes has a hit. -/
theorem firstPublicHit?_boundedPrefix_eq_none
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {cut time : ℕ} (hcut : cut ≤ time) (history : G.Hist time)
    (hno : G.firstPublicHit? terminal history = none) :
    G.firstPublicHit? terminal
        (G.boundedHistoryPrefix history
          ⟨cut, Nat.lt_succ_of_le hcut⟩) =
      none := by
  by_contra hnot
  obtain ⟨stage, hstage⟩ :=
    Option.ne_none_iff_exists'.mp hnot
  have hfull :=
    G.firstPublicHit?_of_boundedPrefix
      terminal hcut history stage hstage
  rw [hno] at hfull
  contradiction

/-- Restricting a history to its first-hit time makes the endpoint the first
hit of that shorter history. -/
theorem firstPublicHit?_boundedPrefix_eq_last
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {time : ℕ} (history : G.Hist time)
    (stage : Fin (time + 1))
    (hhit : G.firstPublicHit? terminal history = some stage) :
    G.firstPublicHit? terminal
        (G.boundedHistoryPrefix history stage) =
      some (Fin.last stage.val) := by
  rw [G.firstPublicHit?_eq_some_iff] at hhit ⊢
  constructor
  · have hprefix' :=
      G.boundedHistoryPrefix_last_eq
        (G.boundedHistoryPrefix history stage)
    exact
      (congrArg (terminal stage.val) hprefix').symm.mp
        hhit.1
  · intro earlier hearlier
    let lifted : Fin (time + 1) :=
      ⟨earlier.val,
        lt_of_lt_of_le earlier.isLt
          (Nat.succ_le_succ
            (Nat.lt_succ_iff.mp stage.isLt))⟩
    have hprefix :=
      G.boundedHistoryPrefix_nested history
        (Nat.lt_succ_iff.mp stage.isLt) earlier
    have hterminal :
        terminal lifted.val
          (G.boundedHistoryPrefix history lifted) := by
      simpa only [lifted, hprefix] using hearlier
    have hle := hhit.2 lifted hterminal
    change stage.val ≤ earlier.val
    exact hle

/-- The first-hit selector is a causal bounded stopping time. -/
theorem firstHitStopSelector_causal
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    (fuel : ℕ) :
    G.IsCausalBoundedStopSelector
      (G.firstHitStopSelector terminal fuel) := by
  rw [← G.isExactPrefixBoundedStopSelector_iff_causal]
  intro left right hprefix
  unfold firstHitStopSelector
  change
    G.boundedHistoryPrefix left
        ((G.firstPublicHit? terminal left).getD (Fin.last fuel)) =
      G.boundedHistoryPrefix right
        ((G.firstPublicHit? terminal left).getD (Fin.last fuel))
      at hprefix
  cases hleft :
      G.firstPublicHit? terminal left with
  | none =>
      have hget :
          (G.firstPublicHit? terminal left).getD (Fin.last fuel) =
            Fin.last fuel := by
        rw [hleft]
        rfl
      rw [hget] at hprefix
      have hprefixLast :
          G.boundedHistoryPrefix left (Fin.last fuel) =
            G.boundedHistoryPrefix right (Fin.last fuel) := by
        exact hprefix
      have hfull : left = right := by
        exact
          (G.boundedHistoryPrefix_last_eq left).symm.trans
            (hprefixLast.trans
              (G.boundedHistoryPrefix_last_eq right))
      subst right
      simp [hleft]
  | some stage =>
      have hget :
          (G.firstPublicHit? terminal left).getD (Fin.last fuel) =
            stage := by
        rw [hleft]
        rfl
      rw [hget] at hprefix
      have hprefixStage :
          G.boundedHistoryPrefix left stage =
            G.boundedHistoryPrefix right stage := by
        exact hprefix
      have hshortLeft :=
        G.firstPublicHit?_boundedPrefix_eq_last
          terminal left stage hleft
      have hshortRight :
          G.firstPublicHit? terminal
              (G.boundedHistoryPrefix right stage) =
            some (Fin.last stage.val) := by
        rw [← hprefixStage]
        exact hshortLeft
      have hright :=
        G.firstPublicHit?_of_boundedPrefix
          terminal (Nat.lt_succ_iff.mp stage.isLt)
          right (Fin.last stage.val) hshortRight
      have hrightStage :
          G.firstPublicHit? terminal right = some stage := by
        have hindex :
            (⟨(Fin.last stage.val).val,
              lt_of_lt_of_le (Fin.last stage.val).isLt
                (Nat.succ_le_succ
                  (Nat.lt_succ_iff.mp stage.isLt))⟩ :
                Fin (fuel + 1)) =
              stage := by
          apply Fin.ext
          simp
        rw [hindex] at hright
        exact hright
      simp [hrightStage]

/-- Enlarge only the fuel bound carried by an online stopped path. -/
def promoteOnlineStoppedPath
    {small fuel time : ℕ} (hsmall : small ≤ fuel)
    (path : G.OnlineStoppedPath small time) :
    G.OnlineStoppedPath fuel time where
  base :=
    ⟨⟨path.base.1.val,
      Nat.lt_succ_of_le
        (le_trans (Nat.lt_succ_iff.mp path.base.1.isLt)
          hsmall)⟩,
      path.base.2⟩
  suffixLength := path.suffixLength
  suffix := path.suffix
  length_eq := path.length_eq

/-- Promotion changes no history data in an online path. -/
@[simp] theorem promoteOnlineStoppedPath_base_history
    {small fuel time : ℕ} (hsmall : small ≤ fuel)
    (path : G.OnlineStoppedPath small time) :
    (G.promoteOnlineStoppedPath hsmall path).base.2 =
      path.base.2 :=
  rfl

/-- The canonical root online path reconstructs its history and carries a
genuinely rooted suffix. -/
theorem rootOnlineStoppedPath_sound
    {fuel time : ℕ}
    (selector : G.BoundedPublicStopSelector fuel)
    (htime : fuel ≤ time) (history : G.Hist time) :
    let path :=
      G.rootOnlineStoppedPathOfHistory selector htime history
    path.suffix.StartsAt path.base.2.2 ∧
      cast (congrArg G.Hist path.length_eq)
          (G.appendHist path.base.2 path.suffix) =
        history := by
  let stopped :=
    G.rootStoppedPathOfHistory selector htime history
  have hprefix :=
    G.boundedHistoryPrefix_rootStoppedPathOfHistory
      selector htime history
  have hterminalPrefix :=
    G.terminalPrefix_appendHist_of_rootPrefix
      htime stopped hprefix
  have hstart :
      stopped.2.StartsAt stopped.1.2.2 :=
    Hist.startsAt_of_terminalPrefix_appendHist_eq
      stopped.1.2 stopped.2 hterminalPrefix
  constructor
  · exact hstart
  · exact
      G.rootHistoryOfStoppedSuffix_rootStoppedPathOfHistory_exact
        selector htime history

/-- Package a first hit observed strictly before the fuel as an online
stopped path. -/
def onlineStoppedPathAtFirstHit
    {fuel time : ℕ} (htime : time < fuel)
    (history : G.Hist time) (stage : Fin (time + 1)) :
    G.OnlineStoppedPath fuel time :=
  let selector : G.BoundedPublicStopSelector time :=
    fun _ => stage
  G.promoteOnlineStoppedPath
    (Nat.le_of_lt htime)
    (G.rootOnlineStoppedPathOfHistory
      selector (le_refl time) history)

@[simp] theorem onlineStoppedPathAtFirstHit_base_val
    {fuel time : ℕ} (htime : time < fuel)
    (history : G.Hist time) (stage : Fin (time + 1)) :
    (G.onlineStoppedPathAtFirstHit
      htime history stage).base.1.val =
      stage.val :=
  rfl

/-- The stopped base packaged by a pre-fuel first hit is the corresponding
bounded prefix, with only its bound promoted to `fuel`. -/
theorem onlineStoppedPathAtFirstHit_base
    {fuel time : ℕ} (htime : time < fuel)
    (history : G.Hist time) (stage : Fin (time + 1)) :
    (G.onlineStoppedPathAtFirstHit
      htime history stage).base =
      (⟨⟨stage.val,
        Nat.lt_succ_of_le
          (le_trans
            (Nat.lt_succ_iff.mp stage.isLt)
            (Nat.le_of_lt htime))⟩,
        G.boundedHistoryPrefix history stage⟩ :
        G.BoundedStoppedHistory fuel) := by
  change
    (⟨⟨stage.val, _⟩,
      G.boundedHistoryPrefix
        (G.boundedHistoryPrefix history
          ⟨time, Nat.lt_succ_self time⟩)
        stage⟩ :
      G.BoundedStoppedHistory fuel) =
      _
  rw [G.boundedHistoryPrefix_endpoint_eq]

/-- The online first-hit view.  At and beyond the fuel it is definitionally
the canonical root decomposition required by downstream stopped laws. -/
def firstHitOnlineView
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    (fuel : ℕ) :
    (time : ℕ) → G.Hist time →
      Option (G.OnlineStoppedPath fuel time) :=
  fun time history =>
    if htime : fuel ≤ time then
      some
        (G.rootOnlineStoppedPathOfHistory
          (G.firstHitStopSelector terminal fuel)
          htime history)
    else
      match _hhit : G.firstPublicHit? terminal history with
      | none => none
      | some stage =>
          some
            (G.onlineStoppedPathAtFirstHit
              (Nat.lt_of_not_ge htime) history stage)

@[simp] theorem firstHitOnlineView_never_of_lt
    (fuel : ℕ) {time : ℕ} (htime : time < fuel)
    (history : G.Hist time) :
    G.firstHitOnlineView
        (neverPublicStop G) fuel time history =
      none := by
  rw [firstHitOnlineView]
  simp only [Nat.not_le.mpr htime, ↓reduceDIte]
  split
  next hnone => rfl
  next stage hhit =>
    rw [G.firstPublicHit?_never] at hhit
    simp only [reduceCtorEq] at hhit

/-- Two online paths are equal when their dependent stopped bases and suffix
data agree. -/
theorem OnlineStoppedPath.ext_data
    {fuel time : ℕ}
    {left right : G.OnlineStoppedPath fuel time}
    (hbase : left.base = right.base)
    (hlength : left.suffixLength = right.suffixLength)
    (hsuffix :
      HEq left.suffix right.suffix) :
    left = right := by
  cases left with
  | mk leftBase leftLength leftSuffix leftEq =>
      cases right with
      | mk rightBase rightLength rightSuffix rightEq =>
          simp only at hbase hlength hsuffix
          subst rightBase
          subst rightLength
          have hsuffixEq : leftSuffix = rightSuffix :=
            eq_of_heq hsuffix
          subst rightSuffix
          rfl

/-- At one history, a stopped base uniquely determines the compatible online
path: the suffix is recovered from reconstruction. -/
theorem OnlineStoppedPath.eq_of_base_eq_of_reconstructs
    {fuel time : ℕ}
    {left right : G.OnlineStoppedPath fuel time}
    (history : G.Hist time)
    (hbase : left.base = right.base)
    (left_reconstructs :
      cast (congrArg G.Hist left.length_eq)
          (G.appendHist left.base.2 left.suffix) =
        history)
    (right_reconstructs :
      cast (congrArg G.Hist right.length_eq)
          (G.appendHist right.base.2 right.suffix) =
        history) :
    left = right := by
  cases left with
  | mk leftBase leftLength leftSuffix leftEq =>
      cases right with
      | mk rightBase rightLength rightSuffix rightEq =>
          simp only at hbase left_reconstructs right_reconstructs
          subst rightBase
          have hlength : leftLength = rightLength := by
            omega
          subst rightLength
          have happend :
              G.appendHist leftBase.2 leftSuffix =
                G.appendHist leftBase.2 rightSuffix := by
            have hcast :=
              left_reconstructs.trans right_reconstructs.symm
            change
              (Equiv.cast (congrArg G.Hist leftEq))
                  (G.appendHist leftBase.2 leftSuffix) =
                (Equiv.cast (congrArg G.Hist leftEq))
                  (G.appendHist leftBase.2 rightSuffix)
                at hcast
            apply
              (Equiv.cast
                (congrArg G.Hist leftEq)).injective
            exact hcast
          have hsuffix :=
            congrArg G.terminalSuffix happend
          have hsuffixEq : leftSuffix = rightSuffix := by
            simpa only [G.terminalSuffix_appendHist] using hsuffix
          subst rightSuffix
          rfl

/-- If a selector stops at the fuel endpoint, its canonical root path has an
empty suffix. -/
theorem rootOnlineStoppedPath_eq_append_empty_of_selector_eq_last
    {fuel : ℕ} (selector : G.BoundedPublicStopSelector fuel)
    (history : G.Hist fuel)
    (hlast : selector history = Fin.last fuel) :
    G.rootOnlineStoppedPathOfHistory selector
        (le_refl fuel) history =
      G.onlineStoppedPathOfAppend
        (⟨Fin.last fuel, history⟩ :
          G.BoundedStoppedHistory fuel)
        (G.emptyHist history.2) := by
  apply OnlineStoppedPath.eq_of_base_eq_of_reconstructs history
  · change
      G.selectedStoppedHistory selector
          (G.boundedHistoryPrefix history
            ⟨fuel, Nat.lt_succ_self fuel⟩) =
        (⟨Fin.last fuel, history⟩ :
          G.BoundedStoppedHistory fuel)
    rw [G.boundedHistoryPrefix_endpoint_eq]
    unfold selectedStoppedHistory
    apply Sigma.ext hlast
    have htransport :
        cast (congrArg G.Hist (congrArg Fin.val hlast))
            (G.boundedHistoryPrefix history (selector history)) =
          history :=
      (G.cast_boundedHistoryPrefix history hlast).trans
        (G.boundedHistoryPrefix_last_eq history)
    exact
      (cast_heq
        (congrArg G.Hist (congrArg Fin.val hlast))
        (G.boundedHistoryPrefix history
          (selector history))).symm.trans
        (heq_of_eq htransport)
  · exact
      (G.rootOnlineStoppedPath_sound
        selector (le_refl fuel) history).2
  · apply Prod.ext
    · funext index
      exact Fin.append_left history.1
        (G.emptyHist history.2).1 index
    · rfl

/-- A first-hit path observed at the current endpoint is exactly the empty
suffix occurrence of that endpoint, promoted to the larger fuel bound. -/
theorem onlineStoppedPathAtFirstHit_last
    {fuel time : ℕ} (htime : time < fuel)
    (history : G.Hist time) :
    G.onlineStoppedPathAtFirstHit
        htime history (Fin.last time) =
      G.onlineStoppedPathOfAppend
        (⟨⟨time, Nat.lt_succ_of_le (Nat.le_of_lt htime)⟩,
          history⟩ :
          G.BoundedStoppedHistory fuel)
        (G.emptyHist history.2) := by
  let selector : G.BoundedPublicStopSelector time :=
    fun _ => Fin.last time
  change
    G.promoteOnlineStoppedPath (Nat.le_of_lt htime)
        (G.rootOnlineStoppedPathOfHistory
          selector (le_refl time) history) =
      _
  rw [
    G.rootOnlineStoppedPath_eq_append_empty_of_selector_eq_last
      selector history rfl
  ]
  apply OnlineStoppedPath.ext_data
  · apply Sigma.ext
    · apply Fin.ext
      rfl
    · rfl
  · rfl
  · rfl

/-- Every stopped prefix selected from a complete fuel history occurs in the
online first-hit view at its own stopping time. -/
theorem selectedFirstHitPrefix_occurs
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {fuel : ℕ} (history : G.Hist fuel) :
    G.OnlineStoppedBaseOccurs
      (G.firstHitOnlineView terminal fuel)
      (G.selectedStoppedHistory
        (G.firstHitStopSelector terminal fuel) history) := by
  unfold OnlineStoppedBaseOccurs
  cases hhit :
      G.firstPublicHit? terminal history with
  | none =>
      have hlast :
          G.firstHitStopSelector terminal fuel history =
            Fin.last fuel := by
        simp [firstHitStopSelector, hhit]
      have hroot :=
        G.rootOnlineStoppedPath_eq_append_empty_of_selector_eq_last
          (G.firstHitStopSelector terminal fuel)
          history hlast
      rw [
        G.selectedStoppedHistory_eq_of_selector_eq
          (G.firstHitStopSelector terminal fuel)
          history (Fin.last fuel) hlast
      ]
      rw [G.boundedHistoryPrefix_last_eq]
      simpa [firstHitOnlineView] using
        congrArg some hroot
  | some stage =>
      by_cases hstage : stage.val = fuel
      · have hstageLast : stage = Fin.last fuel := by
          apply Fin.ext
          exact hstage
        subst stage
        have hlast :
            G.firstHitStopSelector terminal fuel history =
              Fin.last fuel := by
          simp [firstHitStopSelector, hhit]
        have hroot :=
          G.rootOnlineStoppedPath_eq_append_empty_of_selector_eq_last
            (G.firstHitStopSelector terminal fuel)
            history hlast
        rw [
          G.selectedStoppedHistory_eq_of_selector_eq
            (G.firstHitStopSelector terminal fuel)
            history (Fin.last fuel) hlast
        ]
        rw [G.boundedHistoryPrefix_last_eq]
        simpa [firstHitOnlineView] using
          congrArg some hroot
      · have hstageLt : stage.val < fuel := by
          have hle := Nat.lt_succ_iff.mp stage.isLt
          omega
        have hrestricted :=
          G.firstPublicHit?_boundedPrefix_eq_last
            terminal history stage hhit
        have hpath :=
          G.onlineStoppedPathAtFirstHit_last
            hstageLt (G.boundedHistoryPrefix history stage)
        have hselector :
            G.firstHitStopSelector terminal fuel history = stage := by
          simp [firstHitStopSelector, hhit]
        rw [
          G.selectedStoppedHistory_eq_of_selector_eq
            (G.firstHitStopSelector terminal fuel)
            history stage hselector
        ]
        rw [firstHitOnlineView]
        simp only [
          Nat.not_le.mpr hstageLt, ↓reduceDIte
        ]
        split
        next hnone =>
          rw [hrestricted] at hnone
          contradiction
        next selected hselected =>
          rw [hrestricted] at hselected
          simp only [Option.some.injEq] at hselected
          subst selected
          exact congrArg some hpath

/-- If the canonical selector chooses a displayed compatible base from an
appended history, the canonical online path is exactly that base and suffix. -/
theorem rootOnlineStoppedPath_append_of_selected_base
    {fuel suffixLength : ℕ}
    (selector : G.BoundedPublicStopSelector fuel)
    (base : G.BoundedStoppedHistory fuel)
    (suffix : G.Hist suffixLength)
    (hfuel : fuel ≤ base.1.val + suffixLength)
    (hselected :
      G.selectedStoppedHistory selector
          (G.boundedHistoryPrefix
            (G.appendHist base.2 suffix)
            ⟨fuel, Nat.lt_succ_of_le hfuel⟩) =
        base) :
    G.rootOnlineStoppedPathOfHistory selector hfuel
        (G.appendHist base.2 suffix) =
      G.onlineStoppedPathOfAppend base suffix := by
  apply OnlineStoppedPath.eq_of_base_eq_of_reconstructs
    (G.appendHist base.2 suffix)
  · exact hselected
  · exact
      (G.rootOnlineStoppedPath_sound selector hfuel
        (G.appendHist base.2 suffix)).2
  · rfl

/-- Before the fuel endpoint, recognizing the already stopped base in an
appended history yields exactly the displayed online path. -/
theorem onlineStoppedPathAtFirstHit_append
    {fuel suffixLength : ℕ}
    (base : G.BoundedStoppedHistory fuel)
    (suffix : G.Hist suffixLength)
    (hstart : suffix.StartsAt base.2.2)
    (htotal : base.1.val + suffixLength < fuel) :
    G.onlineStoppedPathAtFirstHit htotal
        (G.appendHist base.2 suffix)
        ⟨base.1.val, by omega⟩ =
      G.onlineStoppedPathOfAppend base suffix := by
  let localSelector :
      G.BoundedPublicStopSelector
        (base.1.val + suffixLength) :=
    fun _ => ⟨base.1.val, by omega⟩
  apply OnlineStoppedPath.eq_of_base_eq_of_reconstructs
    (G.appendHist base.2 suffix)
  · change
      (⟨⟨base.1.val, by omega⟩,
        G.boundedHistoryPrefix
          (G.boundedHistoryPrefix
            (G.appendHist base.2 suffix)
            ⟨base.1.val + suffixLength,
              Nat.lt_succ_self _⟩)
          ⟨base.1.val, by
            change
              base.1.val <
                base.1.val + suffixLength + 1
            omega⟩⟩ :
        G.BoundedStoppedHistory fuel) =
        base
    rw [
      G.boundedHistoryPrefix_endpoint_eq,
      G.boundedHistoryPrefix_appendHist base.2 suffix hstart
    ]
  · exact
      (G.rootOnlineStoppedPath_sound
        localSelector (le_refl _)
        (G.appendHist base.2 suffix)).2
  · rfl

/-- A first hit at a compatible base remains the selected stopped history in
every fuel prefix that extends that base. -/
theorem selectedStoppedHistory_firstHit_append
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {fuel suffixLength : ℕ}
    (base : G.BoundedStoppedHistory fuel)
    (suffix : G.Hist suffixLength)
    (hstart : suffix.StartsAt base.2.2)
    (hbaseHit :
      G.firstPublicHit? terminal base.2 =
        some (Fin.last base.1.val))
    (hfuel : fuel ≤ base.1.val + suffixLength) :
    G.selectedStoppedHistory
        (G.firstHitStopSelector terminal fuel)
        (G.boundedHistoryPrefix
          (G.appendHist base.2 suffix)
          ⟨fuel, Nat.lt_succ_of_le hfuel⟩) =
      base := by
  let fuelHistory :=
    G.boundedHistoryPrefix
      (G.appendHist base.2 suffix)
      ⟨fuel, Nat.lt_succ_of_le hfuel⟩
  have hbaseLeFuel :
      base.1.val ≤ fuel :=
    Nat.lt_succ_iff.mp base.1.isLt
  have hbasePrefix :
      G.boundedHistoryPrefix fuelHistory
          ⟨base.1.val, Nat.lt_succ_of_le hbaseLeFuel⟩ =
        base.2 := by
    calc
      G.boundedHistoryPrefix fuelHistory
          ⟨base.1.val, Nat.lt_succ_of_le hbaseLeFuel⟩ =
        G.boundedHistoryPrefix
          (G.appendHist base.2 suffix)
          ⟨base.1.val, by omega⟩ := by
            exact
              G.boundedHistoryPrefix_nested
                (G.appendHist base.2 suffix)
                hfuel
                ⟨base.1.val,
                  Nat.lt_succ_of_le hbaseLeFuel⟩
      _ = base.2 :=
        G.boundedHistoryPrefix_appendHist
          base.2 suffix hstart
  have hhitFuel :
      G.firstPublicHit? terminal fuelHistory =
        some
          ⟨base.1.val,
            Nat.lt_succ_of_le hbaseLeFuel⟩ := by
    apply G.firstPublicHit?_of_boundedPrefix
      terminal hbaseLeFuel fuelHistory
      (Fin.last base.1.val)
    simpa only [hbasePrefix] using hbaseHit
  have hselector :
      G.firstHitStopSelector terminal fuel fuelHistory =
        ⟨base.1.val,
          Nat.lt_succ_of_le hbaseLeFuel⟩ := by
    exact
      G.firstHitStopSelector_eq_of_hit
        terminal fuelHistory _ hhitFuel
  rw [
    G.selectedStoppedHistory_eq_of_selector_eq
      (G.firstHitStopSelector terminal fuel)
      fuelHistory _ hselector
  ]
  apply Sigma.ext
  · apply Fin.ext
    rfl
  · exact heq_of_eq hbasePrefix

/-- Compatible suffixes preserve every genuinely occurring first-hit base. -/
theorem firstHitOnlineView_persistent
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    (fuel : ℕ)
    (stopsBeforeFuel :
      ∀ history : G.Hist fuel,
        ∃ stage : Fin (fuel + 1),
          G.firstPublicHit? terminal history = some stage ∧
            stage.val < fuel)
    (base : G.BoundedStoppedHistory fuel)
    (hoccurs :
      G.OnlineStoppedBaseOccurs
        (G.firstHitOnlineView terminal fuel) base)
    {suffixLength : ℕ} (suffix : G.Hist suffixLength)
    (hstart : suffix.StartsAt base.2.2) :
    G.firstHitOnlineView terminal fuel
        (base.1.val + suffixLength)
        (G.appendHist base.2 suffix) =
      some (G.onlineStoppedPathOfAppend base suffix) := by
  by_cases hbaseFuel : base.1.val = fuel
  · unfold OnlineStoppedBaseOccurs at hoccurs
    rw [firstHitOnlineView] at hoccurs
    have hfuelLe : fuel ≤ base.1.val := by omega
    simp only [hfuelLe, ↓reduceDIte,
      Option.some.injEq] at hoccurs
    let fuelHistory :=
      G.boundedHistoryPrefix base.2
        ⟨fuel, Nat.lt_succ_of_le hfuelLe⟩
    obtain ⟨stage, hhit, hstageLt⟩ :=
      stopsBeforeFuel fuelHistory
    have hselector :
        G.firstHitStopSelector terminal fuel fuelHistory =
          stage :=
      G.firstHitStopSelector_eq_of_hit
        terminal fuelHistory stage hhit
    have hbaseEq :=
      congrArg (fun path => path.base.1.val) hoccurs
    change
      (G.firstHitStopSelector terminal fuel
        fuelHistory).val =
        base.1.val at hbaseEq
    rw [hselector] at hbaseEq
    omega
  · have hbaseLtFuel : base.1.val < fuel := by
      have hle := Nat.lt_succ_iff.mp base.1.isLt
      omega
    have hbaseHit :
        G.firstPublicHit? terminal base.2 =
          some (Fin.last base.1.val) := by
      unfold OnlineStoppedBaseOccurs at hoccurs
      rw [firstHitOnlineView] at hoccurs
      simp only [Nat.not_le.mpr hbaseLtFuel,
        ↓reduceDIte] at hoccurs
      split at hoccurs
      next hnone =>
        contradiction
      next selected hselected =>
        simp only [Option.some.injEq] at hoccurs
        have hbaseEq :=
          congrArg (fun path => path.base.1.val) hoccurs
        have hselectedVal :
            selected.val = base.1.val := by
          calc
            selected.val =
                (G.onlineStoppedPathAtFirstHit
                  hbaseLtFuel base.2 selected).base.1.val :=
              (G.onlineStoppedPathAtFirstHit_base_val
                hbaseLtFuel base.2 selected).symm
            _ =
                (G.onlineStoppedPathOfAppend base
                  (G.emptyHist base.2.2)).base.1.val :=
              hbaseEq
            _ = base.1.val := rfl
        have hselectedLast :
            selected = Fin.last base.1.val := by
          apply Fin.ext
          exact hselectedVal
        simpa only [hselectedLast] using hselected
    by_cases htotal :
        base.1.val + suffixLength < fuel
    · have hfullHit :
          G.firstPublicHit? terminal
              (G.appendHist base.2 suffix) =
            some
              ⟨base.1.val, by omega⟩ := by
        apply G.firstPublicHit?_of_boundedPrefix
          terminal (Nat.le_add_right _ _) _
          (Fin.last base.1.val)
        rw [
          G.boundedHistoryPrefix_appendHist
            base.2 suffix hstart
        ]
        exact hbaseHit
      rw [firstHitOnlineView]
      simp only [Nat.not_le.mpr htotal, ↓reduceDIte]
      split
      next hnone =>
        rw [hfullHit] at hnone
        contradiction
      next selected hselected =>
        rw [hfullHit] at hselected
        simp only [Option.some.injEq] at hselected
        subst selected
        exact congrArg some
          (G.onlineStoppedPathAtFirstHit_append
            base suffix hstart htotal)
    · have hfuelTotal :
          fuel ≤ base.1.val + suffixLength := by
        omega
      have hselected :=
        G.selectedStoppedHistory_firstHit_append
          terminal base suffix hstart hbaseHit hfuelTotal
      rw [firstHitOnlineView]
      simp only [hfuelTotal, ↓reduceDIte,
        Option.some.injEq]
      exact
        G.rootOnlineStoppedPath_append_of_selected_base
          (G.firstHitStopSelector terminal fuel)
          base suffix hfuelTotal hselected

/-- Every base returned by the online first-hit view occurs at its own
stopping history. -/
theorem firstHitOnlineView_returned_base_occurs
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {fuel time : ℕ} (history : G.Hist time)
    (path : G.OnlineStoppedPath fuel time)
    (hview :
      G.firstHitOnlineView terminal fuel time history =
        some path) :
    G.OnlineStoppedBaseOccurs
      (G.firstHitOnlineView terminal fuel) path.base := by
  unfold firstHitOnlineView at hview
  split at hview
  next htime =>
    simp only [Option.some.injEq] at hview
    subst path
    let fuelHistory :=
      G.boundedHistoryPrefix history
        ⟨fuel, Nat.lt_succ_of_le htime⟩
    have hoccurs :=
      G.selectedFirstHitPrefix_occurs
        terminal fuelHistory
    simpa [rootOnlineStoppedPathOfHistory,
      rootStoppedPathOfHistory, fuelHistory] using hoccurs
  next htime =>
    split at hview
    next hnone =>
      contradiction
    next stage hhit =>
      simp only [Option.some.injEq] at hview
      subst path
      have htimeLt : time < fuel :=
        Nat.lt_of_not_ge htime
      have hrestricted :=
        G.firstPublicHit?_boundedPrefix_eq_last
          terminal history stage hhit
      unfold OnlineStoppedBaseOccurs
      rw [G.onlineStoppedPathAtFirstHit_base]
      change
        G.firstHitOnlineView terminal fuel stage.val
            (G.boundedHistoryPrefix history stage) =
          some
            (G.onlineStoppedPathOfAppend
              (⟨⟨stage.val, by omega⟩,
                G.boundedHistoryPrefix history stage⟩ :
                G.BoundedStoppedHistory fuel)
              (G.emptyHist
                (G.boundedHistoryPrefix history stage).2))
      rw [firstHitOnlineView]
      have hstageLt : stage.val < fuel := by
        exact lt_of_le_of_lt
          (Nat.lt_succ_iff.mp stage.isLt) htimeLt
      simp only [Nat.not_le.mpr hstageLt,
        ↓reduceDIte]
      split
      next hnone =>
        rw [hrestricted] at hnone
        contradiction
      next selected hselected =>
        rw [hrestricted] at hselected
        simp only [Option.some.injEq] at hselected
        subst selected
        have hlastPath :=
          G.onlineStoppedPathAtFirstHit_last
            hstageLt
            (G.boundedHistoryPrefix history stage)
        simpa only using congrArg some hlastPath

/-- Every path returned by the first-hit view reconstructs the history and
has a suffix rooted at its stopped state. -/
theorem firstHitOnlineView_returned_sound
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    {fuel time : ℕ} (history : G.Hist time)
    (path : G.OnlineStoppedPath fuel time)
    (hview :
      G.firstHitOnlineView terminal fuel time history =
        some path) :
    path.suffix.StartsAt path.base.2.2 ∧
      cast (congrArg G.Hist path.length_eq)
          (G.appendHist path.base.2 path.suffix) =
        history := by
  unfold firstHitOnlineView at hview
  split at hview
  next htime =>
    simp only [Option.some.injEq] at hview
    subst path
    exact
      G.rootOnlineStoppedPath_sound
        (G.firstHitStopSelector terminal fuel)
        htime history
  next htime =>
    split at hview
    next hnone =>
      contradiction
    next stage hhit =>
      simp only [Option.some.injEq] at hview
      subst path
      let localSelector :
          G.BoundedPublicStopSelector time :=
        fun _ => stage
      exact
        G.rootOnlineStoppedPath_sound
          localSelector (le_refl time) history

/-- A public-prefix first-hit region guaranteed to be reached strictly before
the fixed fuel supplies a complete repaired online stopping rule.

The strictness hypothesis is intentional: it avoids conflating a genuine
first hit with the selector's mandatory endpoint fallback. -/
def onlineCausalBoundedStoppingRuleOfFirstHit
    (terminal : ∀ time, G.Hist time → Prop)
    [∀ time, DecidablePred (terminal time)]
    (fuel : ℕ)
    (stopsBeforeFuel :
      ∀ history : G.Hist fuel,
        ∃ stage : Fin (fuel + 1),
          G.firstPublicHit? terminal history = some stage ∧
            stage.val < fuel) :
    G.OnlineCausalBoundedStoppingRule fuel where
  selector := G.firstHitStopSelector terminal fuel
  causal := G.firstHitStopSelector_causal terminal fuel
  view := G.firstHitOnlineView terminal fuel
  reconstructs := by
    intro time history path hview
    exact
      G.firstHitOnlineView_returned_sound
        terminal history path hview
  base_occurs := by
    intro time history path hview
    exact
      G.firstHitOnlineView_returned_base_occurs
        terminal history path hview
  persistent := by
    intro base hoccurs suffixLength suffix hstart
    exact
      G.firstHitOnlineView_persistent
        terminal fuel stopsBeforeFuel base hoccurs
        suffix hstart
  complete := by
    intro time htime history
    simp [firstHitOnlineView, htime]

end StochasticGame
end GameTheory
