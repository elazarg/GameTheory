/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicRootHorizonStoppedAccounting
import GameTheory.Concepts.Stochastic.PublicTerminalChildLawTransfer

/-!
# Causal dynamic terminal-child dispatch

An online stopping view reads only the current public history.  Before it
returns a stopped base, the dispatcher follows a selection profile; after it
returns a base and suffix, the dispatcher follows the corresponding child
profile.

The online API requires returned paths to reconstruct their histories and
persists only genuinely occurring bases along suffixes rooted at the stopped
state.  The assembled dispatcher therefore agrees with a child on its
reachable suffix cone; a canonical restriction fills malformed off-path
histories.  The remaining probabilistic obligation is isolated as a
joint-law factorization: the dependent stopped-base/suffix decomposition of
the actual root law must equal the conditional law from
`PublicRootHorizonStoppedAccounting`.
-/

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}

/-- A stopped base together with its suffix inside a current history of
length `time`.  The local suffix length is stored explicitly so child
profiles are never applied through a dependent cast. -/
structure OnlineStoppedPath (G : StochasticGame ι)
    (fuel time : ℕ) where
  base : G.BoundedStoppedHistory fuel
  suffixLength : ℕ
  suffix : G.Hist suffixLength
  length_eq : base.1.val + suffixLength = time

/-- The canonical online path represented by an appended base and suffix. -/
def onlineStoppedPathOfAppend {fuel suffixLength : ℕ}
    (base : G.BoundedStoppedHistory fuel)
    (suffix : G.Hist suffixLength) :
    G.OnlineStoppedPath fuel (base.1.val + suffixLength) where
  base := base
  suffixLength := suffixLength
  suffix := suffix
  length_eq := rfl

/-- Extract the suffix following a bounded length from a longer root
history. -/
def boundedHistorySuffix {total : ℕ} (history : G.Hist total)
    (length : Fin (total + 1)) :
    G.Hist (total - length.val) :=
  (fun index =>
    history.1 ⟨length.val + index.val, by
      have hindex : index.val < total - length.val := index.isLt
      omega⟩,
    history.2)

/-- Decompose a root history at the stopped base selected from its fuel
prefix. -/
def rootStoppedPathOfHistory {fuel total : ℕ}
    (selector : G.BoundedPublicStopSelector fuel)
    (hfuel : fuel ≤ total) (history : G.Hist total) :
    G.RootHorizonStoppedSuffix fuel total :=
  let fuelLength : Fin (total + 1) :=
    ⟨fuel, Nat.lt_succ_of_le hfuel⟩
  let fuelHistory := G.boundedHistoryPrefix history fuelLength
  let base := G.selectedStoppedHistory selector fuelHistory
  let stopLength : Fin (total + 1) :=
    ⟨base.1, Nat.lt_succ_of_le
      (G.stoppedLength_le_rootHorizon hfuel base)⟩
  ⟨base, G.boundedHistorySuffix history stopLength⟩

/-- The canonical selected root decomposition, packaged as an online view. -/
def rootOnlineStoppedPathOfHistory {fuel time : ℕ}
    (selector : G.BoundedPublicStopSelector fuel)
    (htime : fuel ≤ time) (history : G.Hist time) :
    G.OnlineStoppedPath fuel time :=
  let path :=
    G.rootStoppedPathOfHistory selector htime history
  {
    base := path.1
    suffixLength := time - path.1.1.val
    suffix := path.2
    length_eq :=
      Nat.add_sub_of_le
        (G.stoppedLength_le_rootHorizon htime path.1)
  }

/-- The canonical occurrence of a stopped base at its own stopping time. -/
def OnlineStoppedBaseOccurs {fuel : ℕ}
    (view :
      (time : ℕ) → G.Hist time →
        Option (G.OnlineStoppedPath fuel time))
    (base : G.BoundedStoppedHistory fuel) : Prop :=
  view base.1.val base.2 =
    some
      (G.onlineStoppedPathOfAppend base
        (G.emptyHist base.2.2))

/-- Sound online data for a bounded causal stopping rule.

Every returned path reconstructs the history it describes and has a suffix
genuinely rooted at the stopped state.  A stopped base must occur at its own
history before persistence can be used, and persistence is required only for
compatible suffix histories.  `complete` fixes the view after the fuel to the
canonical decomposition used by the stopped-suffix laws.

These restrictions are essential.  Quantifying persistence over arbitrary
bases and malformed suffixes makes the API inconsistent because one history
admits many raw `appendHist` decompositions. -/
structure OnlineCausalBoundedStoppingRule (G : StochasticGame ι)
    (fuel : ℕ) where
  selector : G.BoundedPublicStopSelector fuel
  causal : G.IsCausalBoundedStopSelector selector
  view :
    (time : ℕ) → G.Hist time →
      Option (G.OnlineStoppedPath fuel time)
  reconstructs :
    ∀ time (history : G.Hist time) path,
      view time history = some path →
        path.suffix.StartsAt path.base.2.2 ∧
          cast (congrArg G.Hist path.length_eq)
              (G.appendHist path.base.2 path.suffix) =
            history
  base_occurs :
    ∀ time (history : G.Hist time) path,
      view time history = some path →
        G.OnlineStoppedBaseOccurs view path.base
  persistent :
    ∀ (base : G.BoundedStoppedHistory fuel),
      G.OnlineStoppedBaseOccurs view base →
      ∀ {suffixLength : ℕ} (suffix : G.Hist suffixLength),
      suffix.StartsAt base.2.2 →
      view (base.1.val + suffixLength)
          (G.appendHist base.2 suffix) =
        some (G.onlineStoppedPathOfAppend base suffix)
  complete :
    ∀ time (htime : fuel ≤ time) (history : G.Hist time),
      view time history =
        some
          (G.rootOnlineStoppedPathOfHistory
            selector htime history)

/-- The dynamic dispatcher: selection before the online stopping view
returns a branch, and the selected child thereafter. -/
def causalTerminalChildDispatcher {fuel : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile) :
    G.BehaviorProfile :=
  fun who time history =>
    match rule.view time history with
    | none => selection who time history
    | some path =>
        child path.base who path.suffixLength path.suffix

/-- On a genuinely occurring stopped branch and a compatible suffix, the
dynamic dispatcher is exactly the selected child's strategy. -/
theorem causalTerminalChildDispatcher_appendHist_of_occurs
    {fuel suffixLength : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel)
    (hoccurs : G.OnlineStoppedBaseOccurs rule.view base)
    (suffix : G.Hist suffixLength)
    (hstart : suffix.StartsAt base.2.2) (who : ι) :
    G.causalTerminalChildDispatcher rule selection child who
        (base.1.val + suffixLength)
        (G.appendHist base.2 suffix) =
      child base who suffixLength suffix := by
  unfold causalTerminalChildDispatcher
  rw [rule.persistent base hoccurs suffix hstart]
  rfl

/-- Canonical off-path completion of one stopped child.

It is definitionally the restriction of the assembled root dispatcher.
Agreement with the intended child is asserted only on compatible suffixes
and only when the stopped base genuinely occurs. -/
def canonicalCausalStoppedChildProfile
    {fuel : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel) :
    G.BehaviorProfile :=
  G.afterHistoryProfile
    (G.causalTerminalChildDispatcher rule selection child) base.2

@[simp] theorem afterHistoryProfile_causalTerminalChildDispatcher_canonical
    {fuel : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel) :
    G.afterHistoryProfile
        (G.causalTerminalChildDispatcher rule selection child) base.2 =
      G.canonicalCausalStoppedChildProfile
        rule selection child base :=
  rfl

/-- Canonical completion preserves the intended child on every genuine
suffix of an actually occurring stopped base. -/
theorem canonicalCausalStoppedChildProfile_apply_of_startsAt
    {fuel suffixLength : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel)
    (hoccurs : G.OnlineStoppedBaseOccurs rule.view base)
    (suffix : G.Hist suffixLength)
    (hstart : suffix.StartsAt base.2.2) (who : ι) :
    G.canonicalCausalStoppedChildProfile
        rule selection child base who suffixLength suffix =
      child base who suffixLength suffix := by
  exact G.causalTerminalChildDispatcher_appendHist_of_occurs
    rule selection child base hoccurs suffix hstart who

/-- The canonical completion and intended child induce identical play from
an actually occurring stopped state. -/
theorem profilesAgreeOnStartsAt_canonicalCausalStoppedChildProfile
    {fuel : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel)
    (hoccurs : G.OnlineStoppedBaseOccurs rule.view base) :
    G.ProfilesAgreeOnStartsAt
      (G.canonicalCausalStoppedChildProfile
        rule selection child base)
      (child base) base.2.2 := by
  intro who suffixLength suffix hstart
  exact G.canonicalCausalStoppedChildProfile_apply_of_startsAt
    rule selection child base hoccurs suffix hstart who

theorem expectedHistoryValue_canonicalCausalStoppedChildProfile
    [Fintype ι] {fuel : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel)
    (hoccurs : G.OnlineStoppedBaseOccurs rule.view base)
    (potential : G.HistoryPotential) (length : ℕ) :
    G.expectedHistoryValue
        (G.canonicalCausalStoppedChildProfile
          rule selection child base)
        base.2.2 potential length =
      G.expectedHistoryValue
        (child base) base.2.2 potential length :=
  G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
    (G.profilesAgreeOnStartsAt_canonicalCausalStoppedChildProfile
      rule selection child base hoccurs)
    potential length

theorem expectedStagePayoff_canonicalCausalStoppedChildProfile
    [Fintype ι] {fuel : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel)
    (hoccurs : G.OnlineStoppedBaseOccurs rule.view base)
    (length : ℕ) (who : ι) :
    G.expectedStagePayoff
        (G.canonicalCausalStoppedChildProfile
          rule selection child base)
        base.2.2 length who =
      G.expectedStagePayoff
        (child base) base.2.2 length who :=
  G.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
    (G.profilesAgreeOnStartsAt_canonicalCausalStoppedChildProfile
      rule selection child base hoccurs)
    length who

theorem expectedHistoryValue_update_canonicalCausalStoppedChildProfile
    [Fintype ι] [DecidableEq ι] {fuel : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel)
    (hoccurs : G.OnlineStoppedBaseOccurs rule.view base)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (potential : G.HistoryPotential) (length : ℕ) :
    G.expectedHistoryValue
        (Function.update
          (G.canonicalCausalStoppedChildProfile
            rule selection child base)
          who (G.afterHistoryStrategy deviation base.2))
        base.2.2 potential length =
      G.expectedHistoryValue
        (Function.update (child base) who
          (G.afterHistoryStrategy deviation base.2))
        base.2.2 potential length :=
  G.expectedHistoryValue_eq_of_profilesAgreeOnStartsAt
    ((G.profilesAgreeOnStartsAt_canonicalCausalStoppedChildProfile
      rule selection child base hoccurs).update
      who (G.afterHistoryStrategy deviation base.2))
    potential length

theorem expectedStagePayoff_update_canonicalCausalStoppedChildProfile
    [Fintype ι] [DecidableEq ι] {fuel : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel)
    (hoccurs : G.OnlineStoppedBaseOccurs rule.view base)
    (who : ι) (deviation : G.BehaviorStrategy who)
    (length : ℕ) :
    G.expectedStagePayoff
        (Function.update
          (G.canonicalCausalStoppedChildProfile
            rule selection child base)
          who (G.afterHistoryStrategy deviation base.2))
        base.2.2 length who =
      G.expectedStagePayoff
        (Function.update (child base) who
          (G.afterHistoryStrategy deviation base.2))
        base.2.2 length who :=
  G.expectedStagePayoff_eq_of_profilesAgreeOnStartsAt
    ((G.profilesAgreeOnStartsAt_canonicalCausalStoppedChildProfile
      rule selection child base hoccurs).update
      who (G.afterHistoryStrategy deviation base.2))
    length who

/-- Every base selected from a full fuel history genuinely occurs in the
online view. -/
theorem OnlineCausalBoundedStoppingRule.selectedStoppedHistory_occurs
    {fuel : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (history : G.Hist fuel) :
    G.OnlineStoppedBaseOccurs rule.view
      (G.selectedStoppedHistory rule.selector history) := by
  have hview :=
    rule.complete fuel (le_refl fuel) history
  have hoccurs :=
    rule.base_occurs fuel history
      (G.rootOnlineStoppedPathOfHistory
        rule.selector (le_refl fuel) history)
      hview
  have hprefix :
      G.boundedHistoryPrefix history
          ⟨fuel, Nat.lt_succ_self fuel⟩ =
        history := by
    apply Prod.ext
    · funext index
      rfl
    · simp [boundedHistoryPrefix]
  simpa [rootOnlineStoppedPathOfHistory,
    rootStoppedPathOfHistory, hprefix] using hoccurs

/-- Every base in the stopped-history law is an actually occurring online
base. -/
theorem OnlineCausalBoundedStoppingRule.occurs_of_mem_stoppedHistoryLaw
    [Fintype ι] {fuel : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (profile : G.BehaviorProfile) (initial : G.State)
    (base : G.BoundedStoppedHistory fuel)
    (hbase :
      base ∈
        (G.stoppedHistoryLaw
          profile initial rule.selector).support) :
    G.OnlineStoppedBaseOccurs rule.view base := by
  rw [stoppedHistoryLaw, PMF.mem_support_map_iff] at hbase
  obtain ⟨history, _history_support, rfl⟩ := hbase
  exact rule.selectedStoppedHistory_occurs history

/-- Exact dependent joint-law assertion left to a concrete online
dispatcher.

The first field says that decomposing and reconstructing actual root
histories loses no law.  The second is the strong-Markov/dispatcher
factorization of the actual dependent pair law.  These are more local and
strictly more informative than merely postulating the final root-law
equality. -/
structure CausalDispatcherJointLawAt
    [Fintype ι] {fuel total : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hfuel : fuel ≤ total) : Prop where
  reconstruct_actual :
    ((G.histDist profile initial total).map
        (G.rootStoppedPathOfHistory selector hfuel)).map
        (G.rootHistoryOfStoppedSuffix hfuel) =
      G.histDist profile initial total
  factorization :
    (G.histDist profile initial total).map
        (G.rootStoppedPathOfHistory selector hfuel) =
      G.rootHorizonStoppedSuffixLaw profile initial selector total

/-- Joint-law factorization for the concrete dynamic dispatcher supplies the
root stopped-suffix disintegration interface. -/
theorem OnlineCausalBoundedStoppingRule.toRootStoppedSuffixDisintegration
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel total : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (initial : G.State) (hfuel : fuel ≤ total)
    (joint :
      CausalDispatcherJointLawAt
        (G.causalTerminalChildDispatcher rule selection child)
        initial rule.selector hfuel) :
    G.IsRootStoppedSuffixDisintegration
      (G.causalTerminalChildDispatcher rule selection child)
      initial rule.selector hfuel where
  causal := rule.causal
  law_eq := by
    let profile :=
      G.causalTerminalChildDispatcher rule selection child
    calc
      G.histDist profile initial total =
          ((G.histDist profile initial total).map
            (G.rootStoppedPathOfHistory rule.selector hfuel)).map
            (G.rootHistoryOfStoppedSuffix hfuel) :=
        joint.reconstruct_actual.symm
      _ =
          (G.rootHorizonStoppedSuffixLaw profile initial rule.selector
            total).map
            (G.rootHistoryOfStoppedSuffix hfuel) := by
        rw [joint.factorization]
      _ =
          G.reconstructedRootHistoryLaw profile initial rule.selector
            hfuel := rfl

end StochasticGame
end GameTheory
