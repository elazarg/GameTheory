/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicRootHorizonStoppedAccounting

/-!
# Causal dynamic terminal-child dispatch

An online stopping view reads only the current public history.  Before it
returns a stopped base, the dispatcher follows a selection profile; after it
returns a base and suffix, the dispatcher follows the corresponding child
profile.

The online API includes persistence on every appended branch.  This gives an
exact suffix-rebasing theorem for the assembled dispatcher.  The remaining
probabilistic obligation is isolated as a joint-law factorization: the
dependent stopped-base/suffix decomposition of the actual root law must equal
the conditional law from `PublicRootHorizonStoppedAccounting`.  From that
strictly stronger, typed statement this file proves the required
`IsRootStoppedSuffixDisintegration.law_eq`.
-/

set_option autoImplicit false

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

/-- Minimal online data for a bounded causal stopping rule.

`view` is evaluated from the current history only.  `persistent` says that
once a stopped base is present, every appended continuation keeps that base
and exposes the appended suffix.  `selector_at_fuel` connects the online view
to the fixed-fuel selector used by the stopped-history laws. -/
structure OnlineCausalBoundedStoppingRule (G : StochasticGame ι)
    (fuel : ℕ) where
  selector : G.BoundedPublicStopSelector fuel
  causal : G.IsCausalBoundedStopSelector selector
  view :
    (time : ℕ) → G.Hist time →
      Option (G.OnlineStoppedPath fuel time)
  persistent :
    ∀ (base : G.BoundedStoppedHistory fuel)
      {suffixLength : ℕ} (suffix : G.Hist suffixLength),
      view (base.1.val + suffixLength)
          (G.appendHist base.2 suffix) =
        some (G.onlineStoppedPathOfAppend base suffix)
  selector_at_fuel :
    ∀ history : G.Hist fuel,
      Option.map OnlineStoppedPath.base (view fuel history) =
        some (G.selectedStoppedHistory selector history)

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

/-- On every explicitly appended stopped branch, the dynamic dispatcher is
exactly the selected child's strategy. -/
theorem causalTerminalChildDispatcher_appendHist
    {fuel suffixLength : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel)
    (suffix : G.Hist suffixLength) (who : ι) :
    G.causalTerminalChildDispatcher rule selection child who
        (base.1.val + suffixLength)
        (G.appendHist base.2 suffix) =
      child base who suffixLength suffix := by
  unfold causalTerminalChildDispatcher
  rw [rule.persistent base suffix]
  rfl

/-- Rebasing the assembled dynamic dispatcher after a stopped base recovers
the selected child profile exactly. -/
theorem afterHistoryProfile_causalTerminalChildDispatcher
    {fuel : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel) :
    G.afterHistoryProfile
        (G.causalTerminalChildDispatcher rule selection child) base.2 =
      child base := by
  funext who suffixLength suffix
  exact G.causalTerminalChildDispatcher_appendHist
    rule selection child base suffix who

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
