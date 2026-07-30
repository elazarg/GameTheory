/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicCausalTerminalChildDispatcher
import GameTheory.Concepts.Stochastic.PublicTerminalChildLawTransfer

/-!
# Finite causal stopping factorization

This file records the exact-event consequence of the bounded stopping-time
predicate.  It is the finite combinatorial input to the strong stopping
factorization of public-history laws.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

variable {ι : Type} {G : StochasticGame ι}

/-- Two maps which agree on the support of a PMF have the same image law. -/
theorem pmf_map_eq_of_eq_on_support
    {α β : Type} (law : PMF α) (left right : α → β)
    (heq : ∀ value, value ∈ law.support →
      left value = right value) :
    law.map left = law.map right := by
  rw [← PMF.bind_pure_comp left law,
    ← PMF.bind_pure_comp right law]
  apply Math.ProbabilityMassFunction.bind_congr_on_support
  intro value hvalue
  simpa only [Function.comp_apply] using
    congrArg PMF.pure (heq value hvalue)

/-- Equality of a longer bounded prefix implies equality of every strictly
shorter bounded prefix. -/
theorem boundedHistoryPrefix_eq_of_prefix_eq_of_lt
    {fuel : ℕ} (left right : G.Hist fuel)
    (shorter longer : Fin (fuel + 1))
    (hlt : shorter.val < longer.val)
    (hlonger :
      G.boundedHistoryPrefix left longer =
        G.boundedHistoryPrefix right longer) :
    G.boundedHistoryPrefix left shorter =
      G.boundedHistoryPrefix right shorter := by
  apply Prod.ext
  · funext index
    have hrecords := congrArg Prod.fst hlonger
    exact congrFun hrecords
      ⟨index.val, lt_of_lt_of_le index.isLt (Nat.le_of_lt hlt)⟩
  · have hrecords := congrArg Prod.fst hlonger
    have hshortFuel : shorter.val < fuel :=
      lt_of_lt_of_le hlt (Nat.lt_succ_iff.mp longer.isLt)
    have hindex : shorter.val < longer.val := hlt
    have hat := congrFun hrecords ⟨shorter.val, hindex⟩
    simpa [boundedHistoryPrefix, hshortFuel] using congrArg Prod.fst hat

/-- If two full histories agree through the time selected by the first one,
a causal selector chooses the same time on both histories. -/
theorem IsCausalBoundedStopSelector.eq_of_prefix_eq_selected
    {fuel : ℕ} {selector : G.BoundedPublicStopSelector fuel}
    (hcausal : G.IsCausalBoundedStopSelector selector)
    (left right : G.Hist fuel)
    (hprefix :
      G.boundedHistoryPrefix left (selector left) =
        G.boundedHistoryPrefix right (selector left)) :
    selector right = selector left := by
  apply Fin.ext
  let time := selector left
  have hle : (selector right).val ≤ time.val :=
    (hcausal time left right hprefix).mp (le_refl time.val)
  apply Nat.le_antisymm hle
  by_contra hnot
  have hlt : (selector right).val < time.val := by omega
  have htime : 0 < time.val :=
    lt_of_le_of_lt (Nat.zero_le _) hlt
  let previous : Fin (fuel + 1) :=
    ⟨time.val - 1, by omega⟩
  have hprefixPrevious :
      G.boundedHistoryPrefix left previous =
        G.boundedHistoryPrefix right previous := by
    exact G.boundedHistoryPrefix_eq_of_prefix_eq_of_lt
      left right previous time (by dsimp [previous]; omega) hprefix
  have hleftNot : ¬(selector left).val ≤ previous.val := by
    dsimp [previous, time]
    omega
  have hright : (selector right).val ≤ previous.val := by
    dsimp [previous]
    omega
  exact hleftNot
    ((hcausal previous left right hprefixPrevious).mpr hright)

/-- Exact stopping is already determined by the selected prefix. -/
def IsExactPrefixBoundedStopSelector {fuel : ℕ}
    (selector : G.BoundedPublicStopSelector fuel) : Prop :=
  ∀ left right : G.Hist fuel,
    G.boundedHistoryPrefix left (selector left) =
        G.boundedHistoryPrefix right (selector left) →
      selector right = selector left

/-- The ordinary cumulative-event definition of causality implies exact
selected-prefix determination. -/
theorem IsCausalBoundedStopSelector.exactPrefix
    {fuel : ℕ} {selector : G.BoundedPublicStopSelector fuel}
    (hcausal : G.IsCausalBoundedStopSelector selector) :
    G.IsExactPrefixBoundedStopSelector selector :=
  fun left right hprefix =>
    hcausal.eq_of_prefix_eq_selected left right hprefix

/-- Exact selected-prefix determination is equivalent to the usual finite
stopping-time condition. -/
theorem isExactPrefixBoundedStopSelector_iff_causal
    {fuel : ℕ} {selector : G.BoundedPublicStopSelector fuel} :
    G.IsExactPrefixBoundedStopSelector selector ↔
      G.IsCausalBoundedStopSelector selector := by
  constructor
  · intro hexact time left right hprefix
    constructor
    · intro hleft
      have hselectedPrefix :
          G.boundedHistoryPrefix left (selector left) =
            G.boundedHistoryPrefix right (selector left) := by
        by_cases hlt : (selector left).val < time.val
        · exact G.boundedHistoryPrefix_eq_of_prefix_eq_of_lt
            left right (selector left) time hlt hprefix
        · have heq : selector left = time := by
            apply Fin.ext
            omega
          rw [heq]
          exact hprefix
      rw [hexact left right hselectedPrefix]
      exact hleft
    · intro hright
      have hselectedPrefix :
          G.boundedHistoryPrefix right (selector right) =
            G.boundedHistoryPrefix left (selector right) := by
        by_cases hlt : (selector right).val < time.val
        · exact G.boundedHistoryPrefix_eq_of_prefix_eq_of_lt
            right left (selector right) time hlt hprefix.symm
        · have heq : selector right = time := by
            apply Fin.ext
            omega
          rw [heq]
          exact hprefix.symm
      rw [hexact right left hselectedPrefix]
      exact hright
  · exact IsCausalBoundedStopSelector.exactPrefix

/-- Remove the first stage from a bounded selector.  A stop at time zero is
sent to zero; otherwise this is ordinary predecessor. -/
def dropFirstStopSelector {fuel : ℕ}
    (selector : G.BoundedPublicStopSelector (fuel + 1))
    (first : G.State × G.JointAct) :
    G.BoundedPublicStopSelector fuel :=
  fun tail =>
    ⟨(selector (G.consHist first tail)).val - 1, by
      have hle :
          (selector (G.consHist first tail)).val ≤ fuel + 1 :=
        Nat.lt_succ_iff.mp (selector (G.consHist first tail)).isLt
      omega⟩

/-- Prefixing one stage commutes with taking a bounded prefix one stage
later. -/
theorem boundedHistoryPrefix_consHist_succ
    {fuel : ℕ} (first : G.State × G.JointAct)
    (tail : G.Hist fuel) (time : Fin (fuel + 1)) :
    G.boundedHistoryPrefix (G.consHist first tail)
        ⟨time.val + 1, by omega⟩ =
      G.consHist first (G.boundedHistoryPrefix tail time) := by
  apply Prod.ext
  · funext index
    cases index using Fin.cases with
    | zero =>
        simp [boundedHistoryPrefix, consHist]
    | succ index =>
        simp [boundedHistoryPrefix, consHist]
  · by_cases hstrict : time.val < fuel
    · simp only [boundedHistoryPrefix, hstrict, ↓reduceDIte, consHist]
      let shortTime : Fin fuel := ⟨time.val, hstrict⟩
      have hindex :
          (⟨time.val + 1, by omega⟩ : Fin (fuel + 1)) =
            Fin.succ shortTime := by
        apply Fin.ext
        rfl
      rw [dif_pos (by omega)]
      rw [hindex, Fin.cons_succ]
    · have htime : time.val = fuel := by omega
      have htimeFin : time = Fin.last fuel := by
        apply Fin.ext
        simpa using htime
      subst time
      simp [boundedHistoryPrefix, consHist]

/-- If the original selector never stops immediately on histories beginning
with `first.1`, its one-stage residual selector is causal. -/
theorem IsCausalBoundedStopSelector.dropFirst
    {fuel : ℕ}
    {selector : G.BoundedPublicStopSelector (fuel + 1)}
    (hcausal : G.IsCausalBoundedStopSelector selector)
    (first : G.State × G.JointAct)
    (hpositive :
      ∀ tail : G.Hist fuel,
        0 < (selector (G.consHist first tail)).val) :
    G.IsCausalBoundedStopSelector
      (G.dropFirstStopSelector selector first) := by
  intro time left right hprefix
  let nextTime : Fin (fuel + 2) :=
    ⟨time.val + 1, by omega⟩
  have hprefixed :
      G.boundedHistoryPrefix (G.consHist first left) nextTime =
        G.boundedHistoryPrefix (G.consHist first right) nextTime := by
    simpa [nextTime, G.boundedHistoryPrefix_consHist_succ] using
      congrArg (G.consHist first) hprefix
  have horiginal :=
    hcausal nextTime (G.consHist first left)
      (G.consHist first right) hprefixed
  dsimp [dropFirstStopSelector, nextTime]
  have hleft := hpositive left
  have hright := hpositive right
  constructor
  · intro hresidual
    have horiginalLeft :
        (selector (G.consHist first left)).val ≤ time.val + 1 := by
      omega
    have horiginalRight :
        (selector (G.consHist first right)).val ≤ time.val + 1 :=
      horiginal.mp horiginalLeft
    omega
  · intro hresidual
    have horiginalRight :
        (selector (G.consHist first right)).val ≤ time.val + 1 := by
      omega
    have horiginalLeft :
        (selector (G.consHist first left)).val ≤ time.val + 1 :=
      horiginal.mpr horiginalRight
    omega

/-- Decomposition at the selected bounded prefix is pointwise lossless.
This is purely deterministic and does not use causality. -/
theorem rootHistoryOfStoppedSuffix_rootStoppedPathOfHistory_exact
    {fuel total : ℕ}
    (selector : G.BoundedPublicStopSelector fuel)
    (hfuel : fuel ≤ total) (history : G.Hist total) :
    G.rootHistoryOfStoppedSuffix hfuel
        (G.rootStoppedPathOfHistory selector hfuel history) =
      history := by
  let fuelLength : Fin (total + 1) :=
    ⟨fuel, Nat.lt_succ_of_le hfuel⟩
  let fuelHistory := G.boundedHistoryPrefix history fuelLength
  let selectedLength := selector fuelHistory
  let stopLength : Fin (total + 1) :=
    ⟨selectedLength, Nat.lt_succ_of_le
      (le_trans (Nat.lt_succ_iff.mp selectedLength.isLt) hfuel)⟩
  let base : G.BoundedStoppedHistory fuel :=
    ⟨selectedLength, G.boundedHistoryPrefix history stopLength⟩
  let suffix := G.boundedHistorySuffix history stopLength
  let hlength := G.stoppedLength_le_rootHorizon hfuel base
  let hadd : base.1.val + (total - base.1.val) = total :=
    Nat.add_sub_of_le hlength
  change G.Hist (total - base.1.val) at suffix
  change
    cast (congrArg G.Hist hadd)
        (G.appendHist base.2 suffix) =
      history
  apply eq_of_heq
  have hcast :
      cast (congrArg G.Hist hadd)
          (G.appendHist base.2 suffix) ≍
        G.appendHist base.2 suffix :=
    cast_heq _ _
  have hraw :
      G.appendHist base.2 suffix ≍ history := by
    unfold appendHist
    let records :=
      Fin.append base.2.1 suffix.1
    have records_heq : records ≍ history.1 := by
      apply Function.hfunext (congrArg Fin hadd)
      intro left right hindex
      revert right
      refine Fin.addCases ?_ ?_ left
      · intro prefixIndex right hindex
        have packaged_eq :
            (⟨base.1.val + (total - base.1.val),
                Fin.castAdd (total - base.1.val) prefixIndex⟩ :
              Σ length, Fin length) =
              ⟨total, right⟩ :=
          Sigma.ext hadd hindex
        have value_eq : prefixIndex.val = right.val := by
          simpa using congrArg
            (fun index : Σ length, Fin length => index.2.val)
            packaged_eq
        dsimp [records]
        rw [Fin.append_left]
        unfold base boundedHistoryPrefix
        dsimp only
        apply heq_of_eq
        apply congrArg history.1
        apply Fin.ext
        simpa using value_eq
      · intro suffixIndex right hindex
        have packaged_eq :
            (⟨base.1.val + (total - base.1.val),
                Fin.natAdd base.1.val suffixIndex⟩ :
              Σ length, Fin length) =
              ⟨total, right⟩ :=
          Sigma.ext hadd hindex
        have value_eq :
            base.1.val + suffixIndex.val = right.val := by
          simpa using congrArg
            (fun index : Σ length, Fin length => index.2.val)
            packaged_eq
        dsimp [records]
        rw [Fin.append_right]
        unfold suffix boundedHistorySuffix
        dsimp only
        apply heq_of_eq
        apply congrArg history.1
        apply Fin.ext
        simpa [base, stopLength, selectedLength] using value_eq
    exact HEq.ndrec (motive := fun {recordsType} otherRecords =>
        (records, suffix.2) ≍ (otherRecords, history.2))
      HEq.rfl records_heq
  exact hcast.trans hraw

/-- The reconstruction field of the joint-law interface is automatic for
every selector and every root history law. -/
theorem reconstruct_actual_rootStoppedPath
    [Fintype ι] {fuel total : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hfuel : fuel ≤ total) :
    ((G.histDist profile initial total).map
        (G.rootStoppedPathOfHistory selector hfuel)).map
        (G.rootHistoryOfStoppedSuffix hfuel) =
      G.histDist profile initial total := by
  rw [PMF.map_comp]
  have hfunction :
      G.rootHistoryOfStoppedSuffix hfuel ∘
          G.rootStoppedPathOfHistory selector hfuel =
        id := by
    funext history
    exact
      G.rootHistoryOfStoppedSuffix_rootStoppedPathOfHistory_exact
        selector hfuel history
  rw [hfunction, PMF.map_id]

/-- The joint-law interface has only one probabilistic obligation:
reconstruction is automatic, so it is equivalent to the stopped-suffix
factorization equality itself. -/
theorem causalDispatcherJointLawAt_iff_factorization
    [Fintype ι] {fuel total : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hfuel : fuel ≤ total) :
    G.CausalDispatcherJointLawAt profile initial selector hfuel ↔
      (G.histDist profile initial total).map
          (G.rootStoppedPathOfHistory selector hfuel) =
        G.rootHorizonStoppedSuffixLaw profile initial selector total := by
  constructor
  · exact fun joint => joint.factorization
  · intro factorization
    exact
      { reconstruct_actual :=
          G.reconstruct_actual_rootStoppedPath
            profile initial selector hfuel
        factorization := factorization }

/-- Rebasing at an empty public prefix is the original profile. -/
@[simp] theorem afterHistoryProfile_empty
    (profile : G.BehaviorProfile) (state : G.State) :
    G.afterHistoryProfile profile (G.emptyHist state) = profile := by
  funext who length suffix
  change
    profile who (0 + length)
        (G.appendHist (G.emptyHist state) suffix) =
      profile who length suffix
  have hsigma :
      (⟨0 + length, G.appendHist (G.emptyHist state) suffix⟩ :
        Σ time, G.Hist time) =
        ⟨length, suffix⟩ := by
    apply Sigma.ext (Nat.zero_add length)
    unfold appendHist emptyHist
    let records := Fin.append Fin.elim0 suffix.1
    have records_heq : records ≍ suffix.1 := by
      apply Function.hfunext (congrArg Fin (Nat.zero_add length))
      intro left right hindex
      have packaged_eq :
          (⟨0 + length, left⟩ : Σ time, Fin time) =
            ⟨length, right⟩ :=
        Sigma.ext (Nat.zero_add length) hindex
      have value_eq : left.val = right.val :=
        congrArg (fun index : Σ time, Fin time => index.2.val)
          packaged_eq
      have hleft : left = Fin.natAdd 0 right := by
        apply Fin.ext
        simpa using value_eq
      subst left
      exact heq_of_eq (Fin.append_right Fin.elim0 suffix.1 right)
    exact HEq.ndrec (motive := fun {recordsType} otherRecords =>
        (records, suffix.2) ≍ (otherRecords, suffix.2))
      HEq.rfl records_heq
  exact congrArg
    (fun path : Σ time, G.Hist time =>
      profile who path.1 path.2) hsigma

/-- The only zero-fuel selection returns the entire zero-length history. -/
@[simp] theorem selectedStoppedHistory_zero_const
    (history : G.Hist 0) :
    G.selectedStoppedHistory
        (fun _history : G.Hist 0 => (0 : Fin 1)) history =
      ⟨0, history⟩ := by
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Prod.ext
    · funext index
      exact Fin.elim0 index
    · rfl

end StochasticGame
end GameTheory
