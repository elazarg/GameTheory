/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.CausalTerminalChildDispatcher
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.FixedPrefixAccounting
import GameTheory.Concepts.Stochastic.UniformEquilibrium.Certificates.Public.TerminalChildLawTransfer

/-!
# Finite causal stopping factorization

This file records the exact-event consequence of the bounded stopping-time
predicate.  It is the finite combinatorial input to the strong stopping
factorization of public-history laws.
-/

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

/-- Primitive finite event-ratio lemma.  If the mass on one projection
fiber factors as the fiber mass times a candidate conditional law, and the
candidate is supported on that fiber, then `condOn` is that candidate. -/
theorem condOn_eq_of_apply_eq_mul
    {α β : Type} [Finite α] [Finite β]
    (joint candidate : PMF α) (proj : α → β) (base : β)
    (hbase : joint.map proj base ≠ 0)
    (hcandidate :
      ∀ value, proj value ≠ base → candidate value = 0)
    (hmass :
      ∀ value, proj value = base →
        joint value = joint.map proj base * candidate value) :
    Math.ProbabilityMassFunction.condOn joint proj base =
      candidate := by
  apply PMF.ext
  intro value
  rw [Math.ProbabilityMassFunction.condOn_apply
    joint proj base value hbase]
  by_cases hvalue : proj value = base
  · rw [if_pos hvalue, hmass value hvalue]
    have hbaseTop : joint.map proj base ≠ ⊤ :=
      PMF.apply_ne_top (joint.map proj) base
    calc
      (joint.map proj base * candidate value) /
          joint.map proj base =
          candidate value *
            (joint.map proj base * (joint.map proj base)⁻¹) := by
        simp only [div_eq_mul_inv]
        ac_rfl
      _ = candidate value := by
        rw [ENNReal.mul_inv_cancel hbase hbaseTop, mul_one]
  · rw [if_neg hvalue, hcandidate value hvalue]

/-- Projecting a deterministic-horizon history law to its fixed prefix
recovers the shorter history law. -/
theorem histDist_add_map_terminalPrefix
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State)
    (prefixLength suffixLength : ℕ) :
    (G.histDist profile initial (prefixLength + suffixLength)).map
        G.terminalPrefix =
      G.histDist profile initial prefixLength := by
  rw [G.histDist_add_eq_bind_histDistAfter, PMF.map_bind]
  have hkernel : (fun base : G.Hist prefixLength =>
      (G.histDistAfter profile base suffixLength).map
        G.terminalPrefix) =
      (fun base => PMF.pure base) := by
    funext base
    unfold histDistAfter
    rw [PMF.map_comp]
    let localLaw :=
      G.histDist (G.afterHistoryProfile profile base) base.2
        suffixLength
    calc
      localLaw.map
          (G.terminalPrefix ∘ G.appendHist base) =
          localLaw.map (fun _suffix => base) := by
        apply pmf_map_eq_of_eq_on_support
        intro suffix hsuffix
        exact G.terminalPrefix_appendHist base suffix
          (G.startsAt_of_mem_support_histDist
            (G.afterHistoryProfile profile base) base.2
            suffixLength suffix hsuffix)
      _ = PMF.pure base := PMF.map_const localLaw base
  rw [hkernel, PMF.bind_pure]

/-- The bounded-prefix and fixed-prefix presentations agree when the total
horizon is displayed as a sum. -/
theorem boundedHistoryPrefix_add_eq_terminalPrefix
    {prefixLength suffixLength : ℕ}
    (history : G.Hist (prefixLength + suffixLength)) :
    G.boundedHistoryPrefix history
        ⟨prefixLength, Nat.lt_succ_of_le
          (Nat.le_add_right prefixLength suffixLength)⟩ =
      G.terminalPrefix history := by
  apply Prod.ext
  · funext index
    rfl
  · cases suffixLength with
    | zero =>
        simp [boundedHistoryPrefix, terminalPrefix]
    | succ suffixLength =>
        simp only [boundedHistoryPrefix, terminalPrefix,
          Nat.lt_add_of_pos_right (Nat.zero_lt_succ _),
          ↓reduceDIte]
        congr 2

/-- The stopped-base marginal of the actual root decomposition is the
selected stopped-history law.  Causality is not needed for this marginal. -/
theorem rootStoppedPath_base_marginal_add
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel suffixLength : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel) :
    ((G.histDist profile initial (fuel + suffixLength)).map
        (G.rootStoppedPathOfHistory selector
          (Nat.le_add_right fuel suffixLength))).map Sigma.fst =
      G.stoppedHistoryLaw profile initial selector := by
  rw [PMF.map_comp]
  have hdecompose :
      Sigma.fst ∘
          G.rootStoppedPathOfHistory selector
            (Nat.le_add_right fuel suffixLength) =
        G.selectedStoppedHistory selector ∘ G.terminalPrefix := by
    funext history
    unfold rootStoppedPathOfHistory
    dsimp only [Function.comp_apply]
    rw [G.boundedHistoryPrefix_add_eq_terminalPrefix]
  rw [hdecompose, ← PMF.map_comp,
    G.histDist_add_map_terminalPrefix]
  rfl

/-- The conditional-kernel form of the finite strong stopping property.
Only supported stopped bases matter. -/
def IsStoppedSuffixConditionalKernelAdd
    [Fintype ι] {fuel suffixLength : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel) : Prop :=
  let joint :=
    (G.histDist profile initial (fuel + suffixLength)).map
      (G.rootStoppedPathOfHistory selector
        (Nat.le_add_right fuel suffixLength))
  ∀ base,
    base ∈ (G.stoppedHistoryLaw profile initial selector).support →
      Math.ProbabilityMassFunction.condOn joint Sigma.fst base =
        (G.histDist (G.afterHistoryProfile profile base.2)
          base.2.2 (fuel + suffixLength - base.1.val)).map
          fun suffix =>
            (⟨base, suffix⟩ :
              G.RootHorizonStoppedSuffix fuel
                (fuel + suffixLength))

/-- The proposed suffix law at one stopped base, tagged back into the common
dependent stopped-path space. -/
def stoppedSuffixCandidateAdd
    [Fintype ι] {fuel suffixLength : ℕ}
    (profile : G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel) :
    PMF (G.RootHorizonStoppedSuffix fuel
      (fuel + suffixLength)) :=
  (G.histDist (G.afterHistoryProfile profile base.2)
    base.2.2 (fuel + suffixLength - base.1.val)).map
    fun suffix =>
      (⟨base, suffix⟩ :
        G.RootHorizonStoppedSuffix fuel
          (fuel + suffixLength))

/-- The tagged candidate has the intended deterministic base marginal. -/
theorem stoppedSuffixCandidateAdd_map_fst
    [Fintype ι] {fuel suffixLength : ℕ}
    (profile : G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel) :
    (G.stoppedSuffixCandidateAdd
        (suffixLength := suffixLength) profile base).map Sigma.fst =
      PMF.pure base := by
  unfold stoppedSuffixCandidateAdd
  rw [PMF.map_comp]
  change
    (G.histDist (G.afterHistoryProfile profile base.2)
      base.2.2 (fuel + suffixLength - base.1.val)).map
        (fun _suffix => base) =
      PMF.pure base
  exact PMF.map_const _ _

/-- The primitive eventwise product identity needed for strong stopping.
It says exactly that every point mass over a supported stopped base is the
base mass times the rebased suffix mass. -/
def IsStoppedSuffixEventRatioAdd
    [Fintype ι] {fuel suffixLength : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel) : Prop :=
  let joint :=
    (G.histDist profile initial (fuel + suffixLength)).map
      (G.rootStoppedPathOfHistory selector
        (Nat.le_add_right fuel suffixLength))
  ∀ base,
    base ∈ (G.stoppedHistoryLaw profile initial selector).support →
      ∀ path, path.1 = base →
        joint path =
          G.stoppedHistoryLaw profile initial selector base *
            G.stoppedSuffixCandidateAdd
              (suffixLength := suffixLength) profile base path

/-- The event-ratio identity implies the support-local conditional kernel
identity. -/
theorem stoppedSuffixConditionalKernelAdd_of_eventRatio
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel suffixLength : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hratio :
      G.IsStoppedSuffixEventRatioAdd
        (suffixLength := suffixLength) profile initial selector) :
    G.IsStoppedSuffixConditionalKernelAdd
      (suffixLength := suffixLength) profile initial selector := by
  let joint :=
    (G.histDist profile initial (fuel + suffixLength)).map
      (G.rootStoppedPathOfHistory selector
        (Nat.le_add_right fuel suffixLength))
  intro base hbase
  let candidate :=
    G.stoppedSuffixCandidateAdd
      (suffixLength := suffixLength) profile base
  have hbaseMarginal :
      joint.map Sigma.fst =
        G.stoppedHistoryLaw profile initial selector :=
    G.rootStoppedPath_base_marginal_add
      profile initial selector
  have hbaseNonzero : joint.map Sigma.fst base ≠ 0 := by
    rw [hbaseMarginal]
    simpa [PMF.mem_support_iff] using hbase
  have hcandidate :
      ∀ path, path.1 ≠ base → candidate path = 0 := by
    intro path hpath
    apply Math.ProbabilityMassFunction.eq_zero_of_pushforward_eq_zero
      candidate Sigma.fst (b := path.1)
    · unfold Math.ProbabilityMassFunction.pushforward
      rw [show candidate.map Sigma.fst = PMF.pure base from
          G.stoppedSuffixCandidateAdd_map_fst
            (suffixLength := suffixLength) profile base]
      simp [hpath]
    · rfl
  have hmass :
      ∀ path, path.1 = base →
        joint path = joint.map Sigma.fst base * candidate path := by
    intro path hpath
    rw [hbaseMarginal]
    exact hratio base hbase path hpath
  exact condOn_eq_of_apply_eq_mul
    joint candidate Sigma.fst base hbaseNonzero hcandidate hmass

/-- Conditional strong stopping kernels imply the full stopped-suffix
factorization. -/
theorem rootStoppedPath_factorization_add_of_conditionalKernel
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel suffixLength : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hkernel :
      G.IsStoppedSuffixConditionalKernelAdd
        (suffixLength := suffixLength) profile initial selector) :
    (G.histDist profile initial (fuel + suffixLength)).map
        (G.rootStoppedPathOfHistory selector
          (Nat.le_add_right fuel suffixLength)) =
      G.rootHorizonStoppedSuffixLaw profile initial selector
        (fuel + suffixLength) := by
  let joint :=
    (G.histDist profile initial (fuel + suffixLength)).map
      (G.rootStoppedPathOfHistory selector
        (Nat.le_add_right fuel suffixLength))
  calc
    joint =
        (joint.map Sigma.fst).bind fun base =>
          Math.ProbabilityMassFunction.condOn
            joint Sigma.fst base :=
      Math.ProbabilityMassFunction.bind_pushforward_condOn_pure
        joint Sigma.fst
    _ =
        (G.stoppedHistoryLaw profile initial selector).bind
          fun base =>
            (G.histDist (G.afterHistoryProfile profile base.2)
              base.2.2
              (fuel + suffixLength - base.1.val)).map
              fun suffix =>
                (⟨base, suffix⟩ :
                  G.RootHorizonStoppedSuffix fuel
                    (fuel + suffixLength)) := by
      rw [show joint.map Sigma.fst =
          G.stoppedHistoryLaw profile initial selector from
        G.rootStoppedPath_base_marginal_add
          profile initial selector]
      apply Math.ProbabilityMassFunction.bind_congr_on_support
      intro base hbase
      exact hkernel base hbase
    _ =
        G.rootHorizonStoppedSuffixLaw profile initial selector
          (fuel + suffixLength) := rfl

/-- The primitive event-ratio identity is sufficient for the full stopped
suffix PMF factorization at additive root horizons. -/
theorem rootStoppedPath_factorization_add_of_eventRatio
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel suffixLength : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hratio :
      G.IsStoppedSuffixEventRatioAdd
        (suffixLength := suffixLength) profile initial selector) :
    (G.histDist profile initial (fuel + suffixLength)).map
        (G.rootStoppedPathOfHistory selector
          (Nat.le_add_right fuel suffixLength)) =
      G.rootHorizonStoppedSuffixLaw profile initial selector
        (fuel + suffixLength) := by
  apply G.rootStoppedPath_factorization_add_of_conditionalKernel
  exact G.stoppedSuffixConditionalKernelAdd_of_eventRatio
    profile initial selector hratio

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

/-- Eventwise product masses supply the complete joint-law interface. -/
theorem causalDispatcherJointLawAt_add_of_eventRatio
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel suffixLength : ℕ}
    (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hratio :
      G.IsStoppedSuffixEventRatioAdd
        (suffixLength := suffixLength) profile initial selector) :
    G.CausalDispatcherJointLawAt profile initial selector
      (Nat.le_add_right fuel suffixLength) :=
  (G.causalDispatcherJointLawAt_iff_factorization
    profile initial selector
      (Nat.le_add_right fuel suffixLength)).2
    (G.rootStoppedPath_factorization_add_of_eventRatio
      profile initial selector hratio)

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
