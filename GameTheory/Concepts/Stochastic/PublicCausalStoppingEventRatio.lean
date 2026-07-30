/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PublicBoundedStoppingFactorization

/-!
# Event ratios for causal bounded stopping

This file derives the point-mass product identity at a causal bounded public
stopping time.  It is kept separate from the finite factorization API so the
probabilistic proof can be audited independently.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory
namespace StochasticGame

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} {G : StochasticGame ι}

/-- Two finite pushforwards have equal point masses when their relevant
fibers agree on the support of the source law. -/
theorem pmf_map_apply_eq_of_fiber_iff_on_support
    {α β γ : Type} [Finite α]
    (law : PMF α) (left : α → β) (right : α → γ)
    (leftValue : β) (rightValue : γ)
    (hfiber : ∀ value, value ∈ law.support →
      (left value = leftValue ↔ right value = rightValue)) :
    law.map left leftValue = law.map right rightValue := by
  letI : Fintype α := Fintype.ofFinite α
  classical
  simp only [PMF.map_apply, tsum_fintype]
  apply Finset.sum_congr rfl
  intro value _hvalue
  by_cases hsupport : value ∈ law.support
  · by_cases hleft : left value = leftValue
    · have hright : right value = rightValue :=
        (hfiber value hsupport).mp hleft
      rw [if_pos hleft.symm, if_pos hright.symm]
    · have hright : ¬right value = rightValue := by
        exact fun h => hleft ((hfiber value hsupport).mpr h)
      rw [if_neg (Ne.symm hleft), if_neg (Ne.symm hright)]
  · have hzero : law value = 0 := by
      simpa [PMF.mem_support_iff] using hsupport
    simp [hzero]

/-- A finite mixture whose kernels live over disjoint projection fibers has
the expected point-mass product formula. -/
theorem pmf_bind_apply_eq_mul_of_map_pure
    {α β : Type} [Finite α] [Finite β]
    (law : PMF α) (kernel : α → PMF β) (proj : β → α)
    (hproj : ∀ base, (kernel base).map proj = PMF.pure base)
    (value : β) :
    law.bind kernel value =
      law (proj value) * kernel (proj value) value := by
  letI : Fintype α := Fintype.ofFinite α
  classical
  simp only [PMF.bind_apply, tsum_fintype]
  apply Finset.sum_eq_single (proj value)
  · intro base _hbase hne
    have hzero : kernel base value = 0 := by
      apply Math.ProbabilityMassFunction.eq_zero_of_pushforward_eq_zero
        (kernel base) proj (b := proj value)
      · change (kernel base).map proj (proj value) = 0
        rw [hproj, PMF.pure_apply]
        exact if_neg (Ne.symm hne)
      · rfl
    simp [hzero]
  · simp

/-- An injective finite pushforward preserves every source point mass. -/
theorem pmf_map_apply_injective
    {α β : Type} [Finite α]
    (law : PMF α) (map : α → β) (hmap : Function.Injective map)
    (value : α) :
    law.map map (map value) = law value := by
  letI : Fintype α := Fintype.ofFinite α
  classical
  simp [PMF.map_apply, tsum_fintype, hmap.eq_iff]

/-- A bounded prefix of an induced history has the shorter induced law. -/
theorem histDist_map_boundedHistoryPrefix
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State)
    {fuel : ℕ} (time : Fin (fuel + 1)) :
    (G.histDist profile initial fuel).map
        (fun history => G.boundedHistoryPrefix history time) =
      G.histDist profile initial time.val := by
  induction fuel with
  | zero =>
      have htime : time = 0 := Fin.eq_zero time
      subst time
      rw [G.histDist_zero, PMF.pure_map]
      congr 1
  | succ fuel ih =>
      by_cases hlast : time.val = fuel + 1
      · have htime : time = Fin.last (fuel + 1) := by
          apply Fin.ext
          simpa using hlast
        subst time
        calc
          (G.histDist profile initial (fuel + 1)).map
                (fun history =>
                  G.boundedHistoryPrefix history (Fin.last (fuel + 1))) =
              (G.histDist profile initial (fuel + 1)).map id := by
            apply pmf_map_eq_of_eq_on_support
            intro history _hsupport
            apply Prod.ext
            · funext index
              rfl
            · simp [boundedHistoryPrefix]
          _ = G.histDist profile initial (fuel + 1) := PMF.map_id _
      · have hstrict : time.val < fuel + 1 := by omega
        let previousTime : Fin (fuel + 1) :=
          ⟨time.val, hstrict⟩
        rw [G.histDist_succ, PMF.map_bind]
        have hkernel :
            (fun history : G.Hist fuel =>
              ((G.stageActionDist profile history).bind fun action =>
                (G.transition history.2 action).bind fun next =>
                  PMF.pure
                    ((Fin.snoc history.1 (history.2, action), next) :
                      G.Hist (fuel + 1))).map
                (fun extended =>
                  G.boundedHistoryPrefix extended time)) =
              (fun history =>
                PMF.pure
                  (G.boundedHistoryPrefix history previousTime)) := by
          funext history
          rw [PMF.map_bind]
          have haction :
              (fun action =>
                ((G.transition history.2 action).bind fun next =>
                  PMF.pure
                    ((Fin.snoc history.1 (history.2, action), next) :
                      G.Hist (fuel + 1))).map
                  (fun extended =>
                    G.boundedHistoryPrefix extended time)) =
                (fun _action =>
                  PMF.pure
                    (G.boundedHistoryPrefix history previousTime)) := by
            funext action
            rw [PMF.map_bind]
            have hnext :
                (fun next =>
                  (PMF.pure
                    ((Fin.snoc history.1 (history.2, action), next) :
                      G.Hist (fuel + 1))).map
                    (fun extended =>
                      G.boundedHistoryPrefix extended time)) =
                  (fun _next =>
                    PMF.pure
                      (G.boundedHistoryPrefix history previousTime)) := by
              funext next
              rw [PMF.pure_map]
              congr 1
              let extended : G.Hist (fuel + 1) :=
                (Fin.snoc history.1 (history.2, action), next)
              change
                G.boundedHistoryPrefix extended time =
                  G.boundedHistoryPrefix history previousTime
              apply Prod.ext
              · funext index
                let oldIndex : Fin fuel :=
                  ⟨index.val, by omega⟩
                change
                  (@Fin.snoc fuel
                    (fun _ => G.State × G.JointAct)
                    history.1 (history.2, action))
                      (Fin.castLE
                        (Nat.lt_succ_iff.mp time.isLt) index) =
                    history.1
                      (Fin.castLE
                        (Nat.lt_succ_iff.mp previousTime.isLt) index)
                rw [show
                    (Fin.castLE
                      (Nat.lt_succ_iff.mp time.isLt) index) =
                        oldIndex.castSucc by
                    apply Fin.ext
                    rfl,
                  Fin.snoc_castSucc]
                congr 1
              · by_cases hbefore : time.val < fuel
                · let oldTime : Fin fuel := ⟨time.val, hbefore⟩
                  simp only [boundedHistoryPrefix, extended,
                    hstrict, ↓reduceDIte]
                  rw [show
                      (⟨time.val, by omega⟩ :
                        Fin (fuel + 1)) = oldTime.castSucc by
                      apply Fin.ext
                        rfl,
                    Fin.snoc_castSucc]
                  rw [dif_pos (show previousTime.val < fuel by
                    exact hbefore)]
                · have heq : time.val = fuel := by omega
                  simp [boundedHistoryPrefix, previousTime,
                    extended, heq, Fin.snoc]
            rw [hnext, PMF.bind_const]
          rw [haction, PMF.bind_const]
        rw [hkernel]
        change
          (G.histDist profile initial fuel).bind
              (PMF.pure ∘ fun history =>
                G.boundedHistoryPrefix history previousTime) =
            G.histDist profile initial time.val
        rw [PMF.bind_pure_comp, ih previousTime]

/-- Transporting a bounded prefix along equality of its length is the
bounded prefix at the transported length. -/
theorem cast_boundedHistoryPrefix
    {fuel : ℕ} (history : G.Hist fuel)
    {left right : Fin (fuel + 1)} (hlength : left = right) :
    cast (congrArg G.Hist (congrArg Fin.val hlength))
        (G.boundedHistoryPrefix history left) =
      G.boundedHistoryPrefix history right := by
  subst right
  rfl

/-- Taking a bounded prefix commutes with transporting the ambient history
length. -/
theorem boundedHistoryPrefix_cast
    {left right : ℕ} (hlength : left = right)
    (history : G.Hist left) (length : Fin (left + 1)) :
    G.boundedHistoryPrefix
        (cast (congrArg G.Hist hlength) history)
        (Fin.cast (congrArg (fun n => n + 1) hlength) length) =
      G.boundedHistoryPrefix history length := by
  subst right
  rfl

/-- The bounded prefix of an appended genuine suffix at the append point is
the original base. -/
theorem boundedHistoryPrefix_appendHist
    {prefixLength suffixLength : ℕ}
    (base : G.Hist prefixLength) (suffix : G.Hist suffixLength)
    (hstart : suffix.StartsAt base.2) :
    G.boundedHistoryPrefix (G.appendHist base suffix)
        ⟨prefixLength, by omega⟩ =
      base := by
  simpa only [
      G.boundedHistoryPrefix_add_eq_terminalPrefix] using
    G.terminalPrefix_appendHist base suffix hstart

/-- A stopped path reconstructed to the common root horizon has its original
stopped base as the bounded prefix at the stopped length. -/
theorem boundedHistoryPrefix_rootHistoryOfStoppedSuffix
    {fuel total : ℕ} (hfuel : fuel ≤ total)
    (path : G.RootHorizonStoppedSuffix fuel total)
    (hstart : path.2.StartsAt path.1.2.2) :
    G.boundedHistoryPrefix
        (G.rootHistoryOfStoppedSuffix hfuel path)
        ⟨path.1.1.val,
          Nat.lt_succ_of_le
            (G.stoppedLength_le_rootHorizon hfuel path.1)⟩ =
      path.1.2 := by
  let remaining := total - path.1.1.val
  have hlength := G.stoppedLength_le_rootHorizon hfuel path.1
  have hadd : path.1.1.val + remaining = total :=
    Nat.add_sub_of_le hlength
  let rawLength : Fin (path.1.1.val + remaining + 1) :=
    ⟨path.1.1.val, by omega⟩
  let rootLength : Fin (total + 1) :=
    ⟨path.1.1.val, Nat.lt_succ_of_le hlength⟩
  unfold rootHistoryOfStoppedSuffix
  change
    G.boundedHistoryPrefix
        (cast (congrArg G.Hist hadd)
          (G.appendHist path.1.2 path.2)) rootLength =
      path.1.2
  have htransport :=
    G.boundedHistoryPrefix_cast hadd
      (G.appendHist path.1.2 path.2) rawLength
  have hraw :=
    G.boundedHistoryPrefix_appendHist
      path.1.2 path.2 hstart
  have hcombined := htransport.trans hraw
  simpa [rootLength, rawLength] using hcombined

/-- Taking a bounded prefix through a longer bounded prefix gives the direct
short bounded prefix. -/
theorem boundedHistoryPrefix_nested
    {total fuel : ℕ} (history : G.Hist total)
    (hfuel : fuel ≤ total) (time : Fin (fuel + 1)) :
    G.boundedHistoryPrefix
        (G.boundedHistoryPrefix history
          ⟨fuel, Nat.lt_succ_of_le hfuel⟩) time =
      G.boundedHistoryPrefix history
        ⟨time.val, Nat.lt_succ_of_le
          (le_trans (Nat.lt_succ_iff.mp time.isLt) hfuel)⟩ := by
  apply Prod.ext
  · funext index
    rfl
  · by_cases htime : time.val < fuel
    · have htotal : time.val < total :=
        lt_of_lt_of_le htime hfuel
      simp [boundedHistoryPrefix, htime, htotal]
    · have heq : time.val = fuel := by omega
      simp [boundedHistoryPrefix, heq]

/-- At one fixed stopped base, reconstruction to the common root horizon is
injective in the suffix. -/
theorem rootHistoryOfStoppedSuffix_fixedBase_injective
    {fuel total : ℕ} (hfuel : fuel ≤ total)
    (base : G.BoundedStoppedHistory fuel) :
    Function.Injective
      (fun suffix : G.Hist (total - base.1.val) =>
        G.rootHistoryOfStoppedSuffix hfuel
          (⟨base, suffix⟩ :
            G.RootHorizonStoppedSuffix fuel total)) := by
  intro left right heq
  unfold rootHistoryOfStoppedSuffix at heq
  have happend :
      G.appendHist base.2 left =
        G.appendHist base.2 right :=
    (Equiv.cast _).injective heq
  simpa only [G.terminalSuffix_appendHist] using
    congrArg G.terminalSuffix happend

/-- Reconstructed stopped paths with the same base and the same root history
are equal. -/
theorem rootStoppedSuffix_eq_of_base_eq_of_rootHistory_eq
    {fuel total : ℕ} (hfuel : fuel ≤ total)
    (left right : G.RootHorizonStoppedSuffix fuel total)
    (hbase : left.1 = right.1)
    (hroot :
      G.rootHistoryOfStoppedSuffix hfuel left =
        G.rootHistoryOfStoppedSuffix hfuel right) :
    left = right := by
  rcases left with ⟨leftBase, leftSuffix⟩
  rcases right with ⟨rightBase, rightSuffix⟩
  dsimp only at hbase
  subst rightBase
  apply Sigma.ext
    (x := (⟨leftBase, leftSuffix⟩ :
      G.RootHorizonStoppedSuffix fuel total))
    (y := (⟨leftBase, rightSuffix⟩ :
      G.RootHorizonStoppedSuffix fuel total)) rfl
  apply heq_of_eq
  exact rootHistoryOfStoppedSuffix_fixedBase_injective
    hfuel leftBase hroot

/-- Every conditional fixed-prefix history kernel is supported over its
deterministic terminal prefix. -/
theorem histDistAfter_map_terminalPrefix
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) {prefixLength suffixLength : ℕ}
    (base : G.Hist prefixLength) :
    (G.histDistAfter profile base suffixLength).map
        G.terminalPrefix =
      PMF.pure base := by
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

/-- Point masses of an induced history law factor at every deterministic
prefix. -/
theorem histDist_add_apply_eq_prefix_mul_after
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) (initial : G.State)
    (prefixLength suffixLength : ℕ)
    (history : G.Hist (prefixLength + suffixLength)) :
    G.histDist profile initial (prefixLength + suffixLength) history =
      G.histDist profile initial prefixLength
          (G.terminalPrefix history) *
        G.histDistAfter profile (G.terminalPrefix history)
          suffixLength history := by
  rw [G.histDist_add_eq_bind_histDistAfter]
  exact pmf_bind_apply_eq_mul_of_map_pure
    (G.histDist profile initial prefixLength)
    (fun base => G.histDistAfter profile base suffixLength)
    G.terminalPrefix
    (G.histDistAfter_map_terminalPrefix profile) history

/-- Appending one fixed base is injective in the suffix. -/
theorem appendHist_injective
    {prefixLength suffixLength : ℕ} (base : G.Hist prefixLength) :
    Function.Injective
      (G.appendHist base :
        G.Hist suffixLength → G.Hist (prefixLength + suffixLength)) := by
  intro left right heq
  simpa only [G.terminalSuffix_appendHist] using
    congrArg G.terminalSuffix heq

/-- The conditional full-history point mass at an appended genuine suffix
is exactly the local suffix point mass. -/
theorem histDistAfter_apply_appendHist
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    (profile : G.BehaviorProfile) {prefixLength suffixLength : ℕ}
    (base : G.Hist prefixLength) (suffix : G.Hist suffixLength) :
    G.histDistAfter profile base suffixLength
        (G.appendHist base suffix) =
      G.histDist (G.afterHistoryProfile profile base) base.2
        suffixLength suffix := by
  unfold histDistAfter
  exact pmf_map_apply_injective
    (G.histDist (G.afterHistoryProfile profile base) base.2
      suffixLength)
    (G.appendHist base)
    (G.appendHist_injective base) suffix

/-- Transporting a point mass together with its finite horizon does not
change that point mass. -/
theorem histDist_apply_cast
    [Fintype ι] (profile : G.BehaviorProfile) (initial : G.State)
    {left right : ℕ} (hlength : left = right)
    (history : G.Hist left) :
    G.histDist profile initial right
        (cast (congrArg G.Hist hlength) history) =
      G.histDist profile initial left history := by
  subst right
  rfl

/-- The root-law mass of a stopped base followed by a genuine local suffix
is the product of the base-prefix mass and the rebased suffix mass. -/
theorem histDist_apply_rootHistoryOfStoppedSuffix
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel total : ℕ} (profile : G.BehaviorProfile)
    (initial : G.State) (hfuel : fuel ≤ total)
    (path : G.RootHorizonStoppedSuffix fuel total)
    (hstart : path.2.StartsAt path.1.2.2) :
    G.histDist profile initial total
        (G.rootHistoryOfStoppedSuffix hfuel path) =
      G.histDist profile initial path.1.1.val path.1.2 *
        G.histDist
          (G.afterHistoryProfile profile path.1.2)
          path.1.2.2 (total - path.1.1.val) path.2 := by
  let remaining := total - path.1.1.val
  have hlength := G.stoppedLength_le_rootHorizon hfuel path.1
  have hadd : path.1.1.val + remaining = total :=
    Nat.add_sub_of_le hlength
  unfold rootHistoryOfStoppedSuffix
  rw [G.histDist_apply_cast profile initial hadd
    (G.appendHist path.1.2 path.2)]
  rw [G.histDist_add_apply_eq_prefix_mul_after]
  have hprefix :
      G.terminalPrefix (G.appendHist path.1.2 path.2) =
        path.1.2 :=
    G.terminalPrefix_appendHist path.1.2 path.2 hstart
  rw [hprefix, G.histDistAfter_apply_appendHist]

/-- At a supported stopped public history, causality removes all future
selection mass: the stopped-history mass is exactly the mass of its public
prefix at the selected time. -/
theorem stoppedHistoryLaw_apply_eq_histDist_of_causal
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel : ℕ} (profile : G.BehaviorProfile) (initial : G.State)
    (selector : G.BoundedPublicStopSelector fuel)
    (hcausal : G.IsCausalBoundedStopSelector selector)
    (base : G.BoundedStoppedHistory fuel)
    (hbase :
      base ∈
        (G.stoppedHistoryLaw profile initial selector).support) :
    G.stoppedHistoryLaw profile initial selector base =
      G.histDist profile initial base.1.val base.2 := by
  unfold stoppedHistoryLaw at hbase ⊢
  rcases
      (PMF.mem_support_map_iff
        (G.selectedStoppedHistory selector)
        (G.histDist profile initial fuel) base).1 hbase with
    ⟨witness, hwitness, hwitnessBase⟩
  subst base
  calc
    (G.histDist profile initial fuel).map
          (G.selectedStoppedHistory selector)
          (G.selectedStoppedHistory selector witness) =
        (G.histDist profile initial fuel).map
          (fun history =>
            G.boundedHistoryPrefix history (selector witness))
          (G.boundedHistoryPrefix witness (selector witness)) := by
      apply pmf_map_apply_eq_of_fiber_iff_on_support
      intro history hhistory
      constructor
      · intro heq
        have hparts := (Sigma.ext_iff.mp heq)
        have hselection :
            selector history = selector witness := by
          exact hparts.1
        have hsnd :
            G.boundedHistoryPrefix history (selector history) ≍
              G.boundedHistoryPrefix witness
                (selector witness) := by
          exact hparts.2
        have hcast :
            cast (congrArg G.Hist
              (congrArg Fin.val hselection))
                (G.boundedHistoryPrefix history
                  (selector history)) =
              G.boundedHistoryPrefix witness
                (selector witness) :=
          cast_eq_iff_heq.mpr hsnd
        calc
          G.boundedHistoryPrefix history (selector witness) =
              cast (congrArg G.Hist
                (congrArg Fin.val hselection))
                (G.boundedHistoryPrefix history
                  (selector history)) :=
            (cast_boundedHistoryPrefix history hselection).symm
          _ =
              G.boundedHistoryPrefix witness
                (selector witness) := hcast
      · intro hprefix
        have hselection :
            selector history = selector witness :=
          hcausal.exactPrefix witness history hprefix.symm
        apply Sigma.ext hselection
        apply cast_eq_iff_heq.mp
        calc
          cast (congrArg G.Hist
            (congrArg Fin.val hselection))
                (G.boundedHistoryPrefix history
                  (selector history)) =
              G.boundedHistoryPrefix history
                (selector witness) :=
            cast_boundedHistoryPrefix history hselection
          _ =
              G.boundedHistoryPrefix witness
                (selector witness) := hprefix
    _ =
        G.histDist profile initial (selector witness).val
          (G.boundedHistoryPrefix witness
            (selector witness)) := by
      rw [G.histDist_map_boundedHistoryPrefix]

/-- A supported causal stopped path is recovered exactly after reconstructing
its root history. -/
theorem rootStoppedPathOfHistory_rootHistoryOfStoppedSuffix
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel total : ℕ} (profile : G.BehaviorProfile)
    (initial : G.State) (selector : G.BoundedPublicStopSelector fuel)
    (hcausal : G.IsCausalBoundedStopSelector selector)
    (hfuel : fuel ≤ total)
    (path : G.RootHorizonStoppedSuffix fuel total)
    (hbase :
      path.1 ∈
        (G.stoppedHistoryLaw profile initial selector).support)
    (hstart : path.2.StartsAt path.1.2.2) :
    G.rootStoppedPathOfHistory selector hfuel
        (G.rootHistoryOfStoppedSuffix hfuel path) =
      path := by
  unfold stoppedHistoryLaw at hbase
  rcases
      (PMF.mem_support_map_iff
        (G.selectedStoppedHistory selector)
        (G.histDist profile initial fuel) path.1).1 hbase with
    ⟨witness, _hwitness, hwitnessBase⟩
  have hparts := Sigma.ext_iff.mp hwitnessBase
  have hwitnessLength :
      selector witness = path.1.1 := hparts.1
  have hwitnessCast :
      cast (congrArg G.Hist
        (congrArg Fin.val hwitnessLength))
          (G.boundedHistoryPrefix witness (selector witness)) =
        path.1.2 :=
    cast_eq_iff_heq.mpr hparts.2
  have hwitnessPrefix :
      G.boundedHistoryPrefix witness path.1.1 = path.1.2 := by
    calc
      G.boundedHistoryPrefix witness path.1.1 =
          cast (congrArg G.Hist
            (congrArg Fin.val hwitnessLength))
              (G.boundedHistoryPrefix witness
                (selector witness)) :=
        (cast_boundedHistoryPrefix witness
          hwitnessLength).symm
      _ = path.1.2 := hwitnessCast
  let full := G.rootHistoryOfStoppedSuffix hfuel path
  let fuelLength : Fin (total + 1) :=
    ⟨fuel, Nat.lt_succ_of_le hfuel⟩
  let fuelHistory := G.boundedHistoryPrefix full fuelLength
  have hfullPrefix :
      G.boundedHistoryPrefix fuelHistory path.1.1 =
        path.1.2 := by
    calc
      G.boundedHistoryPrefix fuelHistory path.1.1 =
          G.boundedHistoryPrefix full
            ⟨path.1.1.val,
              Nat.lt_succ_of_le
                (G.stoppedLength_le_rootHorizon
                  hfuel path.1)⟩ := by
        exact G.boundedHistoryPrefix_nested full hfuel path.1.1
      _ = path.1.2 :=
        G.boundedHistoryPrefix_rootHistoryOfStoppedSuffix
          hfuel path hstart
  have hselectedPrefix :
      G.boundedHistoryPrefix witness (selector witness) =
        G.boundedHistoryPrefix fuelHistory
          (selector witness) := by
    rw [hwitnessLength]
    exact hwitnessPrefix.trans hfullPrefix.symm
  have hfuelSelection :
      selector fuelHistory = path.1.1 :=
    (hcausal.exactPrefix witness fuelHistory
      hselectedPrefix).trans hwitnessLength
  have hselectedBase :
      G.selectedStoppedHistory selector fuelHistory = path.1 := by
    apply Sigma.ext hfuelSelection
    apply cast_eq_iff_heq.mp
    calc
      cast (congrArg G.Hist
        (congrArg Fin.val hfuelSelection))
          (G.boundedHistoryPrefix fuelHistory
            (selector fuelHistory)) =
          G.boundedHistoryPrefix fuelHistory path.1.1 :=
        cast_boundedHistoryPrefix fuelHistory hfuelSelection
      _ = path.1.2 := hfullPrefix
  let actual :=
    G.rootStoppedPathOfHistory selector hfuel full
  have hactualBase : actual.1 = path.1 := by
    exact hselectedBase
  apply G.rootStoppedSuffix_eq_of_base_eq_of_rootHistory_eq
    hfuel actual path hactualBase
  calc
    G.rootHistoryOfStoppedSuffix hfuel actual = full :=
      G.rootHistoryOfStoppedSuffix_rootStoppedPathOfHistory_exact
        selector hfuel full
    _ = G.rootHistoryOfStoppedSuffix hfuel path := rfl

/-- Reconstructing an actually stopped path has the actual stopped base as
its bounded prefix. -/
theorem boundedHistoryPrefix_rootStoppedPathOfHistory
    {fuel total : ℕ} (selector : G.BoundedPublicStopSelector fuel)
    (hfuel : fuel ≤ total) (history : G.Hist total) :
    G.boundedHistoryPrefix
        (G.rootHistoryOfStoppedSuffix hfuel
          (G.rootStoppedPathOfHistory selector hfuel history))
        ⟨(G.rootStoppedPathOfHistory selector hfuel history).1.1.val,
          Nat.lt_succ_of_le
            (G.stoppedLength_le_rootHorizon hfuel
              (G.rootStoppedPathOfHistory selector hfuel history).1)⟩ =
      (G.rootStoppedPathOfHistory selector hfuel history).1.2 := by
  let fuelLength : Fin (total + 1) :=
    ⟨fuel, Nat.lt_succ_of_le hfuel⟩
  let fuelHistory := G.boundedHistoryPrefix history fuelLength
  let base := G.selectedStoppedHistory selector fuelHistory
  have hreconstruct :
      G.rootHistoryOfStoppedSuffix hfuel
          (G.rootStoppedPathOfHistory selector hfuel history) =
        history :=
    G.rootHistoryOfStoppedSuffix_rootStoppedPathOfHistory_exact
      selector hfuel history
  rw [hreconstruct]
  calc
    G.boundedHistoryPrefix history
          ⟨base.1.val,
            Nat.lt_succ_of_le
              (G.stoppedLength_le_rootHorizon hfuel base)⟩ =
        G.boundedHistoryPrefix fuelHistory base.1 := by
      exact
        (G.boundedHistoryPrefix_nested
          history hfuel base.1).symm
    _ = base.2 := rfl

/-- If a reconstructed path has its displayed base as its stopped prefix,
then the raw appended suffix has that base as its terminal prefix. -/
theorem terminalPrefix_appendHist_of_rootPrefix
    {fuel total : ℕ} (hfuel : fuel ≤ total)
    (path : G.RootHorizonStoppedSuffix fuel total)
    (hrootPrefix :
      G.boundedHistoryPrefix
          (G.rootHistoryOfStoppedSuffix hfuel path)
          ⟨path.1.1.val,
            Nat.lt_succ_of_le
              (G.stoppedLength_le_rootHorizon hfuel path.1)⟩ =
        path.1.2) :
    G.terminalPrefix (G.appendHist path.1.2 path.2) =
      path.1.2 := by
  let remaining := total - path.1.1.val
  have hlength := G.stoppedLength_le_rootHorizon hfuel path.1
  have hadd : path.1.1.val + remaining = total :=
    Nat.add_sub_of_le hlength
  let rawLength : Fin (path.1.1.val + remaining + 1) :=
    ⟨path.1.1.val, by omega⟩
  have htransport :=
    G.boundedHistoryPrefix_cast hadd
      (G.appendHist path.1.2 path.2) rawLength
  have hrootAtCast :
      G.boundedHistoryPrefix
          (G.rootHistoryOfStoppedSuffix hfuel path)
          (Fin.cast
            (congrArg (fun n => n + 1) hadd) rawLength) =
        path.1.2 := by
    simpa [rawLength] using hrootPrefix
  have hrawPrefix :
      G.boundedHistoryPrefix
          (G.appendHist path.1.2 path.2) rawLength =
        path.1.2 :=
    htransport.symm.trans hrootAtCast
  calc
    G.terminalPrefix (G.appendHist path.1.2 path.2) =
        G.boundedHistoryPrefix
          (G.appendHist path.1.2 path.2) rawLength := by
      exact
        (G.boundedHistoryPrefix_add_eq_terminalPrefix
          (G.appendHist path.1.2 path.2)).symm
    _ = path.1.2 := hrawPrefix

/-- Root point-mass factorization under the intrinsic stopped-prefix
identity. -/
theorem histDist_apply_rootHistoryOfStoppedSuffix_of_rootPrefix
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel total : ℕ} (profile : G.BehaviorProfile)
    (initial : G.State) (hfuel : fuel ≤ total)
    (path : G.RootHorizonStoppedSuffix fuel total)
    (hrootPrefix :
      G.boundedHistoryPrefix
          (G.rootHistoryOfStoppedSuffix hfuel path)
          ⟨path.1.1.val,
            Nat.lt_succ_of_le
              (G.stoppedLength_le_rootHorizon hfuel path.1)⟩ =
        path.1.2) :
    G.histDist profile initial total
        (G.rootHistoryOfStoppedSuffix hfuel path) =
      G.histDist profile initial path.1.1.val path.1.2 *
        G.histDist
          (G.afterHistoryProfile profile path.1.2)
          path.1.2.2 (total - path.1.1.val) path.2 := by
  let remaining := total - path.1.1.val
  have hlength := G.stoppedLength_le_rootHorizon hfuel path.1
  have hadd : path.1.1.val + remaining = total :=
    Nat.add_sub_of_le hlength
  unfold rootHistoryOfStoppedSuffix
  rw [G.histDist_apply_cast profile initial hadd
    (G.appendHist path.1.2 path.2)]
  rw [G.histDist_add_apply_eq_prefix_mul_after]
  have hprefix :
      G.terminalPrefix (G.appendHist path.1.2 path.2) =
        path.1.2 :=
    G.terminalPrefix_appendHist_of_rootPrefix
      hfuel path hrootPrefix
  rw [hprefix, G.histDistAfter_apply_appendHist]

/-- Tagging one local suffix with a fixed stopped base is injective. -/
theorem stoppedSuffixTag_injective
    {fuel total : ℕ} (base : G.BoundedStoppedHistory fuel) :
    Function.Injective
      (fun suffix : G.Hist (total - base.1.val) =>
        (⟨base, suffix⟩ :
          G.RootHorizonStoppedSuffix fuel total)) := by
  intro left right heq
  exact eq_of_heq (Sigma.ext_iff.mp heq).2

/-- The candidate stopped-suffix point mass at its fixed tag is the local
rebased suffix point mass. -/
theorem stoppedSuffixCandidateAdd_apply
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel suffixLength : ℕ} (profile : G.BehaviorProfile)
    (base : G.BoundedStoppedHistory fuel)
    (suffix : G.Hist (fuel + suffixLength - base.1.val)) :
    G.stoppedSuffixCandidateAdd
        (suffixLength := suffixLength) profile base
        (⟨base, suffix⟩ :
          G.RootHorizonStoppedSuffix fuel
            (fuel + suffixLength)) =
      G.histDist (G.afterHistoryProfile profile base.2)
        base.2.2 (fuel + suffixLength - base.1.val) suffix := by
  unfold stoppedSuffixCandidateAdd
  exact pmf_map_apply_injective
    (G.histDist (G.afterHistoryProfile profile base.2)
      base.2.2 (fuel + suffixLength - base.1.val))
    (fun localSuffix =>
      (⟨base, localSuffix⟩ :
        G.RootHorizonStoppedSuffix fuel (fuel + suffixLength)))
    (G.stoppedSuffixTag_injective base) suffix

/-- Decomposition at a bounded selector is injective because reconstruction
is a pointwise left inverse. -/
theorem rootStoppedPathOfHistory_injective
    {fuel total : ℕ} (selector : G.BoundedPublicStopSelector fuel)
    (hfuel : fuel ≤ total) :
    Function.Injective
      (G.rootStoppedPathOfHistory selector hfuel) := by
  intro left right heq
  have hreconstruct :=
    congrArg (G.rootHistoryOfStoppedSuffix hfuel) heq
  simpa only [
      G.rootHistoryOfStoppedSuffix_rootStoppedPathOfHistory_exact]
    using hreconstruct

/-- Finite strong stopping: every causal bounded selector satisfies the
eventwise product identity at every additive root horizon. -/
theorem isStoppedSuffixEventRatioAdd_of_causal
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel suffixLength : ℕ} (profile : G.BehaviorProfile)
    (initial : G.State) (selector : G.BoundedPublicStopSelector fuel)
    (hcausal : G.IsCausalBoundedStopSelector selector) :
    G.IsStoppedSuffixEventRatioAdd
      (suffixLength := suffixLength) profile initial selector := by
  intro base hbase path hpath
  subst base
  let total := fuel + suffixLength
  let full :=
    G.rootHistoryOfStoppedSuffix
      (Nat.le_add_right fuel suffixLength) path
  let localLaw :=
    G.histDist (G.afterHistoryProfile profile path.1.2)
      path.1.2.2 (total - path.1.1.val)
  have hbaseMass :
      G.stoppedHistoryLaw profile initial selector path.1 =
        G.histDist profile initial path.1.1.val path.1.2 :=
    G.stoppedHistoryLaw_apply_eq_histDist_of_causal
      profile initial selector hcausal path.1 hbase
  by_cases hlocal : localLaw path.2 = 0
  · have hcandidate :
        G.stoppedSuffixCandidateAdd
            (suffixLength := suffixLength) profile path.1 path = 0 := by
      rw [show path = ⟨path.1, path.2⟩ from path.eta]
      exact G.stoppedSuffixCandidateAdd_apply
        (suffixLength := suffixLength) profile path.1 path.2
          |>.trans hlocal
    rw [hcandidate, mul_zero]
    by_contra hjoint
    have hpathSupport :
        path ∈
          ((G.histDist profile initial total).map
            (G.rootStoppedPathOfHistory selector
              (Nat.le_add_right fuel suffixLength))).support := by
      simpa only [PMF.mem_support_iff] using hjoint
    rcases
        (PMF.mem_support_map_iff
          (G.rootStoppedPathOfHistory selector
            (Nat.le_add_right fuel suffixLength))
      (G.histDist profile initial total) path).1 hpathSupport with
      ⟨actualFull, hactualSupport, hactualPath⟩
    have hactualPrefix :=
      G.boundedHistoryPrefix_rootStoppedPathOfHistory
        selector (Nat.le_add_right fuel suffixLength) actualFull
    rw [hactualPath] at hactualPrefix
    have hfullEq : actualFull = full := by
      change actualFull =
        G.rootHistoryOfStoppedSuffix
          (Nat.le_add_right fuel suffixLength) path
      calc
        actualFull =
            G.rootHistoryOfStoppedSuffix
              (Nat.le_add_right fuel suffixLength)
              (G.rootStoppedPathOfHistory selector
                (Nat.le_add_right fuel suffixLength) actualFull) :=
          (G.rootHistoryOfStoppedSuffix_rootStoppedPathOfHistory_exact
            selector (Nat.le_add_right fuel suffixLength)
            actualFull).symm
        _ =
            G.rootHistoryOfStoppedSuffix
              (Nat.le_add_right fuel suffixLength) path := by
          rw [hactualPath]
    have hfullPositive :
        G.histDist profile initial total full ≠ 0 := by
      rw [← hfullEq]
      simpa [PMF.mem_support_iff] using hactualSupport
    have hproduct :=
      G.histDist_apply_rootHistoryOfStoppedSuffix_of_rootPrefix
        profile initial (Nat.le_add_right fuel suffixLength)
        path hactualPrefix
    change
      G.histDist profile initial total full =
        G.histDist profile initial path.1.1.val path.1.2 *
          localLaw path.2 at hproduct
    rw [hlocal, mul_zero] at hproduct
    exact hfullPositive hproduct
  · have hlocalSupport : path.2 ∈ localLaw.support := by
      simpa [PMF.mem_support_iff] using hlocal
    have hstart : path.2.StartsAt path.1.2.2 :=
      G.startsAt_of_mem_support_histDist
        (G.afterHistoryProfile profile path.1.2)
        path.1.2.2 (total - path.1.1.val) path.2
        hlocalSupport
    have hrealized :
        G.rootStoppedPathOfHistory selector
            (Nat.le_add_right fuel suffixLength) full =
          path :=
      G.rootStoppedPathOfHistory_rootHistoryOfStoppedSuffix
        profile initial selector hcausal
        (Nat.le_add_right fuel suffixLength) path hbase hstart
    have hjoint :
        (G.histDist profile initial total).map
            (G.rootStoppedPathOfHistory selector
              (Nat.le_add_right fuel suffixLength)) path =
          G.histDist profile initial total full := by
      rw [← hrealized]
      exact pmf_map_apply_injective
        (G.histDist profile initial total)
        (G.rootStoppedPathOfHistory selector
          (Nat.le_add_right fuel suffixLength))
        (G.rootStoppedPathOfHistory_injective selector
          (Nat.le_add_right fuel suffixLength)) full
    rw [hjoint,
      G.histDist_apply_rootHistoryOfStoppedSuffix
        profile initial (Nat.le_add_right fuel suffixLength)
        path hstart,
      ← hbaseMass]
    congr 1
    rw [show path = ⟨path.1, path.2⟩ from path.eta]
    exact
      (G.stoppedSuffixCandidateAdd_apply
        (suffixLength := suffixLength)
        profile path.1 path.2).symm

/-- A concrete online causal rule inherits the stopped-suffix event ratio
from its finite stopping-time field. -/
theorem OnlineCausalBoundedStoppingRule.isStoppedSuffixEventRatioAdd
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel suffixLength : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (profile : G.BehaviorProfile) (initial : G.State) :
    G.IsStoppedSuffixEventRatioAdd
      (suffixLength := suffixLength)
      profile initial rule.selector :=
  G.isStoppedSuffixEventRatioAdd_of_causal
    profile initial rule.selector rule.causal

/-- Causality alone supplies the complete dependent stopped-path joint-law
factorization at every additive root horizon. -/
theorem causalDispatcherJointLawAt_add_of_causal
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel suffixLength : ℕ} (profile : G.BehaviorProfile)
    (initial : G.State) (selector : G.BoundedPublicStopSelector fuel)
    (hcausal : G.IsCausalBoundedStopSelector selector) :
    G.CausalDispatcherJointLawAt profile initial selector
      (Nat.le_add_right fuel suffixLength) :=
  G.causalDispatcherJointLawAt_add_of_eventRatio
    profile initial selector
    (G.isStoppedSuffixEventRatioAdd_of_causal
      profile initial selector hcausal)

/-- The dynamic dispatcher of an online causal rule therefore has the exact
root stopped-suffix disintegration, without a separately supplied joint-law
hypothesis. -/
theorem OnlineCausalBoundedStoppingRule.toRootDisintegration_add
    [Fintype ι] [Finite G.State] [∀ who, Finite (G.Act who)]
    {fuel suffixLength : ℕ}
    (rule : OnlineCausalBoundedStoppingRule G fuel)
    (selection : G.BehaviorProfile)
    (child :
      G.BoundedStoppedHistory fuel → G.BehaviorProfile)
    (initial : G.State) :
    G.IsRootStoppedSuffixDisintegration
      (G.causalTerminalChildDispatcher rule selection child)
      initial rule.selector
      (Nat.le_add_right fuel suffixLength) :=
  rule.toRootStoppedSuffixDisintegration
    selection child initial (Nat.le_add_right fuel suffixLength)
    (G.causalDispatcherJointLawAt_add_of_causal
      (G.causalTerminalChildDispatcher rule selection child)
      initial rule.selector rule.causal)

end StochasticGame
end GameTheory
