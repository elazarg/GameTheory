/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Diagnostics.Quitting.TerminalSemanticEqualityStratum

/-!
# State-matched chronology on the minimum terminal-semantic stratum

Fix a minimum-total-debt point of the compact terminal-semantic carrier.  The
fiber of all carrier points with the same total debt is compact.  Exact Nash
prefixing sends every point of this fiber to another point of the fiber, so
the prefix correspondence is predecessor-serial there.  Its compact inverse
limit gives one infinite chronology in which every current semantic pair is
the exact prefix of the next pair.

The resulting path is more than an abstract payoff spine: it transports the
full prescribed/envelope pair, hence every literal semantic-debt coordinate
is constant along time.  If no point of the minimum fiber admits an
all-Continue Nash root, the equality-stratum alternative then fixes one
positive-debt owner for the entire path.  Every root is a positive-hazard
solo-owner row, and every date exposes an outsider whose attractive singleton
option is deterred by that row.

The construction remains finite-dimensional.  It does not identify a carrier
pair with the terminal semantics of one behavior profile, nor does it prove
that the root path absorbs almost surely.
-/

noncomputable section

namespace GameTheory

open Filter Math.Probability Math.ProbabilityMassFunction Math.Topology
open scoped Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- A semantic pair together with the simplex root labelling its outgoing
backward prefix edge. -/
abbrev QuittingTerminalSemanticSpinePoint (ι : Type) [Fintype ι] :=
  QuittingTerminalSemanticPair ι × QuittingRootSimplex ι

/-- The compact minimum-total-debt fiber through a fixed minimum point. -/
def quittingTerminalSemanticMinimumSpineBox
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι) :
    Set (QuittingTerminalSemanticSpinePoint ι) :=
  {point | point.1 ∈ quittingTerminalSemanticCarrier reward ∧
    quittingTerminalSemanticDebtSum point.1 =
      quittingTerminalSemanticDebtSum base}

/-- One exact state-matched semantic prefix edge.  The current state's
simplex coordinate supplies the root; the tail state's simplex coordinate is
irrelevant to this edge. -/
def IsQuittingTerminalSemanticMinimumSpineEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current tail : QuittingTerminalSemanticSpinePoint ι) : Prop :=
  current.1 = quittingTerminalSemanticPrefix reward
      (quittingRootOfSimplex current.2) tail.1 ∧
    IsεQuittingRootEndpointNash reward tail.1.1 0
      (quittingRootOfSimplex current.2)

theorem quittingTerminalSemanticMinimumSpineBox_nonempty
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι)
    (hbase : base ∈ quittingTerminalSemanticCarrier reward) :
    (quittingTerminalSemanticMinimumSpineBox reward base).Nonempty := by
  let root : QuittingRootSimplex ι :=
    fun _ => stdSimplexEquiv (PMF.pure false)
  exact ⟨(base, root), hbase, rfl⟩

/-- The fixed minimum fiber, including its harmless simplex label, is
compact. -/
theorem quittingTerminalSemanticMinimumSpineBox_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    IsCompact (quittingTerminalSemanticMinimumSpineBox reward base) := by
  let fiber : Set (QuittingTerminalSemanticPair ι) :=
    quittingTerminalSemanticCarrier reward ∩
      {pair | quittingTerminalSemanticDebtSum pair =
        quittingTerminalSemanticDebtSum base}
  have hfiberClosed : IsClosed
      {pair : QuittingTerminalSemanticPair ι |
        quittingTerminalSemanticDebtSum pair =
          quittingTerminalSemanticDebtSum base} :=
    isClosed_eq continuous_quittingTerminalSemanticDebtSum continuous_const
  have hfiberCompact : IsCompact fiber :=
    (quittingTerminalSemanticCarrier_isCompact reward hM hreward).inter_right
      hfiberClosed
  have heq : quittingTerminalSemanticMinimumSpineBox reward base =
      fiber ×ˢ (Set.univ : Set (QuittingRootSimplex ι)) := by
    ext point
    simp [quittingTerminalSemanticMinimumSpineBox, fiber]
  rw [heq]
  exact hfiberCompact.prod isCompact_univ

/-- Exact minimum-fiber semantic prefix edges form a closed graph. -/
theorem isClosed_quittingTerminalSemanticMinimumSpineEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    IsClosed {edge : QuittingTerminalSemanticSpinePoint ι ×
        QuittingTerminalSemanticSpinePoint ι |
      edge.1 ∈ quittingTerminalSemanticMinimumSpineBox reward base ∧
        edge.2 ∈ quittingTerminalSemanticMinimumSpineBox reward base ∧
        IsQuittingTerminalSemanticMinimumSpineEdge reward edge.1 edge.2} := by
  let box := quittingTerminalSemanticMinimumSpineBox reward base
  have hbox : IsClosed box :=
    (quittingTerminalSemanticMinimumSpineBox_isCompact
      reward base hM hreward).isClosed
  have hcurrentBox : IsClosed
      {edge : QuittingTerminalSemanticSpinePoint ι ×
          QuittingTerminalSemanticSpinePoint ι | edge.1 ∈ box} :=
    hbox.preimage continuous_fst
  have htailBox : IsClosed
      {edge : QuittingTerminalSemanticSpinePoint ι ×
          QuittingTerminalSemanticSpinePoint ι | edge.2 ∈ box} :=
    hbox.preimage continuous_snd
  let prefixData : QuittingTerminalSemanticSpinePoint ι ×
      QuittingTerminalSemanticSpinePoint ι →
      QuittingRootSimplex ι × QuittingTerminalSemanticPair ι :=
    fun edge => (edge.1.2, edge.2.1)
  have hprefixData : Continuous prefixData := by
    dsimp only [prefixData]
    fun_prop
  have hprefixMap : Continuous
      (fun data : QuittingRootSimplex ι ×
          QuittingTerminalSemanticPair ι =>
        quittingTerminalSemanticPrefix reward
          (quittingRootOfSimplex data.1) data.2) := by
    -- Continuity in the root and semantic pair follows coordinatewise from
    -- the finite root-payoff formulas.
    have hprescribed : Continuous
        (fun data : QuittingRootSimplex ι ×
            QuittingTerminalSemanticPair ι =>
          quittingRootSuccessorPayoff reward data.2.1
            (quittingRootOfSimplex data.1)) := by
      have hmap : Continuous (fun data : QuittingRootSimplex ι ×
          QuittingTerminalSemanticPair ι => (data.2.1, data.1)) := by
        fun_prop
      have hc :=
        (continuous_quittingRootSuccessorPayoff_simplex reward).comp hmap
      change Continuous (fun data : QuittingRootSimplex ι ×
        QuittingTerminalSemanticPair ι =>
          quittingRootSuccessorPayoff reward data.2.1
            (quittingRootOfSimplex data.1)) at hc
      exact hc
    have henvelope : Continuous
        (fun data : QuittingRootSimplex ι ×
            QuittingTerminalSemanticPair ι => fun who =>
          max
            (quittingRootQuitPayoff reward data.2.1
              (quittingRootOfSimplex data.1) who)
            (quittingRootContinuePayoff reward
              (Function.update data.2.1 who (data.2.2 who))
              (quittingRootOfSimplex data.1) who)) := by
      apply continuous_pi
      intro who
      have hquitMap : Continuous (fun data : QuittingRootSimplex ι ×
          QuittingTerminalSemanticPair ι => (data.2.1, data.1)) := by
        fun_prop
      have hquit :=
        (continuous_quittingRootQuitPayoff_simplex reward who).comp hquitMap
      have htail : Continuous (fun data : QuittingRootSimplex ι ×
          QuittingTerminalSemanticPair ι =>
        Function.update data.2.1 who (data.2.2 who)) := by
        apply continuous_pi
        intro player
        by_cases hplayer : player = who
        · subst player
          have hpair : Continuous
              (fun data : QuittingRootSimplex ι ×
                QuittingTerminalSemanticPair ι => data.2) := continuous_snd
          have henvelopePayoff : Continuous
              (fun data : QuittingRootSimplex ι ×
                QuittingTerminalSemanticPair ι => data.2.2) :=
            continuous_snd.comp hpair
          have hcoordinate := (continuous_apply who).comp henvelopePayoff
          change Continuous (fun data : QuittingRootSimplex ι ×
            QuittingTerminalSemanticPair ι => data.2.2 who) at hcoordinate
          simpa [Function.update_self] using hcoordinate
        · have hpair : Continuous
              (fun data : QuittingRootSimplex ι ×
                QuittingTerminalSemanticPair ι => data.2) := continuous_snd
          have hprescribedPayoff : Continuous
              (fun data : QuittingRootSimplex ι ×
                QuittingTerminalSemanticPair ι => data.2.1) :=
            continuous_fst.comp hpair
          have hcoordinate :=
            (continuous_apply player).comp hprescribedPayoff
          change Continuous (fun data : QuittingRootSimplex ι ×
            QuittingTerminalSemanticPair ι => data.2.1 player) at hcoordinate
          simpa [Function.update_of_ne hplayer] using hcoordinate
      have hcontinueMap : Continuous
          (fun data : QuittingRootSimplex ι ×
              QuittingTerminalSemanticPair ι =>
            (Function.update data.2.1 who (data.2.2 who), data.1)) :=
        htail.prodMk continuous_fst
      have hcontinue :=
        (continuous_quittingRootContinuePayoff_simplex reward who).comp
          hcontinueMap
      exact (by
        simpa only [Function.comp_apply] using hquit.max hcontinue)
    change Continuous (fun data : QuittingRootSimplex ι ×
        QuittingTerminalSemanticPair ι =>
      (quittingRootSuccessorPayoff reward data.2.1
          (quittingRootOfSimplex data.1),
        fun who =>
          max
            (quittingRootQuitPayoff reward data.2.1
              (quittingRootOfSimplex data.1) who)
            (quittingRootContinuePayoff reward
              (Function.update data.2.1 who (data.2.2 who))
              (quittingRootOfSimplex data.1) who)))
    exact hprescribed.prodMk henvelope
  have hprefix : IsClosed
      {edge : QuittingTerminalSemanticSpinePoint ι ×
          QuittingTerminalSemanticSpinePoint ι |
        edge.1.1 = quittingTerminalSemanticPrefix reward
          (quittingRootOfSimplex edge.1.2) edge.2.1} := by
    have hleft : Continuous
        (fun edge : QuittingTerminalSemanticSpinePoint ι ×
          QuittingTerminalSemanticSpinePoint ι => edge.1.1) := by
      fun_prop
    have hright := hprefixMap.comp hprefixData
    change Continuous
      (fun edge : QuittingTerminalSemanticSpinePoint ι ×
        QuittingTerminalSemanticSpinePoint ι =>
        quittingTerminalSemanticPrefix reward
          (quittingRootOfSimplex edge.1.2) edge.2.1) at hright
    exact isClosed_eq hleft hright
  let nashData : QuittingTerminalSemanticSpinePoint ι ×
      QuittingTerminalSemanticSpinePoint ι →
      Payoff ι × QuittingRootSimplex ι :=
    fun edge => (edge.2.1.1, edge.1.2)
  have hnashData : Continuous nashData := by
    dsimp only [nashData]
    fun_prop
  have hnash : IsClosed
      {edge : QuittingTerminalSemanticSpinePoint ι ×
          QuittingTerminalSemanticSpinePoint ι |
        IsεQuittingRootEndpointNash reward edge.2.1.1 0
          (quittingRootOfSimplex edge.1.2)} :=
    (isClosed_isZeroQuittingRootEndpointNash_simplex reward).preimage hnashData
  have heq : {edge : QuittingTerminalSemanticSpinePoint ι ×
        QuittingTerminalSemanticSpinePoint ι |
      edge.1 ∈ box ∧ edge.2 ∈ box ∧
        IsQuittingTerminalSemanticMinimumSpineEdge reward edge.1 edge.2} =
      {edge | edge.1 ∈ box} ∩
        ({edge | edge.2 ∈ box} ∩
          ({edge | edge.1.1 = quittingTerminalSemanticPrefix reward
              (quittingRootOfSimplex edge.1.2) edge.2.1} ∩
            {edge | IsεQuittingRootEndpointNash reward edge.2.1.1 0
              (quittingRootOfSimplex edge.1.2)})) := by
    ext edge
    simp [IsQuittingTerminalSemanticMinimumSpineEdge]
  rw [heq]
  exact hcurrentBox.inter (htailBox.inter (hprefix.inter hnash))

/-- Every point of a minimum-total-debt fiber has an exact semantic-prefix
predecessor in the same fiber. -/
theorem exists_quittingTerminalSemanticMinimumSpinePredecessor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate)
    (tail : QuittingTerminalSemanticSpinePoint ι)
    (htail : tail ∈ quittingTerminalSemanticMinimumSpineBox reward base) :
    ∃ current,
      current ∈ quittingTerminalSemanticMinimumSpineBox reward base ∧
        IsQuittingTerminalSemanticMinimumSpineEdge reward current tail := by
  obtain ⟨simplexRoot, hnashEndpoint⟩ :=
    exists_isZeroQuittingRootEndpointNash_simplex reward tail.1.1
  let root := quittingRootOfSimplex simplexRoot
  let currentPair := quittingTerminalSemanticPrefix reward root tail.1
  have hnash : IsεQuittingRootNash reward tail.1.1 0 root :=
    (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail.1.1 root).mp hnashEndpoint
  have htailMin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum tail.1 ≤
        quittingTerminalSemanticDebtSum candidate := by
    intro candidate hcandidate
    rw [htail.2]
    exact hmin candidate hcandidate
  have hcurrentCarrier : currentPair ∈
      quittingTerminalSemanticCarrier reward :=
    quittingTerminalSemanticPrefix_mem_carrier
      reward root tail.1 hM hreward htail.1
  have hcoordinate : ∀ who,
      quittingTerminalSemanticDebt currentPair who =
        quittingTerminalSemanticDebt tail.1 who :=
    quittingTerminalSemanticDebt_prefix_eq_of_minimum
      reward tail.1 root hM hreward htail.1 htailMin hnash
  have hsum : quittingTerminalSemanticDebtSum currentPair =
      quittingTerminalSemanticDebtSum tail.1 := by
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_congr rfl fun who _ => hcoordinate who
  refine ⟨(currentPair, simplexRoot), ⟨hcurrentCarrier, ?_⟩, rfl, ?_⟩
  · exact hsum.trans htail.2
  · exact hnashEndpoint

/-- Compact predecessor system on the minimum semantic fiber. -/
def quittingTerminalSemanticMinimumSerialRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hbase : base ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate) :
    CompactSerialRelation (QuittingTerminalSemanticSpinePoint ι) where
  box := quittingTerminalSemanticMinimumSpineBox reward base
  relation := IsQuittingTerminalSemanticMinimumSpineEdge reward
  box_nonempty :=
    quittingTerminalSemanticMinimumSpineBox_nonempty reward base hbase
  box_compact :=
    quittingTerminalSemanticMinimumSpineBox_isCompact reward base hM hreward
  relationGraph_closed :=
    isClosed_quittingTerminalSemanticMinimumSpineEdgeGraph
      reward base hM hreward
  predecessor_exists :=
    exists_quittingTerminalSemanticMinimumSpinePredecessor
      reward base hM hreward hmin

/-- **Minimum-semantic inverse limit.**  A minimum carrier point generates an
infinite state-matched chronology of full semantic pairs and exact Nash roots.
Every pair remains in the same minimum-total-debt fiber. -/
theorem exists_infinite_minimumTerminalSemanticSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (base : QuittingTerminalSemanticPair ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hbase : base ∈ quittingTerminalSemanticCarrier reward)
    (hmin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
      quittingTerminalSemanticDebtSum base ≤
        quittingTerminalSemanticDebtSum candidate) :
    ∃ (pair : ℕ → QuittingTerminalSemanticPair ι)
        (root : ℕ → ι → PMF Bool),
      (∀ time, pair time ∈ quittingTerminalSemanticCarrier reward) ∧
      (∀ time, quittingTerminalSemanticDebtSum (pair time) =
        quittingTerminalSemanticDebtSum base) ∧
      (∀ time, pair time = quittingTerminalSemanticPrefix reward
        (root time) (pair (time + 1))) ∧
      (∀ time who, quittingTerminalSemanticDebt (pair time) who =
        quittingTerminalSemanticDebt (pair (time + 1)) who) ∧
      ∀ time, IsεQuittingRootNash reward (pair (time + 1)).1 0
        (root time) := by
  let system := quittingTerminalSemanticMinimumSerialRelation
    reward base hM hreward hbase hmin
  obtain ⟨state, hstateBox, hstateEdge⟩ := system.exists_infiniteChain
  let pair : ℕ → QuittingTerminalSemanticPair ι :=
    fun time => (state time).1
  let root : ℕ → ι → PMF Bool :=
    fun time => quittingRootOfSimplex (state time).2
  refine ⟨pair, root, ?_, ?_, ?_, ?_, ?_⟩
  · intro time
    exact (hstateBox time).1
  · intro time
    exact (hstateBox time).2
  · intro time
    exact (hstateEdge time).1
  · intro time who
    have hnash : IsεQuittingRootNash reward (pair (time + 1)).1 0
        (root time) :=
      (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
        reward (pair (time + 1)).1 (root time)).mp (hstateEdge time).2
    have htailMin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum (pair (time + 1)) ≤
          quittingTerminalSemanticDebtSum candidate := by
      intro candidate hcandidate
      rw [(hstateBox (time + 1)).2]
      exact hmin candidate hcandidate
    have hedge := (hstateEdge time).1
    change pair time = quittingTerminalSemanticPrefix reward
      (root time) (pair (time + 1)) at hedge
    rw [hedge]
    exact quittingTerminalSemanticDebt_prefix_eq_of_minimum
      reward (pair (time + 1)) (root time) hM hreward
        (hstateBox (time + 1)).1 htailMin hnash who
  · intro time
    exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (pair (time + 1)).1 (root time)).mp (hstateEdge time).2

/-- If every outsider Continues purely, the owner's deleted root survival is
exactly one, irrespective of the owner's own hazard. -/
theorem quittingRootOpponentContinueMass_eq_one_of_others_pureContinue
    (root : ι → PMF Bool) (owner : ι)
    (hpure : ∀ player, player ≠ owner →
      root player = PMF.pure false) :
    quittingRootOpponentContinueMass root owner = 1 := by
  have hupdate : Function.update root owner (PMF.pure false) =
      (quittingAllContinueRoot : ι → PMF Bool) := by
    funext player
    by_cases hplayer : player = owner
    · subst player
      simp [quittingAllContinueRoot]
    · simpa [Function.update_of_ne hplayer, quittingAllContinueRoot] using
        hpure player hplayer
  unfold quittingRootOpponentContinueMass
  rw [hupdate]
  simp [quittingStationaryContinueMass, quittingAllContinueRoot,
    quittingAllContinueAction]

omit [Fintype ι] in
/-- A root with one distinguished arbitrary marginal and all outsiders pure
Continue is literally the standard solo-stationary root. -/
theorem quittingRoot_eq_soloStationaryRoot_of_pureOutsiders
    (root : ι → PMF Bool) (owner : ι)
    (hpure : ∀ player, player ≠ owner →
      root player = PMF.pure false) :
    root = quittingSoloStationaryRoot owner (root owner) := by
  funext player
  by_cases hplayer : player = owner
  · subst player
    simp [quittingSoloStationaryRoot]
  · rw [hpure player hplayer]
    simp [quittingSoloStationaryRoot, hplayer]

/-- Along a fixed-owner solo-root path, the owner's opponent-only survival
weight is identically one on every finite window.  Thus the ordinary
all-player survival-selection premise of the infinite-path compiler can never
hold on a positive owner-debt spine. -/
theorem quittingOpponentSurvivalWeight_eq_one_of_fixedOwner_pureOutsiders
    (roots : ℕ → ι → PMF Bool) (owner : ι)
    (hpure : ∀ time player, player ≠ owner →
      roots time player = PMF.pure false) :
    ∀ start fuel,
      quittingOpponentSurvivalWeight roots owner start fuel = 1 := by
  intro start fuel
  unfold quittingOpponentSurvivalWeight
  apply Finset.prod_eq_one
  intro offset _
  change quittingRootOpponentContinueMass (roots (start + offset)) owner = 1
  exact quittingRootOpponentContinueMass_eq_one_of_others_pureContinue
    (roots (start + offset)) owner (hpure (start + offset))

/-- **Chronological counterexample dichotomy.**  In the absence of a uniform
payoff, the positive minimum semantic stratum has one of two exact forms.

* A minimum carrier point is a positive-debt all-Continue semantic fixed
  plateau.
* There is an infinite state-matched semantic prefix path with one fixed
  positive-debt owner.  Every root has positive owner hazard, every outsider
  Continues purely, the owner is singleton-tight against the next value, and
  at every date some outsider has a singleton payoff above its next declared
  continuation while still satisfying the root's deterrence inequality.

The second branch is a direct solo-root Nash--Bellman producer.  What remains
outside this theorem is absorption or a return/conditioning argument that
turns the semantic spine into one terminal behavior profile. -/
theorem exists_positiveMinimumPlateau_or_fixedOwnerSoloSemanticSpine_of_no_uniformPayoff
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M)
    (hno : ¬ ∃ payoff : Payoff ι,
      (quittingGame reward).IsUniformEquilibriumPayoff none payoff) :
    (∃ pair : QuittingTerminalSemanticPair ι,
        pair ∈ quittingTerminalSemanticCarrier reward ∧
        (∀ candidate ∈ quittingTerminalSemanticCarrier reward,
          quittingTerminalSemanticDebtSum pair ≤
            quittingTerminalSemanticDebtSum candidate) ∧
        (∃ who, 0 < quittingTerminalSemanticDebt pair who) ∧
        IsεQuittingRootNash reward pair.1 0
          (quittingAllContinueRoot : ι → PMF Bool) ∧
        quittingTerminalSemanticPrefix reward quittingAllContinueRoot pair =
          pair) ∨
      ∃ (pair : ℕ → QuittingTerminalSemanticPair ι)
          (root : ℕ → ι → PMF Bool) (owner : ι) (debt : ℝ),
        0 < debt ∧
        (∀ time, pair time ∈ quittingTerminalSemanticCarrier reward) ∧
        (∀ time candidate,
          candidate ∈ quittingTerminalSemanticCarrier reward →
          quittingTerminalSemanticDebtSum (pair time) ≤
            quittingTerminalSemanticDebtSum candidate) ∧
        (∀ time, pair time = quittingTerminalSemanticPrefix reward
          (root time) (pair (time + 1))) ∧
        (∀ time, IsεQuittingRootNash reward (pair (time + 1)).1 0
          (root time)) ∧
        (∀ time, ¬ IsεQuittingRootNash reward (pair time).1 0
          (quittingAllContinueRoot : ι → PMF Bool)) ∧
        (∀ time, quittingTerminalSemanticDebt (pair time) owner = debt) ∧
        (∀ time player, player ≠ owner →
          quittingTerminalSemanticDebt (pair time) player = 0) ∧
        (∀ time, 0 < (root time owner true).toReal) ∧
        (∀ time player, player ≠ owner →
          root time player = PMF.pure false) ∧
        (∀ time, root time =
          quittingSoloStationaryRoot owner (root time owner)) ∧
        (∀ start fuel,
          quittingOpponentSurvivalWeight root owner start fuel = 1) ∧
        (∀ time, reward (quittingSingletonTerminal owner) owner =
          (pair (time + 1)).1 owner) ∧
        ∀ time, ∃ blocker, blocker ≠ owner ∧
          (pair (time + 1)).1 blocker <
            reward (quittingSingletonTerminal blocker) blocker ∧
          quittingRootQuitPayoff reward (pair (time + 1)).1
              (root time) blocker ≤
            quittingRootContinuePayoff reward (pair (time + 1)).1
              (root time) blocker := by
  obtain ⟨base, _selectedRoot, hbase, _hnashBase, hmin, hpositive, _hface⟩ :=
    exists_positive_minimumTerminalSemanticDebt_face_of_no_uniformPayoff
      reward hM hreward hno
  have hbaseDebtNonneg : ∀ player,
      0 ≤ quittingTerminalSemanticDebt base player :=
    quittingTerminalSemanticDebt_nonneg_of_mem_carrier
      reward hM hreward hbase
  have hbaseSumPositive : 0 < quittingTerminalSemanticDebtSum base := by
    obtain ⟨who, hwho⟩ := hpositive
    unfold quittingTerminalSemanticDebtSum
    exact Finset.sum_pos' (fun player _ => hbaseDebtNonneg player)
      ⟨who, Finset.mem_univ who, hwho⟩
  by_cases hplateau : ∃ pair : QuittingTerminalSemanticPair ι,
      pair ∈ quittingTerminalSemanticCarrier reward ∧
      quittingTerminalSemanticDebtSum pair =
        quittingTerminalSemanticDebtSum base ∧
      IsεQuittingRootNash reward pair.1 0
        (quittingAllContinueRoot : ι → PMF Bool)
  · obtain ⟨pair, hpair, hsum, hnashAll⟩ := hplateau
    have hpairMin : ∀ candidate ∈ quittingTerminalSemanticCarrier reward,
        quittingTerminalSemanticDebtSum pair ≤
          quittingTerminalSemanticDebtSum candidate := by
      intro candidate hcandidate
      rw [hsum]
      exact hmin candidate hcandidate
    have hpairDebtNonneg : ∀ player,
        0 ≤ quittingTerminalSemanticDebt pair player :=
      quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hM hreward hpair
    have hpairPositive : ∃ player,
        0 < quittingTerminalSemanticDebt pair player := by
      by_contra hnot
      have hzero : ∀ player,
          quittingTerminalSemanticDebt pair player = 0 := by
        intro player
        exact le_antisymm
          (le_of_not_gt fun hpos => hnot ⟨player, hpos⟩)
          (hpairDebtNonneg player)
      have hsumZero : quittingTerminalSemanticDebtSum pair = 0 := by
        unfold quittingTerminalSemanticDebtSum
        simp [hzero]
      rw [hsumZero] at hsum
      linarith
    exact Or.inl ⟨pair, hpair, hpairMin, hpairPositive, hnashAll,
      quittingTerminalSemanticPrefix_allContinue_eq_of_isZeroNash
        reward pair hpairDebtNonneg hnashAll⟩
  · obtain ⟨pair, root, hpairCarrier, hpairSum, hprefix, hdebtStep,
        hnash⟩ :=
      exists_infinite_minimumTerminalSemanticSpine
        reward base hM hreward hbase hmin
    have hpairMin : ∀ time candidate,
        candidate ∈ quittingTerminalSemanticCarrier reward →
        quittingTerminalSemanticDebtSum (pair time) ≤
          quittingTerminalSemanticDebtSum candidate := by
      intro time candidate hcandidate
      rw [hpairSum time]
      exact hmin candidate hcandidate
    have hpairDebtNonneg : ∀ time player,
        0 ≤ quittingTerminalSemanticDebt (pair time) player := by
      intro time
      exact quittingTerminalSemanticDebt_nonneg_of_mem_carrier
        reward hM hreward (hpairCarrier time)
    have htimeZeroPositive : ∃ owner,
        0 < quittingTerminalSemanticDebt (pair 0) owner := by
      by_contra hnot
      have hzero : ∀ player,
          quittingTerminalSemanticDebt (pair 0) player = 0 := by
        intro player
        exact le_antisymm
          (le_of_not_gt fun hpos => hnot ⟨player, hpos⟩)
          (hpairDebtNonneg 0 player)
      have hsumZero : quittingTerminalSemanticDebtSum (pair 0) = 0 := by
        unfold quittingTerminalSemanticDebtSum
        simp [hzero]
      linarith [hpairSum 0, hsumZero, hbaseSumPositive]
    obtain ⟨owner, hownerPositiveZero⟩ := htimeZeroPositive
    let debt := quittingTerminalSemanticDebt (pair 0) owner
    have hdebtConstant : ∀ time,
        quittingTerminalSemanticDebt (pair time) owner = debt := by
      intro time
      induction time with
      | zero => rfl
      | succ time ih =>
          calc
            quittingTerminalSemanticDebt (pair (time + 1)) owner =
                quittingTerminalSemanticDebt (pair time) owner :=
              (hdebtStep time owner).symm
            _ = debt := ih
    have hownerPositive : ∀ time,
        0 < quittingTerminalSemanticDebt (pair time) owner := by
      intro time
      rw [hdebtConstant time]
      exact hownerPositiveZero
    have hnoPlateauAt : ∀ time,
        ¬ IsεQuittingRootNash reward (pair time).1 0
          (quittingAllContinueRoot : ι → PMF Bool) := by
      intro time hnashAll
      exact hplateau ⟨pair time, hpairCarrier time, hpairSum time, hnashAll⟩
    have hdeterrence : ∀ time,
        (∀ player, 0 < quittingTerminalSemanticDebt
          (pair (time + 1)) player → player = owner) ∧
        0 < (root time owner true).toReal ∧
        reward (quittingSingletonTerminal owner) owner =
          (pair (time + 1)).1 owner ∧
        (∀ player, player ≠ owner →
          root time player = PMF.pure false) ∧
        ∃ blocker, blocker ≠ owner ∧
          (pair (time + 1)).1 blocker <
            reward (quittingSingletonTerminal blocker) blocker ∧
          quittingRootQuitPayoff reward (pair (time + 1)).1
              (root time) blocker ≤
            quittingRootContinuePayoff reward (pair (time + 1)).1
              (root time) blocker := by
      intro time
      have halt := quittingTerminalSemantic_minimum_stratum_alternative
        reward (pair (time + 1)) (root time) hM hreward
          (hpairCarrier (time + 1)) (hpairMin (time + 1)) (hnash time)
          owner (hownerPositive (time + 1))
      rcases halt with hall | ⟨selectedOwner, blocker, hselectedPositive,
          hunique, hblockerNe, hblockerGain, hselectedQuit, hselectedTight,
          hpure, hendpoint⟩
      · exact absurd hall.1 (hnoPlateauAt (time + 1))
      · have hownerEq : owner = selectedOwner :=
          hunique owner (hownerPositive (time + 1))
        subst selectedOwner
        exact ⟨hunique, hselectedQuit, hselectedTight, hpure,
          blocker, hblockerNe, hblockerGain,
          hendpoint blocker hblockerNe⟩
    have hotherDebtZero : ∀ time player, player ≠ owner →
        quittingTerminalSemanticDebt (pair time) player = 0 := by
      intro time player hne
      have hunique := (hdeterrence time).1
      have hnotPositive : ¬ 0 <
          quittingTerminalSemanticDebt (pair (time + 1)) player := by
        intro hpositivePlayer
        exact hne (hunique player hpositivePlayer)
      have hzeroNext : quittingTerminalSemanticDebt
          (pair (time + 1)) player = 0 :=
        le_antisymm (le_of_not_gt hnotPositive)
          (hpairDebtNonneg (time + 1) player)
      exact (hdebtStep time player).trans hzeroNext
    have hpureAll : ∀ time player, player ≠ owner →
        root time player = PMF.pure false := by
      intro time player hne
      exact (hdeterrence time).2.2.2.1 player hne
    have hrootSolo : ∀ time, root time =
        quittingSoloStationaryRoot owner (root time owner) := by
      intro time
      exact quittingRoot_eq_soloStationaryRoot_of_pureOutsiders
        (root time) owner (hpureAll time)
    have hownerSurvival : ∀ start fuel,
        quittingOpponentSurvivalWeight root owner start fuel = 1 :=
      quittingOpponentSurvivalWeight_eq_one_of_fixedOwner_pureOutsiders
        root owner hpureAll
    refine Or.inr ⟨pair, root, owner, debt, hownerPositiveZero,
      hpairCarrier, hpairMin, hprefix, hnash, hnoPlateauAt, hdebtConstant,
      hotherDebtZero, ?_, hpureAll, hrootSolo, hownerSurvival, ?_, ?_⟩
    · intro time
      exact (hdeterrence time).2.1
    · intro time
      exact (hdeterrence time).2.2.1
    · intro time
      exact (hdeterrence time).2.2.2.2

end GameTheory
