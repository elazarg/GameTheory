/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Existence.NashExistenceMixed
import Math.Topology.CompactSerialRelation
import GameTheory.Concepts.Stochastic.QuittingRootSuccessorCertificate
import GameTheory.Concepts.Stochastic.QuittingTerminalUniformization
import Math.ProbabilityMassFunction.Simplex

/-!
# Exact Nash--Bellman spines for finite quitting games

For every bounded finite quitting payoff table, one-stage mixed Nash
existence defines a predecessor-serial Bellman correspondence on a compact
payoff cube.  The compact serial-relation inverse limit then produces a
bounded infinite sequence of continuation values and mixed roots satisfying
the exact Bellman equation and exact root Nash inequalities at every time.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Product of Boolean mixed-action simplices used as a topological model of
quitting roots. -/
abbrev QuittingRootSimplex (ι : Type) [Fintype ι] :=
  ∀ _ : ι, stdSimplex ℝ Bool

/-- Convert simplex coordinates to the corresponding profile of finite
probability mass functions. -/
def quittingRootOfSimplex (root : QuittingRootSimplex ι) :
    ι → PMF Bool :=
  fun who => (stdSimplexEquiv (α := Bool)).symm (root who)

omit [DecidableEq ι] in
@[simp] theorem quittingRootOfSimplex_apply_toReal
    (root : QuittingRootSimplex ι) (who : ι) (action : Bool) :
    ((quittingRootOfSimplex root who) action).toReal = root who action := by
  simp [quittingRootOfSimplex, stdSimplexEquiv_symm_apply]

/-- The expected quitting payoff in simplex coordinates is a finite
multilinear sum. -/
theorem quittingRootExpectedPayoff_simplex_eq_sum
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : QuittingRootSimplex ι) (who : ι) :
    quittingRootExpectedPayoff reward continuation
        (quittingRootOfSimplex root) who =
      ∑ action : ι → Bool,
        (∏ player, root player (action player)) *
          quittingRootPayoff reward continuation action who := by
  unfold quittingRootExpectedPayoff
  rw [expect_eq_sum]
  apply Finset.sum_congr rfl
  intro action _
  congr 1
  simp [pmfPi_apply, quittingRootOfSimplex]

omit [DecidableEq ι] in
/- Joint continuity in the continuation vector and all simplex root
coordinates. -/
theorem continuous_quittingRootExpectedPayoff_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootExpectedPayoff reward point.1
        (quittingRootOfSimplex point.2) who) := by
  classical
  rw [show (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootExpectedPayoff reward point.1
        (quittingRootOfSimplex point.2) who) =
      (fun point =>
        ∑ action : ι → Bool,
          (∏ player, point.2 player (action player)) *
            quittingRootPayoff reward point.1 action who) by
    funext point
    exact quittingRootExpectedPayoff_simplex_eq_sum
      reward point.1 point.2 who]
  refine continuous_finsetSum
    (s := (Finset.univ : Finset (ι → Bool))) ?_
  intro action _
  refine (continuous_finsetProd
    (s := (Finset.univ : Finset ι)) ?_).mul ?_
  · intro player _
    exact (continuous_apply (action player)).comp
      (continuous_subtype_val.comp
        ((continuous_apply player).comp continuous_snd))
  · by_cases hquit : (quittingQuitters action).Nonempty
    · simpa [quittingRootPayoff, hquit] using
        (continuous_const : Continuous
          (fun _ : Payoff ι × QuittingRootSimplex ι =>
            reward ⟨quittingQuitters action, hquit⟩ who))
    · simp only [quittingRootPayoff, dif_neg hquit]
      exact (continuous_apply who).comp continuous_fst

/-- Replace one simplex marginal by a pure Boolean action. -/
def quittingRootSimplexUpdate
    (root : QuittingRootSimplex ι) (who : ι) (action : Bool) :
    QuittingRootSimplex ι :=
  Function.update root who (stdSimplexEquiv (PMF.pure action))

/-- Simplex update agrees with PMF-profile update. -/
theorem quittingRootOfSimplex_update
    (root : QuittingRootSimplex ι) (who : ι) (action : Bool) :
    quittingRootOfSimplex (quittingRootSimplexUpdate root who action) =
      Function.update (quittingRootOfSimplex root) who (PMF.pure action) := by
  funext player
  by_cases hplayer : player = who
  · subst player
    simp [quittingRootSimplexUpdate, quittingRootOfSimplex]
  · simp [quittingRootSimplexUpdate, quittingRootOfSimplex,
      Function.update_of_ne hplayer]

/-- Replacing one simplex coordinate by a fixed pure action is continuous. -/
theorem continuous_quittingRootSimplexUpdate (who : ι) (action : Bool) :
    Continuous (fun root : QuittingRootSimplex ι =>
      quittingRootSimplexUpdate root who action) := by
  apply continuous_pi
  intro player
  by_cases hplayer : player = who
  · subst player
    simpa [quittingRootSimplexUpdate] using
      (continuous_const : Continuous (fun _ : QuittingRootSimplex ι =>
        stdSimplexEquiv (PMF.pure action)))
  · simpa [quittingRootSimplexUpdate, Function.update_of_ne hplayer] using
      (continuous_apply player : Continuous
        (fun root : QuittingRootSimplex ι => root player))

/-- Pure-Quit payoff is jointly continuous in the continuation and simplex
root. -/
theorem continuous_quittingRootQuitPayoff_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootQuitPayoff reward point.1
        (quittingRootOfSimplex point.2) who) := by
  have hmap : Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      (point.1, quittingRootSimplexUpdate point.2 who true)) :=
    continuous_fst.prodMk
      ((continuous_quittingRootSimplexUpdate who true).comp continuous_snd)
  have hcontinuous :=
    (continuous_quittingRootExpectedPayoff_simplex reward who).comp hmap
  rw [show (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootQuitPayoff reward point.1
        (quittingRootOfSimplex point.2) who) =
      ((fun point : Payoff ι × QuittingRootSimplex ι =>
          quittingRootExpectedPayoff reward point.1
            (quittingRootOfSimplex point.2) who) ∘
        fun point =>
          (point.1, quittingRootSimplexUpdate point.2 who true)) by
    funext point
    simp only [Function.comp_apply, quittingRootQuitPayoff]
    rw [quittingRootOfSimplex_update]]
  exact hcontinuous

/-- Pure-Continue payoff is jointly continuous in the continuation and
simplex root. -/
theorem continuous_quittingRootContinuePayoff_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootContinuePayoff reward point.1
        (quittingRootOfSimplex point.2) who) := by
  have hmap : Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      (point.1, quittingRootSimplexUpdate point.2 who false)) :=
    continuous_fst.prodMk
      ((continuous_quittingRootSimplexUpdate who false).comp continuous_snd)
  have hcontinuous :=
    (continuous_quittingRootExpectedPayoff_simplex reward who).comp hmap
  rw [show (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootContinuePayoff reward point.1
        (quittingRootOfSimplex point.2) who) =
      ((fun point : Payoff ι × QuittingRootSimplex ι =>
          quittingRootExpectedPayoff reward point.1
            (quittingRootOfSimplex point.2) who) ∘
        fun point =>
          (point.1, quittingRootSimplexUpdate point.2 who false)) by
    funext point
    simp only [Function.comp_apply, quittingRootContinuePayoff]
    rw [quittingRootOfSimplex_update]]
  exact hcontinuous

/-- The pure Quit-minus-Continue difference is jointly continuous. -/
theorem continuous_quittingRootEndpointDifference_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootEndpointDifference reward point.1
        (quittingRootOfSimplex point.2) who) := by
  exact (continuous_quittingRootQuitPayoff_simplex reward who).sub
    (continuous_quittingRootContinuePayoff_simplex reward who)

/-- Exact endpoint-Nash constraints form a closed subset of continuation
vectors and simplex roots. -/
theorem isClosed_isZeroQuittingRootEndpointNash_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    IsClosed {point : Payoff ι × QuittingRootSimplex ι |
      IsεQuittingRootEndpointNash reward point.1 0
        (quittingRootOfSimplex point.2)} := by
  have hcoordinate : ∀ who : ι,
      Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
        point.2 who false) ∧
      Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
        point.2 who true) := by
    intro who
    constructor
    · exact (continuous_apply false).comp
        (continuous_subtype_val.comp
          ((continuous_apply who).comp continuous_snd))
    · exact (continuous_apply true).comp
        (continuous_subtype_val.comp
          ((continuous_apply who).comp continuous_snd))
  have hclosed : ∀ who : ι, IsClosed
      {point : Payoff ι × QuittingRootSimplex ι |
        point.2 who false *
            quittingRootEndpointDifference reward point.1
              (quittingRootOfSimplex point.2) who ≤ 0 ∧
          0 ≤ point.2 who true *
            quittingRootEndpointDifference reward point.1
              (quittingRootOfSimplex point.2) who} := by
    intro who
    exact (isClosed_le
      ((hcoordinate who).1.mul
        (continuous_quittingRootEndpointDifference_simplex reward who))
      continuous_const).inter
      (isClosed_le continuous_const
        ((hcoordinate who).2.mul
          (continuous_quittingRootEndpointDifference_simplex reward who)))
  have hinter : IsClosed (⋂ who : ι,
      {point : Payoff ι × QuittingRootSimplex ι |
        point.2 who false *
            quittingRootEndpointDifference reward point.1
              (quittingRootOfSimplex point.2) who ≤ 0 ∧
          0 ≤ point.2 who true *
            quittingRootEndpointDifference reward point.1
              (quittingRootOfSimplex point.2) who}) :=
    isClosed_iInter hclosed
  have heq : {point : Payoff ι × QuittingRootSimplex ι |
      IsεQuittingRootEndpointNash reward point.1 0
        (quittingRootOfSimplex point.2)} =
      ⋂ who : ι,
        {point : Payoff ι × QuittingRootSimplex ι |
          point.2 who false *
              quittingRootEndpointDifference reward point.1
                (quittingRootOfSimplex point.2) who ≤ 0 ∧
            0 ≤ point.2 who true *
              quittingRootEndpointDifference reward point.1
                (quittingRootOfSimplex point.2) who} := by
    ext point
    simp only [IsεQuittingRootEndpointNash,
      quittingRootOfSimplex_apply_toReal, neg_zero, Set.mem_setOf_eq,
      Set.mem_iInter]
  rw [heq]
  exact hinter

/-- The one-stage normal-form game obtained from a continuation payoff
vector. -/
abbrev quittingContinuationGame
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) : KernelGame ι :=
  KernelGame.ofPureEU (fun _ => Bool)
    (fun action who => quittingRootPayoff reward continuation action who)

omit [DecidableEq ι] in
/- Mixed expected utility in the one-stage normal form is exactly the
quitting root expected payoff. -/
theorem quittingContinuationGame_mixedExtension_eu
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    (quittingContinuationGame reward continuation).mixedExtension.eu
        root who =
      quittingRootExpectedPayoff reward continuation root who := by
  letI : Finite (quittingContinuationGame reward continuation).Outcome := by
    change Finite (ι → Bool)
    infer_instance
  change (KernelGame.ofPureEU (fun _ : ι => Bool)
      (fun action who =>
        quittingRootPayoff reward continuation action who)).mixedExtension.eu
      root who = _
  rw [KernelGame.mixedExtension_eu]
  simp only [KernelGame.eu_ofPureEU]
  rfl

/-- Nash equilibrium in the one-stage normal form is exact quitting-root
Nash. -/
theorem quittingContinuationGame_isNash_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) :
    (quittingContinuationGame reward continuation).mixedExtension.IsNash root ↔
      IsεQuittingRootNash reward continuation 0 root := by
  change (KernelGame.ofPureEU (fun _ : ι => Bool)
      (fun action who =>
        quittingRootPayoff reward continuation action who)).mixedExtension.IsNash
      root ↔ _
  simp only [KernelGame.IsNash, KernelGame.mixedExtension_Strategy,
    KernelGame.ofPureEU_Strategy, IsεQuittingRootNash, add_zero, ge_iff_le,
    quittingContinuationGame_mixedExtension_eu]

/-! ## Compact Nash--Bellman correspondence -/

omit [DecidableEq ι] in
/- Successor payoff is jointly continuous in the tail vector and simplex
root. -/
theorem continuous_quittingRootSuccessorPayoff_simplex
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
      quittingRootSuccessorPayoff reward point.1
        (quittingRootOfSimplex point.2)) := by
  change Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
    fun who => quittingRootExpectedPayoff reward point.1
      (quittingRootOfSimplex point.2) who)
  exact continuous_pi fun who =>
    continuous_quittingRootExpectedPayoff_simplex reward who

omit [DecidableEq ι] in
/- A common bound on terminal and continuation payoffs bounds each expected
root payoff. -/
theorem abs_quittingRootExpectedPayoff_le_bound
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation : Payoff ι) (root : ι → PMF Bool) (who : ι)
    {M : ℝ} (hreward : ∀ S player, |reward S player| ≤ M)
    (hcontinuation : ∀ player, |continuation player| ≤ M) :
    |quittingRootExpectedPayoff reward continuation root who| ≤ M := by
  unfold quittingRootExpectedPayoff
  exact abs_expect_le_of_abs_le (pmfPi root)
    (fun action => quittingRootPayoff reward continuation action who)
    (fun action => abs_quittingRootPayoff_le reward continuation
      hreward hcontinuation action who)

/-- State space carrying the current payoff vector and the root which maps
the next payoff vector back to it. -/
abbrev QuittingNashBellmanPoint (ι : Type) [Fintype ι] :=
  Payoff ι × QuittingRootSimplex ι

/-- Bounded payoff states; the simplex component is already compact. -/
def quittingNashBellmanBox (M : ℝ) :
    Set (QuittingNashBellmanPoint ι) :=
  {point | point.1 ∈ Set.Icc (fun _ => -M) (fun _ => M)}

/-- One exact backward Nash--Bellman edge.  The tail state's simplex
coordinate is irrelevant; it is retained so consecutive roots live in the
same compact state space. -/
def IsQuittingNashBellmanEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (current tail : QuittingNashBellmanPoint ι) : Prop :=
  current.1 = quittingRootSuccessorPayoff reward tail.1
      (quittingRootOfSimplex current.2) ∧
    IsεQuittingRootEndpointNash reward tail.1 0
      (quittingRootOfSimplex current.2)

omit [DecidableEq ι] in
/- The bounded Nash--Bellman state box is nonempty. -/
theorem quittingNashBellmanBox_nonempty {M : ℝ} (hM : 0 ≤ M) :
    (quittingNashBellmanBox (ι := ι) M).Nonempty := by
  let root : QuittingRootSimplex ι :=
    fun _ => stdSimplexEquiv (PMF.pure false)
  refine ⟨((0 : Payoff ι), root), ?_⟩
  change (0 : Payoff ι) ∈ Set.Icc (fun _ => -M) (fun _ => M)
  constructor
  · intro who
    dsimp
    linarith
  · intro who
    dsimp
    exact hM

omit [DecidableEq ι] in
/- The bounded Nash--Bellman state box is compact. -/
theorem quittingNashBellmanBox_isCompact (M : ℝ) :
    IsCompact (quittingNashBellmanBox (ι := ι) M) := by
  have heq : quittingNashBellmanBox (ι := ι) M =
      Set.Icc (fun _ : ι => -M) (fun _ => M) ×ˢ
        (Set.univ : Set (QuittingRootSimplex ι)) := by
    ext point
    simp [quittingNashBellmanBox]
  rw [heq]
  exact isCompact_Icc.prod isCompact_univ

/-- Exact bounded Nash--Bellman edges form a closed graph. -/
theorem isClosed_quittingNashBellmanEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (M : ℝ) :
    IsClosed {edge : QuittingNashBellmanPoint ι ×
        QuittingNashBellmanPoint ι |
      edge.1 ∈ quittingNashBellmanBox M ∧
        edge.2 ∈ quittingNashBellmanBox M ∧
        IsQuittingNashBellmanEdge reward edge.1 edge.2} := by
  let edgeData : (QuittingNashBellmanPoint ι ×
      QuittingNashBellmanPoint ι) →
      Payoff ι × QuittingRootSimplex ι :=
    fun edge => (edge.2.1, edge.1.2)
  have hedgeData : Continuous edgeData := by
    dsimp only [edgeData]
    fun_prop
  have hbox : IsClosed (quittingNashBellmanBox (ι := ι) M) :=
    (quittingNashBellmanBox_isCompact (ι := ι) M).isClosed
  have hcurrentBox : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        edge.1 ∈ quittingNashBellmanBox M} :=
    hbox.preimage continuous_fst
  have htailBox : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        edge.2 ∈ quittingNashBellmanBox M} :=
    hbox.preimage continuous_snd
  have hbellman : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        edge.1.1 = quittingRootSuccessorPayoff reward edge.2.1
          (quittingRootOfSimplex edge.1.2)} := by
    exact isClosed_eq
      (continuous_fst.comp continuous_fst)
      ((continuous_quittingRootSuccessorPayoff_simplex reward).comp hedgeData)
  have hnash : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        IsεQuittingRootEndpointNash reward edge.2.1 0
          (quittingRootOfSimplex edge.1.2)} := by
    exact (isClosed_isZeroQuittingRootEndpointNash_simplex reward).preimage
      hedgeData
  have heq : {edge : QuittingNashBellmanPoint ι ×
        QuittingNashBellmanPoint ι |
      edge.1 ∈ quittingNashBellmanBox M ∧
        edge.2 ∈ quittingNashBellmanBox M ∧
        IsQuittingNashBellmanEdge reward edge.1 edge.2} =
      {edge | edge.1 ∈ quittingNashBellmanBox M} ∩
        ({edge | edge.2 ∈ quittingNashBellmanBox M} ∩
          ({edge | edge.1.1 = quittingRootSuccessorPayoff reward edge.2.1
              (quittingRootOfSimplex edge.1.2)} ∩
            {edge | IsεQuittingRootEndpointNash reward edge.2.1 0
              (quittingRootOfSimplex edge.1.2)})) := by
    ext edge
    simp [IsQuittingNashBellmanEdge]
  rw [heq]
  exact hcurrentBox.inter (htailBox.inter (hbellman.inter hnash))

/-- Every bounded tail state has a bounded exact Nash--Bellman predecessor. -/
theorem exists_quittingNashBellmanPredecessor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hreward : ∀ S player, |reward S player| ≤ M)
    (tail : QuittingNashBellmanPoint ι)
    (htail : tail ∈ quittingNashBellmanBox M) :
    ∃ current, current ∈ quittingNashBellmanBox M ∧
      IsQuittingNashBellmanEdge reward current tail := by
  have htailBound : ∀ who, |tail.1 who| ≤ M := by
    intro who
    exact abs_le.mpr ⟨htail.1 who, htail.2 who⟩
  have hexists : ∃ root : ι → PMF Bool,
      IsεQuittingRootNash reward tail.1 0 root := by
    let stageGame : KernelGame ι :=
      quittingContinuationGame reward tail.1
    haveI : ∀ who, Finite (stageGame.Strategy who) :=
      fun who => inferInstanceAs (Finite Bool)
    haveI : ∀ who, Nonempty (stageGame.Strategy who) :=
      fun who => inferInstanceAs (Nonempty Bool)
    haveI : Finite stageGame.Outcome :=
      inferInstanceAs (Finite (ι → Bool))
    obtain ⟨root, hroot⟩ := stageGame.mixed_nash_exists
    refine ⟨root, ?_⟩
    exact (quittingContinuationGame_isNash_iff reward tail.1 root).1 hroot
  obtain ⟨root, hnash⟩ := hexists
  let simplexRoot : QuittingRootSimplex ι :=
    fun who => stdSimplexEquiv (root who)
  have hroot : quittingRootOfSimplex simplexRoot = root := by
    funext who
    exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (root who)
  let currentValue : Payoff ι :=
    quittingRootSuccessorPayoff reward tail.1 root
  have hcurrentBound : ∀ who, |currentValue who| ≤ M := by
    intro who
    exact abs_quittingRootExpectedPayoff_le_bound reward tail.1 root who
      hreward htailBound
  have hcurrentMem : currentValue ∈
      Set.Icc (fun _ : ι => -M) (fun _ => M) := by
    constructor
    · intro who
      exact (abs_le.mp (hcurrentBound who)).1
    · intro who
      exact (abs_le.mp (hcurrentBound who)).2
  refine ⟨(currentValue, simplexRoot), hcurrentMem, ?_, ?_⟩
  · dsimp only [currentValue]
    rw [hroot]
  · rw [hroot]
    exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward tail.1 root).2 hnash

/-- The compact exact Nash--Bellman predecessor correspondence. -/
def quittingNashBellmanSerialRelation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (M : ℝ) (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    CompactSerialRelation (QuittingNashBellmanPoint ι) where
  box := quittingNashBellmanBox M
  relation := IsQuittingNashBellmanEdge reward
  box_nonempty := quittingNashBellmanBox_nonempty hM
  box_compact := quittingNashBellmanBox_isCompact M
  relationGraph_closed := isClosed_quittingNashBellmanEdgeGraph reward M
  predecessor_exists := exists_quittingNashBellmanPredecessor reward hreward

/-! ## Infinite exact spine -/

/-- Every uniformly bounded finite quitting payoff table admits a bounded
infinite exact Nash--Bellman spine. -/
theorem exists_bounded_exact_quittingNashBellmanSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {M : ℝ} (hM : 0 ≤ M)
    (hreward : ∀ S player, |reward S player| ≤ M) :
    ∃ (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
      (∀ time who, |value time who| ≤ M) ∧
      (∀ time, value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) ∧
      ∀ time, IsεQuittingRootNash reward
        (value (time + 1)) 0 (roots time) := by
  let system := quittingNashBellmanSerialRelation reward M hM hreward
  obtain ⟨state, hstateBox, hstateEdge⟩ := system.exists_infiniteChain
  let value : ℕ → Payoff ι := fun time => (state time).1
  let roots : ℕ → ι → PMF Bool :=
    fun time => quittingRootOfSimplex (state time).2
  refine ⟨value, roots, ?_, ?_, ?_⟩
  · intro time who
    exact abs_le.mpr
      ⟨(hstateBox time).1 who, (hstateBox time).2 who⟩
  · intro time
    exact (hstateEdge time).1
  · intro time
    exact (isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash
      reward (value (time + 1)) (roots time)).1 (hstateEdge time).2

/-- Bound-free finite-table wrapper using the canonical quitting reward
bound. -/
theorem exists_exact_quittingNashBellmanSpine
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) :
    ∃ (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
      (∀ time who, |value time who| ≤ quittingRewardBound reward) ∧
      (∀ time, value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) ∧
      ∀ time, IsεQuittingRootNash reward
        (value (time + 1)) 0 (roots time) := by
  exact exists_bounded_exact_quittingNashBellmanSpine reward
    (quittingRewardBound_nonneg reward)
    (abs_reward_le_quittingRewardBound reward)

end GameTheory
