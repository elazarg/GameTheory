/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.MultiOwnerFaceCirculationPath
import GameTheory.Concepts.Stochastic.QuittingJointSurvivalSelection

/-!
# Compact chronological paths from multi-owner face circulations

A face-circulation orbit is generated in the forward affine orientation

`forward (n + 1) = F (row n) (forward n)`.

A chronological quitting path has the opposite orientation: its value at time
`t` is the Bellman predecessor of its value at time `t+1`.  The bridge is to
reverse every finite forward prefix.  Those reversed prefixes satisfy the
chronological equations exactly.  A compact finite-prefix inverse limit then
selects one infinite path.

The selected path keeps three closed pieces of information at every edge:

* the exact Bellman policy-evaluation equation;
* the support-local approximate Nash witness, written as a closed disjunction
  (`probability = 0` or the corresponding endpoint inequality); and
* a uniform positive lower bound on one-stage absorption.

The absorption lower bound has two roles.  It makes the total absorption
charge nonsummable, and it makes joint survival geometric.  The latter selects
the compactly constructed continuation vectors uniquely as the actual
terminal tails of the infinite root path.  A floor above each player's
`quittingPunishmentValue` therefore becomes the individual-rationality input
of `QuittingSupportWitnessPathCompiler.lean`.
-/

noncomputable section

namespace GameTheory

open Finset Filter StochasticGame Math.Probability Math.PMFProduct
open Math.ProbabilityMassFunction Math.Topology

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Hazard rows as simplex roots -/

/-- Simplex-coordinate presentation of the PMF root associated with a real
hazard row. -/
def quittingRootSimplexOfHazard
    (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    QuittingRootSimplex ι :=
  fun who => stdSimplexEquiv (rootOfHazard x hx0 hx1 who)

omit [DecidableEq ι] in
/-- Converting a real hazard row to simplex coordinates and back is exact. -/
@[simp] theorem quittingRootOfSimplex_quittingRootSimplexOfHazard
    (x : ι → ℝ) (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i ≤ 1) :
    quittingRootOfSimplex (quittingRootSimplexOfHazard x hx0 hx1) =
      rootOfHazard x hx0 hx1 := by
  classical
  funext who
  simp [quittingRootOfSimplex, quittingRootSimplexOfHazard]

/-- One-stage absorption, written polynomially in simplex coordinates. -/
def quittingSimplexAbsorptionMass (root : QuittingRootSimplex ι) : ℝ :=
  1 - ∏ who, root who false

omit [DecidableEq ι] in
/-- Simplex-coordinate absorption agrees with the PMF-root definition. -/
theorem quittingSimplexAbsorptionMass_eq_rootAbsorptionMass
    (root : QuittingRootSimplex ι) :
    quittingSimplexAbsorptionMass root =
      quittingRootAbsorptionMass (quittingRootOfSimplex root) := by
  classical
  unfold quittingSimplexAbsorptionMass quittingRootAbsorptionMass
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  simp

omit [DecidableEq ι] in
/-- Simplex-coordinate absorption is continuous. -/
theorem continuous_quittingSimplexAbsorptionMass :
    Continuous (quittingSimplexAbsorptionMass :
      QuittingRootSimplex ι → ℝ) := by
  classical
  unfold quittingSimplexAbsorptionMass
  exact continuous_const.sub
    (continuous_finsetProd (s := (Finset.univ : Finset ι)) fun who _ =>
      (continuous_apply false).comp
        (continuous_subtype_val.comp (continuous_apply who)))

/-! ## A closed support-local root condition -/

/-- Closed simplex form of support-local approximate Nash.  Positivity is
replaced by the equivalent closed disjunction saying that a coordinate is
zero or its endpoint inequality holds. -/
def IsQuittingSimplexRootSupportApproxNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (δ : ℝ) (root : QuittingRootSimplex ι) : Prop :=
  ∀ who,
    (root who true = 0 ∨
      -δ ≤ quittingRootEndpointDifference reward tail
        (quittingRootOfSimplex root) who) ∧
    (root who false = 0 ∨
      quittingRootEndpointDifference reward tail
        (quittingRootOfSimplex root) who ≤ δ)

/-- The closed simplex condition is exactly the PMF support condition. -/
theorem isQuittingSimplexRootSupportApproxNash_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (tail : Payoff ι) (δ : ℝ) (root : QuittingRootSimplex ι) :
    IsQuittingSimplexRootSupportApproxNash reward tail δ root ↔
      IsQuittingRootSupportApproxNash reward tail δ
        (quittingRootOfSimplex root) := by
  constructor
  · intro hclosed who
    constructor
    · intro hpositive
      rcases (hclosed who).1 with hzero | hgap
      · rw [quittingRootOfSimplex_apply_toReal, hzero] at hpositive
        linarith
      · exact hgap
    · intro hpositive
      rcases (hclosed who).2 with hzero | hgap
      · rw [quittingRootOfSimplex_apply_toReal, hzero] at hpositive
        linarith
      · exact hgap
  · intro hsupport who
    have htrue0 : 0 ≤ root who true := (root who).property.1 true
    have hfalse0 : 0 ≤ root who false := (root who).property.1 false
    constructor
    · by_cases hzero : root who true = 0
      · exact Or.inl hzero
      · refine Or.inr ((hsupport who).1 ?_)
        rw [quittingRootOfSimplex_apply_toReal]
        exact lt_of_le_of_ne htrue0 (Ne.symm hzero)
    · by_cases hzero : root who false = 0
      · exact Or.inl hzero
      · refine Or.inr ((hsupport who).2 ?_)
        rw [quittingRootOfSimplex_apply_toReal]
        exact lt_of_le_of_ne hfalse0 (Ne.symm hzero)

/-- Support-local approximate Nash is closed jointly in the tail vector and
simplex root. -/
theorem isClosed_isQuittingSimplexRootSupportApproxNash
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (δ : ℝ) :
    IsClosed {point : Payoff ι × QuittingRootSimplex ι |
      IsQuittingSimplexRootSupportApproxNash reward point.1 δ point.2} := by
  have hcoordinate : ∀ who : ι,
      Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
        point.2 who true) ∧
      Continuous (fun point : Payoff ι × QuittingRootSimplex ι =>
        point.2 who false) := by
    intro who
    constructor
    · exact (continuous_apply true).comp
        (continuous_subtype_val.comp
          ((continuous_apply who).comp continuous_snd))
    · exact (continuous_apply false).comp
        (continuous_subtype_val.comp
          ((continuous_apply who).comp continuous_snd))
  have hgap : ∀ who : ι, Continuous
      (fun point : Payoff ι × QuittingRootSimplex ι =>
        quittingRootEndpointDifference reward point.1
          (quittingRootOfSimplex point.2) who) :=
    continuous_quittingRootEndpointDifference_simplex reward
  have hclosedWho : ∀ who : ι, IsClosed
      (({point : Payoff ι × QuittingRootSimplex ι |
          point.2 who true = 0} ∪
        {point |
          -δ ≤ quittingRootEndpointDifference reward point.1
            (quittingRootOfSimplex point.2) who}) ∩
       ({point |
          point.2 who false = 0} ∪
        {point |
          quittingRootEndpointDifference reward point.1
            (quittingRootOfSimplex point.2) who ≤ δ})) := by
    intro who
    exact ((isClosed_eq (hcoordinate who).1 continuous_const).union
      (isClosed_le continuous_const (hgap who))).inter
      ((isClosed_eq (hcoordinate who).2 continuous_const).union
        (isClosed_le (hgap who) continuous_const))
  have hinter : IsClosed (⋂ who : ι,
      (({point : Payoff ι × QuittingRootSimplex ι |
          point.2 who true = 0} ∪
        {point |
          -δ ≤ quittingRootEndpointDifference reward point.1
            (quittingRootOfSimplex point.2) who}) ∩
       ({point |
          point.2 who false = 0} ∪
        {point |
          quittingRootEndpointDifference reward point.1
            (quittingRootOfSimplex point.2) who ≤ δ}))) :=
    isClosed_iInter hclosedWho
  have heq : {point : Payoff ι × QuittingRootSimplex ι |
      IsQuittingSimplexRootSupportApproxNash reward point.1 δ point.2} =
      ⋂ who : ι,
        (({point : Payoff ι × QuittingRootSimplex ι |
            point.2 who true = 0} ∪
          {point |
            -δ ≤ quittingRootEndpointDifference reward point.1
              (quittingRootOfSimplex point.2) who}) ∩
         ({point |
            point.2 who false = 0} ∪
          {point |
            quittingRootEndpointDifference reward point.1
              (quittingRootOfSimplex point.2) who ≤ δ})) := by
    ext point
    simp [IsQuittingSimplexRootSupportApproxNash]
  rw [heq]
  exact hinter

/-! ## The compact chronological edge system -/

/-- Bounded continuation vectors above a prescribed coordinatewise floor,
paired with arbitrary simplex roots. -/
def quittingCirculationPathBox (bound : ℝ) (lower : Payoff ι) :
    Set (QuittingNashBellmanPoint ι) :=
  quittingNashBellmanBox bound ∩
    {point | ∀ who, lower who ≤ point.1 who}

omit [DecidableEq ι] in
/-- The circulation path box is compact. -/
theorem quittingCirculationPathBox_isCompact
    (bound : ℝ) (lower : Payoff ι) :
    IsCompact (quittingCirculationPathBox (ι := ι) bound lower) := by
  classical
  have hlowerWho : ∀ who : ι, IsClosed
      {point : QuittingNashBellmanPoint ι |
        lower who ≤ point.1 who} := by
    intro who
    exact isClosed_le continuous_const
      ((continuous_apply who).comp continuous_fst)
  have hlower : IsClosed
      {point : QuittingNashBellmanPoint ι |
        ∀ who, lower who ≤ point.1 who} := by
    have heq : {point : QuittingNashBellmanPoint ι |
        ∀ who, lower who ≤ point.1 who} =
        ⋂ who : ι, {point | lower who ≤ point.1 who} := by
      ext point
      simp
    rw [heq]
    exact isClosed_iInter hlowerWho
  have hclosed : IsClosed
      (quittingCirculationPathBox (ι := ι) bound lower) :=
    (quittingNashBellmanBox_isCompact (ι := ι) bound).isClosed.inter hlower
  exact (quittingNashBellmanBox_isCompact (ι := ι) bound).of_isClosed_subset
    hclosed Set.inter_subset_left

omit [DecidableEq ι] in
/-- Coordinatewise absolute and lower bounds put a state in the compact
circulation path box. -/
theorem mem_quittingCirculationPathBox_of_bounds
    {bound : ℝ} {lower value : Payoff ι}
    (root : QuittingRootSimplex ι)
    (hbound : ∀ who, |value who| ≤ bound)
    (hlower : ∀ who, lower who ≤ value who) :
    (value, root) ∈ quittingCirculationPathBox bound lower := by
  classical
  refine ⟨?_, hlower⟩
  constructor
  · intro who
    exact (abs_le.mp (hbound who)).1
  · intro who
    exact (abs_le.mp (hbound who)).2

/-- One chronological edge carrying Bellman evaluation, a support witness,
and a uniform one-stage absorption floor. -/
def IsQuittingCirculationPathEdge
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (δ charge : ℝ)
    (current tail : QuittingNashBellmanPoint ι) : Prop :=
  current.1 = quittingRootSuccessorPayoff reward tail.1
      (quittingRootOfSimplex current.2) ∧
    IsQuittingSimplexRootSupportApproxNash reward tail.1 δ current.2 ∧
    charge ≤ quittingSimplexAbsorptionMass current.2

/-- The box-restricted chronological edge graph is closed. -/
theorem isClosed_quittingCirculationPathEdgeGraph
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (bound : ℝ) (lower : Payoff ι) (δ charge : ℝ) :
    IsClosed {edge : QuittingNashBellmanPoint ι ×
        QuittingNashBellmanPoint ι |
      edge.1 ∈ quittingCirculationPathBox bound lower ∧
      edge.2 ∈ quittingCirculationPathBox bound lower ∧
      IsQuittingCirculationPathEdge reward δ charge edge.1 edge.2} := by
  let edgeData : (QuittingNashBellmanPoint ι ×
      QuittingNashBellmanPoint ι) →
      Payoff ι × QuittingRootSimplex ι :=
    fun edge => (edge.2.1, edge.1.2)
  have hedgeData : Continuous edgeData := by
    dsimp only [edgeData]
    fun_prop
  have hbox : IsClosed
      (quittingCirculationPathBox (ι := ι) bound lower) :=
    (quittingCirculationPathBox_isCompact (ι := ι) bound lower).isClosed
  have hcurrentBox : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        edge.1 ∈ quittingCirculationPathBox bound lower} :=
    hbox.preimage continuous_fst
  have htailBox : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        edge.2 ∈ quittingCirculationPathBox bound lower} :=
    hbox.preimage continuous_snd
  have hbellman : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        edge.1.1 = quittingRootSuccessorPayoff reward edge.2.1
          (quittingRootOfSimplex edge.1.2)} := by
    exact isClosed_eq
      (continuous_fst.comp continuous_fst)
      ((continuous_quittingRootSuccessorPayoff_simplex reward).comp hedgeData)
  have hsupport : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        IsQuittingSimplexRootSupportApproxNash reward edge.2.1 δ
          edge.1.2} :=
    (isClosed_isQuittingSimplexRootSupportApproxNash reward δ).preimage
      hedgeData
  have habsorption : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        charge ≤ quittingSimplexAbsorptionMass edge.1.2} := by
    exact isClosed_le continuous_const
      (continuous_quittingSimplexAbsorptionMass.comp
        (continuous_snd.comp continuous_fst))
  have heq : {edge : QuittingNashBellmanPoint ι ×
        QuittingNashBellmanPoint ι |
      edge.1 ∈ quittingCirculationPathBox bound lower ∧
      edge.2 ∈ quittingCirculationPathBox bound lower ∧
      IsQuittingCirculationPathEdge reward δ charge edge.1 edge.2} =
      {edge | edge.1 ∈ quittingCirculationPathBox bound lower} ∩
      ({edge | edge.2 ∈ quittingCirculationPathBox bound lower} ∩
       ({edge | edge.1.1 = quittingRootSuccessorPayoff reward edge.2.1
          (quittingRootOfSimplex edge.1.2)} ∩
        ({edge | IsQuittingSimplexRootSupportApproxNash reward edge.2.1 δ
          edge.1.2} ∩
         {edge | charge ≤ quittingSimplexAbsorptionMass edge.1.2}))) := by
    ext edge
    simp [IsQuittingCirculationPathEdge]
  rw [heq]
  exact hcurrentBox.inter
    (htailBox.inter (hbellman.inter (hsupport.inter habsorption)))

/-! ## Reversing every finite prefix -/

/-- **Chronological compact extraction.**  A bounded forward Bellman orbit
whose rows carry support witnesses and a positive absorption floor yields one
infinite chronological path carrying the same data. -/
theorem exists_chronologicalSupportPath_of_forwardOrbit
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (row : ℕ → ι → ℝ) (forward : ℕ → Payoff ι)
    (lower : Payoff ι) {δ charge bound : ℝ}
    (hrow0 : ∀ time who, 0 ≤ row time who)
    (hrow1 : ∀ time who, row time who ≤ 1)
    (hforwardBound : ∀ time who, |forward time who| ≤ bound)
    (hforwardLower : ∀ time who, lower who ≤ forward time who)
    (hpolicy : ∀ time,
      forward (time + 1) = quittingRootSuccessorPayoff reward
        (forward time)
        (rootOfHazard (row time) (hrow0 time) (hrow1 time)))
    (hsupport : ∀ time,
      IsQuittingRootSupportApproxNash reward (forward time) δ
        (rootOfHazard (row time) (hrow0 time) (hrow1 time)))
    (habsorption : ∀ time,
      charge ≤ quittingRootAbsorptionMass
        (rootOfHazard (row time) (hrow0 time) (hrow1 time))) :
    ∃ (value : ℕ → Payoff ι) (roots : ℕ → ι → PMF Bool),
      (∀ time who, |value time who| ≤ bound) ∧
      (∀ time who, lower who ≤ value time who) ∧
      (∀ time, value time = quittingRootSuccessorPayoff reward
        (value (time + 1)) (roots time)) ∧
      (∀ time, IsQuittingRootSupportApproxNash reward
        (value (time + 1)) δ (roots time)) ∧
      ∀ time, charge ≤ quittingRootAbsorptionMass (roots time) := by
  let simplexRow : ℕ → QuittingRootSimplex ι :=
    fun time => quittingRootSimplexOfHazard
      (row time) (hrow0 time) (hrow1 time)
  let box : Set (QuittingNashBellmanPoint ι) :=
    quittingCirculationPathBox bound lower
  let relation : QuittingNashBellmanPoint ι →
      QuittingNashBellmanPoint ι → Prop :=
    IsQuittingCirculationPathEdge reward δ charge
  have hbox : IsCompact box :=
    quittingCirculationPathBox_isCompact bound lower
  have hgraph : IsClosed
      {edge : QuittingNashBellmanPoint ι × QuittingNashBellmanPoint ι |
        edge.1 ∈ box ∧ edge.2 ∈ box ∧ relation edge.1 edge.2} := by
    simpa only [box, relation] using
      isClosed_quittingCirculationPathEdgeGraph
        reward bound lower δ charge
  have hprefix : ∀ horizon,
      (compactFinitePrefixSolutionSet box relation horizon).Nonempty := by
    intro horizon
    let finitePath : ℕ → QuittingNashBellmanPoint ι := fun time =>
      if time ≤ horizon then
        (forward (horizon - time), simplexRow (horizon - (time + 1)))
      else
        (forward 0, simplexRow 0)
    refine ⟨finitePath, ?_, ?_⟩
    · intro time
      by_cases htime : time ≤ horizon
      · rw [show finitePath time =
          (forward (horizon - time),
            simplexRow (horizon - (time + 1))) by
          simp [finitePath, htime]]
        exact mem_quittingCirculationPathBox_of_bounds
          (simplexRow (horizon - (time + 1)))
          (hforwardBound (horizon - time))
          (hforwardLower (horizon - time))
      · rw [show finitePath time = (forward 0, simplexRow 0) by
          simp [finitePath, htime]]
        exact mem_quittingCirculationPathBox_of_bounds
          (simplexRow 0) (hforwardBound 0) (hforwardLower 0)
    · intro time
      have htime : (time : ℕ) < horizon := time.isLt
      have hcurrent : (time : ℕ) ≤ horizon := htime.le
      have htail : (time : ℕ) + 1 ≤ horizon := htime
      let index := horizon - ((time : ℕ) + 1)
      have hindex : horizon - (time : ℕ) = index + 1 := by
        dsimp only [index]
        omega
      rw [show finitePath time =
          (forward (horizon - (time : ℕ)), simplexRow index) by
        simp [finitePath, hcurrent, index],
        show finitePath ((time : ℕ) + 1) =
          (forward index,
            simplexRow (horizon - (((time : ℕ) + 1) + 1))) by
          simp [finitePath, htail, index]]
      unfold relation IsQuittingCirculationPathEdge
      constructor
      · rw [hindex]
        simpa [simplexRow] using hpolicy index
      constructor
      · apply (isQuittingSimplexRootSupportApproxNash_iff
          reward (forward index) δ (simplexRow index)).2
        simpa [simplexRow] using hsupport index
      · rw [quittingSimplexAbsorptionMass_eq_rootAbsorptionMass]
        simpa [simplexRow] using habsorption index
  obtain ⟨state, hstateBox, hstateEdge⟩ :=
    exists_infiniteChain_of_finitePrefixes box relation hbox hgraph hprefix
  let value : ℕ → Payoff ι := fun time => (state time).1
  let roots : ℕ → ι → PMF Bool :=
    fun time => quittingRootOfSimplex (state time).2
  refine ⟨value, roots, ?_, ?_, ?_, ?_, ?_⟩
  · intro time who
    exact abs_le.mpr
      ⟨(hstateBox time).1.1 who, (hstateBox time).1.2 who⟩
  · intro time who
    exact (hstateBox time).2 who
  · intro time
    exact (hstateEdge time).1
  · intro time
    exact (isQuittingSimplexRootSupportApproxNash_iff
      reward (value (time + 1)) δ (state time).2).1
        (hstateEdge time).2.1
  · intro time
    rw [← quittingSimplexAbsorptionMass_eq_rootAbsorptionMass]
    exact (hstateEdge time).2.2

/-! ## The circulation certificate compiles to the support-path interface -/

/-- The natural rationality floor for a quitting weight: the larger of the
solo payoff and the punishment value. -/
def quittingCirculationRationalityFloor
    (r : Finset ι → ι → ℝ) (who : ι) : ℝ :=
  max (r {who} who) (quittingPunishmentValue (rewardOfWeight r) who)

/-- The natural circulation rationality floor dominates punishment values. -/
theorem quittingPunishmentValue_le_circulationRationalityFloor
    (r : Finset ι → ι → ℝ) (who : ι) :
    quittingPunishmentValue (rewardOfWeight r) who ≤
      quittingCirculationRationalityFloor r who :=
  le_max_right _ _

/-- **Complete producer/consumer bridge.**  A multi-owner circulation whose
floor dominates the quitting punishment values produces, at every positive
accuracy, one PMF-root path with support witnesses, nonsummable absorption,
and punishment-rational actual terminal tails. -/
theorem exists_supportRationalDivergentPath_of_multiCirculation
    [Nonempty ι]
    {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]
    (C : FaceCirculationCertificate r floor L)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (s : ℕ) (hs : ∀ l, (mixSupport (C.mixWeight l)).card ≤ s)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (hpunishmentFloor : ∀ who,
      quittingPunishmentValue (rewardOfWeight r) who ≤ floor who)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash
          (rewardOfWeight r) plan ε ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      ∀ target time,
        quittingPunishmentValue (rewardOfWeight r) target - ε ≤
          quittingRootSequenceTerminalValue
            (rewardOfWeight r) plan target time := by
  obtain ⟨N, β, word, hN, hβ0, hβ1, hβN,
      hforwardPolicy, hforwardSupport, hforwardFloor,
      hquitLower, _hprefix⟩ :=
    exists_multiCirculation_orbit_uniform_prefix C M hM0 hM s hs
      a ha ha1 ε hε
  let row : ℕ → ι → ℝ := multiRow word β N
  let forward : ℕ → Payoff ι := multiActual C word β N
  let lower : Payoff ι := fun who => floor who - ε
  let bound : ℝ := M + ∑ who, |C.vertex 0 who|
  let charge : ℝ := (1 - a) / (N : ℝ)
  have hrow0 : ∀ time who, 0 ≤ row time who := by
    intro time who
    have hinterval := singletonRow_mem_unitInterval
      (1 - β (chainPhase L N time))
      (sub_nonneg.mpr (hβ1 (chainPhase L N time)))
      (by linarith [hβ0 (chainPhase L N time)])
      (word (chainPhase L N time) (chainStep L N time)) who
    simpa [row, multiRow] using hinterval.1
  have hrow1 : ∀ time who, row time who ≤ 1 := by
    intro time who
    have hinterval := singletonRow_mem_unitInterval
      (1 - β (chainPhase L N time))
      (sub_nonneg.mpr (hβ1 (chainPhase L N time)))
      (by linarith [hβ0 (chainPhase L N time)])
      (word (chainPhase L N time) (chainStep L N time)) who
    simpa [row, multiRow] using hinterval.2
  have hbound0 : 0 ≤ bound := by
    dsimp only [bound]
    exact add_nonneg hM0 (Finset.sum_nonneg fun who _ =>
      abs_nonneg (C.vertex 0 who))
  have hforwardBound : ∀ time who, |forward time who| ≤ bound := by
    intro time who
    simpa [forward, bound] using
      abs_multiActual_le_reward_add_vertex C word β N hβ0 hβ1
        M hM0 hM time who
  have hforwardLower : ∀ time who, lower who ≤ forward time who := by
    intro time who
    simpa [lower, forward] using hforwardFloor time who
  have hpolicy : ∀ time,
      forward (time + 1) = quittingRootSuccessorPayoff
        (rewardOfWeight r) (forward time)
        (rootOfHazard (row time) (hrow0 time) (hrow1 time)) := by
    intro time
    calc
      forward (time + 1) = oneStageNext r (row time) (forward time) := by
        funext who
        simpa [forward, row] using hforwardPolicy time who
      _ = quittingRootSuccessorPayoff
          (rewardOfWeight r) (forward time)
          (rootOfHazard (row time) (hrow0 time) (hrow1 time)) := by
        symm
        exact quittingRootSuccessorPayoff_rootOfHazard_eq_oneStageNext
          r (row time) (hrow0 time) (hrow1 time) (forward time)
  have hsupport : ∀ time,
      IsQuittingRootSupportApproxNash
        (rewardOfWeight r) (forward time) ε
        (rootOfHazard (row time) (hrow0 time) (hrow1 time)) := by
    intro time
    exact
      isQuittingRootSupportApproxNash_rootOfHazard_of_isSupportPerfectRow
        r (row time) (hrow0 time) (hrow1 time) (forward time) ε
        (by simpa [row, forward] using hforwardSupport time)
  have habsorption : ∀ time,
      charge ≤ quittingRootAbsorptionMass
        (rootOfHazard (row time) (hrow0 time) (hrow1 time)) := by
    intro time
    rw [quittingRootAbsorptionMass_rootOfHazard]
    simpa [charge, row] using hquitLower time
  obtain ⟨value, roots, hvalueBound, hvalueLower,
      hvaluePolicy, hvalueSupport, hvalueAbsorption⟩ :=
    exists_chronologicalSupportPath_of_forwardOrbit
      (rewardOfWeight r) row forward lower hrow0 hrow1
      hforwardBound hforwardLower hpolicy hsupport habsorption
  have hcharge : 0 < charge := by
    dsimp only [charge]
    exact div_pos (sub_pos.mpr ha1) (by exact_mod_cast hN)
  have hreward : ∀ terminal who,
      |rewardOfWeight r terminal who| ≤ bound := by
    intro terminal who
    change |r terminal.1 who| ≤ bound
    exact (hM terminal.1 who).trans
      (le_add_of_nonneg_right
        (Finset.sum_nonneg fun player _ => abs_nonneg (C.vertex 0 player)))
  have hselected : ∀ time,
      value time = fun who =>
        quittingRootSequenceTerminalValue
          (rewardOfWeight r) roots who time :=
    eq_quittingRootSequenceTerminalValue_of_exact_bounded_path_of_absorption_lower
      (rewardOfWeight r) roots value hcharge hvalueAbsorption
      hbound0 hreward hvalueBound hvaluePolicy
  have hsupportSequence :
      IsQuittingRootSequenceSupportApproxNash
        (rewardOfWeight r) roots ε := by
    intro time
    have htail :
        quittingRootSequenceTailVector (rewardOfWeight r) roots
            (time + 1) = value (time + 1) := by
      funext who
      change quittingRootSequenceTerminalValue
          (rewardOfWeight r) roots who (time + 1) = value (time + 1) who
      exact (congrFun (hselected (time + 1)) who).symm
    rw [htail]
    exact hvalueSupport time
  have hdiverges : ¬Summable (quittingTotalAbsorptionCharge roots) := by
    apply not_summable_quittingTotalAbsorptionCharge_of_uniform_lower
      roots hcharge
    intro time
    simpa [quittingTotalAbsorptionCharge] using hvalueAbsorption time
  refine ⟨roots, hsupportSequence, hdiverges, ?_⟩
  intro target time
  rw [← congrFun (hselected time) target]
  have hfloor := hpunishmentFloor target
  have hlower := hvalueLower time target
  dsimp only [lower] at hlower
  linarith

/-- A circulation certificate written directly over the natural rationality
floor automatically satisfies the punishment-floor hypothesis. -/
theorem exists_supportRationalDivergentPath_of_multiCirculation_rationalityFloor
    [Nonempty ι]
    {r : Finset ι → ι → ℝ} {L : ℕ} [NeZero L]
    (C : FaceCirculationCertificate r
      (quittingCirculationRationalityFloor r) L)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (s : ℕ) (hs : ∀ l, (mixSupport (C.mixWeight l)).card ≤ s)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ plan : ℕ → ι → PMF Bool,
      IsQuittingRootSequenceSupportApproxNash
          (rewardOfWeight r) plan ε ∧
      ¬Summable (quittingTotalAbsorptionCharge plan) ∧
      ∀ target time,
        quittingPunishmentValue (rewardOfWeight r) target - ε ≤
          quittingRootSequenceTerminalValue
            (rewardOfWeight r) plan target time := by
  exact exists_supportRationalDivergentPath_of_multiCirculation
    C M hM0 hM s hs a ha ha1
      (quittingPunishmentValue_le_circulationRationalityFloor r) ε hε

/-- **Uniform-equilibrium payoff from a multi-owner circulation.** -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_multiCirculation
    [Nonempty ι]
    {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]
    (C : FaceCirculationCertificate r floor L)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (s : ℕ) (hs : ∀ l, (mixSupport (C.mixWeight l)).card ≤ s)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1)
    (hpunishmentFloor : ∀ who,
      quittingPunishmentValue (rewardOfWeight r) who ≤ floor who) :
    ∃ payoff : Payoff ι,
      (quittingGame (rewardOfWeight r)).IsUniformEquilibriumPayoff none payoff := by
  apply
    quittingGame_exists_uniformEquilibriumPayoff_of_supportRationalDivergentPaths
      (rewardOfWeight r)
  intro δ hδ
  exact exists_supportRationalDivergentPath_of_multiCirculation
    C M hM0 hM s hs a ha ha1 hpunishmentFloor δ hδ

/-- A singleton-supported circulation has support-card bound one, so its
uniform-payoff compiler needs no separate combinatorial support estimate. -/
theorem quittingGame_exists_uniformEquilibriumPayoff_of_singletonCirculation
    [Nonempty ι]
    {r : Finset ι → ι → ℝ} {floor : ι → ℝ} {L : ℕ} [NeZero L]
    (C : FaceCirculationCertificate r floor L)
    (S : SingletonSupport C)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ coalition who, |r coalition who| ≤ M)
    (a : ℝ) (ha : ∀ phase, C.ratio phase ≤ a) (ha1 : a < 1)
    (hpunishmentFloor : ∀ who,
      quittingPunishmentValue (rewardOfWeight r) who ≤ floor who) :
    ∃ payoff : Payoff ι,
      (quittingGame (rewardOfWeight r)).IsUniformEquilibriumPayoff none payoff := by
  apply quittingGame_exists_uniformEquilibriumPayoff_of_multiCirculation
    C M hM0 hM 1
  · intro phase
    have hsupport :
        mixSupport (C.mixWeight phase) = {S.owner phase} := by
      rw [S.mixWeight_eq phase]
      ext who
      simp only [mixSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      by_cases hwho : who = S.owner phase <;> simp [hwho]
    rw [hsupport]
    simp
  · exact ha
  · exact ha1
  · exact hpunishmentFloor

/-- Natural-floor specialization of the uniform-equilibrium theorem. -/
theorem
    quittingGame_exists_uniformEquilibriumPayoff_of_multiCirculation_rationalityFloor
    [Nonempty ι]
    {r : Finset ι → ι → ℝ} {L : ℕ} [NeZero L]
    (C : FaceCirculationCertificate r
      (quittingCirculationRationalityFloor r) L)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ S j, |r S j| ≤ M)
    (s : ℕ) (hs : ∀ l, (mixSupport (C.mixWeight l)).card ≤ s)
    (a : ℝ) (ha : ∀ l, C.ratio l ≤ a) (ha1 : a < 1) :
    ∃ payoff : Payoff ι,
      (quittingGame (rewardOfWeight r)).IsUniformEquilibriumPayoff none payoff := by
  exact quittingGame_exists_uniformEquilibriumPayoff_of_multiCirculation
    C M hM0 hM s hs a ha ha1
      (quittingPunishmentValue_le_circulationRationalityFloor r)

end GameTheory
