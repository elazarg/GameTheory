/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.UniformEquilibrium.Quitting.Boundary.Holonomy.Basic

/-!
# Compactness fence for realized quitting boundary holonomy

The scalar coefficient box from `QuittingBoundaryHolonomy` is not by itself
a compact space of strategically realized blocks.  This file proves the
strongest unconditional closedness statement available from the finite-chain
construction: at one fixed cutoff, the graph which retains the *entire exact
Nash--Bellman path* together with the holonomy of any nonempty subblock is
compact, hence closed.  Taking the finite union over every subblock at that
cutoff preserves compactness.  A calibrated anchored block lands in this
resolved graph with its selected minimizing path literally present, so root,
support, exact-D, and prefix provenance have not been projected away.

The final theorem is a bounded-cost fence: any compact lift which retains
the literal number of game stages as a natural-valued coordinate has
a uniform stage bound.  Consequently an arbitrary-length positive-plateau
middle cannot have such a compact lift unless one first proves a uniform
length/tightness theorem, or changes the length coordinate by adding a point
at infinity.  The latter change no longer supplies the bounded edge-cost
interface.  This is a precise compactness obstruction, not a scalar
coefficient defect.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Continuous fixed-cutoff holonomy coordinates -/

/-- Holonomy coordinates of a fixed subblock of a finite Nash--Bellman path.
The operational roots are padded by all-Continue after the cutoff, although
the realized graph below only uses blocks lying before the cutoff. -/
def quittingFinitePathBoundaryHolonomyCoordinates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff start extra : ℕ)
    (path : QuittingFiniteNashBellmanPath ι cutoff) :
    QuittingBoundaryHolonomyCoordinates ι :=
  (quittingFiniteBoundaryHolonomy reward
    (quittingFiniteNashBellmanPathRoots cutoff path) start extra).coordinates

omit [DecidableEq ι] in
/-- Every fixed simplex action coordinate is continuous in the full finite
path. -/
theorem continuous_quittingFiniteNashBellmanPathSimplexRoot_apply
    (cutoff time : ℕ) (who : ι) (action : Bool) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFiniteNashBellmanPathSimplexRoot cutoff path time who action) :=
  (continuous_apply action).comp
    (continuous_subtype_val.comp
      ((continuous_apply who).comp
        (continuous_quittingFiniteNashBellmanPathSimplexRoot cutoff time)))

/-- At a fixed time, the pure-Quit endpoint against the displayed opponents
is continuous in the finite path. -/
theorem continuous_quittingFixedOpponentsQuitValue_finitePath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) (who : ι) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFixedOpponentsQuitValue reward
        (quittingFiniteNashBellmanPathRoots cutoff path) who time) := by
  let endpointData := fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
    ((0 : Payoff ι),
      quittingFiniteNashBellmanPathSimplexRoot cutoff path time)
  have hdata : Continuous endpointData := by
    exact continuous_const.prodMk
      (continuous_quittingFiniteNashBellmanPathSimplexRoot cutoff time)
  have hendpoint :=
    (continuous_quittingRootQuitPayoff_simplex reward who).comp hdata
  have heq : (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFixedOpponentsQuitValue reward
        (quittingFiniteNashBellmanPathRoots cutoff path) who time) =
      fun path ↦ quittingRootQuitPayoff reward (0 : Payoff ι)
        (quittingRootOfSimplex
          (quittingFiniteNashBellmanPathSimplexRoot cutoff path time)) who := by
    funext path
    rw [quittingRootOfSimplex_finiteNashBellmanPathSimplexRoot]
    exact (quittingRootQuitPayoff_eq_fixedOpponentsQuitValue
      reward (quittingFiniteNashBellmanPathRoots cutoff path) who 0 time).symm
  rw [heq]
  change Continuous
    ((fun point : Payoff ι × QuittingRootSimplex ι ↦
      quittingRootQuitPayoff reward point.1
        (quittingRootOfSimplex point.2) who) ∘ endpointData)
  exact hendpoint

/-- At a fixed time, the immediate pure-Continue absorbing contribution is
continuous in the finite path. -/
theorem continuous_quittingFixedOpponentsContinueReward_finitePath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) (who : ι) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFixedOpponentsContinueReward reward
        (quittingFiniteNashBellmanPathRoots cutoff path) who time) := by
  let endpointData := fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
    ((0 : Payoff ι),
      quittingFiniteNashBellmanPathSimplexRoot cutoff path time)
  have hdata : Continuous endpointData := by
    exact continuous_const.prodMk
      (continuous_quittingFiniteNashBellmanPathSimplexRoot cutoff time)
  have hendpoint :=
    (continuous_quittingRootContinuePayoff_simplex reward who).comp hdata
  have heq : (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFixedOpponentsContinueReward reward
        (quittingFiniteNashBellmanPathRoots cutoff path) who time) =
      fun path ↦ quittingRootContinuePayoff reward (0 : Payoff ι)
        (quittingRootOfSimplex
          (quittingFiniteNashBellmanPathSimplexRoot cutoff path time)) who := by
    funext path
    rw [quittingRootOfSimplex_finiteNashBellmanPathSimplexRoot]
    have h := quittingRootContinuePayoff_eq_fixedOpponents reward
      (quittingFiniteNashBellmanPathRoots cutoff path) who 0 time
    simpa using h.symm
  rw [heq]
  change Continuous
    ((fun point : Payoff ι × QuittingRootSimplex ι ↦
      quittingRootContinuePayoff reward point.1
        (quittingRootOfSimplex point.2) who) ∘ endpointData)
  exact hendpoint

omit [DecidableEq ι] in
/-- A fixed operational PMF coordinate, converted to a real probability, is
continuous in the finite path. -/
theorem continuous_quittingFiniteNashBellmanPathRoot_toReal
    (cutoff time : ℕ) (who : ι) (action : Bool) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      ((quittingFiniteNashBellmanPathRoots cutoff path time who) action).toReal) := by
  have heq : (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      ((quittingFiniteNashBellmanPathRoots cutoff path time who) action).toReal) =
      fun path ↦ quittingFiniteNashBellmanPathSimplexRoot
        cutoff path time who action := by
    funext path
    rw [← quittingRootOfSimplex_finiteNashBellmanPathSimplexRoot
      cutoff path time]
    exact quittingRootOfSimplex_apply_toReal _ who action
  rw [heq]
  exact continuous_quittingFiniteNashBellmanPathSimplexRoot_apply
    cutoff time who action

/-- Coordinates of one actual root stage vary continuously with a fixed
finite path. -/
theorem continuous_quittingBoundaryStageHolonomy_coordinates_finitePath
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff time : ℕ) :
    Continuous (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      (quittingBoundaryStageHolonomy reward
        (quittingFiniteNashBellmanPathRoots cutoff path) time).coordinates) := by
  let quitValue := fun who : ι ↦
    fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFixedOpponentsQuitValue reward
        (quittingFiniteNashBellmanPathRoots cutoff path) who time
  let continueReward := fun who : ι ↦
    fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFixedOpponentsContinueReward reward
        (quittingFiniteNashBellmanPathRoots cutoff path) who time
  let opponentMass := fun who : ι ↦
    fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      quittingFixedOpponentsContinueMass
        (quittingFiniteNashBellmanPathRoots cutoff path) who time
  let quitProbability := fun who : ι ↦
    fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      ((quittingFiniteNashBellmanPathRoots cutoff path time who) true).toReal
  let continueProbability := fun who : ι ↦
    fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      ((quittingFiniteNashBellmanPathRoots cutoff path time who) false).toReal
  have hquit : ∀ who, Continuous (quitValue who) :=
    fun who ↦ continuous_quittingFixedOpponentsQuitValue_finitePath
      reward cutoff time who
  have hcontinue : ∀ who, Continuous (continueReward who) :=
    fun who ↦ continuous_quittingFixedOpponentsContinueReward_finitePath
      reward cutoff time who
  have hmass : ∀ who, Continuous (opponentMass who) :=
    fun who ↦ continuous_quittingFixedOpponentsContinueMass_finitePath
      cutoff time who
  have hq : ∀ who, Continuous (quitProbability who) :=
    fun who ↦ continuous_quittingFiniteNashBellmanPathRoot_toReal
      cutoff time who true
  have hc : ∀ who, Continuous (continueProbability who) :=
    fun who ↦ continuous_quittingFiniteNashBellmanPathRoot_toReal
      cutoff time who false
  have hformula : (fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
      (quittingBoundaryStageHolonomy reward
        (quittingFiniteNashBellmanPathRoots cutoff path) time).coordinates) =
      fun path ↦
        (fun who ↦
          (quitProbability who path * quitValue who path +
              continueProbability who path * continueReward who path,
            continueProbability who path * opponentMass who path),
         fun who ↦
          (quitValue who path,
            (continueReward who path, opponentMass who path))) := by
    funext path
    rfl
  rw [hformula]
  exact (continuous_pi fun who ↦
      ((hq who).mul (hquit who) |>.add ((hc who).mul (hcontinue who))).prodMk
        ((hc who).mul (hmass who))).prodMk
    (continuous_pi fun who ↦
      (hquit who).prodMk ((hcontinue who).prodMk (hmass who)))

/-- Polynomial/max-affine composition directly on the five coordinate
families. -/
def quittingBoundaryHolonomyCoordinatesCompose
    (outer inner : QuittingBoundaryHolonomyCoordinates ι) :
    QuittingBoundaryHolonomyCoordinates ι :=
  (fun who ↦
    ((outer.1 who).1 + (outer.1 who).2 * (inner.1 who).1,
      (outer.1 who).2 * (inner.1 who).2),
   fun who ↦
    (max (outer.2 who).1
        ((outer.2 who).2.1 +
          (outer.2 who).2.2 * (inner.2 who).1),
      ((outer.2 who).2.1 +
          (outer.2 who).2.2 * (inner.2 who).2.1,
        (outer.2 who).2.2 * (inner.2 who).2.2)))

omit [Fintype ι] [DecidableEq ι] in
/-- Forgetting a chronological semigroup product is coordinate
composition. -/
theorem QuittingBoundaryHolonomy.coordinates_mul
    (outer inner : QuittingBoundaryHolonomy ι) :
    (outer * inner).coordinates =
      quittingBoundaryHolonomyCoordinatesCompose
        outer.coordinates inner.coordinates := by
  simp [QuittingBoundaryHolonomy.coordinates,
    quittingBoundaryHolonomyCoordinatesCompose,
    QuittingBoundaryHolonomy.mul_eq_compose,
    QuittingBoundaryHolonomy.compose,
    QuittingAffineSummary.mul_eq_compose, QuittingAffineSummary.compose,
    QuittingMaxAffineSummary.mul_eq_compose, QuittingMaxAffineSummary.compose]

omit [Fintype ι] [DecidableEq ι] in
/-- Coordinate composition is continuous. -/
theorem continuous_quittingBoundaryHolonomyCoordinatesCompose :
    Continuous (fun point : QuittingBoundaryHolonomyCoordinates ι ×
        QuittingBoundaryHolonomyCoordinates ι ↦
      quittingBoundaryHolonomyCoordinatesCompose point.1 point.2) := by
  unfold quittingBoundaryHolonomyCoordinatesCompose
  fun_prop

/-- At fixed cutoff, start, and length, all five holonomy coordinates are
continuous in the complete finite chain. -/
theorem continuous_quittingFinitePathBoundaryHolonomyCoordinates
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff start extra : ℕ) :
    Continuous (quittingFinitePathBoundaryHolonomyCoordinates
      reward cutoff start extra) := by
  induction extra generalizing start with
  | zero =>
      exact continuous_quittingBoundaryStageHolonomy_coordinates_finitePath
        reward cutoff start
  | succ extra ih =>
      have hformula :
          quittingFinitePathBoundaryHolonomyCoordinates reward cutoff start
              (extra + 1) =
            fun path ↦ quittingBoundaryHolonomyCoordinatesCompose
              (quittingBoundaryStageHolonomy reward
                (quittingFiniteNashBellmanPathRoots cutoff path)
                start).coordinates
              (quittingFinitePathBoundaryHolonomyCoordinates reward cutoff
                (start + 1) extra path) := by
        funext path
        exact QuittingBoundaryHolonomy.coordinates_mul _ _
      rw [hformula]
      exact continuous_quittingBoundaryHolonomyCoordinatesCompose.comp
        ((continuous_quittingBoundaryStageHolonomy_coordinates_finitePath
            reward cutoff start).prodMk (ih (start + 1)))

/-! ## The full-path resolved graph -/

/-- At fixed cutoff and fixed nonempty subblock, retain the entire exact
zero-boundary chain alongside the block holonomy.  Unlike the scalar image,
this graph retains every root coordinate and support face; its exact-D
entry/exit and all prefix facts remain reconstructible from the path. -/
def quittingFixedBlockResolvedHolonomyLift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff start extra : ℕ) :
    Set (QuittingFiniteNashBellmanPath ι cutoff ×
      QuittingBoundaryHolonomyCoordinates ι) :=
  {point | point.1 ∈
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff ∧
    point.2 = quittingFinitePathBoundaryHolonomyCoordinates
      reward cutoff start extra point.1}

/-- The fixed-block full-path graph is the continuous image of the compact
exact-chain set. -/
theorem quittingFixedBlockResolvedHolonomyLift_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff start extra : ℕ) :
    IsCompact (quittingFixedBlockResolvedHolonomyLift
      reward cutoff start extra) := by
  let embed := fun path : QuittingFiniteNashBellmanPath ι cutoff ↦
    (path, quittingFinitePathBoundaryHolonomyCoordinates
      reward cutoff start extra path)
  have hembed : Continuous embed :=
    continuous_id.prodMk
      (continuous_quittingFinitePathBoundaryHolonomyCoordinates
        reward cutoff start extra)
  have heq : quittingFixedBlockResolvedHolonomyLift
      reward cutoff start extra =
      embed '' quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff := by
    ext point
    constructor
    · intro hpoint
      exact ⟨point.1, hpoint.1, by
        apply Prod.ext
        · rfl
        · exact hpoint.2.symm⟩
    · rintro ⟨path, hpath, rfl⟩
      exact ⟨hpath, rfl⟩
  rw [heq]
  exact (quittingFiniteZeroBoundaryNashBellmanChainSet_isCompact
    reward cutoff).image hembed

/-- The fixed-block realized full-path graph is closed. -/
theorem quittingFixedBlockResolvedHolonomyLift_isClosed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff start extra : ℕ) :
    IsClosed (quittingFixedBlockResolvedHolonomyLift
      reward cutoff start extra) :=
  (quittingFixedBlockResolvedHolonomyLift_isCompact
    reward cutoff start extra).isClosed

/-- All strategically realized nonempty subblocks at one fixed cutoff.  The
finite union is taken in a common ambient space which still contains the
whole source path. -/
def quittingFixedCutoffResolvedHolonomyLift
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    Set (QuittingFiniteNashBellmanPath ι cutoff ×
      QuittingBoundaryHolonomyCoordinates ι) :=
  ⋃ start : Fin cutoff, ⋃ extra : Fin cutoff,
    if start.val + (extra.val + 1) ≤ cutoff then
      quittingFixedBlockResolvedHolonomyLift reward cutoff start.val extra.val
    else ∅

/-- **Maximal unconditional closed subclass.**  At a fixed cutoff, the full
resolved realized lift of every subblock is compact. -/
theorem quittingFixedCutoffResolvedHolonomyLift_isCompact
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    IsCompact (quittingFixedCutoffResolvedHolonomyLift reward cutoff) := by
  unfold quittingFixedCutoffResolvedHolonomyLift
  apply isCompact_iUnion
  intro start
  apply isCompact_iUnion
  intro extra
  split_ifs
  · exact quittingFixedBlockResolvedHolonomyLift_isCompact
      reward cutoff start.val extra.val
  · exact isCompact_empty

/-- The fixed-cutoff resolved realized lift is closed. -/
theorem quittingFixedCutoffResolvedHolonomyLift_isClosed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (cutoff : ℕ) :
    IsClosed (quittingFixedCutoffResolvedHolonomyLift reward cutoff) :=
  (quittingFixedCutoffResolvedHolonomyLift_isCompact reward cutoff).isClosed

/-- Every calibrated anchored block lands in the fixed-cutoff compact lift
with its canonical selected minimizer literally retained. -/
theorem QuittingAnchoredBoundaryBlock.path_coordinates_mem_fixedCutoffLift
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) :
    (anchor.path, block.holonomy.coordinates) ∈
      quittingFixedCutoffResolvedHolonomyLift reward (anchor.last + 1) := by
  have hstart : block.start < anchor.last + 1 := by
    have hwithin := block.within
    omega
  have hextra : block.extra < anchor.last + 1 := by
    have hwithin := block.within
    omega
  let start : Fin (anchor.last + 1) := ⟨block.start, hstart⟩
  let extra : Fin (anchor.last + 1) := ⟨block.extra, hextra⟩
  change (anchor.path, block.holonomy.coordinates) ∈
    ⋃ start : Fin (anchor.last + 1), ⋃ extra : Fin (anchor.last + 1),
      if start.val + (extra.val + 1) ≤ anchor.last + 1 then
        quittingFixedBlockResolvedHolonomyLift reward (anchor.last + 1)
          start.val extra.val
      else ∅
  refine Set.mem_iUnion.2 ⟨start, Set.mem_iUnion.2 ⟨extra, ?_⟩⟩
  rw [if_pos block.within]
  refine ⟨quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer_mem
    reward (anchor.last + 1), ?_⟩
  rfl

/-! ## Fully anchored fixed-last lift -/

/-- A topology-friendly owner label.  Encoding the owner as a one-hot Boolean
word avoids imposing an extraneous topology on the player index type. -/
def quittingBoundaryOwnerCode (owner : ι) : ι → Bool :=
  fun who ↦ decide (who = owner)

/-- Full resolved data retained by an anchored block at a fixed terminal
index: the complete selected path, owner and terminal-action codes, exact-D
entry and exit, the two separately calibrated packet factors, and the common
five-coordinate holonomy. -/
abbrev QuittingFixedLastAnchoredHolonomyState (ι : Type) [Fintype ι]
    (last : ℕ) :=
  QuittingFiniteNashBellmanPath ι (last + 1) ×
    ((ι → Bool) × ((ι → Bool) ×
      ((QuittingDebtPoint ι × QuittingDebtPoint ι) ×
        ((ℝ × ℝ) × QuittingBoundaryHolonomyCoordinates ι))))

/-- Construct the full resolved state from fixed labels and a fixed finite
path. -/
def quittingFixedLastAnchoredHolonomyData
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) (owner : ι) (action : ι → Bool)
    (start extra : ℕ)
    (path : QuittingFiniteNashBellmanPath ι (last + 1)) :
    QuittingFixedLastAnchoredHolonomyState ι last :=
  (path,
    (quittingBoundaryOwnerCode owner,
      (action,
        ((quittingFiniteNashBellmanPathDynamicDebtPoint reward (last + 1)
              path start,
            quittingFiniteNashBellmanPathDynamicDebtPoint reward (last + 1)
              path (start + extra + 1)),
          ((quittingOpponentSurvivalWeight
              (quittingFiniteNashBellmanPathRoots (last + 1) path)
              owner 0 last,
            ((pmfPi (Function.update
              (quittingFiniteNashBellmanPathRoots (last + 1) path last)
                owner (PMF.pure false))) action).toReal),
            quittingFinitePathBoundaryHolonomyCoordinates reward
              (last + 1) start extra path)))))

/-- The exact fixed-last predicate carried by
`QuittingCalibratedTerminalAnchor`.  It is stated independently so the
realized fixed-last set lives in one common topological type. -/
def IsQuittingCalibratedTerminalPacketAt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    [Nonempty ι] (last : ℕ) (owner : ι) (action : ι → Bool) : Prop :=
  let path :=
    quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
      reward (last + 1)
  let roots := quittingFiniteNashBellmanPathRoots (last + 1) path
  let survival := quittingOpponentSurvivalWeight roots owner 0 last
  let mass := ((pmfPi (Function.update (roots last) owner
    (PMF.pure false))) action).toReal
  let debt := quittingFiniteNashBellmanPathDynamicDebt
    reward (last + 1) path owner 0
  0 < debt ∧
    0 < survival ∧ survival ≤ 1 ∧
    0 < mass ∧ mass ≤ 1 ∧
    action owner = false ∧
    (quittingQuitters action).Nonempty ∧
    0 < quittingTerminalOpponentAdvantage reward owner action ∧
    debt ≤ (Fintype.card (ι → Bool) : ℝ) *
      (survival * mass) *
        quittingTerminalOpponentAdvantage reward owner action

/-- An anchor is exactly a witness of the common fixed-last packet
predicate. -/
theorem QuittingCalibratedTerminalAnchor.isPacketAt
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    (anchor : QuittingCalibratedTerminalAnchor reward) :
    IsQuittingCalibratedTerminalPacketAt reward anchor.last
      anchor.owner anchor.action := by
  exact ⟨anchor.ownerDebt_pos, anchor.preterminalSurvival_pos,
    anchor.preterminalSurvival_le_one, anchor.terminalMass_pos,
    anchor.terminalMass_le_one, anchor.owner_continues,
    anchor.terminalQuitters_nonempty, anchor.terminalAdvantage_pos,
    anchor.debt_le_weighted_packet⟩

/-- Conversely, the fixed-last predicate constructs the production anchor;
there is no relaxation hidden in the common-topology representation. -/
def QuittingCalibratedTerminalAnchor.ofPacketAt
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) (owner : ι) (action : ι → Bool)
    (hpacket : IsQuittingCalibratedTerminalPacketAt
      reward last owner action) :
    QuittingCalibratedTerminalAnchor reward where
  last := last
  owner := owner
  action := action
  ownerDebt_pos := hpacket.1
  preterminalSurvival_pos := hpacket.2.1
  preterminalSurvival_le_one := hpacket.2.2.1
  terminalMass_pos := hpacket.2.2.2.1
  terminalMass_le_one := hpacket.2.2.2.2.1
  owner_continues := hpacket.2.2.2.2.2.1
  terminalQuitters_nonempty := hpacket.2.2.2.2.2.2.1
  terminalAdvantage_pos := hpacket.2.2.2.2.2.2.2.1
  debt_le_weighted_packet := hpacket.2.2.2.2.2.2.2.2

/-- Strategically sound anchored blocks at one fixed terminal index.  Each
point contains the selected minimizer, both exact-D endpoints, owner, full
marked action, separate packet factors, and the holonomy of the actual common
root block. -/
def quittingFixedLastCalibratedHolonomyLift
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) : Set (QuittingFixedLastAnchoredHolonomyState ι last) :=
  {point | ∃ (owner : ι) (action : ι → Bool) (start extra : ℕ),
    IsQuittingCalibratedTerminalPacketAt reward last owner action ∧
      start + (extra + 1) ≤ last + 1 ∧
      point = quittingFixedLastAnchoredHolonomyData reward last owner action
        start extra
        (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
          reward (last + 1))}

/-- The fully resolved, strategically calibrated realized lift at fixed last
is finite.  This is stronger than scalar compactness: no source coordinate is
forgotten. -/
theorem quittingFixedLastCalibratedHolonomyLift_finite
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) :
    (quittingFixedLastCalibratedHolonomyLift reward last).Finite := by
  let candidate := fun index :
      ι × (ι → Bool) × Fin (last + 1) × Fin (last + 1) ↦
    quittingFixedLastAnchoredHolonomyData reward last
      index.1 index.2.1 index.2.2.1.val index.2.2.2.val
      (quittingFiniteZeroBoundaryNashBellmanMaxDynamicDebtMinimizer
        reward (last + 1))
  apply (Set.finite_range candidate).subset
  intro point hpoint
  obtain ⟨owner, action, start, extra, _, hwithin, rfl⟩ := hpoint
  have hstart : start < last + 1 := by omega
  have hextra : extra < last + 1 := by omega
  refine ⟨(owner, action, ⟨start, hstart⟩, ⟨extra, hextra⟩), ?_⟩
  rfl

/-- Therefore the fully anchored fixed-last lift is compact. -/
theorem quittingFixedLastCalibratedHolonomyLift_isCompact
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) :
    IsCompact (quittingFixedLastCalibratedHolonomyLift reward last) :=
  (quittingFixedLastCalibratedHolonomyLift_finite reward last).isCompact

/-- The fully anchored fixed-last lift is closed. -/
theorem quittingFixedLastCalibratedHolonomyLift_isClosed
    [Nonempty ι]
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (last : ℕ) :
    IsClosed (quittingFixedLastCalibratedHolonomyLift reward last) :=
  (quittingFixedLastCalibratedHolonomyLift_isCompact reward last).isClosed

/-- The production anchored block maps into the fully resolved fixed-last
lift, with every field definitionally synchronized. -/
theorem QuittingAnchoredBoundaryBlock.resolvedData_mem_fixedLastLift
    [Nonempty ι]
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) :
    quittingFixedLastAnchoredHolonomyData reward anchor.last anchor.owner
        anchor.action block.start block.extra anchor.path ∈
      quittingFixedLastCalibratedHolonomyLift reward anchor.last := by
  exact ⟨anchor.owner, anchor.action, block.start, block.extra,
    anchor.isPacketAt, block.within, rfl⟩

/-! ## Compact literal cost forces bounded length -/

/-- A compact set of resolved objects which retains a literal natural-valued
stage cost has a uniform cost bound.  This is the bounded-cost fence
described in the module docstring above. -/
theorem IsCompact.exists_uniform_nat_fst_bound
    {α : Type} [TopologicalSpace α]
    {K : Set (ℕ × α)} (hK : IsCompact K) :
    ∃ L : ℕ, ∀ point ∈ K, point.1 ≤ L := by
  have himage : IsCompact (Prod.fst '' K) := hK.image continuous_fst
  have hfinite : (Prod.fst '' K).Finite := himage.finite_of_discrete
  let values : Finset ℕ := hfinite.toFinset
  refine ⟨values.sup id, ?_⟩
  intro point hpoint
  have hmemSet : point.1 ∈ Prod.fst '' K := ⟨point, hpoint, rfl⟩
  have hmem : point.1 ∈ values := by
    simpa only [values, Set.Finite.mem_toFinset] using hmemSet
  exact Finset.le_sup (α := ℕ) (f := id) hmem

/-- Hence a family with unbounded literal game-stage cost cannot itself be a
compact resolved lift, even if every scalar coefficient projection lies in a
fixed compact box. -/
theorem not_isCompact_of_unbounded_nat_fst
    {α : Type} [TopologicalSpace α]
    {K : Set (ℕ × α)}
    (hunbounded : ∀ L : ℕ, ∃ point ∈ K, L < point.1) :
    ¬ IsCompact K := by
  intro hcompact
  obtain ⟨L, hL⟩ := IsCompact.exists_uniform_nat_fst_bound hcompact
  obtain ⟨point, hpoint, hlt⟩ := hunbounded L
  exact (not_lt_of_ge (hL point hpoint)) hlt

/-- Concrete sharp fence: attaching an escaping natural length to one fixed
compact coefficient point destroys compactness, although forgetting the
length leaves a singleton. -/
theorem not_isCompact_range_nat_pair_const
    {α : Type} [TopologicalSpace α] (coefficient : α) :
    ¬ IsCompact (Set.range fun length : ℕ ↦ (length, coefficient)) := by
  apply not_isCompact_of_unbounded_nat_fst
  intro L
  refine ⟨(L + 1, coefficient), ⟨L + 1, rfl⟩, ?_⟩
  omega

/-- Forgetting the escaping literal length in the preceding fence leaves
exactly one coefficient point. -/
theorem snd_image_range_nat_pair_const
    {α : Type} [TopologicalSpace α] (coefficient : α) :
    Prod.snd '' (Set.range fun length : ℕ ↦ (length, coefficient)) =
      {coefficient} := by
  ext point
  simp [eq_comm]

/-- Thus the coefficient projection in the sharp fence is compact even
though the provenance-and-cost lift is not. -/
theorem isCompact_snd_image_range_nat_pair_const
    {α : Type} [TopologicalSpace α] (coefficient : α) :
    IsCompact (Prod.snd ''
      (Set.range fun length : ℕ ↦ (length, coefficient))) := by
  rw [snd_image_range_nat_pair_const]
  exact isCompact_singleton

end GameTheory
