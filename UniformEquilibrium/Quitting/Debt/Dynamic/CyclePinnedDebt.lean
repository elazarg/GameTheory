/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Repair.BoundedSurgeryDescentCounterexample
import UniformEquilibrium.Quitting.Debt.Dynamic.DebtTransportLaw

/-!
# Dynamic debt against a realized cyclic continuation

The existing optimized finite-chain debt
`quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt` pins the terminal
continuation of every admissible chain to `0`.  On the surgery table of
`QuittingBoundedSurgeryDescentCounterexample` that pin manufactures a
strictly positive plateau `a(1 - a) / (1 - a^(m+1)) ↓ a(1 - a) > 0`, even
though the same game has an exact stationary equilibrium at which the debt
against its own continuation is exactly zero at every horizon
(`quittingConstantDynamicDebt_eq_zero`).

This file replaces the pin by a *realized* terminal continuation.

## The vacuity trap and how it is fenced

If the terminal continuation `z` were an arbitrary vector, the objective
would collapse: choosing `z` so that the terminal debt is `0` makes the whole
debt identically `0` for every chain, by
`quittingFiniteDynamicDebt_eq_zero_of_terminalDebt_eq_zero`.  Three fences
are used, and all three are needed.

1. **`z` must be self-consistent.**  `IsQuittingCyclicContinuation` demands a
   finite block of Nash--Bellman points of length `L ≥ 1` which is run
   against `z` at its terminal end and *reproduces* `z` at its origin.
2. **The block must absorb.**  *This hypothesis is not redundant and must not
   be removed.*  Take the all-Continue row, at which every player continues
   with probability one.  Its all-continue mass is `1` and every absorbing
   coalition has probability `0`, so its Bellman map is the **identity**:
   `quittingRootSuccessorPayoff reward z quittingAllContinueRoot = z` for
   *every* `z` (`quittingRootSuccessorPayoff_allContinueRoot_eq`).  It is also
   exactly endpoint Nash against every `z` dominating the solo-quit rewards,
   since the endpoint difference is `r({i})_i - z_i`
   (`quittingAllContinueRoot_isZeroNash_of_singleton_le`).  So without
   fence 2 the all-Continue block would certify an essentially arbitrary
   vector -- e.g. the constant reward bound, cf. the phantom spine of
   `canonicalPhantom_isExactQuittingNashBellmanSpine` -- as a "realized"
   continuation, and its terminal mismatch would be `0`, making the whole
   objective vacuously zero.  `quittingAllContinueBlock_forced` records
   exactly this: the all-Continue block satisfies *every other clause* of the
   predicate and fails only absorption.  Requiring one stage of the block to
   have positive `quittingRootAbsorptionMass` makes the block's affine
   fixed-point equation nondegenerate, so `z` is *determined* by the block
   rather than chosen; see
   `quittingCyclicContinuation_value_eq_of_absorbing_period_one`.
3. **The terminal debt is not free either.**  It is
   `quittingTerminalContinuationMismatch`, the positive part of the solo-quit
   deviation gain *measured against `z`*.  At `z = 0` this is literally the
   existing `quittingPositiveSingletonDebtCap`
   (`quittingTerminalContinuationMismatch_zero`), so the construction
   specializes to the existing zero-pinned debt
   (`quittingCyclePinnedDynamicDebt_zero`) rather than replacing it.

## Which existing chain grammar is reused, and why

The block and the chain are both members of
`quittingFiniteAnchoredNashBellmanChainSet`, which is
`quittingFiniteZeroBoundaryNashBellmanChainSet` with the hard-coded terminal
value `0` promoted to a parameter; `quittingFiniteAnchoredNashBellmanChainSet
reward 0 = quittingFiniteZeroBoundaryNashBellmanChainSet reward` holds by
`rfl`.  Its per-stage exactness condition is the unmodified
`IsQuittingNashBellmanEdge`: the displayed value equals
`quittingRootSuccessorPayoff` of the next displayed value under the stage
root, and the stage root is *exactly* (`ε = 0`) endpoint Nash against the
next displayed value.  That is the right notion here precisely because it is
the same one the zero-pinned family is graded against: the only difference
between the two families is which vector sits at the far end, so any debt gap
between them is attributable to the boundary and to nothing else.

## What is not claimed

`quittingTerminalContinuationMismatch` is the exact analogue of the existing
terminal cap -- a one-step solo-quit gain against the boundary vector -- and
not a proven envelope for the full exploitability of the infinitely repeated
block.  No optimization over the cycle-pinned family is defined here, and no
compactness or attainment statement is made about it.

General nonnegativity of the cycle-pinned debt is not proved *in this file*.
The reason is an API limitation rather than a mathematical one:
`quittingFiniteDynamicDebt_nonneg` wants `IsQuittingLivePrescribedValue`,
which is a condition at *every* time, while
`quittingFiniteNashBellmanPathValue` and `quittingFiniteNashBellmanPathRoots`
pad beyond the cutoff with `0` and all-Continue -- a padding that is coherent
only for the zero boundary.  The debt itself never reads that padding (the
recursion is run with fuel `cutoff - time`, and
`quittingFiniteDynamicDebt_congr` below localizes it), but the global
hypothesis is unavailable here.  The periodic extension of the anchored chain
by its own cyclic block supplies it, and is built in
`QuittingCyclicPeriodicExtension`; nonnegativity is
`quittingCyclePinnedDynamicDebt_nonneg` there.

Uniqueness of the realized continuation is likewise proved only at period one
below (`quittingCyclicContinuation_unique_of_absorbing_period_one`); the
general-period form is `quittingCyclicContinuation_unique_of_absorbing` in the
same downstream file.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Chains anchored at a prescribed terminal vector -/

/-- Bounded exact Nash--Bellman chains whose terminal displayed value is the
prescribed vector `terminal`.  This is verbatim
`quittingFiniteZeroBoundaryNashBellmanChainSet` with the hard-coded `0`
promoted to a parameter; see `quittingFiniteAnchoredNashBellmanChainSet_zero`. -/
def quittingFiniteAnchoredNashBellmanChainSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (cutoff : ℕ) :
    Set (QuittingFiniteNashBellmanPath ι cutoff) :=
  {path |
    (∀ time, path time ∈
      quittingNashBellmanBox (quittingRewardBound reward)) ∧
    (path (Fin.last cutoff)).1 = terminal ∧
    ∀ time : Fin cutoff,
      IsQuittingNashBellmanEdge reward
        (path (Fin.castSucc time)) (path (Fin.succ time))}

/-- Anchoring at `0` is exactly the existing zero-boundary chain family. -/
theorem quittingFiniteAnchoredNashBellmanChainSet_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (cutoff : ℕ) :
    quittingFiniteAnchoredNashBellmanChainSet reward 0 cutoff =
      quittingFiniteZeroBoundaryNashBellmanChainSet reward cutoff := rfl

/-! ## Self-consistent (cyclic) terminal continuations -/

/-- A *cyclic continuation block* for `terminal`: an exact Nash--Bellman
chain of length `period` which is run against `terminal` at its terminal end,
reproduces `terminal` at its origin, and absorbs with positive probability at
some stage.

The last clause is the essential fence and is **not** redundant.  Dropping it
readmits the all-Continue block, whose Bellman map is the identity and which
is therefore run against, and reproduces, *every* vector dominating the
solo-quit rewards; see `quittingAllContinueBlock_forced`. -/
def IsQuittingCyclicContinuationBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι period) : Prop :=
  block ∈ quittingFiniteAnchoredNashBellmanChainSet reward terminal period ∧
    (block 0).1 = terminal ∧
    ∃ stage : Fin period,
      0 < quittingRootAbsorptionMass
        (quittingRootOfSimplex (block (Fin.castSucc stage)).2)

/-- `terminal` is realized by some absorbing exact cyclic block of length at
least one. -/
def IsQuittingCyclicContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) : Prop :=
  ∃ period : ℕ, ∃ block : QuittingFiniteNashBellmanPath ι (period + 1),
    IsQuittingCyclicContinuationBlock reward terminal (period + 1) block

/-! ## The terminal mismatch replacing the solo-quit cap -/

/-- The mismatch at the cutoff: the positive part of the solo-quit deviation
gain measured against the realized terminal continuation.  At `terminal = 0`
this is the existing `quittingPositiveSingletonDebtCap`. -/
def quittingTerminalContinuationMismatch
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (who : ι) : ℝ :=
  max 0 (quittingRootEndpointDifference reward terminal
    (quittingAllContinueRoot : ι → PMF Bool) who)

/-- Explicit form of the terminal mismatch. -/
theorem quittingTerminalContinuationMismatch_eq
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (who : ι) :
    quittingTerminalContinuationMismatch reward terminal who =
      max 0 (reward (quittingSingletonTerminal who) who - terminal who) := by
  rw [quittingTerminalContinuationMismatch,
    quittingRootEndpointDifference_allContinueRoot]

/-- The terminal mismatch is nonnegative. -/
theorem quittingTerminalContinuationMismatch_nonneg
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (who : ι) :
    0 ≤ quittingTerminalContinuationMismatch reward terminal who :=
  le_max_left _ _

/-- **Specialization check.**  Against the zero pin the terminal mismatch is
literally the solo-quit cap used by the existing zero-boundary debt. -/
theorem quittingTerminalContinuationMismatch_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingTerminalContinuationMismatch reward 0 who =
      quittingPositiveSingletonDebtCap reward who := by
  rw [quittingTerminalContinuationMismatch_eq, quittingPositiveSingletonDebtCap]
  norm_num

/-! ## The cycle-pinned dynamic debt -/

/-- The cycle-pinned dynamic debt of a chain: the exact backward Bellman debt
of `quittingFiniteDynamicDebt` run on the chain's own roots and displayed
values, with terminal debt the mismatch against `terminal` instead of the
solo-quit cap.

This is meaningful only on `quittingCyclePinnedChainSet`, which additionally
requires `terminal` to be a self-consistent cyclic continuation and the chain
to be anchored at it. -/
def quittingCyclePinnedDynamicDebt
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath ι cutoff)
    (who : ι) (time : ℕ) : ℝ :=
  quittingFiniteDynamicDebt reward
    (quittingFiniteNashBellmanPathRoots cutoff path) who
    (fun liveTime ↦
      quittingFiniteNashBellmanPathValue cutoff path liveTime who)
    (quittingTerminalContinuationMismatch reward terminal who)
    time (cutoff - time)

/-- The admissible cycle-pinned pairs at a fixed cutoff: a self-consistent
terminal continuation together with an exact chain anchored at it. -/
def quittingCyclePinnedChainSet
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (cutoff : ℕ) :
    Set (Payoff ι × QuittingFiniteNashBellmanPath ι cutoff) :=
  {pair | IsQuittingCyclicContinuation reward pair.1 ∧
    pair.2 ∈ quittingFiniteAnchoredNashBellmanChainSet reward pair.1 cutoff}

/-- **Specialization check.**  At the zero pin the cycle-pinned debt is
literally the existing zero-boundary exact dynamic debt.  (The zero pin is
generally *not* an admissible cycle-pinned terminal continuation; this is a
statement about the formula, not about admissibility.) -/
theorem quittingCyclePinnedDynamicDebt_zero
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (cutoff : ℕ)
    (path : QuittingFiniteNashBellmanPath ι cutoff) (who : ι) (time : ℕ) :
    quittingCyclePinnedDynamicDebt reward 0 cutoff path who time =
      quittingFiniteNashBellmanPathDynamicDebt reward cutoff path who time := by
  rw [quittingCyclePinnedDynamicDebt, quittingFiniteNashBellmanPathDynamicDebt,
    quittingTerminalContinuationMismatch_zero]

/-! ## A localization lemma for the finite debt recursion -/

/-- The finite dynamic debt reads its root sequence only on
`[start, start + fuel)` and its prescribed sequence only on
`[start, start + fuel]`.  This is what lets a chain-derived debt be compared
with a globally constant one. -/
theorem quittingFiniteDynamicDebt_congr
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (roots roots' : ℕ → ι → PMF Bool) (who : ι)
    (prescribed prescribed' : ℕ → ℝ) (terminalDebt : ℝ) (start fuel : ℕ)
    (hroots : ∀ time, start ≤ time → time < start + fuel →
      roots time = roots' time)
    (hprescribed : ∀ time, start ≤ time → time ≤ start + fuel →
      prescribed time = prescribed' time) :
    quittingFiniteDynamicDebt reward roots who prescribed terminalDebt
        start fuel =
      quittingFiniteDynamicDebt reward roots' who prescribed' terminalDebt
        start fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      have hstart : roots start = roots' start :=
        hroots start le_rfl (by omega)
      have htail := ih (start + 1)
        (fun time hle hlt ↦ hroots time (by omega) (by omega))
        (fun time hle hle' ↦ hprescribed time (by omega) (by omega))
      rw [quittingFiniteDynamicDebt_succ, quittingFiniteDynamicDebt_succ, htail,
        hprescribed start le_rfl (by omega),
        hprescribed (start + 1) (by omega) (by omega)]
      unfold quittingFixedOpponentsQuitValue quittingFixedOpponentsContinueReward
        quittingFixedOpponentsContinueMass
      rw [hstart]

/-! ## Self-consistency is a genuine constraint -/

omit [DecidableEq ι] in
/-- **What a length-one self-consistency forces.**  If the block root `root`
reproduces `terminal` at its origin, then every coordinate of `terminal`
satisfies the affine fixed-point equation
`absorptionMass * terminal = absorbingContribution`. -/
theorem quittingRootAbsorptionMass_mul_eq_absorbingContribution_of_fixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (root : ι → PMF Bool)
    (hfixed : terminal = quittingRootSuccessorPayoff reward terminal root)
    (who : ι) :
    quittingRootAbsorptionMass root * terminal who =
      quittingRootAbsorbingContribution reward root who := by
  have hstep := quittingRootSuccessorPayoff_sub_tail reward terminal root who
  rw [← congrFun hfixed who, sub_self] at hstep
  linarith

omit [DecidableEq ι] in
/-- **Self-consistency plus absorption determines the continuation.**  With
positive absorption the fixed-point equation is nondegenerate, so the
terminal vector is not a free parameter: it is the block's absorbed reward
divided by its absorption probability. -/
theorem quittingCyclicContinuation_value_eq_of_absorbing_period_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (root : ι → PMF Bool)
    (hfixed : terminal = quittingRootSuccessorPayoff reward terminal root)
    (habsorb : 0 < quittingRootAbsorptionMass root) (who : ι) :
    terminal who =
      quittingRootAbsorbingContribution reward root who /
        quittingRootAbsorptionMass root := by
  rw [eq_div_iff habsorb.ne', mul_comm]
  exact quittingRootAbsorptionMass_mul_eq_absorbingContribution_of_fixed
    reward terminal root hfixed who

omit [DecidableEq ι] in
/-- **The contraction step.**  One exact backward Nash--Bellman step is affine
in the continuation with scalar linear part the all-continue mass: two
continuations propagate to values differing by exactly that mass times their
difference.  Positive absorption is exactly `mass < 1`, i.e. strict
contraction. -/
theorem quittingRootSuccessorPayoff_sub
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (continuation continuation' : Payoff ι) (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward continuation root who -
        quittingRootSuccessorPayoff reward continuation' root who =
      quittingStationaryContinueMass root *
        (continuation who - continuation' who) := by
  change quittingRootExpectedPayoff reward continuation root who -
    quittingRootExpectedPayoff reward continuation' root who = _
  rw [quittingRootExpectedPayoff_eq_absorbingContribution_add,
    quittingRootExpectedPayoff_eq_absorbingContribution_add]
  ring

omit [DecidableEq ι] in
/-- **Uniqueness at period one.**  An absorbing self-reproducing root has
exactly one fixed continuation, so a length-one cyclic continuation is
determined by its root and is not a free parameter. -/
theorem quittingCyclicContinuation_unique_of_absorbing_period_one
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal terminal' : Payoff ι) (root : ι → PMF Bool)
    (hfixed : terminal = quittingRootSuccessorPayoff reward terminal root)
    (hfixed' : terminal' = quittingRootSuccessorPayoff reward terminal' root)
    (habsorb : 0 < quittingRootAbsorptionMass root) :
    terminal = terminal' := by
  funext who
  have hmass : quittingStationaryContinueMass root < 1 := by
    rw [quittingRootAbsorptionMass] at habsorb; linarith
  have hstep := quittingRootSuccessorPayoff_sub reward terminal terminal' root who
  rw [← congrFun hfixed who, ← congrFun hfixed' who] at hstep
  nlinarith [hstep]

/-- The origin edge of a cyclic continuation block of length one is exactly a
self-reproducing root, so the previous two lemmas apply to it. -/
theorem quittingCyclicContinuationBlock_one_fixed
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι)
    (block : QuittingFiniteNashBellmanPath ι 1)
    (hblock : IsQuittingCyclicContinuationBlock reward terminal 1 block) :
    terminal = quittingRootSuccessorPayoff reward terminal
      (quittingRootOfSimplex (block 0).2) := by
  have hedge := hblock.1.2.2 0
  have hlast : (block (Fin.succ 0)).1 = terminal := hblock.1.2.1
  have hcast : Fin.castSucc (0 : Fin 1) = (0 : Fin 2) := rfl
  have hstep := hedge.1
  rw [hcast, hlast] at hstep
  exact hblock.2.1.symm.trans hstep

/-! ## The all-Continue block: why the absorption fence is not redundant -/

omit [DecidableEq ι] in
/-- The all-Continue root never absorbs. -/
@[simp] theorem quittingRootAbsorptionMass_allContinueRoot :
    quittingRootAbsorptionMass (quittingAllContinueRoot : ι → PMF Bool) = 0 := by
  rw [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability]
  simp [quittingAllContinueRoot]

/-- The constant block sitting at `terminal` with the all-Continue root at
every stage. -/
def quittingAllContinueBlock
    (terminal : Payoff ι) (period : ℕ) :
    QuittingFiniteNashBellmanPath ι period :=
  fun _ ↦ (terminal, quittingAllContinueSimplexRoot)

/-- **The absorption fence is doing real work.**  For *every* vector
`terminal` that is bounded by the reward bound and dominates the solo-quit
rewards, the all-Continue block satisfies every clause of
`IsQuittingCyclicContinuationBlock` except absorption, and its absorption
mass is identically `0`.  Without the absorption clause the predicate would
therefore certify an essentially arbitrary terminal vector. -/
theorem quittingAllContinueBlock_forced
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ)
    (hbound : ∀ who, |terminal who| ≤ quittingRewardBound reward)
    (hdominate : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ terminal who) :
    quittingAllContinueBlock terminal period ∈
        quittingFiniteAnchoredNashBellmanChainSet reward terminal period ∧
      (quittingAllContinueBlock (ι := ι) terminal period 0).1 = terminal ∧
      ∀ stage : Fin period,
        quittingRootAbsorptionMass (quittingRootOfSimplex
          ((quittingAllContinueBlock (ι := ι) terminal period)
            (Fin.castSucc stage)).2) = 0 := by
  have hedge : IsQuittingNashBellmanEdge reward
      ((terminal, quittingAllContinueSimplexRoot) : QuittingNashBellmanPoint ι)
      ((terminal, quittingAllContinueSimplexRoot) : QuittingNashBellmanPoint ι) := by
    constructor
    · change terminal = quittingRootSuccessorPayoff reward terminal
        (quittingRootOfSimplex quittingAllContinueSimplexRoot)
      rw [quittingRootOfSimplex_allContinueSimplexRoot,
        quittingRootSuccessorPayoff_allContinueRoot_eq]
    · change IsεQuittingRootEndpointNash reward terminal 0
        (quittingRootOfSimplex quittingAllContinueSimplexRoot)
      rw [quittingRootOfSimplex_allContinueSimplexRoot,
        isZeroQuittingRootEndpointNash_iff_isZeroQuittingRootNash]
      exact quittingAllContinueRoot_isZeroNash_of_singleton_le reward terminal hdominate
  refine ⟨⟨fun time ↦ ?_, rfl, fun time ↦ hedge⟩, rfl, fun stage ↦ ?_⟩
  · change terminal ∈ Set.Icc (fun _ : ι ↦ -(quittingRewardBound reward))
      (fun _ ↦ quittingRewardBound reward)
    constructor
    · intro who
      have := (abs_le.mp (hbound who)).1
      exact this
    · intro who
      exact (abs_le.mp (hbound who)).2
  · change quittingRootAbsorptionMass
      (quittingRootOfSimplex (quittingAllContinueSimplexRoot : QuittingRootSimplex ι)) = 0
    rw [quittingRootOfSimplex_allContinueSimplexRoot,
      quittingRootAbsorptionMass_allContinueRoot]

/-- The all-Continue block is nevertheless **not** a cyclic continuation
block: the absorption clause fails. -/
theorem not_isQuittingCyclicContinuationBlock_allContinueBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι) (period : ℕ) :
    ¬ IsQuittingCyclicContinuationBlock reward terminal period
      (quittingAllContinueBlock terminal period) := by
  rintro ⟨-, -, stage, hstage⟩
  rw [show ((quittingAllContinueBlock (ι := ι) terminal period)
      (Fin.castSucc stage)).2 = quittingAllContinueSimplexRoot from rfl,
    quittingRootOfSimplex_allContinueSimplexRoot,
    quittingRootAbsorptionMass_allContinueRoot] at hstage
  exact lt_irrefl 0 hstage

/-! ## The structural wrapper: absorption as a field, not a side condition

`IsQuittingCyclicContinuationBlock` already states absorption, but it is a
*Prop*: a semantic consumer that merely names the Prop as a hypothesis type
can just as easily be restated, elsewhere, against a differently-shaped
hypothesis that drops the absorption conjunct -- exactly the omission
`quittingAllContinueBlock_forced` shows is silent and passes every other
clause.  `QuittingRealizedContinuation` closes that off at the type level for
every consumer that is phrased in terms of it: absorption is a *field*, so a
term of this structure cannot exist without a proof of absorption baked in,
and there is no route to one except through `IsQuittingCyclicContinuationBlock`
itself (`QuittingRealizedContinuation.ofBlock`) or an equivalent direct
construction that still has to supply the `absorbs` field. -/

/-- **A realized cyclic continuation for `terminal`.**  The structural form of
`IsQuittingCyclicContinuation`: the same three clauses as
`IsQuittingCyclicContinuationBlock`, bundled as fields of a type instead of
conjuncts of a Prop that a future hypothesis list could omit.  Consumers
stated against this structure, rather than against the raw predicate or some
future look-alike, cannot be fed a continuation whose absorption obligation
was never discharged. -/
structure QuittingRealizedContinuation
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι) where
  /-- The block has `period + 1` displayed stages. -/
  period : ℕ
  /-- The underlying exact Nash--Bellman block. -/
  block : QuittingFiniteNashBellmanPath ι (period + 1)
  /-- The block is a bounded exact Nash--Bellman chain anchored at `terminal`. -/
  mem_chainSet : block ∈
    quittingFiniteAnchoredNashBellmanChainSet reward terminal (period + 1)
  /-- The block reproduces `terminal` at its origin. -/
  origin_eq : (block 0).1 = terminal
  /-- **Absorption obligation.**  Some stage of the block absorbs with
  positive probability.  Dropping this field is exactly what would let the
  all-Continue block (`quittingAllContinueBlock`) inhabit the structure for
  every `terminal` dominating the solo-quit rewards
  (`quittingAllContinueBlock_forced`); see `block_ne_allContinueBlock` below
  for the proof that, with this field present, it cannot. -/
  absorbs : ∃ stage : Fin (period + 1),
    0 < quittingRootAbsorptionMass
      (quittingRootOfSimplex (block (Fin.castSucc stage)).2)

/-- Unbundling: a `QuittingRealizedContinuation` yields the raw
`IsQuittingCyclicContinuationBlock` predicate on its own block. -/
theorem QuittingRealizedContinuation.isQuittingCyclicContinuationBlock
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {terminal : Payoff ι}
    (rc : QuittingRealizedContinuation reward terminal) :
    IsQuittingCyclicContinuationBlock reward terminal (rc.period + 1) rc.block :=
  ⟨rc.mem_chainSet, rc.origin_eq, rc.absorbs⟩

/-- Unbundling further: a `QuittingRealizedContinuation` witnesses
`IsQuittingCyclicContinuation`. -/
theorem QuittingRealizedContinuation.isQuittingCyclicContinuation
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {terminal : Payoff ι}
    (rc : QuittingRealizedContinuation reward terminal) :
    IsQuittingCyclicContinuation reward terminal :=
  ⟨rc.period, rc.block, rc.isQuittingCyclicContinuationBlock⟩

/-- **Constructor from the existing block predicate.**  The cheap migration
path: any call site already holding an `IsQuittingCyclicContinuationBlock`
proof produces a `QuittingRealizedContinuation` for free, so existing
certificates need no rework, only their consumers' signatures change. -/
def QuittingRealizedContinuation.ofBlock
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (terminal : Payoff ι)
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1))
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block) :
    QuittingRealizedContinuation reward terminal where
  period := period
  block := block
  mem_chainSet := hblock.1
  origin_eq := hblock.2.1
  absorbs := hblock.2.2

/-- **Regression: the all-Continue block does not inhabit the wrapper**, at
any period and against any terminal.  Reuses
`not_isQuittingCyclicContinuationBlock_allContinueBlock` rather than
reproving it: unbundle `rc` to the raw predicate and apply that lemma to the
substituted block directly.  This is the precise sense in which the vacuity
trap becomes a type error here: there is no way to build a
`QuittingRealizedContinuation` whose block is the identity-Bellman
all-Continue row. -/
theorem QuittingRealizedContinuation.block_ne_allContinueBlock
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {terminal : Payoff ι}
    (rc : QuittingRealizedContinuation reward terminal) :
    rc.block ≠ quittingAllContinueBlock terminal (rc.period + 1) := by
  intro hcontra
  refine not_isQuittingCyclicContinuationBlock_allContinueBlock
    reward terminal (rc.period + 1) ?_
  rw [← hcontra]
  exact rc.isQuittingCyclicContinuationBlock

/-- Against any continuation dominating the solo-quit rewards the terminal
mismatch vanishes.  Combined with `quittingAllContinueBlock_forced` this is
the precise statement that an unfenced predicate would make the cycle-pinned
objective vacuously zero. -/
theorem quittingTerminalContinuationMismatch_eq_zero_of_singleton_le
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (terminal : Payoff ι)
    (hdominate : ∀ who,
      reward (quittingSingletonTerminal who) who ≤ terminal who) (who : ι) :
    quittingTerminalContinuationMismatch reward terminal who = 0 := by
  rw [quittingTerminalContinuationMismatch_eq]
  exact max_eq_left (sub_nonpos.mpr (hdominate who))

namespace QuittingBoundedSurgeryDescentCounterexample

/-! ## The surgery table: the zero pin is not realizable -/

/-- One backward exact Nash--Bellman step out of a `(t, 0)`-shaped displayed
value with `0 ≤ t < a` is completely forced: it lands on
`(a / (a - t + 1), 0)`, whose first coordinate is again in `[0, a)` and is
*strictly larger* than `t`.  The root is forced by
`root_forced_of_endpointNash`; only its consequence for the displayed value
is computed here. -/
theorem edge_forced_of_shape (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ)
    (ht0 : 0 ≤ t) (hta : t < a)
    (current tail : QuittingNashBellmanPoint Bool)
    (htail : tail.1 = fun who ↦ if who then (0 : ℝ) else t)
    (hedge : IsQuittingNashBellmanEdge (reward a) current tail) :
    current.1 = (fun who ↦ if who then (0 : ℝ) else a / (a - t + 1)) ∧
      0 ≤ a / (a - t + 1) ∧ a / (a - t + 1) < a ∧ t < a / (a - t + 1) := by
  set root := quittingRootOfSimplex current.2 with hroot
  have hden : 0 < a - t + 1 := by linarith
  have hnash : IsεQuittingRootEndpointNash (reward a)
      (fun who ↦ if who then (0 : ℝ) else t) 0 root := by
    rw [← htail]; exact hedge.2
  obtain ⟨hp, hq⟩ := root_forced_of_endpointNash a t ht0 hta root hnash
  have hpfalse : (root false false).toReal = 1 / 2 := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root false
    linarith
  have hqfalse : (root true false).toReal = 1 - (a - t) / (a - t + 1) := by
    have hsum := quittingRoot_continueProbability_add_quitProbability root true
    linarith
  have hvalue := hedge.1
  rw [htail] at hvalue
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hvalue]
    funext who
    rw [quittingRootSuccessorPayoff_eq_endpointMix]
    cases who
    · rw [false_quitPayoff, false_continuePayoff, hp, hpfalse, hq]
      simp only [Bool.false_eq_true, if_false]
      field_simp
      ring
    · rw [true_quitPayoff, true_continuePayoff, hp]
      simp
  · positivity
  · rw [div_lt_iff₀ hden]
    nlinarith
  · rw [lt_div_iff₀ hden]
    nlinarith [mul_pos (show (0 : ℝ) < 1 - t by linarith) (show (0 : ℝ) < a - t by linarith)]

/-- **No cyclic block of any length reproduces a `(t, 0)`-shaped value with
`0 ≤ t < a`.**  Walking backwards from the terminal end the first coordinate
strictly increases at every stage and never leaves `[0, a)`, so it cannot
return to its starting value.  Absorption is not used: the obstruction is the
exactness grammar alone. -/
theorem shape_ne_origin_of_anchoredChain (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (t : ℝ) (ht0 : 0 ≤ t) (hta : t < a) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath Bool (period + 1))
    (hmem : block ∈ quittingFiniteAnchoredNashBellmanChainSet (reward a)
      (fun who ↦ if who then (0 : ℝ) else t) (period + 1)) :
    (block 0).1 ≠ fun who ↦ if who then (0 : ℝ) else t := by
  intro hcontra
  have key : ∀ k, k ≤ period + 1 → ∃ s : ℝ, 0 ≤ s ∧ s < a ∧ t ≤ s ∧
      (0 < k → t < s) ∧
      (block ⟨period + 1 - k, by omega⟩).1 = fun who ↦ if who then (0 : ℝ) else s := by
    intro k
    induction k with
    | zero =>
        intro _
        refine ⟨t, ht0, hta, le_rfl, by omega, ?_⟩
        have hindex : (⟨period + 1 - 0, by omega⟩ : Fin (period + 2)) =
            Fin.last (period + 1) := by
          apply Fin.ext; simp
        rw [hindex]
        exact hmem.2.1
    | succ k ih =>
        intro hk
        obtain ⟨s, hs0, hsa, hts, -, hval⟩ := ih (by omega)
        have hstage : period + 1 - (k + 1) < period + 1 := by omega
        have hstep := hmem.2.2 ⟨period + 1 - (k + 1), hstage⟩
        have hcast : Fin.castSucc (⟨period + 1 - (k + 1), hstage⟩ : Fin (period + 1)) =
            (⟨period + 1 - (k + 1), by omega⟩ : Fin (period + 2)) := by
          apply Fin.ext; simp
        have hsucc : Fin.succ (⟨period + 1 - (k + 1), hstage⟩ : Fin (period + 1)) =
            (⟨period + 1 - k, by omega⟩ : Fin (period + 2)) := by
          apply Fin.ext
          simp only [Fin.val_succ]
          omega
        rw [hcast, hsucc] at hstep
        obtain ⟨hcur, hnn, hlt, hgt⟩ :=
          edge_forced_of_shape a ha0 ha1 s hs0 hsa _ _ hval hstep
        exact ⟨a / (a - s + 1), hnn, hlt, (hts.trans hgt.le), fun _ ↦ hts.trans_lt hgt, hcur⟩
  obtain ⟨s, -, -, -, hlt, hval⟩ := key (period + 1) le_rfl
  have hindex : (⟨period + 1 - (period + 1), by omega⟩ : Fin (period + 2)) = 0 := by
    apply Fin.ext; simp
  rw [hindex, hcontra] at hval
  have hcoord := congrFun hval false
  simp only [Bool.false_eq_true, if_false] at hcoord
  exact absurd hcoord (ne_of_lt (hlt (by omega)))

/-- **The zero pin is not a self-consistent continuation.**  For the surgery
weight no vector of the form `(t, 0)` with `0 ≤ t < a` is realized by any
exact cyclic block, of any length. -/
theorem not_isQuittingCyclicContinuation_of_shape (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1)
    (t : ℝ) (ht0 : 0 ≤ t) (hta : t < a) :
    ¬ IsQuittingCyclicContinuation (reward a)
      (fun who ↦ if who then (0 : ℝ) else t) := by
  rintro ⟨period, block, hmem, horigin, -⟩
  exact shape_ne_origin_of_anchoredChain a ha0 ha1 t ht0 hta period block hmem horigin

/-- In particular the zero boundary used by
`quittingFiniteZeroBoundaryNashBellmanChainSet` is *not* an admissible
cycle-pinned terminal continuation for this table.  The positive plateau of
`quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_eq` is therefore
charged against a boundary the game itself never realizes.

`HEADLINE` — the strongest form of the pin diagnosis: the zero boundary is
not a bad choice for this weight, it is an impossible one. -/
theorem not_isQuittingCyclicContinuation_zero (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ¬ IsQuittingCyclicContinuation (reward a) (0 : Payoff Bool) := by
  have hshape : (fun who : Bool ↦ if who then (0 : ℝ) else 0) = (0 : Payoff Bool) := by
    funext who; cases who <;> simp
  have h := not_isQuittingCyclicContinuation_of_shape a ha0 ha1 0 le_rfl ha0
  rwa [hshape] at h

/-! ## The stationary row is a self-consistent continuation of length one -/

/-- The stationary equilibrium value vector `(a, 0)`. -/
def stationaryValue (a : ℝ) : Payoff Bool := fun who ↦ if who then (0 : ℝ) else a

@[simp] theorem stationaryRoot_true_false (a : ℝ) :
    (stationaryRoot a true false).toReal = 1 := by simp [stationaryRoot]

/-- Simplex presentation of the stationary root. -/
def stationarySimplexRoot (a : ℝ) : QuittingRootSimplex Bool :=
  fun who ↦ stdSimplexEquiv (stationaryRoot a who)

@[simp] theorem quittingRootOfSimplex_stationarySimplexRoot (a : ℝ) :
    quittingRootOfSimplex (stationarySimplexRoot a) = stationaryRoot a := by
  funext who
  exact (stdSimplexEquiv (α := Bool)).symm_apply_apply (stationaryRoot a who)

/-- **The stationary row absorbs.**  Player one quits with probability `1/2`,
so the all-continue mass is `1/2` and the absorption mass is `1/2 > 0`: the
fence of `IsQuittingCyclicContinuationBlock` is satisfied. -/
theorem quittingRootAbsorptionMass_stationaryRoot (a : ℝ) :
    quittingRootAbsorptionMass (stationaryRoot a) = 1 / 2 := by
  rw [quittingRootAbsorptionMass,
    quittingStationaryContinueMass_eq_prod_continueProbability, Fintype.prod_bool,
    stationaryRoot_true_false, stationaryRoot_false_false]
  norm_num

/-- The stationary point is a self-loop of the exact Nash--Bellman edge
relation: `stationaryRoot_successor_eq` gives the value equation and
`stationaryRoot_isEndpointNash` the exact (`ε = 0`) Nash certificate. -/
theorem stationaryPoint_isEdge (a : ℝ) :
    IsQuittingNashBellmanEdge (reward a)
      ((stationaryValue a, stationarySimplexRoot a) : QuittingNashBellmanPoint Bool)
      ((stationaryValue a, stationarySimplexRoot a) : QuittingNashBellmanPoint Bool) := by
  constructor
  · change stationaryValue a = quittingRootSuccessorPayoff (reward a)
      (stationaryValue a) (quittingRootOfSimplex (stationarySimplexRoot a))
    rw [quittingRootOfSimplex_stationarySimplexRoot]
    exact (stationaryRoot_successor_eq a).symm
  · change IsεQuittingRootEndpointNash (reward a) (stationaryValue a) 0
      (quittingRootOfSimplex (stationarySimplexRoot a))
    rw [quittingRootOfSimplex_stationarySimplexRoot]
    exact stationaryRoot_isEndpointNash a

/-- The stationary point lies in the canonical compact Nash--Bellman box. -/
theorem stationaryPoint_mem_box (a : ℝ) (ha0 : 0 < a) :
    ((stationaryValue a, stationarySimplexRoot a) : QuittingNashBellmanPoint Bool) ∈
      quittingNashBellmanBox (quittingRewardBound (reward a)) := by
  have hM := quittingRewardBound_nonneg (reward a)
  have haM := le_quittingRewardBound a ha0
  change stationaryValue a ∈
    Set.Icc (fun _ : Bool ↦ -(quittingRewardBound (reward a)))
      (fun _ ↦ quittingRewardBound (reward a))
  constructor
  · intro who
    cases who <;> simp only [stationaryValue] <;> dsimp <;> linarith
  · intro who
    cases who <;> simp only [stationaryValue] <;> dsimp <;> linarith

/-- The length-one cyclic block sitting at the stationary row. -/
def stationaryBlock (a : ℝ) : QuittingFiniteNashBellmanPath Bool 1 :=
  fun _ ↦ (stationaryValue a, stationarySimplexRoot a)

/-- **The stationary row is a cyclic continuation block of length one.** -/
theorem stationaryBlock_isQuittingCyclicContinuationBlock (a : ℝ) (ha0 : 0 < a) :
    IsQuittingCyclicContinuationBlock (reward a) (stationaryValue a) 1
      (stationaryBlock a) := by
  refine ⟨⟨fun _ ↦ stationaryPoint_mem_box a ha0, rfl,
    fun _ ↦ stationaryPoint_isEdge a⟩, rfl, ⟨0, ?_⟩⟩
  change 0 < quittingRootAbsorptionMass
    (quittingRootOfSimplex (stationarySimplexRoot a))
  rw [quittingRootOfSimplex_stationarySimplexRoot,
    quittingRootAbsorptionMass_stationaryRoot]
  norm_num

/-- **The stationary value is a self-consistent terminal continuation.** -/
theorem stationaryValue_isQuittingCyclicContinuation (a : ℝ) (ha0 : 0 < a) :
    IsQuittingCyclicContinuation (reward a) (stationaryValue a) :=
  ⟨0, stationaryBlock a, stationaryBlock_isQuittingCyclicContinuationBlock a ha0⟩

/-! ## The cycle-pinned debt at the stationary row is zero at every cutoff -/

/-- The chain of length `cutoff` that sits at the stationary row throughout. -/
def stationaryChain (a : ℝ) (cutoff : ℕ) :
    QuittingFiniteNashBellmanPath Bool cutoff :=
  fun _ ↦ (stationaryValue a, stationarySimplexRoot a)

theorem stationaryChain_mem (a : ℝ) (ha0 : 0 < a) (cutoff : ℕ) :
    stationaryChain a cutoff ∈
      quittingFiniteAnchoredNashBellmanChainSet (reward a) (stationaryValue a) cutoff :=
  ⟨fun _ ↦ stationaryPoint_mem_box a ha0, rfl, fun _ ↦ stationaryPoint_isEdge a⟩

/-- The stationary pair is an admissible cycle-pinned pair at every cutoff. -/
theorem stationaryChain_mem_cyclePinnedChainSet (a : ℝ) (ha0 : 0 < a) (cutoff : ℕ) :
    (stationaryValue a, stationaryChain a cutoff) ∈
      quittingCyclePinnedChainSet (reward a) cutoff :=
  ⟨stationaryValue_isQuittingCyclicContinuation a ha0,
    stationaryChain_mem a ha0 cutoff⟩

/-- Against the stationary continuation the terminal mismatch vanishes for
both players: player one's solo-quit reward is exactly its realized value `a`,
and player two's is `-1 < 0`.  Contrast the zero pin, where player one's
mismatch is the strictly positive `a`. -/
theorem quittingTerminalContinuationMismatch_stationaryValue (a : ℝ) (who : Bool) :
    quittingTerminalContinuationMismatch (reward a) (stationaryValue a) who = 0 := by
  rw [quittingTerminalContinuationMismatch_eq]
  cases who
  · rw [show reward a (quittingSingletonTerminal false) false = a by
      simp [reward, quittingSingletonTerminal]]
    simp [stationaryValue]
  · rw [show reward a (quittingSingletonTerminal true) true = -1 by
      simp [reward, quittingSingletonTerminal]]
    simp [stationaryValue]

/-- Player two's exact dynamic debt against the constant stationary
continuation is zero at every horizon, the companion of
`quittingConstantDynamicDebt_eq_zero` for the other player. -/
theorem quittingConstantDynamicDebt_true_eq_zero (a : ℝ) :
    ∀ fuel start : ℕ,
      quittingFiniteDynamicDebt (reward a) (fun _ ↦ stationaryRoot a) true
        (fun _ ↦ (0 : ℝ)) 0 start fuel = 0 := by
  intro fuel
  induction fuel with
  | zero => intro start; rfl
  | succ fuel ih =>
      intro start
      rw [quittingFiniteDynamicDebt_succ_eq_endpoints, ih (start + 1),
        true_quitPayoff, true_continuePayoff, stationaryRoot_false_true]
      norm_num

/-- **The cycle-pinned debt of the stationary chain is exactly zero at every
cutoff, for both players.**  Same exact Bellman debt recursion as the
zero-pinned family, same exactness grammar, only a realized terminal
continuation instead of the pin -- and the strictly positive plateau
`dVal a m ≥ a(1 - a)` of
`quittingFiniteZeroBoundaryNashBellmanMinMaxDynamicDebt_eq` disappears. -/
theorem quittingCyclePinnedDynamicDebt_stationaryChain_eq_zero
    (a : ℝ) (cutoff : ℕ) (who : Bool) (time : ℕ) :
    quittingCyclePinnedDynamicDebt (reward a) (stationaryValue a) cutoff
      (stationaryChain a cutoff) who time = 0 := by
  rw [quittingCyclePinnedDynamicDebt,
    quittingTerminalContinuationMismatch_stationaryValue a who]
  by_cases htime : time ≤ cutoff
  · have hroots : ∀ liveTime, time ≤ liveTime → liveTime < time + (cutoff - time) →
        quittingFiniteNashBellmanPathRoots cutoff (stationaryChain a cutoff) liveTime =
          (fun _ ↦ stationaryRoot a) liveTime := by
      intro liveTime _ hlt
      have hlive : liveTime < cutoff := by omega
      simp [quittingFiniteNashBellmanPathRoots, hlive, stationaryChain]
    cases who
    · rw [quittingFiniteDynamicDebt_congr (reward a) _ (fun _ ↦ stationaryRoot a) false
        _ (fun _ ↦ a) 0 time (cutoff - time) hroots ?_]
      · exact quittingConstantDynamicDebt_eq_zero a (cutoff - time) time
      · intro liveTime _ hle
        have hlive : liveTime < cutoff + 1 := by omega
        simp [quittingFiniteNashBellmanPathValue, hlive, stationaryChain, stationaryValue]
    · rw [quittingFiniteDynamicDebt_congr (reward a) _ (fun _ ↦ stationaryRoot a) true
        _ (fun _ ↦ (0 : ℝ)) 0 time (cutoff - time) hroots ?_]
      · exact quittingConstantDynamicDebt_true_eq_zero a (cutoff - time) time
      · intro liveTime _ hle
        have hlive : liveTime < cutoff + 1 := by omega
        simp [quittingFiniteNashBellmanPathValue, hlive, stationaryChain, stationaryValue]
  · rw [show cutoff - time = 0 by omega, quittingFiniteDynamicDebt_zero]

end QuittingBoundedSurgeryDescentCounterexample

end GameTheory
