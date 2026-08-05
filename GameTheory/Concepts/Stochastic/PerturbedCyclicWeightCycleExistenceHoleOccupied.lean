/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.PerturbedCyclicWeightNoExactCycle
import GameTheory.Concepts.Stochastic.FTVEpsilonPerturbedCycleExclusion
import GameTheory.Concepts.Stochastic.QuittingHazardRowBridge
import GameTheory.Concepts.Stochastic.QuittingCyclicPeriodicExtension

/-!
# The trichotomy's cycle-existence hole is occupied

`PerturbedCyclicWeightNoExactCycle` proves, in the real-hazard encoding
(`ZMod m` phases, `perturbedWeight ε`), that for `ε ∈ (0, 2]` no `ExactCycle`
of any period exists. `FTVEpsilonPerturbedCycleExclusion` builds the same
`ε`-bonus table on the `PMF Bool`-mixture side (`ftvRewardEps ε`) that the
trichotomy of `QuittingThreeBranchDisjunction` is stated against, and shows
period-one and period-three cycles fail for it, but explicitly stops short of
the all-periods statement.

This file supplies the missing cycle-level bridge and concludes: for
`ε ∈ (0, 2]`, `ftvRewardEps ε` admits **no** `IsQuittingCyclicContinuation` of
any period. Since the trichotomy `quittingCycle_zeroSolo_or_admissible_or_isolatedNegative`
of `QuittingThreeBranchDisjunction` is conditioned on
`∃ terminal, IsQuittingCyclicContinuation reward terminal`, this weight sits
outside its hypothesis at every `ε ∈ (0, 2]`: it is a genuine occupant of the
"weights admitting no absorbing complementary cycle of any period" residue
that file's docstring names as open.

## Weight alignment

`Player` (`FTVCyclicMinimality.Player`) and `CyclicIndex`
(`QuittingCyclicWeightRowDichotomy.CyclicIndex`) are both `abbrev _ := Fin 3`,
hence definitionally the same type, so the two tables can be compared without
any relabeling map. `weightOfReward_ftvRewardEps_eq_perturbedWeight` decides
the two tables entry by entry (`fin_cases` on the coalition and the
coordinate, `decide` on which branch of each `if`-chain fires) and finds them
identical under the identity map on that shared type -- no offset, scaling,
or successor-convention mismatch.

## Cycle transport

`IsQuittingCyclicContinuationBlock.toExactCycle` builds, from a PMF-side
cyclic continuation block of period `period + 1`, a real-side `ExactCycle` of
the same period. The construction reuses `QuittingCyclicPeriodicExtension`'s
periodic value/root extension at `cutoff := 0` (a pure period, no anchored
prefix) rather than re-deriving the wrap-around indexing by hand: the block's
own edge relation supplies the Bellman recursion and the exact endpoint-Nash
certificate at every phase, translated coordinatewise through
`QuittingHazardRowBridge`'s row-level bridge at `ε = 0`, and the block's
positive-absorption clause supplies the strict survival bound.

## The conclusion

`not_isQuittingCyclicContinuation_ftvRewardEps` contraposes the transport
against `PerturbedCyclicWeightNoExactCycle.no_exactCycle`.
-/

set_option autoImplicit false

noncomputable section

namespace GameTheory

open Math.Probability Math.ProbabilityMassFunction Math.PMFProduct
open FTVCyclicMinimality
open FTVCyclicAdmissibleCycle (ftvReward)
open FTVEpsilonPerturbedCycleExclusion (ftvRewardEps)

/-! ## Weight alignment -/

/-- **Weight alignment.** The PMF-side `ε`-bonus reward `ftvRewardEps ε`,
extended to a real weight by `weightOfReward`, is *exactly*
`perturbedWeight ε`, under the identity map on the shared type `Fin 3`
(`Player` and `CyclicIndex` are both `abbrev _ := Fin 3`). No relabeling of
players or phases and no scaling is used: the two tables were transcribed
from the same source with the same 0-indexed cyclic convention. -/
theorem weightOfReward_ftvRewardEps_eq_perturbedWeight (ε : ℝ) :
    weightOfReward (ftvRewardEps ε) = perturbedWeight ε := by
  funext S i
  fin_cases S <;> fin_cases i <;>
    simp (config := { decide := true }) [weightOfReward, perturbedWeight, ftvRewardEps,
      ftvReward, terminalReward]

/-! ## The Bellman translation at a single stage -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The PMF-side successor payoff is the real-side Bellman split.** At a
coordinate `who`, the one-stage successor payoff against `root` and `tail`
equals `x_who Σ_who + (1 - x_who) Γ_who` at the hazard row `x = hazardOfRoot
root`, against the real weight `weightOfReward reward`. This is the
coordinatewise identity the cycle transport reads the block's value
recursion through: it is exactly the shape of `ExactCycle.bellman`. -/
theorem quittingRootSuccessorPayoff_eq_bellman
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (tail : Payoff ι)
    (root : ι → PMF Bool) (who : ι) :
    quittingRootSuccessorPayoff reward tail root who =
      hazardOfRoot root who * sigmaValue (weightOfReward reward) (hazardOfRoot root) who +
        (1 - hazardOfRoot root who) *
          gammaValue (weightOfReward reward) (hazardOfRoot root) who (tail who) := by
  rw [quittingRootSuccessorPayoff_eq_endpointMix, quittingRootQuitPayoff_eq_sigmaValue,
    quittingRootContinuePayoff_eq_gammaValue]
  have hsum := quittingRoot_continueProbability_add_quitProbability root who
  have hx : (root who true).toReal = hazardOfRoot root who := rfl
  rw [hx] at hsum ⊢
  have hy : (root who false).toReal = 1 - hazardOfRoot root who := by linarith
  rw [hy]

omit [DecidableEq ι] in
/-- **The real-side survival factor is the PMF-side stationary continue
mass.** `continueMass` reads a row of hazards; `quittingStationaryContinueMass`
reads a product root action; `hazardOfRoot` is the bridge, and the two
factorizations (`∏ i, (1 - x i)` against `∏ player, (root player false).toReal`)
agree termwise. -/
theorem continueMass_hazardOfRoot (root : ι → PMF Bool) :
    continueMass (hazardOfRoot root) = quittingStationaryContinueMass root := by
  rw [quittingStationaryContinueMass_eq_prod_continueProbability]
  unfold continueMass
  refine Finset.prod_congr rfl fun i _ => ?_
  have hsum := quittingRoot_continueProbability_add_quitProbability root i
  have hx : (root i true).toReal = hazardOfRoot root i := rfl
  rw [hx] at hsum
  linarith

/-! ## `ZMod` successor arithmetic and the pure-period extension -/

/-- The `ZMod`-valuation of `t + 1` is the naive successor of `t`'s
valuation, reduced mod `m`. The cyclic-index bookkeeping the transport needs
reduces to this one fact. -/
theorem zmod_val_add_one {m : ℕ} [NeZero m] (t : ZMod m) :
    (t + 1).val = (t.val + 1) % m := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

omit [DecidableEq ι] in
/-- **The pure-period extension is periodic mod its own period.** At
`cutoff = 0` `quittingCyclicPeriodicValue` reads only `time % (period + 1)`,
so any two times with the same residue display the same value. This is what
lets the extension be re-indexed by `ZMod (period + 1)`. -/
theorem quittingCyclicPeriodicValue_zero_periodic
    (path : QuittingFiniteNashBellmanPath ι 0) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι (period + 1)) (t1 t2 : ℕ)
    (hmod : t1 % (period + 1) = t2 % (period + 1)) :
    quittingCyclicPeriodicValue 0 path period block t1 =
      quittingCyclicPeriodicValue 0 path period block t2 := by
  have hstage : quittingCyclicPeriodicStage 0 period t1 =
      quittingCyclicPeriodicStage 0 period t2 :=
    Fin.ext (by simpa [quittingCyclicPeriodicStage] using hmod)
  rw [quittingCyclicPeriodicValue_of_le 0 path period block t1 (Nat.zero_le _),
    quittingCyclicPeriodicValue_of_le 0 path period block t2 (Nat.zero_le _), hstage]

omit [DecidableEq ι] in
/-- The root companion of `quittingCyclicPeriodicValue_zero_periodic`. -/
theorem quittingCyclicPeriodicRoots_zero_periodic
    (path : QuittingFiniteNashBellmanPath ι 0) (period : ℕ)
    (block : QuittingFiniteNashBellmanPath ι (period + 1)) (t1 t2 : ℕ)
    (hmod : t1 % (period + 1) = t2 % (period + 1)) :
    quittingCyclicPeriodicRoots 0 path period block t1 =
      quittingCyclicPeriodicRoots 0 path period block t2 := by
  have hstage : quittingCyclicPeriodicStage 0 period t1 =
      quittingCyclicPeriodicStage 0 period t2 :=
    Fin.ext (by simpa [quittingCyclicPeriodicStage] using hmod)
  rw [quittingCyclicPeriodicRoots_of_le 0 path period block t1 (Nat.zero_le _),
    quittingCyclicPeriodicRoots_of_le 0 path period block t2 (Nat.zero_le _), hstage]

/-- **The block's own origin, as a length-zero path.** Anchoring
`QuittingCyclicPeriodicExtension`'s periodic extension at `cutoff := 0` with
this trivial path makes the extension a pure period: no anchored prefix, just
the block repeated forever. -/
def cyclicBlockOriginPath (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1)) :
    QuittingFiniteNashBellmanPath ι 0 :=
  fun _ => block 0

/-- **The block's displayed value, read at every natural time by pure
repetition.** -/
noncomputable def cyclicBlockValueN
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1)) :
    ℕ → Payoff ι :=
  quittingCyclicPeriodicValue 0 (cyclicBlockOriginPath period block) period block

/-- **The block's root, read at every natural time by pure repetition.** -/
noncomputable def cyclicBlockRootN
    (period : ℕ) (block : QuittingFiniteNashBellmanPath ι (period + 1)) :
    ℕ → ι → PMF Bool :=
  quittingCyclicPeriodicRoots 0 (cyclicBlockOriginPath period block) period block

omit [DecidableEq ι] in
/-- **A single absorbing phase forces the cyclic survival product below
one.** The `ZMod`-indexed analogue of
`prod_quittingStationaryContinueMass_lt_one_of_absorbing`; proved directly,
by the same one-factor-out argument, rather than converted from the `Fin`
form. -/
theorem prod_quittingStationaryContinueMass_zmod_lt_one_of_absorbing
    {m : ℕ} [NeZero m] (roots : ZMod m → ι → PMF Bool) (t0 : ZMod m)
    (habsorb : 0 < quittingRootAbsorptionMass (roots t0)) :
    (∏ t : ZMod m, quittingStationaryContinueMass (roots t)) < 1 := by
  have hmem : t0 ∈ (Finset.univ : Finset (ZMod m)) := Finset.mem_univ _
  have hsplit := Finset.mul_prod_erase (Finset.univ : Finset (ZMod m))
    (fun t ↦ quittingStationaryContinueMass (roots t)) hmem
  have hle : (∏ t ∈ (Finset.univ : Finset (ZMod m)).erase t0,
      quittingStationaryContinueMass (roots t)) ≤ 1 :=
    Finset.prod_le_one (fun t _ ↦ quittingStationaryContinueMass_nonneg (roots t))
      (fun t _ ↦ quittingStationaryContinueMass_le_one (roots t))
  have hnonneg : 0 ≤ quittingStationaryContinueMass (roots t0) :=
    quittingStationaryContinueMass_nonneg (roots t0)
  have hlt : quittingStationaryContinueMass (roots t0) < 1 := by
    rw [quittingRootAbsorptionMass] at habsorb; linarith
  calc (∏ t : ZMod m, quittingStationaryContinueMass (roots t)) =
      quittingStationaryContinueMass (roots t0) *
        ∏ t ∈ (Finset.univ : Finset (ZMod m)).erase t0,
          quittingStationaryContinueMass (roots t) := hsplit.symm
    _ ≤ quittingStationaryContinueMass (roots t0) * 1 :=
        mul_le_mul_of_nonneg_left hle hnonneg
    _ = quittingStationaryContinueMass (roots t0) := mul_one _
    _ < 1 := hlt

/-! ## Cycle transport -/

/-- **Cycle transport.** A PMF-side cyclic continuation block of period
`period + 1` produces a real-side `ExactCycle` of the same period, for the
extended weight `weightOfReward reward`: the row at phase `t` is the block's
own hazard row at (the residue of) `t`, the value is the block's own
displayed value there, the Bellman recursion and exact row complementarity
are the block's edge relation translated coordinatewise through
`quittingRootSuccessorPayoff_eq_bellman` and
`isExactRowComplementary_hazardOfRoot_iff`, and the strict survival bound is
the block's positive-absorption clause. -/
noncomputable def IsQuittingCyclicContinuationBlock.toExactCycle
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι} {terminal : Payoff ι}
    {period : ℕ} {block : QuittingFiniteNashBellmanPath ι (period + 1)}
    (hblock : IsQuittingCyclicContinuationBlock reward terminal (period + 1) block) :
    ExactCycle (weightOfReward reward) (period + 1) where
  row := fun t i => hazardOfRoot (cyclicBlockRootN period block t.val) i
  value := fun t => cyclicBlockValueN period block t.val
  row_nonneg := fun t i => hazardOfRoot_nonneg _ i
  row_le_one := fun t i => hazardOfRoot_le_one _ i
  bellman := by
    intro t i
    have hcycle : (block 0).1 = (block (Fin.last (period + 1))).1 :=
      hblock.2.1.trans hblock.1.2.1.symm
    have hrec := congrFun (quittingCyclicPeriodicValue_eq_successor 0
      (cyclicBlockOriginPath period block) period block reward
      (fun stage => stage.elim0) hblock.1.2.2 rfl hcycle t.val) i
    rw [quittingRootSuccessorPayoff_eq_bellman] at hrec
    have hvsucc : cyclicBlockValueN period block (t + 1).val =
        cyclicBlockValueN period block (t.val + 1) :=
      quittingCyclicPeriodicValue_zero_periodic (cyclicBlockOriginPath period block) period block
        (t + 1).val (t.val + 1)
        (by rw [Nat.mod_eq_of_lt (ZMod.val_lt (t + 1)), zmod_val_add_one])
    rw [hvsucc]
    exact hrec
  exact_row := by
    intro t
    have hcycle : (block 0).1 = (block (Fin.last (period + 1))).1 :=
      hblock.2.1.trans hblock.1.2.1.symm
    have hvsucc : cyclicBlockValueN period block (t + 1).val =
        cyclicBlockValueN period block (t.val + 1) :=
      quittingCyclicPeriodicValue_zero_periodic (cyclicBlockOriginPath period block) period block
        (t + 1).val (t.val + 1)
        (by rw [Nat.mod_eq_of_lt (ZMod.val_lt (t + 1)), zmod_val_add_one])
    have hvstage : cyclicBlockValueN period block (t.val + 1) =
        (block (Fin.succ (quittingCyclicPeriodicStage 0 period t.val))).1 :=
      quittingCyclicPeriodicValue_succ_of_le 0 (cyclicBlockOriginPath period block) period block
        hcycle t.val (Nat.zero_le _)
    have hrstage : cyclicBlockRootN period block t.val =
        quittingRootOfSimplex
          (block (Fin.castSucc (quittingCyclicPeriodicStage 0 period t.val))).2 :=
      quittingCyclicPeriodicRoots_of_le 0 (cyclicBlockOriginPath period block) period block
        t.val (Nat.zero_le _)
    have hnash := (hblock.1.2.2 (quittingCyclicPeriodicStage 0 period t.val)).2
    rw [hvsucc, hvstage, hrstage]
    exact (isExactRowComplementary_hazardOfRoot_iff reward _ _).mpr hnash
  survival := by
    obtain ⟨stage, habsorb⟩ := hblock.2.2
    have hval : (stage : ZMod (period + 1)).val = stage.val := rfl
    have hstageEq :
        quittingCyclicPeriodicStage 0 period (stage : ZMod (period + 1)).val = stage := by
      apply Fin.ext
      change (stage : ZMod (period + 1)).val % (period + 1) = stage.val
      rw [hval, Nat.mod_eq_of_lt stage.isLt]
    have hrstage : cyclicBlockRootN period block (stage : ZMod (period + 1)).val =
        quittingRootOfSimplex (block (Fin.castSucc stage)).2 := by
      unfold cyclicBlockRootN
      rw [quittingCyclicPeriodicRoots_of_le 0 (cyclicBlockOriginPath period block) period block
        (stage : ZMod (period + 1)).val (Nat.zero_le _), hstageEq]
    have habsorb' : 0 < quittingRootAbsorptionMass
        (cyclicBlockRootN period block (stage : ZMod (period + 1)).val) := by
      rw [hrstage]; exact habsorb
    have hprod := prod_quittingStationaryContinueMass_zmod_lt_one_of_absorbing
      (fun t : ZMod (period + 1) => cyclicBlockRootN period block t.val)
      (stage : ZMod (period + 1)) habsorb'
    have heq : ∀ t : ZMod (period + 1),
        continueMass (fun i => hazardOfRoot (cyclicBlockRootN period block t.val) i) =
          quittingStationaryContinueMass (cyclicBlockRootN period block t.val) :=
      fun t => continueMass_hazardOfRoot _
    simpa only [heq] using hprod

/-! ## The conclusion -/

/-- **The trichotomy's cycle-existence hole is occupied.** For `ε ∈ (0, 2]`,
`ftvRewardEps ε` admits no self-consistent absorbing cyclic continuation of
any period at all -- not merely no period-one or period-three one. By
contraposition through `IsQuittingCyclicContinuationBlock.toExactCycle` and
the weight alignment, a cyclic continuation block would produce an
`ExactCycle (perturbedWeight ε)` of the same period, which
`PerturbedCyclicWeightNoExactCycle.no_exactCycle` excludes. Consequently
`ftvRewardEps ε` sits outside the hypothesis of
`quittingCycle_zeroSolo_or_admissible_or_isolatedNegative`
(`QuittingThreeBranchDisjunction`): it is a genuine occupant of the
"weights admitting no absorbing complementary cycle of any period" residue
that trichotomy's own docstring names as open. -/
theorem not_isQuittingCyclicContinuation_ftvRewardEps (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2)
    (terminal : Payoff Player) :
    ¬ IsQuittingCyclicContinuation (ftvRewardEps ε) terminal := by
  rintro ⟨period, block, hblock⟩
  have C := hblock.toExactCycle
  rw [weightOfReward_ftvRewardEps_eq_perturbedWeight] at C
  exact no_exactCycle ε hε hε2 C

/-- **Existential form.** For `ε ∈ (0, 2]`, no terminal vector at all is a
self-consistent cyclic continuation of `ftvRewardEps ε`. This is the exact
negation of the trichotomy's own hypothesis
(`∃ terminal, IsQuittingCyclicContinuation reward terminal`), stated in the
trichotomy's own vocabulary. -/
theorem not_exists_isQuittingCyclicContinuation_ftvRewardEps
    (ε : ℝ) (hε : 0 < ε) (hε2 : ε ≤ 2) :
    ¬ ∃ terminal, IsQuittingCyclicContinuation (ftvRewardEps ε) terminal := by
  rintro ⟨terminal, hterminal⟩
  exact not_isQuittingCyclicContinuation_ftvRewardEps ε hε hε2 terminal hterminal

end GameTheory
