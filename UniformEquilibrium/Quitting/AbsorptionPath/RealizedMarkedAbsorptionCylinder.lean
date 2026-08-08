/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import UniformEquilibrium.Quitting.Boundary.Holonomy.Basic
import Math.PMFProduct.CoalitionMass
import Math.SurvivalProduct

/-!
# Realized finite marked absorption cylinders

This file is a source-retaining realization adapter for the marked-
absorption-path route.  It deliberately has no source-forgetting cylinder,
infinite carrier, topology, closure statement, or decoder.  A realized object
retains an existing calibrated exact-`D` `QuittingAnchoredBoundaryBlock`,
including its literal horizon and chronology; its stored endpoint scalars and
packet/debt coordinates are pinned back to that source.

The absorption samples use `Math.PMFProduct.coalitionMass` and retain their
chronological stage index.  Thus zero-mass stages remain visible and the
obstacle is not presented as a function of accumulated mass.  The final
index of an obstacle sample is the existing finite-horizon zero-boundary
(`never`) sentinel.  It is not generally an obstacle quit date and is not
equal to the holonomy `early` cap (for example, with negative quit rewards it
contributes zero while the early cap may be negative).  Mark transport,
source-forgetting, and all infinite-path claims remain open obligations of
the later generalized-trace layer.
-/

noncomputable section

namespace GameTheory

open Math.Probability Math.PMFProduct

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Finite rows and clocks -/

/-- The Bernoulli quit-rate family associated with a product root. -/
def quittingRootQuitRates (root : ι → PMF Bool) : ι → ℝ :=
  fun who => (root who true).toReal

/-- Mass of exactly the displayed nonempty coalition at one live row. -/
def quittingRootCoalitionMass (root : ι → PMF Bool)
    (coalition : Finset ι) : ℝ :=
  coalitionMass (quittingRootQuitRates root) coalition

/-- Full survival through a bounded prefix of the realized block. -/
def realizedBlockFullSurvival
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) (fuel : ℕ)
    (_hfuel : fuel ≤ block.length) : ℝ :=
  Math.survivalProduct
    (fun time => quittingStationaryContinueMass
      (anchor.roots time)) block.start fuel

@[simp] theorem realizedBlockFullSurvival_zero
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) :
    realizedBlockFullSurvival block 0 (by simp) = 1 := by
  simp [realizedBlockFullSurvival]

theorem realizedBlockFullSurvival_succ
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) (fuel : ℕ)
    (hfuel : fuel + 1 ≤ block.length) :
    realizedBlockFullSurvival block (fuel + 1) hfuel =
      realizedBlockFullSurvival block fuel (by omega) *
        quittingStationaryContinueMass
          (anchor.roots (block.start + fuel)) := by
  exact Math.survivalProduct_succ _ block.start fuel

theorem realizedBlockFullSurvival_add
    {reward : {S : Finset ι // S.Nonempty} → Payoff ι}
    [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) (first second : ℕ)
    (hfuel : first + second ≤ block.length) :
    realizedBlockFullSurvival block (first + second) hfuel =
      realizedBlockFullSurvival block first (by omega) *
        Math.survivalProduct
          (fun time => quittingStationaryContinueMass
            (anchor.roots time)) (block.start + first) second := by
  exact Math.survivalProduct_add _ block.start first second

theorem quittingRootCoalitionMass_sum_nonempty
    (root : ι → PMF Bool) :
    (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
      quittingRootCoalitionMass root coalition) =
      1 - quittingStationaryContinueMass root := by
  have hcoalition :=
    sum_coalitionMass_nonempty (quittingRootQuitRates root)
  have hcontinue :
      continueMass (quittingRootQuitRates root) =
        quittingStationaryContinueMass root := by
    rw [continueMass, quittingStationaryContinueMass_eq_prod_continueProbability]
    congr 1
    funext who
    have hsum := quittingRoot_continueProbability_add_quitProbability root who
    change 1 - (root who true).toReal = (root who false).toReal
    linarith
  simpa [quittingRootCoalitionMass, hcontinue] using hcoalition

/-! ## The finite marked object -/

/--
A source-retaining realized marked absorption cylinder over one existing
calibrated chain.  It is an adapter for finite semantics, not the
source-forgetting target cylinder.

The fields `sExit`, `chi`, `cap`, `preterminalSurvival`, `terminalMass`,
`advantage`, and `entryDebt` are intentionally stored rather than defined by
projection.  Their accompanying pins make the representation exact while
leaving a future compactification free to use them as coordinates.
-/
structure RealizedMarkedAbsorptionCylinder
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    [Nonempty ι]
    (anchor : QuittingCalibratedTerminalAnchor reward) where
  block : QuittingAnchoredBoundaryBlock anchor
  sExit : ℝ
  sExit_pin : sExit = realizedBlockFullSurvival block block.length le_rfl
  chi : ι → ℝ
  chi_pin : ∀ who, chi who =
    quittingOpponentSurvivalWeight anchor.roots who block.start block.length
  cap : ι → ℝ
  cap_pin : ∀ who, cap who =
    QuittingMaxAffineSummary.early (block.holonomy.bestResponse who)
  preterminalSurvival : ℝ
  preterminalSurvival_pin : preterminalSurvival =
    anchor.preterminalSurvival
  terminalMass : ℝ
  terminalMass_pin : terminalMass = anchor.terminalMass
  advantage : ℝ
  advantage_pin : advantage = quittingTerminalOpponentAdvantage
    reward anchor.owner anchor.action
  entryDebt : Payoff ι
  entryDebt_pin : entryDebt = block.entry.2

namespace RealizedMarkedAbsorptionCylinder

variable {reward : {S : Finset ι // S.Nonempty} → Payoff ι}

/-- Construct the pinned cylinder carried by any finite anchored block. -/
def ofBlock [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (block : QuittingAnchoredBoundaryBlock anchor) :
    RealizedMarkedAbsorptionCylinder reward anchor where
  block := block
  sExit := realizedBlockFullSurvival block block.length le_rfl
  sExit_pin := rfl
  chi := fun who =>
    quittingOpponentSurvivalWeight anchor.roots who block.start block.length
  chi_pin := fun _ => rfl
  cap := fun who =>
    QuittingMaxAffineSummary.early (block.holonomy.bestResponse who)
  cap_pin := fun _ => rfl
  preterminalSurvival := anchor.preterminalSurvival
  preterminalSurvival_pin := rfl
  terminalMass := anchor.terminalMass
  terminalMass_pin := rfl
  advantage := quittingTerminalOpponentAdvantage reward anchor.owner anchor.action
  advantage_pin := rfl
  entryDebt := block.entry.2
  entryDebt_pin := rfl

@[simp] theorem length_eq [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) :
    c.block.length = c.block.extra + 1 := by
  rfl

/-- The entry and exit exact-`D` anchors retained by the cylinder. -/
def entryAnchor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) : QuittingDebtPoint ι :=
  c.block.entry

def exitAnchor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) : QuittingDebtPoint ι :=
  c.block.exit

theorem sExit_nonneg [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) :
    0 ≤ c.sExit := by
  rw [c.sExit_pin]
  exact Math.survivalProduct_nonneg _
    (fun time => quittingStationaryContinueMass_nonneg _)
    c.block.start c.block.length

theorem sExit_le_one [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) :
    c.sExit ≤ 1 := by
  rw [c.sExit_pin]
  exact Math.survivalProduct_le_one _
    (fun time => quittingStationaryContinueMass_nonneg _)
    (fun time => quittingStationaryContinueMass_le_one _) c.block.start
      c.block.length

theorem chi_nonneg [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) (who : ι) :
    0 ≤ c.chi who := by
  rw [c.chi_pin]
  exact quittingOpponentSurvivalWeight_nonneg _ _ _ _

theorem chi_le_one [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) (who : ι) :
    c.chi who ≤ 1 := by
  rw [c.chi_pin]
  exact quittingOpponentSurvivalWeight_le_one _ _ _ _

theorem entryDebt_eq [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) :
    c.entryDebt = (c.entryAnchor).2 := by
  exact c.entryDebt_pin

theorem entryAnchor_eq_debtPoint [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) :
    c.entryAnchor = anchor.debtPoint c.block.start := rfl

theorem exitAnchor_eq_debtPoint [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) :
    c.exitAnchor = anchor.debtPoint (c.block.start + c.block.length) := rfl

/-! ## Absorption samples and obstacle samples -/

/-- Chronological absorption atom at a block offset. -/
def absorptionAtom [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (offset : ℕ) (_hoffset : offset < c.block.length)
    (coalition : Finset ι) : ℝ :=
  quittingRootCoalitionMass
    (anchor.roots (c.block.start + offset)) coalition

/-- The accumulated mass of a coalition through a finite prefix. -/
def absorptionPathValue [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (fuel : ℕ) (hfuel : fuel ≤ c.block.length)
    (coalition : Finset ι) : ℝ :=
  ∑ offset : Fin fuel,
    realizedBlockFullSurvival c.block offset.val (by omega) *
      c.absorptionAtom offset.val (by omega) coalition

theorem absorptionPathValue_zero [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) (coalition : Finset ι) :
    c.absorptionPathValue 0 (by simp) coalition = 0 := by
  simp [absorptionPathValue]

theorem absorptionPath_total_eq_one_sub_survival [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) (fuel : ℕ)
    (hfuel : fuel ≤ c.block.length) :
  (∑ coalition ∈ Finset.univ.erase (∅ : Finset ι),
      c.absorptionPathValue fuel hfuel coalition) =
      1 - realizedBlockFullSurvival c.block fuel hfuel := by
  unfold absorptionPathValue
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp_rw [absorptionAtom]
  simp_rw [quittingRootCoalitionMass_sum_nonempty]
  induction fuel with
  | zero => simp [realizedBlockFullSurvival]
  | succ fuel ih =>
      rw [Fin.sum_univ_castSucc]
      have htail :
          (∑ i : Fin fuel,
            realizedBlockFullSurvival c.block i.castSucc (by omega) *
              (1 - quittingStationaryContinueMass
                (anchor.roots (c.block.start + i.castSucc)))) =
            1 - realizedBlockFullSurvival c.block fuel (by omega) := by
        convert ih (by omega) using 1
        all_goals rfl
      rw [htail, realizedBlockFullSurvival_succ]
      simp only [Fin.val_last]
      ring_nf

/-- Literal finite quit-time obstacle samples, retaining their stage index.
The last index is the standard zero-boundary `never` sentinel. -/
def obstacleSample [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) : ℝ :=
  quittingFinitePureTimePayoff reward anchor.roots who c.block.start
    c.block.extra offset

theorem obstacleSample_eq_pureTime [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (offset : Fin c.block.length) :
    c.obstacleSample who offset =
      quittingFinitePureTimePayoff reward anchor.roots who c.block.start
        c.block.extra offset := rfl

/-! ## Pinned endpoint and packet identities -/

theorem sExit_eq_holonomy_survival [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) (who : ι) :
    c.sExit = QuittingAffineSummary.survival
      (c.block.holonomy.prescribed who) := by
  have h := quittingFiniteBoundaryHolonomy_prescribed_survival
    reward anchor.roots c.block.start c.block.extra who
  calc
    c.sExit = realizedBlockFullSurvival c.block c.block.length le_rfl :=
      c.sExit_pin
    _ = quittingFiniteFullSurvivalWeight anchor.roots anchor.owner
        (fun time => anchor.roots time anchor.owner) c.block.start
          (c.block.extra + 1) := by
      rw [quittingFiniteFullSurvivalWeight_self_eq_survivalProduct]
      rfl
    _ = quittingFiniteFullSurvivalWeight anchor.roots who
        (fun time => anchor.roots time who) c.block.start
          (c.block.extra + 1) := by
      rw [quittingFiniteFullSurvivalWeight_self_eq_survivalProduct,
        quittingFiniteFullSurvivalWeight_self_eq_survivalProduct]
    _ = QuittingAffineSummary.survival
        ((quittingFiniteBoundaryHolonomy reward anchor.roots
          c.block.start c.block.extra).prescribed who) := h.symm
    _ = QuittingAffineSummary.survival
        (c.block.holonomy.prescribed who) := rfl

theorem chi_eq_holonomy_survival [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) (who : ι) :
    c.chi who = QuittingMaxAffineSummary.survival
      (c.block.holonomy.bestResponse who) := by
  rw [c.chi_pin]
  exact (quittingFiniteBoundaryHolonomy_bestResponse_survival
    reward anchor.roots c.block.start c.block.extra who).symm

theorem packetMass [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) :
    c.preterminalSurvival * c.terminalMass =
      anchor.preterminalSurvival * anchor.terminalMass := by
  rw [c.preterminalSurvival_pin, c.terminalMass_pin]

theorem cap_eq_holonomy_early [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) (who : ι) :
    c.cap who = QuittingMaxAffineSummary.early
      (c.block.holonomy.bestResponse who) := c.cap_pin who

theorem advantage_eq_anchor [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor) :
    c.advantage = quittingTerminalOpponentAdvantage
      reward anchor.owner anchor.action := c.advantage_pin

/-- Prescribed continuation evaluation at an arbitrary exit payoff. -/
def prescribedValue [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (terminalValue : ℝ) : ℝ :=
  (c.block.holonomy.prescribed who).eval terminalValue

/-- Unilateral finite-horizon evaluation at an arbitrary exit payoff. -/
def unilateralValue [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (terminalValue : ℝ) : ℝ :=
  (c.block.holonomy.bestResponse who).eval terminalValue

theorem prescribedValue_eq_literal [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (terminalValue : ℝ) :
    c.prescribedValue who terminalValue =
      quittingFiniteTerminalHazardValue reward anchor.roots who
        (fun time => anchor.roots time who) terminalValue
        c.block.start c.block.length := by
  exact c.block.prescribed_eval who terminalValue

theorem unilateralValue_eq_literal [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (c : RealizedMarkedAbsorptionCylinder reward anchor)
    (who : ι) (terminalValue : ℝ) :
    c.unilateralValue who terminalValue =
      quittingFiniteTerminalBestResponseValue reward anchor.roots who
        terminalValue c.block.start c.block.length := by
  exact c.block.bestResponse_eval who terminalValue

/-!
## Same-source realized concatenation

The following operations concern only adjacent blocks cut from the same
calibrated source anchor.  They establish source holonomy and clock laws;
they are not composition laws for a source-forgetting cylinder and make no
claim about absorption-path, obstacle, cap, packet, or debt composition.
-/

def concat [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    RealizedMarkedAbsorptionCylinder reward anchor :=
  ofBlock (outer.block.concat inner.block hadjacent)

@[simp] theorem length_concat [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    (outer.concat inner hadjacent).block.length =
      outer.block.length + inner.block.length := by
  change (outer.block.concat inner.block hadjacent).length =
    outer.block.length + inner.block.length
  exact QuittingAnchoredBoundaryBlock.length_concat
    outer.block inner.block hadjacent

theorem seam_eq [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    outer.exitAnchor = inner.entryAnchor := by
  exact QuittingAnchoredBoundaryBlock.exit_eq_entry_of_adjacent
    outer.block inner.block hadjacent

theorem holonomy_concat [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    (outer.concat inner hadjacent).block.holonomy =
      outer.block.holonomy * inner.block.holonomy := by
  exact QuittingAnchoredBoundaryBlock.holonomy_concat
    outer.block inner.block hadjacent

theorem fullSurvival_concat [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) :
    realizedBlockFullSurvival
        (outer.block.concat inner.block hadjacent)
        (outer.block.length + inner.block.length) (by
          rw [QuittingAnchoredBoundaryBlock.length_concat]) =
    realizedBlockFullSurvival outer.block outer.block.length le_rfl *
        realizedBlockFullSurvival inner.block inner.block.length le_rfl := by
  change Math.survivalProduct
      (fun time => quittingStationaryContinueMass (anchor.roots time))
      outer.block.start (outer.block.length + inner.block.length) =
    Math.survivalProduct
      (fun time => quittingStationaryContinueMass (anchor.roots time))
      outer.block.start outer.block.length *
      Math.survivalProduct
        (fun time => quittingStationaryContinueMass (anchor.roots time))
        inner.block.start inner.block.length
  rw [Math.survivalProduct_add]
  rw [hadjacent]

theorem chi_concat [Nonempty ι]
    {anchor : QuittingCalibratedTerminalAnchor reward}
    (outer inner : RealizedMarkedAbsorptionCylinder reward anchor)
    (hadjacent : inner.block.start =
      outer.block.start + outer.block.length) (who : ι) :
    (outer.concat inner hadjacent).chi who =
      outer.chi who * inner.chi who := by
  rw [(outer.concat inner hadjacent).chi_pin, outer.chi_pin, inner.chi_pin]
  rw [show (outer.concat inner hadjacent).block.start = outer.block.start by
    rfl, length_concat outer inner hadjacent]
  rw [quittingOpponentSurvivalWeight_add]
  rw [hadjacent]

end RealizedMarkedAbsorptionCylinder

end GameTheory
