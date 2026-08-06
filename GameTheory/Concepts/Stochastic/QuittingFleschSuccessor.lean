/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/

import GameTheory.Concepts.Stochastic.QuittingSingletonStationaryRoot

/-!
# The Flesch successor graph for quitting games

For an owner `i`, a different player `j` can be the next active singleton
quitter on a sequentially perfect Flesch absorption path only when the two
cross-payoff comparisons have opposite signs relative to the players' own
singleton payoffs:

* player `i` strictly loses when `j` quits rather than `i`;
* player `j` strictly gains when `i` quits rather than `j`.

This is the normalization-independent form of the graph in
Ashkenazi-Golan--Krasikov--Rainer--Solan.  When every own-singleton payoff is
normalized to zero it becomes

`r_i({j}) < 0 < r_j({i})`

with the repository convention that
`quittingSoloReward reward quitter recipient = r_recipient({quitter})`.

The strict cross-sign rule is asymmetric, so the graph has neither loops nor
directed two-cycles.  The final theorem extracts an edge from two consecutive
positive singleton arcs under the paper's singleton genericity condition.
-/

noncomputable section

namespace GameTheory

open StochasticGame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Playerwise baseline given by quitting alone. -/
def quittingSoloBaseline
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Payoff ι :=
  fun who ↦ quittingSoloReward reward who who

@[simp] theorem quittingSoloBaseline_apply
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingSoloBaseline reward who = quittingSoloReward reward who who :=
  rfl

/-- The paper's convenient normalization: each player receives zero when
quitting alone. -/
def IsQuittingSoloNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ who, quittingSoloReward reward who who = 0

/-- Baseline-invariant version of genericity of the singleton-payoff matrix.
An off-diagonal singleton outcome never gives a recipient exactly that
recipient's own-singleton payoff. -/
def IsQuittingSoloGeneric
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) : Prop :=
  ∀ quitter recipient,
    quittingSoloReward reward quitter recipient =
        quittingSoloReward reward recipient recipient ↔
      quitter = recipient

/-- Normalized effect on `receiver` when `quitter` quits alone. -/
def quittingNormalizedSingletonEffect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (receiver quitter : ι) : ℝ :=
  quittingSoloReward reward quitter receiver -
    quittingSoloReward reward receiver receiver

@[simp] theorem quittingNormalizedSingletonEffect_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι) (who : ι) :
    quittingNormalizedSingletonEffect reward who who = 0 := by
  simp [quittingNormalizedSingletonEffect]

/-- Under the zero-diagonal normalization, baseline-invariant genericity is
exactly the paper's statement that a singleton matrix entry is zero iff it is
on the diagonal. -/
theorem isQuittingSoloGeneric_iff_of_soloNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnormalized : IsQuittingSoloNormalized reward) :
    IsQuittingSoloGeneric reward ↔
      ∀ quitter recipient,
        quittingSoloReward reward quitter recipient = 0 ↔
          quitter = recipient := by
  constructor
  · intro hgeneric quitter recipient
    simpa [hnormalized recipient] using hgeneric quitter recipient
  · intro hgeneric quitter recipient
    simpa [hnormalized recipient] using hgeneric quitter recipient

/-- Genericity makes every off-diagonal normalized singleton effect nonzero. -/
theorem quittingNormalizedSingletonEffect_ne_zero_of_generic
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hgeneric : IsQuittingSoloGeneric reward)
    {receiver quitter : ι} (hne : receiver ≠ quitter) :
    quittingNormalizedSingletonEffect reward receiver quitter ≠ 0 := by
  intro hzero
  have heq : quittingSoloReward reward quitter receiver =
      quittingSoloReward reward receiver receiver := by
    exact sub_eq_zero.mp hzero
  exact hne ((hgeneric quitter receiver).mp heq).symm

/-- `successor` may follow `owner` on the continuous singleton-flow stratum.
The first inequality is the loss to `owner` when `successor` quits; the second
is the gain to `successor` when `owner` quits. -/
def QuittingFleschSuccessor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner successor : ι) : Prop :=
  quittingSoloReward reward successor owner <
      quittingSoloReward reward owner owner ∧
    quittingSoloReward reward successor successor <
      quittingSoloReward reward owner successor

/-- Equivalent normalized-effect form of the successor rule. -/
theorem quittingFleschSuccessor_iff_normalizedEffect
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner successor : ι) :
    QuittingFleschSuccessor reward owner successor ↔
      quittingNormalizedSingletonEffect reward owner successor < 0 ∧
        0 < quittingNormalizedSingletonEffect reward successor owner := by
  unfold QuittingFleschSuccessor quittingNormalizedSingletonEffect
  constructor <;> rintro ⟨hfirst, hsecond⟩ <;>
    constructor <;> linarith

/-- Zero-diagonal form of the exact cross-sign test. -/
theorem quittingFleschSuccessor_iff_of_soloNormalized
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hnormalized : IsQuittingSoloNormalized reward)
    (owner successor : ι) :
    QuittingFleschSuccessor reward owner successor ↔
      quittingSoloReward reward successor owner < 0 ∧
        0 < quittingSoloReward reward owner successor := by
  constructor
  · rintro ⟨hloss, hgain⟩
    exact ⟨by simpa [hnormalized owner] using hloss,
      by simpa [hnormalized successor] using hgain⟩
  · rintro ⟨hloss, hgain⟩
    exact ⟨by simpa [hnormalized owner] using hloss,
      by simpa [hnormalized successor] using hgain⟩

/-- The successor graph has no loops. -/
theorem not_quittingFleschSuccessor_self
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) :
    ¬ QuittingFleschSuccessor reward owner owner := by
  intro h
  exact (lt_irrefl (quittingSoloReward reward owner owner)) h.1

/-- A successor is necessarily a different player. -/
theorem ne_of_quittingFleschSuccessor
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner successor : ι}
    (h : QuittingFleschSuccessor reward owner successor) :
    owner ≠ successor := by
  intro heq
  subst successor
  exact not_quittingFleschSuccessor_self reward owner h

/-- The cross-sign rule is asymmetric. -/
theorem quittingFleschSuccessor_asymm
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner successor : ι}
    (h : QuittingFleschSuccessor reward owner successor) :
    ¬ QuittingFleschSuccessor reward successor owner := by
  intro hreverse
  exact (lt_asymm h.1 hreverse.2)

/-- Finite adjacency list of the Flesch successor graph. -/
def quittingFleschSuccessors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) : Finset ι := by
  classical
  exact Finset.univ.filter (QuittingFleschSuccessor reward owner)

@[simp] theorem mem_quittingFleschSuccessors_iff
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner successor : ι) :
    successor ∈ quittingFleschSuccessors reward owner ↔
      QuittingFleschSuccessor reward owner successor := by
  classical
  simp [quittingFleschSuccessors]

/-- The finite graph contains no self-edge. -/
theorem owner_not_mem_quittingFleschSuccessors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (owner : ι) :
    owner ∉ quittingFleschSuccessors reward owner := by
  rw [mem_quittingFleschSuccessors_iff]
  exact not_quittingFleschSuccessor_self reward owner

/-- A displayed edge rules out its reverse edge. -/
theorem reverse_not_mem_quittingFleschSuccessors
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    {owner successor : ι}
    (h : successor ∈ quittingFleschSuccessors reward owner) :
    owner ∉ quittingFleschSuccessors reward successor := by
  rw [mem_quittingFleschSuccessors_iff] at h ⊢
  exact quittingFleschSuccessor_asymm reward h

/-- **Two consecutive positive singleton arcs determine the graph edge.**

`current` is on the active face of `owner`; `next` is on the active face of
`successor`. The first arc has positive mass below one, and the second has
positive mass at most one. The two continuation-floor inequalities force the
weak cross signs; singleton genericity upgrades them to the strict Flesch
successor signs. -/
theorem quittingFleschSuccessor_of_consecutive_arcs
    (reward : {S : Finset ι // S.Nonempty} → Payoff ι)
    (hgeneric : IsQuittingSoloGeneric reward)
    {owner successor : ι} (howners : owner ≠ successor)
    {firstMass secondMass : ℝ}
    (hfirstMassPos : 0 < firstMass)
    (hfirstMassLtOne : firstMass < 1)
    (hsecondMassPos : 0 < secondMass)
    (hsecondMassLeOne : secondMass ≤ 1)
    {current next after : Payoff ι}
    (hcurrentArc :
      current = quittingSingletonArcPayoff firstMass
        (quittingSoloReward reward owner) next)
    (hnextArc :
      next = quittingSingletonArcPayoff secondMass
        (quittingSoloReward reward successor) after)
    (hcurrentFace :
      current owner = quittingSoloReward reward owner owner)
    (hnextFace :
      next successor = quittingSoloReward reward successor successor)
    (hafterFloor :
      quittingSoloReward reward owner owner ≤ after owner)
    (hcurrentFloor :
      quittingSoloReward reward successor successor ≤ current successor) :
    QuittingFleschSuccessor reward owner successor := by
  have hcurrentOwner := congrFun hcurrentArc owner
  have hnextOwner := congrFun hnextArc owner
  have hcurrentSuccessor := congrFun hcurrentArc successor
  simp only [quittingSingletonArcPayoff] at hcurrentOwner hnextOwner hcurrentSuccessor

  have hnextOwnerEq :
      next owner = quittingSoloReward reward owner owner := by
    have hfactor :
        (1 - firstMass) *
            (next owner - quittingSoloReward reward owner owner) = 0 := by
      calc
        (1 - firstMass) *
              (next owner - quittingSoloReward reward owner owner) =
            firstMass * quittingSoloReward reward owner owner +
                (1 - firstMass) * next owner -
              quittingSoloReward reward owner owner := by ring
        _ = current owner -
              quittingSoloReward reward owner owner := by
            rw [← hcurrentOwner]
        _ = 0 := sub_eq_zero.mpr hcurrentFace
    have hcontinueNe : 1 - firstMass ≠ 0 :=
      ne_of_gt (sub_pos.mpr hfirstMassLtOne)
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hfactor).resolve_left hcontinueNe)

  have hownerBalance :
      secondMass *
          quittingNormalizedSingletonEffect reward owner successor +
        (1 - secondMass) *
          (after owner - quittingSoloReward reward owner owner) = 0 := by
    calc
      (secondMass *
          quittingNormalizedSingletonEffect reward owner successor +
        (1 - secondMass) *
          (after owner - quittingSoloReward reward owner owner)) =
          secondMass * quittingSoloReward reward successor owner +
              (1 - secondMass) * after owner -
            quittingSoloReward reward owner owner := by
        unfold quittingNormalizedSingletonEffect
        ring
      _ = next owner - quittingSoloReward reward owner owner := by
        rw [← hnextOwner]
      _ = 0 := by rw [hnextOwnerEq]; ring
  have htailNonneg :
      0 ≤ (1 - secondMass) *
        (after owner - quittingSoloReward reward owner owner) :=
    mul_nonneg (sub_nonneg.mpr hsecondMassLeOne)
      (sub_nonneg.mpr hafterFloor)
  have hownerMulNonpos :
      secondMass *
        quittingNormalizedSingletonEffect reward owner successor ≤ 0 := by
    linarith [hownerBalance, htailNonneg]
  have hownerWeak :
      quittingNormalizedSingletonEffect reward owner successor ≤ 0 := by
    nlinarith [hownerMulNonpos, hsecondMassPos]
  have hownerNe :=
    quittingNormalizedSingletonEffect_ne_zero_of_generic
      reward hgeneric howners
  have hownerStrict :
      quittingNormalizedSingletonEffect reward owner successor < 0 :=
    lt_of_le_of_ne hownerWeak hownerNe

  have hsuccessorMulEq :
      firstMass *
          quittingNormalizedSingletonEffect reward successor owner =
        current successor -
          quittingSoloReward reward successor successor := by
    rw [hcurrentSuccessor, hnextFace]
    unfold quittingNormalizedSingletonEffect
    ring
  have hsuccessorMulNonneg :
      0 ≤ firstMass *
        quittingNormalizedSingletonEffect reward successor owner := by
    rw [hsuccessorMulEq]
    exact sub_nonneg.mpr hcurrentFloor
  have hsuccessorWeak :
      0 ≤ quittingNormalizedSingletonEffect reward successor owner := by
    nlinarith [hsuccessorMulNonneg, hfirstMassPos]
  have hsuccessorNe :=
    quittingNormalizedSingletonEffect_ne_zero_of_generic
      reward hgeneric howners.symm
  have hsuccessorStrict :
      0 < quittingNormalizedSingletonEffect reward successor owner :=
    lt_of_le_of_ne hsuccessorWeak hsuccessorNe.symm

  exact (quittingFleschSuccessor_iff_normalizedEffect
    reward owner successor).2 ⟨hownerStrict, hsuccessorStrict⟩

end GameTheory
