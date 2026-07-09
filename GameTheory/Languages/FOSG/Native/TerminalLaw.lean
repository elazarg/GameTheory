/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Languages.Bridges.FOSG.ObsModelCore
import GameTheory.Languages.FOSG.Compile
import GameTheory.Languages.FOSG.Execution
import GameTheory.Concepts.Foundations.DeviationSimulation
import GameTheory.Languages.Kuhn.BehavioralToMixedCore
import GameTheory.Languages.Kuhn.MixedToBehavioralCore
import GameTheory.Languages.FOSG.Native.HistoryMarginal

namespace GameTheory

namespace FOSG

namespace Kuhn

open ObsModelCoreBridge

attribute [local instance] Fintype.ofFinite

open scoped BigOperators

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
variable (G : FOSG ι W Act PrivObs PubObs)


section TerminalCorollaries

variable [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)]
variable [DecidablePred G.terminal]

noncomputable local instance pureStrategyFintypeTerminal
    (i : ι) : Fintype (PureStrategy (G := G) i) := by
  classical
  dsimp [PureStrategy]
  infer_instance

noncomputable local instance pureProfileFintypeTerminal
    : Fintype (_root_.GameTheory.FOSG.PureProfile G) := by
  classical
  dsimp [_root_.GameTheory.FOSG.PureProfile, PureStrategy]
  infer_instance

/-- Native FOSG behavioral-to-mixed equality for terminal-history mass. -/
theorem marginal_terminalWeight
    (β : BehavioralProfile (G := G)) (h : G.History) :
    ∑ π, behavioralToMixedJoint (G := G) β π *
      History.terminalWeight (G := G) (G.pureToBehavioral π) h =
        History.terminalWeight (G := G) β h := by
  by_cases hterm : G.terminal h.lastState
  · have hsum :
        (∑ π, behavioralToMixedJoint (G := G) β π *
          History.terminalWeight (G := G) (G.pureToBehavioral π) h) =
          ∑ π, behavioralToMixedJoint (G := G) β π *
            History.prob (G.pureToBehavioral π) h := by
              refine Finset.sum_congr rfl ?_
              intro π _
              rw [History.terminalWeight_of_terminal (G := G)
                (σ := G.pureToBehavioral π) hterm]
    rw [History.terminalWeight_of_terminal (G := G) β hterm, hsum, marginal_prob]
  · rw [History.terminalWeight_of_not_terminal (G := G) β hterm]
    have hsum :
        (∑ π, behavioralToMixedJoint (G := G) β π *
          History.terminalWeight (G := G) (G.pureToBehavioral π) h) =
          ∑ π, behavioralToMixedJoint (G := G) β π * 0 := by
              refine Finset.sum_congr rfl ?_
              intro π _
              rw [History.terminalWeight_of_not_terminal (G := G)
                (σ := G.pureToBehavioral π) hterm]
    rw [hsum]
    simp

/-- Native FOSG distribution preservation on any finite event of terminal
histories. The induced product mixed strategy assigns the same total
terminal-history mass to every finite set of histories as the behavioral
profile. -/
theorem marginal_terminalMassOn
    (β : BehavioralProfile (G := G)) (hs : Finset G.History) :
    (∑ π, behavioralToMixedJoint (G := G) β π *
      History.terminalMassOn (G := G) (G.pureToBehavioral π) hs) =
      History.terminalMassOn (G := G) β hs := by
  calc
    ∑ π, behavioralToMixedJoint (G := G) β π *
        History.terminalMassOn (G := G) (G.pureToBehavioral π) hs
      = ∑ π, Finset.sum hs (fun h =>
          behavioralToMixedJoint (G := G) β π *
            History.terminalWeight (G := G) (G.pureToBehavioral π) h) := by
              refine Finset.sum_congr rfl ?_
              intro π _
              rw [History.terminalMassOn, Finset.mul_sum]
    _ = Finset.sum hs (fun h => ∑ π,
          behavioralToMixedJoint (G := G) β π *
            History.terminalWeight (G := G) (G.pureToBehavioral π) h) := by
              rw [Finset.sum_comm]
    _ = History.terminalMassOn (G := G) β hs := by
          rw [History.terminalMassOn]
          refine Finset.sum_congr rfl ?_
          intro h hh
          exact marginal_terminalWeight (G := G) β h

/-- Native FOSG terminal-law preservation on finite events. This packages the
behavioral-to-mixed terminal distribution equality as equality of the native
terminal-history event-mass functional. -/
theorem marginal_terminalLaw
    (β : BehavioralProfile (G := G)) :
    (fun hs =>
      ∑ π, behavioralToMixedJoint (G := G) β π *
        History.terminalLaw (G := G) (G.pureToBehavioral π) hs) =
      History.terminalLaw (G := G) β := by
  funext hs
  simpa [History.terminalLaw] using marginal_terminalMassOn (G := G) β hs

/-- Pointwise real-valued terminal-mass preservation. This is the `toReal`
version of `marginal_terminalWeight`, suitable for expected-utility
calculations. -/
theorem marginal_terminalWeight_toReal
    (β : BehavioralProfile (G := G)) (h : G.History) :
    ∑ π, (behavioralToMixedJoint (G := G) β π).toReal *
      (History.terminalWeight (G := G) (G.pureToBehavioral π) h).toReal =
      (History.terminalWeight (G := G) β h).toReal := by
  calc
    ∑ π, (behavioralToMixedJoint (G := G) β π).toReal *
        (History.terminalWeight (G := G) (G.pureToBehavioral π) h).toReal
      = ∑ π,
          (behavioralToMixedJoint (G := G) β π *
            History.terminalWeight (G := G) (G.pureToBehavioral π) h).toReal := by
              refine Finset.sum_congr rfl ?_
              intro π _
              rw [ENNReal.toReal_mul]
    _ = (∑ π,
          behavioralToMixedJoint (G := G) β π *
            History.terminalWeight (G := G) (G.pureToBehavioral π) h).toReal := by
          symm
          apply ENNReal.toReal_sum
          intro π _
          exact ENNReal.mul_ne_top
            (PMF.apply_ne_top (behavioralToMixedJoint (G := G) β) π)
            (History.terminalWeight_ne_top (G := G) (σ := G.pureToBehavioral π) h)
    _ = (History.terminalWeight (G := G) β h).toReal := by
          rw [marginal_terminalWeight (G := G) β h]

/-- `terminalWeight` specialized to the classical decidability instance, used
internally to keep private utility lemmas free of hidden section-instance
arguments. -/
noncomputable def terminalWeightClassical
    [Fintype G.History]
    (σ : BehavioralProfile (G := G)) (h : G.History) : ENNReal :=
  @History.terminalWeight ι W _ Act PrivObs PubObs _ G (Classical.decPred G.terminal) σ h

omit [DecidablePred G.terminal] in
/-- Native FOSG preservation of the terminal-history utility sum under the
product mixed strategy induced by a behavioral profile. -/
theorem marginal_terminalUtilitySum
    [Fintype G.History]
    (β : BehavioralProfile (G := G)) (i : ι) :
    ∑ π, (behavioralToMixedJoint (G := G) β π).toReal *
      (∑ h : G.History,
        (terminalWeightClassical (G := G) (G.pureToBehavioral π) h).toReal *
          History.utility h i) =
      ∑ h : G.History,
        (terminalWeightClassical (G := G) β h).toReal * History.utility h i := by
  classical
  letI : DecidablePred G.terminal := Classical.decPred G.terminal
  calc
    ∑ π, (behavioralToMixedJoint (G := G) β π).toReal *
        ∑ h : G.History,
          (terminalWeightClassical (G := G) (G.pureToBehavioral π) h).toReal *
            History.utility h i
      = ∑ π, ∑ h : G.History,
          ((behavioralToMixedJoint (G := G) β π).toReal *
            (terminalWeightClassical (G := G) (G.pureToBehavioral π) h).toReal) *
              History.utility h i := by
                refine Finset.sum_congr rfl ?_
                intro π _
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro h _
                simp [mul_assoc]
    _ = ∑ h : G.History, ∑ π,
          ((behavioralToMixedJoint (G := G) β π).toReal *
            (terminalWeightClassical (G := G) (G.pureToBehavioral π) h).toReal) *
              History.utility h i := by
                rw [Finset.sum_comm]
    _ = ∑ h : G.History,
          (∑ π, (behavioralToMixedJoint (G := G) β π).toReal *
            (terminalWeightClassical (G := G) (G.pureToBehavioral π) h).toReal) *
              History.utility h i := by
                refine Finset.sum_congr rfl ?_
                intro h _
                rw [← Finset.sum_mul]
    _ = ∑ h : G.History,
          (terminalWeightClassical (G := G) β h).toReal * History.utility h i := by
                refine Finset.sum_congr rfl ?_
                intro h _
                simpa [terminalWeightClassical] using
                  congrArg (fun x => x * History.utility h i)
                    (marginal_terminalWeight_toReal (G := G) β h)

omit [DecidablePred G.terminal] in
/-- **Native Kuhn theorem for FOSGs at realized histories.**

Sampling a pure profile ex ante from the independent product mixed strategy
induced by a behavioral profile preserves the weight of every realized FOSG
history. -/
theorem behavioral_to_mixed_prob
    (β : BehavioralProfile (G := G)) (h : G.History) :
    ∑ π, behavioralToMixedJoint (G := G) β π *
      History.prob (G.pureToBehavioral π) h =
        History.prob β h :=
  marginal_prob (G := G) β h

/-- **Native Kuhn theorem for FOSGs at terminal histories.**

The product mixed strategy induced by a behavioral profile preserves the
terminal weight of every realized terminal history. -/
theorem behavioral_to_mixed_terminalWeight
    (β : BehavioralProfile (G := G)) (h : G.History) :
    ∑ π, behavioralToMixedJoint (G := G) β π *
      History.terminalWeight (G := G) (G.pureToBehavioral π) h =
        History.terminalWeight (G := G) β h :=
  marginal_terminalWeight (G := G) β h

/-- **Native Kuhn theorem for finite terminal events in a FOSG.**

The product mixed strategy induced by a behavioral profile assigns the same
total terminal mass to every finite set of realized histories. -/
theorem behavioral_to_mixed_terminalMassOn
    (β : BehavioralProfile (G := G)) (hs : Finset G.History) :
    (∑ π, behavioralToMixedJoint (G := G) β π *
      History.terminalMassOn (G := G) (G.pureToBehavioral π) hs) =
      History.terminalMassOn (G := G) β hs :=
  marginal_terminalMassOn (G := G) β hs

/-- **Native Kuhn theorem for the terminal law of a FOSG.**

The product mixed strategy induced by a behavioral profile preserves the native
terminal-history law exactly. -/
theorem behavioral_to_mixed_terminalLaw
    (β : BehavioralProfile (G := G)) :
    (fun hs =>
      ∑ π, behavioralToMixedJoint (G := G) β π *
        History.terminalLaw (G := G) (G.pureToBehavioral π) hs) =
      History.terminalLaw (G := G) β :=
  marginal_terminalLaw (G := G) β

/-- **Native Kuhn theorem for FOSG expected utility.**

The product mixed strategy induced by a legal behavioral profile preserves
expected utility for every player in the induced `KernelGame`. -/
theorem behavioral_to_mixed_eu
    [Fintype G.History]
    (hNorm : G.HasNormalizedTerminalLaw)
    (β : G.LegalBehavioralProfile) (i : ι) :
    ∑ π, (behavioralToMixedJoint (G := G) β.toProfile π).toReal *
      (∑ h : G.History,
        (History.terminalWeight (G := G) (G.pureToBehavioral π) h).toReal *
          History.utility h i) =
      (G.toKernelGame hNorm).eu β i := by
  have hEqWeight :
      ∀ (σ : BehavioralProfile (G := G)) (h : G.History),
        terminalWeightClassical (G := G) σ h = History.terminalWeight (G := G) σ h := by
    intro σ h
    classical
    unfold terminalWeightClassical History.terminalWeight
    by_cases hterm : G.terminal h.lastState <;> simp [hterm]
  rw [G.toKernelGame_eu_eq hNorm β i]
  have hMain := marginal_terminalUtilitySum (G := G) β.toProfile i
  simpa [hEqWeight] using hMain

end TerminalCorollaries

end Kuhn

end FOSG

end GameTheory
