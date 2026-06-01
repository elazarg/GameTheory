/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Languages.Bridges.FOSG.ObsModelCore
import GameTheory.Languages.FOSG.Compile
import GameTheory.Languages.FOSG.Execution
import GameTheory.Concepts.Foundations.DeviationSimulation
import GameTheory.Theorems.Kuhn.BehavioralToMixedCore
import GameTheory.Theorems.Kuhn.MixedToBehavioralCore
import GameTheory.Languages.FOSG.Kuhn.StepIndependence

namespace GameTheory

namespace FOSG

namespace Kuhn

open ObsModelCoreBridge

attribute [local instance] Fintype.ofFinite

open scoped BigOperators

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
variable (G : FOSG ι W Act PrivObs PubObs)


section HistoryMarginal

variable [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)]

noncomputable local instance pureStrategyFintypeHistory
    (i : ι) : Fintype (PureStrategy (G := G) i) := by
  classical
  dsimp [PureStrategy]
  infer_instance

noncomputable local instance pureProfileFintypeHistory
    : Fintype (_root_.GameTheory.FOSG.PureProfile G) := by
  classical
  dsimp [_root_.GameTheory.FOSG.PureProfile, PureStrategy]
  infer_instance

/-- Information-state coordinates that already appeared on a proper prefix of
`h`. -/
def SeenBefore
    (h : G.History) (i : ι) (v : G.InfoState i) : Prop :=
  ∃ h' : G.History, h'.IsPrefix h ∧ h' ≠ h ∧ h'.playerView i = v

omit [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
theorem stepChainFrom_prefix
    {w : W} {es : List G.Step} {e : G.Step}
    (hchain : G.StepChainFrom w (es ++ [e])) :
    G.StepChainFrom w es := by
  induction es generalizing w with
  | nil =>
      trivial
  | cons e₀ es ih =>
      rcases hchain with ⟨hsrc, htail⟩
      exact And.intro hsrc (ih htail)

omit [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
theorem stepChainFrom_last_src
    {w : W} {es : List G.Step} {e : G.Step}
    (hchain : G.StepChainFrom w (es ++ [e])) :
    e.src = G.lastStateFrom w es := by
  induction es generalizing w with
  | nil =>
      simpa [StepChainFrom, lastStateFrom] using hchain.1
  | cons e₀ es ih =>
      rcases hchain with ⟨hsrc, htail⟩
      simpa [lastStateFrom] using ih htail

omit [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
theorem seenBefore_mono_appendStep
    {h : G.History} {e : G.Step} {hsrc : e.src = h.lastState}
    {i : ι} {v : G.InfoState i}
    (hSeen : SeenBefore (G := G) h i v) :
    SeenBefore (G := G) (h.appendStep e hsrc) i v := by
  rcases hSeen with ⟨h', hpref, hne, hv⟩
  refine ⟨h', History.prefix_trans hpref ?_, ?_, hv⟩
  · exact ⟨[e], by simp [History.appendStep]⟩
  · intro hEq
    have hpref' : (h.appendStep e hsrc).IsPrefix h := by
      simpa [hEq] using hpref
    rcases hpref' with ⟨s, hs⟩
    have hlen := congrArg List.length hs
    simp [History.appendStep] at hlen

omit [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
theorem seenBefore_current_appendStep
    (h : G.History) (e : G.Step) (hsrc : e.src = h.lastState) (i : ι) :
    SeenBefore (G := G) (h.appendStep e hsrc) i (h.playerView i) := by
  refine ⟨h, ?_, ?_, rfl⟩
  · exact ⟨[e], by simp [History.appendStep]⟩
  · intro hEq
    have hlen := congrArg (fun h' : G.History => h'.steps.length) hEq
    simp [History.appendStep] at hlen

omit [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
theorem not_seenBefore_current
    (h : G.History) (i : ι) :
    ¬ SeenBefore (G := G) h i (h.playerView i) := by
  intro hSeen
  rcases hSeen with ⟨h', hpref, hne, hv⟩
  exact History.playerView_ne_of_properPrefix (G := G) i hpref hne hv

omit [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
theorem stepProb_pure_congr_at_history
    {π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G}
    (h : G.History) (e : G.Step)
    (hag : ∀ i, π₁ i (h.playerView i) = π₂ i (h.playerView i)) :
    G.stepProb (G.pureToBehavioral π₁) h e =
      G.stepProb (G.pureToBehavioral π₂) h e := by
  classical
  rw [G.stepProb_eq_stepActionProb_mul_transition,
    G.stepProb_eq_stepActionProb_mul_transition]
  congr 1
  unfold FOSG.stepActionProb
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [FOSG.pureToBehavioral_apply, FOSG.pureToBehavioral_apply]
  simp [PMF.pure_apply, hag i]

omit [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
/-- Pure-history weight depends only on the information-state coordinates that
appear on proper prefixes of the history. -/
theorem prob_pure_congr_of_agreeOnSeenBefore
    {π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G}
    (h : G.History)
    (hag : ∀ i (v : G.InfoState i), SeenBefore (G := G) h i v → π₁ i v = π₂ i v) :
    History.prob (G.pureToBehavioral π₁) h =
      History.prob (G.pureToBehavioral π₂) h := by
  classical
  let H :
      ∀ (es : List G.Step) (hchain : G.StepChainFrom G.init es),
        (∀ i (v : G.InfoState i),
          SeenBefore (G := G) ({ steps := es, chain := hchain } : G.History) i v →
            π₁ i v = π₂ i v) →
          History.prob (G.pureToBehavioral π₁)
              ({ steps := es, chain := hchain } : G.History) =
            History.prob (G.pureToBehavioral π₂)
              ({ steps := es, chain := hchain } : G.History) := by
    intro es
    induction es using List.reverseRecOn with
    | nil =>
        intro hchain hag'
        simp [History.prob]
    | append_singleton es e ih =>
        intro hchain hag'
        let prefChain : G.StepChainFrom G.init es :=
          stepChainFrom_prefix (G := G) hchain
        let pref : G.History := ⟨es, prefChain⟩
        have hsrc : e.src = pref.lastState := by
          simpa [pref, History.lastState] using stepChainFrom_last_src (G := G) hchain
        have hh :
            ({ steps := es ++ [e], chain := hchain } : G.History) = pref.appendStep e hsrc := by
          apply History.ext
          simp [pref, History.appendStep]
        rw [hh] at hag' ⊢
        have hPref :
            History.prob (G.pureToBehavioral π₁) pref =
              History.prob (G.pureToBehavioral π₂) pref := by
          apply ih prefChain
          intro i v hSeen
          exact hag' i v (seenBefore_mono_appendStep (G := G) hSeen)
        have hStep :
            G.stepProb (G.pureToBehavioral π₁) pref e =
            G.stepProb (G.pureToBehavioral π₂) pref e := by
          apply stepProb_pure_congr_at_history (G := G) pref e
          intro i
          exact hag' i _ (seenBefore_current_appendStep (G := G) pref e hsrc i)
        rw [History.prob_appendStep, History.prob_appendStep, hPref, hStep]
  exact H h.steps h.chain hag

/-- Native FOSG behavioral-to-mixed equality for realized-history weights. -/
theorem marginal_prob
    (β : BehavioralProfile (G := G)) (h : G.History) :
    ∑ π, behavioralToMixedJoint (G := G) β π *
      History.prob (G.pureToBehavioral π) h =
        History.prob β h := by
  classical
  let H :
      ∀ (es : List G.Step) (hchain : G.StepChainFrom G.init es),
        ∑ π, behavioralToMixedJoint (G := G) β π *
          History.prob (G.pureToBehavioral π) ({ steps := es, chain := hchain } : G.History) =
            History.prob β ({ steps := es, chain := hchain } : G.History) := by
    intro es
    induction es using List.reverseRecOn with
    | nil =>
        intro hchain
        simp [History.prob]
        have := PMF.tsum_coe (behavioralToMixedJoint (G := G) β)
        rwa [tsum_fintype] at this
    | append_singleton es e ih =>
        intro hchain
        let prefChain : G.StepChainFrom G.init es :=
          stepChainFrom_prefix (G := G) hchain
        let pref : G.History := ⟨es, prefChain⟩
        have hsrc : e.src = pref.lastState := by
          simpa [pref, History.lastState] using stepChainFrom_last_src (G := G) hchain
        have hh :
            ({ steps := es ++ [e], chain := hchain } : G.History) = pref.appendStep e hsrc := by
          apply History.ext
          simp [pref, History.appendStep]
        rw [hh]
        calc
          ∑ π, behavioralToMixedJoint (G := G) β π *
              History.prob (G.pureToBehavioral π) (pref.appendStep e hsrc)
            = ∑ π, behavioralToMixedJoint (G := G) β π *
                (History.prob (G.pureToBehavioral π) pref *
                  G.stepProb (G.pureToBehavioral π) pref e) := by
                    refine Finset.sum_congr rfl ?_
                    intro π _
                    rw [History.prob_appendStep]
          _ = (∑ π, behavioralToMixedJoint (G := G) β π *
                History.prob (G.pureToBehavioral π) pref) *
                G.stepProb β pref e := by
                  exact scalar_indep_stepProb (G := G)
                    (P := SeenBefore (G := G) pref) β
                    (fun π => History.prob (G.pureToBehavioral π) pref)
                    pref e
                    (fun π₁ π₂ hag =>
                      prob_pure_congr_of_agreeOnSeenBefore (G := G) pref hag)
                    (fun i => not_seenBefore_current (G := G) pref i)
          _ = History.prob β pref * G.stepProb β pref e := by
                rw [ih prefChain]
          _ = History.prob β (pref.appendStep e hsrc) := by
                rw [History.prob_appendStep]
  exact H h.steps h.chain

end HistoryMarginal

end Kuhn

end FOSG

end GameTheory
