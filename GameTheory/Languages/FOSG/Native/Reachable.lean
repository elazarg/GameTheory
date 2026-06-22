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
import GameTheory.Languages.FOSG.Native.TerminalLaw

namespace GameTheory

namespace FOSG

namespace Kuhn

open ObsModelCoreBridge

attribute [local instance] Fintype.ofFinite

open scoped BigOperators

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
variable (G : FOSG ι W Act PrivObs PubObs)



section ReachableNative

variable [Fintype ι] [Fintype G.History] [∀ i, Fintype (Act i)]

/-- Native reachable pure-strategy type. -/
abbrev ReachablePureStrategy (i : ι) : Type :=
  _root_.GameTheory.FOSG.ReachablePureStrategy G i

/-- Native reachable behavioral-profile type. -/
abbrev ReachableBehavioralProfile : Type :=
  _root_.GameTheory.FOSG.ReachableBehavioralProfile G

noncomputable local instance reachablePureStrategyFintype
    (i : ι) : Fintype (ReachablePureStrategy (G := G) i) := by
  classical
  dsimp [ReachablePureStrategy, _root_.GameTheory.FOSG.ReachablePureStrategy]
  infer_instance

noncomputable local instance reachablePureProfileFintype
    : Fintype (_root_.GameTheory.FOSG.ReachablePureProfile G) := by
  classical
  dsimp [_root_.GameTheory.FOSG.ReachablePureProfile, ReachablePureStrategy,
    _root_.GameTheory.FOSG.ReachablePureStrategy]
  infer_instance

/-- Native product mixed strategy induced by independently sampling a pure
strategy at each reachable information state for each player. -/
noncomputable def reachableBehavioralToMixed
    (β : ReachableBehavioralProfile (G := G)) :
    ∀ i, PMF (ReachablePureStrategy (G := G) i) := by
  classical
  intro i
  exact Math.PMFProduct.pmfPi (β i)

/-- Native joint mixed strategy over reachable pure profiles. -/
noncomputable def reachableBehavioralToMixedJoint
    (β : ReachableBehavioralProfile (G := G)) :
    PMF (_root_.GameTheory.FOSG.ReachablePureProfile G) := by
  classical
  exact Math.PMFProduct.pmfPi (reachableBehavioralToMixed (G := G) β)

open Classical in
omit [Fintype G.History] [∀ i, Fintype (Act i)] in
theorem reachable_stepActionProb_pureToBehavioral
    (π : _root_.GameTheory.FOSG.ReachablePureProfile G) (pref : G.History) (e : G.Step) :
    G.stepActionProb (G.pureToBehavioral π.extend) pref e =
      ∏ i, if π i (G.reachableInfoStateOfHistory i pref) = e.ownAction? i then 1 else 0 := by
  classical
  unfold FOSG.stepActionProb
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [FOSG.pureToBehavioral_apply]
  simp [_root_.GameTheory.FOSG.ReachablePureProfile.extend, eq_comm]

open Classical in
theorem reachable_marginal_stepActionProb
    (β : ReachableBehavioralProfile (G := G)) (pref : G.History) (e : G.Step) :
    ∑ π : _root_.GameTheory.FOSG.ReachablePureProfile G,
      reachableBehavioralToMixedJoint (G := G) β π *
        G.stepActionProb (G.pureToBehavioral π.extend) pref e =
      G.stepActionProb β.extend pref e := by
  classical
  rw [show (∑ π : _root_.GameTheory.FOSG.ReachablePureProfile G,
        reachableBehavioralToMixedJoint (G := G) β π *
          G.stepActionProb (G.pureToBehavioral π.extend) pref e) =
      ∑ ρ : ((i : ι) → ReachablePureStrategy (G := G) i),
        (Math.PMFProduct.pmfPi (reachableBehavioralToMixed (G := G) β)) ρ *
          (∏ i, if ρ i (G.reachableInfoStateOfHistory i pref) = e.ownAction? i then 1 else 0) by
      refine Finset.sum_congr rfl ?_
      intro ρ _
      rw [reachable_stepActionProb_pureToBehavioral (G := G) ρ pref e]
      rfl]
  have hprod :
      (∑ ρ : ((i : ι) → ReachablePureStrategy (G := G) i),
        (Math.PMFProduct.pmfPi (reachableBehavioralToMixed (G := G) β)) ρ *
          (∏ i, if ρ i (G.reachableInfoStateOfHistory i pref) = e.ownAction? i then 1 else 0)) =
      ∑ ρ : ((i : ι) → ReachablePureStrategy (G := G) i),
        ∏ i,
          (reachableBehavioralToMixed (G := G) β i) (ρ i) *
            (if ρ i (G.reachableInfoStateOfHistory i pref) = e.ownAction? i then 1 else 0) := by
    refine Finset.sum_congr rfl ?_
    intro ρ _
    rw [Math.PMFProduct.pmfPi_apply, ← Finset.prod_mul_distrib]
  rw [hprod]
  rw [show (∑ ρ : ((i : ι) → ReachablePureStrategy (G := G) i),
        ∏ i,
          (reachableBehavioralToMixed (G := G) β i) (ρ i) *
            (if ρ i (G.reachableInfoStateOfHistory i pref) = e.ownAction? i then 1 else 0)) =
      ∏ i, ∑ πi : ReachablePureStrategy (G := G) i,
        (reachableBehavioralToMixed (G := G) β i) πi *
          (if πi (G.reachableInfoStateOfHistory i pref) = e.ownAction? i then 1 else 0) by
      exact
        (show (∏ i, ∑ πi : ReachablePureStrategy (G := G) i,
            (reachableBehavioralToMixed (G := G) β i) πi *
              (if πi (G.reachableInfoStateOfHistory i pref) = e.ownAction? i then 1 else 0)) =
            ∑ ρ : ((i : ι) → ReachablePureStrategy (G := G) i),
              ∏ i,
                (reachableBehavioralToMixed (G := G) β i) (ρ i) *
                  (if ρ i (G.reachableInfoStateOfHistory i pref) = e.ownAction? i
                    then 1 else 0) from
          (@Fintype.prod_sum ι ENNReal _ _ _ (fun i => ReachablePureStrategy (G := G) i) _
          (fun i πi =>
            (reachableBehavioralToMixed (G := G) β i) πi *
              (if πi (G.reachableInfoStateOfHistory i pref) = e.ownAction? i then 1 else 0)))).symm]
  unfold FOSG.stepActionProb
  refine Finset.prod_congr rfl ?_
  intro i _
  have hcoord :
      ∑ πi : ReachablePureStrategy (G := G) i,
        (reachableBehavioralToMixed (G := G) β i) πi *
          (if πi (G.reachableInfoStateOfHistory i pref) = e.ownAction? i then 1 else 0) =
            β i (G.reachableInfoStateOfHistory i pref) (e.ownAction? i) := by
    change (∑ πi : G.ReachableInfoState i → Option (Act i),
        (Math.PMFProduct.pmfPi (β i)) πi *
          (if πi (G.reachableInfoStateOfHistory i pref) = e.ownAction? i then 1 else 0)) =
      β i (G.reachableInfoStateOfHistory i pref) (e.ownAction? i)
    exact Math.PMFProduct.pmfPi_coord_mass_mul_indicator (β i)
      (G.reachableInfoStateOfHistory i pref) (e.ownAction? i)
  simpa [_root_.GameTheory.FOSG.ReachableBehavioralProfile.extend] using hcoord

theorem reachable_marginal_stepProb
    (β : ReachableBehavioralProfile (G := G)) (pref : G.History) (e : G.Step) :
    ∑ π : _root_.GameTheory.FOSG.ReachablePureProfile G,
      reachableBehavioralToMixedJoint (G := G) β π *
        G.stepProb (G.pureToBehavioral π.extend) pref e =
      G.stepProb β.extend pref e := by
  let p : ENNReal := (G.transition e.src e.act) e.dst
  calc
    ∑ π : _root_.GameTheory.FOSG.ReachablePureProfile G,
        reachableBehavioralToMixedJoint (G := G) β π *
          G.stepProb (G.pureToBehavioral π.extend) pref e
      = ∑ π : _root_.GameTheory.FOSG.ReachablePureProfile G,
          (reachableBehavioralToMixedJoint (G := G) β π *
            G.stepActionProb (G.pureToBehavioral π.extend) pref e) * p := by
              simp [p, mul_assoc]
    _ = (∑ π : _root_.GameTheory.FOSG.ReachablePureProfile G,
          reachableBehavioralToMixedJoint (G := G) β π *
            G.stepActionProb (G.pureToBehavioral π.extend) pref e) * p := by
              rw [Finset.sum_mul]
    _ = G.stepActionProb β.extend pref e * p := by
          rw [reachable_marginal_stepActionProb (G := G) β pref e]
    _ = G.stepProb β.extend pref e := by
          simp [p]

noncomputable def swapReachableProfileBy
    (P : ∀ i, G.ReachableInfoState i → Prop)
    (π₁ π₂ : _root_.GameTheory.FOSG.ReachablePureProfile G) :
    _root_.GameTheory.FOSG.ReachablePureProfile G := by
  classical
  exact fun i v => if P i v then π₁ i v else π₂ i v

omit [Fintype ι] [Fintype G.History] [∀ i, Fintype (Act i)] in
theorem swapReachableProfileBy_involutive
    (P : ∀ i, G.ReachableInfoState i → Prop) :
    Function.Involutive
      (fun (p : _root_.GameTheory.FOSG.ReachablePureProfile G ×
          _root_.GameTheory.FOSG.ReachablePureProfile G) =>
        (swapReachableProfileBy (G := G) P p.1 p.2,
          swapReachableProfileBy (G := G) P p.2 p.1)) := by
  classical
  intro ⟨π₁, π₂⟩
  apply Prod.ext
  · funext i v
    by_cases hv : P i v <;> simp [swapReachableProfileBy, hv]
  · funext i v
    by_cases hv : P i v <;> simp [swapReachableProfileBy, hv]

omit [∀ i, Fintype (Act i)] in
theorem swapReachableBy_weight_eq
    (P : ∀ i, G.ReachableInfoState i → Prop)
    (β : ReachableBehavioralProfile (G := G))
    (π₁ π₂ : _root_.GameTheory.FOSG.ReachablePureProfile G) :
    reachableBehavioralToMixedJoint (G := G) β (swapReachableProfileBy (G := G) P π₁ π₂) *
      reachableBehavioralToMixedJoint (G := G) β (swapReachableProfileBy (G := G) P π₂ π₁) =
    reachableBehavioralToMixedJoint (G := G) β π₁ *
      reachableBehavioralToMixedJoint (G := G) β π₂ := by
  simp only [reachableBehavioralToMixedJoint, reachableBehavioralToMixed,
    Math.PMFProduct.pmfPi_apply]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  funext i
  simp only [swapReachableProfileBy]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  funext v
  by_cases hv : P i v <;> simp [hv, mul_comm]

theorem reachable_scalar_indep
    (P : ∀ i, G.ReachableInfoState i → Prop)
    (β : ReachableBehavioralProfile (G := G))
    (f g : _root_.GameTheory.FOSG.ReachablePureProfile G → ENNReal)
    (hf : ∀ π₁ π₂ : _root_.GameTheory.FOSG.ReachablePureProfile G,
      (∀ i (v : G.ReachableInfoState i), P i v → π₁ i v = π₂ i v) →
        f π₁ = f π₂)
    (hg : ∀ π₁ π₂ : _root_.GameTheory.FOSG.ReachablePureProfile G,
      (∀ i (v : G.ReachableInfoState i), ¬ P i v → π₁ i v = π₂ i v) →
        g π₁ = g π₂) :
    ∑ π, reachableBehavioralToMixedJoint (G := G) β π * (f π * g π) =
      (∑ π, reachableBehavioralToMixedJoint (G := G) β π * f π) *
      (∑ π, reachableBehavioralToMixedJoint (G := G) β π * g π) := by
  set ν : PMF (_root_.GameTheory.FOSG.ReachablePureProfile G) :=
    reachableBehavioralToMixedJoint (G := G) β
  have hf_swap :
      ∀ π₁ π₂, f (swapReachableProfileBy (G := G) P π₁ π₂) = f π₁ := by
    intro π₁ π₂
    apply hf
    intro i v hv
    simp [swapReachableProfileBy, hv]
  have hg_swap :
      ∀ π₁ π₂, g (swapReachableProfileBy (G := G) P π₁ π₂) = g π₂ := by
    intro π₁ π₂
    apply hg
    intro i v hv
    simp [swapReachableProfileBy, hv]
  let W := fun π => ν π
  let Fsame : _root_.GameTheory.FOSG.ReachablePureProfile G ×
      _root_.GameTheory.FOSG.ReachablePureProfile G → ENNReal :=
    fun p => W p.1 * W p.2 * (f p.1 * g p.1)
  let Fcross : _root_.GameTheory.FOSG.ReachablePureProfile G ×
      _root_.GameTheory.FOSG.ReachablePureProfile G → ENNReal :=
    fun p => W p.1 * W p.2 * (f p.1 * g p.2)
  let e : _root_.GameTheory.FOSG.ReachablePureProfile G ×
      _root_.GameTheory.FOSG.ReachablePureProfile G →
      _root_.GameTheory.FOSG.ReachablePureProfile G ×
        _root_.GameTheory.FOSG.ReachablePureProfile G :=
    fun p => (swapReachableProfileBy (G := G) P p.1 p.2,
      swapReachableProfileBy (G := G) P p.2 p.1)
  have he : Function.Involutive e := swapReachableProfileBy_involutive (G := G) P
  have hpoint : ∀ p, Fcross p = Fsame (e p) := by
    intro ⟨π₁, π₂⟩
    simp only [Fcross, Fsame, e, W]
    rw [swapReachableBy_weight_eq (G := G) P β π₁ π₂, hf_swap π₁ π₂, hg_swap π₁ π₂]
  have hFsame_eq_Fcross :
      ∑ p : _root_.GameTheory.FOSG.ReachablePureProfile G ×
          _root_.GameTheory.FOSG.ReachablePureProfile G, Fsame p =
        ∑ p : _root_.GameTheory.FOSG.ReachablePureProfile G ×
          _root_.GameTheory.FOSG.ReachablePureProfile G, Fcross p := by
    calc
      ∑ p, Fsame p = ∑ p, Fsame (e p) :=
        (Math.Reindex.sum_univ_eq_sum_univ_of_involutive e he Fsame).symm
      _ = ∑ p, Fcross p := by
        congr 1
        funext p
        exact (hpoint p).symm
  have hFsame_expand :
      ∑ p : _root_.GameTheory.FOSG.ReachablePureProfile G ×
          _root_.GameTheory.FOSG.ReachablePureProfile G, Fsame p =
        (∑ π, ν π * (f π * g π)) * (∑ π₂, ν π₂) := by
    have h1 :
        ∀ (a b : _root_.GameTheory.FOSG.ReachablePureProfile G),
          Fsame (a, b) = (ν a * (f a * g a)) * ν b := fun a b => by
            simp [Fsame, W]
            ring
    simp_rw [Fintype.sum_prod_type, h1, ← Finset.mul_sum, ← Finset.sum_mul]
  have hFcross_expand :
      ∑ p : _root_.GameTheory.FOSG.ReachablePureProfile G ×
          _root_.GameTheory.FOSG.ReachablePureProfile G, Fcross p =
        (∑ π, ν π * f π) * (∑ π, ν π * g π) := by
    have h1 :
        ∀ (a b : _root_.GameTheory.FOSG.ReachablePureProfile G),
          Fcross (a, b) = (ν a * f a) * (ν b * g b) := fun a b => by
            simp [Fcross, W]
            ring
    simp_rw [Fintype.sum_prod_type, h1, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have hsum_one : (∑ π : _root_.GameTheory.FOSG.ReachablePureProfile G, ν π) = 1 := by
    have := PMF.tsum_coe ν
    rwa [tsum_fintype] at this
  calc
    ∑ π, ν π * (f π * g π) = (∑ π, ν π * (f π * g π)) * 1 := by ring
    _ = (∑ π, ν π * (f π * g π)) * (∑ π₂, ν π₂) := by rw [hsum_one]
    _ = ∑ p : _root_.GameTheory.FOSG.ReachablePureProfile G ×
          _root_.GameTheory.FOSG.ReachablePureProfile G, Fsame p := hFsame_expand.symm
    _ = ∑ p : _root_.GameTheory.FOSG.ReachablePureProfile G ×
          _root_.GameTheory.FOSG.ReachablePureProfile G, Fcross p := hFsame_eq_Fcross
    _ = (∑ π, ν π * f π) * (∑ π, ν π * g π) := hFcross_expand

def ReachableSeenBefore
    (h : G.History) (i : ι) (v : G.ReachableInfoState i) : Prop :=
  ∃ h' : G.History, h'.IsPrefix h ∧ h' ≠ h ∧ G.reachableInfoStateOfHistory i h' = v

omit [Fintype ι] [Fintype G.History] [∀ i, Fintype (Act i)] in
theorem reachable_seenBefore_mono_appendStep
    {h : G.History} {e : G.Step} {hsrc : e.src = h.lastState}
    {i : ι} {v : G.ReachableInfoState i}
    (hSeen : ReachableSeenBefore (G := G) h i v) :
    ReachableSeenBefore (G := G) (h.appendStep e hsrc) i v := by
  rcases hSeen with ⟨h', hpref, hne, hv⟩
  refine ⟨h', History.prefix_trans hpref ?_, ?_, hv⟩
  · exact ⟨[e], by simp [History.appendStep]⟩
  · intro hEq
    have hpref' : (h.appendStep e hsrc).IsPrefix h := by
      simpa [hEq] using hpref
    rcases hpref' with ⟨s, hs⟩
    have hlen := congrArg List.length hs
    simp [History.appendStep] at hlen

omit [Fintype ι] [Fintype G.History] [∀ i, Fintype (Act i)] in
theorem reachable_seenBefore_current_appendStep
    (h : G.History) (e : G.Step) (hsrc : e.src = h.lastState) (i : ι) :
    ReachableSeenBefore (G := G) (h.appendStep e hsrc) i
      (G.reachableInfoStateOfHistory i h) := by
  refine ⟨h, ?_, ?_, rfl⟩
  · exact ⟨[e], by simp [History.appendStep]⟩
  · intro hEq
    have hlen := congrArg (fun h' : G.History => h'.steps.length) hEq
    simp [History.appendStep] at hlen

omit [Fintype ι] [Fintype G.History] [∀ i, Fintype (Act i)] in
theorem reachable_not_seenBefore_current
    (h : G.History) (i : ι) :
    ¬ ReachableSeenBefore (G := G) h i (G.reachableInfoStateOfHistory i h) := by
  intro hSeen
  rcases hSeen with ⟨h', hpref, hne, hv⟩
  have hv' : h'.playerView i = h.playerView i := by
    exact congrArg Subtype.val hv
  exact History.playerView_ne_of_properPrefix (G := G) i hpref hne hv'

omit [Fintype G.History] [∀ i, Fintype (Act i)] in
theorem reachable_stepProb_pure_congr_at_history
    {π₁ π₂ : _root_.GameTheory.FOSG.ReachablePureProfile G}
    (h : G.History) (e : G.Step)
    (hag : ∀ i, π₁ i (G.reachableInfoStateOfHistory i h) =
      π₂ i (G.reachableInfoStateOfHistory i h)) :
    G.stepProb (G.pureToBehavioral π₁.extend) h e =
      G.stepProb (G.pureToBehavioral π₂.extend) h e := by
  classical
  rw [G.stepProb_eq_stepActionProb_mul_transition,
    G.stepProb_eq_stepActionProb_mul_transition]
  congr 1
  rw [reachable_stepActionProb_pureToBehavioral (G := G) π₁ h e,
    reachable_stepActionProb_pureToBehavioral (G := G) π₂ h e]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [hag i]

omit [Fintype G.History] [∀ i, Fintype (Act i)] in
/-- Pure-history weight depends only on reachable information-state coordinates
that appear on proper prefixes of the history. -/
theorem reachable_prob_pure_congr_of_agreeOnSeenBefore
    {π₁ π₂ : _root_.GameTheory.FOSG.ReachablePureProfile G}
    (h : G.History)
    (hag : ∀ i (v : G.ReachableInfoState i),
      ReachableSeenBefore (G := G) h i v → π₁ i v = π₂ i v) :
    History.prob (G.pureToBehavioral π₁.extend) h =
      History.prob (G.pureToBehavioral π₂.extend) h := by
  classical
  let H :
      ∀ (es : List G.Step) (hchain : G.StepChainFrom G.init es),
        (∀ i (v : G.ReachableInfoState i),
          ReachableSeenBefore (G := G) ({ steps := es, chain := hchain } : G.History) i v →
            π₁ i v = π₂ i v) →
          History.prob (G.pureToBehavioral π₁.extend)
              ({ steps := es, chain := hchain } : G.History) =
            History.prob (G.pureToBehavioral π₂.extend)
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
            History.prob (G.pureToBehavioral π₁.extend) pref =
              History.prob (G.pureToBehavioral π₂.extend) pref := by
          apply ih prefChain
          intro i v hSeen
          exact hag' i v (reachable_seenBefore_mono_appendStep (G := G) hSeen)
        have hStep :
            G.stepProb (G.pureToBehavioral π₁.extend) pref e =
            G.stepProb (G.pureToBehavioral π₂.extend) pref e := by
          apply reachable_stepProb_pure_congr_at_history (G := G) pref e
          intro i
          exact hag' i _ (reachable_seenBefore_current_appendStep (G := G) pref e hsrc i)
        rw [History.prob_appendStep, History.prob_appendStep, hPref, hStep]
  exact H h.steps h.chain hag

theorem reachable_scalar_indep_stepProb
    (P : ∀ i, G.ReachableInfoState i → Prop)
    (β : ReachableBehavioralProfile (G := G))
    (f : _root_.GameTheory.FOSG.ReachablePureProfile G → ENNReal)
    (h : G.History) (e : G.Step)
    (hf : ∀ π₁ π₂ : _root_.GameTheory.FOSG.ReachablePureProfile G,
      (∀ i (v : G.ReachableInfoState i), P i v → π₁ i v = π₂ i v) →
        f π₁ = f π₂)
    (hP : ∀ i, ¬ P i (G.reachableInfoStateOfHistory i h)) :
    ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
      (f π * G.stepProb (G.pureToBehavioral π.extend) h e) =
        (∑ π, reachableBehavioralToMixedJoint (G := G) β π * f π) *
          G.stepProb β.extend h e := by
  classical
  have hg : ∀ π₁ π₂ : _root_.GameTheory.FOSG.ReachablePureProfile G,
      (∀ i (v : G.ReachableInfoState i), ¬ P i v → π₁ i v = π₂ i v) →
        G.stepProb (G.pureToBehavioral π₁.extend) h e =
          G.stepProb (G.pureToBehavioral π₂.extend) h e := by
    intro π₁ π₂ hag
    apply reachable_stepProb_pure_congr_at_history (G := G) h e
    intro i
    exact hag i _ (hP i)
  calc
    ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
        (f π * G.stepProb (G.pureToBehavioral π.extend) h e)
      = (∑ π, reachableBehavioralToMixedJoint (G := G) β π * f π) *
          (∑ π, reachableBehavioralToMixedJoint (G := G) β π *
            G.stepProb (G.pureToBehavioral π.extend) h e) := by
              exact reachable_scalar_indep (G := G) P β f
                (fun π => G.stepProb (G.pureToBehavioral π.extend) h e) hf hg
    _ = (∑ π, reachableBehavioralToMixedJoint (G := G) β π * f π) *
          G.stepProb β.extend h e := by
            rw [reachable_marginal_stepProb (G := G) β h e]

theorem reachable_marginal_prob
    (β : ReachableBehavioralProfile (G := G)) (h : G.History) :
    ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
      History.prob (G.pureToBehavioral π.extend) h =
        History.prob β.extend h := by
  classical
  let H :
      ∀ (es : List G.Step) (hchain : G.StepChainFrom G.init es),
        ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
          History.prob (G.pureToBehavioral π.extend)
            ({ steps := es, chain := hchain } : G.History) =
            History.prob β.extend ({ steps := es, chain := hchain } : G.History) := by
    intro es
    induction es using List.reverseRecOn with
    | nil =>
        intro hchain
        simp [History.prob]
        have := PMF.tsum_coe (reachableBehavioralToMixedJoint (G := G) β)
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
          ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
              History.prob (G.pureToBehavioral π.extend) (pref.appendStep e hsrc)
            = ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
                (History.prob (G.pureToBehavioral π.extend) pref *
                  G.stepProb (G.pureToBehavioral π.extend) pref e) := by
                    refine Finset.sum_congr rfl ?_
                    intro π _
                    rw [History.prob_appendStep]
          _ = (∑ π, reachableBehavioralToMixedJoint (G := G) β π *
                History.prob (G.pureToBehavioral π.extend) pref) *
                G.stepProb β.extend pref e := by
                  exact reachable_scalar_indep_stepProb (G := G)
                    (P := ReachableSeenBefore (G := G) pref) β
                    (fun π => History.prob (G.pureToBehavioral π.extend) pref)
                    pref e
                    (fun π₁ π₂ hag =>
                      reachable_prob_pure_congr_of_agreeOnSeenBefore (G := G) pref hag)
                    (fun i => reachable_not_seenBefore_current (G := G) pref i)
          _ = History.prob β.extend pref * G.stepProb β.extend pref e := by
                rw [ih prefChain]
          _ = History.prob β.extend (pref.appendStep e hsrc) := by
                rw [History.prob_appendStep]
  exact H h.steps h.chain

variable [DecidablePred G.terminal]

theorem reachable_marginal_terminalWeight
    (β : ReachableBehavioralProfile (G := G)) (h : G.History) :
    ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
      History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h =
        History.terminalWeight (G := G) β.extend h := by
  by_cases hterm : G.terminal h.lastState
  · have hsum :
        (∑ π, reachableBehavioralToMixedJoint (G := G) β π *
          History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h) =
          ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
            History.prob (G.pureToBehavioral π.extend) h := by
              refine Finset.sum_congr rfl ?_
              intro π _
              rw [History.terminalWeight_of_terminal (G := G)
                (σ := G.pureToBehavioral π.extend) hterm]
    rw [History.terminalWeight_of_terminal (G := G) β.extend hterm, hsum,
      reachable_marginal_prob]
  · rw [History.terminalWeight_of_not_terminal (G := G) β.extend hterm]
    have hsum :
        (∑ π, reachableBehavioralToMixedJoint (G := G) β π *
          History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h) =
          ∑ π, reachableBehavioralToMixedJoint (G := G) β π * 0 := by
              refine Finset.sum_congr rfl ?_
              intro π _
              rw [History.terminalWeight_of_not_terminal (G := G)
                (σ := G.pureToBehavioral π.extend) hterm]
    rw [hsum]
    simp

theorem reachable_marginal_terminalMassOn
    (β : ReachableBehavioralProfile (G := G)) (hs : Finset G.History) :
    (∑ π, reachableBehavioralToMixedJoint (G := G) β π *
      History.terminalMassOn (G := G) (G.pureToBehavioral π.extend) hs) =
      History.terminalMassOn (G := G) β.extend hs := by
  calc
    ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
        History.terminalMassOn (G := G) (G.pureToBehavioral π.extend) hs
      = ∑ π, Finset.sum hs (fun h =>
          reachableBehavioralToMixedJoint (G := G) β π *
            History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h) := by
              refine Finset.sum_congr rfl ?_
              intro π _
              rw [History.terminalMassOn, Finset.mul_sum]
    _ = Finset.sum hs (fun h => ∑ π,
          reachableBehavioralToMixedJoint (G := G) β π *
            History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h) := by
              rw [Finset.sum_comm]
    _ = History.terminalMassOn (G := G) β.extend hs := by
          rw [History.terminalMassOn]
          refine Finset.sum_congr rfl ?_
          intro h hh
          exact reachable_marginal_terminalWeight (G := G) β h

theorem reachable_marginal_terminalLaw
    (β : ReachableBehavioralProfile (G := G)) :
    (fun hs =>
      ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
        History.terminalLaw (G := G) (G.pureToBehavioral π.extend) hs) =
      History.terminalLaw (G := G) β.extend := by
  funext hs
  simpa [History.terminalLaw] using reachable_marginal_terminalMassOn (G := G) β hs

theorem reachable_marginal_terminalWeight_toReal
    (β : ReachableBehavioralProfile (G := G)) (h : G.History) :
    ∑ π, (reachableBehavioralToMixedJoint (G := G) β π).toReal *
      (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal =
      (History.terminalWeight (G := G) β.extend h).toReal := by
  calc
    ∑ π, (reachableBehavioralToMixedJoint (G := G) β π).toReal *
        (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal
      = ∑ π,
          (reachableBehavioralToMixedJoint (G := G) β π *
            History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal := by
              refine Finset.sum_congr rfl ?_
              intro π _
              rw [ENNReal.toReal_mul]
    _ = (∑ π,
          reachableBehavioralToMixedJoint (G := G) β π *
            History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal := by
          symm
          apply ENNReal.toReal_sum
          intro π _
          exact ENNReal.mul_ne_top
            (PMF.apply_ne_top (reachableBehavioralToMixedJoint (G := G) β) π)
            (History.terminalWeight_ne_top (G := G) (σ := G.pureToBehavioral π.extend) h)
    _ = (History.terminalWeight (G := G) β.extend h).toReal := by
          rw [reachable_marginal_terminalWeight (G := G) β h]

theorem reachable_marginal_terminalUtilitySum
    (β : ReachableBehavioralProfile (G := G)) (i : ι) :
    ∑ π, (reachableBehavioralToMixedJoint (G := G) β π).toReal *
      (∑ h : G.History,
        (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal *
          History.utility h i) =
      ∑ h : G.History,
        (History.terminalWeight (G := G) β.extend h).toReal * History.utility h i := by
  classical
  calc
    ∑ π, (reachableBehavioralToMixedJoint (G := G) β π).toReal *
        ∑ h : G.History,
          (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal *
            History.utility h i
      = ∑ π, ∑ h : G.History,
          ((reachableBehavioralToMixedJoint (G := G) β π).toReal *
            (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal) *
              History.utility h i := by
                refine Finset.sum_congr rfl ?_
                intro π _
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro h _
                simp [mul_assoc]
    _ = ∑ h : G.History, ∑ π,
          ((reachableBehavioralToMixedJoint (G := G) β π).toReal *
            (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal) *
              History.utility h i := by
                rw [Finset.sum_comm]
    _ = ∑ h : G.History,
          (∑ π, (reachableBehavioralToMixedJoint (G := G) β π).toReal *
            (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal) *
              History.utility h i := by
                refine Finset.sum_congr rfl ?_
                intro h _
                rw [← Finset.sum_mul]
    _ = ∑ h : G.History,
          (History.terminalWeight (G := G) β.extend h).toReal * History.utility h i := by
                refine Finset.sum_congr rfl ?_
                intro h _
                simpa using
                  congrArg (fun x => x * History.utility h i)
                    (reachable_marginal_terminalWeight_toReal (G := G) β h)

theorem reachable_marginal_terminalExpectation
    (β : ReachableBehavioralProfile (G := G)) (u : G.History → ℝ) :
    ∑ π, (reachableBehavioralToMixedJoint (G := G) β π).toReal *
      (∑ h : G.History,
        (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal *
          u h) =
      ∑ h : G.History,
        (History.terminalWeight (G := G) β.extend h).toReal * u h := by
  classical
  calc
    ∑ π, (reachableBehavioralToMixedJoint (G := G) β π).toReal *
        ∑ h : G.History,
          (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal *
            u h
      = ∑ π, ∑ h : G.History,
          ((reachableBehavioralToMixedJoint (G := G) β π).toReal *
            (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal) *
              u h := by
                refine Finset.sum_congr rfl ?_
                intro π _
                rw [Finset.mul_sum]
                refine Finset.sum_congr rfl ?_
                intro h _
                simp [mul_assoc]
    _ = ∑ h : G.History, ∑ π,
          ((reachableBehavioralToMixedJoint (G := G) β π).toReal *
            (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal) *
              u h := by
                rw [Finset.sum_comm]
    _ = ∑ h : G.History,
          (∑ π, (reachableBehavioralToMixedJoint (G := G) β π).toReal *
            (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal) *
              u h := by
                refine Finset.sum_congr rfl ?_
                intro h _
                rw [← Finset.sum_mul]
    _ = ∑ h : G.History,
          (History.terminalWeight (G := G) β.extend h).toReal * u h := by
                refine Finset.sum_congr rfl ?_
                intro h _
                simpa using
                  congrArg (fun x => x * u h)
                    (reachable_marginal_terminalWeight_toReal (G := G) β h)

/- Native reachable-coordinate Kuhn theorem for FOSGs at realized histories. -/
omit [DecidablePred G.terminal] in
theorem behavioral_to_mixed_prob_reachable
    (β : ReachableBehavioralProfile (G := G)) (h : G.History) :
    ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
      History.prob (G.pureToBehavioral π.extend) h =
        History.prob β.extend h :=
  reachable_marginal_prob (G := G) β h

/-- Native reachable-coordinate Kuhn theorem for terminal-history weights. -/
theorem behavioral_to_mixed_terminalWeight_reachable
    (β : ReachableBehavioralProfile (G := G)) (h : G.History) :
    ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
      History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h =
        History.terminalWeight (G := G) β.extend h :=
  reachable_marginal_terminalWeight (G := G) β h

/-- Native reachable-coordinate Kuhn theorem for finite terminal events. -/
theorem behavioral_to_mixed_terminalMassOn_reachable
    (β : ReachableBehavioralProfile (G := G)) (hs : Finset G.History) :
    (∑ π, reachableBehavioralToMixedJoint (G := G) β π *
      History.terminalMassOn (G := G) (G.pureToBehavioral π.extend) hs) =
      History.terminalMassOn (G := G) β.extend hs :=
  reachable_marginal_terminalMassOn (G := G) β hs

/-- Native reachable-coordinate Kuhn theorem for terminal laws. -/
theorem behavioral_to_mixed_terminalLaw_reachable
    (β : ReachableBehavioralProfile (G := G)) :
    (fun hs =>
      ∑ π, reachableBehavioralToMixedJoint (G := G) β π *
        History.terminalLaw (G := G) (G.pureToBehavioral π.extend) hs) =
      History.terminalLaw (G := G) β.extend :=
  reachable_marginal_terminalLaw (G := G) β

/-- Native reachable-coordinate Kuhn theorem for FOSG expected utility. -/
theorem behavioral_to_mixed_eu_reachable
    (hNorm : G.HasNormalizedTerminalLaw)
    (β : G.ReachableLegalBehavioralProfile) (i : ι) :
    ∑ π, (reachableBehavioralToMixedJoint (G := G) β.toProfile π).toReal *
      (∑ h : G.History,
        (History.terminalWeight (G := G) (G.pureToBehavioral π.extend) h).toReal *
          History.utility h i) =
      (G.toKernelGame hNorm).eu β.extend i := by
  rw [G.toKernelGame_eu_eq hNorm β.extend i]
  exact reachable_marginal_terminalUtilitySum (G := G) β.toProfile i

end ReachableNative

end Kuhn

end FOSG

end GameTheory
