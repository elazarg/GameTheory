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
import GameTheory.Languages.FOSG.ReachableHistory.Law

namespace GameTheory

namespace FOSG

namespace Kuhn

open ObsModelCoreBridge

attribute [local instance] Fintype.ofFinite

open scoped BigOperators

variable {ι W : Type} [DecidableEq ι]
variable {Act : ι → Type} {PrivObs : ι → Type} {PubObs : Type}
variable (G : FOSG ι W Act PrivObs PubObs)

section Step

variable [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)]

noncomputable local instance pureStrategyFintype
    (i : ι) : Fintype (PureStrategy (G := G) i) := by
  classical
  dsimp [PureStrategy]
  infer_instance

noncomputable local instance pureProfileFintype
    : Fintype (_root_.GameTheory.FOSG.PureProfile G) := by
  classical
  dsimp [_root_.GameTheory.FOSG.PureProfile, PureStrategy]
  infer_instance

section Raw

variable [∀ i, DecidableEq (Act i)]

omit [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
theorem stepActionProb_pureToBehavioral
    (π : _root_.GameTheory.FOSG.PureProfile G) (pref : G.History) (e : G.Step) :
    G.stepActionProb (G.pureToBehavioral π) pref e =
      ∏ i, if π i (pref.playerView i) = e.ownAction? i then 1 else 0 := by
  classical
  unfold FOSG.stepActionProb
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [FOSG.pureToBehavioral_apply]
  by_cases hEq : π i (pref.playerView i) = e.ownAction? i
  · simp [PMF.pure_apply, hEq]
  · have hEq' : e.ownAction? i ≠ π i (pref.playerView i) := by
      simpa [eq_comm] using hEq
    simp [PMF.pure_apply, hEq, hEq']

/-- One-step Kuhn marginal at the raw dependent function type. -/
theorem marginal_stepActionProb_raw
    (β : BehavioralProfile (G := G)) (pref : G.History) (e : G.Step) :
    ∑ ρ : ((i : ι) → PureStrategy (G := G) i),
      (Math.PMFProduct.pmfPi (behavioralToMixed (G := G) β)) ρ *
        (∏ i, if ρ i (pref.playerView i) = e.ownAction? i then 1 else 0) =
      G.stepActionProb β pref e := by
  classical
  have hprod :
      (∑ ρ : ((i : ι) → PureStrategy (G := G) i),
        (Math.PMFProduct.pmfPi (behavioralToMixed (G := G) β)) ρ *
          (∏ i, if ρ i (pref.playerView i) = e.ownAction? i then 1 else 0)) =
      ∑ ρ : ((i : ι) → PureStrategy (G := G) i),
        ∏ i,
          (behavioralToMixed (G := G) β i) (ρ i) *
            (if ρ i (pref.playerView i) = e.ownAction? i then 1 else 0) := by
    refine Finset.sum_congr rfl ?_
    intro ρ _
    rw [Math.PMFProduct.pmfPi_apply, ← Finset.prod_mul_distrib]
  rw [hprod]
  rw [show (∑ ρ : ((i : ι) → PureStrategy (G := G) i),
        ∏ i,
          (behavioralToMixed (G := G) β i) (ρ i) *
            (if ρ i (pref.playerView i) = e.ownAction? i then 1 else 0)) =
      ∏ i, ∑ πi : PureStrategy (G := G) i,
        (behavioralToMixed (G := G) β i) πi *
          (if πi (pref.playerView i) = e.ownAction? i then 1 else 0) by
      exact
        (show (∏ i, ∑ πi : PureStrategy (G := G) i,
            (behavioralToMixed (G := G) β i) πi *
              (if πi (pref.playerView i) = e.ownAction? i then 1 else 0)) =
            ∑ ρ : ((i : ι) → PureStrategy (G := G) i),
              ∏ i,
                (behavioralToMixed (G := G) β i) (ρ i) *
                  (if ρ i (pref.playerView i) = e.ownAction? i then 1 else 0) from
          (@Fintype.prod_sum ι ENNReal _ _ _ (fun i => PureStrategy (G := G) i) _
          (fun i πi =>
            (behavioralToMixed (G := G) β i) πi *
              (if πi (pref.playerView i) = e.ownAction? i then 1 else 0)))).symm]
  unfold FOSG.stepActionProb
  refine Finset.prod_congr rfl ?_
  intro i _
  have hcoord :
      ∑ πi : PureStrategy (G := G) i,
        (behavioralToMixed (G := G) β i) πi *
          (if πi (pref.playerView i) = e.ownAction? i then 1 else 0) =
            β i (pref.playerView i) (e.ownAction? i) := by
    change (∑ πi : G.InfoState i → Option (Act i),
        (Math.PMFProduct.pmfPi (β i)) πi *
          (if πi (pref.playerView i) = e.ownAction? i then 1 else 0)) =
      β i (pref.playerView i) (e.ownAction? i)
    exact Math.PMFProduct.pmfPi_coord_mass_mul_indicator (β i) (pref.playerView i)
      (e.ownAction? i)
  simpa using hcoord

end Raw

/-- One-step Kuhn marginal in the native FOSG profile type. -/
theorem marginal_stepActionProb
    (β : BehavioralProfile (G := G)) (pref : G.History) (e : G.Step) :
    ∑ π : _root_.GameTheory.FOSG.PureProfile G,
      behavioralToMixedJoint (G := G) β π *
        G.stepActionProb (G.pureToBehavioral π) pref e =
      G.stepActionProb β pref e := by
  classical
  rw [show (∑ π : _root_.GameTheory.FOSG.PureProfile G,
        behavioralToMixedJoint (G := G) β π *
          G.stepActionProb (G.pureToBehavioral π) pref e) =
      ∑ ρ : ((i : ι) → PureStrategy (G := G) i),
        (Math.PMFProduct.pmfPi (behavioralToMixed (G := G) β)) ρ *
          (∏ i, if ρ i (pref.playerView i) = e.ownAction? i then 1 else 0) by
      refine Finset.sum_congr rfl ?_
      intro ρ _
      rw [stepActionProb_pureToBehavioral (G := G) ρ pref e]
      rfl]
  simpa using marginal_stepActionProb_raw (G := G) β pref e

/-- One-step Kuhn marginal for realized step weights in native FOSG semantics. -/
theorem marginal_stepProb
    (β : BehavioralProfile (G := G)) (pref : G.History) (e : G.Step) :
    ∑ π : _root_.GameTheory.FOSG.PureProfile G,
      behavioralToMixedJoint (G := G) β π *
        G.stepProb (G.pureToBehavioral π) pref e =
      G.stepProb β pref e := by
  let p : ENNReal := (G.transition e.src e.act) e.dst
  calc
    ∑ π : _root_.GameTheory.FOSG.PureProfile G,
        behavioralToMixedJoint (G := G) β π *
          G.stepProb (G.pureToBehavioral π) pref e
      = ∑ π : _root_.GameTheory.FOSG.PureProfile G,
          (behavioralToMixedJoint (G := G) β π *
            G.stepActionProb (G.pureToBehavioral π) pref e) * p := by
              simp [p, mul_assoc]
    _ = (∑ π : _root_.GameTheory.FOSG.PureProfile G,
          behavioralToMixedJoint (G := G) β π *
            G.stepActionProb (G.pureToBehavioral π) pref e) * p := by
              rw [Finset.sum_mul]
    _ = G.stepActionProb β pref e * p := by
          rw [marginal_stepActionProb (G := G) β pref e]
    _ = G.stepProb β pref e := by
          simp [p]

end Step

section ScalarIndependence

variable [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)]

noncomputable local instance pureStrategyFintypeScalar
    (i : ι) : Fintype (PureStrategy (G := G) i) := by
  classical
  dsimp [PureStrategy]
  infer_instance

noncomputable local instance pureProfileFintypeScalar
    : Fintype (_root_.GameTheory.FOSG.PureProfile G) := by
  classical
  dsimp [_root_.GameTheory.FOSG.PureProfile, PureStrategy]
  infer_instance

/-- Swap coordinates between two pure profiles according to a predicate on
player-information-state coordinates. -/
noncomputable def swapProfileBy
    (P : ∀ i, G.InfoState i → Prop)
    (π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G) :
    _root_.GameTheory.FOSG.PureProfile G := by
  classical
  exact fun i v => if P i v then π₁ i v else π₂ i v

omit [Fintype ι] [∀ i, Fintype (G.InfoState i)] [∀ i, Fintype (Act i)] in
theorem swapProfileBy_involutive
    (P : ∀ i, G.InfoState i → Prop) :
    Function.Involutive
      (fun (p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G) =>
        (swapProfileBy (G := G) P p.1 p.2,
          swapProfileBy (G := G) P p.2 p.1)) := by
  classical
  intro ⟨π₁, π₂⟩
  apply Prod.ext
  · funext i v
    by_cases hv : P i v <;> simp [swapProfileBy, hv]
  · funext i v
    by_cases hv : P i v <;> simp [swapProfileBy, hv]

open Classical in
theorem swapBy_weight_eq
    (P : ∀ i, G.InfoState i → Prop)
    (β : BehavioralProfile (G := G))
    (π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G) :
    behavioralToMixedJoint (G := G) β (swapProfileBy (G := G) P π₁ π₂) *
      behavioralToMixedJoint (G := G) β (swapProfileBy (G := G) P π₂ π₁) =
    behavioralToMixedJoint (G := G) β π₁ *
      behavioralToMixedJoint (G := G) β π₂ := by
  simp only [behavioralToMixedJoint, behavioralToMixed,
    Math.PMFProduct.pmfPi_apply]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  funext i
  simp only [swapProfileBy]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  funext v
  by_cases hv : P i v <;> simp [hv, mul_comm]

/-- Scalar independence under the native FOSG product mixed measure: if `f`
depends only on coordinates where `P` holds, and `g` depends only on the
complementary coordinates, then `E[f * g] = E[f] * E[g]`. -/
theorem scalar_indep
    (P : ∀ i, G.InfoState i → Prop)
    (β : BehavioralProfile (G := G))
    (f g : _root_.GameTheory.FOSG.PureProfile G → ENNReal)
    (hf : ∀ π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G,
      (∀ i (v : G.InfoState i), P i v → π₁ i v = π₂ i v) →
        f π₁ = f π₂)
    (hg : ∀ π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G,
      (∀ i (v : G.InfoState i), ¬ P i v → π₁ i v = π₂ i v) →
        g π₁ = g π₂) :
    ∑ π, behavioralToMixedJoint (G := G) β π * (f π * g π) =
      (∑ π, behavioralToMixedJoint (G := G) β π * f π) *
      (∑ π, behavioralToMixedJoint (G := G) β π * g π) := by
  set ν : PMF (_root_.GameTheory.FOSG.PureProfile G) := behavioralToMixedJoint (G := G) β
  have hf_swap :
      ∀ π₁ π₂, f (swapProfileBy (G := G) P π₁ π₂) = f π₁ := by
    intro π₁ π₂
    apply hf
    intro i v hv
    simp [swapProfileBy, hv]
  have hg_swap :
      ∀ π₁ π₂, g (swapProfileBy (G := G) P π₁ π₂) = g π₂ := by
    intro π₁ π₂
    apply hg
    intro i v hv
    simp [swapProfileBy, hv]
  let W := fun π => ν π
  let Fsame : _root_.GameTheory.FOSG.PureProfile G ×
      _root_.GameTheory.FOSG.PureProfile G → ENNReal :=
    fun p => W p.1 * W p.2 * (f p.1 * g p.1)
  let Fcross : _root_.GameTheory.FOSG.PureProfile G ×
      _root_.GameTheory.FOSG.PureProfile G → ENNReal :=
    fun p => W p.1 * W p.2 * (f p.1 * g p.2)
  let e : _root_.GameTheory.FOSG.PureProfile G ×
      _root_.GameTheory.FOSG.PureProfile G →
      _root_.GameTheory.FOSG.PureProfile G ×
        _root_.GameTheory.FOSG.PureProfile G :=
    fun p => (swapProfileBy (G := G) P p.1 p.2,
      swapProfileBy (G := G) P p.2 p.1)
  have he : Function.Involutive e := swapProfileBy_involutive (G := G) P
  have hpoint : ∀ p, Fcross p = Fsame (e p) := by
    intro ⟨π₁, π₂⟩
    simp only [Fcross, Fsame, e, W]
    rw [swapBy_weight_eq (G := G) P β π₁ π₂, hf_swap π₁ π₂, hg_swap π₁ π₂]
  have hFsame_eq_Fcross :
      ∑ p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G, Fsame p =
        ∑ p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G, Fcross p := by
    calc
      ∑ p, Fsame p = ∑ p, Fsame (e p) :=
        (Math.Reindex.sum_univ_eq_sum_univ_of_involutive e he Fsame).symm
      _ = ∑ p, Fcross p := by
        congr 1
        funext p
        exact (hpoint p).symm
  have hFsame_expand :
      ∑ p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G, Fsame p =
        (∑ π, ν π * (f π * g π)) * (∑ π₂, ν π₂) := by
    have h1 :
        ∀ (a b : _root_.GameTheory.FOSG.PureProfile G),
          Fsame (a, b) = (ν a * (f a * g a)) * ν b := fun a b => by
            simp [Fsame, W]
            ring
    simp_rw [Fintype.sum_prod_type, h1, ← Finset.mul_sum, ← Finset.sum_mul]
  have hFcross_expand :
      ∑ p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G, Fcross p =
        (∑ π, ν π * f π) * (∑ π, ν π * g π) := by
    have h1 :
        ∀ (a b : _root_.GameTheory.FOSG.PureProfile G),
          Fcross (a, b) = (ν a * f a) * (ν b * g b) := fun a b => by
            simp [Fcross, W]
            ring
    simp_rw [Fintype.sum_prod_type, h1, ← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have hsum_one : (∑ π : _root_.GameTheory.FOSG.PureProfile G, ν π) = 1 := by
    have := PMF.tsum_coe ν
    rwa [tsum_fintype] at this
  calc
    ∑ π, ν π * (f π * g π) = (∑ π, ν π * (f π * g π)) * 1 := by ring
    _ = (∑ π, ν π * (f π * g π)) * (∑ π₂, ν π₂) := by rw [hsum_one]
    _ = ∑ p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G, Fsame p := hFsame_expand.symm
    _ = ∑ p : _root_.GameTheory.FOSG.PureProfile G ×
          _root_.GameTheory.FOSG.PureProfile G, Fcross p := hFsame_eq_Fcross
    _ = (∑ π, ν π * f π) * (∑ π, ν π * g π) := hFcross_expand

section StepCorollaries

/-- Scalar independence specialized to the realized one-step weight at a given
history. If `f` depends only on coordinates in `P`, and the current
information states of `h` all lie outside `P`, then `f` is independent of the
next-step realized weight. -/
theorem scalar_indep_stepProb
    (P : ∀ i, G.InfoState i → Prop)
    (β : BehavioralProfile (G := G))
    (f : _root_.GameTheory.FOSG.PureProfile G → ENNReal)
    (h : G.History) (e : G.Step)
    (hf : ∀ π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G,
      (∀ i (v : G.InfoState i), P i v → π₁ i v = π₂ i v) →
        f π₁ = f π₂)
    (hP : ∀ i, ¬ P i (h.playerView i)) :
    ∑ π, behavioralToMixedJoint (G := G) β π *
      (f π * G.stepProb (G.pureToBehavioral π) h e) =
        (∑ π, behavioralToMixedJoint (G := G) β π * f π) *
          G.stepProb β h e := by
  classical
  have hg : ∀ π₁ π₂ : _root_.GameTheory.FOSG.PureProfile G,
      (∀ i (v : G.InfoState i), ¬ P i v → π₁ i v = π₂ i v) →
        G.stepProb (G.pureToBehavioral π₁) h e =
          G.stepProb (G.pureToBehavioral π₂) h e := by
    intro π₁ π₂ hag
    rw [G.stepProb_eq_stepActionProb_mul_transition,
      G.stepProb_eq_stepActionProb_mul_transition]
    congr 1
    unfold FOSG.stepActionProb
    refine Finset.prod_congr rfl ?_
    intro i _
    rw [FOSG.pureToBehavioral_apply, FOSG.pureToBehavioral_apply]
    have hEq : π₁ i (h.playerView i) = π₂ i (h.playerView i) := hag i _ (hP i)
    simp [PMF.pure_apply, hEq]
  calc
    ∑ π, behavioralToMixedJoint (G := G) β π *
        (f π * G.stepProb (G.pureToBehavioral π) h e)
      = (∑ π, behavioralToMixedJoint (G := G) β π * f π) *
          (∑ π, behavioralToMixedJoint (G := G) β π *
            G.stepProb (G.pureToBehavioral π) h e) := by
              exact scalar_indep (G := G) P β f
                (fun π => G.stepProb (G.pureToBehavioral π) h e) hf hg
    _ = (∑ π, behavioralToMixedJoint (G := G) β π * f π) *
          G.stepProb β h e := by
            rw [marginal_stepProb (G := G) β h e]

end StepCorollaries

end ScalarIndependence

end Kuhn

end FOSG

end GameTheory
