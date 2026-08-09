/-
Copyright (c) 2026 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import GameTheory.Concepts.Stochastic.Core.Basic

/-!
# The infinite-play measure for a stochastic game

`GameTheory.Concepts.Stochastic.Core.Basic` builds, for a fixed `StochasticGame` and a fixed
`BehaviorProfile`, only the **finite-horizon** distributions `histDist σ s₀ t` over
`t`-stage histories. This file supplies the missing infinite object: a probability measure
over entire infinite plays, built by the **Ionescu-Tulcea theorem**
(`ProbabilityTheory.Kernel.trajMeasure`, `Mathlib.Probability.Kernel.IonescuTulcea.Traj`),
together with the projection property identifying its finite-horizon marginals with
`histDist`.

## Measurable-space choice

`StochasticGame.State` and `StochasticGame.Act` are bare `Type`s with no `MeasurableSpace`
instance. The uniform-equilibrium program only needs this construction for games with
finitely many states and actions, so this file equips both with the **discrete** (`⊤`)
measurable-space structure
under `[Fintype G.State]` / `[∀ i, Fintype (G.Act i)]` hypotheses, added here rather than as
fields of `StochasticGame` itself. Every set is measurable in this structure, so every
function out of a finite power of these spaces is automatically measurable
(`Measurable.of_discrete`), which is what makes the Ionescu-Tulcea kernel family trivial to
build: no separate measurability side conditions are needed anywhere below.

## The construction

An infinite play is recorded as a sequence `Play G := ℕ → G.State × G.JointAct` of per-stage
outcomes: the state occupied at a stage together with the joint action played there. Fixing a
`BehaviorProfile σ` and initial state `s₀` gives, at every stage `n`, a kernel from the
trajectory so far (`∀ i : Set.Iic n, G.State × G.JointAct`) to the next stage's outcome
(`stepKernel`): draw the next state from `G.transition` at the last state and action, then
draw the next joint action from `σ`'s randomization at the history this determines. This
family of kernels, together with the stage-`0` distribution (`initialMeasure`), is exactly the
input the Ionescu-Tulcea theorem needs; `infinitePlayMeasure` is its output.

## Main definitions

* `StochasticGame.Play` — an infinite play: the per-stage `(state, joint action)` outcome
  realized at every stage `0, 1, 2, …`
* `StochasticGame.stepKernel` — the one-stage Ionescu-Tulcea kernel: from the trajectory so
  far to the next stage's outcome
* `StochasticGame.infinitePlayMeasure` — the infinite-play measure, built from `stepKernel`
  and the stage-`0` distribution via `ProbabilityTheory.Kernel.trajMeasure`
* `StochasticGame.histOfPlay` — the `Hist t` implicit in the first `t` stages of a play

## Main statements

* `StochasticGame.map_histOfPlay_infinitePlayMeasure` — **the projection property**: the
  pushforward of `infinitePlayMeasure` along `histOfPlay t` is `(histDist σ s₀ t).toMeasure`,
  so `infinitePlayMeasure`'s finite-horizon marginals agree with the existing finite-horizon
  history distribution
* `StochasticGame.integral_histOfPlay_infinitePlayMeasure` — the projection property
  transported through integration, which is what makes `LiminfAverageBridge`'s
  game-facing corollaries unconditional in their pathwise realization
-/

noncomputable section

open MeasureTheory ProbabilityTheory Kernel Set
open scoped ENNReal

namespace GameTheory

namespace StochasticGame

variable {ι : Type} (G : StochasticGame ι)

/-- The per-stage outcome recorded in an infinite play of `G`: the state occupied at a stage
together with the joint action played there. -/
abbrev StageOutcome : Type := G.State × G.JointAct

/-- An infinite play of `G`: the `(state, joint action)` pair realized at every stage
`0, 1, 2, …`. -/
abbrev Play : Type := ℕ → G.StageOutcome

/-- Rebuild the `Hist (n + 1)` used by `histDist` from the first `n + 1` stage outcomes of a
play (indexed by `Finset.Iic n`, which has `n + 1` elements `0, …, n`) and a freshly drawn next
state: the stage outcomes become the completed-stage record, and the drawn state becomes the
current state. -/
def histOfCoords {n : ℕ} (x : ∀ _ : Finset.Iic n, G.StageOutcome) (s' : G.State) :
    G.Hist (n + 1) :=
  (fun k : Fin (n + 1) => x ⟨k.1, Finset.mem_Iic.mpr (Nat.lt_succ_iff.mp k.2)⟩, s')

/-- Read off the `Hist t` implicit in the first `t + 1` stage outcomes of a play (indexed by
`Finset.Iic t`): the completed-stage record is stage outcomes `0, …, t - 1`, and the current
state is the state half of stage `t`'s outcome — the state occupied just before stage `t`'s
action is chosen. -/
def histOfIic (t : ℕ) (x : ∀ _ : Finset.Iic t, G.StageOutcome) : G.Hist t :=
  (fun k : Fin t => x ⟨k.1, Finset.mem_Iic.mpr k.2.le⟩,
    (x ⟨t, Finset.mem_Iic.mpr (le_refl t)⟩).1)

/-- The history recorded after `t` completed stages of a play: the first `t` stage outcomes
form the completed-stage record, and the state half of stage `t`'s outcome — the state
occupied just before stage `t`'s action is chosen — is the current state. -/
def histOfPlay (t : ℕ) (p : G.Play) : G.Hist t :=
  (fun k : Fin t => p k, (p t).1)

variable [Fintype ι] [DecidableEq ι]

/-- The one-step distribution of the next stage outcome, given the behavior profile `σ` and
the stage outcomes realized so far (up to and including stage `n`): draw the next state from
the transition kernel at the last-recorded state and action, then draw the next joint action
from `σ`'s randomization at the history this determines. -/
def stepPMF (σ : G.BehaviorProfile) (n : ℕ) (x : ∀ _ : Finset.Iic n, G.StageOutcome) :
    PMF G.StageOutcome :=
  (G.transition (x ⟨n, Finset.mem_Iic.mpr (le_refl n)⟩).1
      (x ⟨n, Finset.mem_Iic.mpr (le_refl n)⟩).2).bind fun s' =>
    (G.stageActionDist σ (G.histOfCoords x s')).map fun a' => (s', a')

/-- The distribution of the stage-`0` outcome from initial state `s₀`: the state is `s₀`
deterministically, and the joint action is `σ`'s randomization at the empty history. -/
def initialPMF (σ : G.BehaviorProfile) (s₀ : G.State) : PMF G.StageOutcome :=
  (G.stageActionDist σ (G.emptyHist s₀)).map fun a => (s₀, a)

section Measure

variable [Fintype G.State] [DecidableEq G.State] [∀ i, Fintype (G.Act i)]
  [∀ i, DecidableEq (G.Act i)]

/-- The discrete (`⊤`) measurable-space structure on the game's finite state space: every
subset is measurable. See the module docstring for why this choice is legitimate here. -/
instance instMeasurableSpaceState : MeasurableSpace G.State := ⊤

/-- The discrete measurable-space structure on each player's finite action set. -/
instance instMeasurableSpaceAct (i : ι) : MeasurableSpace (G.Act i) := ⊤

/-- `stepPMF`, bundled as a kernel from the trajectory so far to the next stage outcome — the
input the Ionescu-Tulcea theorem needs. Every function out of a finite discrete space is
measurable (`Measurable.of_discrete`), so this needs no separate measurability argument. -/
def stepKernel (σ : G.BehaviorProfile) (n : ℕ) :
    Kernel (∀ _ : Finset.Iic n, G.StageOutcome) G.StageOutcome where
  toFun x := (G.stepPMF σ n x).toMeasure
  measurable' := Measurable.of_discrete

instance instIsMarkovKernelStepKernel (σ : G.BehaviorProfile) (n : ℕ) :
    IsMarkovKernel (G.stepKernel σ n) :=
  ⟨fun _ => PMF.toMeasure.isProbabilityMeasure _⟩

/-- The distribution of the stage-`0` outcome, as a measure. -/
def initialMeasure (σ : G.BehaviorProfile) (s₀ : G.State) : Measure G.StageOutcome :=
  (G.initialPMF σ s₀).toMeasure

instance instIsProbabilityMeasureInitialMeasure (σ : G.BehaviorProfile) (s₀ : G.State) :
    IsProbabilityMeasure (G.initialMeasure σ s₀) :=
  PMF.toMeasure.isProbabilityMeasure _

/-- **The infinite-play measure.** The distribution over infinite plays of `G` induced by the
behavior profile `σ` from initial state `s₀`, constructed via the Ionescu-Tulcea theorem
(`ProbabilityTheory.Kernel.trajMeasure`) from the one-step kernel family `stepKernel` and the
stage-`0` distribution `initialMeasure`. -/
def infinitePlayMeasure (σ : G.BehaviorProfile) (s₀ : G.State) : Measure G.Play :=
  Kernel.trajMeasure (X := fun _ : ℕ => G.StageOutcome) (G.initialMeasure σ s₀)
    (G.stepKernel σ)

instance instIsProbabilityMeasureInfinitePlayMeasure (σ : G.BehaviorProfile) (s₀ : G.State) :
    IsProbabilityMeasure (G.infinitePlayMeasure σ s₀) := by
  unfold infinitePlayMeasure
  infer_instance

end Measure

section BindToMeasure

/-- `Measure.bind` of two measures built from `PMF.toMeasure` agrees with `PMF.toMeasure` of
the corresponding `PMF.bind`. This is the compatibility lemma between the Giry monad
(`Measure.bind`, used by `Kernel` composition) and the `PMF` monad (used by `histDist`) that
the projection property is built from. -/
theorem measureBind_toMeasure_eq {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Countable α] [MeasurableSingletonClass α] (p : PMF α) (q : α → PMF β) :
    Measure.bind p.toMeasure (fun a => (q a).toMeasure) = (p.bind q).toMeasure := by
  ext s hs
  rw [Measure.bind_apply hs (Measurable.of_discrete).aemeasurable,
    MeasureTheory.lintegral_countable', PMF.toMeasure_bind_apply p q s hs]
  refine tsum_congr fun a => ?_
  rw [PMF.toMeasure_apply_singleton p a (measurableSet_singleton a), mul_comm]

/-- Pushing a `Measure.bind` forward along a measurable map is the same as pushing each fiber
forward first. This is the Giry-monad fact that lets the pushforward of `infinitePlayMeasure`
(built by `Measure.bind` through `Kernel.trajMeasure`) commute past `frestrictLe`. -/
theorem bind_map_eq {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : Measure α} {A : α → Measure β} {f : β → γ}
    (hA : Measurable A) (hf : Measurable f) :
    (μ.bind A).map f = μ.bind (fun a => (A a).map f) := by
  have hg : Measurable (fun b : β => Measure.dirac (f b)) := Measure.measurable_dirac.comp hf
  rw [← Measure.bind_dirac_eq_map (μ.bind A) hf,
    Measure.bind_bind hA.aemeasurable hg.aemeasurable]
  have : (fun a => (A a).bind (fun b => Measure.dirac (f b))) = fun a => (A a).map f := by
    funext a
    exact Measure.bind_dirac_eq_map (A a) hf
  rw [this]

end BindToMeasure

section ProjectiveFamily

variable [Fintype G.State] [DecidableEq G.State] [∀ i, Fintype (G.Act i)]
  [∀ i, DecidableEq (G.Act i)]

/-- Extend the trajectory `x` up to time `n` by one fresh stage outcome `z` at time `n + 1`,
keeping every earlier coordinate as recorded in `x`. This is the concrete shape of Mathlib's
`IicProdIoc n (n + 1) (x, piSingleton n z)` gluing map for the constant type family used here,
computed once so the Ionescu-Tulcea recursion can be matched against `coordsDist`'s. -/
def extendCoords {n : ℕ} (x : ∀ _ : Finset.Iic n, G.StageOutcome) (z : G.StageOutcome) :
    ∀ _ : Finset.Iic (n + 1), G.StageOutcome :=
  fun i => if h : i.1 ≤ n then x ⟨i.1, Finset.mem_Iic.mpr h⟩ else z

/-- A hand-rolled recursive `PMF` family over the first `t + 1` stage outcomes of a play
(indexed by `Finset.Iic t`), matching `stepPMF`/`initialPMF`'s recursion directly. This is the
bridge between `histDist`'s finite recursion and the Ionescu-Tulcea `partialTraj` kernel
family. -/
def coordsDist (σ : G.BehaviorProfile) (s₀ : G.State) :
    (t : ℕ) → PMF (∀ _ : Finset.Iic t, G.StageOutcome) :=
  fun t => Nat.rec ((G.initialPMF σ s₀).map fun z (_ : Finset.Iic 0) => z)
    (fun n ih => ih.bind fun x => (G.stepPMF σ n x).map (G.extendCoords x)) t

omit [DecidableEq ι] [Fintype G.State] [DecidableEq G.State] [∀ i, Fintype (G.Act i)]
  [∀ i, DecidableEq (G.Act i)] in
/-- Unfold `coordsDist` at a successor time: bind the previous stage's distribution and step
forward via `stepPMF`/`extendCoords`. -/
theorem coordsDist_succ (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) :
    G.coordsDist σ s₀ (t + 1) =
      (G.coordsDist σ s₀ t).bind fun x => (G.stepPMF σ t x).map (G.extendCoords x) :=
  rfl

/-- **Generic one-step `partialTraj` formula**, for an abstract Ionescu-Tulcea kernel family.
Kept fully generic in `X`/`κ` (never specialized inline) because instantiating `X` with a
concrete constant family before rewriting defeats Lean's unification of the `IicProdIoc`/
`piSingleton` gluing combinators used by `partialTraj_succ_self`; specializing only after the
rewrite (`stepKernel_partialTraj_succ_self` below) avoids that. -/
private theorem partialTraj_succ_self_apply {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
    {κ : (n : ℕ) → Kernel (∀ i : Finset.Iic n, X i) (X (n + 1))}
    [∀ n, IsMarkovKernel (κ n)] (n : ℕ) (x : ∀ i : Finset.Iic n, X i) :
    partialTraj κ n (n + 1) x =
      (κ n x).map fun z => IicProdIoc n (n + 1) (x, MeasurableEquiv.piSingleton n z) := by
  rw [partialTraj_succ_self, Kernel.map_apply _ measurable_IicProdIoc, Kernel.prod_apply,
    Kernel.id_apply, Kernel.map_apply _ (MeasurableEquiv.piSingleton n).measurable,
    Measure.dirac_prod, Measure.map_map measurable_IicProdIoc (by fun_prop),
    Measure.map_map (by fun_prop) (MeasurableEquiv.piSingleton n).measurable]
  rfl

omit [DecidableEq ι] [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- One step of `partialTraj` along `stepKernel` agrees with the corresponding step of
`stepPMF`, glued on via `extendCoords`: the specialization of `partialTraj_succ_self_apply` to
the constant family `X n := G.StageOutcome`, with the `IicProdIoc`/`piSingleton` gluing
combinators unfolded to `extendCoords`'s concrete `if`-formula. -/
theorem stepKernel_partialTraj_succ_self (σ : G.BehaviorProfile) (n : ℕ)
    (x : ∀ _ : Finset.Iic n, G.StageOutcome) :
    partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) n (n + 1) x =
      ((G.stepPMF σ n x).map (G.extendCoords x)).toMeasure := by
  have hfg : (fun z : G.StageOutcome =>
      IicProdIoc (X := fun _ : ℕ => G.StageOutcome) n (n + 1)
        (x, MeasurableEquiv.piSingleton (X := fun _ : ℕ => G.StageOutcome) n z)) =
      G.extendCoords x := by
    funext z i
    simp only [IicProdIoc, MeasurableEquiv.piSingleton, MeasurableEquiv.coe_mk,
      Equiv.coe_fn_mk, extendCoords]
    by_cases h : i.1 ≤ n
    · simp [h]
    · have hi2 : i.1 ≤ n + 1 := Finset.mem_Iic.mp i.2
      have hi : (i : ℕ) = n + 1 := by omega
      have hi' : i = ⟨n + 1, Finset.mem_Iic.mpr (le_refl (n + 1))⟩ := Subtype.ext hi
      simp only [h, dif_neg, not_false_eq_true]
      subst hi'
      rfl
  have step := partialTraj_succ_self_apply (X := fun _ : ℕ => G.StageOutcome)
    (κ := G.stepKernel σ) n x
  rw [step, hfg,
    show (G.stepKernel σ n) x = (G.stepPMF σ n x).toMeasure from rfl,
    PMF.toMeasure_map (p := G.stepPMF σ n x) (hf := Measurable.of_discrete)]

/-- The `Iic 0`-indexed measure `Kernel.trajMeasure` starts from: `initialMeasure` transported
along `MeasurableEquiv.piUnique`'s inverse (a singleton-index gluing, needed only because
Ionescu-Tulcea's kernels start their trajectory at `Iic 0` rather than at a bare point). -/
def startMeasure (σ : G.BehaviorProfile) (s₀ : G.State) :
    Measure (∀ _ : Finset.Iic 0, G.StageOutcome) :=
  (G.initialMeasure σ s₀).map (MeasurableEquiv.piUnique
    (fun _ : Finset.Iic 0 => G.StageOutcome)).symm

omit [DecidableEq ι] [Fintype G.State] [DecidableEq G.State] [∀ i, Fintype (G.Act i)]
  [∀ i, DecidableEq (G.Act i)] in
/-- `startMeasure` is `initialMeasure` transported along the (trivial, single-coordinate)
gluing map, matching `coordsDist`'s own stage-`0` distribution. -/
theorem startMeasure_eq (σ : G.BehaviorProfile) (s₀ : G.State) :
    G.startMeasure σ s₀ = (G.initialMeasure σ s₀).map fun z (_ : Finset.Iic 0) => z := by
  have hfun : ⇑(MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => G.StageOutcome)).symm =
      fun z (_ : Finset.Iic 0) => z := by
    funext z i
    have hi : i = (default : Finset.Iic 0) := Subsingleton.elim i default
    subst hi
    rfl
  rw [startMeasure, hfun]

omit [DecidableEq ι] [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- **The key projective-family identity.** Binding `startMeasure` against `partialTraj`
along `stepKernel`, up to time `t`, agrees with `coordsDist σ s₀ t`'s measure: the
Ionescu-Tulcea recursion and the hand-rolled `coordsDist` recursion compute the same
distribution over the first `t + 1` stage outcomes. -/
theorem bind_partialTraj_eq_coordsDist_toMeasure (σ : G.BehaviorProfile) (s₀ : G.State)
    (t : ℕ) :
    Measure.bind (G.startMeasure σ s₀)
      (partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) 0 t) =
      (G.coordsDist σ s₀ t).toMeasure := by
  induction t with
  | zero =>
    rw [partialTraj_self]
    have : (⇑(Kernel.id (α := ∀ _ : Finset.Iic 0, G.StageOutcome))) = Measure.dirac := by
      funext x
      exact Kernel.id_apply x
    rw [this, Measure.bind_dirac, startMeasure_eq, initialMeasure,
      PMF.toMeasure_map (p := G.initialPMF σ s₀) (hf := Measurable.of_discrete)]
    rfl
  | succ t ih =>
    have heq : partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) 0 (t + 1) =
        partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) t (t + 1) ∘ₖ
          partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) 0 t :=
      partialTraj_succ_eq_comp (Nat.zero_le t)
    have hcomp : (⇑(partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) t (t + 1) ∘ₖ
        partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) 0 t)) =
        fun x => Measure.bind
          (partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) 0 t x)
          (partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) t (t + 1)) :=
      funext fun x => Kernel.comp_apply _ _ x
    rw [heq, hcomp,
      ← Measure.bind_bind (Kernel.measurable _).aemeasurable (Kernel.measurable _).aemeasurable,
      ih]
    have hfun : (⇑(partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) t (t + 1))) =
        fun x => ((G.stepPMF σ t x).map (G.extendCoords x)).toMeasure :=
      funext (G.stepKernel_partialTraj_succ_self σ t)
    rw [hfun, measureBind_toMeasure_eq, G.coordsDist_succ]

end ProjectiveFamily

section HistDistBridge

variable [Fintype G.State] [DecidableEq G.State] [∀ i, Fintype (G.Act i)]
  [∀ i, DecidableEq (G.Act i)]

/-- Rebuild a full `t + 1`-stage-outcome trajectory (indexed by `Finset.Iic t`) from the
`Hist t` it should read off via `histOfIic`, together with a chosen action `a` for stage `t`:
the earlier stage outcomes come from `h`'s record, and stage `t`'s outcome is `(h.2, a)` — the
current state of `h`, paired with `a`. This is the inverse direction of `histOfIic`, and is
what makes the joint distribution of `(histOfIic t x, x`'s own stage-`t` action`)` under
`coordsDist` line up with `histDist` plus one fresh action draw. -/
def reconstructCoords (t : ℕ) (h : G.Hist t) (a : G.JointAct) :
    ∀ _ : Finset.Iic t, G.StageOutcome :=
  fun k => if hk : k.1 < t then h.1 ⟨k.1, hk⟩ else (h.2, a)

omit [Fintype ι] [DecidableEq ι] [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
/-- `reconstructCoords` really does invert `histOfIic`, for any choice of the stage-`t`
action. -/
theorem histOfIic_reconstructCoords (t : ℕ) (h : G.Hist t) (a : G.JointAct) :
    G.histOfIic t (G.reconstructCoords t h a) = h := by
  unfold histOfIic reconstructCoords
  refine Prod.ext ?_ ?_
  · funext k
    simp
  · simp

omit [Fintype ι] [DecidableEq ι] [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
/-- Extending `reconstructCoords t h a` by one fresh state and action reproduces
`histOfCoords` at the record `Fin.snoc h.1 (h.2, a)`: this is the one-step compatibility
between `reconstructCoords`'s reindexing and `stepPMF`'s history-lookup. -/
theorem histOfCoords_reconstructCoords (t : ℕ) (h : G.Hist t) (a : G.JointAct)
    (s' : G.State) :
    G.histOfCoords (G.reconstructCoords t h a) s' = (Fin.snoc h.1 (h.2, a), s') := by
  unfold histOfCoords
  refine Prod.ext ?_ rfl
  funext k
  induction k using Fin.lastCases with
  | last => simp [reconstructCoords]
  | cast j => simp [reconstructCoords, j.2, Fin.snoc_castSucc]

omit [Fintype ι] [DecidableEq ι] [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
/-- `extendCoords` after `reconstructCoords` reproduces `reconstructCoords` one stage later,
at the record `Fin.snoc h.1 (h.2, a)` and the fresh action from `z`: the two "extend by one
stage" operations (Ionescu-Tulcea's `extendCoords` and `histDist`'s own record extension)
agree once reindexed through `reconstructCoords`. -/
theorem extendCoords_reconstructCoords (t : ℕ) (h : G.Hist t) (a : G.JointAct)
    (z : G.StageOutcome) :
    G.extendCoords (G.reconstructCoords t h a) z =
      G.reconstructCoords (t + 1) (Fin.snoc h.1 (h.2, a), z.1) z.2 := by
  funext k
  have hkle : k.1 ≤ t + 1 := Finset.mem_Iic.mp k.2
  simp only [extendCoords, reconstructCoords]
  rcases lt_trichotomy k.1 t with hlt | heq | hgt
  · have hcast : Fin.snoc (α := fun _ : Fin (t + 1) => G.StageOutcome) h.1 (h.2, a)
        (⟨k.1, by omega⟩ : Fin (t + 1)) = h.1 ⟨k.1, hlt⟩ := by
      have := Fin.snoc_castSucc (α := fun _ : Fin (t + 1) => G.StageOutcome) (p := h.1)
        (x := (h.2, a)) (i := (⟨k.1, hlt⟩ : Fin t))
      simpa [Fin.castSucc, Fin.castAdd, Fin.castLE] using this
    rw [dif_pos hlt.le, dif_pos hlt, dif_pos (show k.1 < t + 1 by omega), hcast]
  · have hcast : Fin.snoc (α := fun _ : Fin (t + 1) => G.StageOutcome) h.1 (h.2, a)
        (⟨k.1, by omega⟩ : Fin (t + 1)) = (h.2, a) := by
      have hlast : (⟨k.1, by omega⟩ : Fin (t + 1)) = Fin.last t := by
        ext; simpa using heq
      rw [hlast]
      exact Fin.snoc_last (α := fun _ : Fin (t + 1) => G.StageOutcome) (x := (h.2, a)) (p := h.1)
    have hle : k.1 ≤ t := heq.le
    have hnlt : ¬ k.1 < t := by omega
    have hlt1 : k.1 < t + 1 := by omega
    rw [dif_pos hle, dif_neg hnlt, dif_pos hlt1, hcast]
  · rw [dif_neg (by omega), dif_neg (by omega)]

omit [DecidableEq ι] [Fintype G.State] [DecidableEq G.State] [∀ i, Fintype (G.Act i)]
  [∀ i, DecidableEq (G.Act i)] in
/-- **`coordsDist` unfolds through `histDist` plus one fresh action draw.** The recursive
`coordsDist` family — which carries the action already decided for stage `t` — equals
`histDist t`'s distribution over histories, followed by drawing that stage-`t` action from
`σ` and reconstructing the full trajectory via `reconstructCoords`. -/
theorem coordsDist_eq_histDist_bind (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) :
    G.coordsDist σ s₀ t =
      (G.histDist σ s₀ t).bind fun h =>
        (G.stageActionDist σ h).map (G.reconstructCoords t h) := by
  induction t with
  | zero =>
    rw [histDist_zero, PMF.pure_bind]
    change (G.initialPMF σ s₀).map (fun z (_ : Finset.Iic 0) => z) = _
    unfold initialPMF
    rw [PMF.map_comp]
    have hfun : (fun z : G.StageOutcome => fun (_ : Finset.Iic 0) => z) ∘ (fun a => (s₀, a)) =
        G.reconstructCoords 0 (G.emptyHist s₀) := by
      funext a k
      simp [reconstructCoords, emptyHist]
    rw [hfun]
  | succ t ih =>
    rw [coordsDist_succ, ih, PMF.bind_bind, histDist_succ, PMF.bind_bind]
    have hstep : ∀ h : G.Hist t,
        ((G.stageActionDist σ h).map (G.reconstructCoords t h)).bind
            (fun x => (G.stepPMF σ t x).map (G.extendCoords x)) =
          ((G.stageActionDist σ h).bind fun a =>
            (G.transition h.2 a).bind fun s' =>
              PMF.pure (Fin.snoc h.1 (h.2, a), s')).bind
            (fun h' => (G.stageActionDist σ h').map (G.reconstructCoords (t + 1) h')) := by
      intro h
      rw [PMF.bind_map]
      change (G.stageActionDist σ h).bind
          (fun a => (G.stepPMF σ t (G.reconstructCoords t h a)).map
            (G.extendCoords (G.reconstructCoords t h a))) = _
      rw [PMF.bind_bind]
      congr 1
      funext a
      have hxt1 : (G.reconstructCoords t h a ⟨t, Finset.mem_Iic.mpr (le_refl t)⟩).1 = h.2 := by
        simp [reconstructCoords]
      have hxt2 : (G.reconstructCoords t h a ⟨t, Finset.mem_Iic.mpr (le_refl t)⟩).2 = a := by
        simp [reconstructCoords]
      change (G.stepPMF σ t (G.reconstructCoords t h a)).map
          (G.extendCoords (G.reconstructCoords t h a)) =
          ((G.transition h.2 a).bind fun s' => PMF.pure (Fin.snoc h.1 (h.2, a), s')).bind
            (fun h' => (G.stageActionDist σ h').map (G.reconstructCoords (t + 1) h'))
      unfold stepPMF
      rw [hxt1, hxt2, PMF.map_bind, PMF.bind_bind]
      congr 1
      funext s'
      rw [PMF.map_comp, G.histOfCoords_reconstructCoords, PMF.pure_bind]
      change (G.stageActionDist σ (Fin.snoc h.1 (h.2, a), s')).map
          ((G.extendCoords (G.reconstructCoords t h a)) ∘ (fun a' => (s', a'))) = _
      congr 1
      funext a'
      exact G.extendCoords_reconstructCoords t h a (s', a')
    congr 1
    funext h
    exact hstep h

omit [DecidableEq ι] [Fintype G.State] [DecidableEq G.State] [∀ i, Fintype (G.Act i)]
  [∀ i, DecidableEq (G.Act i)] in
/-- **The projection property, at the level of `coordsDist`.** Forgetting the extra
stage-`t` action `coordsDist` carries (via `histOfIic`) recovers `histDist` exactly. -/
theorem map_histOfIic_coordsDist (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) :
    PMF.map (G.histOfIic t) (G.coordsDist σ s₀ t) = G.histDist σ s₀ t := by
  rw [coordsDist_eq_histDist_bind, PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure (G.histDist σ s₀ t)]
  congr 1
  funext h
  rw [PMF.map_comp]
  change (G.stageActionDist σ h).map (fun a => G.histOfIic t (G.reconstructCoords t h a)) = _
  simp only [G.histOfIic_reconstructCoords]
  change (G.stageActionDist σ h).map (Function.const G.JointAct h) = _
  exact PMF.map_const (p := G.stageActionDist σ h) (b := h)

omit [Fintype ι] [DecidableEq ι] [Fintype G.State] [DecidableEq G.State]
  [∀ i, Fintype (G.Act i)] [∀ i, DecidableEq (G.Act i)] in
/-- `histOfPlay` factors through restricting a play to its first `t + 1` coordinates: read off
the same `Hist t` either directly from the play, or from its `Finset.Iic t`-indexed
restriction via `histOfIic`. -/
theorem histOfPlay_eq_histOfIic_frestrictLe (t : ℕ) (p : G.Play) :
    G.histOfPlay t p =
      G.histOfIic t (Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) t p) :=
  rfl

omit [DecidableEq ι] [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] [Fintype ι]
  [Fintype G.State] [∀ i, Fintype (G.Act i)] in
/-- `histOfPlay t` is measurable: it factors as the (discrete-domain, automatically measurable)
map `histOfIic t` composed with the (Ionescu-Tulcea-supplied) measurable restriction
`frestrictLe t`. Only finiteness (not the concrete `Fintype` data the surrounding section
otherwise needs) is required here. -/
theorem measurable_histOfPlay [Finite ι] [Finite G.State] [∀ i, Finite (G.Act i)] (t : ℕ) :
    Measurable (G.histOfPlay t) := by
  classical
  haveI : Fintype ι := Fintype.ofFinite ι
  haveI : Fintype G.State := Fintype.ofFinite G.State
  haveI : ∀ i, Fintype (G.Act i) := fun i => Fintype.ofFinite (G.Act i)
  have hfactor : G.histOfPlay t =
      G.histOfIic t ∘ Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) t := rfl
  rw [hfactor]
  exact Measurable.of_discrete.comp
    (Preorder.measurable_frestrictLe (X := fun _ : ℕ => G.StageOutcome) t)

omit [DecidableEq ι] [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- **The projection property.** The pushforward of `infinitePlayMeasure` along `histOfPlay t`
is `(histDist σ s₀ t).toMeasure`: `infinitePlayMeasure`'s finite-horizon marginals agree with
the existing finite-horizon history distribution `histDist` that `finiteAveragePayoff` is
built from. -/
theorem map_histOfPlay_infinitePlayMeasure (σ : G.BehaviorProfile) (s₀ : G.State) (t : ℕ) :
    (G.infinitePlayMeasure σ s₀).map (G.histOfPlay t) = (G.histDist σ s₀ t).toMeasure := by
  have hbind : G.infinitePlayMeasure σ s₀ =
      Measure.bind (G.startMeasure σ s₀)
        (traj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) 0) := rfl
  have hfrestrict : (G.infinitePlayMeasure σ s₀).map
      (Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) t) =
      (G.coordsDist σ s₀ t).toMeasure := by
    rw [hbind, bind_map_eq (Kernel.measurable _)
      (Preorder.measurable_frestrictLe (X := fun _ : ℕ => G.StageOutcome) t)]
    have hpt : (fun x => (traj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) 0 x).map
        (Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) t)) =
        partialTraj (X := fun _ : ℕ => G.StageOutcome) (G.stepKernel σ) 0 t :=
      funext fun x => traj_map_frestrictLe_apply (X := fun _ : ℕ => G.StageOutcome)
        (κ := G.stepKernel σ) 0 t x
    rw [hpt, G.bind_partialTraj_eq_coordsDist_toMeasure]
  calc (G.infinitePlayMeasure σ s₀).map (G.histOfPlay t)
      = (G.infinitePlayMeasure σ s₀).map
          (G.histOfIic t ∘ Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) t) := rfl
    _ = ((G.infinitePlayMeasure σ s₀).map
          (Preorder.frestrictLe (π := fun _ : ℕ => G.StageOutcome) t)).map (G.histOfIic t) := by
        rw [Measure.map_map Measurable.of_discrete
          (Preorder.measurable_frestrictLe (X := fun _ : ℕ => G.StageOutcome) t)]
    _ = ((G.coordsDist σ s₀ t).toMeasure).map (G.histOfIic t) := by rw [hfrestrict]
    _ = ((G.coordsDist σ s₀ t).map (G.histOfIic t)).toMeasure :=
        PMF.toMeasure_map (p := G.coordsDist σ s₀ t) (hf := Measurable.of_discrete)
    _ = (G.histDist σ s₀ t).toMeasure := by rw [G.map_histOfIic_coordsDist]

omit [DecidableEq ι] [DecidableEq G.State] [∀ i, DecidableEq (G.Act i)] in
/-- **Integrating a bounded function of the `Hist t` implicit in a play against
`infinitePlayMeasure` agrees with its `expect`-ation against `histDist`.** This transports the
projection property through integration, and is what lets `finiteAveragePayoff` be realized
pathwise by `infinitePlayMeasure`. -/
theorem integral_histOfPlay_infinitePlayMeasure (σ : G.BehaviorProfile) (s₀ : G.State)
    (t : ℕ) (f : G.Hist t → ℝ) :
    ∫ p, f (G.histOfPlay t p) ∂(G.infinitePlayMeasure σ s₀) =
      Math.Probability.expect (G.histDist σ s₀ t) f := by
  classical
  rw [← integral_map (G.measurable_histOfPlay t).aemeasurable
      Measurable.of_discrete.aestronglyMeasurable,
    G.map_histOfPlay_infinitePlayMeasure, PMF.integral_eq_sum, Math.Probability.expect_eq_sum]
  simp [smul_eq_mul]

end HistDistBridge

end StochasticGame

end GameTheory
