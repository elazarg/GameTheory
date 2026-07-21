/-
Copyright (c) 2025 GameTheory contributors. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: GameTheory contributors
-/
import GameTheory.Concepts.Repeated.MonitoringDiscounted

/-!
# Recursive Decomposition for Repeated Games with Public Monitoring

The Abreu--Pearce--Stacchetti (APS) decomposition of a normalized discounted
payoff into a current stage profile and public-signal-contingent continuation
payoffs.  The definitions in this file are independent of finiteness of the
signal type; admissible continuation assignments therefore carry an explicit
boundedness condition so that their countable expectations have the intended
meaning.

## Main definitions

* `PublicMonitoring.ContinuationAssignment`
* `PublicMonitoring.decomposedPayoff`
* `PublicMonitoring.IsPromiseKeeping`
* `PublicMonitoring.IsEnforceable`
* `PublicMonitoring.DecomposesOn`
* `PublicMonitoring.decompositionOperator`
* `PublicMonitoring.SelfGenerating`
-/

noncomputable section

namespace GameTheory

namespace KernelGame

namespace PublicMonitoring

variable {ι : Type} {G : KernelGame ι}

/-- A public continuation payoff vector assigned to every next-period public
signal. -/
abbrev ContinuationAssignment (M : G.PublicMonitoring) :=
  M.Signal → Payoff ι

/-- Coordinatewise boundedness of a continuation assignment.  This is
automatic for finite public-signal types. -/
def IsBoundedContinuationAssignment (M : G.PublicMonitoring)
    (w : M.ContinuationAssignment) : Prop :=
  ∀ who, ∃ C : ℝ, ∀ y, |w y who| ≤ C

/-- Every continuation assignment is bounded when the public-signal type is
finite. -/
theorem isBoundedContinuationAssignment_of_finite
    (M : G.PublicMonitoring) [Finite M.Signal]
    (w : M.ContinuationAssignment) :
    M.IsBoundedContinuationAssignment w := by
  intro who
  exact Math.Probability.exists_abs_bound_of_finite (fun y => w y who)

/-- The normalized discounted payoff promised by current play `a` and public
continuation assignment `w`. -/
def decomposedPayoff (M : G.PublicMonitoring) (δ : ℝ)
    (a : Profile G) (w : M.ContinuationAssignment) : Payoff ι :=
  fun who =>
    (1 - δ) * G.eu a who +
      δ * Math.Probability.expect (M.signalKernel a) (fun y => w y who)

/-- Payoff to `who` from a current unilateral deviation, retaining the same
public continuation assignment after the resulting signal. -/
def decomposedDeviationPayoff (M : G.PublicMonitoring) [DecidableEq ι]
    (δ : ℝ) (a : Profile G) (w : M.ContinuationAssignment)
    (who : ι) (dev : G.Strategy who) : ℝ :=
  let a' := Function.update a who dev
  (1 - δ) * G.eu a' who +
    δ * Math.Probability.expect (M.signalKernel a') (fun y => w y who)

/-- The current profile and continuation assignment deliver the promised
payoff vector. -/
def IsPromiseKeeping (M : G.PublicMonitoring) (δ : ℝ) (v : Payoff ι)
    (a : Profile G) (w : M.ContinuationAssignment) : Prop :=
  M.decomposedPayoff δ a w = v

/-- Every current unilateral deviation is deterred by the public continuation
assignment. -/
def IsEnforceable (M : G.PublicMonitoring) [DecidableEq ι]
    (δ : ℝ) (a : Profile G) (w : M.ContinuationAssignment) : Prop :=
  ∀ who (dev : G.Strategy who),
    M.decomposedDeviationPayoff δ a w who dev ≤
      M.decomposedPayoff δ a w who

/-- Payoff `v` decomposes on `W` if it is delivered and enforced by a current
profile whose bounded public continuation payoffs all lie in `W`. -/
def DecomposesOn (M : G.PublicMonitoring) [DecidableEq ι]
    (δ : ℝ) (W : Set (Payoff ι)) (v : Payoff ι) : Prop :=
  ∃ (a : Profile G) (w : M.ContinuationAssignment),
    M.IsBoundedContinuationAssignment w ∧
      (∀ y, w y ∈ W) ∧
      M.IsPromiseKeeping δ v a w ∧
      M.IsEnforceable δ a w

/-- The APS decomposition operator: all payoffs decomposable using
continuations in `W`. -/
def decompositionOperator (M : G.PublicMonitoring) [DecidableEq ι]
    (δ : ℝ) (W : Set (Payoff ι)) : Set (Payoff ι) :=
  {v | M.DecomposesOn δ W v}

/-- A payoff set is self-generating when each of its promises decomposes using
continuations from the same set. -/
def SelfGenerating (M : G.PublicMonitoring) [DecidableEq ι]
    (δ : ℝ) (W : Set (Payoff ι)) : Prop :=
  ∀ v ∈ W, M.DecomposesOn δ W v

@[simp] theorem mem_decompositionOperator_iff
    (M : G.PublicMonitoring) [DecidableEq ι]
    (δ : ℝ) (W : Set (Payoff ι)) (v : Payoff ι) :
    v ∈ M.decompositionOperator δ W ↔ M.DecomposesOn δ W v :=
  Iff.rfl

/-- The decomposition operator is monotone in the continuation set. -/
theorem decompositionOperator_mono
    (M : G.PublicMonitoring) [DecidableEq ι] (δ : ℝ) :
    Monotone (M.decompositionOperator δ) := by
  intro W W' hWW' v
  rintro ⟨a, w, hbounded, hw, hpromise, henforce⟩
  exact ⟨a, w, hbounded, fun y => hWW' (hw y), hpromise, henforce⟩

/-- Operator inclusion characterization of self-generation. -/
theorem selfGenerating_iff_subset_decompositionOperator
    (M : G.PublicMonitoring) [DecidableEq ι]
    (δ : ℝ) (W : Set (Payoff ι)) :
    M.SelfGenerating δ W ↔ W ⊆ M.decompositionOperator δ W :=
  Iff.rfl

@[simp] theorem selfGenerating_empty
    (M : G.PublicMonitoring) [DecidableEq ι] (δ : ℝ) :
    M.SelfGenerating δ (∅ : Set (Payoff ι)) := by
  simp [SelfGenerating]

/-- History-independent continuation at payoff vector `v`. -/
def constantContinuation (M : G.PublicMonitoring) (v : Payoff ι) :
    M.ContinuationAssignment :=
  fun _ => v

@[simp] theorem constantContinuation_apply
    (M : G.PublicMonitoring) (v : Payoff ι) (y : M.Signal) :
    M.constantContinuation v y = v :=
  rfl

theorem isBoundedContinuationAssignment_constant
    (M : G.PublicMonitoring) (v : Payoff ι) :
    M.IsBoundedContinuationAssignment (M.constantContinuation v) := by
  intro who
  exact ⟨|v who|, fun _ => le_rfl⟩

/-- Translate every public continuation payoff by the same payoff vector. -/
def translateContinuation (M : G.PublicMonitoring)
    (w : M.ContinuationAssignment) (v : Payoff ι) :
    M.ContinuationAssignment :=
  fun y who => w y who + v who

@[simp]
theorem translateContinuation_apply
    (M : G.PublicMonitoring) (w : M.ContinuationAssignment)
    (v : Payoff ι) (y : M.Signal) (who : ι) :
    M.translateContinuation w v y who = w y who + v who :=
  rfl

/-- Translating a bounded continuation assignment by a fixed payoff vector
preserves boundedness. -/
theorem IsBoundedContinuationAssignment.translate
    (M : G.PublicMonitoring) {w : M.ContinuationAssignment}
    (hw : M.IsBoundedContinuationAssignment w) (v : Payoff ι) :
    M.IsBoundedContinuationAssignment (M.translateContinuation w v) := by
  intro who
  obtain ⟨C, hC⟩ := hw who
  refine ⟨C + |v who|, fun y => ?_⟩
  calc
    |M.translateContinuation w v y who| ≤ |w y who| + |v who| :=
      abs_add_le _ _
    _ ≤ C + |v who| := add_le_add (hC y) le_rfl

/-- A signal-independent continuation translation shifts the prescribed
decomposed payoff by `delta` times the translation vector. -/
theorem decomposedPayoff_translateContinuation
    (M : G.PublicMonitoring) [Finite M.Signal]
    (delta : ℝ) (a : Profile G) (w : M.ContinuationAssignment)
    (v : Payoff ι) (who : ι) :
    M.decomposedPayoff delta a (M.translateContinuation w v) who =
      M.decomposedPayoff delta a w who + delta * v who := by
  simp only [decomposedPayoff, translateContinuation]
  rw [Math.Probability.expect_add]
  simp
  ring

/-- The same translation shifts every unilateral-deviation decomposed payoff
by exactly the same amount. -/
theorem decomposedDeviationPayoff_translateContinuation
    (M : G.PublicMonitoring) [DecidableEq ι] [Finite M.Signal]
    (delta : ℝ) (a : Profile G) (w : M.ContinuationAssignment)
    (v : Payoff ι) (who : ι) (dev : G.Strategy who) :
    M.decomposedDeviationPayoff delta a (M.translateContinuation w v)
        who dev =
      M.decomposedDeviationPayoff delta a w who dev + delta * v who := by
  simp only [decomposedDeviationPayoff, translateContinuation]
  rw [Math.Probability.expect_add]
  simp
  ring

/-- Signal-independent continuation translations preserve and reflect APS
enforceability. -/
theorem isEnforceable_translateContinuation_iff
    (M : G.PublicMonitoring) [DecidableEq ι] [Finite M.Signal]
    (delta : ℝ) (a : Profile G) (w : M.ContinuationAssignment)
    (v : Payoff ι) :
    M.IsEnforceable delta a (M.translateContinuation w v) ↔
      M.IsEnforceable delta a w := by
  simp only [IsEnforceable,
    M.decomposedDeviationPayoff_translateContinuation,
    M.decomposedPayoff_translateContinuation, add_le_add_iff_right]

/-- Decomposition with a constant continuation has the expected affine
form. -/
@[simp] theorem decomposedPayoff_constant
    (M : G.PublicMonitoring) (δ : ℝ) (a : Profile G) (v : Payoff ι)
    (who : ι) :
    M.decomposedPayoff δ a (M.constantContinuation v) who =
      (1 - δ) * G.eu a who + δ * v who := by
  simp [decomposedPayoff, constantContinuation]

@[simp] theorem decomposedDeviationPayoff_constant
    (M : G.PublicMonitoring) [DecidableEq ι]
    (δ : ℝ) (a : Profile G) (v : Payoff ι)
    (who : ι) (dev : G.Strategy who) :
    M.decomposedDeviationPayoff δ a (M.constantContinuation v) who dev =
      (1 - δ) * G.eu (Function.update a who dev) who + δ * v who := by
  simp [decomposedDeviationPayoff, constantContinuation]

/-- Repeating the current expected-utility vector as the continuation promise
keeps that promise for every discount factor. -/
theorem isPromiseKeeping_constant_eu
    (M : G.PublicMonitoring) (δ : ℝ) (a : Profile G) :
    M.IsPromiseKeeping δ (fun who => G.eu a who) a
      (M.constantContinuation fun who => G.eu a who) := by
  funext who
  simp
  ring

/-- Constant continuation payoffs enforce exactly the stage Nash profiles
when `δ < 1`; the monitoring law cancels from every incentive comparison. -/
theorem isEnforceable_constant_iff_isNash
    (M : G.PublicMonitoring) [DecidableEq ι]
    {δ : ℝ} (hδ1 : δ < 1) (a : Profile G) (v : Payoff ι) :
    M.IsEnforceable δ a (M.constantContinuation v) ↔ G.IsNash a := by
  constructor
  · intro h who dev
    have hdev := h who dev
    simp only [decomposedDeviationPayoff_constant,
      decomposedPayoff_constant] at hdev
    nlinarith
  · intro h who dev
    simp only [decomposedDeviationPayoff_constant,
      decomposedPayoff_constant]
    have hdev := h who dev
    nlinarith

/-- A stage Nash payoff decomposes on its singleton by stationary play. -/
theorem decomposesOn_singleton_eu_of_isNash
    (M : G.PublicMonitoring) [DecidableEq ι]
    {δ : ℝ} (hδ1 : δ < 1) {a : Profile G} (hN : G.IsNash a) :
    M.DecomposesOn δ ({fun who => G.eu a who} : Set (Payoff ι))
      (fun who => G.eu a who) := by
  let v : Payoff ι := fun who => G.eu a who
  refine ⟨a, M.constantContinuation v,
    M.isBoundedContinuationAssignment_constant v, ?_, ?_, ?_⟩
  · intro y
    simp [v]
  · exact M.isPromiseKeeping_constant_eu δ a
  · exact (M.isEnforceable_constant_iff_isNash hδ1 a v).2 hN

/-- Every singleton stage-Nash payoff is a self-generating set. -/
theorem selfGenerating_singleton_eu_of_isNash
    (M : G.PublicMonitoring) [DecidableEq ι]
    {δ : ℝ} (hδ1 : δ < 1) {a : Profile G} (hN : G.IsNash a) :
    M.SelfGenerating δ ({fun who => G.eu a who} : Set (Payoff ι)) := by
  intro v hv
  simpa only [Set.mem_singleton_iff.mp hv] using
    M.decomposesOn_singleton_eu_of_isNash hδ1 hN

end PublicMonitoring

end KernelGame

end GameTheory
