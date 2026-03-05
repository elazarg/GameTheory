import Math.PMFProduct
import Math.ProbabilityMassFunction
import GameTheory.Model.SemanticForm

/-!
# Kuhn at the InfoModel Layer

Language-agnostic outcome-distribution form of Kuhn's theorem over
`LSM` + `InfoModel` + `Execution.Dynamics`.
-/

namespace GameTheory
namespace Theorems

open Math
open Math.PMFProduct

/-- Generic behavioral -> mixed outcome-equality schema. -/
def KuhnBehavioralToMixedOutcome
    (Behavioral Pure Outcome : Type)
    (mixedOfBehavioral : Behavioral → PMF Pure)
    (evalBehavioral : Behavioral → PMF Outcome)
    (evalPure : Pure → PMF Outcome) : Prop :=
  ∀ σ : Behavioral, (mixedOfBehavioral σ).bind evalPure = evalBehavioral σ

/-- Generic mixed -> behavioral realization schema. -/
def KuhnMixedToBehavioralViaOutcome
    (Behavioral Mixed Pure Outcome : Type)
    (joint : Mixed → PMF Pure)
    (evalBehavioral : Behavioral → PMF Outcome)
    (evalPure : Pure → PMF Outcome) : Prop :=
  ∀ μ : Mixed, ∃ σ : Behavioral, evalBehavioral σ = (joint μ).bind evalPure

/-- Complete Kuhn statement (both directions) at outcome-distribution level. -/
def KuhnCompleteViaOutcome
    (Behavioral Mixed Pure Outcome : Type)
    (mixedOfBehavioral : Behavioral → PMF Pure)
    (joint : Mixed → PMF Pure)
    (evalBehavioral : Behavioral → PMF Outcome)
    (evalPure : Pure → PMF Outcome) : Prop :=
  (∀ σ : Behavioral, (mixedOfBehavioral σ).bind evalPure = evalBehavioral σ) ∧
  (∀ μ : Mixed, ∃ σ : Behavioral, evalBehavioral σ = (joint μ).bind evalPure)

section BehavioralToMixed

variable {ι : Type} [Fintype ι]
variable {A : ι → Type} [∀ i, Fintype (A i)]
variable {β γ : Type} [Finite β]

open Classical in
theorem kuhn_behavioral_to_mixed_indep
    (σ : ∀ i, PMF (A i))
    (f : (∀ i, A i) → PMF β)
    (g : β → (∀ i, A i) → PMF γ)
    (J : Finset ι)
    (hf : ∀ j, j ∉ J → Ignores j f)
    (hg : ∀ j, j ∈ J → ∀ b, Ignores j (g b)) :
    (pmfPi σ).bind (fun s => (f s).bind (fun b => g b s)) =
    (pmfPi σ).bind (fun s => (f s).bind (fun b => (pmfPi σ).bind (fun t => g b t))) :=
  pmfPi_bind_indep (σ := σ) (f := f) (g := g) (J := J) hf hg

end BehavioralToMixed

section MixedToBehavioral

variable {α β γ : Type} [Fintype α] [Finite β]

theorem kuhn_mixed_to_behavioral_disintegrate
    (μ : PMF α) (proj : α → β) (g : α → PMF γ) :
    μ.bind g =
      (Math.ProbabilityMassFunction.pushforward μ proj).bind
        (fun b => (Math.ProbabilityMassFunction.condOn μ proj b).bind g) := by
  classical
  letI : Fintype β := Fintype.ofFinite β
  simpa using
    (Math.ProbabilityMassFunction.bind_pushforward_condOn (μ := μ) (proj := proj) (g := g))

end MixedToBehavioral

section InfoModel

open Execution
open Execution.Dynamics

variable {ι : Type} [Fintype ι]
variable {M : LSM ι} (I : InfoModel M)
variable (D : Execution.Dynamics I)
variable [∀ i, Fintype (Option (M.Act i))]
variable (k : Nat)

/-- Mixed profiles over pure policies for an `InfoModel`. -/
abbrev MixedProfile : Type := PMF (PureProfile I)

/-- Outcome evaluation of a mixed profile (sample pure profile, then evaluate). -/
noncomputable def evalMixed (μ : MixedProfile (I := I)) : PMF I.Outcome :=
  μ.bind (D.evalPure k)

/-- Identity joint map for `MixedProfile := PMF PureProfile`. -/
def mixedJoint (μ : MixedProfile (I := I)) : PMF (PureProfile I) := μ

abbrev LocalPure (i : ι) : Type :=
  M.Label → Execution.View I i → Option (M.Act i)

noncomputable def localMixedOfBehavioralCanonical
    [Fintype M.Label] [∀ i, Fintype (Execution.View I i)]
    (σ : BehavioralProfile I) (i : ι) : PMF (LocalPure (I := I) i) := by
  classical
  let μ : PMF (M.Label × Execution.View I i → Option (M.Act i)) :=
    pmfPi (fun p : M.Label × Execution.View I i => σ i p.1 p.2)
  exact PMF.map (Equiv.curry _ _ _) μ

/-- Canonical behavioral -> mixed map on `PureProfile`. -/
noncomputable def mixedOfBehavioralCanonical
    [Fintype M.Label] [∀ i, Fintype (Execution.View I i)]
    (σ : BehavioralProfile I) : PMF (PureProfile I) := by
  classical
  change PMF (∀ i, LocalPure (I := I) i)
  exact pmfPi (fun i => localMixedOfBehavioralCanonical (I := I) σ i)

/-- Canonical mixed evaluation for `InfoModel`. -/
noncomputable def evalMixedCanonical (μ : MixedProfile (I := I)) : PMF I.Outcome :=
  μ.bind (D.evalPure k)

theorem kuhn_behavioral_side_of_infoModel_axiomatic
    (mixedOfBehavioral : BehavioralProfile I → PMF (PureProfile I))
    (hB2M : ∀ σ : BehavioralProfile I,
      D.evalBehavioral k σ = evalMixed (I := I) (D := D) k (mixedOfBehavioral σ)) :
    KuhnBehavioralToMixedOutcome
      (BehavioralProfile I) (PureProfile I) I.Outcome
      mixedOfBehavioral (D.evalBehavioral k) (D.evalPure k) := by
  intro σ
  simpa [evalMixed] using (hB2M σ).symm

theorem kuhn_mixed_side_of_infoModel_axiomatic
    (realizeBehavioral : MixedProfile (I := I) → BehavioralProfile I)
    (hM2B : ∀ μ : MixedProfile (I := I),
      D.evalBehavioral k (realizeBehavioral μ) = evalMixed (I := I) (D := D) k μ) :
    KuhnMixedToBehavioralViaOutcome
      (BehavioralProfile I) (MixedProfile (I := I)) (PureProfile I) I.Outcome
      (mixedJoint (I := I)) (D.evalBehavioral k) (D.evalPure k) := by
  intro μ
  exact ⟨realizeBehavioral μ, by simpa [evalMixed, mixedJoint] using hM2B μ⟩

/-- Axiomatic assembly theorem (kept as a helper during the constructive proof
refactor). -/
theorem kuhn_complete_of_infoModel_axiomatic
    (mixedOfBehavioral : BehavioralProfile I → PMF (PureProfile I))
    (realizeBehavioral : MixedProfile (I := I) → BehavioralProfile I)
    (hB2M : ∀ σ : BehavioralProfile I,
      D.evalBehavioral k σ = evalMixed (I := I) (D := D) k (mixedOfBehavioral σ))
    (hM2B : ∀ μ : MixedProfile (I := I),
      D.evalBehavioral k (realizeBehavioral μ) = evalMixed (I := I) (D := D) k μ) :
    KuhnCompleteViaOutcome
      (BehavioralProfile I) (MixedProfile (I := I)) (PureProfile I) I.Outcome
      mixedOfBehavioral (mixedJoint (I := I)) (D.evalBehavioral k) (D.evalPure k) := by
  refine ⟨?_, ?_⟩
  · exact kuhn_behavioral_side_of_infoModel_axiomatic
      (I := I) (D := D) (k := k) mixedOfBehavioral hB2M
  · exact kuhn_mixed_side_of_infoModel_axiomatic
      (I := I) (D := D) (k := k) realizeBehavioral hM2B

/-! ## ProtoKuhn Port Skeleton (InfoModel)

This subsection mirrors the substantive proof phases in `ProtoKuhn.lean.txt`,
but directly over `InfoModel + Execution`.
-/

section ProtoPort

open Execution
open Execution.Dynamics

/-!
Port map to `ProtoKuhn.lean.txt`:
- `runDist_zero`, `runDist_succ`: eval decomposition (`evalRoundsMixed_nil/cons` analog).
- `behavioral_to_mixed_oneLayer_factor`: `independent_factor` analog at execution-layer.
- `behavioral_to_mixed_reduce_to_factorization`: behavioral->mixed induction shell.
- `pureActionAt`, `mixed_disintegrate_oneCoordinate`: `bind_marginal_cond`/disintegration analog.
- `realizeBehavioralCanonical`: `mixedToBehavioralRoot` analog (semantic form).
- `realizeBehavioralCanonical_correct`: mixed->behavioral main induction shell.
- `kuhn_*_core_port`, `kuhn_complete_of_infoModel`: assembled final theorem.

Transport omitted intentionally:
- flat/pure profile encoding bridges specific to EFG/Proto syntax.
- syntax-level path/tree constructors replaced by `Execution`/`InfoModel`.
-/

/-- Execution unfolding: base case for bounded runs. -/
@[simp] theorem runDist_zero
    [Fintype M.Label]
    [∀ i, Fintype (Option (M.Act i))]
    (σ : BehavioralProfile I) :
    D.runDist 0 σ = PMF.pure ([], M.init) := rfl

/-- Execution unfolding: one-step recursion for bounded runs. -/
@[simp] theorem runDist_succ
    [Fintype M.Label]
    [∀ i, Fintype (Option (M.Act i))]
    (n : Nat) (σ : BehavioralProfile I) :
    D.runDist (n + 1) σ =
      (D.runDist n σ).bind (fun hs =>
        Math.ProbabilityMassFunction.pushforward (D.stepDist σ hs.2)
          (fun ls => (hs.1 ++ [ls.1], ls.2))) := rfl

/-- Canonical mixed evaluator is definitionally the mixed bind evaluator. -/
@[simp] theorem evalMixedCanonical_eq_evalMixed
    (μ : MixedProfile (I := I)) :
    evalMixedCanonical (I := I) (D := D) (k := k) μ = evalMixed (I := I) (D := D) k μ := rfl

/-- Canonical behavioral-to-mixed map is the product over controller-local
pure-policy laws. This is the semantic analogue of ProtoKuhn's product profile. -/
theorem mixedOfBehavioralCanonical_def
    [Fintype M.Label] [∀ i, Fintype (Execution.View I i)]
    (σ : BehavioralProfile I) :
    mixedOfBehavioralCanonical (I := I) σ =
      pmfPi (fun i => localMixedOfBehavioralCanonical (I := I) σ i) := by
  rfl

/-- Proto step (behavioral->mixed): local independence factorization on one
execution layer. This is where the transition-level "ignores fresh coordinates"
lemma must be supplied from perfect recall + step-locality. -/
theorem behavioral_to_mixed_oneLayer_factor
    [Fintype M.Label] [∀ i, Fintype (Execution.View I i)]
    (hPR : I.PerfectRecall)
    (σ : BehavioralProfile I) :
    True := by
  -- Missing deep ingredient:
  -- an `Ignores` statement for continuation kernels under the canonical sampled
  -- pure-policy product, analogous to ProtoKuhn's `independent_factor`.
  -- This requires a semantic "no local information-state revisit along run"
  -- consequence extracted from `hPR`.
  trivial

/-- Proto step (behavioral->mixed): reduce full theorem to layered factorization. -/
theorem behavioral_to_mixed_reduce_to_factorization
    [Fintype M.Label] [∀ i, Fintype (Execution.View I i)]
    (hPR : I.PerfectRecall) :
    KuhnBehavioralToMixedOutcome
      (BehavioralProfile I) (PureProfile I) I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (D.evalBehavioral k) (D.evalPure k) := by
  -- Missing deep proof:
  -- induction on horizon `k`, using `runDist_succ`, `pmfPi_bind_indep`, and
  -- `behavioral_to_mixed_oneLayer_factor`.
  -- This is the direct semantic port of ProtoKuhn behavioral->mixed induction.
  sorry

/-- Conditioning object for mixed->behavioral: controller-local action view.
Used as the projection for disintegration on pure policies. -/
def pureActionAt (i : ι) (ℓ : M.Label) (v : Execution.View I i)
    (π : PureProfile I) : Option (M.Act i) :=
  π i ℓ v

/-- Proto step (mixed->behavioral): disintegrate mixed evaluation at a single
controller-local decision coordinate. -/
theorem mixed_disintegrate_oneCoordinate
    [Fintype M.Label] [∀ i, Fintype (Execution.View I i)]
    (μ : MixedProfile (I := I)) (i : ι) (ℓ : M.Label) (v : Execution.View I i) :
    evalMixedCanonical (I := I) (D := D) (k := k) μ =
      (Math.ProbabilityMassFunction.pushforward μ (pureActionAt (I := I) i ℓ v)).bind
        (fun a =>
          evalMixedCanonical (I := I) (D := D) (k := k)
            (Math.ProbabilityMassFunction.condOn μ (pureActionAt (I := I) i ℓ v) a)) := by
  simpa [evalMixedCanonical, pureActionAt] using
    (kuhn_mixed_to_behavioral_disintegrate
      (μ := μ) (proj := pureActionAt (I := I) i ℓ v) (g := D.evalPure k))

/-- Canonical realization candidate for mixed->behavioral.
This is intentionally left abstract until the semantic "history/context"
selection mechanism is fixed in `Execution` (reachable local contexts). -/
noncomputable def realizeBehavioralCanonical
    [Fintype M.Label] [∀ i, Fintype (Execution.View I i)]
    (_hPR : I.PerfectRecall)
    (_μ : MixedProfile (I := I)) : BehavioralProfile I := by
  -- Missing structure:
  -- a canonical map from current execution context to the conditioning event
  -- in pure-policy space (semantic analogue of ProtoKuhn's path/history filter).
  classical
  exact fun i _ℓ _v => PMF.pure (none)

/-- Proto step (mixed->behavioral): correctness of canonical realization.
This is the substantive disintegration + conditioning induction port. -/
theorem realizeBehavioralCanonical_correct
    [Fintype M.Label] [∀ i, Fintype (Execution.View I i)]
    (hPR : I.PerfectRecall) (μ : MixedProfile (I := I)) :
    D.evalBehavioral k (realizeBehavioralCanonical (I := I) (hPR := hPR) μ) =
      evalMixedCanonical (I := I) (D := D) (k := k) μ := by
  -- Missing deep proof:
  -- 1. define context-indexed conditioning events from semantic reachable traces,
  -- 2. prove commutation/invariance lemmas (ProtoKuhn `muCondPath` family),
  -- 3. prove subtree/run induction for equality of outcome distributions.
  --
  -- Not omitted as "transport": this is the genuine mixed->behavioral core.
  sorry

/-- Behavioral -> mixed core now reduced to semantic factorization work only. -/
theorem kuhn_behavioral_to_mixed_core_port
    [Fintype M.Label] [∀ i, Fintype (Execution.View I i)]
    (hPR : I.PerfectRecall) :
    KuhnBehavioralToMixedOutcome
      (BehavioralProfile I) (PureProfile I) I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (D.evalBehavioral k) (D.evalPure k) := by
  exact behavioral_to_mixed_reduce_to_factorization (I := I) (D := D) (k := k) hPR

/-- Mixed -> behavioral core with canonical realization target. -/
theorem kuhn_mixed_to_behavioral_core_port
    [Fintype M.Label] [∀ i, Fintype (Execution.View I i)]
    (hPR : I.PerfectRecall) :
    KuhnMixedToBehavioralViaOutcome
      (BehavioralProfile I) (MixedProfile (I := I)) (PureProfile I) I.Outcome
      (fun μ => μ) (D.evalBehavioral k) (D.evalPure k) := by
  intro μ
  refine ⟨realizeBehavioralCanonical (I := I) (hPR := hPR) μ, ?_⟩
  simpa [evalMixedCanonical_eq_evalMixed (I := I) (D := D) (k := k) μ] using
    realizeBehavioralCanonical_correct (I := I) (D := D) (k := k) hPR μ

/-- Kuhn on `InfoModel` with no theorem-local behavioral/mixed obligations.
Only model assumptions remain (finiteness + perfect recall). -/
theorem kuhn_complete_of_infoModel
    [Fintype M.Label] [∀ i, Fintype (Execution.View I i)]
    (hPR : I.PerfectRecall) :
    KuhnCompleteViaOutcome
      (BehavioralProfile I) (MixedProfile (I := I)) (PureProfile I) I.Outcome
      (mixedOfBehavioralCanonical (I := I))
      (fun μ => μ)
      (D.evalBehavioral k) (D.evalPure k) := by
  exact ⟨kuhn_behavioral_to_mixed_core_port (I := I) (D := D) (k := k) hPR,
    kuhn_mixed_to_behavioral_core_port (I := I) (D := D) (k := k) hPR⟩

end ProtoPort

end Theorems
end GameTheory
