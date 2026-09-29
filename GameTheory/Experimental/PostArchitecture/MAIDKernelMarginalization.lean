/-
# Experimental kernel marginalization for MAID information removal

Given a law of full observation contexts and an action kernel that may inspect
the whole context, average that kernel over the conditional law of full
contexts at each kept observation.  The resulting kernel sees only the kept
observation and preserves the joint law of kept observations and actions.

This is the constructive probability step needed by local MAID information
removal.  It is not yet a graph theorem: d-separation must still justify that
the owner's continuation utility depends on the full context only through the
kept observation and chosen action.
-/

import GameTheory.Math.Probability.Conditioning
import GameTheory.Math.Probability.ExpectationBind
import GameTheory.Math.Probability.ExpectationMixture

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDKernelMarginalization

open GameTheory.Math.Probability

universe uContext uKept uAction

variable {Context : Type uContext} {Kept : Type uKept}
variable {Action : Type uAction}

/-- The actual fiber posterior on positive kept observations. Null fibers use
the source law as a total fallback, which is never charged by the marginal. -/
private def conditionedContext (contextLaw : PMF Context) (keep : Context → Kept)
    (kept : Kept) : PMF Context :=
  fiberPosterior contextLaw keep kept

/-- Average a full-context action kernel over the actual fiber posterior. -/
def averagedKernel (contextLaw : PMF Context) (keep : Context → Kept)
    (kernel : Context → PMF Action) (kept : Kept) : PMF Action :=
  (conditionedContext contextLaw keep kept).bind kernel

/-- The joint experiment using the original full-context kernel. -/
def fullJoint (contextLaw : PMF Context) (keep : Context → Kept)
    (kernel : Context → PMF Action) : PMF (Kept × Action) :=
  contextLaw.bind fun context =>
    (kernel context).map fun action => (keep context, action)

/-- The joint experiment after replacing the kernel by its kept-context
average. -/
def averagedJoint (contextLaw : PMF Context) (keep : Context → Kept)
    (kernel : Context → PMF Action) : PMF (Kept × Action) :=
  (contextLaw.map keep).bind fun kept =>
    (averagedKernel contextLaw keep kernel kept).map fun action =>
      (kept, action)

/-- Marginalizing the removed part of a context preserves the exact joint law
of the kept context and action. -/
theorem fullJoint_eq_averagedJoint (contextLaw : PMF Context)
    (keep : Context → Kept) (kernel : Context → PMF Action) :
    fullJoint contextLaw keep kernel =
      averagedJoint contextLaw keep kernel := by
  classical
  have hdecompose :
      (contextLaw.map keep).bind
        (conditionedContext contextLaw keep) = contextLaw := by
    exact fiberPosterior_reconstruct contextLaw keep
  calc
    fullJoint contextLaw keep kernel =
        (contextLaw.map keep).bind fun kept =>
          (conditionedContext contextLaw keep kept).bind fun context =>
            (kernel context).map fun action =>
              (keep context, action) := by
      unfold fullJoint
      conv_lhs => rw [← hdecompose, PMF.bind_bind]
    _ = (contextLaw.map keep).bind fun kept =>
          (conditionedContext contextLaw keep kept).bind fun context =>
            (kernel context).map fun action => (kept, action) := by
      apply bind_congr_on_support
      intro kept hkept
      apply bind_congr_on_support
      intro context hcontext
      have hcontextFibre :
          context ∈ {value | keep value = kept} ∩ contextLaw.support := by
        simpa only [conditionedContext, fiberPosterior_support _ _ _ hkept] using hcontext
      have hkeep : keep context = kept := hcontextFibre.1
      rw [hkeep]
    _ = averagedJoint contextLaw keep kernel := by
      unfold averagedJoint averagedKernel
      apply bind_congr_on_support
      intro kept _
      rw [PMF.map_bind]

/-- The averaged kept-context kernel may be expanded back to a full-context
kernel without changing the kept-context/action joint law. -/
theorem fullJoint_eq_fullJoint_averagedKernel
    (contextLaw : PMF Context) (keep : Context → Kept)
    (kernel : Context → PMF Action) :
    fullJoint contextLaw keep kernel =
      fullJoint contextLaw keep (fun context =>
        averagedKernel contextLaw keep kernel (keep context)) := by
  rw [fullJoint_eq_averagedJoint]
  unfold averagedJoint fullJoint
  rw [PMF.bind_map]
  rfl

/-- Exact joint-law equality transports every observable's expectation. -/
theorem expect_fullJoint_eq_averagedJoint (contextLaw : PMF Context)
    (keep : Context → Kept) (kernel : Context → PMF Action)
    (observable : Kept × Action → ℝ) :
    expect (fullJoint contextLaw keep kernel) observable =
      expect (averagedJoint contextLaw keep kernel) observable :=
  expect_congr_law (fullJoint_eq_averagedJoint contextLaw keep kernel)
    observable

/-- The same statement for a continuation value on kept context and action. -/
theorem expect_kernel_eq_averagedKernel (contextLaw : PMF Context)
    (keep : Context → Kept) (kernel : Context → PMF Action)
    (continuationValue : Kept → Action → ℝ) :
    expect (fullJoint contextLaw keep kernel)
        (fun pair => continuationValue pair.1 pair.2) =
      expect (averagedJoint contextLaw keep kernel)
        (fun pair => continuationValue pair.1 pair.2) :=
  expect_fullJoint_eq_averagedJoint contextLaw keep kernel _

/-- A kept-rule's actual joint law. -/
def keptJoint (contextLaw : PMF Context) (keep : Context → Kept)
    (kernel : Kept → PMF Action) : PMF (Kept × Action) :=
  (contextLaw.map keep).bind fun kept =>
    (kernel kept).map fun action => (kept, action)

/-- A shared continuation value and guards for the actual family of full and
kept rules compared by local information removal. -/
structure ContinuationFactorsThrough (contextLaw : PMF Context)
    (keep : Context → Kept)
    (fullValue : (Context → PMF Action) → ℝ)
    (keptValue : (Kept → PMF Action) → ℝ) where
  continuationValue : Kept → Action → ℝ
  fullGuard : ∀ kernel, PayoffIntegrable (fullJoint contextLaw keep kernel)
    (fun pair => continuationValue pair.1 pair.2)
  keptGuard : ∀ kernel, PayoffIntegrable (keptJoint contextLaw keep kernel)
    (fun pair => continuationValue pair.1 pair.2)
  full_eq : ∀ kernel,
    fullValue kernel = expect (fullJoint contextLaw keep kernel)
      (fun pair => continuationValue pair.1 pair.2)
  kept_eq : ∀ kernel,
    keptValue kernel = expect (keptJoint contextLaw keep kernel)
      (fun pair => continuationValue pair.1 pair.2)

/-- The conditional average covers every full-context rule's actual value. -/
theorem exists_keptRule_value_eq_of_continuationFactorsThrough
    (contextLaw : PMF Context) (keep : Context → Kept)
    (fullValue : (Context → PMF Action) → ℝ)
    (keptValue : (Kept → PMF Action) → ℝ)
    (hfactor : ContinuationFactorsThrough contextLaw keep fullValue keptValue)
    (fullRule : Context → PMF Action) :
    ∃ keptRule : Kept → PMF Action,
      fullValue fullRule = keptValue keptRule := by
  let keptRule := averagedKernel contextLaw keep fullRule
  refine ⟨keptRule, ?_⟩
  rw [hfactor.full_eq, hfactor.kept_eq]
  exact expect_congr_law
    (fullJoint_eq_averagedJoint contextLaw keep fullRule)
    (fun pair => hfactor.continuationValue pair.1 pair.2)


/-! ## Fair-signal control -/

def fairSignal : PMF Bool :=
  mix (1 / 2) (by norm_num) (by norm_num)
    (PMF.pure false) (PMF.pure true)

def copySignal (signal : Bool) : PMF Bool := PMF.pure signal

def fullActionValue (kernel : Bool → PMF Bool) : ℝ :=
  expect (fullJoint fairSignal (fun _ : Bool => ()) kernel)
    (fun pair => if pair.2 then 1 else 0)

def keptActionValue (kernel : Unit → PMF Bool) : ℝ :=
  expect (keptJoint fairSignal (fun _ : Bool => ()) kernel)
    (fun pair => if pair.2 then 1 else 0)

/-- Both finite-control evaluators use the same guarded joint observable. -/
def actionValueFactors : ContinuationFactorsThrough fairSignal
    (fun _ : Bool => ()) fullActionValue keptActionValue where
  continuationValue _ action := if action then 1 else 0
  fullGuard _ := payoffIntegrable_of_bounded _ _ (C := 1) (by
    intro pair
    cases pair.2 <;> norm_num)
  keptGuard _ := payoffIntegrable_of_bounded _ _ (C := 1) (by
    intro pair
    cases pair.2 <;> norm_num)
  full_eq _ := rfl
  kept_eq _ := rfl

theorem copySignal_reads_context : copySignal false ≠ copySignal true := by
  intro hequal
  have hfalse := congrArg (fun law : PMF Bool => law false) hequal
  norm_num [copySignal, PMF.pure_apply] at hfalse

/-- Averaging the copying rule after forgetting the signal gives its fair law. -/
theorem averagedKernel_copySignal :
    averagedKernel fairSignal (fun _ : Bool => ()) copySignal () =
      fairSignal := by
  unfold averagedKernel conditionedContext
  have hsupport : () ∈ (fairSignal.map fun _ : Bool => ()).support := by
    simp
  have hposterior : fiberPosterior fairSignal (fun _ : Bool => ()) () = fairSignal := by
    rw [fiberPosterior_of_mem_support _ _ hsupport]
    apply filter_of_support_subset
    intro signal _
    simp
  rw [hposterior]
  exact PMF.bind_pure fairSignal

theorem copySignal_joint_preserved :
    fullJoint fairSignal (fun _ : Bool => ()) copySignal =
      averagedJoint fairSignal (fun _ : Bool => ()) copySignal :=
  fullJoint_eq_averagedJoint fairSignal (fun _ => ()) copySignal

theorem exists_keptRule_copySignal_value_eq :
    ∃ keptRule : Unit → PMF Bool,
      fullActionValue copySignal = keptActionValue keptRule :=
  exists_keptRule_value_eq_of_continuationFactorsThrough
    fairSignal (fun _ => ()) fullActionValue keptActionValue
      actionValueFactors copySignal

end GameTheory.Experimental.PostArchitecture.MAIDKernelMarginalization
