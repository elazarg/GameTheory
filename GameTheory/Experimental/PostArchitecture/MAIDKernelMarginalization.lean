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

import GameTheory.Math.Probability.FinDist

noncomputable section

namespace GameTheory.Experimental.PostArchitecture.MAIDKernelMarginalization

open GameTheory.Math.Probability

universe uContext uKept uAction

variable {Context : Type uContext} {Kept : Type uKept}
variable {Action : Type uAction}

/-- Average a full-context action kernel over the conditional distribution of
full contexts at one kept observation.  `condOnFibre` supplies an arbitrary
total fallback off the support; such kept observations are never drawn. -/
def averagedKernel (contextLaw : FinDist Context) (keep : Context → Kept)
    (kernel : Context → FinDist Action) (kept : Kept) : FinDist Action :=
  (contextLaw.condOnFibre keep kept).bind kernel

/-- The joint experiment using the original full-context kernel. -/
def fullJoint (contextLaw : FinDist Context) (keep : Context → Kept)
    (kernel : Context → FinDist Action) : FinDist (Kept × Action) :=
  contextLaw.bind fun context =>
    (kernel context).map fun action => (keep context, action)

/-- The joint experiment after replacing the kernel by its kept-context
average. -/
def averagedJoint (contextLaw : FinDist Context) (keep : Context → Kept)
    (kernel : Context → FinDist Action) : FinDist (Kept × Action) :=
  (contextLaw.map keep).bind fun kept =>
    (averagedKernel contextLaw keep kernel kept).map fun action =>
      (kept, action)

/-- Marginalizing the removed part of a context preserves the exact joint law
of the kept context and action. -/
theorem fullJoint_eq_averagedJoint (contextLaw : FinDist Context)
    (keep : Context → Kept) (kernel : Context → FinDist Action) :
    fullJoint contextLaw keep kernel =
      averagedJoint contextLaw keep kernel := by
  classical
  have hdecompose := FinDist.eq_bind_condOnFibre contextLaw keep
  calc
    fullJoint contextLaw keep kernel =
        (contextLaw.map keep).bind fun kept =>
          (contextLaw.condOnFibre keep kept).bind fun context =>
            (kernel context).map fun action =>
              (keep context, action) := by
      unfold fullJoint
      conv_lhs => rw [hdecompose, FinDist.bind_bind]
    _ = (contextLaw.map keep).bind fun kept =>
          (contextLaw.condOnFibre keep kept).bind fun context =>
            (kernel context).map fun action => (kept, action) := by
      apply FinDist.bind_congr
      intro kept hkept
      apply FinDist.bind_congr
      intro context hcontext
      have hfibre :
          ∃ witness ∈ keep ⁻¹' {kept}, witness ∈ contextLaw.support := by
        rw [FinDist.support_map] at hkept
        obtain ⟨witness, hwitness, hkeep⟩ := hkept
        exact ⟨witness, by simpa using hkeep, hwitness⟩
      have hcontextFibre : context ∈ keep ⁻¹' {kept} := by
        have hconditioned := hcontext
        simp only [FinDist.condOnFibre, dif_pos hfibre] at hconditioned
        exact (FinDist.support_condOn contextLaw
          (keep ⁻¹' {kept}) hfibre hconditioned).1
      have hkeep : keep context = kept := by
        simpa using hcontextFibre
      rw [hkeep]
    _ = averagedJoint contextLaw keep kernel := by
      unfold averagedJoint averagedKernel
      apply FinDist.bind_congr
      intro kept _
      rw [FinDist.map_bind]

/-- The averaged kept-context kernel may be expanded back to a full-context
kernel without changing the kept-context/action joint law. -/
theorem fullJoint_eq_fullJoint_averagedKernel
    (contextLaw : FinDist Context) (keep : Context → Kept)
    (kernel : Context → FinDist Action) :
    fullJoint contextLaw keep kernel =
      fullJoint contextLaw keep (fun context =>
        averagedKernel contextLaw keep kernel (keep context)) := by
  rw [fullJoint_eq_averagedJoint]
  unfold averagedJoint fullJoint
  rw [FinDist.bind_map]

/-- Consequently every observable of the kept context and action has the same
expectation before and after marginalization. -/
theorem expect_fullJoint_eq_averagedJoint (contextLaw : FinDist Context)
    (keep : Context → Kept) (kernel : Context → FinDist Action)
    (observable : Kept × Action → ℝ) :
    (fullJoint contextLaw keep kernel).expect observable =
      (averagedJoint contextLaw keep kernel).expect observable := by
  rw [fullJoint_eq_averagedJoint]

/-- Graph-free local-value bridge: whenever continuation value is a function
only of the kept context and chosen action, averaging away the rest of the
context preserves expected continuation value exactly. -/
theorem expect_kernel_eq_averagedKernel (contextLaw : FinDist Context)
    (keep : Context → Kept) (kernel : Context → FinDist Action)
    (continuationValue : Kept → Action → ℝ) :
    contextLaw.expect (fun context =>
        (kernel context).expect fun action =>
          continuationValue (keep context) action) =
      (contextLaw.map keep).expect (fun kept =>
        (averagedKernel contextLaw keep kernel kept).expect fun action =>
          continuationValue kept action) := by
  have hjoint := expect_fullJoint_eq_averagedJoint
    contextLaw keep kernel (fun pair => continuationValue pair.1 pair.2)
  simpa only [fullJoint, averagedJoint, FinDist.expect_bind,
    FinDist.expect_map] using hjoint

/-- A graph-free certificate that both the full-rule and kept-rule evaluators
use one continuation value depending only on the kept context and action.  A
future MAID global-Markov theorem should construct this certificate from
d-separation; it is not deviation coverage by definition. -/
structure ContinuationFactorsThrough (contextLaw : FinDist Context)
    (keep : Context → Kept)
    (fullValue : (Context → FinDist Action) → ℝ)
    (keptValue : (Kept → FinDist Action) → ℝ) where
  continuationValue : Kept → Action → ℝ
  full_eq : ∀ kernel,
    fullValue kernel =
      contextLaw.expect (fun context =>
        (kernel context).expect fun action =>
          continuationValue (keep context) action)
  kept_eq : ∀ kernel,
    keptValue kernel =
      (contextLaw.map keep).expect (fun kept =>
        (kernel kept).expect fun action =>
          continuationValue kept action)

/-- A shared continuation factor constructs exact local rule coverage.  The
witness is the conditional average of the arbitrary full-context rule. -/
theorem exists_keptRule_value_eq_of_continuationFactorsThrough
    (contextLaw : FinDist Context) (keep : Context → Kept)
    (fullValue : (Context → FinDist Action) → ℝ)
    (keptValue : (Kept → FinDist Action) → ℝ)
    (hfactor : ContinuationFactorsThrough contextLaw keep fullValue keptValue)
    (fullRule : Context → FinDist Action) :
    ∃ keptRule : Kept → FinDist Action,
      fullValue fullRule = keptValue keptRule := by
  refine ⟨averagedKernel contextLaw keep fullRule, ?_⟩
  rw [hfactor.full_eq, hfactor.kept_eq]
  exact expect_kernel_eq_averagedKernel contextLaw keep fullRule
    hfactor.continuationValue

/-! ## Fair-signal control -/

def fairSignal : FinDist Bool :=
  FinDist.mix (1 / 2) (by norm_num) (by norm_num)
    (FinDist.pure false) (FinDist.pure true)

def copySignal (signal : Bool) : FinDist Bool :=
  FinDist.pure signal

def fullActionValue (kernel : Bool → FinDist Bool) : ℝ :=
  fairSignal.expect fun signal =>
    (kernel signal).expect fun action => if action then 1 else 0

def keptActionValue (kernel : Unit → FinDist Bool) : ℝ :=
  (kernel ()).expect fun action => if action then 1 else 0

/-- The fair-signal action-only payoff supplies the stronger local
continuation-factorization certificate, not merely an equality for one rule.
-/
def actionValueFactors : ContinuationFactorsThrough fairSignal
    (fun _ : Bool => ()) fullActionValue keptActionValue where
  continuationValue _ action := if action then 1 else 0
  full_eq _ := rfl
  kept_eq kernel := by
    unfold keptActionValue
    rw [FinDist.map_const, FinDist.expect_pure]

/-- The full kernel genuinely reads the context that will be removed. -/
theorem copySignal_reads_context : copySignal false ≠ copySignal true := by
  intro hequal
  have hprob := congrArg (fun law : FinDist Bool => law.prob true) hequal
  norm_num [copySignal, FinDist.prob_pure_eq_ite] at hprob

/-- After forgetting the entire context, averaging the copying rule produces
the fair randomized action law.  This is not constant-policy factorization. -/
theorem averagedKernel_copySignal :
    averagedKernel fairSignal (fun _ : Bool => ()) copySignal () =
      fairSignal := by
  unfold averagedKernel
  have hfibre :
      ∃ signal ∈ (fun _ : Bool => ()) ⁻¹' {()},
        signal ∈ fairSignal.support := by
    refine ⟨false, by simp, ?_⟩
    rw [← FinDist.prob_pos_iff]
    norm_num [fairSignal, FinDist.prob_mix,
      FinDist.prob_pure_eq_ite]
  rw [FinDist.condOnFibre, dif_pos hfibre]
  have hfibreUniv : (fun _ : Bool => ()) ⁻¹' {()} = Set.univ := by
    ext signal
    simp
  have huniv : ∃ signal ∈ Set.univ, signal ∈ fairSignal.support := by
    obtain ⟨signal, _, hsignal⟩ := hfibre
    exact ⟨signal, Set.mem_univ signal, hsignal⟩
  rw [FinDist.condOn_congr fairSignal hfibreUniv hfibre huniv,
    FinDist.condOn_univ fairSignal huniv]
  exact FinDist.bind_pure fairSignal

/-- The generic joint-law theorem is exercised on a signal-dependent kernel,
so it cannot pass by simplifying the original rule to a constant. -/
theorem copySignal_joint_preserved :
    fullJoint fairSignal (fun _ : Bool => ()) copySignal =
      averagedJoint fairSignal (fun _ : Bool => ()) copySignal :=
  fullJoint_eq_averagedJoint fairSignal (fun _ => ()) copySignal

/-- The named continuation certificate constructs a signal-blind rule with
the same action-only value as the genuinely signal-reading copy rule. -/
theorem exists_keptRule_copySignal_value_eq :
    ∃ keptRule : Unit → FinDist Bool,
      fullActionValue copySignal = keptActionValue keptRule :=
  exists_keptRule_value_eq_of_continuationFactorsThrough
    fairSignal (fun _ => ()) fullActionValue keptActionValue
      actionValueFactors copySignal

end GameTheory.Experimental.PostArchitecture.MAIDKernelMarginalization
