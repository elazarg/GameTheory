import Semantics.TransitionTrace

set_option autoImplicit false

namespace GameTheory
namespace Model
namespace FiniteRecall

open Semantics.Transition

variable {ι α σ : Type}

/-- Finite-trace semantic perfect recall.

For each agent `i`, any two finite runs from `s0` that end in `i`-equivalent
states induce the same remembered local projection. -/
def PerfectRecall
    (step : α → σ → σ → Prop)
    (s0 : σ)
    (TraceView : ι → Type)
    (infoEq : (i : ι) → σ → σ → Prop)
    (project : (i : ι) → List α → TraceView i) : Prop :=
  ∀ (i : ι) (h1 h2 : List α) (s1 s2 : σ),
    ReachBy step h1 s0 s1 →
    ReachBy step h2 s0 s2 →
    infoEq i s1 s2 →
    project i h1 = project i h2

/-- Bounded finite-trace semantic perfect recall up to run length `k`. -/
def PerfectRecallUpTo
    (k : Nat)
    (step : α → σ → σ → Prop)
    (s0 : σ)
    (TraceView : ι → Type)
    (infoEq : (i : ι) → σ → σ → Prop)
    (project : (i : ι) → List α → TraceView i) : Prop :=
  ∀ (i : ι) (h1 h2 : List α) (s1 s2 : σ),
    h1.length ≤ k →
    h2.length ≤ k →
    ReachBy step h1 s0 s1 →
    ReachBy step h2 s0 s2 →
    infoEq i s1 s2 →
    project i h1 = project i h2

theorem perfectRecall_implies_upTo
    (k : Nat)
    {step : α → σ → σ → Prop}
    {s0 : σ}
    {TraceView : ι → Type}
    {infoEq : (i : ι) → σ → σ → Prop}
    {project : (i : ι) → List α → TraceView i}
    (hpr : PerfectRecall step s0 TraceView infoEq project) :
    PerfectRecallUpTo k step s0 TraceView infoEq project := by
  intro i h1 h2 s1 s2 _h1 _h2 hr1 hr2 heq
  exact hpr i h1 h2 s1 s2 hr1 hr2 heq

theorem perfectRecallUpTo_mono
    {k k' : Nat}
    (hkk' : k ≤ k')
    {step : α → σ → σ → Prop}
    {s0 : σ}
    {TraceView : ι → Type}
    {infoEq : (i : ι) → σ → σ → Prop}
    {project : (i : ι) → List α → TraceView i}
    (hpr : PerfectRecallUpTo k' step s0 TraceView infoEq project) :
    PerfectRecallUpTo k step s0 TraceView infoEq project := by
  intro i h1 h2 s1 s2 hh1 hh2 hr1 hr2 heq
  exact hpr i h1 h2 s1 s2 (Nat.le_trans hh1 hkk') (Nat.le_trans hh2 hkk') hr1 hr2 heq

end FiniteRecall
end Model
end GameTheory
