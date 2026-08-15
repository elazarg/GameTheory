/-
# EXP-020: the same question at the layer where it was decided

The protocol spike measures the sequential layer. The signature-ownership
decision was taken at the static one, and it has a cost there that the protocol
spike cannot show.

A form that *stores* its signature must say what the signature of a transformed
form is, and say it as a theorem: `(F.mixed).sig = F.sig.mixed`. That equation
does not hold by reduction at default transparency, which is why the accepted
design makes every signature transformer an `abbrev` — four of them in the core.
A form *indexed* by its signature states the same fact in its type, where there
is nothing left to reduce and nothing to annotate.

This file carries both sides far enough to see the difference. Recorded
evidence, not API.
-/

import GameTheory.Core.Form

noncomputable section

namespace GameTheory.Experimental.Phase4.D1

open GameTheory GameTheory.Math.Probability

universe uι us uo

variable {ι : Type uι}

/-! ## The indexed form -/

/-- A form indexed by its signature rather than storing it. -/
structure IndexedForm (sig : GameSignature.{uι, us, uo} ι) where
  /-- The stochastic outcome law of each profile. -/
  play : Profile sig → FinDist sig.Outcome

/-- Relabelling outcomes. What the accepted design states as a theorem — that the
result's signature is the transformed signature — is written here in the type. -/
def IndexedForm.mapOutcome {sig : GameSignature.{uι, us, uo} ι} (F : IndexedForm sig)
    (Outcome : Type uo) (relabel : sig.Outcome → Outcome) :
    IndexedForm (sig.mapOutcome Outcome) where
  play profile := (F.play profile).map relabel

/-- The mixed extension. Likewise. -/
def IndexedForm.mixed [Fintype ι] {sig : GameSignature.{uι, us, uo} ι} (F : IndexedForm sig) :
    IndexedForm sig.mixed where
  play law := (FinDist.pi law).bind F.play

/-! ## What indexing removes, and what it does not

It removes the two facts the accepted design has to state and the two
annotations that make them hold. `mapOutcome_sig` and `mixed_sig` are theorems
about a projection of a constructed form; here there is no projection, so they
are not statable and not needed, and the form transformers can be plain
definitions.

It does *not* remove the need for the two `GameSignature` transformers to be
reducible. The field types above still have to reduce through them — that is why
they are `abbrev` in the core and why they must stay so. So the honest count at
this layer is four annotations against two, a halving rather than an
elimination.

The three checks below use no annotation of their own. -/

example [Fintype ι] {sig : GameSignature.{uι, us, uo} ι} (F : IndexedForm sig) :
    IndexedForm sig.mixed := F.mixed

example {sig : GameSignature.{uι, us, uo} ι} (F : IndexedForm sig) (Outcome : Type uo)
    (relabel : sig.Outcome → Outcome) : IndexedForm (sig.mapOutcome Outcome) :=
  F.mapOutcome Outcome relabel

/-- Relabelling twice is relabelling once, and the types already agree — under
bundling the signature identity has to be applied first. -/
example {sig : GameSignature.{uι, us, uo} ι} (F : IndexedForm sig)
    (Middle Outcome : Type uo) (first : sig.Outcome → Middle) (second : Middle → Outcome) :
    (F.mapOutcome Middle first).mapOutcome Outcome second =
      F.mapOutcome Outcome (second ∘ first) := by
  refine congrArg IndexedForm.mk (funext fun profile => ?_)
  simp [IndexedForm.mapOutcome, Function.comp_def]

/-! ## What the index costs

Everything mentioning a form gains a signature argument. Where the signature is
a section variable that is invisible, which is the same amortization the protocol
spike found; it becomes visible only where forms with different signatures meet,
and that is exactly where the accepted design needs its annotation. The two costs
sit at the same sites. -/

variable (sig : GameSignature.{uι, us, uo} ι)

example (F : IndexedForm sig) : Profile sig → FinDist sig.Outcome := F.play

end GameTheory.Experimental.Phase4.D1
