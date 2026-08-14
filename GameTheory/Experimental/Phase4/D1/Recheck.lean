/-
# EXP-020: the transformation recheck the decision named

The signature-ownership record does not leave the recheck open-ended. It names
three tests: a nested operation chain, a reindex round trip along `e` and then
`e.symm`, and an equivalence lifted through mixed extension. It also names what
would overturn the decision — the accepted design *repeatedly* needing signature
equalities or user-visible transports.

Two spikes elsewhere in this directory measure reducibility annotations, and
both favour indexing. Neither touches the axis the decision was actually taken
on, which the record states plainly: bundling makes ordinary downstream
signatures shorter, and indexing exposes a signature parameter wherever a form
appears. This file runs the named tests on that axis.

The unit of comparison is what each candidate has to put in a *statement*, since
that is the axis in question. Recorded evidence, not API.
-/

import GameTheory.Experimental.Phase1.D1.Stress

noncomputable section

namespace GameTheory.Experimental.Phase4.D1.Recheck

open GameTheory.Experimental.Phase1
open GameTheory.Experimental.Phase1.D1

/-! ## Test one: a nested operation chain

Relabel outcomes, take the mixed extension, then form a product. Both candidates
state the evaluation law and both prove it by reduction; the difference is that
the indexed statement carries the whole chain in the profile's type while the
bundled one says `Form ι` and projects. -/

namespace Chain

open GameTheory.Experimental.Phase1.D1.Indexed
open GameTheory.Experimental.Phase1.D2.FiniteSupportPMF

theorem indexed {ι : Type*} [Fintype ι] {sig τ : Signature ι} (F : Form sig) (G : Form τ)
    {Outcome : Type*} (relabel : sig.Outcome → Outcome)
    (profile : Profile ((sig.mapOutcome Outcome).mixed.product τ)) :
    (((F.mapOutcome relabel).mixed).product G).play profile =
      (((F.mapOutcome relabel).mixed).play fun i => (profile i).1).bind fun first =>
        (G.play fun i => (profile i).2).map fun second => (first, second) := rfl

end Chain

namespace ChainBundled

open GameTheory.Experimental.Phase1.D1.Bundled
open GameTheory.Experimental.Phase1.D2.FiniteSupportPMF

theorem bundled {ι : Type*} [Fintype ι] (F G : Form ι) {Outcome : Type*}
    (relabel : F.sig.Outcome → Outcome)
    (profile : Profile ((((F.mapOutcome relabel).mixed).product G).sig)) :
    (((F.mapOutcome relabel).mixed).product G).play profile =
      (((F.mapOutcome relabel).mixed).play fun i => (profile i).1).bind fun first =>
        (G.play fun i => (profile i).2).map fun second => (first, second) := rfl

end ChainBundled

/-! ## Test two: the reindex round trip

This is the test that discriminates, and it discriminates against indexing.

Reindexing forward and back does not return to the same signature by reduction:
the strategy carrier becomes `sig.Strategy (e.symm (e i))`, and that is `sig`'s
carrier only propositionally. So under indexing the two sides of the round trip
live in *different types*, and the statement cannot be written down at all
without a signature equality to transport along. Under bundling both sides are
`Form ι` and the statement needs neither.

The two definitions below are the two statements. Neither is proved here; what
is being measured is what each one costs to write, which is the axis the
decision was taken on. The asymmetry is visible in their signatures. -/

namespace RoundTrip

open GameTheory.Experimental.Phase1.D1.Indexed

/-- The indexed round trip. The hypothesis is not a convenience: without it the
equation is ill-typed, and `subst` cannot remove it because the signature occurs
on both sides of it. -/
def indexedStatement {ι κ : Type*} {sig : Signature ι} (F : Form sig) (e : ι ≃ κ)
    (hsig : (sig.reindex e).reindex e.symm = sig) : Prop :=
  hsig ▸ ((F.reindex e).reindex e.symm) = F

end RoundTrip

namespace RoundTripBundled

open GameTheory.Experimental.Phase1.D1.Bundled

/-- The bundled round trip, with no hypothesis and no transport. -/
def bundledStatement {ι κ : Type*} (F : Form ι) (e : ι ≃ κ) : Prop :=
  (F.reindex e).reindex e.symm = F

end RoundTripBundled

/-! ## Test three: an equivalence lifted through mixed extension

This one does not discriminate. Reindexing commutes with the mixed extension
only up to an interchange of the independent product with the relabelling of
players, and that is a real lemma in both candidates rather than a reduction —
`rfl` is rejected on both sides. So the third named test is neutral: it costs the
same either way, and it costs more than nothing. -/

namespace MixedThroughEquiv

open GameTheory.Experimental.Phase1.D1.Indexed

def indexedStatement {ι κ : Type*} [Fintype ι] [Fintype κ] {sig : Signature ι}
    (F : Form sig) (e : ι ≃ κ) : Prop :=
  (F.mixed).reindex e = (F.reindex e).mixed

end MixedThroughEquiv

namespace MixedThroughEquivBundled

open GameTheory.Experimental.Phase1.D1.Bundled

def bundledStatement {ι κ : Type*} [Fintype ι] [Fintype κ] (F : Form ι) (e : ι ≃ κ) : Prop :=
  (F.mixed).reindex e = (F.reindex e).mixed

end MixedThroughEquivBundled

end GameTheory.Experimental.Phase4.D1.Recheck
