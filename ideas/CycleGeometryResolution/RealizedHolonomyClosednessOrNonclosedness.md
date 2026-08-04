# Realized holonomy closedness or nonclosedness

| Status | Provenance | Formalization | Next experiment |
| --- | --- | --- | --- |
| `PARTIAL`, maturity `M+L/I` | E50 + `e1fe7dc` + Q133 | full fixed-cutoff lift compact/closed; escaping literal length is noncompact | tight infinity/stopping-law lift versus calibrated incompatible-splice family |

The finite-block holonomy map sends provenance-carrying exact chain blocks to
a compact scalar coefficient box. The decisive question is the topology of its
**realized arbitrary-length image**, with enough source labels to preserve
chronology and the terminal anchor.

Positive route: prove sequential closedness after adding the minimal finite
support/branch labels and, if needed, an iterated scale or stopping-law limit.
Negative route: construct two calibrated block sequences with the same scalar
limit but incompatible root words, packet transport, or splice acceptance.
Such a counterexample is not failure; it identifies the missing coordinate or
proves that no finite-dimensional closed summary of the proposed type exists.

K11 overlapping branches, FTV neutral rotation, Q129 owner nontransfer, and the
two-ended missing-middle example are mandatory tests. Ambient coefficient
compactness alone is not evidence for the positive route.

`QuittingBoundaryHolonomyCompactness.lean` now draws the exact endpoint
fence.  At any fixed cutoff, the holonomy graph over all exact zero-boundary
chains is the continuous image of a compact path space.  Its finite union over
all legal subblocks is compact and closed while retaining the whole source
path.  A second fixed-last lift retains the selected minimizer, owner, marked
terminal action, exact-D endpoints, separate survival/atom packet, and common
holonomy; it is finite and receives every calibrated production block.

The obstruction occurs only when game length escapes.  A machine-checked
general theorem says that every compact subset of `ℕ × X` has uniformly
bounded first coordinate.  Hence no compact resolved state can simultaneously
retain literal finite stage cost and contain arbitrarily long middles.  This
is the Q133 endpoint: a point at infinity or measure-valued word limit may be
topologically compact, but topology then supplies no bounded-cost exact
decoder.  The strongest presently justified closed subclass is the uniformly
bounded-cutoff class.  To cover the positive plateau one must prove a uniform
finite-support/length reduction, or add an infinity chart together with a
separate theorem converting it to bounded finite repair. The debt-descent
alternative is closed within the zero-pinned grammar — no bounded exact
extension achieves a cutoff-independent decrement — and that closure is itself
an artifact of the pin, since the plateaus driving it vanish once the terminal
continuation is unpinned. See
[anchored repair or uniform debt descent](../PositivePlateauBoundaryClosure/AnchoredRepairOrUniformDebtDescent.md).
