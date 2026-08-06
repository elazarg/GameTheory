# Boundary-holonomy residuals and tangent coordinates

Finite quitting blocks act on a supplied continuation value in two different
ways.  Prescribed play gives an affine map, while a player's unilateral
stopping problem gives a max-affine map.  The boundary-holonomy tangent layer
records the exact residual algebra of these maps and the first-order data that
survive when a block's absorption mass tends to zero.

This is a coefficient and projection layer.  It neither produces finite
strategic blocks nor decodes a limiting coefficient packet into one.

## Residual algebra

For an affine summary `w ↦ intercept + survival * w`, set

```text
absorptionMass = 1 - survival
targetResidual = eval(target) - target.
```

The residual is exactly

```text
intercept - absorptionMass * target
```

and chronological composition obeys the cocycle law

```text
r(outer * inner) = r(outer) + outer.survival * r(inner).
```

Away from the neutral face, division by absorption mass recovers the
displacement of the contracting fixed point from the target.  Finite
self-composition multiplies the residual by the geometric amplifier.  At
survival one a nonzero residual therefore grows linearly under repetition.
The coefficient idempotents are exactly constant projectors and the identity.

For a max-affine stopping summary

```text
w ↦ max early (tail + survival * w),
```

the tail residual satisfies the same transported cocycle, while total target
excess satisfies a max-plus Bellman recurrence.  Safety at a target is exactly
the pair of halfspaces

```text
early ≤ target,
tail ≤ absorptionMass * target.
```

Its idempotents are constant summaries and threshold closures.  Nonempty
iteration is used because a finite max-affine stopping summary has no finite
identity element.

## Self-similarity

`QuittingBoundaryHolonomy.IsSelfSimilarAt target` combines the playerwise
conditions that prescribed transport fixes `target` and unilateral stopping
is capped by `target`.  It is a finite semialgebraic condition, is preserved by
chronological composition, and gives a nonpositive zero-debt boundary gap.
Finite nonempty repetition preserves it, and coefficient-idempotent
self-similar holonomies have explicit normal forms.

The definition is deliberately not an existence theorem.  An abstract
self-similar coefficient tuple need not be realized by a common root block,
and a coefficient limit retains neither the source path nor splice
provenance.

## Absorbed-mass tangent

Writing an affine block with mass `m` and conditional anchor `a` gives the
exact finite-scale formula

```text
eval(w) = w + m * (a - w).
```

The max-affine analogue separates an early obstacle and a conditional tail
anchor.  Probing at `target + m*x` yields the exact normalized expression

```text
max earlyDrift (tailAnchor - target + x - m*x).
```

The limiting scalar tangent is `x ↦ max early (tail + x)`.  Its repetitions
have a complete trichotomy: positive tail drift exceeds every finite budget,
zero drift is the idempotent threshold closure, and negative drift eventually
becomes the constant early projector.

## Realized bounds and projected compactness

The weighted finite-block bounds imply that every nonneutral realized
prescribed fixed point and unilateral tail anchor lies within the terminal
reward bound.  Target residuals are first-order in their own absorption mass.
On a realized neutral face, the weighted intercept vanishes: prescribed
transport is the identity and unilateral tail transport is a threshold
closure.

The tangent core retains playerwise absorption masses, conditional anchors,
and the unscaled early floor.  Every realized finite-holonomy projection lies
in one compact product box, so every sequence has a convergent coordinate
subsequence.  An extended coordinate adjoins

```text
positive early excess / tail absorption mass
```

in `ℝ≥0∞`; infinity records an unsafe early obstacle on a neutral tail face.

Three boundaries are essential:

- compactness is proved for the coordinate projection, not for realized
  strategic blocks or their source paths;
- the totalized anchor value at zero mass is a coordinate convention, not a
  recovered limiting conditional payoff; and
- the extended coordinate records the positive safety obstruction, not a full
  signed early tangent or a theorem that a selected sequence converges to
  infinity.

Fixed-cutoff and fixed-last resolved holonomy lifts remain the source-retaining
compactness interfaces.  Arbitrary-length realization, strategic closedness,
and a decoder from tangent data remain separate obligations.

## Lean surface

- `QuittingBoundaryHolonomyAffineResidual.lean` contains affine residual,
  repetition, pumping, and idempotent algebra.
- `QuittingBoundaryHolonomyMaxAffineResidual.lean` contains the max-affine
  residual, target-safety, repetition, and idempotent layer.
- `QuittingBoundaryHolonomySelfSimilarity.lean` contains playerwise
  self-similarity and synchronized repetition.
- `QuittingBoundaryHolonomyTangent.lean` contains absorbed-mass normal forms
  and max-plus dynamics.
- `QuittingBoundaryHolonomyRealizedTangent.lean` contains actual-block bounds,
  neutral forms, and compact coordinate subsequences.
