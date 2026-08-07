# Charged projective lassos: the producer interface

## Status

This note separates three statements that should not be conflated.

1. **Exact first-event normalization** is elementary and Lean-checked in
   `Math.ProjectiveBellmanPacket`.
2. **A charged projective lasso can be corrected and compiled** is
   Lean-checked in `QuittingProjectiveLasso`.
3. **Every finite quitting game produces such lassos, or reaches a simpler
   output boundary**, is the remaining projective pivot-or-output theorem.
   It is stated here as the next theorem target; no proof of it is claimed by
   this PR.

The purpose of the new layer is to replace the vague request for a prefix with
small joint survival by a finite recurrent certificate whose downstream
compiler is complete.

## 1. First-event projectivization

Let `ε > 0` be the discount-complement and write `β = 1 - ε`.  At a stationary
root, let

- `c` be the probability that everybody continues;
- `q = 1 - c` be the real absorption probability; and
- `a` be the unconditional absorbing payoff contribution in one stage.

The discounted Bellman equation in one coordinate is

```text
v = β * (a + c * v).
```

Define

```text
D  = ε + β * q = 1 - β * c,
ω₀ = ε / D,
ω₁ = β * q / D.
```

Then

```text
ω₀ + ω₁ = 1
```

and the Bellman equation is exactly

```text
D * v = β * a.
```

When `q > 0`,

```text
v = ω₁ * (a / q).
```

Thus `ω₀` is the normalized mass of the artificial discount or cemetery event,
while `ω₁` is the normalized mass of a genuine absorption event.  The matching
regime is not a pathology: it is the interior face `0 < ω₀ < 1`.  Discarding
`ω₀` before compactification loses the continuation datum needed to pass
through that face.

The exact algebra is formalized by:

```text
Math.projectiveCemeteryWeight_add_absorptionWeight
Math.projectiveBellman_balance
Math.projectiveBellman_value_eq_absorptionWeight_mul_conditional
```

## 2. Finite charged projective lasso

Fix a finite root word

```text
cycle : Fin K → ι → PMF Bool
```

and proposed cyclic values

```text
value : Fin K → Payoff ι.
```

At phase `p`, define the policy seam

```text
e_p = value p -
  quittingRootSuccessorPayoff reward
    (value (finRotate K p)) (cycle p).
```

Let

```text
c_p = quittingStationaryContinueMass (cycle p),
q_p = 1 - c_p.
```

A charged lasso at error `η` requires

```text
|e_p(i)| ≤ η * q_p
```

for every phase and player.  It additionally retains:

- support-local `η`-optimality at the displayed next value;
- punishment rationality to error `η`; and
- one phase with `q_p > 0`.

This is the structure

```text
QuittingFiniteChargedProjectiveLasso reward K η.
```

The adjective *projective* refers to the ratio `e_p / q_p`.  Raw seam error is
not the stable quantity near a neutral block; residual divided by real
absorption is.

## 3. Exact correction theorem

Let `u_p` be the actual terminal value selected by periodically repeating the
root word.  The one-step difference satisfies

```text
value p - u_p = e_p + c_p * (value (next p) - u_(next p)).
```

For a chosen starting phase, write

```text
W_k = product of c along the first k phases.
```

After one turn,

```text
(1 - C) * (value p - u_p)
  = sum_{k < K} W_k * e_k,
```

where `C = product_p c_p`.  Independently,

```text
1 - C = sum_{k < K} W_k * (1 - c_k).
```

Therefore

```text
|value p - u_p|
  ≤ η * (1 - C) / (1 - C)
  = η.
```

One absorbing phase gives `C < 1`, so division is legitimate.  No period
factor appears.  This is the theorem

```text
abs_quittingCyclicValue_sub_terminalValue_le_of_chargedResidual.
```

The proof is entirely finite.  It does not invoke compactness, a minimizer, or
continuity at saturated hazards.

## 4. Support and rationality survive correction

For fixed root and player, the endpoint difference is affine in the player's
continuation coordinate with coefficient equal to the opponents' continue
mass.  That coefficient lies in `[0,1]`, hence

```text
|D_i(w) - D_i(w')| ≤ |w_i - w'_i|.
```

This is

```text
abs_quittingRootEndpointDifference_sub_le_tail.
```

Consequently replacing `value` by `u` costs at most another `η` in both the
support inequalities and the punishment floor.  The corrected exact cycle is
therefore support-rational at error `2η`:

```text
QuittingFiniteChargedProjectiveLasso.toFiniteSupportRationalCycle.
```

The existing periodic support-witness adapter then gives:

- an infinite PMF-root path;
- support-local error `2η`;
- punishment rationality error `2η`; and
- nonsummable absorption.

The all-accuracy conclusion is

```text
quittingGame_exists_uniformEquilibriumPayoff_of_chargedProjectiveLassos.
```

## 5. Why this is the correct recurrent producer

The diagonal-prefix compiler asks for small joint survival at a chosen
endpoint.  That is a useful output face, but it is not the general object
supplied by a matching-scale vanishing-discount branch.  In the matching
regime a nonzero fraction of the normalized first-event mass is cemetery mass.
The correct procedure is:

1. retain the cemetery coordinate;
2. rebase it as a continuation anchor;
3. follow the resolved complementary/valuation pivot;
4. stop at a simple output boundary, or close a repeated projective state.

A repeated labelled state need not close the raw Bellman equations exactly.
It closes their leading projective data.  Therefore the seam has strictly
higher valuation than the real absorption charge, which is precisely the
charged-lasso condition consumed above.

## 6. Remaining theorem: physical pivot completeness

The unresolved global theorem can now be stated locally.

> **Physical Pivot Completeness.** At every nonterminal resolved projective
> Nash--Bellman node with positive cemetery mass, either the lexicographic
> complementary pivot has a physically admissible continuation orientation,
> or the dual row is one of the following finite output certificates:
>
> 1. a stationary or pure terminal equilibrium;
> 2. a Never certificate;
> 3. a target-closed-tail boundary;
> 4. a strict support/valuation-rank descent.

There may be no fifth unclassified barrier.

After generic perturbation there are finitely many complementary bases and
finitely many valuation cones.  Physical Pivot Completeness would therefore
imply that pivot iteration either reaches one of the four outputs or repeats a
labelled projective state.  The repeated state yields the charged lasso
compiled by this PR.  Perturbation closure can then return the conclusion to
the original rational table.

This PR does **not** formalize or assume that theorem.  Its contribution is to
make the recurrent output exact, finite, and fully executable, so future work
is concentrated on the local pivot classification rather than another global
compact-minimizer problem.
