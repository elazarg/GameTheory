# Finite-group orbit gluing for monotone constraints

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `PENDING` |
| Verdict | `MIXED` |
| Objective priority | `P2` |
| Last audited | 2026-08-03, isolated experiment `FiniteGroupOrbitGluing.lean` |
| Central live claim | Orbit joins or meets turn equivariant translated witnesses into one invariant common witness exactly when the feasibility predicates have the matching order closure. |
| Next discriminant | Identify a concrete coalition continuation constraint that is genuinely upward- or downward-closed and retains all strategic labels. |
| Production destination | None yet; possible small order-theoretic helper only after a second actual consumer appears. |
| Supersedes / superseded by | None; it must not be used as a quotient replacement for the resolved groupoid in `ideas/CycleGeometryResolution/README.md`. |

### Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| FOG1 | For a monotone group action on a complete lattice, the supremum and infimum of an orbit are invariant. | `PROVED` | `X` | Any group; stronger than the finite-group motivation. |
| FOG2 | Equivariant upward-closed constraints glue at the orbit supremum, and downward-closed constraints glue at the orbit infimum. | `PROVED` | `X` | `FiniteGroupOrbitGluing.lean`. |
| FOG3 | One representative per constraint orbit suffices after translating and joining/meeting its witness. | `CONDITIONAL` | `I` | Requires the family action law and the appropriate closure orientation. |
| FOG4 | Certified coalition-split continuation constraints in the current stochastic-game program satisfy those closure hypotheses on a strategically sound lattice. | `OPEN` | `I` | Missing actual-data adapter. |

### Falsifiers and wrong turns

- Convexity alone does not work: each translated witness belongs to a
  different constraint set, so their average need not belong to any of them.
- Reversing join and meet invalidates Bellman inequalities in general;
  expectation does not commute with pointwise maximum.
- A lattice aggregate may erase support, owner, terminal action, scale, or
  provenance.  Such an aggregate is not a resolved certificate.
- One non-monotone strategic constraint is enough to block FOG4 even though
  FOG1--FOG2 remain true.

### Production map

```text
monotone group action + complete lattice -> invariant orbit sup/inf [X]
equivariant closed constraints ----------> common witness           [X]
actual coalition certificates -----------> those hypotheses         [?]
```

### Exit conditions

- Mark `MINED` once an independent audit either promotes the small abstract
  lemma for a named consumer or confirms that existing lattice APIs suffice.
- Mark FOG4 `WRONG` for a proposed certificate space as soon as a mandatory
  strategic field or inequality is not preserved by its join/meet.
- Mark `PARKED` if no current coalition producer has the needed monotonicity.
- Do not mark the group `WRONG` merely because one game-facing lattice fails;
  the abstract order theorem is separate.

## Scope

This note concerns group actions on ordered feasibility spaces.  It is
independent of stochastic games and coalition modeling.  Its coalition-split
application is isolated in
[`CoalitionSplittingGroupActions`](../CoalitionSplittingGroupActions/README.md).

Let a finite group `Gamma` act on a partially ordered type `L`.  Assume every
group element acts by an order automorphism.  The Lean experiment proves a
slightly stronger version for an arbitrary group acting monotonically on a
complete lattice; inverses make each action map an order automorphism.  For a
finite group the mathematical argument only needs the corresponding finite
joins or meets.

This construction is safe only in the ordered feasibility coordinate for
which closure was proved.  In particular, it does not authorize quotienting
the resolved cycle atlas or forgetting the groupoid labels retained by
[`CycleGeometryResolution`](../CycleGeometryResolution/README.md).

## 1. Orbit joins

Suppose `L` is a join-semilattice and `F_g subseteq L` is an equivariant
family of upward-closed sets:

```text
F_(h*g) = h . F_g.
```

Choose `x in F_e`.  Then `g.x in F_g` for every `g`.

### Theorem 1: orbit-join gluing

Define

```text
xbar = join_{g in Gamma} g.x.
```

Then:

1. `xbar in F_g` for every `g`;
2. `h.xbar = xbar` for every `h in Gamma`.

### Proof

For fixed `g`, the join lies above the summand `g.x`.  Since `F_g` is upward
closed and contains `g.x`, it contains `xbar`.

For invariance, an order automorphism preserving joins gives

```text
h.xbar = join_g h.(g.x) = join_g (h*g).x.
```

Left multiplication by `h` permutes the finite group, so the last join is
`xbar`.  QED.

## 2. Orbit meets

### Theorem 2: orbit-meet gluing

If `L` is a meet-semilattice and the `F_g` are downward closed, then

```text
xunder = meet_g g.x
```

belongs to every `F_g` and is group-invariant.

The proof is the order dual of Theorem 1.

## 3. One constraint orbit versus several orbits

If the constraint index set has several `Gamma`-orbits, choose one witness
per orbit and take the join of all translated witnesses.  Upward closure then
gives a common invariant point.  Thus the number of independent selections is
the number of constraint orbits, not the number of constraints.

Stabilizer invariance of the representative witness is **not** required for
the orbit join itself: joining all translates removes the ambiguity.  It is
required when one wants to transport the representative as a single-valued
equivariant selection without subsequently joining.

## 4. Why convex averaging is different

Given `x in F_e`, the translated point `g.x` lies in `F_g`, but generally not
in `F_h` for `h != g`.  Convexity of each individual `F_g` therefore does not
imply that the average of the orbit lies in every set.  Orbit averaging works
immediately only for one invariant convex set.

Monotonicity is what validates orbit join/meet gluing: the common aggregate is
ordered beyond each set's own witness.

## 5. Bellman orientation

For upper Bellman supersolutions

```text
r + P H <= g + H,
```

pointwise minima are again supersolutions:

```text
P(min_k H_k) <= P(H_j)
```

for every `j`, so taking the minimum of the right sides proves the claim.
Pointwise maxima need not work because expectation of a maximum is generally
larger than the maximum of expectations.  Hence upper Bellman feasibility is
naturally a downward/meet construction.

Lower Bellman subsolutions have the dual join orientation.

## 6. Formalization status

The independent experiment
`experiments/FiniteGroupOrbitGluing.lean`
proves:

1. finite orbit joins are invariant under a finite group action preserving
   `sup`;
2. orbit joins satisfy every equivariant upward-closed constraint containing
   its corresponding translate;
3. the dual meet statements;
4. the common invariant witness obtained from either orientation.

It deliberately does not claim the game-facing specialization in FOG4.  In
particular, no continuation or resolved-certificate type has been shown to
carry all of the required complete-lattice and closure structure.
