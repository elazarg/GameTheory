# Equivariant transport of periodic block words

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `PENDING` |
| Verdict | `MIXED` |
| Objective priority | `P2` |
| Last audited | 2026-08-03, isolated experiment `EquivariantWordTransport.lean` |
| Central live claim | An automorphism action that intertwines each certified block map transports every finite word, its fixed points, and equivariant acceptance tests to the corresponding word orbit. |
| Next discriminant | Define or refute the required action on fully labelled edges and fibers in one certified resolved component. |
| Production destination | Possible adapter to graph-directed periodic lift and max-affine word validation; none until actual resolved data supplies the action. |
| Supersedes / superseded by | Independent infrastructure consumed conceptually by `CoalitionSplittingGroupActions.md`; does not supersede `CycleGeometryResolution.md`. |

### Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| EWT1 | Relabeling every letter of a word defines a group action on finite words. | `PROVED` | `X` | `EquivariantWordTransport.lean`. |
| EWT2 | Letterwise equivariance implies equivariance of the composite map of every finite word. | `PROVED` | `X` | No inverse or identity is required of the block-map semigroup. |
| EWT3 | A fixed point of a word transports to a fixed point of every relabelled word. | `PROVED` | `X` | Periodic block validation on a supplied orbit. |
| EWT4 | If a group element stabilizes a word and that word has a unique fixed point, then it fixes the point. | `PROVED` | `X` | Stabilizer compatibility follows from uniqueness. |
| EWT5 | The current resolved game certificates carry the required action while retaining support, terminal action, owner, scale, and provenance. | `OPEN` | `I` | Actual-data adapter to cycle geometry. |

### Falsifiers and wrong turns

- Player relabeling alone is insufficient; the action must include the full
  edge labels and continuation fiber and must intertwine every block map.
- Word transport reduces validation to group orbits but cannot generate a
  missing edge, chart, repair relation, or strategic decoder.
- Rotation of positions in one word is not the same action as relabeling all
  its letters.  The based composites of cyclic rotations need not be
  conjugate through a block map unless that block map is invertible.
- Passing to an orbit quotient before retaining stabilizers and provenance can
  identify strategically different certificates.

### Production map

```text
edge/fiber action + one-block intertwining -> whole-word transport [X]
unique periodic lift + word stabilizer ----> fixed-point stabilizer [X]
resolved strategic atlas ------------------> required full action   [?]
word-orbit representative -----------------> all orbit validations  [?]
```

### Exit conditions

- Upgrade EWT1--EWT4 to `M` only after independent mathematical audit.
- Mark `MINED` when an audited actual-data adapter either lands the small
  theorem surface or shows that existing equivariance APIs already subsume it.
- Mark EWT5 `WRONG` for a proposed action if any mandatory certificate label
  is not transported or any block square fails to commute.
- Mark `PARKED` if no current resolved component has a nontrivial
  automorphism group.

## 1. Word action

Let a group `Gamma` act on a type `E` of fully labelled block edges and a
fiber `X`.  For `g : Gamma` and a word

```text
w = [e_0, ..., e_(n-1)],
```

define

```text
g.w = [g.e_0, ..., g.e_(n-1)].
```

The pointwise laws immediately give

```text
1.w = w,
(g*h).w = g.(h.w).
```

Thus words inherit the group action without quotienting their labels.

## 2. Intertwining finite block composites

Give each edge a predecessor map `T_e : X -> X`.  Assume the one-block square
commutes:

```text
T_(g.e)(g.x) = g.(T_e(x)).                 (2.1)
```

For chronological predecessor composition, put

```text
T_[](x) = x,
T_(e::w)(x) = T_e(T_w(x)).
```

### Theorem 1: word transport

For every finite word,

```text
T_(g.w)(g.x) = g.(T_w(x)).                 (2.2)
```

### Proof

Induct on the word.  The empty case is the identity action.  For `e::w`, use
the induction hypothesis inside the outer block, then apply (2.1):

```text
T_(g.e)(T_(g.w)(g.x))
  = T_(g.e)(g.(T_w(x)))
  = g.(T_e(T_w(x))).
```

No inverse for `T_e` is used.  Equivalently, because the action map `A_g` is
invertible, (2.2) may be written

```text
T_(g.w) = A_g o T_w o A_(g^-1).
```

The conjugating maps are the game automorphisms, not inverses of the block
maps.

## 3. Periodic fixed points and stabilizers

If `T_w(x) = x`, (2.2) gives

```text
T_(g.w)(g.x) = g.x.
```

Thus one periodic fixed point transports to every word in its group orbit.
Suppose additionally that `g.w = w` and `T_w` has a unique fixed point `x`.
Then `g.x` is another fixed point of the same word, so uniqueness forces

```text
g.x = x.
```

This is the precise stabilizer mechanism needed by an equivariant selection:
uniqueness can provide stabilizer invariance rather than requiring it as
separate data.

## 4. Equivariant acceptance tests

Let `Accept(w,x)` contain the transported chamber, payoff-cap, terminal-label,
and scale/provenance checks.  If

```text
Accept(w,x) -> Accept(g.w,g.x),
```

then validating one representative fixed point validates its entire word
orbit.  This is only a reduction in duplicated proof work.  Establishing the
acceptance transport law is the strategic content and must mention every
field retained by the resolved atlas.

## 5. Relation to the two cycle structures

For the graph-directed part of
[`ideas/CycleGeometryResolution.md`](../ideas/CycleGeometryResolution.md),
Theorem 1 transports a supplied periodic code and its lift.  Under strict
contraction, uniqueness supplies the stabilizer conclusion automatically.

For max-affine summaries, the edge data live in a semigroup rather than a
group.  The same induction still transports products because it uses only
associative composition and the external automorphism action.  By contrast,
changing the base point of a cycle rotates the factors; that is a different
operation and cannot generally be expressed by conjugation inside a
noninvertible semigroup.
