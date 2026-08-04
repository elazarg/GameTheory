# The zero pin is not a realizable continuation

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `PROVED` at the exhibited weight family; general statement `OPEN` |
| Objective priority | `P0` |
| Last audited | 2026-08-04, `301bb28` |
| Central live claim | For the surgery weight family, no vector `(t,0)` with `0 ≤ t < a` — the zero pin included — is reproduced by any exact cyclic block of any length, so the optimized zero-boundary debt is charged against a boundary the game never realizes. |
| Next discriminant | Whether a positive optimized zero-pinned plateau implies the zero vector is not a self-consistent continuation, in general. |
| Production destination | `QuittingCyclePinnedDebt.lean` (landed) |
| Supersedes / superseded by | none |

## Claim ledger

| Claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- |
| The backward step out of `(t,0)` with `0 ≤ t < a` is forced by exactness and lands on `(a/(1+a-t), 0)` | `PROVED` | `M+L` | surgery weight, `0 < a < 1` | monotonicity below |
| That step is strictly increasing in `t` on `[0,a)` | `PROVED` | `M+L` | as above | no periodic point |
| Hence no `(t,0)` with `t < a` is reproduced by an exact cyclic block of any length, absorbing or not | `PROVED` | `M+L` | as above | the pin diagnosis |
| In particular the zero pin is not an admissible cycle-pinned terminal continuation | `PROVED` | `M+L` | as above | reading of the plateau |
| A positive zero-pinned plateau implies the zero vector is not self-consistent | — | — | general weights | `OPEN`, see below |

## Why it matters

The optimized zero-boundary dynamic debt is a minimization over chains whose
terminal continuation is the zero vector. The companion claims in this group
show the resulting plateau is manufactured by that pin. This claim is the
sharper statement: on the exhibited family the pin is not merely a *bad* choice
of boundary, it is not a *possible* one. No exact block of any length
reproduces it. The plateau is therefore charged against a boundary the exactness
grammar itself forbids, which is the strongest available form of the diagnosis.

Note the strength of the obstruction: it uses only the exactness grammar, not
absorption. Absorption is what makes a reproduced value unique; here even the
unfenced notion has no fixed point of the required shape.

## Proof

For the weight `r({1}) = (a,0)`, `r({2}) = (1,-1)`, `r({1,2}) = (0,1)` with
`0 < a < 1`, exactness forces the row out of a continuation `(t,0)` with
`0 ≤ t < a` uniquely, and the resulting value is `(a/(1+a-t), 0)`. Writing
`u' = a/(1+a-t)`,

    u' > t  ⟺  a > t(1+a-t)  ⟺  (a-t)(1-t) > 0,

which holds for `t < a < 1`. So the backward orbit is strictly increasing on
`[0,a)` and has no periodic point there. A cyclic block reproducing `(t,0)`
would supply one.

## Falsifiers and wrong turns

- The claim is about vectors of the shape `(t,0)`. It says nothing about
  general vectors, and in particular does not assert that the equilibrium value
  `(a,0)` is unreachable — that value *is* realized, at `t = a`, which is the
  excluded endpoint. The strict inequality `t < a` is essential and the
  boundary case is exactly where the equilibrium lives.
- Do not read this as "the zero vector is never self-consistent". For a weight
  with `r ≡ 0` every row reproduces the zero vector, and there is no debt to
  explain. The general question below is the one worth asking.
- Do not read it as a nonexistence statement about the game. The same weight
  has an exact stationary equilibrium; see the companion claims.

## The general question

Does a positive optimized zero-pinned plateau imply the zero vector is not a
self-consistent continuation? A proof would say the plateau is *always* charged
against an unrealizable boundary, and would make the pin diagnosis general
rather than exhibited. A counterexample — a weight with positive plateau whose
zero vector *is* reproduced by an absorbing cycle — would be more interesting
still, since by the mismatch characterization that cycle would have mismatch
`Λ` transported around it, and one could ask directly why the optimizer does
not use it.

## Production map

Landed as `not_isQuittingCyclicContinuation_of_shape` and
`not_isQuittingCyclicContinuation_zero`, built on `edge_forced_of_shape`, which
reuses the existing `root_forced_of_endpointNash`. Missing arrow: the general
statement above has no formalization target yet.

## Exit conditions

`MINED` when the general question is decided either way. Returns to the front
if a weight is found whose zero pin *is* realizable while its plateau is
positive, since that would break the current reading of every plateau result.
