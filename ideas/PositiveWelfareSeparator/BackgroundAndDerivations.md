# Positive welfare separation from failed repair

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `PENDING` |
| Verdict | `OPEN` |
| Objective priority | `P2` |
| Last audited | 2026-08-03, through `bf65314` |
| Central live claim | Robust failure of all certified boundary repairs can be lifted to a strictly positive separator of the global occupation polytope, whose LP dual is a bounded all-profile Bellman welfare ceiling saturated by singleton security floors. |
| Next discriminant | Either construct the lift to the occupation polytope with a strictly positive normal, or exhibit a small table whose local repair separators necessarily have mixed signs or fail globally. |
| Production destination | Weighted security--welfare assembly (`81aec6c`) via the Bellman-bias source (`bf65314`). |
| Supersedes / superseded by | Split from the mined coalition-assembly group; no successor. |

## Claim ledger

| ID | Exact claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- | --- |
| WS1 | Positive one-sided security floors plus a uniform positive weighted welfare cap imply a uniform-equilibrium payoff. | `PROVED` | `M+L+C` | Finite stochastic games, all behavioral profiles. | Semantic uniform-equilibrium theorem. |
| WS2 | A bounded universal weighted Bellman bias gives the required cap with error `2*C/T`. | `PROVED` | `M+L+A+C` | The bias is supplied; its existence is not automatic. | WS1. |
| WS3 | Robust nonintersection of quitting repair-acceptance polyhedra yields such positive weights and a global bias. | `OPEN` | `I` | Must hold against every behavior profile, not only one continuation cell. | WS2 then WS1. |
| WS4 | For a finite controlled transition system and fixed weights, a ceiling on every invariant occupation measure is equivalent by finite LP duality to an actionwise bounded Bellman-bias inequality. | `PROVED` | `M` | The weights are supplied; strict positivity and the lift from repair failure are not included. | WS2. |

## Falsifiers and wrong turns

- Ordinary separation of a finite continuation cell is insufficient if its
  multipliers have zero/negative player components or if the inequality fails
  outside that cell.
- Even compact convex strong separation need not admit a positive normal. For
  \(C=\operatorname{conv}\{(1,0),(0,1)\}\) and
  \(v=(0.4,0.4)\), every \(\alpha\gg0\) satisfies
  \(h_C(\alpha)=\max(\alpha_1,\alpha_2)>\alpha\cdot v\). The separating
  direction points the wrong way for a welfare ceiling.
- Separately feasible singleton security profiles do not glue without the
  common ceiling.
- A small rational quitting table with robust local nonintersection but no
  positive global Bellman separator would mark WS3 `WRONG` while leaving WS1
  and WS2 intact.

## Production map

```text
failed certified repairs
        -> positive separator of invariant occupation measures       [?]
        -> bounded actionwise Bellman bias by finite LP duality       [M]
        -> uniform all-profile welfare cap                           [L]
singleton security floors + cap
        -> uniform-equilibrium payoff                                [L+C]
```

The first arrow is the entire open idea. Do not call a Farkas certificate on
one finite cell a game-level separator. For the prefix max-affine inequalities,
nonnegative combinations of the two branch normals have payoff coefficient

\[
-P\lambda_Q+(\chi-P)\lambda_C,
\]

which can have either sign. Positivity is therefore an additional theorem,
not a consequence of Farkas duality.

For clarity, the valid LP waist is as follows. Given finite states, finite
joint actions, transition kernel \(P\), vector reward \(r\), target \(v\), and
fixed \(\alpha\gg0\), let \(\Omega\) be the invariant occupation-measure
polytope. Then

\[
\sup_{\mu\in\Omega}
\sum_{s,a}\mu(s,a)\,\alpha\!\cdot\!(r(s,a)-v)\le0
\]

is equivalent to existence of a bounded state function \(B\) satisfying

\[
\alpha\!\cdot r(s,a)+\sum_{s'}P(s'\mid s,a)B(s')
\le \alpha\!\cdot v+B(s)
\]

for every state and joint action. This is finite average-reward LP duality.
What remains open is obtaining its premise, with \(\alpha\gg0\), from failed
strategic repair. Separation of a nonconvex attainable-tail set from one prefix
polyhedron does not do so, and it does not supply the one-sided security floors
needed by WS1.

## Exit conditions

- `MINED` if WS3 is proved and adapted, or refuted by an exact table while its
  strongest surviving restricted version is recorded.
- `PARKED` if no natural source supplies positive weights or an all-profile
  inequality after the current quitting repair analysis.
- WS3 becomes `WRONG` on an exact local/global separation counterexample.
- `SUPERSEDED` if the quitting producer closes without any separation branch.
