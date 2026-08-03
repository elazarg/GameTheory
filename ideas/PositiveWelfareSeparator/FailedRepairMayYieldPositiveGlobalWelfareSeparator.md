# Failed repair may yield a positive global welfare separator

| Status | Provenance | Formalization | Next discriminant |
| --- | --- | --- | --- |
| `OPEN`, maturity `I`; downstream duality `M+L` | Q133 convex audit and proof-mining repair failure lane | Bellman-bias consumer landed; producer absent | small exact table comparing local and global separator signs |

If every certified boundary repair fails robustly, seek weights
`α_i>0` and a bounded Bellman bias `B` such that every joint action satisfies

\[
\alpha\!\cdot r(s,a)+E[B(s')\mid s,a]
\le \alpha\!\cdot v+B(s).
\]

Together with one-sided security floors at `v`, this all-profile welfare
ceiling implies a uniform-equilibrium payoff. For fixed positive `α`, finite
occupation-measure LP duality exactly equates the invariant-occupation ceiling
with such a bias.

The open arrow is obtaining `α >> 0` from failed **local** repair. Ordinary
Farkas separation can have mixed signs and may hold only on one continuation
cell; neither gives a global welfare normal. A small table where every local
separator has a nonpositive coordinate or fails on another occupation measure
would refute the general claim and identify its maximal valid subclass.
