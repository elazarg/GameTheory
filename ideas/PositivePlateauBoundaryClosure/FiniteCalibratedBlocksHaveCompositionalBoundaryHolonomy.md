# Finite calibrated blocks have compositional boundary holonomy

| Status | Provenance | Lean | Consumer |
| --- | --- | --- | --- |
| `PROVED`, maturity `M+L` | Proof-mining §§79,83; commit `e1fe7dc` | `QuittingBoundaryHolonomy.lean` | Realized-middle compactness/decoder |

Every nonempty block of one selected finite minimizer produces a multiplayer
summary. For each player, prescribed payoff has affine data `(B,P)` and the
arbitrary behavioral cap has max-affine data `(A,T,χ)`:

\[
w_i=B_i+P w_i',\qquad
Cap_i(w_i',\beta_i')=
\max\{A_i,\;T_i+\chi_i(w_i'+\beta_i')\}.
\]

Adjacent blocks compose chronologically and associatively. The calibrated
wrapper retains all source roots, exact-D endpoints, minimizer provenance,
owner, full marked action, and the separated survival/atom packet. Scalar
coefficients lie in one fixed compact product box, and fixed-word cap safety is
two affine inequalities per player.

This is exact finite-block semantics, not a compact repair relation. Projecting
to scalar coefficients forgets the root word and splice admissibility; keeping
the full source preserves them at finite length but leaves an unbounded witness
space. The open object is the set of limits **realized** by arbitrary-length
anchored blocks.
