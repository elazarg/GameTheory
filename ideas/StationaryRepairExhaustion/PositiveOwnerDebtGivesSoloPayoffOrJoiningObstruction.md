# Positive owner debt gives a solo payoff or universal joining obstruction

| Status | Provenance | Lean | Next escalation |
| --- | --- | --- | --- |
| `PROVED`, maturity `M+L+C` | E39 | `QuittingOwnerSoloCertification` | pair/set stationary repair or dynamic boundary block |

Positive exact dynamic debt for owner `i` certifies a positive solo reward.
At stationary owner hazard `p>0`, the owner-solo profile is exact terminal Nash
iff every opponent `j` satisfies

\[
(1-p)r_j(\{j\})+p r_j(\{i,j\})\le r_j(\{i\}).
\]

Therefore positive owner debt yields either the solo terminal payoff as a
uniform-equilibrium payoff or a universal joining obstruction: at every
positive owner rate some opponent wants to quit into the owner's exit. This is
a table-checkable one-variable repair test.

The obstruction is not yet a profitable global time-varying deviation and does
not transfer debt to the joining player. It is the input for the next repair
rung—larger quitter sets, pair-stationary certificates, or finite holonomy
blocks.
