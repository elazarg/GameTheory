# Pure Nash equilibria of harmonic games are flat

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `PROVED`, maturity `M` | Proof-mining §37, extracted 2026-08-03 | Target: companion to `Potential/Harmonic.lean` | `INDEPENDENT` |

At every pure profile of a finite harmonic game, the sum of all unilateral
deviation flows is zero. At a pure Nash profile each flow is nonpositive.
Finiteness therefore forces every flow to be exactly zero:

\[
  IsHarmonic(u)\land IsNash_u(\sigma)
  \Longrightarrow
  \forall i,a_i',\; flow_u(\sigma,i,a_i')=0.
\]

Every player is indifferent among all unilateral actions against the
opponents' equilibrium actions. Hence a harmonic game with a player having a
nontrivial action set has no strict pure Nash equilibrium; if every profile has
some strict unilateral comparison, it has no pure Nash equilibrium.

This concerns pure equilibria and the repository's flow sign convention. It
does not say that every action is in the support of a mixed equilibrium. The
proof is complete; only library packaging remains. The observation may be
folklore in harmonic-game theory, so novelty is not claimed.
