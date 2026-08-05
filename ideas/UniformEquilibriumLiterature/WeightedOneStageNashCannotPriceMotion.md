# Weighted one-stage Nash cannot price motion

| Status | Provenance | Consumer | Falsifier |
| --- | --- | --- | --- |
| `OPEN`, maturity `L` (separation, no-motion-price) / `M [reported]` (the absence proofs), P0 | Q159 §§1–2; `WeightedRowMotionSeparation.lean` | every use of Lemma-5-type bounds; the Q158 discharge gate; `MATH-P0-9` | an error in the (machine-checked) tremble computation |

**Machine-checked**: the weighted condition as mixture-`ε`-optimality, the
one-directional conversion, the tremble membership and motion computations at
the scaled cyclic weight (every constant reproducing), support-perfection
failing below `1/9`, and the theorem `no_motion_price_scaledCyclicWeight` —
no positive `ρ` prices motion by quit mass on the weighted correspondence.
The §2.1 absence proofs (no stationary, no instant families) remain
`M [reported]`; the separation theorem does not depend on them.

## The separation

The one-stage `ε`-Nash notion defined by mixture deviations is **weighted**:
for player `i` with action difference `D_i` (stop minus continue against the
continuation), membership means `(1−x_i)·D_i ≤ ε` and `−x_i·D_i ≤ ε`. The
**support-perfect** condition — `x_i > 0 ⟹ D_i ≥ −ε`, `x_i < 1 ⟹ D_i ≤ ε` —
is strictly stronger, and passing from the first to the second requires
dividing by a hazard, unavailable at small trembles. This is the `ε`-bridge
one-directionality (K7) striking at the foundations rather than at a
technicality.

## The counterexample

At the standard cyclic three-player weight scaled by `1/3` (so `M = 1`),
which has **neither stationary nor instant approximate equilibria** (both
proved in the answer), take the rational feasible vector `r* = (4/9,4/9,4/9)`
and the symmetric tremble row `x(t) = (t,t,t)`. Then every `D_i < 0`, the
only profitable deviation is reducing one's own hazard, and its weighted gain
is `≤ t/3` — so `x(t)` is weighted-`ρ`-Nash for `t ≤ 3ρ` — while the motion
per quit mass is `≤ 2t/3 → 0`. **No constant `ρ` can satisfy the motion
lower bound `ρ·q ≤ ‖r − f(r,x)‖` on the weighted correspondence.** The same
two vectors give a length-one rational feasible orbit violating the
quit-mass-to-variation lower bound.

So (K1)-as-transcribed is false, and with it the claimed equivalence of
divergent quit mass and unbounded variation on weighted orbits. The
**upper** half — motion `≤ 2M·q` — survives unconditionally.

## What is and is not implicated

- **Not implicated**: the Q158 window repair itself (the answer states this
  explicitly), and the Lean landing chain, which takes the continue-mass
  bound as a named hypothesis.
- **Implicated**: the *discharge* of that hypothesis from the published
  Lemma 5(2), which is now doubly gated: the lemma must be read on the
  support-perfect correspondence (on the weighted one, this counterexample
  plus the absence proofs contradict it), **and** the reached-stage transfer
  delivers only weighted membership at reached stages — support-perfect
  membership does not follow by scaling. A support-purification step, or a
  restatement of the ambient argument on the support-perfect correspondence,
  is genuinely missing.
- **My inference, to verify, beyond the answer**: the published proof's
  case (a′) — "one-shot `ε`-equilibrium at own stationary value, `ε`
  arbitrary, gives stationary approximate equilibria" — is exactly where the
  weighted reading breaks, since per-stage weighted gains amplify by the
  number of live stages under repetition (the tremble row repeated is *not*
  a game `ε`-equilibrium: never-quitting gains order one). If confirmed,
  this is a new defect-register entry, deeper than №13.

## Consequence for the program

Every motion/orbit argument must state which correspondence it lives on. The
valid formulations of the open core are: support-perfect throughout (where
the granted constant is plausible but membership transfer from global
equilibria is unproven), or weighted throughout (where quit mass and
variation genuinely decouple). The dichotomy axis of the original Q159 Part A
is wrong as posed; the missing branch is strict local continuation rests
with diffuse trembles.
