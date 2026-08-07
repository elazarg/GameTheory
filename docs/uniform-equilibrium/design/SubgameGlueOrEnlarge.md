# Proper-subgame gluing or support enlargement

**Status:** focused mathematical design target; the estimates below are not yet
production theorems.  
**Scope:** a proposed adapter from a solution on a proper player set to either a
full-game terminal approximate equilibrium or explicit support-enlargement data.

The main branch already separates producers from compilers and already tracks
proper-subgame/LCP preprocessing, blocker designation, exact instant
punishment, support-witness paths, and face circulations.  The missing addition
is not another research taxonomy.  It is a theorem that makes failure of
subgame reinsertion produce the next active player or coalition.

## 1. Quantitative outsider bound

Let `J` be a proper subset of the players.  Suppose players in `J` follow a
terminal quitting profile and every outsider always Continues.  Fix an outsider
`i ∉ J` and condition on survival to stage `t`.

Write:

- `a_t` for the conditional probability that some insider quits at stage `t`;
- `S` for the nonempty insider coalition conditional on such absorption;
- `V_i(t+1)` for outsider `i`'s continuation payoff after everybody Continues;
  and
- `M` for a common absolute bound on terminal rewards.

If outsider `i` quits at stage `t`, its Quit-minus-Continue difference is

```text
(1 - a_t) * (r_i({i}) - V_i(t+1))
  + a_t * E[r_i(S ∪ {i}) - r_i(S) | S ≠ ∅].
```

Therefore, if every suffix satisfies

```text
V_i(t+1) ≥ r_i({i}) - eta,
```

then

```text
QuitGain_i(t) ≤ eta + 2 * M * a_t.                 (1)
```

In particular, if `sup_t a_t ≤ delta`, every deterministic quit-time deviation
of outsider `i` gains at most

```text
eta + 2 * M * delta.                               (2)
```

The repository's pure-quit-time/Never extremality theorem should then lift (2)
to every behavioral deviation of `i`.  Insider deviations are unchanged,
because outsiders never quit.  This gives the candidate full-game estimate

```text
subgame error
  + max_{i ∉ J} (eta_i + 2 * M * delta).            (3)
```

The continuous atomless case is the exact limit `a_t = 0`: suffix domination
of every outsider's solo payoff is enough to reinsert all outsiders by Never.
For discrete plans the atom term is load-bearing; it prices profitable joining
of an insider absorption event.

## 2. The useful contrapositive

A failed gluing theorem should not return only “the subgame does not extend.”
It should identify one of two concrete causes.

### Low-atom failure: entering outsider

If all insider atoms are small but outsider `i` has a robust profitable quit
time, then some suffix must satisfy

```text
V_i(t+1) < r_i({i}) - eta.
```

The player `i`, the suffix `t`, and this strict solo-versus-continuation
inequality are the support-enlargement payload.

### Atomic failure: profitable joiner

If the obstruction is concentrated at a positive insider atom, retain the
coalition `S` and the sign of

```text
r_i(S ∪ {i}) - r_i(S).
```

A positive sign says that the outsider should enter the same absorption event,
not merely start a second time scale elsewhere.

Thus the desired adapter has the shape

```text
proper-subgame profile
  -> full-game approximate profile
   | entering outsider with a failed suffix inequality
   | profitable joiner with a marked absorption coalition.
```

## 3. Exact two-owner local pivot

The smallest support-enlargement calculation is explicit.  Let only players
`i` and `j` be allowed to quit at one root, with probabilities `x` and `y`, and
let `w` be the continuation value.

Player `i`'s Quit-minus-Continue difference is

```text
D_i(y) =
  (1 - y) * (r_i({i}) - w_i)
    + y * (r_i({i,j}) - r_i({j})).                  (4)
```

Similarly,

```text
D_j(x) =
  (1 - x) * (r_j({j}) - w_j)
    + x * (r_j({i,j}) - r_j({i})).                  (5)
```

Whenever both affine functions cross zero on the unit interval, there is an
explicit product root.  In the strict nondegenerate case,

```text
y* = (w_i - r_i({i})) /
     (w_i - r_i({i}) + r_i({i,j}) - r_i({j})),      (6)
```

and analogously for `x*`.

The endpoint signs already classify the boundary outputs:

- profitable solo preemption;
- profitable joining of the other owner;
- sure exit or Never;
- support deletion; or
- a strict inequality suitable for a separator or rank-descent argument.

A usable theorem must also retain every outsider inequality and the target or
continuation data.  Equations (4)--(6) solve owner indifference only; they are
not by themselves a complete strategic root.

## 4. Integration with the existing branch

This adapter is useful only through already tracked work:

1. a principal-subgame or LCP preprocessor supplies `J` and its solution data;
2. the gluing estimate either reinserts outsiders or identifies the first
   entering player/coalition;
3. exact instant-punishment and sure-exit results consume boundary cases;
4. multi-owner root or support-pivot work consumes enlargement cases; and
5. recurrent support data may then feed the existing support-witness or
   face-circulation compilers.

The most direct neighbouring project items are the Solan--Solan Q-matrix
preprocessor audit, general blocker designation, the inexpensive repair ladder,
and arbitrary-weight face-circulation certificate production.  This page does
not change their status or priority; it identifies a concrete missing arrow
between them.

## 5. Acceptance and falsification

A production result should provide:

- the exact repository strategy and suffix conventions;
- inequality (1) with the correct conditioning and reward bound;
- the lift from deterministic quit times and Never to arbitrary behavioral
  deviations;
- preservation of insider incentives under reinsertion;
- a finite marked failure payload when the estimate cannot close; and
- one named downstream consumer for every failure case.

A counterexample showing that suffix domination plus small atoms is
insufficient under the repository's behavioral semantics would refute this
adapter and should be retained as a permanent boundary.  Failure of the
adapter would not refute the quitting-game conjecture.
