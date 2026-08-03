# Cyclic phase signals: Reynolds projection and coboundaries

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `PENDING` |
| Verdict | `MIXED` |
| Objective priority | `P2` |
| Last audited | 2026-08-03, isolated experiments `CyclicPhaseReynolds.lean` and `PhaseLiftedWelfareCap.lean` |
| Central live claim | Scalar cyclic oscillations are exactly bounded phase coboundaries after removing their mean; using this on a game cycle additionally requires an actual phase-state bias certificate. |
| Next discriminant | Exhibit one certified periodic game block whose weighted welfare slack factors through this phase clock, or park the construction as reusable infrastructure. |
| Production destination | Possible adapter to `Math.Probability.SwitchedPotentialCalculus`; none nominated without an actual-data consumer. |
| Supersedes / superseded by | Complements, and does not supersede, `ideas/CycleGeometryResolution/README.md`. |

### Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| CPR1 | Cyclic averaging is the Reynolds projection onto the constant signals. | `PROVED` | `X` | Scalar functions on `ZMod P`. |
| CPR2 | Every scalar cyclic signal is its mean plus `H - shift H`; zero mean is the only obstruction. | `PROVED` | `X` | `CyclicPhaseReynolds.lean`. |
| CPR3 | Every shifted finite window telescopes exactly and a primitive bounded by `C` gives error at most `2*C/T`. | `PROVED` | `X` | Uniform in starting phase and horizon. |
| CPR4 | A phase-state weighted Bellman bias gives the production all-profile welfare-cap predicate with the same endpoint rate. | `PROVED` | `X` | `PhaseLiftedWelfareCap.lean`; isolated adapter to coalition assembly. |
| CPR5 | Fourier modes and peripheral roots of unity classify useful phase-state resonances in the current game certificates. | `OPEN` | `I` | Diagnostic only; no actual certificate adapter or spectral theorem. |

### Falsifiers and wrong turns

- Periodicity of a symbolic word does not by itself produce a scalar
  zero-mean welfare slack or a bounded phase-state bias.
- A phase coboundary controls time averages, not strategic deviations; the
  policy-universal Bellman inequality is still required.
- State-dependent resonant modes need not be pure functions of the clock.
- An endpoint estimate does not solve branch overlap, strategic exhaustion,
  owner transport, or terminal packets at infinity.

### Production map

```text
cyclic scalar signal -> mean + phase coboundary                    [X]
phase-state Bellman inequality -> all-profile welfare cap          [X -> L predicate]
certified split cycle -> suitable phase-state Bellman inequality    [?]
```

The missing arrow is an actual-data producer.  Until it exists, CPR1--CPR4
remain isolated verification infrastructure.

### Exit conditions

- Mark `MINED` if an independently audited adapter identifies the exact
  production theorem surface, or if no current certificate needs more than
  the existing switched-potential calculus.
- Mark CPR5 `WRONG` if a proposed spectral criterion fails on a named finite
  phase-state kernel; the elementary CPR1--CPR4 claims survive.
- Mark `PARKED` if no certified cycle supplies the required bias data.
- Mark `SUPERSEDED` only if an existing production theorem subsumes both the
  exact clock decomposition and the game-facing cap adapter.

## Scope

This note is the phase-analysis component used by periodic game
constructions.  It contains no coalition-specific claims.  Its role in
coalition splitting is stated separately in
[`CoalitionSplittingGroupActions`](../CoalitionSplittingGroupActions/README.md).

In [`CycleGeometryResolution`](../CycleGeometryResolution/README.md),
"periodic" primarily means a periodic word in a resolved graph-directed
system.  Such a word is evaluated by the max-affine block-composition
semigroup.  The cyclic group here is only the clock acting on an already
chosen period.  It neither replaces that semigroup nor produces the compact
exhaustive repair relation or its strategic decoder.

Fix a positive period `P` and write

```text
C_P = Z / P Z.
```

Let `S` denote the cyclic shift on functions `f : C_P -> V`:

```text
(S f)(q) = f(q + 1).
```

Here `V` is initially `R`; every algebraic argument extends to a real vector
space.

## 1. Reynolds projection

Define

```text
R(f) = (1/P) * sum_{q in C_P} f(q).
```

This is the Reynolds projection for the regular action of `C_P`.

### Proposition 1

`R` is linear, `R(Sf) = R(f)`, and `R(R(f)) = R(f)`.  Its image consists
exactly of constant functions.

### Proof

Linearity is linearity of finite sums.  Translation by `1` permutes `C_P`, so
the sum is unchanged.  Applying `R` to the constant function with value
`R(f)` returns that value because there are `P` equal summands.  Conversely,
every fixed point of the regular cyclic shift is constant, since every phase
is reached from `0` by repeatedly adding `1`.  QED.

## 2. Cyclic Reynolds decomposition

Let

```text
c(q) = f(q) - R(f).
```

Then `sum_q c(q) = 0`.

### Theorem 2

There exists `H : C_P -> R` such that

```text
f(q) = R(f) + H(q) - H(q+1)
```

for every `q`.

### Explicit construction and proof

Represent phases by `0, ..., P-1` and put

```text
H(0) = 0,
H(k) = -sum_{j=0}^{k-1} c(j)       for 1 <= k < P.
```

If `k < P-1`, subtraction of successive prefix sums gives

```text
H(k) - H(k+1) = c(k).
```

At the wraparound phase,

```text
H(P-1) - H(0)
  = -sum_{j=0}^{P-2} c(j)
  = c(P-1),
```

because the total centered sum is zero.  Hence `c = H - S H`, which gives the
claim.  QED.

### Corollary 3

For scalar phase signals,

```text
functions(C_P, R)
  = constants direct-sum image(1 - S).
```

The intersection is zero: a constant cyclic coboundary has total sum zero,
so it is the zero constant.  Thus the average is the unique obstruction to
solving `c = H - S H`.

## 3. Exact shifted-window telescope

### Theorem 4

Assume

```text
f(q) = m + H(q) - H(q+1).
```

Then for every natural starting time `a` and horizon `T`,

```text
sum_{t=0}^{T-1} f(a+t mod P)
  = T*m + H(a mod P) - H(a+T mod P).
```

### Proof

Substitute the assumed identity.  The constant terms sum to `T*m`, and

```text
sum_{t<T} (H(a+t)-H(a+t+1))
```

telescopes.  Cyclic indexing makes the identity valid across every wraparound.
QED.

### Corollary 5

If `|H(q)| <= C` and `T > 0`, then uniformly in `a`,

```text
abs ((1/T) * sum_{t<T} f(a+t mod P) - m) <= 2*C/T.
```

This is the exact reason a periodic phase error is harmless for a uniform
long-horizon criterion: it is an endpoint error, not an accumulated error.

## 4. Phase-augmented state potentials

Let `S` now be a finite state type and let `B : C_P -> S -> R`.  Suppose a
controlled process has phase-dependent reward `r_q(s,a)` and satisfies

```text
r_q(s,a) + E[B_(q+1)(s') | s,a] <= g + B_q(s).
```

Summing conditional expectations gives

```text
sum_{t<T} E[r_(a+t)(s_t,a_t)]
  <= T*g + E[B_a(s_0)] - E[B_(a+T)(s_T)].
```

If `|B_q(s)| <= C`, the right endpoint contribution is at most `2*C`,
uniformly in the policy, starting phase, and horizon.  This is the
phase-augmented version of a state Bellman bias.

The repository already contains this controlled-kernel telescope as
`Math.Probability.SwitchedPotentialCalculus.HasPhaseSlack` and
`sum_expect_phaseCost_le`.  What is not yet packaged is its relationship to
the Reynolds decomposition and to stochastic-game weighted welfare.

## 5. Fourier interpretation

After complexification, the regular representation decomposes into the
characters

```text
q |-> exp(2*pi*i*k*q/P),       k = 0, ..., P-1.
```

The shift `S` acts on frequency `k` by a root of unity.  The operator `1-S`
vanishes only on the zero-frequency component.  Therefore:

- frequency `0` is the persistent cycle average;
- every nonzero frequency is a coboundary and contributes only endpoints to
  long averages;
- for a state kernel `K`, phase-state equations involve operators
  `1 - zeta_k K`; roots of unity in the peripheral spectrum of `K` are the
  possible resonances;
- an aperiodic or Doeblin contraction removes those nonzero-frequency
  resonances quantitatively.

The elementary prefix-sum proof is preferable for the first Lean theorem.
Fourier diagonalization becomes useful only when quantitative bounds or
phase-state operators are studied.

## 6. Formalization status

The isolated experiment
`experiments/CyclicPhaseReynolds.lean`
proves:

1. centered phase sums vanish;
2. the explicit prefix primitive satisfies the cyclic difference equation;
3. every scalar phase signal equals its mean plus a cyclic coboundary;
4. shifted finite windows telescope exactly;
5. bounded primitives give the uniform `2*C/T` estimate.

The independent game-facing experiment
`experiments/PhaseLiftedWelfareCap.lean`
proves the policy-universal phase-state Bellman telescope and returns the
production `HasUniformWeightedWelfareCap` predicate.  Both results retain seal
`X`; no certified coalition cycle has yet supplied their hypotheses.
