# Extended early-obstacle scale and max-plus dynamics

This note completes the finite-dimensional tangent picture developed in
[SelfSimilarityTangent.md](SelfSimilarityTangent.md). The tail anchor is
naturally scaled by opponent-only absorption mass, but the early stopping floor
need not be. Rather than assume a bounded real ratio, the correct totalized
coordinate lives in the extended nonnegative reals.

## 1. Positive early excess

For a max-affine stopping map

\[
D(w)=\max\{A,T+\chi w\}
\]

and target `v`, define

\[
e^+(D,v)=\max\{0,A-v\}.
\tag{1.1}
\]

This discards negative early slack but retains exactly what matters to target
safety:

\[
e^+(D,v)=0
\quad\Longleftrightarrow\quad
A\le v.
\tag{1.2}
\]

Let the tail absorption mass be

\[
n=1-\chi.
\]

The scaled positive early excess is

\[
\Xi(D,v)=
\frac{\operatorname{ofReal}(e^+(D,v))}
     {\operatorname{ofReal}(n)}
\in[0,+\infty].
\tag{1.3}
\]

Division is the totalized division of `ℝ≥0∞`.

## 2. Exact interpretation of the boundary values

**Status: Lean-checked in this PR.**

The extended coordinate has three exact meanings.

### Safe

\[
\Xi(D,v)=0
\quad\Longleftrightarrow\quad
A\le v.
\tag{2.1}
\]

This remains true at `n=0`: a safe neutral obstacle gives `0/0=0` under the
chosen totalized convention.

### Finite scaled violation

When `n>0`, `\Xi(D,v)<+\infty`. A positive finite value is precisely an early
violation whose size is comparable to tail absorption mass.

### Unsafe neutral face

For `n\ge0`,

\[
\Xi(D,v)=+\infty
\quad\Longleftrightarrow\quad
n=0\text{ and }A>v.
\tag{2.2}
\]

Thus infinity is not a failure of compactness. It is the correct boundary
point for a positive early stopping obstacle surviving on a neutral tail face.

## 3. Extended tangent compactness

**Status: Lean-checked in this PR.**

The bounded tangent core of an actual finite block retains, for every player:

- prescribed absorption mass;
- prescribed conditional anchor;
- raw early stopping floor;
- tail absorption mass; and
- conditional tail anchor.

The new extended coordinates adjoin `\Xi_i(D,v)\in[0,+\infty]` for every
player. Since `ℝ≥0∞` is compact, the product remains compact. Therefore every
sequence of actual finite blocks has a subsequence along which all these
coordinates converge simultaneously.

This improves the earlier statement in one important way: no boundedness
assumption on `(A_i-v_i)/(1-\chi_i)` is needed. A divergent positive ratio
converges to infinity and remains visible.

The theorem is still only coefficient compactness. It does not establish
closedness of:

- the complete quit-time obstacle;
- continuation identity;
- the conditional marked packet;
- entry-measured debt;
- chronological splice data; or
- strategic repeatability.

## 4. Max-plus tangent dynamics

At positive scale `m`, the finite block tangent from
`SelfSimilarityTangent.md` has the limit operator

\[
F_{\alpha,\beta}(x)=\max\{\alpha,\beta+x\},
\tag{4.1}
\]

where

\[
\alpha=\text{early drift},
\qquad
\beta=R-v=\text{tail-anchor drift}.
\]

The PR formalizes nonempty iteration of this operator and proves a complete
sign trichotomy for `\beta`.

### Negative tail drift

If `\beta<0`, then for every initial `x`, finitely many iterations reach the
constant early projector:

\[
F_{\alpha,\beta}^{\,k}(x)=\alpha
\quad\text{for all sufficiently large }k.
\tag{4.2}
\]

More precisely, for `k\ge1`,

\[
F_{\alpha,\beta}^{\,k}(x)
=
\max\{\alpha,k\beta+x\}.
\tag{4.3}
\]

### Zero tail drift

If `\beta=0`, then one application already gives the idempotent threshold
closure

\[
F_{\alpha,0}^{\,k}(x)=\max\{\alpha,x\}
\quad(k\ge1).
\tag{4.4}
\]

### Positive tail drift

If `\beta>0`, then

\[
F_{\alpha,\beta}^{\,k}(x)\ge k\beta+x,
\tag{4.5}
\]

so the iterates exceed every finite budget.

This is the rigorous relevant/marginal/irrelevant classification:

- positive drift is a pumping obstruction;
- zero drift is the recurrent threshold idempotent; and
- negative drift collapses to an early projector.

## 5. Strategic interpretation

At the tangent origin, safety is

\[
F_{\alpha,\beta}(0)\le0
\quad\Longleftrightarrow\quad
\alpha\le0\text{ and }\beta\le0.
\tag{5.1}
\]

The extended coordinate `\Xi` handles the cases where a finite real
`\alpha` does not exist. In particular:

- `\Xi=0` records the only condition needed from the early branch;
- finite `\Xi>0` records a first-order violation;
- `\Xi=+\infty` records an unsafe neutral face.

A complete nonexistence theorem would still need to transport a positive
finite or infinite tangent obstruction through an actual returning strategic
packet, invariant current, or executable escape. The coefficient dynamics make
the resulting pumping exact once that semantic bridge is supplied.

## 6. Lean declarations

The implementation is split between:

- `QuittingSelfSimilarityEarlyExcess.lean`:
  positive excess, extended scaling, zero/top classifications, and compact
  extended subsequences;
- `QuittingSelfSimilarityMaxPlusDynamics.lean`:
  tangent iteration, linear tail lower bound, negative/zero/positive
  trichotomy, and positive-drift pumping;
- `QuittingSelfSimilarityTangentCompactness.lean`:
  the bounded real tangent core of actual finite blocks.

These are exported through
`GameTheory/Concepts/Stochastic/QuittingSelfSimilarity.lean`.
