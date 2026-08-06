# Self-similarity research program: rates, compactness, and falsifiers

This document continues [SelfSimilarity.md](SelfSimilarity.md). The preceding
note establishes the exact affine/max-affine holonomy algebra, absorbed-mass
normalization, idempotent classification, and realized first-order bounds.
Here the focus is the remaining analytic and game-facing bridge.

## 11. Puiseux and scaling classification

**Status: mathematical theorem once the stated asymptotics exist.**

Suppose a realized family has

\[
1-p(t)\sim d t^a,
\qquad
P_t(v)-v\sim c t^b,
\qquad d>0.
\]

Then

\[
\frac{P_t(v)-v}{1-p(t)}
\sim \frac{c}{d}t^{b-a}.
\tag{11.1}
\]

The exponent comparison gives three regimes:

- `b<a`: normalized residual blows up; the perturbation is relevant;
- `b=a`: a finite nonzero tangent generator survives; the perturbation is
  marginal;
- `b>a`: the residual vanishes at this scale; pass to a later jet.

This gives a concrete role for Puiseux order and lexicographic rank. A leading
term removable by a potential is gauge; a nonzero strategic leading term is a
charge; if it vanishes, the order increases and supplies rank descent.

For multiple playerwise scales, one should retain the projective ratios of
`m_i`, `n_i`, and any early-obstacle scale. Ratios tending to zero or infinity
belong to different boundary strata rather than one Euclidean tangent chart.

---

## 12. Big Match as a neutral fixed point

**Status: existing Lean facts plus interpretation.**

The exact two-stage Big-Match live cycle returns to the live physical state and
has zero target debt at `(1/2,-1/2)`. Its prescribed payoff holonomy is neutral.

This does not make the successful strategy periodic. The deficit/account
coordinate changes, and the stopping hazard depends on that scale. A linear
running-deficit index gives harmonic-order hazards and fails; the
Blackwell--Ferguson nonlinear account gives square-order hazards and succeeds.

In renormalization language, the live cycle is a marginal physical fixed point.
The account is the missing scale coordinate, and the hazard exponent decides
whether repeated neutral returns have finite or infinite cumulative cost.

This is exactly why physical self-similarity is too weak and why tangent data
must include the controller/account dynamics.

---

## 13. The strategic idempotent theorem one would like

**Status: open target.**

A useful producer theorem would not say merely that some coefficient subsequence
converges. It would say that a uniform-equilibrium construction supplies, at
every accuracy, a realized enriched block in one of two regimes.

### Contracting return

There is a complete semantically repeatable block with total contraction bounded
away from one and with seam residuals controlled relative to the contraction
defect. Existing periodic and pullback compilers can then absorb the seam.

### Tangent return

The survival defects tend to zero, the normalized prescribed and tail anchors
converge, the scaled early obstacles are bounded, and the complete marked
entry/exit packets converge in a strategically closed topology. The limiting
max-plus generator satisfies the target safety inequalities.

### Escape or descent

If neither return exists, the failure must yield an observable positive charge,
a bounded surgery lowering root debt, or strict finite-rank descent. Mere
unbounded calendar length is not itself a contradiction.

A concise target is:

> **Strategic self-similarity / escape alternative.** Every positive-debt
> plateau has either a contracting admissible return, an admissible tangent
> return, or a positive-work escape that yields a cutoff-independent descent.

No proof of this statement is claimed.

---

## 14. Conditional pumping criterion for nonexistence

**Status: conditional theorem.**

Assume there is a fixed finite block `B` of length `L` whose complete strategic
packet returns exactly to itself and which is executable repeatedly. Suppose
for some player the prescribed or unilateral excess over target is `c>0` per
copy, measured at the returning packet.

After `n` copies, exact concatenation gives excess `nc`; the elapsed calendar
length is `nL`. Hence the average excess is `c/L`, independent of `n`. No
uniform-equilibrium certificate with smaller error can use that returning
packet.

The coefficient pumping theorem proves the algebraic part. The hypotheses
that the packet returns, the block is repeatable, and coefficient excess equals
actual strategic excess are the game-facing obligations.

An approximate version requires seam error `o(1-p)` in the contracting regime,
or a summable sequence of normalized seam errors. Raw seam convergence alone
is insufficient.

---

## 15. Compact semigroups and their exact limitation

**Status: conditional theorem.**

If complete enriched realized block semantics formed a compact Hausdorff
right-topological semigroup under chronological composition, compact semigroup
theory would provide an idempotent. The classification above would then make
its coefficient projection extremely rigid.

The premise is not established:

1. the finite-dimensional coefficient box is compact, but the subset realized
   by actual arbitrary-length blocks is not known closed;
2. forgetting the source chain loses product-root compatibility and chronology;
3. retaining literal natural-valued length in a compact lift forces a uniform
   length bound;
4. adjoining a point at infinity does not provide an executable strategy;
5. obstacle, mark, debt, and splice semantics still need closedness and two
   decoders.

Therefore “compact coefficients imply a strategic idempotent” is a false proof
step. The idempotent route becomes valid only after the enriched semantic
semigroup is constructed.

---

## 16. The finite enriched self-similarity packet

**Status: open formalization target.**

The first responsible next object is finite. For every calibrated finite
block, retain:

- the complete source Nash--Bellman path;
- entry and exit dynamic-debt points;
- owner and all playerwise survival clocks;
- prescribed and best-response holonomy;
- every quit-time payoff and the complete Snell obstacle, including Never;
- the conditional marked terminal packet and its transported mass separately;
- chronological splice/rebasing identities;
- a chosen scale stratum for prescribed, tail, and early-obstacle defects.

The tangent projection should then be a proved map from this finite packet,
not the definition of the packet itself.

Only after exact finite recovery and concatenation theorems are established is
it meaningful to choose an infinite topology.

---

## 17. Computational program

The new algebra turns self-similarity into finite exact tests once a support
chart and scale stratum are fixed.

### 17.1 Strict-contraction charts

Solve

\[
B_i=(1-p_i)v_i,
\qquad
A_i\le v_i,
\qquad
T_i\le(1-\chi_i)v_i,
\]

together with actual root realization and seam constraints. Quantify the
condition number `1/(1-p_i)` and reject seams whose residual is not small at
that scale.

### 17.2 Tangent charts

Introduce absorbed masses and normalized anchors. Solve the limiting affine
and max-plus inequalities, retaining projective scale ratios. Puiseux
elimination can decide which leading stratum is active.

### 17.3 Negative certificates

A counterexample route would certify a uniform positive normalized obstacle:
for every realized recurrent chart, some player has either

\[
\frac{P_i(v_i)-v_i}{1-p_i}>c,
\]

or

\[
\max\left
\{
\frac{A_i-v_i}{\text{early scale}},
\frac{T_i-(1-\chi_i)v_i}{1-\chi_i}
\right\}>c,
\]

with the zero-denominator faces treated by the neutral normal forms. A sound
repeatability or current-or-escape theorem would turn that finite certificate
into nonexistence.

### 17.4 Positive certificates

If admissible contracting or tangent charts are dense in the payoff table,
fixed-skeleton reward closure can settle their boundary tables without taking
limits of strategies.

---

## 18. What this changes

The escaping middle is not merely “a block whose length tends to infinity.”
At coefficient level it is a sequence approaching the identity. The existing
weighted bounds show that its meaningful first-order data remain bounded after
dividing by absorption mass.

This yields a more precise research question:

> Is the complete enriched strategic block compact after blowing up its neutral
> holonomy faces by the relevant absorption and obstacle scales?

A positive answer must still provide both strategic decoders. A negative
answer should exhibit two finite families with the same blown-up coefficient
limit but incompatible obstacle, mark, debt, or splice semantics.

The contribution of the present layer is to remove ambiguity about the algebra:
which residuals compose, which normalization is forced, what repeats pump, and
what idempotents can look like are now exact finite statements. The remaining
uncertainty is semantic realization and compactness, not the coefficient
calculus.
