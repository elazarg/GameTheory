# Mathematical Research Method for Uniform Equilibrium

## Scope

This document describes how to conduct the mathematical research. It contains
no current backlog and makes no claim about which open route is presently most
promising. The changing theorem boundary is recorded separately in
`ephemeral/UniformEquilibriumCurrentFrontier.md`.

## Start from the semantic deficit

Each investigation begins by identifying what is missing from the semantic
uniform-deviation-cap constructor. Typical deficit types are:

- payoff delivery;
- unilateral-deviation safety;
- legal public entry;
- complete-vector target transport;
- recursive progress or account discharge;
- compilation across stopping or rebasing.

Atlas labels, analytic coefficients, separators, and implementation records
are evidence about a deficit; they are not themselves the deficit.

## Separate soundness from expressiveness

For every proposed proof language, ask independently:

1. **Soundness:** does the proposed certificate imply the semantic conclusion?
2. **Expressiveness:** can it represent the stochastic cancellation, stopping,
   target transport, and strategic response needed by the intended class?

A sound but restrictive certificate is a valid special-case theorem. It is not
a universal normal form without a completeness proof.

Also separate three increasingly strong questions:

1. verification of one supplied architecture;
2. synthesis or obstruction within a fixed bounded class;
3. coverage of every semantic payoff by that strategy class.

The first may be exact and decidable while the third is false or open. Record
the strategy model, memory visibility, clock dependence, and size/accuracy
quantifiers at every transition between these questions.

## Treat probability mode as mathematical data

The position of expectation, absolute value, conditioning, supremum, and
stopping is part of the theorem. In general,

\[
|\mathbb E X|,\qquad
\mathbb E|X|,\qquad
\mathbb E[X\mid\mathcal F_\tau],\qquad
\sup_\tau\mathbb E X_\tau
\]

are inequivalent. A proof may move to a stronger mode only by an explicit
theorem.

Keep stochastic cancellation and strategic debt conceptually distinct.
Signed or martingale-like terms may cancel in the expectation used by the
verifier. Nonnegative debt and punishment obligations generally cannot.

A current-stage payoff loss is not by itself strategic debt. Continuation gain
and bias may make a stagewise non-best reply dynamically optimal. Conversely,
a floor or minmax bound does not prove that a responder has no profitable
complete unilateral strategy against the proposed continuation. Credibility
is evaluated against that complete strategy, from every claimed entry
history, in the probability mode used by the semantic waist.

## Expose agency and information

For every action, random choice, stopping rule, and target coordinate, state:

- who chooses it;
- what is publicly observed;
- what one deviator can change;
- whether the randomization belongs to the base game or must be synthesized;
- which history filtration makes the object adapted.

An argument that uses stronger information or correlation than the model must
either construct it or state it as a special-case assumption.

## Require concrete consumed outputs

A local theorem becomes strategically useful when it outputs a concrete
profile, terminal system, credible continuation, discharged account, or
strictly lower child with a complete target bridge.

A separator, detector, circulation, failed gate, or mismatch is intermediate
evidence until another theorem consumes it. Negative alternatives should be
typed so that a claimed exhaustive proof cannot silently discard them.

## Prove progress intrinsically

Recursive identity and rank must not depend on arbitrary bases,
enumerations, or presentations. Rebased nodes representing the same strategic
obligation must compare coherently. Discharged debt may not be recreated by a
restart. Same-rank plateaux close as terminal outputs or require a stronger
well-founded measure.

## Research cycle

1. State one self-contained mathematical question.
2. Test it on the smallest positive and negative examples available.
3. Try to prove the exact statement, not a nearby interface-shaped version.
4. If false, identify the minimal failed implication and strongest surviving
   theorem.
5. Record quantitative constants and all quantifier orders.
6. Identify a concrete adapter and consumer before claiming conjecture-facing
   progress.
7. State whether the result is verification, bounded synthesis, or
   strategy-class coverage.
8. Package the proof or counterexample for independent checking and Lean.

## Result classification

Record a result as one of:

- unconditional construction;
- conditional construction;
- exact equivalence or characterization;
- impossibility or counterexample;
- semidecision, viability, or approximation theorem;
- supporting structure with no current consumer.

Do not turn a semidecision into a decision theorem, an approximation into exact
attainment, a conditional compiler into source coverage, or a negative
obstruction into a closed branch.

## Formalization-ready packet

The packet includes the full statement and proof, input/output data,
probability mode, agency model, quantitative bounds, finite tests, dependency
on previous mathematics, and intended adapter and consumer. It is written in
ordinary mathematical language and does not refer to codebase-only names.
For a claimed converse, it includes the full necessity argument rather than a
pointer to an unnamed or unexpanded optimal-control theorem.
