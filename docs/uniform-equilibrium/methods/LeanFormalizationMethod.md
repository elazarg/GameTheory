# Lean Formalization Method for Uniform Equilibrium

## Scope

This document describes the stable formalization method. It is not a module
backlog. Current mathematical and Lean frontiers are recorded in
[`../FRONTIER.md`](../FRONTIER.md); the detailed historical
inventory is in `docs/uniform-equilibrium/audits/LeanSettlementAudit.md`.

## Preserve the semantic waist

The formal endpoint is the semantic uniform-deviation-cap constructor already
proved equivalent to a uniform-equilibrium payoff. Intermediate certificate
languages are sufficient routes into that constructor, not definitions of the
conjecture unless equivalence is separately proved.

Allow several sound proof languages to coexist. Do not replace a semantic goal
by a stronger certificate merely because that certificate is convenient for a
particular compiler.

## Unit of formalization

A theorem package distinguishes three declarations:

1. **Kernel:** the abstract mathematical theorem.
2. **Adapter:** derivation of its hypotheses from actual source data.
3. **Consumer:** conversion of its output into semantic closure or a valid
   recursive output.

These stages receive separate status. A checked kernel without an adapter or
consumer remains useful checked mathematics but not source coverage.

The package also states which logical level it occupies:

1. soundness for a supplied object;
2. synthesis or finite obstruction in a bounded class;
3. completeness of a strategy class.

Use separate declarations and status entries for these levels. Do not give a
fixed-object verifier a name or docstring suggesting that it constructs an
object for every game or captures unrestricted behavior.

## Readiness rule

Formalize a frontier theorem after its mathematical packet fixes:

- quantifiers and finiteness assumptions;
- randomness, observation, and agency;
- expectation, absolute value, conditioning, and stopping placement;
- prefix, shift, and restart semantics;
- concrete outputs rather than an assumed final certificate;
- positive and negative examples;
- intended adapter and consumer.

An if-and-only-if package is ready only after the necessity direction has been
expanded with the exact reachability, recurrent-class, strategy-observation,
and target-selection hypotheses. It is legitimate to formalize the sound
direction first, provided its one-way scope is explicit.

Stable auxiliary mathematics may be formalized independently when its
statement does not freeze an unsettled strategic interface.

## Interface discipline

### Add rather than rewrite speculatively

Introduce small parallel types and adapters before restructuring established
interfaces. Parameters such as a declared target may be neutral data; the type
must not silently assert attainability, endpoint equality, or semantic closure.

### No hidden conclusion fields

Construction records may contain strategies, trees, stopping rules,
occupations, bridges, ledgers, or rank facts. They may not contain the desired
certificate or semantic theorem as an assumed closer field.

### Falsifier-first testing

Every frontier interface is tested against minimal counterexamples and trivial
witnesses. Whenever practical, make the falsifier a checked theorem. A type
which accepts a forbidden witness is revised before it acquires downstream
users.

### Vertical-slice validation

Freeze strategic interfaces only after one actual source object passes through

~~~text
actual data -> adapter -> concrete local output -> consumer -> sound verifier.
~~~

This tests quantifiers and ownership by use. Exhaustive dispatchers and generic
recursive wrappers come later.

For strategic credibility, the preferred order is:

1. formalize the supplied-object verifier;
2. pass a genuine multiplayer source example through it;
3. prove equivalence with any alternative finite certificate language;
4. formalize necessity and obstruction extraction;
5. only then expose bounded synthesis or strategy-class APIs.

This order does not demote the converse. It prevents the representation chosen
for an early sufficient theorem from silently becoming the definition of all
credible play.

## Build and axiom discipline

Each landed package records its focused build, umbrella build when imports
change, critical declarations, and `#print axioms` result. “No `sorry` in the
new file” is insufficient if the theorem does not compile or inherits a
conjectural axiom.

Preserve unrelated work and isolate refactors from mathematical translations.
Use a stable committed base when the active tree is changing.

## Lean-to-mathematics escalation

Stop implementation when the obstacle is mathematical. Extract one
self-contained question with finite data and the desired conclusion, without
codebase terminology. Include the failed type shape or smallest countermodel.

Classify the obstacle as:

- mathematical falsehood or missing hypothesis;
- missing library theorem;
- representation or elaboration issue;
- integration mismatch with an existing consumer.

Only the first category changes the mathematical frontier. The last may still
show that a mathematically correct theorem has not removed the intended gap.

## Evidence accounting

Use the independent M/L/A/C seals for mathematics, checked theorem, actual-data
adapter, and downstream consumer. LOC, number of modules, interface count, and
conditional compilation are diagnostic information rather than closure
evidence.

Record the seals separately for verification, bounded synthesis, and
strategy-class coverage. “Formalized credibility” without this qualifier is
too ambiguous for the research ledger.
