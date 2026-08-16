# D56: MAID information reduction uses semantic deviation coverage

- **Status:** adopted for the semantic seam; graphical discharge remains
  experiment-gated
- **Date:** 2026-08-16
- **Experiment IDs:** EXP-102, EXP-103, EXP-104

## Decision and result

Use `ObservationPruning.CoversFullDeviationsAt` as the boundary between
canonical MAID semantics and any graphical information-reduction package. At
a reduced profile `p`, it requires every full owner-policy replacement to be
weakly dominated, for that owner, by some reduced replacement against the same
opposing profile:

```text
EU_a(expand(p)[a := full]) ≤ EU_a(expand(p[a := reduced])).
```

This is the exact missing obligation at one profile. Full Nash implies both
reduced Nash and coverage; reduced Nash plus coverage implies full Nash. The
same certificate serves native and compiled execution through the existing law
equivalence. It introduces no second policy, utility, evaluator, or equilibrium
predicate.

The graph-only design is rejected. `Structure` stores chance and decision
nodes, while `Semantics.utility` is an arbitrary function of a completed
assignment. Two semantics can share the same graph and chance laws while one
utility ignores a signal and the other rewards matching it. No predicate of
the existing graph alone can safely distinguish them.

An experiment-only proved `UtilityView` survives as a possible graph front end.
It enumerates distinct owner-indexed additive utility terms and proves their
sum equals canonical utility. It is not a public API and currently supplies no
graph-to-coverage theorem.

## Independent criterion and terminology

The independent sources are Koller and Milch,
[*Multi-Agent Influence Diagrams for Representing and Solving
Games*](https://people.csail.mit.edu/milch/papers/geb-maid.pdf) (2003,
Definitions 5.1--5.4 and Theorems 5.1--5.2), and Milch and Koller,
[*Ignorable Information in Multi-Agent
Scenarios*](https://people.csail.mit.edu/milch/papers/tr08-irrelevance.pdf)
(2008, Definition 3.3 and Theorems 3.4 and 5.3).

For decision `D` owned by `a`, let `RelUtils_G(D)` be `a`'s descendant utility
nodes. A set `X ⊆ Pa_G(D)` is graphically ignorable when

```text
d-sep_G(X, RelUtils_G(D) | (Pa_G(D) ∪ {D}) \ X).
```

The source calls this *ignorable*. This repository may call a singleton parent
*requisite* only for the complementary condition. The removed set must remain
set-valued internally because the conditioning set removes all of `X` at once.

Strategic reliance is different. It asks whether changing another decision
`D'`'s rule can change which rule is optimal at `D`, ignoring behavior only at
parent contexts that originally had zero probability. Its graph test adds a
dummy mechanism parent `M[D'] -> D'` and tests an active path to
`RelUtils_G(D)` conditional on `Pa_G(D) ∪ {D}`. A realized observation can be
requisite even when the generating rule is not strategically relevant. The
2003 relevance-graph direction is `D' -> D` when `D` relies on `D'`.

Neither notion is the paper's intermediate *requisite probability node*.

The theorem scopes must also remain separate:

- d-separation gives the sound local ignorability direction without a
  faithfulness assumption;
- s-non-reachability gives absence of reliance in the current parameterized
  MAID;
- s-reachability completeness is existential over parameterizations with the
  same skeleton, not a claim about the current numeric utility; and
- completeness needs nontrivial variable domains. Singleton observations are
  always ignorable and singleton decisions cannot witness reliance.

Local soundness does not require recall. Combining local removals into the
2008 global safe-pruning fixpoint needs its sufficient-recall condition. Even a
safe reduction may discard original equilibria, including Pareto-preferred
ones; safety is only reduced-Nash-to-full-Nash inclusion.

## Competing designs

1. Infer safety from the existing chance/decision graph alone.
2. Attach a proved utility-dependence view and run d-separation on an augmented
   graph.
3. Change stable MAID syntax to store owned local utility nodes.
4. Adopt semantic full-deviation coverage and let an optional graph package
   construct it later.

Design 1 hit the graph-opacity kill condition. Design 3 is premature because
the consumer does not justify changing D14's validated syntax. Design 4 is
adopted. Design 2 remains experimental and may graduate only by constructing
coverage on a hostile semantic consumer.

## Representative experiment

`Tests.MAIDSafeReduction` removes a genuinely fair Boolean signal from one
decision. When payoff rewards the action alone, the always-true reduced policy
attains the pointwise upper bound, covers every full signal-contingent
deviation, and lifts reduced Nash to full Nash. With identical execution and
pruning but payoff for `decision = signal`, every signal-blind policy is worth
`1/2`, the full copying rule is worth `1`, reduced Nash fails after expansion,
and coverage is false.

`Experimental.PostArchitecture.MAIDRequisiteObservation` adds a proved utility
view with distinct local utility leaves and a reward node. In
`signal -> decision -> reward -> utility`, conditioning on `decision` blocks
the observation. Adding only `signal -> reward` leaves an active path and makes
the observation requisite. The owner utility must be a descendant of the
decision; omitting that guard falsely marks payoffs unaffected by the decision
as relevant.

The exact-term representation is load-bearing. Two views prove the same
canonical utility `reward + signal`: with separate leaves the signal-only term
is not a descendant of the decision and the signal is nonrequisite; merging the
terms into one leaf creates a moral-graph route and marks it requisite. A
single synthetic sink per owner is therefore conservatively imprecise.

`MAIDKernelMarginalization` constructs the reduced rule by conditionally
averaging an arbitrary full-context rule over removed observations and proves
that the kept-context/action joint law is unchanged. `MAIDLocalReduction` then
shows that a uniform continuation factorization constructs the existing
full-deviation coverage certificate for one unique pruned site, while every
untouched owner's policy is represented exactly. The factorization premise
contains neither a reduced witness nor a preference inequality.

`FiniteBNGlobalMarkov` proves the first representation-neutral factor algebra:
parent-closed component products depend only on their own coordinates and
split multiplicatively across a disjoint partition. It deliberately does not
define a second joint law or assert conditional independence.

EXP-104 proves that the canonical native MAID assignment law has exactly the
effective-parent local-factor point masses, including a typed three-node
consumer. A separate finite-law surface states conditional independence by the
division-free atom cross-product identity and validates impossible-evidence and
dependent controls. Cylinder marginalization is proved through one normalized
reverse-elimination step. The full parent-closed theorem remains blocked only
on cast-free dependent-complement enumeration and nested-sum reindexing; no
positivity, faithfulness, or alternate evaluator was needed.

## Measurements and kill conditions

The stable certificate is 11 source lines. The 445-line semantic consumer
unfolds the canonical assignment runner once and reuses canonical
`expectedUtility`, `euPreference`, and `IsNash`. The exact-term graph spike is
821 lines; kernel marginalization is 237 lines; the graph-free MAID coverage
bridge is 190 lines; and the initial finite-BN factor algebra is 149 lines.

Focused builds passed warning-free: the semantic test built 1735 jobs with a
6.9-second final module build; the graph spike built 1715 jobs with an
8.1-second final module build; the local reduction bridge built 1736 jobs with
a 7.9-second final module build; and the finite-BN factors built 1713 jobs with
a 7.4-second final module build. The new artifacts contain no `set_option`,
`nolint`, `sorry`, `admit`, axiom, direct `Function.update`, stored value-domain
finiteness, positivity, faithfulness, or user-visible equality transport.

Reject or narrow the graph route if it becomes a second evaluator, cannot
construct full owner-deviation coverage, assumes faithfulness of the current
parameterization, or certifies the live signal as removable. Do not add utility
nodes to stable syntax merely to make the experiment pass.

Before any completeness theorem, add constant-utility and singleton-domain
controls. Before global pruning, prove the required recall/fixpoint theorem.

## Consequences and compatibility posture

The semantic seam is public. Graphical ignorability, requisite observation,
strategic reliance, and s-reachability remain experimental and separate.
Canonical MAID point-mass factorization, a division-free finite-law
conditional-independence surface, cast-free dependent-complement enumeration,
one-pivot Fubini, and rank-one cross multiplication are now validated
experimentally. The next gate is reverse-topological parent-closed cylinder
marginalization followed by ancestral-moral factor-scope elimination. Only
then may local-utility d-separation construct
`CoversFullDeviationsAt` on the multi-agent hostile consumer.

There is no backward-compatibility obligation in this greenfield rewrite. If a
hostile consumer finds the coverage quantifiers, utility view, or graph witness
poorly modeled, change or remove them directly. Do not add aliases, adapters,
deprecated constructors, duplicate predicates, or theorem shims.
