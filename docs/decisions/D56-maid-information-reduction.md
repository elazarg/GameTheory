# D56: MAID information reduction uses semantic deviation coverage

- **Status:** adopted for the semantic seam; experiment-only one-site
  graphical discharge validated
- **Date:** 2026-08-16
- **Experiment IDs:** EXP-102, EXP-103, EXP-104, EXP-105, EXP-107

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

Nested semantic reductions compose. `Pruning.Refines` records that a finer
reduction keeps no more observations than a coarser one, while
`CoversReducedDeviationsAt` covers the coarser replacement space from a finer
profile. Relative coverage followed by full-deviation coverage constructs
`CoversFullDeviationsAt` for the finer profile. This result assumes the two
coverage certificates; it does not infer either certificate from a graph.

The graph-only design is rejected. `Structure` stores chance and decision
nodes, while `Semantics.utility` is an arbitrary function of a completed
assignment. Two semantics can share the same graph and chance laws while one
utility ignores a signal and the other rewards matching it. No predicate of
the existing graph alone can safely distinguish them.

An experiment-only proved `UtilityView` survives as a possible graph front end.
It enumerates distinct owner-indexed additive utility terms and proves their
sum equals canonical utility. It is not a public API. EXP-105 uses it to
construct the existing semantic coverage certificate for one unique pruned
decision site without changing stable MAID syntax.

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

Local soundness does not require recall, and neither does composition of
already-certified relative coverage steps. The sufficient-recall condition is
load-bearing for the less-conservative 2008 edge-addition fixpoint and its
coordinated same-owner graphical safety theorem: those results must construct
the certificates rather than assume them. Even a safe reduction may discard
original equilibria, including Pareto-preferred ones; safety is only
reduced-Nash-to-full-Nash inclusion.

EXP-107 keeps the global theorem experiment-gated. Its hybrid restore-all
graph, original-graph mechanism-node s-reachability, candidate/hybrid
factorization, fixed-law global-Markov conditional independence, exact
hybrid-to-site policy adapter, multi-site target-rule surgery, and
replacement-uniform relevant-term continuation now compile. The
nonrelevant-term marginal certificate and site-local factor/optimality
endpoints now compile as
[`MAIDPruningNonrelevantInvariance.lean`](../../GameTheory/Experimental/PostArchitecture/MAIDPruningNonrelevantInvariance.lean)
and
[`MAIDPruningSiteReduction.lean`](../../GameTheory/Experimental/PostArchitecture/MAIDPruningSiteReduction.lean);
the proof-side fully mixed owner order and mechanism-selector factorization
also compile as
[`MAIDPruningRecallOrder.lean`](../../GameTheory/Experimental/PostArchitecture/MAIDPruningRecallOrder.lean)
and
[`MAIDMechanismSelectorFactorization.lean`](../../GameTheory/Experimental/PostArchitecture/MAIDMechanismSelectorFactorization.lean).
The selector conditional-independence/score argument, semantic
soundness/optimality transport under a fully mixed reference rule
(Koller--Milch Lemmas 6.1--6.2 style), same-owner relevance-order induction,
and global coverage theorem do not.
The paper's
qualitative Forgetful Movie Star profile is not accepted as negative evidence:
under an explicit `2 * avoid + consistency` instantiation, its described
independent-uniform behavioral profile earns `3/2` while a legal reduced
whole-owner constant-equal deviation earns `2`. The graph remains a valid
fixpoint and recall-cycle sentinel, but not an unsafe reduced-Nash consumer.

## Competing designs

1. Infer safety from the existing chance/decision graph alone.
2. Attach a proved utility-dependence view and run d-separation on an augmented
   graph.
3. Change stable MAID syntax to store owned local utility nodes.
4. Adopt semantic full-deviation coverage and let an optional graph package
   construct it later.

Design 1 hit the graph-opacity kill condition. Design 3 is premature because
the consumer does not justify changing D14's validated syntax. Design 4 is
adopted. Design 2 passes the hostile one-site semantic consumer but remains an
optional experimental front end rather than a stable API.

## Representative experiment

`Tests.MAIDSafeReduction` removes a genuinely fair Boolean signal from one
decision. When payoff rewards the action alone, the always-true reduced policy
attains the pointwise upper bound, covers every full signal-contingent
deviation, and lifts reduced Nash to full Nash. With identical execution and
pruning but payoff for `decision = signal`, every signal-blind policy is worth
`1/2`, the full copying rule is worth `1`, reduced Nash fails after expansion,
and coverage is false.

`Tests.MAIDPruningComposition` uses one decision that originally observes two
Boolean signals. A coarser reduction retains one signal and a finer reduction
retains none. The stable API proves refinement, staged policy expansion,
unilateral-update compatibility, and equality of the canonical native laws;
relative fine-to-coarse coverage then composes with coarse-to-full coverage.
A nonconstant action-reward case exercises both coverage inequalities and
transfers Nash through both stages. In the matching-payoff control,
coarse-to-full coverage survives while fine-to-coarse coverage fails; the fine
profile remains reduced Nash but its expansion admits the signal-copying
deviation.

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

EXP-104 proves finite global-Markov soundness end to end. The canonical native
MAID assignment law has exactly the effective-parent local-factor point masses.
Reverse-topological elimination marginalizes every factor outside a
parent-closed ancestral set; ancestral-moral components partition the retained
factor scopes; dependent latent sums produce a rank-one table; and point, row,
column, and total identities rewrite that table to the four cylinder masses of
division-free conditional independence. The canonical MAID corollary reuses
the same native evaluator and effective kernels. Heterogeneous chain,
collider/descendant-evidence, and zero-mass evidence consumers pass without
positivity, faithfulness, nontriviality, or an alternate evaluator.

EXP-105 augments canonical play with distinct finite configuration-valued
utility leaves and proves the mapped law factorizes. Set-valued graphical
ignorability constructs one replacement-invariant utility-law certificate:
relevant terms share a continuation chosen independently of the replacement,
while nonrelevant terms have an exact parent-closed invariant marginal. This
feeds the existing `LocalUtilityFactorsAt` bridge and then
`CoversFullDeviationsAt` under an explicit one-site pruning shape. The hostile
consumer accepts the signal-blind rival and transfers Nash, while a
signal-relaying rival makes the observation requisite and not ignorable; its
copying full deviation earns `3/2` against the blind reduced value `1`, so
coverage is false.

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

The completed EXP-104 path adds a 249-line generic global-Markov theorem and a
57-line canonical MAID corollary after the measured factorization,
marginalization, moral-component, retained-cylinder, and rank-one modules. Its
153-line heterogeneous chain, 268-line collider/descendant, and 159-line
zero-evidence consumers compile warning-free. The final theorem stores no
finiteness capability and adds no positivity, nontriviality, or inhabitedness
premise; a default dependent assignment is selected from the input law's
nonempty support.

The EXP-105 close-out adds a 100-line generic graphical assembly and an
802-line safe/live relay consumer after the measured augmentation,
factorization, conditional-independence, continuation, and kernel-invariance
modules. The focused consumer build passes warning-free, and the source audit
finds no option, lint suppression, placeholder, axiom, direct update, visible
transport, representation leak, or compatibility shim.

EXP-107's site-local closeout adds the nonrelevant-term marginal certificate,
the edge-addition-stable site-local factor/optimality endpoint, the fully mixed
owner-order machinery, and canonical mechanism-selector factorization. The
thirteen-artifact foundation set plus the two hostile consumers has a warning-
free aggregate targeted Lake build (1,784 jobs), full repository build (3,671
jobs), and deep Phase 1--3 audit (`VERIFIED=1` for each phase). The remaining
load-bearing global step is semantic soundness/optimality transport for
changes at non-s-reachable same-owner sites under a fully mixed reference rule
(Koller--Milch Lemmas 6.1--6.2 style). The remaining selector-CI cross-law and
score comparison must establish that transport. Once it is established, the
same-owner relevance-order induction must combine the local optimality rules
into one reduced whole-owner rule and then discharge full-deviation coverage.

Reject or narrow the graph route if it becomes a second evaluator, cannot
construct full owner-deviation coverage, assumes faithfulness of the current
parameterization, or certifies the live signal as removable. Do not add utility
nodes to stable syntax merely to make the experiment pass.

The hostile relay control satisfies the final one-site kill condition: the
same theorem that certifies the signal-blind graph does not certify the live
relay, and semantic coverage is independently refuted there.

Before any completeness theorem, add constant-utility and singleton-domain
controls. Nonrelevant-term invariance and site-local utility-factor assembly
are now complete at the experiment-only endpoint. Before the global graphical
theorem, prove the sufficient-recall relevance-order induction for the
edge-addition fixpoint.

## Consequences and compatibility posture

The semantic seam is public. Graphical ignorability, requisite observation,
strategic reliance, and s-reachability remain experimental and separate.
Canonical MAID point-mass factorization and division-free finite global-Markov
soundness are now validated experimentally through arbitrary dependent query
configurations, including impossible evidence. Finite utility-leaf
augmentation and replacement invariance now let local graphical ignorability
construct `CoversFullDeviationsAt` for one unique pruned site, and the hostile
safe/live relay consumer validates both sides. Stable relative coverage now
composes already-certified nested reductions without a recall premise. It does
not promote the graph view to a public API, derive either stage's certificate,
or justify coordinated same-owner graphical pruning. The next graphical gate
is semantic soundness/optimality transport for changes at non-s-reachable
same-owner sites under a fully mixed reference rule (Koller--Milch Lemmas
6.1--6.2 style). The sufficient-recall relevance-order induction then
constructs a reduced whole-owner best response at an edge-addition fixpoint
from the completed site-local endpoints, yielding global coverage. Requisite
observation and strategic reliance remain distinct notions despite that
dependency.

There is no backward-compatibility obligation in this greenfield rewrite. If a
hostile consumer finds the coverage quantifiers, utility view, or graph witness
poorly modeled, change or remove them directly. Do not add aliases, adapters,
deprecated constructors, duplicate predicates, or theorem shims.
