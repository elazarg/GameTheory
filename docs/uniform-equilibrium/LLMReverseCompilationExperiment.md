# LLM-Guided Symbolic Reverse Compilation Experiment

## Status

This is an experimental research protocol. It is not a theorem, a new
certificate completeness claim, or a change to the current mathematical
frontier. Production Lean remains machine truth; [FRONTIER.md](FRONTIER.md)
remains the curated mathematical boundary; and [PIPELINE.md](PIPELINE.md)
remains project-control truth.

The initial protocol was written on 2026-08-09 against commit
`099dc1721502515a5db954105fe73d9490e612a0`. Every actual run must record its
own source commit because the compiler catalog and open obligations change.

## Purpose

The experiment tests whether modern LLM agents can make cumulative progress
on uniform-equilibrium existence by using the verified certificate/compiler
stack as a guide for backward mathematical proof search.

The proposal is not to train a model to invert a numerical function. It is to
ask proof-capable agents to reason backward from a desired semantic conclusion,
construct the premises of an existing compiler, prove an exact alternative
when those premises cannot hold, and invent intermediate mathematical language
when the existing certificate interfaces forget necessary information.

Lean and external symbolic tools are critics and local oracles. The LLM agents
perform the abductive part of the search: choosing representations, retaining
strategic provenance, proposing witnesses and case splits, finding adapters,
and deciding whether a failed finite construction calls for a different route
or an unbounded/compactness argument.

The experiment has two goals:

1. determine whether this method produces rigorous conjecture-facing
   mathematics; and
2. determine where it is useful even if it does not close the conjecture—for
   example fixed-architecture synthesis, exact counterexamples, adapter
   discovery, statement repair, formalization, or compactness design.

## Mathematical target

For finite quitting games, the canonical exact waist is
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.
Schematically,

\[
  \exists v\;\operatorname{UEPayoff}(G,v)
  \quad\Longleftrightarrow\quad
  \forall \varepsilon>0\;\exists \sigma\;
  \operatorname{TerminalNash}_{\varepsilon}(G,\sigma).
\]

The profile and its terminal payoff may depend on `ε`; compactness selects one
fixed uniform-equilibrium payoff afterward. Therefore the primary production
goal is per accuracy, not one fixed certificate family.

For a compiler route `k`, let `θ` contain its discrete architecture, internal
tolerances, continuous parameters, and proof-relevant certificate data. Write

\[
  \operatorname{Premise}_k(G,\theta)
  \Longrightarrow
  \exists\sigma\;
  \operatorname{TerminalNash}_{E_k(G,\theta)}(G,\sigma),
\]

where `E_k` is the route's exact error map. Define

\[
  \operatorname{Accepts}_k(G,\varepsilon,\theta)
  \;:\!\Longleftrightarrow\;
  \operatorname{Premise}_k(G,\theta)
  \wedge E_k(G,\theta)\le\varepsilon.
\]

The conjecture-facing target of the experiment is

\[
  \boxed{
  \forall G\;\forall\varepsilon>0\;\exists k,\theta\;
  \operatorname{Accepts}_k(G,\varepsilon,\theta).}
\]

Both `k` and `θ` may depend on `ε`. In particular, the period, support word,
chart, cutoff, recurrent component, and compiler family may all change as the
requested accuracy shrinks. An implementation need not quantify over theorem
names in Lean: the final proof may instead use a fixed dependent route type or
a concrete dispatcher whose cases invoke the relevant compilers directly.

Solving this target proves the finite-quitting specialization. Extending the
result to arbitrary finite stochastic games is a separate program unless a
general-to-quitting reduction is proved.

## What “reverse compilation” means

The phrase is deliberately suggestive but is not literal logical inversion.
From

\[
  \operatorname{Premise}_k(G,\theta)\Longrightarrow
  \operatorname{UE}(G)
\]

and the truth of `UE(G)`, nothing implies that this particular `θ` exists.
Sound compilers can be incomplete, overlap, and discard information. The
project already contains solved games outside particular exact-cycle and
truncated-ledger grammars.

The operative meaning is:

> Construct preimages of selected sufficient predicates; when a preimage is
> provably absent, derive an exact strategically meaningful alternative; and
> enlarge or change the predicate family only through a proved adapter.

The agents therefore search over more than certificate coordinates. They may
also search for:

- the right architecture or support stratum;
- an internal accuracy that makes the compiler's error map fit `ε`;
- a missing marked field or provenance invariant;
- a new adapter between existing producer and compiler interfaces;
- a useful primal/dual alternative;
- a compact or infinite object replacing escaping finite complexity; or
- the theorem statement in which the remaining alternatives become
  exhaustive.

This is abductive proof search followed by exact deductive checking.

## Why LLM guidance may add value

A conventional solver is effective after the variables, architecture,
constraints, and meaning of infeasibility have been chosen. Those choices are
often the hard mathematical step here. A proof-search agent may help with tasks
such as:

- choosing the compiler closest to the currently available data;
- preserving an owner, entering outsider, support action, source row, or
  continuation witness that elimination would erase;
- recognizing a zero-denominator or persistent-live case as productive rather
  than degenerate;
- inventing a support-enlargement, retargeting, or subgame-gluing lemma;
- decoding a Farkas row or other dual witness strategically;
- identifying when increasing a finite cutoff is the wrong move and an escape
  or compactness theorem is required; and
- finding a smaller intermediate proposition that both admits proof and feeds
  a real downstream consumer.

LP, SMT, CAD, CAS, interval arithmetic, algebraic-real certificates, numerical
experiments, and finite enumeration remain useful local tools. Their outputs
become mathematics only after exact checking or an independent proof.

## Two engines and two graphs

The experiment must not collapse fundamentally different search regimes.

### Finite preimage engine

For a fixed support, chart, period, cutoff, and accuracy, expose the finite
system of equalities and inequalities. Preserve strategically marked data,
split singular cases before division, and seek either an exact certificate or
an exact infeasibility alternative. Rational witnesses are welcome but not
required; polynomial systems may require certified algebraic reals.

### Escape engine

The union over all finite architectures may have unbounded period, cutoff, or
word length. Bounded-search failure does not decide this union. The escape
engine handles charged recurrence, reachable SCCs, chronological realization,
finite charged return, compactness, inverse limits, support-witness paths,
adaptive potential systems, and completed boundary objects.

The experiment also maintains two distinct graphs:

- The **mathematical dispatcher graph** has game/support/chart states and
  proved strategic transformations. Its unresolved outer transitions require
  genuine exhaustivity and well-founded progress. Recurrence inside a reachable
  component may instead be productive.
- The **research-obligation graph** has theorem tasks and dependency edges. It
  schedules work and may be revisited indefinitely; its shape proves nothing
  about termination of the mathematical dispatcher.

## Experimental stages

### Stage 0: Thin search map

Before a run, record only the compiler information needed by the selected
tasks:

- canonical theorem and source file;
- quantifier shape and error map;
- architecture and certificate fields;
- downstream consumer chain;
- known adapters and no-go examples;
- exact unresolved producer premise; and
- semantic fences that the attempt must not cross.

This begins as a small external ledger, not a new universal Lean API. A
machine-readable registry or generated audit is justified only if repeated
runs show that manual task preparation or theorem drift is a material source
of failure.

### Stage 1: Calibration by reconstruction

Give agents bounded, already-solved theorems while withholding their existing
proofs. Include representative tasks from:

- a finite algebraic certificate;
- an error-accounting adapter;
- a boundary or singular case;
- an exact counterexample or no-go; and
- a small Lean formalization task.

The purpose is not to claim new mathematics. It tests whether the agents can
respect the project's quantifiers and semantic fences, use exact tools, and
produce independently checked artifacts. Calibration failures should change
task packaging before expensive frontier work begins.

### Stage 2: Bounded live obligations

Select small open obligations from the current pinned `PIPELINE.md`. Prefer
tasks with finite inputs, a precise positive/negative alternative, canonical
regression games, and a short consumer path. For each fixed architecture, ask
for one of:

- an accepted certificate;
- an exact adapter theorem;
- a proved architecture-specific no-go;
- a typed strategic obstruction; or
- a strictly sharper proposition that remains explicitly open.

This stage evaluates where reverse compilation is locally fruitful without
pretending that bounded synthesis proves coverage.

### Stage 3: Routing and recurrence pilot

After successful bounded work, attempt one genuinely bifurcating theorem near
the current spine. The preferred shape is a bounded piece of:

\[
  \text{finite strategically legal support atlas}
  \Longrightarrow
  \text{reachable charged component}
  \;\vee\;
  \text{strategically decoded separator}.
\]

The positive output must feed chronological charged closing or another named
consumer. The negative output must force support enlargement, retargeting,
proper-subgame descent, component exit, or a separately stated barrier. A
global flow that cancels across distinct recurrent components is not an
executable path.

### Stage 4: Evaluate, specialize, or stop

Only after the earlier stages should the experiment attempt a broader
dispatcher or escaping-complexity theorem. The evidence may support different
conclusions:

- use agents primarily for Lean formalization and proof repair;
- use them for finite certificate inversion but not global routing;
- use them as adversarial statement and counterexample critics;
- use them for cross-route adapter discovery;
- use them for compactness/representation design; or
- continue toward an exhaustive terminal producer.

Failure to solve the conjecture does not make the experiment uninformative,
but unverified prose and search transcripts do not count as progress.

## Unit of work

No individual agent receives “prove uniform equilibrium.” A task packet should
contain:

- a pinned source commit;
- one exact theorem statement or exact positive/negative alternative;
- relevant declaration signatures and canonical files;
- the downstream consumer chain;
- positive and adversarial regression examples;
- allowed strategy, information, and probability semantics;
- explicit nonclaims and forbidden upgrades;
- allowed edits and tools; and
- acceptance commands.

An attempt ends with exactly one of these classifications:

1. **Accepted witness:** certificate plus a checked validity proof.
2. **Adapter theorem:** checked map into another productive route.
3. **Exact no-go:** checked exclusion of a stated architecture or grammar.
4. **Typed obstruction:** exact separator, entering-player witness, retarget,
   face, component, or escape datum with a stated consumer.
5. **Refined open obligation:** a narrower unresolved proposition.
6. **No result:** timeout, heuristic failure, or unreproducible output.

The last two do not close a mathematical branch. In particular:

- no stationary witness is not terminal nonexistence;
- no period-`K` certificate is not an all-period obstruction;
- no current compiler applies is not a catalog-completeness theorem; and
- only an all-behavior terminal exploitability gap, or a theorem producing
  one, is a quitting-game nonexistence certificate.

## Suggested agent roles

When several agents are used, give them asymmetric jobs rather than asking
several copies to endorse the same route:

1. a **route proposer** produces competing proof decompositions;
2. a **counterexample critic**, initially blind to the preferred route, attacks
   quantifiers, boundary cases, circular premises, and semantic upgrades;
3. a **symbolic specialist** obtains exact local formulas or certificates;
4. a **formalizer** minimizes and checks the surviving mathematical claim; and
5. an **integrator** verifies repository fit, consumers, regressions, and
   source-of-truth updates.

A smaller run may combine roles, but proposal and adversarial criticism should
remain visibly separate.

## Trust boundary

The experiment has three one-way trust layers:

| Layer | Contents | Status |
| --- | --- | --- |
| Production | Lean definitions, theorems, and exact checkers | Trusted at their built and audited scope |
| Reproducible evidence | Solver scripts, exact tables, interval certificates, generated witnesses | Evidence only until consumed by a production checker or proof |
| Orchestration | Prompts, rankings, task selection, search traces, agent summaries | Never part of a proof |

Agents must not game a verifier through unreachable states, vacuous support,
the wrong deviation class, nonphysical flows, hidden correlation, or a premise
equivalent to the desired equilibrium. Known target-mismatch, ledger-boundary,
SCC-cancellation, and architecture-cap examples are adversarial tests, not
optional illustrations.

## Evaluation protocol

### Questions

Each run should contribute evidence about the following separately:

1. **Reconstruction:** can agents recover known proofs without semantic
   weakening?
2. **Fixed inversion:** can they construct or exactly refute fixed
   architectures?
3. **Provenance:** can they retain and interpret the strategic data needed by
   downstream consumers?
4. **Adapter discovery:** can they prove new maps between existing routes?
5. **Statement repair:** can critics find false quantifiers or missing
   hypotheses before formalization effort is wasted?
6. **Escape recognition:** can agents distinguish a finite failure from an
   unbounded-complexity problem and formulate the correct next theorem?
7. **Cumulative value:** do failed attempts leave reusable checked artifacts or
   sharper obligations?

### Run record

Record for every task:

- task ID and pinned commit;
- mathematical category and logical level;
- supplied context and whether it was golfed;
- model, reasoning setting, time/token budget, and tool access;
- acceptance criteria declared before launch;
- final artifact classification;
- exact verification commands and results;
- critic verdict and regression results;
- downstream consumers actually unblocked; and
- new obligations or no-go information deposited in the ledger.

### Primary measures

Prefer measures tied to mathematical movement:

- checked artifacts per bounded attempt;
- typed residual branches eliminated;
- compiler premises derived from more primitive game data;
- exact adapters added to the productive dependency chain;
- false universal grammars killed by checked counterexamples;
- assumptions or quantifier complexity removed from a live obligation;
- shortest checked path from source game data to terminal Nash; and
- proportion of failed attempts leaving reproducible mathematical residue.

Theorem count, generated lines, proof length, solver calls, and polished prose
are not primary measures. A lane should be continued, narrowed, or paused based
on its predeclared bounded cohort, not on a single impressive success or a long
unstructured run.

### Reporting where the method works

Results should be reported by lane rather than as one success rate:

| Lane | Typical work | Separate evaluation reason |
| --- | --- | --- |
| Reconstruction/formalization | Known theorem recovery, proof repair, API use | Tests basic reliability, not new mathematics |
| Finite preimage | Fixed supports, periods, charts, exact algebra | Most amenable to local exact tools |
| Criticism/no-go | Counterexamples, quantifier attacks, boundary strata | Can be valuable even with low positive-proof yield |
| Adapter/routing | Support change, retargeting, strategic dual decoding | Tests representation choice and provenance |
| Escape/compactness | Unbounded length, recurrence, infinite execution | Hardest and least reducible to finite solving |
| Exhaustivity | Global dispatcher and outer termination | Conjecture-strength; never inferred empirically |

## JIT golfing experiment

“Golfing” can mean several different operations, with different risks.

### Forms of golf

- **Proof-source golf:** shorten a Lean proof script.
- **API golf:** replace a long downstream derivation by a small named checked
  lemma with the right interface.
- **Dependency golf:** reduce the imports and declarations exposed to a task.
- **Context golf:** create a compact agent prompt containing only the exact
  definitions, theorem signatures, consumers, regressions, and semantic
  fences needed now.
- **Statement golf:** weaken or alter the mathematical claim to make it easier.
  This is forbidden unless recorded as a different theorem.

There is an important logical/research distinction. Once a certificate has
already been constructed, Lean can apply a compiler theorem from its statement;
the downstream proof need not replay the compiler's proof body. Reverse search
is different. The proof body may reveal why every certificate field exists,
where each inequality is consumed, how error constants propagate, which
hypotheses have slack, and which intermediate map is a better inversion target.
Treating the compiler as a black box would discard information directly
relevant to preimage discovery.

Consequently, proof-source golf should not mean hiding the compiler proof from
the research process. An aggressively short tactic proof can also be less
robust and can conceal the mathematical reason a construction works. A more
promising operation is **proof slicing**: retain the full canonical proof, but
extract on demand the definitions, intermediate lemmas, proof fragments, and
hypothesis-to-consumer map relevant to the current reverse obligation.

JIT context and API golf may be substantially more useful. The relevant route
is often unknown until an agent has inspected the goal, so preparing one
globally minimal corpus in advance is both expensive and liable to discard the
marked datum the proof eventually needs. Instead:

1. retain the full canonical sources and discovery proof;
2. choose a concrete task and route at a pinned commit;
3. generate a compact task capsule on demand;
4. keep exact theorem statements, quantifiers, error maps, marked provenance,
   consumers, no-go examples, and nonclaims;
5. include the relevant compiler proof slice and keep every omitted proof body
   and historical discussion immediately retrievable;
6. if a repeated long derivation obstructs search, introduce a small checked
   facade lemma rather than an informal summary; and
7. regenerate the capsule when the source commit changes.

Golf must never remove the accuracy quantifier order, error transformation,
behavioral-deviation class, reachability/SCC condition, target-selection issue,
or a regression known to falsify a tempting shortcut.

The effect is testable. On matched calibration tasks, compare three conditions:

1. theorem signatures and certificate definitions only;
2. complete relevant proof sources; and
3. a JIT-generated proof slice with full sources retrievable on demand.

Compare them using:

- checked solve rate;
- agent and tool cost;
- semantic-error rate;
- number of unnecessary route changes;
- proof robustness and review cost; and
- ability to recover relevant omitted material when the initial capsule was
  too small.

Proof length is not itself a success metric. The useful form of golf is the
smallest checked interface and context that preserves the mathematics needed
for the current search.

## Initial pilot

The first pilot should be deliberately modest:

1. choose several solved reconstruction tasks spanning algebra, error
   accounting, a singular boundary, and a no-go theorem;
2. run at least one matched full-context versus JIT-context comparison;
3. select a small cohort of bounded live obligations from the pinned
   `PIPELINE.md`;
4. require adversarial review of every claimed branch closure;
5. attempt one narrowly stated componentwise positive/negative alternative;
   and
6. publish a lane-by-lane evaluation, including null results and exact costs.

Do not build a large orchestration framework before this pilot demonstrates a
coordination problem worth automating. The first durable outputs should be
mathematical artifacts and a compact run ledger.

## Success condition

The experiment is successful in the strongest sense only if its checked
artifacts assemble into the per-accuracy terminal-production theorem. It can
still be fruitful in narrower, explicitly measured ways if it reliably
produces exact certificates, no-go theorems, useful adapters, repaired
statements, or compactness formulations that advance particular lanes.

Its governing discipline is:

> Use verified compilers as backward proof rules; let LLM agents search
> creatively for witnesses and for the language of exhaustive alternatives;
> require exact artifacts at every durable step; and never promote empirical
> search coverage to mathematical exhaustivity.
