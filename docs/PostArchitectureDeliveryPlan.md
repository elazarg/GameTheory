# Post-architecture delivery plan

Status: active delivery plan.

Baseline: 2026-07-30, after EXP-034 and commit `f23e3ef`.

This document is the mutable plan for turning the accepted architecture into a
broad library. The architecture RFC remains authoritative for foundational
decisions, decision records remain authoritative for measured choices, and
phase records remain historical evidence. This document owns delivery order,
coverage status, and the conditions for calling a subfield supported.

The plan has three simultaneous but unequal obligations:

1. recover the mature mathematics in the pinned v1 snapshot;
2. add mature subfields that v1 omitted or represented only by a token example;
3. create room for research without making stable users pay for speculative
   abstractions.

The first obligation is the protected critical path. The second broadens the
subject deliberately. The third is opt-in and may never weaken either of the
first two.

The headline comparator is the user-facing workflow matrix in
`docs/V1CapabilityMatrix.md`: v2 must be at least as useful as v1 across mature,
in-scope work while improving ownership, trust, assumptions, and integration.
The pinned declaration index remains a regression oracle and attribution
source. It is not a quota requiring every predecessor wrapper or niche theorem
to be reproduced.

## 1. What completion means

File count, line count, declaration count, and source compatibility are not
completion metrics.
The rewrite deliberately changes representation and removes duplicate public
surfaces. Completion is measured by qualitative capability parity supported by
mathematical and architectural evidence.

### 1.1 Capability parity

`docs/V1CapabilityMatrix.md` records recognizable user workflows rather than
assigning equal weight to every predecessor declaration. A release-level parity
claim requires:

1. every mature in-scope v1 workflow is represented in the matrix;
2. no row remains a `critical gap`;
3. a `better` or `comparable` verdict names a checked public theorem, example,
   and integration advantage or equivalence;
4. a `partial` verdict is release-compatible only when its missing remainder is
   explicitly shown not to remove a mature user workflow;
5. beyond-v1 work does not compensate for a regression in a mature field; and
6. architecture, assumptions, trust, executability, and import ergonomics are
   part of usefulness, not secondary polish.

A stronger canonical theorem may replace many predecessor declarations. A
directory, syntax bundle, internal wrapper, or experiment does not establish
capability parity.

### 1.2 Declaration accounting

Exact declaration review protects the qualitative matrix from overlooking a
useful predecessor fact. Declarations reviewed by an active work package
receive exactly one disposition:

- **port:** retain essentially the same statement against the canonical v2 API;
- **adapt:** retain the mathematical result with an honestly changed statement
  or representation;
- **subsumed:** a more general canonical v2 theorem proves the old result by a
  transparent specialization;
- **refuted:** the old statement is false, with a checked counterexample;
- **deferred:** mathematically wanted, but gated by a named missing dependency
  or a later scope decision;
- **retired:** compatibility glue, duplicate semantics, dead transport
  machinery, or a theorem with no surviving mathematical payload;
- **out of scope:** explicitly outside the finite/discrete v1 release boundary.

`docs/V1CoverageLedger.md` is the family-level index. Before routine recovery
starts in a family, its work package must add a declaration-level ledger with
the pinned path, old declaration, disposition, canonical destination, and
validation evidence under `docs/coverage/`. The required schema is documented
there. A family is not called exactly recovered while it contains an
unclassified declaration. Full-snapshot accounting remains a valuable curation
milestone, but it is not the release definition and unreviewed declarations
earn no capability credit.

### 1.3 Four completion levels

The project reports four different milestones and never collapses them into
one percentage:

1. **architecture-ready:** the semantic owner and dependency direction have
   survived a hostile theorem;
2. **capability-covered:** every mature workflow is `better`, `comparable`, or
   an accepted `partial` with no lost mature use case;
3. **v1-accounted:** independently, every pinned declaration has a disposition;
4. **release-ready:** capability coverage, public import review, examples,
   documentation, full build, audits, and cold-build measurements all pass.

The project is architecture-ready for the shared static core and the principal
Protocol and Analysis boundaries. It is neither capability-covered nor fully
v1-accounted yet.

### 1.4 Definition of support for a subfield

A subfield is called **supported** only when all of the following exist:

1. a mathematical object at its lowest sufficient semantic layer;
2. a named public import and documented stability level;
3. one hostile flagship theorem that exercises the subfield's distinctive
   data, rather than a degenerate example;
4. any bridge to another layer proved from independently meaningful
   preservation facts;
5. at least one reader-facing example and one architecture or locality test;
6. exact assumptions on the theorem or operation that needs them;
7. a bounded declaration-level v1 ledger supporting its capability verdict
   when the subfield has a v1 predecessor;
8. a clean relevant build, trust audit, and dependency-boundary audit.

A syntax bundle, one encoding example, or a directory name is a probe, not
subfield support.

## 2. The integration vision

The accepted design is a stratified hybrid, not a universal game object.

- `GameTheory.Core` owns static forms, profiles, preferences, utilities,
  deviations, equilibrium, and the smallest genuinely shared social and
  coalitional foundations.
- `GameTheory.Protocol` owns execution, histories, information, behavioral
  policies, assessments, and strategic extraction. Sequential structure is not
  reconstructed from a static form after compilation.
- `GameTheory.Languages` owns syntax and compilers. Syntax imports no solution
  concept. A language reaches another semantic layer only through a named
  theorem with an actual consumer.
- `GameTheory.Finite` owns executable finite algorithms over explicit
  enumerations and computable scalars. Correctness connects their answers to
  proof semantics.
- `GameTheory.Repeated` owns stagewise, recursive, and finite-prefix repeated
  play without committing the stable root to an infinite path law.
- `GameTheory.Analysis` imports stable semantic roots in one direction for
  topology, convexity, fixed points, minimax, existence, and quantitative
  online-learning consumers. Stable roots never import it back. Protocol,
  Repeated, and Learning bridges have separate positive and negative probes.
- `GameTheory.Cooperative` is reserved for larger coalitional, matching,
  bargaining, and market-design developments that do not honestly reduce to
  strategic profiles.
- `GameTheoryMath` owns independently reusable mathematics only when a live
  consumer justifies it and Mathlib does not already supply it.
- `GameTheory.Frontier` may import stable roots. No stable root imports
  Frontier. `GameTheory.Challenges` is never a proof dependency.

The integration rule is therefore:

> Share foundations when two subfields prove the same mathematics; use named
> compilers when one representation forgets structure; keep genuinely
> different mathematical objects in coordinated parallel branches.

This prevents both failure modes visible in v1: duplicating Nash-like concepts
per language and forcing sequential, cooperative, or epistemic data through a
static universal hub.

## 3. Stable-support covenant

Research breadth is welcome only under rules that preserve mature support.

1. The v1 recovery waves below remain the critical path until capability
   coverage has no critical gap.
   Beyond-v1 work cannot satisfy or postpone a recovery gate.
2. Until capability coverage has no critical gap, at least three of every four
   planned integration work packages target mature v1 workflows. A package is
   a predeclared theorem family or domain gate, not a commit, declaration count,
   or line-count target. Exact accounting may run mechanically in parallel but
   does not choose the lead integration package.
3. At most one Frontier experiment may be active at a time. If fewer than four
   independent work packages are active, Frontier occupies at most one.
4. Mature blind-spot work may begin after Wave 1 when its prerequisites are
   stable, but it gets its own domain gate and does not change a shared API on
   behalf of hypothetical future consumers.
5. A Frontier result may import stable public APIs, but no reverse import,
   instance, notation, or foundation field is allowed.
6. A stable API change proposed by Frontier requires a decision record, a
   mature in-scope consumer, measured migration cost, and all existing mature
   audits. Convenience for the Frontier theorem is not evidence.
7. Frontier build failures, dependency upgrades, or abandoned experiments may
   not block the stable build.
8. No amount of Frontier coverage compensates for a regression in a mature
   theorem, example, executable specification, or audit.

Exceptions to the capacity rule require a short decision record stating what
stable gate is paused, why the pause is bounded, and what result resumes it.

## 4. Delivery workflow

Every work package follows one of two paths.

### 4.1 Routine recovery

Use this path only when the semantic owner and integration boundary are already
validated.

1. Freeze the exact pinned files and declarations in scope.
2. Classify each declaration before translating proofs.
3. Search Mathlib, then the canonical v2 API, before adding helpers.
4. Port statements and proof ideas with attribution to the pinned path and
   commit.
5. Split independent leaf families only after shared definitions are fixed.
6. Integrate continuously against the canonical imports.
7. Update the declaration ledger in the same commit.
8. Run the narrow build, relevant audits, and full build at the domain gate.

Routine recovery does not reserve an experiment merely because a proof is
difficult.

### 4.2 Architecture or frontier spike

Use this path when ownership, representation, probability, scalar, topology,
or dependency direction is unsettled.

1. Predict competing designs and the smallest hostile theorem.
2. Reserve the next `EXP-NNN` entry before code is written.
3. State the kill condition and measurements in advance.
4. Implement only the slice needed to discriminate the designs.
5. Record supporting, refuting, narrowing, or inconclusive evidence.
6. Write or amend a decision record before freezing a public API.
7. Either unlock routine recovery or remove the unused experiment.

An architecture spike does not silently become a broad port.

Any proposed external dependency additionally records version/toolchain fit,
license, manifest disturbance, its own placeholder and axiom profile, the
trusted certificate path, import closure, build cost, and positive and negative
reachability probes. D13 remains rejected unless a concrete recorded reopening
condition is met.

### 4.3 Work-package contract

Each package instantiates this contract:

```text
Domain / horizon / priority:
Pinned roots and declarations:
Beyond-v1 mature target, if any:
Current integration / flagship / harvest status:
Semantic owner and canonical destination:
Stable APIs reused:
Native data retained / deliberately forgotten:
Allowed imports / forbidden dependency edges:
Compiler or projection / reason none is honest:
Finite and executable boundary:
Analysis and D11 measurable boundary:
Hostile flagship / discriminating witness:
Kill conditions:
Experiment requirement and IDs:
Ledger rows changed / exact exit criterion:
Leaf units safe to parallelize:
Narrow and gate-level validation:
Attribution:
Maturity of the result:
```

Parallel agents receive disjoint theorem/file scopes and the same target API.
They do not independently invent shared definitions.

## 5. Wave 0: make coverage accountable

Status: in progress; exact file ownership, generated declaration indexing, the
structural coverage audit, and exact L-NFG/L-FOSG review queues are present.
Static broad-package ledgers, manual classification, and the consolidated
moving delivery audit remain.

The family ledger covers the pinned `GameTheory/` and `Math/` trees and records
current integration and recovery status. Wave 0 closes when:

1. every pinned Lean file belongs to one family row;
2. each family has a semantic owner or an explicit experiment gate;
3. every open package has a declaration-level ledger;
4. a coverage audit rejects unknown dispositions, duplicate ownership, missing
   pinned paths, and a `complete` family containing an open declaration;
5. the moving architecture probes are consolidated under a current delivery
   audit, while immutable gate measurements remain in their historical records
   rather than silently changing inside Phase 2/3-named scripts;
6. README status is derived from the ledger rather than source-size estimates.

The audit now indexes 436 files and 8,324 declarations. Thirty-eight work-package
ledgers claim 1,840 declarations: 1,659 have reviewed dispositions, 181 remain
deliberately seeded `unreviewed`, and 6,484 remain explicitly unaccounted. Both
open sets are review queues, not
auto-classification targets; generated rows are evidence of scope, not
recovery or a release percentage.

The Phase 2 and Phase 3 reachability harnesses use process-unique temporary
probe files. Parallel recovery audits therefore cannot overwrite one another's
import roots and manufacture a false boundary result.

## 6. Wave 1: close the frozen promises

Status: complete.

This wave closes promises made during architecture validation before broad
recovery creates pressure to work around them.

| Gate | Deliverable | Current state | Completion test |
|---|---|---|---|
| W1-A | nonconstant-payoff finite-EFG sequential-equilibrium stress | **complete (EXP-035)** | rationality and Bayes consistency are both nontrivial on the same finite EFG |
| W1-B | public SPE semantics and full well-founded one-shot-deviation theorem | **complete (EXP-036)** | an honest analogue of v1 `oneShotDeviation_iff_spe`, including off-path histories |
| W1-C | no-regret learning to CCE | **complete** | the frozen F2 theorem uses the canonical deviation and correlation APIs |
| W1-D | finite-prefix stochastic monitoring | **complete** | the frozen F8 law handles a nontrivial signal law, not only perfect public observation |
| W1-E | Bayesian outcome-law and truthfulness transfers | **complete** | F5 and F6 are ported, adapted, or explicitly retired with measured reasons |
| W1-F | named language transfers | **complete; T1, T3, and T4 closed** | T1, T3, and T4 are proved or rejected individually; no generic certificate is credited for a missing theorem |
| W1-G | perfect-recall-facing Kuhn surface | **complete** | both constructive directions, realizable history-law equality, arbitrary outcome pushforwards, and expected utility are exposed under the sharp no-revisit/recall hypotheses |
| W1-H | minimal D8 transformation surface | **complete (EXP-045/D8)** | concrete player/strategy equivalences, mixed lifting, Nash/CE invariance, and the shared MAID probability law are public and transport-audited |
| W1-I | overdue knowledge and evolutionary ownership probes | **complete (EXP-043/D16; EXP-044/D17)** | Aumann/`InfoState` and ESS/static-dynamic ownership are settled in separate stable branches with explicit reverse-dependency probes |

Recommended dependency order:

1. Completed W1-E fixes the Bayes-plausibility, obedience, truthful-report, and
   ordinary Bayes-Nash targets used by later mechanism recovery.
2. Completed W1-A through W1-E fix the continuation, Bayes, SPE, one-shot,
   external-regret, approximate-CCE, public-monitoring, recommendation-law, and
   truthful-mechanism targets used by later recovery.
3. T1, T3, T4, W1-G, and W1-H fix the EFG/MAID/NFG/FOSG strategic-form,
   transformation, and Kuhn targets.
4. W1-I may proceed independently, but must close before those domains harvest.
5. The MAID and FOSG execution probes and named transfer packages have passed;
   broader recovery proceeds through their declaration ledgers.

Wave 1 closes only when every frozen flagship F1-F8 and transfer T1-T4 is
`complete`, `subsumed`, `refuted`, `deferred` behind a named later gate, or
`retired` with evidence. `Partial` is not a closing status.

## 7. Wave 2: mature static recovery

Status: ready where Wave 1 does not own the same declaration.

The static core has already survived equilibrium existence, potential games,
zero-sum value, Arrow, Shapley, and mechanism-encoding stress. The following
lanes may harvest in parallel after their lead definitions are checked.

| Lane | Pinned scope | Hostile lead result | Intended home |
|---|---|---|---|
| foundations and VNM | utility invariance, strategic equivalence, expected-utility representation, axiom independence | expected-utility representation without merging probability-free ranks back into lottery preference | `Core.Preference`, finite laws, and independent mathematics only where earned |
| static response | dominance, rationalizability, approximate and secure equilibrium | dominance solvability and one approximation theorem without duplicate Nash predicates | `GameTheory.Core` |
| correlation | correlation regimes, regret, signal timing, value of correlation | **CE/CCE existence complete through mixed Nash;** next one strict separation in the hierarchy | `Core` and opt-in `Analysis` |
| learning | regret, multiplicative weights, fictitious play, approachability | **F2 and finite MW self-play complete (EXP-049/D21);** next potential-game fictitious-play convergence | stable finite identities in Core, law-free MW algebra in `GameTheoryMath`, canonical-law adapter in Probability, and quantitative composition in `Analysis.Learning` |
| potential and congestion | finite-improvement, harmonic/decomposition results, Rosenthal, affine price of anarchy | **pinned congestion family complete, including robust affine CCE PoA (EXP-052/053, D24)** | `Core.Potential` plus the opt-in congestion domain |
| welfare | individual rationality, smoothness, price of anarchy | **pure and robust CCE smoothness complete in Core (EXP-052/053, D24);** next individual rationality | `Core.Welfare` plus the theorem-only `Core.RobustWelfare` bridge |
| zero/constant sum | security, matrix games, complementarity, correlation | minimax/security equivalence and one constant-sum correlation result | `Core.ZeroSum`; existence in `Analysis` |
| communication | observable babbling, exact pure-Nash outcome laws, mixed-Nash-to-CE, and finite Electronic Mail delivered; conditional public-signal disintegration and staged cheap talk remain | babbling plus induced correlation through the ordinary equilibrium predicates | static ownership validated by EXP-046/D18, EXP-047/D19, and EXP-048/D20; Protocol only when theorem-observable timing matters |
| mechanisms and finite auctions | Vickrey, first-price, reserve, VCG, combinatorial, all-pay, exact knapsack search, real pivot-VCG knapsack, repaired executable approximation, finite hidden-action contracts, revelation, finite persuasion, quasilinear weak monotonicity, affine maximizers, and topology-free single-parameter payment bounds | **M-CONTRACT complete (EXP-065/D32), canonical finite-support revelation, information design, truthful Bayesian welfare/participation, feasible posterior laws, D33's monotonicity/affine consumers, topology-free Myerson algebra, and returned-allocation half approximation complete (EXP-056/D27);** envelope integrals and uniqueness remain behind M-BAYES/D11 | coordinated mechanism root with native principal-agent semantics, canonical Bayesian forms, and separately audited auction semantic, executable, and correctness leaves |
| social choice and voting | May, median voter, Gibbard-Satterthwaite, delegation, liquid democracy | one rule theorem and one strategic theorem without conflating rankings with lotteries | `Core` foundations plus coordinated voting modules |

Each lane first inventories its entire pinned family. Once the hostile result
passes, routine leaf recovery should be broad and parallel. A lane closes when
all its in-scope declarations are classified and all `port`/`adapt`
obligations build.

## 8. Wave 3: sequential and language recovery

Status: NFG, EFG, MAID, and FOSG recovery is unblocked; other languages retain
their named gates.

Languages share execution and information infrastructure, not one mandatory
surface syntax.

| Lane | First gate | Recovery after the gate |
|---|---|---|
| NFG | **passed and recovered:** EXP-042/T4 validates compilation; all 126 pinned declarations are classified with no deferred rows | broad examples, observable cheap talk, exact half/half mixed Nash, and the complete Matching Pennies correlated-equilibrium characterization are recovered through their canonical shared layers |
| EFG | W1-A and W1-B complete | syntax-facing histories, refinements, perfect recall, Kuhn, sequential rationality, one-shot deviation, and strategic extraction |
| MAID | **passed (EXP-041/T3):** an incomparable-node typed DAG compiles locally; native and compiled outcome laws and source-owner Nash equilibrium are equivalent | public evaluation, compiler, and strategic transfer promoted; next refinements and Kuhn specialization |
| FOSG | **generic bridge gate passed (EXP-042/T4; EXP-059/060/061, D30):** the stable explicit-order FOSG-to-EFG bridge retains exact source histories while hiding within-round choices; policy projection/translation are full inverses, resolver-only public/private/own-action replay, inactive slots, literal all-round history laws, and order transport pass | **Native history/Kuhn, reachable observation-model, reachable/step-independence/terminal-law/outcome-closure, Compile, Examples, Serial, and the 104-declaration live bridge chain are classified;** the utility-free simultaneous example now exercises the canonical NFG-to-FOSG-to-EFG path, and the non-semantics-preserving serial machine is retired; continue the remaining 81-row exact L-FOSG queue while counterfactual reach, CFR, ordinary continuation coefficients, augmentation, strategic/utility transfer, and expressiveness retain separate gates |
| multi-round | exact previous-action information and imperfect monitoring survive the compiler | stochastic, repeated, absent-minded, and Kuhn-facing theorems |
| intrinsic games | **D31-native layer recovered (EXP-062, D31):** `Languages.Intrinsic` owns capability-light configurations, information-local pure rules, closed-loop solvability, explicit-slot configuration-dependent causality, stable native examples, and an opt-in solution-selection theorem leaf derived only from `IsSolvable` | choose the next gate explicitly: player ownership/outcome preferences, temporal compilation, perfect recall, mixed/behavioral strategy, PMF/utility, and Kuhn remain separate |
| bridges and expressiveness | two real transfers compose more cheaply than direct named proofs | only the earned relation or composition API; otherwise classify v1 transport as retired |
| open games | one compositional theorem with no duplicate stable equilibrium predicate | `GameTheory.Frontier`, not the stable language umbrella |

Every syntax module must reject solution-concept reachability. Every compiler
records its native data, forgotten data, evaluation theorem, workaround list,
and source-level transport count. A broad language port starts only after the
first gate for that language passes.

Wave 3 also owns v1's standalone Kuhn and Zermelo theorem families. General
backward induction belongs to Protocol; a syntax-specific wrapper belongs only
where the language adds real premises.

## 9. Wave 4: coordinated parallel mature domains

Status: partially unlocked.

These domains are not downstream of `GameForm` merely because they are game
theory.

| Domain | Gate theorem | Integration rule |
|---|---|---|
| coalitional games | Bondareva-Shapley or convex-game core nonemptiness after the existing Shapley/core base | larger theory moves to `GameTheory.Cooperative`; no artificial action profile |
| matching and market design | Gale-Shapley stability and perfect matching, then strategyproofness or rural hospitals | native preferences and matchings; share order/list mathematics only |
| bargaining | Nash solution affine invariance on an honest feasible utility set | native convex feasible-set branch under `Analysis` when topology is used |
| finite fair division | round-robin EF1 and one envy-cycle or maximin-share result | coordinated mechanism branch; no measurable cake assumptions |
| knowledge and epistemic games | **complete for pinned v1:** exact/approximate common knowledge and both agreement theorems | any future Protocol bridge must state the extra state-view premise; broader epistemic work is a new consumer, not recovery debt |
| evolutionary stability | **passed (EXP-044/D17):** ESS implies canonical symmetric Nash | recover static ESS/NSS in `Evolutionary`; dynamics do not enter until a named theorem measures scalar/topology needs |
| contracts | **passed and recovered (EXP-065/D32):** stochastic welfare accounting, finite-action maximizer existence, and participation against an explicit outside option, with all 23 pinned declarations classified | native `Mechanism.PrincipalAgent` branch over `FinDist`; no artificial strategic players, and richer contract-selection/adverse-selection models remain separate consumers |

Coalitional foundations and the Shapley characterization are already validated;
their remaining theorem inventory may be harvested immediately. The other
rows begin with an experiment if their owner is still unsettled.

Divisible cake cutting that essentially uses measures, continuous knives, or
topological existence is outside the finite v1 release and enters the D11
measurable program rather than weakening finite fair division.

## 10. Wave 5: analysis and executable depth

Status: demand-driven.

Analysis and computation are capabilities used by subfields, not dumping
grounds for difficult proofs.

The analysis lane includes:

- **correlated- and coarse-correlated-equilibrium existence complete** through
  the topology-free Nash-to-correlation bridges and `Analysis.Nash`;
- demand-driven recovery of reusable Brouwer, KKM, Scarf, or simplex
  approximation mathematics only when a selected theorem needs it;
- convex bargaining and continuous social-choice results admitted by their
  domain gate;
- the existing one-way Protocol and Repeated bridges;
- no topology in Core merely to simplify an existence proof.

The executable lane includes:

- broader rational-table checks and specifications;
- finite reachability, dominance, best-response, and equilibrium certificates;
- solver-generated proof certificates only when a kernel-checked verifier and
  acceptable dependency/toolchain surface pass a new D13 experiment;
- no claim that enumeration or a certificate oracle is the proof semantics;
- no exact general mixed-equilibrium solver as a release requirement.

General mathematics is recovered from pinned `Math/` by live consumer, searched
in Mathlib first, and placed in `GameTheoryMath` only when it is independently
reusable. The old `Math/` tree is not ported wholesale.

## 11. Wave 6: accounting and release

Status: blocked by the capability matrix's critical gaps and the release audits
below; open-ended curation elsewhere in Waves 0-5 is not itself a blocker.

The v1-scope release gate requires:

1. every pinned family mapped to a capability row or an explicit mature-scope
   exclusion;
2. no `critical gap` in the capability matrix and no unaccepted loss hidden by
   a `partial` verdict;
3. every parity claim backed by a bounded declaration ledger with no open
   `port`, `adapt`, or `subsumed` obligation in that claim's scope;
4. every `deferred` row names its missing gate and remains visibly excluded
   from the capability claim;
5. the exact unaccounted declaration remainder is reported as curation risk,
   without being converted into a release percentage;
6. public umbrellas reviewed for intentional inclusion and opt-in boundaries;
7. one reader-facing example per supported subfield;
8. full build with warnings treated as failures;
9. all architecture, trust, reachability, transport, and coverage audits;
10. axiom audit on every flagship theorem;
11. cold-build and representative incremental-build measurements;
12. a generated release report listing support, provisional surfaces,
    Frontier work, and explicit non-goals.

Source compatibility with v1 is not a release gate.

## 12. Mature subfields that v1 underrepresented

The pinned tree is the recovery baseline, not a definition of game theory.
The following are mature subjects that are absent or represented by only a
small example in v1. They belong to the mature track, but they do not displace
the protected recovery waves.

| Candidate | Evidence of the v1 blind spot | First serious slice | Candidate placement, not yet an API commitment |
|---|---|---|---|
| finite stochastic/Markov games | one pinned `MultiRound/StochasticGame.lean`, no general value or stationary-equilibrium theory | **domain gate passed (EXP-050/D22 and EXP-051/D23):** native finite-horizon/uniform semantics, an exact uniform deviation-cap certificate equivalence, plus normalized two-player zero-sum Shapley contraction, unique value, and stationary statewise saddles | public opt-in `Stochastic` root using `FinDist` transitions and a named Protocol bridge; discounted value in the one-way `Analysis.Stochastic` bridge; general uniform existence remains an excluded open conjecture |
| games on graphs and reactive synthesis | no reachability, safety, Büchi, parity, or mean-payoff family | finite reachability game with executable attractor and memoryless determinacy proof | independent graph-game root; compare its arena with Protocol before sharing |
| graphical and network games | no local-interaction representation | compile a tree graphical game to `GameForm` and preserve local payoff/Nash facts | language/domain branch over the static core |
| algorithmic game theory and complexity | executable support is enumeration-oriented and v1 has no complexity layer | one verified reduction or certificate family with explicit size/cost theorem | `Finite`, `GameTheoryMath`, and an experiment-gated complexity vocabulary |
| Stackelberg and security games | one NFG Stackelberg example, no domain theory | finite leader-follower value with explicit tie-breaking and a checked response certificate | coordinated static/mechanism branch |
| evolutionary and population dynamics | static ESS/NSS parity is complete; replicator and population dynamics are absent | simplex invariance for one finite replicator dynamic, without moving ESS under Analysis | stable `Evolutionary` root plus opt-in `Analysis.Evolutionary` |
| network formation and cooperative cost sharing | coalitional values exist, formation dynamics and cost-sharing mechanisms do not | one potential or core theorem on a finite network-formation game | cooperative or static branch, decided by the theorem's native data |
| richer matching and market design | stable matching exists, but school choice, matching with contracts, exchange, and richer market constraints do not | deferred acceptance with one strategyproofness or rural-hospitals extension beyond the pinned model | `GameTheory.Cooperative`/market-design branch over native preferences |
| cooperative solution depth | v1 has core, Shapley, Banzhaf, and balancedness, but no nucleolus or least-core family | finite least-core or nucleolus characterization with an independently checkable optimization certificate | `GameTheory.Cooperative`; optimization remains a named Analysis/Finite bridge |
| psychological and behavioral games | no belief-dependent utility hierarchy or behavioral solution theory | one finite psychological-game example showing why ordinary utility on outcomes is insufficient | provisional parallel preference/belief branch |
| mean-field and continuum-player games | absent | finite-population approximation statement before any PDE commitment | post-v1 `Analysis`/Frontier program behind D11 |
| differential and continuous-time games | absent | a finite-state or linear-quadratic statement chosen only after scalar and integration audit | post-v1 `Analysis`/Frontier program |

Admission rules for a mature blind spot:

1. produce a short literature and Mathlib survey;
2. select a theorem recognized independently of this repository;
3. identify the smallest overlap with stable vocabulary;
4. reserve an experiment if representation or ownership is unsettled;
5. pass the normal subfield-support definition;
6. enter the stable umbrella only after API review and a second nondegenerate
   theorem.

## 13. Research Frontier directions

These are research programs, not release promises. Their purpose is to exploit
the clean stable layers without turning a current fashion into a foundation.

| Direction | Why this repository is unusually well placed | Admission experiment | Promotion barrier |
|---|---|---|---|
| kernel-checked equilibrium and optimization certificates | D10 already separates untrusted search from trusted verification | rational CE, zero-sum, or dominance certificate with dependency and axiom audit | toolchain stability, small verifier, two mature consumers |
| causal and interventional games | MAID syntax, information, policy, and Protocol layers are already distinct | intervention commuting with one MAID evaluation and one strategic projection | causal data must not leak into ordinary game forms |
| multi-agent learning in Markov games | static regret/CCE and a future stochastic layer can meet at a named bridge | finite-horizon Markov no-regret-to-CCE theorem | no opaque simulator assumptions in proof semantics |
| robust and ambiguity-aware games | preferences, Bayesian data, and finite laws are separated | finite ambiguity set with robust best response and equilibrium existence | scalar/order assumptions remain local; no generic probability class |
| compositional institutions and open games | v1 supplies evidence and failure modes; Frontier isolates native equilibrium data | one parallel/sequential composition theorem with an external semantic comparison | no duplicate stable equilibrium API and demonstrated composition payoff |
| verified mechanism and information-design synthesis | Bayesian, social-choice, finite algorithm, and certificate layers can cooperate | synthesize or verify a small persuasion/mechanism instance and prove obedience/IC | solver remains untrusted; public theorem is representation-independent |
| large-population and differentiable games | Analysis is opt-in and can host geometry without contaminating finite Core | one finite-dimensional approximation or convergence result | D11 measurable/continuous decision and reusable analytic infrastructure |
| formal multi-agent safety and adversarial planning | Protocol histories and graph games can express strategic environments | finite safety/reachability game with a checked winning strategy certificate | safety terminology must correspond to a precise mathematical objective |

The promotion ladder is:

```text
watchlist
  -> EXP-NNN under Experimental
  -> proved, opt-in Frontier module
  -> provisional stable root after two independent theorems
  -> stable support after the normal domain gate
```

Nothing promotes directly from a paper idea to Core.

### Research signals, not dependencies

The horizon above is grounded in established and active mathematical programs:

- Shapley's finite stochastic games motivate the discounted Markov-game slice:
  <https://www.pnas.org/doi/10.1073/pnas.39.10.1095>.
- Graphical games motivate a local-interaction representation:
  <https://arxiv.org/abs/1301.2281>.
- Games on graphs connect game theory to verification and synthesis:
  <https://arxiv.org/abs/2305.10546>.
- Mean-field games motivate a deliberately post-D11 large-population program:
  <https://doi.org/10.1016/j.crma.2006.09.019>.
- Bayesian persuasion supplies a mature information-design target:
  <https://www.aeaweb.org/articles?id=10.1257/aer.101.6.2590>.
- Recent Markov-game learning results show a natural bridge from regret and CCE:
  <https://proceedings.mlr.press/v242/mao24a.html>.
- Structural causal games provide a concrete interventional extension of MAIDs:
  <https://arxiv.org/abs/2301.02324>.
- Compositional open-game work supplies an external test for Frontier:
  <https://arxiv.org/abs/2101.12045>.

These links justify keeping the directions visible. They do not authorize an
API, dependency, or theorem statement; each admission experiment still performs
its own current literature and dependency review.

## 14. Status and reporting cadence

At the end of each integrated work package:

1. update the family and declaration ledgers;
2. update the owning wave row;
3. record exact validation commands;
4. record any API change or newly exposed gap;
5. attribute adapted v1 results to their pinned paths;
6. report whether the package improved a capability verdict, exact accounting,
   both, or Frontier only.

At each domain gate:

1. run the full build and all phase audits;
2. check flagship axioms;
3. review public imports and module documentation;
4. update README's current wave;
5. verify that Frontier capacity and reverse-dependency rules still hold.

Quarterly or after five domain gates, whichever comes first, review the
beyond-v1 horizon. A direction may be promoted, narrowed, or removed. Mature v1
capability status is not renegotiated during that review.

### Current release-coverage checkpoint

Last integrated checkpoint: 2026-08-08, after the affine-maximizer recovery.
These counts are milestones, not declaration-port percentages.

| Release dimension | Current evidence | Release condition |
|---|---|---|
| mature workflows | 22 better, 5 comparable, 9 partial, 6 critical gaps | zero critical gaps; each partial audited for loss of mature use |
| frozen promises | F1-F8 and T1-T4 complete | remain green under the final public-import review |
| exact accounting | 1,969 of 8,324 pinned declarations have reviewed dispositions | report the exact remainder; complete every ledger supporting a parity claim |
| current DFS seam | D33 monotonicity 5/5, affine maximizers 13/13, and Myerson 38/38 classified with 19 analytic deferrals | retain the envelope/uniqueness half behind the D11 Analysis gate |
| next capability rotation | learning dynamics | finite potential-game fictitious play, then the approachability bridge |
| release engineering | incremental full build and structural/coverage audits green | final cold build, flagship axiom sweep, examples, and generated release report |

## 15. Immediate queue

The next work is ordered. T-ZER is closed: the language-independent
well-founded Bellman construction, transparent EFG wrapper, and hostile
chance/off-path witness now cover its mature workflow without bounded utility
or a second tree evaluator.

Continuous enforcement is now present in `.github/workflows/ci.yml`: a clean
hosted checkout runs the full `.andSubmodules` build, the self-contained Phase
1-3 audits, and the tracked-index structural coverage gate. The
pinned-reference-dependent Phase 0 and full coverage source/freshness checks
remain explicit local release gates until their exact evidence snapshot is
provisioned in CI.

1. **complete:** the safe integration debt now identifies ε-CCE with the
   canonical approximate-equilibrium preference, reuses the Protocol
   singleton-joint and unique-predecessor tree toolkit, and documents
   intentional opt-in leaves rather than importing them into capability-light
   syntax roots;
2. **closed without a semantic redesign:** the MAID root now re-exports D14's
   validated typed `General` surface and the old three-node witness is explicit
   post-architecture evidence.  The EFG/FOSG ownership audit retains separate
   transparent records and domain-facing Kuhn names: their mathematical proof
   spine is already factored at `InformationModel`, while `EFG extends FOSG`
   would thicken the EFG syntax import closure and change public constructor and
   qualified-projection ownership without helping D30.  Any future common
   carrier, `extends`, compiler relocation, or Kuhn import-direction change
   still requires a reserved experiment;
3. **complete:** EXP-064 builds D-REPEAT's public-monitoring equilibrium waist:
   discounted continuation values, canonical perfect-public equilibrium, and
   the bounded one-shot-deviation equivalence.  Its noisy branch-dependent
   witness includes a strict unilateral loss and a zero-probability history,
   without introducing infinite realized-path probability;
4. **complete:** EXP-065/D32 closes M-CONTRACT with a finite-support
   principal-agent model, stochastic welfare identity, incentivized-action
   existence, explicit participation, a premise-erasing negative control, and
   a complete 23/23 pinned declaration ledger;
5. **in progress:** canonical finite-support revelation, all 21 declarations in
   the pinned information-design file, and the four remaining truthful
   welfare/participation declarations are recovered without duplicate
   probability, plausibility, mechanism, or equilibrium layers; all 19
   single/joint feasible-posterior declarations are also complete; EXP-066/D33
   validates quasilinear ownership; the pinned monotonicity and affine-
   maximizer files are now 5/5 and 13/13 recovered, and all 38 Myerson rows are
   classified with its 19 topology-free declarations promoted and 19 analytic
   declarations kept behind D11.  The lead queue now rotates to the learning
   critical gap, while the remaining 81-row L-FOSG classification and D-REPEAT
   rank/self-generation/uniform harvesting, and validated static and language
   leaf recovery remain BFS work;
6. keep beyond-v1 uniform-existence and Frontier work off the lead queue: the
   sibling branch remains research evidence, and no stochastic advance
   discharges L-ROUND or repeated-game parity.

This queue may change when an experiment refutes an assumption, but a change
must update this document rather than silently starting whichever domain is
most convenient.
