# Stochastic games: the uniform-equilibrium program

This directory holds the formalization effort around the **uniform equilibrium
existence problem** — the central open problem of stochastic game theory: every
stochastic game with finitely many players, states, and actions admits a uniform
equilibrium payoff from every initial state.

The conjecture is stated in [`Uniform.lean`](Uniform.lean) as
`StochasticGame.exists_uniformDeviationCapConstructor` and carries the repository's
**only intentional `sorry`** (enforced by `scripts/check_lean_placeholders.py`).
Everything else in this directory is sorry-free; keeper capstones are additionally
axiom-audited (`propext`, `Classical.choice`, `Quot.sound` only).

## How this directory is organized

The directory is a **research program**, not a conventional library. A small spine
of infrastructure files evolves continuously; around it, a large number of
exploratory probe files record attempted routes as complete, machine-checked
developments. Probes promote their unresolved residue to explicitly *named
hypotheses* (`Has...`/`Is... : Prop`) instead of `sorry`, and candidate interfaces
are stress-tested against falsifier games (the Big Match no-go is the permanent
baseline). Dead routes are killed by *proved* no-go theorems, kept permanently.

### The spine

```
Basic ─→ StageGame ─→ Uniform (the conjecture; both waists)
  │          │
  │          └─→ Discounted ─→ ZeroSum (Shapley) ─→ Fink ─→ FinkLimit …
  │                     │
  └─→ Adaptive ─→ AdaptiveCertificate ─→ PublicPhaseCertificate …
```

- **Construction waist**: `HasUniformDeviationCapConstructor` (`Uniform.lean`) —
  the quantitative form every construction must reach; proved exactly equivalent
  to the semantic uniform-payoff property.
- **Verification waist**: the adaptive certificates (`AdaptiveCertificate.lean`) —
  proof-facing sufficient conditions (submartingale floor / decoupled bound /
  one-sided guarantee + zero-sum wrapper) that compile candidate constructions
  into `IsUniformEquilibriumPayoff`.

### Fixed public response architectures

`PublicResponseCredibilityCriterion.lean` and its support-pruned companion
`ReachablePublicResponseCredibilityCriterion.lean` supply a second
proof-facing route for a **given finite public Markov response architecture**.
Target harmonicity, unilateral target superharmonicity, a neutral-occupation
inequality, and prescribed delivery produce bounded potentials, uniform
`O(1/N)` delivery and deviation caps, rebasing, and an enforcement ledger
consumed by the existing public-response compilers.

`ArbitraryStartPrescribedDeliveryTelescope.lean` and
`ArbitraryStartUnilateralCap.lean` make the sound part of the corrected Q96
domain split explicit.  The first gives exact endpoint telescopes and uniform
`O(1/N)` delivery after rebasing at any node in the declared
prescribed-closed region.  The second gives the corresponding endpoint and
uniform unilateral cap after rebasing at any node in the selected player's
owner-specific arena.  Neither module enlarges those domains to their union or
asserts the Q96 converse, recurrent coverage, necessity, or obstruction
extraction.

`ExplicitDomainGainBiasVerifier.lean` combines those two domain-correct
telescopes behind one shared modulus and feeds the existing enforcement ledger
at prescribed entries, where membership in every owner arena is available.

`SplitDomainGainBiasVerifier.lean` separates Q96's delivery union from its
owner-specific arenas, adapts each half to the existing APIs, reuses the
mean-ergodic and controlled-Farkas bias theorems, and proves exact endpoint and
shared-modulus gain--bias sufficiency without a recurrent-coverage assumption.

`SplitDomainAsymptoticConverse.lean` proves the two target-side converse steps
on those exact domains.  Shifted prescribed Cesaro delivery forces prescribed
target harmonicity on the delivery union, and an eventual vanishing-error cap
for every pure one-step rollout forces target superharmonicity on the selected
owner's arena.  The hypotheses use the iterated finite configuration kernel;
identifying those rollouts with the architecture's history semantics remains a
separate finite-horizon law bridge.

`UncoveredPrescribedClassCounterexample.lean` is the two-player/two-node Q96
regression: all four target/occupation-side checks pass on their stated
domains, while the escaped prescribed class is outside player one's arena and
has linear positive delivery error, so its Poisson equation is impossible.

`FTVCyclicCredibility.lean` is the actual-data acceptance test for this
route.  It constructs the Flesch--Thuijsman--Vrieze three-player quitting
game, its ten-configuration public controller (three live clock phases and
seven absorbing children), and the complete target assignment.  It proves
all four criterion conditions and compiles them into an enforcement ledger,
a public-phase punishment system, and an adaptive certificate for payoff
`(1,2,1)` at every positive error.  This is a formal sufficiency result for
that supplied architecture.  The sharp `11/7` finite-horizon modulus and the
necessity, phase-minimality, and rigidity results studied in Question 97 are
not formalized in that module.

`FTVCyclicMinimality.lean` supplies Question 97's exact finite-algebra layer.
For any live cyclic packet satisfying the table-expanded `(Q1)--(Q5)`
conditions with initial promise `(1,2,1)`, it derives the exposed solo-outcome
face, a unique active role in every phase, coverage of all three roles, the
lower bound `K ≥ 3`, and literal uniqueness of the normalized three-phase
packet.  It also constructs that packet and checks all conditions, including
the inactive complementarity inequalities.  The module does not formalize
the equilibrium-theoretic necessity/sufficiency of `(Q1)--(Q5)`, the sharp
finite-horizon modulus, or Question 97's approximate-regret boundary.

`ArchitectureCapSeparators.lean` is a regression guard for the cap notion.
It proves on actual finite games that a supplied architecture's exact
unilateral cap can be `1` while the corresponding one-shot opponent minmax is
`0`, and that testing one deviation followed by immediate obedience can miss
a two-step history-dependent strategy whose average payoff converges to `1`.
Thus neither static minmax nor one-stage-deviation-and-return may replace the
complete unilateral behavior-strategy cap in the credibility interface.

This is deliberately a supplied-object verifier. It does not construct an
architecture from an arbitrary game or target, prove the finite-class
converse, bound the number of public configurations, model hidden randomized
memory, or establish that finite public architectures cover all
uniform-equilibrium payoffs. Those stronger claims have separate mathematical
and formalization status in the research frontier. In particular, the
support-pruned module proves the criterion-to-ledger direction at its declared
entry; it does not formalize the corrected Question 96 converse on the union
of owner-specific reachable arenas.

### Proved results (special cases of the conjecture)

| Game class | Theorem | File |
|---|---|---|
| Absorbing initial state | `exists_uniformEquilibriumPayoff_of_isAbsorbingState` | `Absorbing.lean` |
| Single-state games | `exists_uniformEquilibriumPayoff_of_subsingleton_state` | `Absorbing.lean` |
| Action-independent transitions (full generality, incl. reducible/periodic) | `exists_uniformEquilibriumPayoff_of_isActionIndependent` | `TransitionIndependent.lean` |
| All children absorbing after one step | `exists_uniformEquilibriumPayoff_of_absorbingChildren` | `OneStepAbsorbingChildUniform.lean` |
| Zero-sum single-controller (modulo one named LP-extraction hypothesis) | `exists_uniformEquilibriumPayoff_of_singleController` | `SingleController.lean` |
| **The Big Match** (Blackwell–Ferguson 1968) | `exists_uniformEquilibriumPayoff_live` | `BigMatchUniform.lean` |

Supporting classical theorems, fully proved: Fink's discounted stationary
equilibria (`exists_isDiscountedStationaryBellmanEq`, `Fink.lean`), Shapley's
discounted zero-sum value with exact discounted Nash profiles
(`shapleyBehaviorProfile_isDiscountedNash`, `ZeroSum.lean`), and a **conditional
Mertens–Neyman theorem** reducing the zero-sum uniform value to two named
hypotheses (`uniformValue_of_rowColumnTrackingCertificates`,
`MertensNeymanCriterion.lean`).

### Negative results (no-go keepers)

No-go and counterexample files are first-class results: each kills a specific
route, is machine-checked, and constrains all future interfaces. Load-bearing
ones include:

- `BigMatchNoMarkov.lean` — uniform witnesses must be history-dependent.
- `BigMatchFinkEndpoint.lean` — refutes the calendar-Markov Fink endpoint.
- `BigMatchDeficitIndexNoGo.lean` — the linear running-deficit index is not a
  universal Mertens–Neyman constructor.
- `DiscountBiasNoGo.lean` — unscaled tail variation cannot control the scaled
  discount-bias drift (the mechanism-2/3 boundary).
- `FinkTangentCounterexample.lean`, `FinkSelectionCounterexample.lean` — the
  supported-harmonic-adjustment route is selection-resistant.
- `PureExternalityCycle.lean` — analytic provenance cannot supply the routing
  gluing invariant.

### Family map (file-name prefixes)

| Prefix | Topic |
|---|---|
| `Adaptive*` | History-adaptive potentials and the certificate verification interface |
| `Analytic*` | Analytic-in-discount Bellman germs: hierarchy, endpoints (λ → 0⁺), obstruction coordinates |
| `Bellman*` | Algebraic Bellman varieties, germs, sign cells, curve gates |
| `BigMatch*` | The Big Match worked instance and its no-gos |
| `FiniteBias*` | Finite-bias canonical endpoint alternatives |
| `Fink*` | Discounted stationary equilibria and the vanishing-discount program |
| `MertensNeyman*` | The conditional MN criterion and adaptive account strategies |
| `PlayerNeutral*` / `PlayerOwned*` / `PlayerInvisible*` | Occupation/charge accounts by action orientation (continuation-neutral vs deviator-owned vs invisible) |
| `Prescribed*` / `MovingEndpoint*` / `Endpoint*` | Endpoint-target transport probes |
| `ProcessedHarmonic*` | Harmonic-adjustment response processing |
| `Public*` | Public-history machinery: stopping rules, phase certificates, response architectures and credibility criteria, punishment systems, public coins |
| `Quitting*` | Quitting games (translation lemmas to the uniform concept) |

### File status conventions

- **Core**: the spine files above — evolving infrastructure.
- **Results**: the proved special cases and classical theorems in the tables.
- **No-go / counterexample**: permanent negative results (usually named so).
- **Everything else**: exploratory probes — write-once, sorry-free records of
  attempted routes, kept for their named interfaces and falsifiers. A probe
  having no importers does **not** mean it is dead; probes are consumed by the
  research program, not (yet) by other modules.

The detailed research logs, question corpus, and route scoreboard are maintained
outside the repository (untracked `ephemeral/`); this README is the in-tree map.
The generic mathematics developed for the program (couplings, stitched
martingales, hitting-time potentials, closed classes, occupation flows, curve
selection) lives under `Math/Probability/` and `Math/CurveSelection/`.
