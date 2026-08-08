# Uniform-equilibrium pipeline archive

This file is a one-way archive. Items move here from
[`PIPELINE.md`](PIPELINE.md) once their status reaches `DONE` (or they are
explicitly superseded), and they do not move back -- if a `DONE` item needs
further work, that work is tracked under a new ID in `PIPELINE.md`, not by
resurrecting the old entry here. Verbatim preservation of every item's content
applies here exactly as it does in the main pipeline file.

## Lean formalization lane

### `LEAN-P0-1` — landed debt-transport, cycle-mismatch, FTV, and germ-bridge results this cycle

- **Status:** DONE
- **Lane:** P0
- **Record:** this pipeline

**Objective.** Landed this cycle, for the record: the exact debt transport law;
the cycle mismatch characterization in both branches; the conditional reduction
from an admissible absorbing cycle to a uniform payoff, with no strategy-class
gap; the zero-solo branch and the disjunction; the FTV table's uniform payoff
`(1,2,1)`; periodic extension and cycle-pinned nonnegativity; the
quitting-to-analytic-germ bridge; and `Math.AnalyticOrderComparison`.

**State.** `DONE`, all axiom-clean. Recorded here because the lane previously
had no row for any of it.

**Acceptance.** Consumed by the carrier group; the reduction's *completeness* is
refuted, so none of this closes the conjecture.

### `LEAN-P0-3` — pin the matching scaling case in the germ bridge

- **Status:** DONE
- **Lane:** P0
- **Depends:** `QuittingAnalyticGerm`.
- **Record:** [carrier group](../../ideas/AbsorbingCycleCarrier/README.md)

**Objective.** Pin the matching scaling case in the germ bridge: expand the
absorption product to first order so `t^q / absorption` is pinned rather than
squeezed between `1/(n·Σa)` and `1/Σa`.

**State.** `DONE` on `uniform-existence`, axiom-clean. Route: not an explicit
product expansion but the two-sided Bonferroni estimate of
`Math/BonferroniProductBounds.lean` plus a new
`Math.analyticOrderAt_eq_of_tendsto_div_pow`.
`GameTheory.analyticOrderAt_quittingGermAbsorption_eq` gives
`analyticOrderAt (quittingGermAbsorption g) 0 = m` with leading coefficient
exactly `∑ a` and `t^m / absorption → 1/∑ a`, under `1 ≤ m`, which is free in
the matching branch because `g.ramification = m` and the ramification is
positive. All six transfer directions across the three regimes are landed.

**Acceptance.** Completes the three-way scaling comparison on absorption itself,
which the vanishing-branch argument consumes.

### `LEAN-P0-4` — discharge nondegeneracy of the germ quit family

- **Status:** DONE
- **Lane:** P0
- **Depends:** `QuittingAnalyticGerm`.
- **Record:** [signed
  accumulation](../../ideas/AbsorbingCycleCarrier/TheSignedAccumulationIsTheGain.md)

**Objective.** Discharge nondegeneracy of the germ quit family.

**State.** `DONE` at `7d518eb`: degeneracy is not a gap but the zero-solo
branch, so the entry point is restated with the germ-internal hypothesis
replaced by "not zero-solo".

**Acceptance.** Without it the normalized direction is undefined and the
leading-order package is vacuous on that germ.

### `LEAN-F0-7` — the tail-average transfer is mirrored, not doubled

- **Status:** DONE
- **Lane:** F0
- **Depends:** `LiminfAverageBridge`, `InfinitePlayMeasure`.
- **Record:** [Notion lattice](NotionLattice.md)

**Objective.** Settle how `IsUniformEquilibriumPayoff` transfers to the
tail-average notions, and record the limsup node the registry lacked.

**State.** Landed, and it refutes the framing this row was opened with. That
framing said the liminf on-path failure signals liminf is the wrong target,
with limsup getting **both** directions free. Only half is right.

Negation exchanges the two limits unconditionally, so each abstract lemma
dualizes with no change to the `ENNReal`/Fatou internals. But dualizing the
*conditional* lemma yields a *conditional* statement: the almost-sure
hypothesis is relabelled, not removed. The moving-bump family dualizes too,
refuting the unconditional limsup-deviation bound exactly as the original
refutes the unconditional liminf-on-path bound.

So the split is **mirrored**: liminf gives the deviation direction free and the
on-path direction conditional; limsup gives the on-path direction free and the
deviation direction conditional. Neither tail notion is the uniform notion's
"natural home" — each buys one direction and owes the other. Both game
corollaries are free of any representation hypothesis, since they run on the
landed play measure.

**Acceptance.** The two-directional limsup transfer as a named theorem, the
limsup node and its edges in the registry, and the liminf edges restated as the
conditional ones they are. Cheapest adjacent item: formalize the
typewriter/moving-bump family, converting the registry's FALSE-by-reason edge
into FALSE-by-machine.

### `LEAN-P0-8` — joint complementarity, and absorption derived rather than assumed

- **Status:** DONE (`M+L`), 2026-08-05
- **Lane:** P0
- **Depends:** the fixed-opponents stage primitives; the cyclic-block predicate.
- **Record:** this file

**Objective.** Give the repository a predicate for "an arbitrary infinite row
sequence is complementary in every coordinate", and decide whether absorption
follows from optimality.

**State.** Both landed in `UniformEquilibrium/Quitting/Boundary/Repair/JointComplementarity.lean`, `sorry`-free.

The predicate closes a **structural absence**: the tree had only a
single-coordinate live-value notion and a periodic-only cyclic-block notion, so
claims quantified over "every complementary sequence" — which several recent
results are — **could not be stated at all**. They now can. The tail value
converges from boundedness alone, with no assumption of eventual absorption, and
the compatibility bridge is proved: a periodic sequence satisfying the cyclic
block predicate satisfies this one. That bridge needed a
uniqueness-of-bounded-solutions lemma and a proof that the periodic extension's
joint survival vanishes from *every* start, not just from zero.

**The new mathematics is the second result: a positive solo reward forces
absorption.** If a sequence is jointly complementary and some coordinate has
strictly positive solo reward, play absorbs almost surely from every time. Every
prior result in this tree takes absorption as a **hypothesis**; none derived it.
Consequently a non-absorbing complementary sequence requires every solo reward
non-positive — close to the zero-solo branch, which suggests why that branch has
the shape it does rather than being a case that happens to be listed first.

The flagged risk — that the tail value's vanishing depends on what the other
coordinates do — resolved without an extra hypothesis, via a sharper tail bound
against a known survival limit rather than against the reward bound alone.

**Acceptance.** Met. Consumers: this discharges the tail-product step of the
isolated-negative floor argument, and makes the universal claims of the carrier
and certification results formalizable for the first time.

### `LEAN-P0-10` — separate the three contraction deficits and price re-closing

- **Status:** DONE
- **Lane:** P0
- **Depends:** the transport law, the survival-prefix bridge, the anchored
  max-affine object.
- **Record:** [anchored-repair]

**Objective.** Formalize the exact residual formula for closing a modified
block, and machine-check that the same formula **fails** for the optimized
deviation objective.

**State.** `DONE`. Three deficits must not be conflated: the value recursion's,
the deviation recursion's built from deleted products, and a local block's
transported mass. The law is an exact identity for the first, a sharp upper
bound for the second, and false for the third. Prefix survival is a
multiplicative transport factor, never a denominator.

**Seals differ by leg.** The exact identity and the falsity witness are `L`. The
**sharp middle leg is `M [reported]` and has no theorem** — the formalization's
middle deliverable was the transport split, not a bound on rowwise
complementarity loss. Do not cite the three legs under one seal.

**Acceptance.** **DONE, 2026-08-05**, `UniformEquilibrium/Quitting/Boundary/Analytic/SeamPriceResidual.lean`. All four
parts landed. The exact form needed no hypothesis beyond the definitions — the
successor payoff is affine in the tail value with slope the full joint continue
mass, unconditionally. The failure witness is an isolated coordinate at hazard
rates `1/2` and `1/3`, where the mismatch is rate-independent while the full
deficit varies, so no single numerator reproduces it; the deleted deficit there
is exactly `0`. Unit continue mass makes the successor map the identity, so
vanishing absorption gives no pole.

### `LEAN-P0-11` — bridge the two encodings of complementarity

- **Status:** DONE
- **Lane:** P0
- **Depends:** `UniformEquilibrium/Quitting/Cycles/CyclicWeightRowDichotomy.lean`, the Bool-valued spine.
- **Record:** this file

**Objective.** Prove that the real-valued hazard encoding of the gain and
complementarity conditions agrees with the Bool-valued mixture encoding the main
development uses.

**State.** `DONE`, and this was a duplication introduced deliberately and
knowingly. The questions corpus states everything over arrays of reals; the Lean
development states everything over `PMF Bool` mixtures. Formalizing a question's
answer therefore produced a **second** encoding of `Σ_i`, `Γ_i`, `g_i` and
exact complementarity, generic over a finite index type. Both are correct and
neither can currently feed the other.

Until the bridge exists, a theorem proved in one encoding says nothing about the
other, and a reader may reasonably assume otherwise. That is exactly the shape
that rots.

**Acceptance.** **DONE, 2026-08-05**, `UniformEquilibrium/Quitting/Bellman/Finite/HazardRowBridge.lean`. The
encodings are **equivalent**, not merely analogous: quit payoff, continue
payoff, and endpoint difference agree exactly with the real-valued `Σ`, `Γ`, `g`
for every reward and continuation value, with no sign or scope mismatch and no
extra hypotheses. Exact row complementarity corresponds to zero-error root
endpoint Nash in both directions, which the development already identifies with
exact root Nash. The row dichotomy transports as a demonstration.

The proof needed one new combinatorial lemma: the expectation of a family of
independent Bernoulli coordinates expanded as a powerset sum.

One asymmetry, recorded rather than hidden. Mixture to hazards is total; hazards
back to a mixture needs the row in the unit interval, since the polynomials stay
meaningful outside it but no mixture realizes such a row. Harmless where used,
and it means results proved over unrestricted real rows do **not** automatically
transport.

### `LEAN-P1-5` — linear complementarity infrastructure

- **Status:** DONE — `Math/LinearProgramming/SingletonLCP.lean`. Predicate,
  scaling/permutation invariance, the support-pattern reduction, the
  game-facing instantiation, and a closed-form two-coordinate
  characterization with no residual existential. Decidability for rational
  data is **blocked, precisely**: the Fourier–Motzkin/Farkas material is
  Prop-level, not computable; a `Decidable` instance is a separate project.
  The absorption equivalence (`K4`, Q159 §5's numbering — "the relaxed
  compiler", distinct from Q148's `K1`–`K2` above and from
  `InvertedCounterexampleSearch`'s `K1`/`K4`) is now stateable.
- **Lane:** P1
- **Depends:** none.
- **Record:** [exact-vs-relaxed]

**Objective.** Provide the normalized singleton LCP as a Lean object with a
feasibility predicate.

**State.** `DONE`. Several recorded results turn on the feasibility of
`λ ∈ Δ(I)`, `q = Bλ ≥ 0`, `λᵢqᵢ = 0` with `Bᵢⱼ = rᵢ({j}) - rᵢ({i})` — in
particular the equivalence deciding whether absorption can vanish, and with it
whether a diverging period is even possible. **LCP infrastructure now exists**
in `Math/LinearProgramming/SingletonLCP.lean` (`SingletonLCPFeasible`, its
scaling/permutation invariance, the support-pattern reduction via
`singletonLCPFeasible_iff_exists_supportPattern`, and the game-facing
`quittingSingletonLCPFeasible`); the residual-class material stays an ideas
group, not Lean, but formalizing the absorption-vanishing equivalences is no
longer blocked on the predicate itself.

**Acceptance.** The predicate and enough API to state the absorption
equivalence. Decidability for rational data would be a genuine strengthening,
since it turns the criterion into something checkable on a concrete table.

## Conjecture-closing mathematics

### `MATH-P0-6` — port the all-periods non-existence theorem

- **Status:** DONE
- **Lane:** P0
- **Depends:** `LEAN-P0-9`.
- **Record:** [exact-vs-relaxed]

**Objective.** ~~Machine-check that the `ε`-perturbed cyclic three-player weight
admits no exact cycle at any period.~~ **DONE, end to end, 2026-08-05.**
`PerturbedCyclicWeightNoExactCycle.lean` (the label lock, real encoding, with
the `ε = 0` witness and mechanical verification that positivity is needed)
plus `PerturbedCyclicWeightCycleExistenceHoleOccupied.lean` (the cycle-level
transport and the statement against the trichotomy's own predicate:
`¬∃ terminal, IsQuittingCyclicContinuation (ftvRewardEps ε) terminal`,
`ε ∈ (0,2]`, weight alignment machine-checked entry-for-entry). The leading
hard candidate provably lies outside the trichotomy; the cycle route's
incompleteness is an internal theorem, and the published chain is independent
confirmation only.

**State.** `DONE`, and the motivation was settled rather than speculative
before the last piece landed: that weight already **occupies** the
trichotomy's cycle-existence hole. Its solo
values are all `1 > 0`, so the zero-solo branch fails; period one is excluded by
the affine no-join condition, which at one coordinate pair reads `1 + pε ≤ 0`;
period three is excluded because the unperturbed phase-rotation block acquires a
strictly profitable deviation of exactly `ε/2`. Only the all-periods statement
is missing, and it is the published paper's actual contribution — its own
`ρ`-argument through a chain of six lemmas. Nothing weaker suffices, since the
two computations above cover two periods.

The comparison is sound. The terminal payoff is not a surrogate: finite-average
payoff converges to it unconditionally for every profile including off-path
deviations, so an absorbing cyclic continuation block is the same object as the
literature's completely absorbing admissible sequence.

**Acceptance.** The non-existence theorem for this weight at every period, for
`ε ∈ (0, 2]`, via the floor + row dichotomy + label lock. The formalization
must **fail at `ε = 0`** — a cycle exists there — and the point of failure must
be the predecessor-value strict inequality, which is where `ε` enters. The
published theorem remains as independent confirmation only.

### `MATH-P0-11` — the minimal open family: the four-player cyclic phase diagram

- **Status:** **SOLVED (followup answer); stress-point cashout LANDED.** The
  scaled-cyclic calibration and repaired four-player stress weight
  `(x, λ) = (2, 1)` now have concrete production uniform-payoff corollaries
  through supplied circulation certificates. The broader followup family
  analysis remains audited mathematics, not a blanket production theorem.
  Its reported claim was that every `F′(x, λ)`
  with `x > 0` admits a **rational singleton-face circulation** with explicit payoff
  `v(x) = (1, 3−2a, 1/a, 1)`, `a` the root of `2a² + (x−1)a − 1 = 0` —
  `λ`-independent payoff, period `O(1/δ)`; `x ≤ 0` has the exact
  opposite-pair equilibrium. Extracted en route, each valuable beyond the
  family: the **exact true min-max** with explicit boundaries (`x = 1/2`,
  `x₊(λ) = 1 − 1/((1+λ)²(2+λ))`) — answering Q162's Part C for this family
  in advance; **no instant equilibrium even with true-min-max punishment**;
  the complete **singleton-carrier lock classification at four coordinates**;
  a hand-assembled local-defects-to-arbitrary-deviations chain (§5, the
  compiler's shape done directly for this family); and the hardest remaining
  stress point for *exact-cycle classification* (not existence):
  `(x, λ) = (2, 1)`, reported circulation payoff `(1, 2, 2, 1)`. At that
  stress point the certificate, formal punishment-floor inequality, and
  uniform-payoff existence are now machine-checked. The compact selector does
  not identify its existential payoff with `(1, 2, 2, 1)`. **Reported
  strategic consequence**: the circulation class swallowed the minimal
  candidate family, including the diagonal-tight-floor case; production Lean
  currently certifies the stress point, not the whole parameter family. The
  counterexample hunt should target weights outside the circulation class,
  whose true boundary remains the sharpest open question.

  Previous state, kept for the record: Q160's family **collapsed by an authoring flaw**
  (all triples zeroed made all-quit a period-one exact subgame-perfect
  equilibrium at the true min-max, everywhere; a lone continuer must face a
  nondegenerate `(n−1)`-coalition payoff, and the sparsity shrink went one
  size too far — the vacuity rule now covers game families). **The repaired
  family is filed as a followup in the Q160 thread** (no separate question
  file) — every coalition pays its outsiders `1` — with
  the trivial witnesses probed in authoring and recorded as supplied facts;
  the open region is `x > 0`. Salvaged from Q160's answer, methods not
  values: the true-min-max computation, the symmetric-stationary
  classification with its tangential bifurcation, the pure-First-set
  classification. New load-bearing subquestion: `F′`'s min-max plausibly sits
  *tight against the diagonal* (best responses to both extreme opponent
  profiles earn exactly the solo value), a structure no solved example has —
  and the circulation-certificate check against `F′` is Part B, either
  solving `x > 0` outright or exhibiting the first natural habitat outside
  the circulation class.
- **Lane:** P0.
- **Depends:** affine invariance (the `d ≡ 1` normalization it legitimizes),
  the lock, the landing, the LCP and solo-quitter criteria, the phase-switch
  engine; the certsearch toolchain sweeps its parameter square.
- **Record:** this file; Q160.

**Objective.** The open problem restricted to its plausibly minimal natural
habitat: the two-parameter family `F(x, ε)` — four coordinates, cyclic,
diagonal `1`, `G_ε`-sparse, with `x` the payoff to the opposite player, the
first genuinely four-coordinate degree of freedom. Solve its `(x, ε)` phase
diagram: solved zones by explicit criteria, the lock's fate at four
coordinates, existence by rotating relaxed cycles under phase-switch
punishment, or the first certified counterexample candidate.

**State.** Every known theorem misses the family for a stated reason
(joining is profitable, four players, not zero-solo; escape-class coverage to
be verified). The class lattice above it: `n = 4` (minimal open count) →
diagonal-normalized (legitimate only by our affine invariance — the
literature could not state this class) → cyclic-invariant (the home of every
known hard phenomenon) → sparse. The anonymous/fully-symmetric class one
level up is a cheap dissolves-or-sharpens test (one-dimensional symmetric
complementarity) worth one probe, no more. **Attribution caveat**: the
family's open status is internal-knowledge, medium-high confidence; a
literature verification is owed before any public claim.

## Engineering and documentation lane

### `ENG-P2-1` — break the sure-exit cross-check cycle to deduplicate the six pureSetRoot lemmas

- **Status:** DONE 2026-08-05 (production `258d8b5`) — the cross-check
  theorem moved next to its table, the cycle broken, all six lemmas
  deleted with their 18 uses rewired or inlined, no statement changed;
  root build and both gates green.
- **Lane:** engineering
- **Depends:** nothing
- **Record:** this file

**Objective.** `UniformEquilibrium/Quitting/Boundary/Repair/SureSetRepairFullIntervalCounterexample.lean` carries six
file-local `pureSetRoot` lemmas (definitions around lines 370–452) that are
subsumed by the general versions in `UniformEquilibrium/Quitting/Paths/SureExitSet.lean`. They cannot be
rewired today: `UniformEquilibrium/Quitting/Paths/SureExitSet.lean` imports the counterexample file for
its own cross-check section, so the reverse import is a direct two-module cycle
(verified by attempting it — `lake` reports the cycle). All 18 references to
the six names are internal to the counterexample file, so once the cycle is
broken the deletion is mechanical.

**Plan.** Move the cross-check section of `UniformEquilibrium/Quitting/Paths/SureExitSet.lean` (the part
consuming `not_isεAsymptoticNash_directPureSet`) into the counterexample file
or a third module that imports both; drop the import at
`UniformEquilibrium/Quitting/Paths/SureExitSet.lean:10`; then delete the six lemmas and rewire their
in-file uses to the general versions.

**Acceptance.** The six lemmas gone, no duplicate statements across the two
modules, both modules and the root build green, axiom audit unchanged.

### `ENG-P0-1` — put CI under .github/workflows/ and make it green

- **Status:** DONE
- **Lane:** P0
- **Record:** `.github/workflows/ci.yml`

**Objective.** Put CI under `.github/workflows/` and make its documented
commands green.

**State.** `DONE`. Pull requests reject proof placeholders, select a focused,
full, or empty Lean build scope from the changed files, restore both Mathlib and
project `.lake` caches, and build the selected targets. Pushes to `main` and
manual workflow runs perform the full build and repository/axiom audit.

**Acceptance.** Met. The PR path is optimized for fast cached experimentation,
while the push/workflow path retains the complete audit.

### `ENG-P0-2` — make the axiom audit exact and add P0 keeper capstones

- **Status:** DONE
- **Lane:** P0
- **Record:** `scripts/check_lean_placeholders.py`, `scripts/audit_repository.py`

**Objective.** Make axiom audit exact and add P0 keeper capstones.

**State.** `DONE`. The placeholder allowlist is checked in both directions;
the multiline axiom parser returns exactly the requested declarations; and the
quitting/uniform keeper declarations are current and audited.

**Acceptance.** Met. Requested declarations equal parsed declarations, build
targets are explicit, and the keeper capstones are covered by the audit.

### `ENG-P1-1` — classify root-unreachable Lean modules and opaque/native_decide policy

- **Status:** DONE
- **Lane:** P1
- **Record:** `scripts/audit_repository.py`

**Objective.** Classify root-unreachable Lean modules and the
`opaque`/`native_decide` policy.

**State.** `DONE`. The import audit reports zero unclassified root-unreachable
modules. The `BlockPairK11` `opaque`/`native_decide` island is explicitly
allowlisted, and its exemption is guarded by a containment check that fails if
another production module imports it.

**Acceptance.** Met. Every tracked module has an intentional import surface,
and the sole policy exception is explicit and mechanically contained.

## Historical priority snapshots

The following dated priority section is preserved verbatim.

## Priority stack (2026-08-05, post-review reordering)

Adopted after four independent reviews of the position summary
(`ephemeral/ReviewOfSummary.md`); the review acceptance is binding until a
result changes it. The order is by decisiveness, not by ease:

1. **Compiler assembly — CORE DONE** (`QuittingBoundedWindowLanding`,
   `QuittingTruncationLedgerFold`, `QuittingReducedCapConjecture`). The
   landing consumes the bounded predicate directly and composes with WCM
   into a zero-granted-predicate chain; the fold lives at the value level
   (raw-ledger folding proved **false** — the truncation correction
   telescopes to order one at rarely-reached stages; constant `5B·reach`);
   and **the reduced conjecture exists as the third intentional leaf**:
   `HasQuittingLedgerCapPackage`, six arithmetic clauses, with
   package ⟹ conjecture proved gap-free. The program's progress metric is
   now clause shrinkage. Mathematical residue, named: clause (iv) at the
   punished player and in Case 1 (awaits the excursion layer); clause (v)
   below the solo-clipped ceiling (punishment attainment — Q162's band);
   package *production* (the engines). **Of the two paper IOUs the
   equivalence's outer legs lean on, the stationary min-max formula LANDED
   2026-08-05** (production `0829959`, `UniformEquilibrium/Quitting/Stationary/MinMax.lean`):
   `χ = inf_y Φ(y)` with BOTH legs machine-checked in full
   history-dependent generality, no attainment asserted;
   `quittingRootSequenceHazardTerminalValue_const_le_cap` supplies the
   phase-switch hypothesis (P) with `punishCap = Φ(y)` for ANY constant
   row — strictly below the solo-clipped ceiling whenever
   `inf Φ < max(solo, 0)`, witnessed by `QuittingProfitableSoloTwoCoordinate`
   (χ = 0 vs ceiling 2). Clause (v)'s "below the solo-clipped ceiling"
   residue is therefore now reachable machinery, not an IOU. Still owed:
   the Solan–Vieille perfection-to-equilibrium proposition (SV-2.6), and
   the bridge `lim_T punishmentLevel = quittingPunishmentValue` (inf/sup
   vs limit uniformity — noted, unclaimed). **The clause (P) attack:
   design complete, formalization NOT started** (the dispatched agent
   stopped at the design phase; full hand-verified design recorded at
   `ephemeral/ClausePAttackDesign.md`). Established there: per-player
   attainment at `χ + η` is a 4-line route; the opponents-congruence
   lemma is ≈ rfl and glues a TWO-PLAYER simultaneous clause-(P)
   discharge at exact χ (under `Fintype.card ι = 2`, replacing the
   solo-ceiling discharge; remaining two-player clauses L/Q/R/A); and a
   hand-verified cyclic `Fin 3` table SEPARATES simultaneous from
   per-player punishment — every shared plan leaves some player at
   `χ + 3/4` (AM–GM at row zero; Lean-cheap). Flagged discovery, not
   proved: on the absorption-branch variant, simultaneous punishment is
   the Steinhaus–Trybuła non-transitive-dice problem and time-varying
   plans plausibly BEAT stationary ones — the stationarity theorem
   plausibly fails for simultaneous punishment; POSED as **Question 168**
   (2026-08-06): the exact 3/4 separation, the dice-table stationarity
   verdict with the full stopping-reply supremum, attainment and bounds,
   and the shared-versus-triggered pricing.
   Next session: dispatch the module from the recorded design. **INTAKE PENDING (2026-08-05,
   answer arrived, snapshot-committed `9baa177`, NOT yet sealed): the
   Q163 answer** — verdict headline: the equivalence's hard direction
   repairs WITHOUT support purification; the weighted correspondence
   yields exactly the WCM inequality the landing consumes (∃ρ > 0:
   ρ-rational + weighted-ρ-near ⟹ c(x) ≥ ρ, by separation from the
   c = 0 face using only absence of instant approximate equilibria) —
   discharging its K4 directly; global support purification is FALSE
   (rowwise thresholding fine, but global ε-equilibria exist whose
   every nearby support-perfect plan has order-one exploitability); the
   published lemma's weighted reading is false, its support-perfect
   reading repaired via the Solan–Vieille perfection-to-equilibrium
   proposition — RAISING SV-2.6's priority (it now gates both an outer
   leg and this repair). Next session: full read of the 819-line
   answer, seal in ideas/, then formalize the WCM inequality.
1a. **The χ-floored certificate re-measurement — DONE, verdict split and
   decisive** (`UniformEquilibrium/Quitting/Circulation/ChiFloorBoundary.lean`). Solo-rate and
   pair-repair **fall** to the χ-floored free-hazard variant (the previous
   boundary's own witnesses are inside it; the sub-solo blind spot was a
   floor artifact — and the premise correction: multi-owner phases supply
   no simultaneous collision mass, the deterrent is the owner's own
   hazard). Zero-solo and joint-exit **survive structurally**: their
   payoffs provably leave the solo-row hull, which every circulation
   target inhabits — no floor can fix a range restriction. **The habitat
   moves**: weights whose equilibria pay outside the solo hull with no
   exact mechanism. **The engine extension is named**: circulations
   through arbitrary coalition faces, per-phase condition = the
   sure-exit-set criterion — which is exactly Q165's Part B object, so
   the `n = 3` test and the engine extension are now one road.
2. **`n = 3` through the architecture — Q165 ANSWERED 2026-08-05, verdict:
   inexpressibility, with the missing producer named** (sealed in
   `ideas/TheBranchGateNeedsTwoBlockersAndSwitchRepair.md`). Single-blocker
   designation is **false** (uniform-obstruction counterexample); the sharp
   gate is two-blocker (universal ∨ switching pair) at every `n`. The
   sure-exit-set theorem holds exactly as posed (= the coalition-face
   per-phase condition from 1a — that road is confirmed). Collision
   compensation survives a third party only under three exact scalar
   conditions (owner indifference at interior rate; punishment-independent
   spectator no-join; blocker-floor balance against the **exact** χ);
   the fixed-gap obstruction kills sub-floor compensation at vanishing
   owner rate — `δ ≥ γ/(γ+p)` is forced. The fixed-blocker branch map is
   **not total**: a rational regression (C.20) escapes every branch; the
   missing constructor is `SwitchRepair : two-blocker rate cover ⟶
   two-scale rational relaxed orbit` (interior collision intensity within
   phases, occupation charge λ↓0 across them) — circulation is its
   compiler, not its producer; graded pinning cannot substitute. Successor
   items: (a) Theorems A/B + the C.20 regression **LANDED 2026-08-05**
   (production `97b77b6`: `QuittingBlockerIntervalCover`,
   `QuittingSureExitSet`, `QuittingSwitchingResidueRegression`; root
   build green, axiom audit clean; bonus: "exactly one" refuted, n = 2
   threshold corollary); (b) Theorem C equivalence **LANDED 2026-08-05**
   (production `34fdc11`, `UniformEquilibrium/Quitting/Boundary/Repair/CollisionRepairCharacterization.lean`:
   full iff against the exact χ, both legs, general `n`, forced-rate and
   sub-floor-failure corollaries, rate-1 collapse to the sure-exit test);
   (c) `SwitchRepair` — **Q166 ANSWERED 2026-08-05, verdict: REFUTED as
   posed** (sealed in
   `ideas/TheMissingOperationIsSupportEnlargementNotASecondScale.md`).
   The no-resurrection theorem: the occupation charge occurs in none of
   the packet's pointwise clauses, so vanishing-error two-scale families
   of sure-blocker packets (rates bounded below) exist iff an exact
   one-stage repair or sure-pair set already does — occupation scaling
   cannot repair a pointwise inequality, and rotating owners does not
   average failure away. The K4 regression was never in the residue: it
   has an exact rational period-one orbit (`x* = (1, 2/7, 1)`,
   `v* = (5/7, 0, 2/7)`, quit mass 1, Bellman trivial) absorbed by the
   existing exact-cycle engine, exact floors `χ = (2/3, 0, 2/7)` with NO
   sub-floor gap anywhere, and uniform packet defect 2/5 — the
   obstruction lives at the branch interface, not in the orbit relation.
   The missing operation is **support enlargement**: Theorem C.1, the
   one-sure-blocker/two-owner root (both non-blockers mix at explicit
   rational indifference rates; blocker quit-now inequality; floors) is
   necessary AND sufficient for an exact stationary terminal equilibrium
   on that cell — on K4 it recovers the second exact root
   `(1/2, 1, 1/3)`. Residues exactly characterized and semialgebraic:
   packet residues (switching/universal) ∩ no-two-owner-root =
   `ℜ₃^local`, which longer cycles/circulation may still absorb but
   blocker-cover data alone cannot decide. Successor items: (c1)
   formalize Theorem C.1 + the no-resurrection corollary layer on the
   landed collision-repair module + the K4 exact checks (χ against
   `quittingPunishmentValue`, the period-one root, the 2/5 defect) —
   unblocked, NOT yet dispatched (session stopping point); (c2) the
   `ℜ₃^local` adjudication is POSED as **Question 167** (2026-08-06):
   emptiness of the locally-blocked class or a member plus engine
   adjudication — either outcome a coverage theorem;
   (d) four-player delta: unchanged and explicitly untouched by Q166
   (the packet theorem has one spectator, the two-owner root none
   inactive; the two-spectator common-punishment obligation stands).
3. **The corrected trap schema — Q164 ANSWERED 2026-08-05, verdict: sound
   and semantically complete, but effectively sufficient-only** (sealed in
   `ideas/BoundedOrbitBudgetsAreExactlyBoundedPotentials.md`). The schema
   is sound by telescoping (consequence via repaired Simon (i)⇒(iii)
   contrapositively only — the ε/5 bookkeeping is irrelevant), and the
   format is **complete**: uniform finite-orbit quit mass bounded ⟺ a
   bounded local potential exists (budget-to-go V; exact strong duality
   B* = min osc Φ, no compactness or attainment). But no decision
   procedure: affine and every fixed semialgebraic template are exactly
   decidable by QE (affine has the convex-separation criterion with a
   finite Carathéodory dual on failure); continuous classes are provably
   incomplete (discontinuities at zero-charge accumulation strata can be
   necessary); the completeness⟹decidability hope is false absent an
   effective regularity theorem. Negative filters before synthesis:
   positive-charge fixed edge/cycle (kills all classes; the quit-bonus
   table's exact q=1/2 self-loop is the mandatory negative control),
   zero-drift-in-hull (affine). Successor items: (a) + (b) **LANDED
   2026-08-05** (production `0829959`: `Math/ChargedPathBudget.lean` +
   `ChargedPathBudgetCounterexamples.lean` — the abstract theorem, exact
   strong duality attained by the budget-to-go, Bellman
   least-supersolution characterization, positive-cycle filter, towers,
   the continuous-incompleteness counterexample FULLY proved, and the
   quit-bonus q = 1/2 self-loop calibration; the wiring to the repo's
   `oneStageNext` operator TAKEN same day, production `34fdc11`,
   `UniformEquilibrium/Quitting/Punishment/QuitBonusSelfLoopBridge.lean` — the canonical operator on the
   repo's own table fixes the calibrating value exactly, no bounded
   potential); (c) the QE/CAD search instrument itself is
   experiments-lane work, gated on nothing.
4. **Directed search in the named habitat** (sub-solo compensation at every
   owner), instrumented per 3, with the perimeter weights as mandatory
   negative controls.
5. **Strata geometry as the long bet — gated**: the route is not
   well-posed until a uniform-across-periods structure exists (the union of
   strata over unbounded periods need not be tame); the three-lens
   identification is demoted to working hypothesis (one leg proved) and is
   this route's first milestone, not its foundation.

**Conditional essential-APS singleton-flow interface — LANDED.** The exact
Flesch successor graph, full-convex-hull algebraic operator, executable segment
subrelation, carrier-restricted greatest fixed family, and zero-mass regression
are formalized. A supplied finite proper cycle embeds in the algebraic family
and compiles to a uniform-equilibrium payoff. More generally, compact
functional unique-live terminal-free fibers with finite-window face avoidance
produce a coherent infinite path, uniform opponent contraction, and a hazard
ceiling below one. Fixed subdivision and the nonperiodic supersolution then
prove that every initial point in that component is a uniform-equilibrium
payoff. The remaining APS obligation is structural coverage: no theorem shows
that every quitting game has such a nonempty component. See
[`EssentialAPS.md`](EssentialAPS.md).

Standing corrections from the same review acceptance: the negative map's
completeness claim is scoped (proofs factoring through our interfaces; the
correlated/de-correlation route and the topological route are unfenced);
"sound end to end" means locally machine-checked joints, not one assembled
theorem, until 1 closes; the public statement of the position lives at
`UniformEquilibrium/UniformEquilibriumProblem.md` and is the
external attack surface.


## Superseded and resolved project-control decisions

### `PC-008` — deprioritize escaping-middle compactification pending the free-terminal test

**Decision.** **Deprioritize escaping-middle compactification pending the
free-terminal test.** `MATH-P0-1` and `LEAN-P1-4` drop to P1 until the optimized
debt over chains with a *free admissible* terminal continuation is decided.

**Rationale.** The entire P0 hinge is downstream of "the exact-D chain grammar
has a positive plateau". That premise looked like it might be about the grammar:
both plateau witnesses are two-player tables with equilibria, and the surgery
witness carries a machine-checked zero-gain array.

**The free-terminal test has now been answered by an unaudited, unformalized
solver's answer, and it splits (`M [reported]`).** Two candidate unpinnings
are rejected; the faithful formulation selects both the prescribed and the
deviating terminal values by zero-seeded repeated-period iteration. Under it
the surgery witness collapses to gap zero, but the weight
`r({1}) = r({2}) = (-1,1)`, `r({1,2}) = (1,-1)` has gap **exactly `1` at every
length** — so a gap can survive faithful unpinning, and compactification is
therefore **not** categorically work on an artifact. See
[`FaithfulUnpinningLeavesASurvivingGap.md`](../../ideas/PositivePlateauBoundaryClosure/FaithfulUnpinningLeavesASurvivingGap.md)
for the exact statement, the per-row seals (the "unpinning kills both known
plateau witnesses" sub-claim has independent machine-checked support; the
faithful-formulation content does not), and what would raise the seal.

**Rejected.** Continue building marked-cylinder semantics at P0 before knowing
whether the plateau survives unpinning.

**Consequence.** Escaping-middle work continues at P1 and is not abandoned; the
freed capacity goes to the free-terminal calibration and the zero-mismatch-cycle
question. If free-terminal debt stays positive on some weight, the compactness
lane returns to P0 with a target that is informative about the game.

**Revisit trigger.** The free-terminal test resolving either way, or a weight
exhibiting a plateau that survives unpinning.

### `PC-010` — PC-009's stated basis is established, at the bounded form (RESOLVED)

- **Status:** RESOLVED (2026-08-04)

**Decision.** **RESOLVED 2026-08-04 — `PC-009`'s stated basis is established, at
the bounded form.**

**Rationale.** The attributed theorem is E. Solan, *The dynamics of the Nash
correspondence and `n`-player stochastic games*, International Game Theory
Review **3**(4), 291–299 (2001), DOI
[`10.1142/S0219198901000488`](https://doi.org/10.1142/S0219198901000488),
**Theorem 2.1**; the game of its Figure 1 is the case-2 weight times `3`. Its
literal statement carries no boundedness hypothesis and is machine-checked
**false**; its proof runs through the convex-hull bound `Σ_i y_i ≤ 4`, which is
where boundedness enters unstated, so the bounded form is mathematically
established (the gap is a missing step in a published proof, not a wrong
result) — and the bounded form is what the finite-cycle deduction needs,
since repeating a cycle lands inside that hull. The case-2 row returns to
`PROVED` **at the math level**: `NoBoundedCompletelyAbsorbingInverseIterate`
itself is not machine-checked and remains an open `Prop` (`LEAN-F0-8`, still
`READY`, owns formalizing it) — this is consistent with, not a reversal of,
the "open" verdict recorded below in the original entry. Full record:
[`PerturbedFTVGameHasNoBoundedCompletelyAbsorbingInverseIterate`](../../ideas/UniformEquilibriumLiterature/PerturbedFTVGameHasNoBoundedCompletelyAbsorbingInverseIterate.md).
The same paper's **Theorem 2.2** independently attests the diverging-period
claim. Original entry follows. The case-2 refutation was deduced from "this
weight admits no completely absorbing inverse iterate". That statement,
**without a boundedness condition on the values**, is false: an explicit iterate
has rows `(p,0,0)` and values `(1/3, 1, K·q^{-t})`, whose third coordinate grows
exactly like the inverse of the survival product, leaving an unconsumed
homogeneous boundary term. **Machine-checked** in
`UniformEquilibrium/Quitting/Boundary/Analytic/UnboundedInverseIterate.lean`
(`not_noCompletelyAbsorbingInverseIterate`, for every `η ≥ 0`), with the
mechanism isolated as `survivalPrefix_mul_value_two`: the survival prefix times
the third value is a positive constant at every stage. Repetition of a finite
cycle does give bounded values, so the deduction to "no finite absorbing cyclic
array" would go through from the **bounded** form — stated separately as
`NoBoundedCompletelyAbsorbingInverseIterate`, recorded as the weaker claim, and
open.

**Rejected.** Treat the case-2 refutation as established, or discard `PC-009`
outright.

**Consequence.** The absorption-path route is **not** re-deprioritised:
`PC-009`'s other leg is independent of this. The conversion is available and the
period-`3m` family has vanishing gains, and that computation uses only the block
structure, survivals and defect asymptotic — not the attribution. So the carrier
being non-finite still has support; what lapses is the claim that a specific
weight admits *no* finite cycle.

**Revisit trigger.** Historical audit trail, preserved for record and
resolved within this same entry — not a live future trigger. **Audit
returned 2026-08-04: `NOT LOCATABLE`.** No such theorem was found under that attribution — every Solan quitting-game paper and
an arXiv author sweep were searched; none contains the cited terminology and
none of the quitting papers has a Theorem 2.1. Worse for the claim: the weight
at `η = 0` is the Flesch–Thuijsman–Vrieze cubic game divided by three on all
seven rows, and that game has an exact bounded absorbing complementary cycle of
length three — so the **bounded** form is false at `η = 0` too, and the entire
statement rests on the perturbation. The perturbation is aimed exactly at that
cycle and kills it on a knife-edge: the idle coordinate's gap is `η/6`, zero at
`η = 0` and positive after — matching the source's own scope, "for every `ε > 0`
sufficiently small", with no `ε_0` supplied. **Both sweeps missed the paper**
because its title names neither quitting games nor absorption and it is not
among the repository's local PDFs; the citation trail found it, as reference
`[16]` of Ashkenazi-Golan–Krasikov–Rainer–Solan. A source audit must chase the
reference lists of papers already on disk before returning `NOT LOCATABLE`, and
must sweep `ephemeral/` — noting that `sources/aps-quitting-2026.pdf` there is a
3 KB HTML bot-block page, not a paper.


### `MATH-P1-6` — characterize instant approximate equilibria (SOLVED)

- **Status:** SOLVED (2026-08-07)
- **Lane:** P1

**Objective.** Decide where the instant equilibrium family lands in the
program's splits and give it a named exact interface.

**Resolution.** `UniformEquilibrium/Quitting/Punishment/InstantPunishment.lean` characterizes the family
exactly.  A sure-solo first-stage exit completed by off-path punishment works
at every positive accuracy iff the owner's singleton payoff dominates its
punishment value and no outsider gains by joining the exit.  The same module
constructs the approximate profiles and promotes the singleton payoff vector
to a uniform-equilibrium payoff.  This is a separate punishment-completed
mechanism, not a stationary or bare period-one cycle.

**Acceptance.** Met by `quittingInstantPunishmentWorks_iff` and
`isUniformEquilibriumPayoff_soloReward_of_instantPunishment`.

## Link references

[anchored-repair]: ../../ideas/PositivePlateauBoundaryClosure/AnchoredRepairOrUniformDebtDescent.md
[exact-vs-relaxed]: ../../ideas/AbsorbingCycleCarrier/ExactCyclesAreNotLimitsOfRelaxedOnes.md
