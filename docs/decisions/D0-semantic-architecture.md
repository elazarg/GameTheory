# D0: semantic architecture by level

**Status:** final at every semantic level; the Phase 3 finalization below
supersedes the provisional Phase 0 choice.

**Phase 0 provisional decision:** Select a stratified hybrid for static
outcome-law semantics and coordinated native branches for protocol/information
semantics. Do not select a generic certificate hierarchy yet. The final
decision, after Phase 3, is recorded below.

**Experiment IDs:** EXP-001; post-decision stress evidence EXP-028, EXP-029,
EXP-030

**Hypothesis:** A utility-free shared static form and common deviation logic can
remove duplicated strategic concepts without forcing sequential languages to
erase histories, recall, or information. Named certificates are useful only
where real transfers reuse or compose them.

**Competing designs:** A utility-bearing universal hub; coordinated native
branches with theorem-specific bridges; a stratified hybrid with shared static
forms, native protocols, and measured named adequacy certificates.

**Representative examples:** T1 finite EFG strategic extraction and pure/mixed
Nash; T2 both directions of Kuhn; T3 MAID/EFG outcome-law and equilibrium
transfer; T4 the one-shot NFG-to-FOSG embedding commuting with compilation. The
exact declarations and baselines are frozen in
[`../Phase0ArchitectureEvidence.md`](../Phase0ArchitectureEvidence.md).

**Measurements:** The complete pinned v1 snapshot has 436 Lean files and
117,094 nonblank lines: 380/99,301 in `GameTheory/` and 56/17,793 in `Math/`.
Within authored `GameTheory/` file text, `KernelGame` occurs in 187 files and 47
language files. The 14 language bridge files contain 6,243 nonblank lines. Language code contains 84
`cast`/`Eq.ndrec` tokens in 12 files after comments and strings are stripped,
83.3% concentrated in four compiler or bridge files. Generic transport plus the five game-morphism files total 4,225
nonblank lines, while no language file composes `GameForm.Transport` and only
three expressiveness declarations compose kernel morphisms/simulations. Direct
T3 laws are 8/12 nonblank lines versus 20/25-line certificate wrappers; T4 is
21 direct lines plus a 9-line wrapper.

**Evidence from existing libraries:** v1 proves that a static outcome-law target
supports mixed lifting, Nash existence, CE/CCE, learning, potential games, and
several language bridges. It also proves that Kuhn mixed-to-behavioral needs
reach mass/support factorization and player-local action posteriors, not merely
a field named perfect recall. Native EFG, MAID, FOSG, and open-game structures
retain materially different protocol data. The snapshot contains duplicate
static equilibrium surfaces despite the hub.

**Unexpected costs:** The most general v1 transport surface is much larger than
the direct T1/T3/T4 preservation lemmas and has no same-level composition in
language consumers. The snapshot has no git history, so historical change
concentration cannot be measured. The Bayesian branch contains no declaration
or prose occurrence of “interim,” so its apparent Bayes-Nash coverage is only
ex-ante and cannot validate the planned scope by itself.

**Kill condition:** Reject a shared static form if the Phase 2 concepts require
language-specific fields or three consumers still duplicate equilibrium logic.
Reject a protocol hub if two languages require dummy/escape data or the hub
approaches native-semantics size. Reject a certificate level if its payload
mirrors native semantics, exceeds twice its direct baseline or 25% of native
semantics without greater measured reuse, lacks two consumers or a real
composition, exposes user transports, or is over 25% slower.

**Result:** Narrow. Provisionally accept the hybrid at static outcome-law and
incentive levels; accept coordinated branches at protocol/information level;
defer certificate stratification and D7 until Phase 3 measures the greenfield
prototype against T1–T4 direct bridges.

**Consequences for public API:** Phase 1 may compete signature-bound, utility-free
`GameForm` designs. Utility and preference stay separate. Protocol languages do
not inherit from a universal semantic object. No generic adequacy hierarchy is
public before Phase 3. Each compiler exposes only named evaluation/law facts for
the frozen transfers, with no user-visible transports and no theorem stored as
a certificate field.

---

## Finalization (2026-07-28)

**Status:** final at every level. Accept the shared static form and shared
incentive logic; accept *one* shared execution base rather than coordinated
native branches; reject certificate stratification.

**Experiment IDs:** EXP-005 through EXP-015.

### Kill conditions, checked

*Shared static form — did not fire.* One `IsEquilibrium` predicate over one
`DeviationScheme` expresses pure and mixed Nash, coarse correlated and
correlated equilibrium, and strong Nash. No consumer defines an equilibrium
notion of its own: not the executable rational frontend, not the worked
classical examples, and not either compiled language. No concept needed a
language-specific field.

*Protocol hub — did not fire, and the provisional call was too weak.* Two
languages, an influence diagram and a two-round simultaneous game, compile onto
one execution base with no fake players, no fake actions beyond the canonical
no-op, which the second language never uses at all, and no escape fields; each
absence is recorded as a theorem in that module's workaround list. On size, the
execution interface is 214 nonblank lines and the whole sequential layer,
including backward induction, extraction, information, assessment, and static
compilation, is 1393. That is larger than the two front-ends put together, so
the amortization argument has to be marginal rather than total, and it is: the
first front-end is 669 lines of compiler and named facts plus 46 of probes, and
the **second is 158 lines in total** — for which it receives the run law,
histories, reachability, backward induction, information locality, assessment,
and compilation into the static core, adding none of them.

This is why the provisional wording changes. Phase 0 predicted coordinated
native protocol branches. The measurement is stronger: the branches were not
needed, because both native shapes fit one base.

*Certificate level — fired, and the level is rejected.* See
[`D7-certificate-stratification.md`](D7-certificate-stratification.md). The
direct baseline turned out to be zero declarations per language, which no
certificate level can beat.

### What the finalization does not rest on

Phase 0 froze four transfers, T1–T4, as the intended yardstick. At finalization,
Phase 3 had measured the T1 and T3 shapes: strategy extraction over a protocol's
own decision sites, and a diagram compiled to a static outcome law consumed by
the static equilibrium concepts. T2, both directions of Kuhn, and T4, the
one-shot embedding commuting with compilation, had not been built, so this
decision did not rest on reproducing all four.

That gap is not incidental: T2 is the one frozen transfer whose real
obligations the snapshot shows to be much larger than its name.

**Correction (2026-07-29).** This paragraph originally also claimed T2 was the
reopening condition for the certificate decision. Once its first direction was
built, that claim was visibly wrong. The behavioral/mixed equivalence is a
theorem about two strategy *representations* within one information model, not
a transfer between two languages, so both sides live in the same layer and
neither needs a witness — the same reason the compiled languages needed none.

**Close-out (2026-07-30).** T2 is now built in both directions at the stronger
history-law level. Local randomization is representable by one policy draw
under `ActsOnceWhereItMatters`; one policy draw is representable by local
randomization under `ConstrainsAlike`, which perfect recall implies; and the
sets of realizable laws are equal when both conditions hold. D7's reopening
condition remains unmet, because this is still a same-layer representation
theorem. T4 remains outside the evidence on which D0 was finalized.

The execution-side scope limit recorded at finalization is now closed.
`History.lean` and `Randomized.lean` run information-local deterministic,
behavioral, and mixed policies over histories, with pushforward and point-mass
compatibility theorems. `InformationModel.toGameForm` compiles pure policies
with histories as outcomes, its ordinary mixed extension is the existing
mixed-policy runner, and a separate behavioral form is connected by the two
sharp correspondence theorems.

The finite-horizon information-local one-shot theorem also reaches the
compiler: one-shot optimality at every history defeats every whole replacement
policy and implies ordinary static Nash. Its `historyContext` packages the
actual continuation at a history, and the one-shot premise is equivalent to
`IsSequentiallyRationalAt` in those contexts. This is not yet a full
well-founded `oneShotDeviation_iff_spe`: there is no SPE predicate, and no
converse from initial static Nash is claimed because it does not quantify over
off-path histories.

### Unexpected cost from Phase 0, resolved

The pinned snapshot's Bayesian branch was ex-ante only, which left open whether
the shared local-deviation interface could carry an interim, type-dependent
deviation at all. It can: the interim probe fits the same interface with no new
equilibrium predicate.

### Phase 5 cooperative stress

[EXP-028](../ExperimentLog.md) confirms the decision to keep coalitional games
as a parallel stable primitive. The existing `CoalitionalGame` supports the
direct marginal-contribution formula for the Shapley value, its efficiency,
symmetry, null-player, and additivity laws, and the unanimity-basis proof that
those four axioms characterize it uniquely. `Fintype` is required by the value
and theorems that enumerate coalitions; it is not stored in the game.

The three-agent majority game separates the two cooperative solution concepts
without changing representation: its core is empty, while its Shapley
allocation exists and pays every agent `1/3`. No `GameForm`, strategy, outcome,
probability, or certificate layer appears. The Phase 0 judgment that
`GameForm` is not the universal semantic hub therefore survives a theorem that
uses substantially more of cooperative-game structure than the original core
example.

### Phase 5 Bayesian stress

[EXP-029](../ExperimentLog.md) closes the unfinished Bayesian edge between the
shared static form and the accepted information layer. Stable
`BayesianGame` data compiles directly to a type-contingent `GameForm`; a
separate core module proves its ordinary Nash predicate equivalent to
prior-weighted interim optimality. The solution-concept-free language compiler
turns the same data into a two-step chance/simultaneous `ExecutionProtocol` and
an `InformationModel` whose acting view contains only the observing player's
own type.

Policies and contingent plans are exactly equivalent, and the compiled
two-step outcome law equals the direct law mapped to completed outcomes. The
typed fair-bit endpoint transfers truthful Nash through that equality without
a Bayesian equilibrium wrapper. Bayesian games therefore form a coordinated
native presentation only where execution and information require it; their
static incentive theory continues to use the shared form and predicate.
Finiteness remains attached to the interim decomposition theorem rather than
stored in the game.

### Phase 5 repeated-play stress

[EXP-030](../ExperimentLog.md) confirms the level split at an infinite-horizon
consumer. A repeated profile is native deterministic recursion over one public
list history; normalized discounted payoff evaluates that path and ordinary
`IsNash` states equilibrium. Finite execution is not reimplemented: a
`GameTheory.Repeated.Protocol` bridge uses the accepted `ExecutionProtocol` and
`InformationModel`, with the accumulated public list as its state, and proves
that every finite run is exactly the corresponding native prefix.

The split is discriminating rather than cosmetic. Making Protocol the sole
infinite-horizon representation would add no value to the deterministic
discounted theorem, while a second repeated transition would duplicate D6.
Basic and Discounted cannot reach Protocol; the Protocol bridge cannot reach
discounting; positive probes show the bridge still consumes both the native
path and the information model. No new equilibrium definition, generic
certificate, or infinite-path law appears.

### Consequences for public API

`GameTheory.Core` and `GameTheory.Protocol` are both public. Both a bare
`ExecutionProtocol` and a composed `InformationModel` compile into `Core` by
ordinary functions with named evaluation theorems. There is no `Adequacy`
record at any level, no user-visible transport, and no theorem stored as a
certificate field. Language encodings stay outside the public umbrella until
one of them covers its source formalism.
