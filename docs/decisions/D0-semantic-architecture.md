# D0: semantic architecture by level

**Decision:** Provisionally select a stratified hybrid for static outcome-law
semantics and coordinated native branches for protocol/information semantics.
Do not select a generic certificate hierarchy yet.

**Experiment IDs:** EXP-001

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

Phase 0 froze four transfers, T1–T4, as the intended yardstick. Phase 3 measured
the T1 and T3 shapes: strategy extraction over a protocol's own decision sites,
and a diagram compiled to a static outcome law consumed by the static
equilibrium concepts. T2, both directions of Kuhn, and T4, the one-shot
embedding commuting with compilation, were not built, so this decision rests on
the greenfield measurements rather than on reproducing all four.

That gap is not incidental, because T2 is exactly the reopening condition D7
names: a transfer that must preserve something the shared static target
forgets — here, recall. Building it is the experiment that could still overturn
the certificate rejection, and nothing else currently in the repository can.

The protocol-level acceptance also carries a recorded scope limit:
information-local policies are indexed by history while the runner is indexed by
state, so the compilation into the static core covers the perfect-information
case. Lifting it needs a trace-indexed run law.

### Unexpected cost from Phase 0, resolved

The pinned snapshot's Bayesian branch was ex-ante only, which left open whether
the shared local-deviation interface could carry an interim, type-dependent
deviation at all. It can: the interim probe fits the same interface with no new
equilibrium predicate.

### Consequences for public API

`GameTheory.Core` and `GameTheory.Protocol` are both public, and `Protocol`
compiles into `Core` by an ordinary function with a named evaluation theorem.
There is no `Adequacy` record at any level, no user-visible transport, and no
theorem stored as a certificate field. Language encodings stay outside the
public umbrella until one of them covers its source formalism.
