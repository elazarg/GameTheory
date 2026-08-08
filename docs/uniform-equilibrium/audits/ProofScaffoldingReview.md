# Critical Review: Mathematical Progress versus Proof Scaffolding

## Addendum: Question 84 certificate boundary (2026-08-01)

Question 84 is false as stated. Its action-independent three-state
counterexample has a trivial uniform equilibrium at the ex-ante target (0),
but positive and negative absorbing branches make the proposed absolute
remainder

\[
\mathbb E[C_N+|\Phi_N-\Phi_0|]=o(N)
\]

impossible. The local inequality forces linear potential/account growth on
the positive branch even though the branches cancel ex ante.

This narrows the critical review: the existing expectation-level adaptive
potential verifier remains sound and is not refuted by this example, but the
proof program may not assume that every uniform equilibrium admits the
stronger Question 84 certificate. Direct deviation caps and other sound
certificate languages must remain available. Question 84 is now a permanent
falsifier for interfaces which move an absolute value inside an expectation
or silently replace ex-ante control by branchwise control.

## Addendum: Question 85 multiscale reduction (2026-08-02)

Question 85 supplies the previously missing player-free coupled-scale Abel
reduction. Successive faster-than-killing recurrent quotients terminate after
at most \(|S|-1\) nontrivial dimension drops, followed by one critical
resolvent. The construction is invariant under analytic reparameterization.

Its feedback half is deliberately not a universal finite decision theorem.
Fresh-public-randomized finite-mode realization has an exact
occupation--flux criterion, and a specified finite-mode architecture has an
exact augmented-chain test. Unrestricted deterministic exact realization has
a nonclosed entrance obstruction; the answer gives an inverse-limit viability
description and sufficient Poisson/summability controls.

For the conjecture, the crucial correction is that exact one-policy
realization is stronger than necessary. Uniform equilibrium permits an
accuracy-indexed family of profiles. The Q85 leakage target is not exactly
realizable but is arbitrarily approximable, so the remaining strategic bridge
must concern proof-carrying all-accuracy delivery and deviation safety, not
membership in a closed exact-realization polytope.

## Addendum: consumer wiring and untracked modules (2026-08-02)

Two repository-state statements below are outdated at the current committed
tip and are corrected here rather than rewritten in place:

- The claim that no declaration outside `AnalyticBellmanExistence.lean`
  consumes `analyticBellmanGermExistence`, and none outside
  `UniformEquilibrium/VanishingDiscount/Analytic/Endpoint/Atlas.lean` consumes `AnalyticEndpointAtlasLeaf`, was
  true at `98cc266` and was closed by the very next commit (`6763c94`):
  `UniformEquilibrium/VanishingDiscount/Analytic/Endpoint/Existence.lean` derives a typed endpoint leaf for every
  finite game from germ existence, and
  `AttainableEndpointCorrespondence.lean` (`d5434c7`) consumes the germ as
  well. The "easy missing wiring" is done. The leaf-resolution difficulty
  is unchanged and the 0/13 generic closure score stands.
- The five untracked WIP modules excluded from the stable score were
  repaired, build-verified, imported by the umbrella, and committed
  (`d64563d`, `c879fdc`). Three of the five did not compile despite
  containing zero `sorry` — reaffirming the build-before-status rule.

## Scope and snapshot

This review records the state of the `uniform-existence` branch at the
stable committed tip

```text
98cc266  Construct finite public terminal Nash systems
```

on 2026-07-31. The worktree was active during the review. Five untracked
stochastic-game modules were excluded from the stable score:

```text
UniformEquilibrium/Certificates/Adaptive/PotentialFiniteTimeTargetBounds.lean
FiniteHorizonProfileLawTransfer.lean
FiniteRankedTerminalChildNashClosure.lean
UniformEquilibrium/Certificates/Public/FirstHitStoppingRule.lean
UniformEquilibrium/Certificates/Public/HistoryFirstHitStoppingAcceptance.lean
```

The purpose of this review is not to discount the large body of checked
mathematics. It is to distinguish:

1. unconditional progress from an arbitrary finite stochastic game;
2. conditional verification and composition theorems;
3. interfaces that merely name the missing strategic construction;
4. counterexamples and boundary results that rule out false shortcuts.

## Critical target correction (2026-08-01)

Sorin's two-player absorbing game supplies a decisive correction to the
architecture assumed in the original snapshot. Its rational analytic family
of stationary discounted Nash equilibria has the constant payoff endpoint

\[
v=\left(\frac12,\frac23\right),
\]

while its uniform-equilibrium payoff set is

\[
\left\{\bigl(\alpha,2(1-\alpha)\bigr):
\frac12\le\alpha\le\frac23\right\}.
\]

The endpoint is outside this set: every uniform payoff obeys
\(2w_1+w_2=2\), whereas \(2v_1+v_2=5/3\). The example and calculation are
recorded in `UniformEquilibriumFrontierManuscript.tex`, with the primary
reference S. Sorin, *International Journal of Game Theory* 15 (1986),
101--107, DOI `10.1007/BF01770978`.

Therefore the previously stated universal bridge

```text
analytic endpoint leaf
  -> preserve that endpoint target
  -> adaptive certificate
```

is false. The corrected bridge is

```text
finite stochastic game
  -> select an analytic germ/endpoint leaf as source data
  -> endogenous selection of an implementable target w
  -> legal, credible preservation of w through recursive continuations
  -> adaptive certificate at w
```

This does **not** make whole-target transport optional. It separates two
stages: the root may have to retarget away from the discounted endpoint; once
a node declares a target, every child edge and splice must preserve or
explicitly bridge the whole vector. Any reconstruction interface whose output
is forced to be a certificate at `germ.endpointValue` is universally
overstrong and fails on Sorin's example.

The analytic arc is also existential. Closing all thirteen nonsemantic leaf
types is sufficient but not logically necessary: a proof may select a germ
which lands in a closable leaf. This arc-improvement route cannot replace
target selection, because Sorin's game has no discounted endpoint in the
uniform-payoff set, but it may substantially shrink the leaf space that must
be closed.

## Bottom line

This is a substantial body of real formal mathematics, but it is not a
nearly completed proof of the general uniform-equilibrium conjecture.

The project has completed:

- the semantic verification layer from adaptive certificates to uniform
  equilibrium;
- analytic Bellman-germ existence for every finite stochastic game,
  including the curve-selection input;
- a finite and honest analytic endpoint classification;
- much of the probability, monitoring, deflation, accounting, stopping,
  and child-composition machinery;
- several genuine special cases.

It has not completed the corrected central strategic bridge:

> Use the analytic leaf to select an implementable root target, then construct
> a legal, credible, whole-target-preserving, rank-decreasing—or completely
> account-discharged—public response at that selected target.

That bridge still contains essentially the conjecture-level difficulty.

## Honest progress dashboard

| Gate | Status | Meaning |
|---|---:|---|
| Adaptive certificate implies uniform equilibrium | Complete | Genuine checked verifier |
| Analytic Bellman germ exists for every finite game | Complete | germ existence is substantive mathematics |
| Every germ has a finite endpoint classification | Complete | Honest obstruction atlas |
| Discounted endpoint is always a uniform target | **False** | Sorin's rational analytic example forces root retargeting |
| Generic closure of nonsemantic atlas leaves | **0 / 13** | Conservative sufficient route; a germ-selection theorem could avoid some leaves instead |
| Conditional finite-child composition | Complete in important fixed-depth and stopping variants | Works once legal children, targets, safety, and rank data are supplied |
| Arbitrary-game global recursion constructor | Missing | No theorem constructs it |
| Executable placeholders | **1** | The central conjecture-level constructor |

The strongest unconditional arbitrary-game path is presently:

```text
finite stochastic game
  → selectable analytic Bellman germ
  → first analytic hierarchy response
  → honest endpoint leaf
  ↛ endogenous implementable target
  ↛ adaptive certificate
```

The relevant declarations are:

- `AnalyticBellmanExistence.lean:65` — `analyticBellmanGermExistence`;
- `AnalyticBellmanHierarchy.lean:1615` —
  `exists_firstHierarchyResponse`;
- `UniformEquilibrium/VanishingDiscount/Analytic/Endpoint/Atlas.lean:606` — classification of a first hierarchy
  response into an honest endpoint leaf;
- `Uniform.lean:207` — the unproved global constructor, with the `sorry` at
  line 211.

At this snapshot:

- no declaration outside `AnalyticBellmanExistence.lean` consumes `analyticBellmanGermExistence`;
- no declaration outside `UniformEquilibrium/VanishingDiscount/Analytic/Endpoint/Atlas.lean` consumes
  `AnalyticEndpointAtlasLeaf`.

The missing wiring from germ existence to the classifier is easy. Resolving the
resulting leaf is not.

## Tangible mathematics

The following are genuine advances rather than mere API packaging.

### Analytic and finite-dimensional structure

- The semialgebraic analytic curve-selection construction behind germ existence.
- Coupled analytic Bellman germs, endpoint values, finite-bias data, lower
  jets, and stabilized sign/support cells.
- Exact Farkas, flow, stationary-class, charged-circulation, and analytic
  endpoint alternatives.
- Finite operational deflation with strict active-set rank loss and
  sublinear accounts for deleted use.
- A common lexicographic rank combining harmonic dimension and proper
  support loss, together with an explicit proof that full support is
  stagnant in both coordinates.

### Probability and accounting

- Processed-harmonic continuation telescopes and realized state accounts.
- Predictable shadow couplings and exact causal stopping-law factorization.
- Contextual monitors, stitched martingale estimates, regeneration
  calendars, and finite reset accounting.
- Realization of analytic occupation and response schedules on actual
  public histories.
- Finite-prefix and stopped-child charge estimates under arbitrary
  unilateral behavior deviations.

### Strategic and compositional results

- Finite public-tree backward Nash for arbitrary terminal continuation
  payoffs.
- Exact equality of prescribed and worst-unilateral terminal potentials in
  the backward-Nash system.
- Conditional fixed-depth and variable-stopping child composition.
- Direct uniform closure of the finite-bias/common-potential branch when
  prescribed target transport is additionally available.
- Conversion of failure of that prescribed transport into concrete
  tail-reachable charged-circulation evidence.

### Negative results

The counterexamples are also substantive. They prove that:

- separate player feasibility need not give mixed-player compatibility;
- positive circulation need not preserve the complete payoff target;
- a positive recurrent class need not decrease support rank;
- full support and regeneration need not yield a bounded realized account;
- detector drift does not create strategic credibility;
- endpoint harmonicity and a Poisson correction do not automatically make
  moving-calendar target transport sublinear;
- expectation-preserving randomized child selection need not be safe under
  unilateral deviation.

These results remain valuable even if the general conjecture is not
settled.

## What is scaffolding

Scaffolding is useful when it exposes a precise quantifier or interface
error. It is not itself progress on the conjecture when its premise already
contains the desired strategic output.

The clearest example is `UniformEquilibrium/VanishingDiscount/Analytic/Endpoint/Atlas.lean`. It has one semantic
leaf and thirteen nonsemantic leaves. Its reconstruction structures
ultimately contain fields returning an
`IsAdaptivePotentialCertificateAt`. The eliminator
`semanticClose_or_certificate_of_resolution` is correct bookkeeping:
once a certificate-producing reconstruction is supplied, the leaf closes.
It does not construct that reconstruction.

Likewise, `UniformEquilibrium/Certificates/Public/LocalResponseRecursion.lean` assumes:

- mixed-player continuation compatibility;
- a legal core-history entry interface;
- a local closer returning the desired public punishment system.

Its well-founded compiler is correct, but it does not manufacture those
strategic witnesses.

Other scaffold patterns include:

- completed adaptive recursions proved equivalent to the semantic goal;
- one-node embeddings among recursive APIs;
- response closers whose decisive field returns the target certificate;
- rank or region fields not used to derive a strict recursive call;
- top-level atlas and boundary modules with no consumer except the umbrella
  import.

This architecture has prevented unsound promotions of a circulation,
detector, span membership, or harmonic vector into a punishment. Further
interfaces of the form “supply the missing certificate here” should not be
counted as critical-path progress.

## The seven-seam acceptance matrix

The global construction must discharge all seven items. The first is a root
obligation; the remaining six apply after a target has been declared:

1. **Germ and target selection:** a justified analytic branch and an
   endogenous implementable root payoff, not an arbitrary germ with its
   assumed discounted endpoint.
2. **Profile:** an actual public behavior profile or legal child strategy.
3. **Incentives:** deviation-safe selection or a credible punishment.
4. **Target transport:** anchoring and transport of the complete
   player-indexed payoff vector after selection.
5. **Entry:** legal public-history entry, suffix rebasing, and continuation
   gluing.
6. **Progress:** strict well-founded descent or a fully discharged realized
   account.
7. **Certificate:** a direct theorem producing
   `IsAdaptivePotentialCertificateAt`, without a reconstruction or closer
   argument.

At the stable snapshot, the project had no generic root target-selection
theorem, and no generic nonsemantic analytic leaf satisfied all of the six
post-selection seams. Several leaves have strong partial entries, especially
processed-harmonic accounting and operational deflation, but the generic
leaf-closure score remains 0 of 13.

Future work should be counted as critical-path progress only when it removes
at least one genuinely assumed cell from this matrix.

## Assessment of the answer to Question45

[Question45-RandomizedRecurrentChildComposition.md](../../../questions/old/Question45-RandomizedRecurrentChildComposition.md)
now contains a detailed
answer. Its main semantic theorem is useful and, under the clarified
hypotheses, essentially correct.

### What the answer establishes

Let a public selector stop within \(L\) stages and choose child \(J\). Assume
that:

\[
\mathbb E_\sigma[v^J]=v,
\tag{Q45.1}
\]

and, for every unilateral deviation during selection,

\[
\mathbb E_{\mathrm{dev}_i,\sigma_{-i}}[v_i^J]
\le v_i+\eta.
\tag{Q45.2}
\]

If the selected children have uniform continuation moduli, the composite
profile satisfies explicit bounds of the form

\[
\left|
\frac1N\mathbb E_\sigma G_{i,N}-v_i
\right|
\le
\frac{(1+V_i)L}{N}
+\frac{A_i^{N,L}}N,
\tag{Q45.3}
\]

and

\[
\sup_{\beta_i}
\frac1N\mathbb E_{\beta_i,\sigma_{-i}}G_{i,N}
\le
v_i+\eta+\varepsilon
+\frac{(1+V_i)L+B_i^{N,L}}N.
\tag{Q45.4}
\]

The answer correctly handles one global deviation used both before and
after stopping. Conditional on a stopped history, its post-stop restriction
is a legal child deviation. Correlation between the pre-stop and post-stop
parts causes no additional loss.

It also correctly separates three levels of selector safety:

1. invariance of the complete terminal-child law from every public prefix;
2. payoff-coordinate supermartingale safety \(D_i(h)=M_i(h)\);
3. the root-only terminal payoff ceiling
   \(D_i(h_0)\le M_i(h_0)+\eta\).

Only the third is needed for semantic composition from the fixed root.
Historywise or full-law invariance is stronger.

The answer also identifies two necessary qualifications:

- the stopping bound must survive every unilateral deviation;
- action-independence must govern all public information used by the
  stopping rule and child map, not merely the physical next state.

### Qualifications and corrections

The answer should not be translated verbatim without addressing the
following points.

#### 1. Uniform child moduli

The assertion

\[
A_i(n)=o(n)
\]

requires exact uniform convergence of each selected child profile to its
target, uniformly over the finite family of admissible rebased entries.
If “uniform \(\varepsilon\)-equilibrium with payoff \(v^c\)” means only
eventual \(\varepsilon\)-closeness, the proof must retain that
\(\varepsilon\) in the on-path bound instead of declaring \(A_i(n)=o(n)\).

This is a quantifier clarification, not a failure of the composition idea.

#### 2. Certificate boundary matching

The semantic proof uses only child payoff and deviation moduli and is solid.
The public-phase certificate paragraph is less complete.

It asserts exact boundary matching

\[
M_i(H_\tau)=D_i(H_\tau)=v_i^J.
\]

However, an arbitrary child adaptive or public-phase certificate generally
anchors its initial potentials only within the requested child error of
\(v_i^J\); the potentials need not equal the target exactly.

A complete certificate splice must therefore do one of:

- add the initial child-potential mismatch as a one-time bounded charge;
- use a target-perturbation lemma;
- instantiate a child system with exact terminal potentials;
- use the existing fixed-depth adaptive splice, which explicitly tracks
  the three child obstacles and their root errors.

This is a repairable boundary issue, but it prevents the certificate section
from being considered a complete proof as written.

#### 3. The selector ceiling remains assumed

Question45 assumes the crucial terminal deviation ceiling (Q45.2). It does
not derive the selector, its endogenous target, or deviation safety.
Consequently it closes the **conditional composition** seam but does not
close any analytic endpoint leaf.

Finite public-tree backward Nash is the natural way to derive (Q45.2) with
\(\eta=0\) for an endogenous parent target. The untracked
`FiniteRankedTerminalChildNashClosure.lean` is pursuing exactly this route.
At the reviewed state it constructs the finite child coverage, endogenous
parent target, profile-law transfer, and root-anchor estimates, but it does
not yet contain the final all-accuracy parent certificate theorem.

### Verdict on Question45

The answer is:

- **correct and useful** as a semantic bounded-selector composition theorem,
  after making the uniform-modulus hypothesis explicit;
- **interesting** in its exact hierarchy of terminal-law, payoff-level, and
  root-only safety conditions;
- **not yet a generic gap closure**, because terminal deviation safety is an
  input;
- **not yet a complete public-phase certificate proof**, because the child
  boundary-potential mismatch is omitted.

Its most important consequence is to focus the next theorem:

> Derive the Question45 terminal payoff ceiling and all three parent target
> anchors from finite-tree backward Nash, then compile the result directly
> to an all-accuracy adaptive certificate.

## Best road forward

The most promising tractable integration theorem is:

> A finite legal family of strictly lower-ranked terminal children,
> equipped with all-accuracy child certificates, constructs an endogenous
> parent target and all-accuracy parent adaptive certificates.

The theorem must derive rather than assume:

- the parent public strategy;
- parent target anchors;
- deviation-envelope safety;
- the finite-prefix accounting budget.

The clean first case is fixed terminal depth. Finite-tree backward Nash
supplies the selection profile and endogenous target. Question45 supplies
the semantic splice, while the existing finite-horizon envelope and
adaptive-potential machinery should supply the local certificate.

The next case is genuine early stopping. It additionally requires a
stopped-tree Nash transfer theorem and exact suffix factorization.

After those integration results, the conjecture-level task remains:

> Select a useful analytic endpoint leaf and use it as source data to select
> an implementable root target, then map it into certified child coverage or a
> complete account/credibility closure at that selected target.

Failure at a leaf should produce an explicit obstruction or finite
counterexample, not another reconstruction field.

## Repository health at the reviewed snapshot

- Stable committed tip: `98cc266`.
- The committed umbrella had a recent successful build before the active
  WIP layer; the finite terminal Nash module also had a fresh `.olean`.
- The only executable placeholder in tracked Lean source is the deliberate
  central `sorry` in `Uniform.lean`.
- Five untracked WIP modules were excluded from the stable score.
- CI remains stored at `.github/ci.yml`, not under `.github/workflows`, so
  ordinary GitHub Actions will not discover it automatically.

## Final assessment

The project has built a serious formal theory around the conjecture and has
materially narrowed the frontier. It has also become much better at
distinguishing evidence from strategy and conditional verification from
construction.

The conjecture itself is still standing at endogenous target selection and the
first general strategic reconstruction step. The next phase should prioritize
integration and unconditional closure relative to a selected target. New atlas
or recursion wrappers should be
paused unless they immediately acquire a consumer that removes a genuine
cell from the seven-seam matrix.
