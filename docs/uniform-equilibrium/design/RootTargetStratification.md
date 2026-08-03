# Root Target Stratification

Dated design note, 2026-08-02. This documents the phase-lifted root-target
proposal, the external critique that refined it, the adopted design, and
the controller questions it isolates (Q93, Q94), the credibility theorem
that sharpens it (Q95--Q99), the correlation-implementation axis isolated
by Q100, the target-free falsification test posed in Q101, and the finite
occupation/product/realization and multiscale calibration in Q102--Q106.
Q107--Q112 isolate the resulting bridge, selector, confluence, punisher-side,
causal-realization, and bounded predictive-compression questions. Q108 now
settles the abstract joint-packet obstruction and Q109 the supplied full-germ
algebra; their game-shaped selector and controlled-policy compiler residuals
remain. Q107 now states and adversarially verifies, modulo explicit imported
compactness/refinement/block lemmas, the corrected terminal quitting-game
Never/credible-First/standard-proper-path bridge at the mathematical level,
while Solan--Vieille Proposition 2.13 separately identifies terminal
approximate existence with common-horizon uniform existence and compact target
selection. The quitting-specific terminal-to-uniform bridge and fixed-payoff
selection are now formalized in `QuittingTerminalUniformization.lean` and
`QuittingTerminalUniformPayoffSelection.lean`. The remaining gap is terminal
approximate-equilibrium production, not uniformization. The current
cross-layer interpretation and theorem status live in
[`FRONTIER.md`](../FRONTIER.md); project decisions and priorities live in
[`PIPELINE.md`](../PIPELINE.md).
This note records the idea and its rationale so neither depends on which
design branch is eventually taken.

## The proposal (original form)

The root target correspondence of a finite stochastic game — the set of
payoff vectors selectable as uniform targets — should be built over
**phase-lifted occupation structures**, not stationary ones, with the
automaton-resistant class handled by a separate adaptive branch.

Three independent evidence lines motivated the phase lift:

1. Question 89 (answered, verified): for switched harmless environments,
   delivery-plus-caps holds over periodic mode words, and the exact
   invariant for a fixed periodic schedule is a phase-indexed bias system
   on \(S\times\mathbb Z/P\mathbb Z\) (equivalently an occupation LP on
   the phase-lifted chain).
2. Experiment E03 (independent): path-complete accounts are coboundaries
   on lifted (mode, state) graphs — state-only potentials provably do not
   suffice.
3. The Flesch–Thuijsman–Vrieze game: no stationary
   \(\varepsilon\)-equilibrium exists, while cyclic Markov equilibria do —
   so some games *force* nontrivial phases. The verified Q87 answer gives its
   uniform payoff set as
   \(\{u\ge1,\ u_1+u_2+u_3=4,\ \prod_i(u_i-1)=0\}\): what the original
   proposal called an individually-rational truncation of an occupation face.
   The cap correction below supersedes that terminology.

Sorin's example calibrates the target side: the uniform set
\(\{(\alpha,2(1-\alpha)):1/2\le\alpha\le2/3\}\) is a truncation of
the exposed edge \(2w_1+w_2=2\) of the feasible set, and the analytic
discounted endpoint lies off it — target selection is forced.

**Cap correction (2026-08-02, after Q87 and Q95).** The truncation values are
not generally individual-rationality or minmax floors. For a proposed
architecture (\mathcal A), player (i), and reachable configuration (x), the
operational binding coordinate is the uniform-horizon complete unilateral
best-response value

\[
\beta_{i,\mathrm{unif}}^{\mathcal A}(x)
:=
\limsup_N\sup_{\tau_i}
\mathbb E_x^{\tau_i,\mathcal A_{-i}}
\frac1N\sum_{t<N}g_i(t).
\]

Historywise delivery and credibility directly compare the local target
coordinate with this value. Q96 now proves, on the finite owner-specific
reachable multichain arena, that this uniform-horizon value and the standard
average-reward MDP gain both equal the local target and admit the claimed
gain--bias representation. It also shows that the corresponding
(T0)/(Ti)/(N)/(P) occupation language needs recurrent coverage (RC) or a fifth
cross-owner recurrent-class obstruction. In FTV the checked local value equals
the quitting/indifference value (1), while
the minmax is (1/2); this is an instance, not a universal one-stage-floor
formula. Uniform sets may therefore be architecture-specific unilateral-value
truncations of exposed occupation sets and may be lower-dimensional stratified
boundaries. The FTV interior requires correlation of phase-shifted cycles and
is not supplied by the uncorrelated cyclic architecture.

Q110 adds a restricted but useful floor correction. If \(J_{j,F}\) is the
punisher's floor game and the response is credible against every unilateral
punisher deviation, then

\[
\underline v_j
\le \sup_{\tau_j}J_{j,F}(\tau_j,\pi_{-j})
\le \sup_{\tau_j}J_j(\tau_j,\pi_{-j})
\le J_j^\pi+\eta.
\]

Thus responder floor preservation is automatic from credibility in that
fixed-arena formulation. It is not a separate boundary inequality to add to
the root correspondence. Cap, credibility, re-entry, and the owner-cycle
alternative remain open. The abstract comparison theorem is Lean-formalized
in `ResponderFloorCredibilityComparison.lean` at `c485210`.

**Correlation-implementation correction (2026-08-02, after the primary
Solan--Vieille audit).** Every finite multiplayer stochastic game already has
a uniform autonomous correlated-equilibrium payoff when an external device is
allowed. Thus at the correlated stratum the root target correspondence is
nonempty for every player number. The ordinary-Nash open core is the
implementable subcorrespondence: which of those mediated targets can be
realized using only the original game's legal actions, public monitoring, and
independent private randomness? This is not captured by a Boolean "public
coin available" field. The Solan--Vieille construction uses current private
recommendations and one-stage-delayed disclosure. Its device continues to
emit signals after a detected deviation, but the prescribed coalition-minmax
punishment is ordinary and ignores those signals; it should not be described
as correlated punishment. Fresh contingent tables are sampled independently
across dates, while the realized play remains temporally linked through the
public-history-indexed recommendation and delayed disclosure. Q100 therefore
makes the correlation source an explicit strategy-class axis and asks for a
robust sublinear-cost compiler or an obstruction. No such general compiler is
assumed by this stratification.

**Product-image correction (2026-08-02, after the fiberwise audit).** For any
finite local observation map \(L\), the correlated image is exactly the convex
hull of the product image:

\[
C_L=\operatorname{conv}P_L.
\]

Hence exact product replacement on a selected local fiber is possible exactly
when the selected observation lies in \(P_L\), and universal equality
\(P_L=C_L\) is equivalent to convexity of \(P_L\). If full local equality is
available, simultaneous replacement preserves every retained exit, charge, and
slack coordinate on an arbitrary graph; there is no additional DAG or
recurrent-class gluing obstruction. This conditional core is now formalized.
It does not prove that the sustainable correlated selector chosen by the root
correspondence lies in a product fiber. Selected-fiber realization remains the
operative de-correlation problem.

Q108 now proves the exact abstract quantifier obstruction: for rational affine
packet correspondences, product feasibility at every context over every
target, and even joint feasibility for every proper context subset, need not
give one common packet. The binary gadget and the two- and three-context
counterexamples are Lean-formalized through `80d7cb2`. This rules out a local
Helly-style shortcut. It is not a phase-lifted stochastic-game realization or
a root refutation. The next theorem must use game-shaped balance and
continuation structure, or embed the obstruction in an actual game with
targetwise or target-free strategic quantifiers.

**Multiscale correction (2026-08-02, after the compactification audits).**
Ordinary limiting occupation measures erase rare exits, and one ordinary
Poisson bias can miss the scale selecting a moving multichain resolvent. The
first leading-symbol/SCC residual calculus is exact in the forward direction.
Within an explicitly supplied convergent finite-ramification presentation, the
full Puiseux hierarchy of deviation residuals is complete. No converse has
been proved for arbitrary abstract scale packets or unrestricted policy
selections. Q109's exact full-germ block elimination, affine-row preservation,
and rebasing core is now Lean-formalized in
`ExactBlockElimination.lean` at `b721655`, with the general rectangular
two-block quotient identity in `ExactBlockEliminationConfluence.lean` at
`d35c1d8`. That classical algebra is no longer a prerequisite. The remaining
root-level prerequisite is controlled Schur closure under policy choice:
reduction must produce one finite controlled system whose legal policies and
unilateral deviations correspond to the original choices. Compression,
branch selection, and causal implementation are separate and open.

**Quitting bridge correction (2026-08-02, after Q107).** The launched Q107
plateau axiom omitted the jump set; the published axiom removes
\(S(\pi)\cup T(\pi)\). With that correction and a proper-jump convention,
terminal approximate equilibrium exists exactly when Never, a continuation-
credible First profile, or a standard-proper sequentially perfect absorption
path exists, conditional on the named imported compactness/refinement and
local-to-global lemmas. Q107 supplies the four stationary regimes, localized routing of
a limiting terminal jump to First, and a tail-relative product-cell compiler
with the 2001 stationary fallback. The path theorem remains terminal
internally. Solan--Vieille Proposition 2.13 then converts each terminal
\(\varepsilon\)-equilibrium to a common-horizon uniform
\(\varepsilon'\)-equilibrium for every strict
\(\varepsilon'>\varepsilon\), and compactness selects one fixed target across
accuracies. Thus the unresolved quitting-game root is global proper-path
existence outside the simple branches, not a separate terminal-to-uniform
modulus. Formalization of the compactness, compiler, fallback, and
uniform-over-deviations theorem is still required.

Both verified benchmark constructions (Big Match's fair coin and FTV's cyclic
schedule) use gain--bias indifference: their apparent enforcement cost is zero
after continuation values are included. Q95 proposes that the general
dichotomy is between dynamic indifference and a positive recurrent Bellman
residual, not between current-stage best replies and non-best replies. Its
general budget and irreversibility sections are not yet independently sealed.
A fixed finite loss is asymptotically harmless in the checked finite
gain--bias setting; the full history-dependent formulation remains part of
that audit.

## The external critique (2026-08-02) and what was adopted

Seven corrections, all adopted; credited to the external (GPT) review:

1. **Not a polytope.** Q89's polytope is a one-controller artifact. In a
   multiplayer game, independent mixed actions impose product
   (polynomial, nonconvex) constraints on joint occupations; convexity
   returns only under public correlation, whose endogenous robust cost is
   measured by the Q88 robustness problem. Correct object: the
   **phase-lifted sustainable occupation-certificate set**, semialgebraic
   for a fixed template.
2. **The union over templates is not one semialgebraic set.**
   \(\bigcup_P\mathcal S_P\) has unbounded integer quantification;
   semialgebraicity holds only template by template. Whether a computable
   template bound exists, or the union is provably non-semialgebraic, is
   the isolated question — farmed as **Q93**.
3. **Periodic schedules are too narrow.** The finite stratum must range
   over finite causal public controllers (automata reading the public
   signal); periodic clocks are the special case.
4. **Occupation harmlessness is not sustainability.** The certificate
   must carry: prescribed occupation and payoff delivery; entry and
   complete-vector target transport; per-player handoff-closed deviation
   caps; credible continuation/punishment; the correlation source (or its
   absence); shifted-horizon remainders. (Already the frontier's demand;
   restated here as part of the definition, not an afterthought.)
5. **"Face" is the wrong word.** Uniform sets in the benchmark games appear as
   **truncations** of exposed occupation sets. Q95 sharpens the truncating
   quantities to architecture-specific unilateral values; "individually
   rational" and "solo-deviation floor" are not general formulas. This remains
   a candidate structural regularity, not a proved theorem for all games.
6. **The FTV test is stratum separation.** The benchmark statement is
   "no \(P=1\) sustainable certificate, some \(P>1\) certificate," not
   "no stationary face contains the cyclic payoff" — payoff
   representability and sustainability are different. Q87 has now verified
   the uniform quantifiers and geometric absorption bound.
7. **Big Match reveals an intermediate stratum.** By
   Hansen–Ibsen-Jensen–Neyman (Math. OR, doi 10.1287/moor.2022.1267), a
   clock plus two memory states is already \(\varepsilon\)-optimal in the
   Big Match, while time-homogeneous finite automata fail. So Q90's
   automaton-resistant class measures resistance at the
   **time-homogeneous** stratum only, and any self-similarity verdict for
   it says nothing about clock-aware finite memory.

## The adopted hierarchy

The finite classes form a two-axis partial order rather than one chain:

~~~text
stationary ⊆ periodic ⊆ public homogeneous finite
                              ↙              ↘
            public clocked finite        private homogeneous finite
                              ↘              ↙
                         private clocked finite
                                  ⊆ unrestricted adaptive.
~~~

Here "clocked" permits unrestricted dependence of action and update maps on
the stage number, while "private" permits hidden memory with fresh randomized
updates. Public homogeneous controllers embed into both adjacent classes.
Public-clocked and private-homogeneous are not ordered by the definitions.

Q94 establishes the exact Big-Match cell pattern: homogeneous public,
homogeneous private, and clocked public finite memory all fail; clocked private
memory succeeds with two states. Thus the operative resource is the
combination of the clock and hidden randomized updates, not memory cardinality
alone. Q94's general completeness question remains open already for two-player
zero-sum games.

For a fixed finite **public Markov** architecture (controller skeleton, public
node bound, stationary mixed rows, and deterministic update rule), let
\(\mathcal S_\tau(G,s_0)\) be the targets carrying the Q95 gain--bias
 certificate. This set is semialgebraic; with the rows fixed, the
acceptance and occupation-obstruction tests are finite linear programs.
Conditional on Ummels's primary finite-state-SPE theorem (whose thesis proof is
explicitly a sketch), Question 98 proves that the union over all public-node
bounds and skeletons is recursively enumerable complete. Consequently there
is no total computable per-input node bound. The reachable terminal-game bridge
and graph trimming before all-node completion are internal arguments; none is
yet Lean-formalized, and the result does not decide global geometric tameness.

This claim does not extend automatically to arbitrary clock dependence or
private memory. A clocked controller includes an unrestricted sequence of
date-dependent maps, and a hidden finite controller induces a generally
continuum-valued public posterior. Neither is a finite public semialgebraic
template without an additional representation theorem.

## Benchmark battery (per stratum)

- **Sorin**: target selection is forced off the discounted endpoint; the
  uniform set is a truncation of an exposed edge. Lean now proves the
  target-free `14ε` survival/occupation estimate, the resulting identity
  `2w₁+w₂=2` for every uniform-equilibrium payoff, and unconditional exclusion
  of the discounted endpoint. This settles the separation fence, not the
  converse construction of every point of Sorin's segment and not a generic
  root-target selector.
- **FTV**: no one-live-phase cyclic architecture works, while the period-three
  public architecture satisfies Q56/Q95 exactly. Q87 verifies the uniform
  quantifiers; the mathematical actual-data adapter is complete, and the Lean
  adapter and the exact finite-algebra minimum/normalized rigidity theorem are
  now Lean-formalized. Lean also proves the concrete controller's exact
  prescribed-delivery modulus \(22/(7T)\), its all-start semantic credibility,
  and identification with the standard exact cyclic packet. The general
  arbitrary-\(K\) equilibrium-theoretic necessity and sufficiency of that
  packet, any stronger full-equilibrium sharp modulus, and the weighted-regret
  counterfamily remain unformalized. It is not a uniqueness theorem for
  arbitrary public controllers.
- **Big Match**: public finite memory fails even with a clock, and homogeneous
  private finite memory fails; clocked private two-state memory succeeds. This
  is the mandatory warning that finite-public verification is not
  strategy-class completeness.
- Wanted: a witness separating private-clocked finite memory from unrestricted
  adaptive behavior, or a proof none exists. Q94 shows that this is an open
  zero-sum-hard problem, with the Big Shift only a candidate witness.

## Near-term plan (independent of the open decisions)

The fixed-public global and support-pruned criterion directions are checked,
umbrella-imported, and committed at `24b5bf7`, alongside the already landed
optional transport, signed stopped-target composition, and switched-potential
components. The actual FTV acceptance test is landed at `8090347`, its exact
cyclic minimum/rigidity layer at `408bf3b`, and Q96's escaped-class falsifier
at `68149dd`. The Q96 semantic converse is now also landed through
`SplitDomainNeutralOccupationConverse.lean` (`4f12352`): shifted prescribed
delivery and all-behavior unilateral caps on the exact split domains synthesize
both gain--bias families and force owner-local neutral-occupation
nonpositivity. Its exact all-start semantic iff gain/bias wrapper is now landed
at `fcf3ff4`. This characterizes a supplied split public architecture; it does
not choose an architecture or prove unrestricted coverage. What remains in the
bounded rejection language is the occupation-packet presentation and
rejection theory: formalize the exhaustive `(RC)`/fifth-obstruction
alternative, rational witnesses, and any claimed sharp span constants. Do not
freeze the refuted unconditional four-condition equivalence.

Q100's sharp strategic-form product separator is landed at `a6a66b5`, and its
four-state payoff-preserving absorbing lift at `9f8aece`. These are regression
guards for one declared mediated target. They define neither an autonomous
device nor an ordinary-strategy compiler/noncompiler theorem, and they do not
rule out retargeting or ordinary uniform-equilibrium existence in that game.
The deliberately target-specific close adapter has now landed: `afe018c`
extracts the arbitrary mixed root law and proves unilateral update commutation,
and `a9cb4ca` excludes only the declared target `(5/7,5/7)`. Other uniform
targets in the lift forbid use of a global nonexistence certificate, and this
one-target theorem does not eliminate retargeting.
The next falsification question therefore asks for a target-free late-horizon
exploitability gap or an exhaustive elimination of every target, not merely a
failure to implement one correlated witness.

Several adjacent formal lanes are now closed and should not be left as
dependencies of this design. The finite zero-sum single-controller theorem is
unconditional through `42e4501`, including LP attainment and construction of
the required optimal primal/projection witness. The unique-state
realized-action/history-law bridge, transition-monitoring/Fink-row
identification, and Cesaro observable-action trigger are also landed through
`6e3f0af`, `c772fab`, `096d314`, `c08637c`, and `31a5969`. Finally,
`e5f9145` and `80ea1ba` formalize product-image convexification and
conditional exact fiberwise replacement. These are genuine positive subcases
and adapters, but none selects a sustainable multiplayer architecture or root
target.

The newer finite kernels are also landed with narrow scopes: Q102's
first-scale cut/product-flow package at `f09c92f`, Q104's complete offline
bounded-discrepancy equivalence and Q111 hidden-fiber regression routed at
`32a80e7`, Q108's abstract selected-fiber
counterexamples at `80d7cb2`, Q109's exact block elimination/rebasing at
`b721655` and rectangular quotient confluence at `d35c1d8`, and Q110's
responder-credibility-to-floor comparison at `c485210`. None supplies the
game-shaped selector, causal scheduler, controlled-policy reduction, response
producer, or root correspondence.

The root-design work itself now sits behind four mathematical discriminants:
the repaired quitting path/barrier problem (with four players the first open
and highest-priority test, not a reduction of all larger player sets), a punisher-side
cap/floor/re-entry alternative on a restricted recursive class, selectorwise
de-correlation with retargeting, and a product occupation--escape-flux/SCC
lift. The absorption-path source definition omits sure terminal jumps from its
discrete optimality clause, while testing them against continuation zero is
also unsound. Review 07 records the two repair routes. Until a corrected bridge
lands, the printed path equivalence is not a premise of this stratification.

The quitting discriminant now has a second exhaustive formulation that is
safer to use operationally. Optimized finite zero-boundary exact debt either
vanishes, which already compiles to a uniform payoff, or yields a projective
positive-debt tail with one summable opponent clock (`28df2d0`). The positive
coordinate has machine-checked terminal-solo provenance and a linear-mass
full-set boundary packet (`4600601`, `0ab9d31`). Q129 and Q130 rule out owner
labels and fixed-scale marked recurrence as complete producers. Q131, now
formalized at the scalar level in `801095a`, shows that any actual relative
boundary certificate can be reinserted with a depth-free payoff-mismatch
penalty. The two-ended endpoint core is now also machine-checked (`e2d5170`):
one subsequence retains a forward positive-debt/summable-clock ray and a
reverse zero-boundary ray with the same owner positive at depth one and a
quantitative terminal packet. It does not retain the bridge-survival scale,
preselected marked atom, or transported mass, and it does not join the two
rays. The finite-chain correction at `9334ab4` now proves that the
preterminal survival and final marked-action mass are separately positive,
bounded by one, and each carries the same linear debt lower bound. This makes
them honest distinct compact coordinates; their common-subsequence transport
and bridge factorization remain to be coupled to the two rays. This sharpens
the first discriminant: its unresolved datum is the
**bridge/producer of a sustainable relative boundary**, not endpoint
compactness, terminal-to-uniform conversion, or finite-prefix error
accumulation. The endpoint theorem must not be imported into the general root
correspondence as though a certified splice already existed.

The first static producer rungs are now classified. Positive-solo
own-joining monotonicity closes a genuine table class (`23ed68a`); cutoff-one
safety and finite-prefix max-affine acceptance are exact production APIs
(`6b5ab61`, `76d82df`); owner-solo certification either closes the game or
returns a universal joining obstruction (`ee560bb`). With two players that
obstruction always admits an accuracy-indexed pair repair (`a1e7ccb`,
`6960e5f`). For three or more players the remaining static issue is not a
selected successor owner but credibility of the full quitting set: internal
leavers and outsider joiners must all be controlled. A scoped three-player
regression shows the positive packet and universal solo obstruction alone do
not force such a set in the vanishing-owner limit. It has a credible
owner-containing sure coalition at the opposite endpoint. A strengthened
three-player table now exhausts the full owner-hazard/sure-opponent grammar and
all pure First cells with uniform positive gaps (`9f6614c`). That stronger
fence is repaired by the exact mixed stationary root
`(1/2,1,1/4)` with payoff `(1,3/4,1/2)` (`bc86435`). It therefore remains a
grammar regression and cannot promote a dynamic-repair conclusion. At the
generic level, `6a64b15` now gives a necessary-and-sufficient full-rate cap
test for any supplied stationary product root, including every degenerate
face and arbitrary behavioral deviations. What remains is root synthesis or
exhaustive exclusion for a table, not ambiguity about how to verify a supplied
root. Neither regression establishes a positive optimized plateau or refutes
existence.

A separate general sufficient class is now production-grade: positive
one-sided security floors saturating a uniform positive weighted-welfare cap
assemble into one uniform-equilibrium payoff (`81aec6c`), and a bounded social
Bellman bias supplies that cap with a `2*C/T` loss (`bf65314`). This resolves a
real coalition-split compatibility problem but does not produce saturation in
arbitrary games, so it is a parallel root face rather than a general selector.

The supplied-splice and arbitrary-profile sure-First classifications now land
through `c0fd129` and `a1e6f4a`, alongside Never and the direct negative
finite-horizon implication. Q107 supplies the near-sure/vanishing-hazard
regime extraction, corrected-path exhaustiveness, and uniform
discretization/regret architecture mathematically, but only modulo its named
imported lemmas and without a Lean formalization. The response-side alternative is
deliberately restricted: R4 already implies R5, so it should construct cap,
responder credibility, and robust finite re-entry on a finite
recursive/absorbing class, or return an exhaustive owner-cycle obstruction.
Asking this before a global existence theorem avoids baking an unproved
response producer into the root target definition.

The finite occupation audit likewise separates what may safely enter the
definition. Exact full-coordinate fiberwise equality, the Q108 joint-packet
counterexamples, and offline rational zero-charge circulation are valid
compositional or falsifier kernels. They do not give a game-shaped selected
product fiber or a causal scheduler under deviation-conditioned public laws.
Approximate gluing must retain exit-projection norms and
nonnegative/substochastic bounds for both the original and replacement routing
systems. These are requirements on a future root certificate, not automatic
properties of every target.

Retire Q93's literal (S4)--(S5) class in favor of Q95's configuration-dependent
harmonic targets, retain its finite Bellman-compression result for fixed public
state spaces, and record Q98's negative solution of the computable-node-bound
question. Q99 has an effective input model and the correct product belief
filter for independently randomized private memories under full public action
observation. It asks for verification of one supplied profile, not synthesis
or completeness. Its finite delivery calculation is elementary;
Rosenberg--Solan--Vieille's finite-POMDP theorem gives existence of the
unrestricted asymptotic best-response value and one uniformly near-optimal
behavior strategy. Chatterjee--Saona--Ziliotto further give deterministic
finite-memory approximation, hence finite witnesses for strict cap violation.
The separate audited PFA embedding respects simultaneous-action timing and
makes the threshold hierarchy sharp in this product-filter class:
\(L>c\) is \(\Sigma^0_1\)-complete, \(L\le c\) is
\(\Pi^0_1\)-complete, \(L\ge c\) and \(L=c\) are
\(\Pi^0_2\)-complete, and \(L<c\) is \(\Sigma^0_2\)-complete. Therefore
strict rejection has a finite transducer certificate, while cap acceptance
cannot have a complete recursively
  enumerable finite rational/algebraic certificate family. The appended answer
  now proposes an exact repaired-historywise classification and a third-level
  effective-clock classification, but those additions are review-pending in
  `ephemeral/reviews/Review01-*` and `Review02-*`; the automatic-clock exact
  boundary remains open. Other remaining targets are exact attainment,
  stationary and fixed-memory policy classes, restricted-class
  \(\eta\)-optimal memory bounds, tight delivery complexity, and useful
  decidable subclasses. Do not use Q99 to design an API before the internal
  reduction is formalized, and do not assume Q94's open completeness statement.
  Postpone every finite/adaptive completeness claim.

## Open decisions (deliberately not taken here)

- Whether the *root question* eventually posed to external solvers
  demands the full correspondence be semialgebraic (falsifiable, riskier)
  or only fixed-template computable (provable now). Current stance:
  fixed finite public-Markov templates now. Q98 rules out a total computable
  node bound for their unbounded union; global geometric tameness remains a
  separate question. No semialgebraicity is currently claimed for arbitrary
  clocked or private controllers.
- Whether the private-clocked class equals the unrestricted adaptive class.
  Q94's answer identifies this as open, not as a design choice already decided.
  An affirmative theorem would collapse the adaptive residual; a negative
  witness would define an honest hard core. Neither outcome is assumed by the
  current interfaces.
