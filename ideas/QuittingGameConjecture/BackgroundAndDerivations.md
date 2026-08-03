# The Quitting-Game Uniform Equilibrium Conjecture

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `OPEN` |
| Objective priority | `P0` |
| Last audited | 2026-08-03, through `6a64b15`, `bc86435`, `e2d5170`, and the Q132 audit at `18adbd2` |
| Central live claim | Every positive optimized-debt plateau yields a terminal approximate equilibrium, or a bounded exact extension uniformly lowers the optimized debt. |
| Next discriminant | Refine `e2d5170` along `9334ab4`'s separately positive preterminal-survival and terminal-atom coordinates, retaining one marked action and its bridge factorizations; then decode that bridge as an executable repair or uniform optimized-debt descent. In parallel formalize Q132's behavioral nonclosedness regression. |
| Production destination | Terminal approximate-equilibrium existence, hence a uniform-equilibrium payoff. |
| Supersedes / superseded by | Supersedes the uncorrected proper-path-only plan; no successor. |

## Claim ledger

| ID | Exact claim | Verdict | Seals | Scope / consumer |
| --- | --- | --- | --- | --- |
| QG1 | Terminal approximate Nash profiles at every positive accuracy are equivalent, at the existence level, to a uniform-equilibrium payoff. | `PROVED` | `M+L+C` | Finite quitting games; final semantic reduction. |
| QG2 | Finite exact zero-boundary Nash--Bellman chains have attained optimized debt, and vanishing optimized debt produces terminal approximate equilibria. | `PROVED` | `M+L+A+C` | Positive/zero debt split. |
| QG3 | A positive optimized-debt plateau yields a marked owner, the exhaustive owner-clock split, separated preterminal survival and terminal-action mass, and compatible forward/reverse exact-D boundary rays. | `PROVED` | `M+L+A+X` | The finite middle is not retained by the two-ended experiment. |
| QG4 | Every fully summable positive plateau yields an executable repair or a bounded exact extension with one cutoff-independent positive debt drop. | `OPEN` | `I` | This is the remaining relative-boundary producer, developed precisely in `ideas/PositivePlateauBoundaryClosure/README.md`. |

## Falsifiers and wrong turns

- Failure of owner-solo, direct-First, or a narrow sure-set grammar does not
  imply that a dynamic repair is necessary; the exact mixed stationary
  regression forbids that inference.
- Attainable terminal payoff--cap data are not closed, so a limit point is not
  automatically an executable tail.
- A close forward seam and a reverse marked endpoint do not by themselves
  transport the mark through the finite middle; the exact two-point
  persistence counterexample is a mandatory regression for QG4.

## Production map

The chain optimizer, exact-debt tail, clock split, stationary verifier,
terminal packet, and terminal-to-uniform consumer are in production. Isolated
probes under `experiments/` supply the two-ended compactification, max-affine
block summaries, buffered return/exit topology, and depth-free seam penalty.
The missing arrow is an actual-chain bridge retaining the marked packet and
all playerwise cap data through the finite middle, followed by a strategic
decoder. [`PositivePlateauBoundaryClosure`](../PositivePlateauBoundaryClosure/README.md)
owns that arrow; this file owns the exhaustive conjecture-level assembly.

## Exit conditions

- Mark `MINED/PROVED` only after QG4 is proved and its output reaches terminal
  approximate existence and terminal-to-uniform selection in production.
- Mark QG4 `WRONG` if a finite quitting table has a certified positive plateau
  but admits neither its stated repair nor a uniform debt-decreasing extension;
  retain that table as the next counterexample candidate.
- Mark this group `SUPERSEDED` only if another exhaustive producer or a genuine
  finite quitting-game counterexample resolves every live obligation here.
- Do not mark it `BLOCKED` merely because the finite-middle bridge remains hard.

## Readiness audit and research program

**Assessed:** 2026-08-03
**Repository checkpoint:** `bf65314` (`derive weighted welfare caps from Bellman bias`)

## Executive verdict

The repository is not already in possession of a proof that every finite-player
quitting game has a uniform equilibrium. It is, however, positioned to make a
serious and unusually well-audited attack on the problem.

The distinction is important:

- the formal model, solution concept, terminal-payoff semantics, exact root
  continuation calculation, exact `Never` and supplied-profile `First`
  branches, the continuation-preserving near-sure-to-sure transfer, the
  full finite quitting-game terminal-to-uniform bridge, and compact fixed-payoff
  selection are present in Lean;
- arbitrary behavioral quitting deviations reduce exactly to deterministic
  quit times or Never; cyclic root packets with playerwise contraction compile
  to terminal Nash and uniform payoffs; and the analytic Banach/Krawczyk
  root-existence consumer is present in Lean;
- several general-purpose ingredients that a constructive proof would need are
  also present, including deviation-cap interfaces, self-generation machinery,
  product-image convexification, the exact offline bounded-discrepancy
  equivalence, selected-fiber regression theorems, and explicit finite-horizon
  accounting;
- Q107 supplies, at the mathematical level, the corrected
  Never/First/proper-path equivalence. Questions 125--131 now give a second,
  exact exhaustive attack through optimized finite Nash--Bellman debt. Its
  zero-limit branch compiles to a uniform payoff; its positive-limit branch
  produces a projective exact-debt tail, a summable opponent clock for one
  owner, and a genuine positive-mass terminal full-set advantage packet;
- the missing global chain is now **relative-boundary production**: turn that
  positive-debt exceptional object into an actual certified terminal tail (or
  another exact restart) whose delivered value and all-behavior deviation cap
  fit the prefix, or derive a global positive exploitability gap. Q131 closes
  the semantic splice once such a certificate is supplied, but has no
  independent existence force because its corrected interface permits the
  length-zero prefix. Terminal-to-uniform conversion is no longer part of the
  gap.

Thus the accurate verdict is:

> We are positioned to prove decisive intermediate theorems, to certify a
> candidate counterexample, and possibly to solve the four-player case. We are
> not one routine formalization lemma away from the conjecture.

The leading direct research target remains four-player quitting games, because
one counterexample there settles the conjecture negatively and the first
unknown player count is the smallest realistic place to expose the obstruction.
The leading theorem target, however, is no longer one particular periodic
atlas. It is the positive-exact-debt boundary producer isolated by Q125--Q131.
Stationary roots, credible First profiles, contracting lassos, and proper paths
are tested output classes; none is assumed complete. The exact block-pair
atlases remain valuable nonstationarity and coverage regressions, and Q121's
accuracy-indexed periodic-density problem remains a serious positive subroute,
but objective priority now lies with the exhaustive debt split rather than
with completing one recently successful architecture. A positive result must
eventually work for every finite player set or be paired with a reduction.

### Direct four-player update after Questions 113--118

The first explicit direct table has been resolved positively, not merely
narrowed. For the cyclic \(A=1,C=3\) table, Question 116 constructs an exact
completely mixed stationary product profile with algebraic quit probability
and proves its selected unilateral Snell caps equal its prescribed payoff
after every live history. Independent recomputation confirms the polynomial,
fixed point, hazard, and cap calculation. The table is retired as a
counterexample candidate. This concrete certificate is now machine-checked in
`CyclicFourPlayerQuitting.lean` through `902797d`, including terminal Nash
credibility and the uniform-equilibrium-payoff consequence.

The mechanism extends across the whole positive cyclic family. With
\(\beta=2A-C\):

- \(0<C<2A\) has the rotating continuous absorption path;
- \(C=2A\) has a uniform-singleton continuous path, despite having no
  stationary complementarity root for \(A>0\); and
- \(C>2A\) has a unique symmetric interior stationary root.

This three-way phase diagram is exact hand-verified mathematics, not yet a
Lean theorem. It shows that tuning the old family cannot produce the desired
barrier.

The supporting answers sharpen the proof object without closing the general
conjecture:

- Question 113 gives the selected Snell cap and pure-quit-time extremality. Its
  correction is that zero-boundary finite truncations need not be monotone,
  and support optimality needs cap-side transversality. The infinite
  pure-time/Never extremality and arbitrary behavioral reduction are now in
  Lean at `315ed67`/`338f61f`.
- Question 115's nonnegative-solo survival-weighted bound, after adding the
  own-never atom and repairing off-path claims, is subsumed by the landed
  one-exception synthesis at `f13679f`.
- Question 114 identifies the exact local zero-hazard root fiber by
  semialgebraic directional germs. Ordinary coordinate tiers are not enough,
  and global chattering/relaxed trajectory compactness remains open.

The direct search has now left the cyclic family. Review 23 records an exact
rational mixed-sign-solo block-pair table whose stationary-support and every
sure-quitter face are excluded by rational certificates through `ff5ff0f`.
It also gives a hand proof that the normalized residual inclusion has no
bounded complete ordinary AC singleton-flow path, even under arbitrary
measurable chattering. Mixed signs are structural: Question 115 closes the
sole noncontracting opponent-clock branch when all solo rewards are
nonnegative.

Those filters did not produce a counterexample. Review 25 and the exact
rational-interval checker at `97bcc25` isolate a period-eleven proper
product-jump Bellman root for the same table. Every inactive gap is strictly
negative and every playerwise opponent cycle contracts. The script has passed
an independent equation/Jacobian audit, and `044a3cb` adds the independently
checked 31-polynomial elimination with a canonical rational preconditioner
export. Two neighboring phase-4 supports are exactly certified at `a3ff0b8`
and `909e5ef`. Their phase-zero payoff boxes and the original box are pairwise
disjoint in all four coordinates, so the table has at least three external
periodic payoff branches. The generic Banach/Krawczyk, periodic terminal-Nash,
and uniform-payoff consumers are now in Lean at `b737f4a`, `2214d77`, and
`22cb9ac`; exact Lean evaluation of the finite witnesses and their concrete
endpoint/contraction packets is not.
The example now proves, at the external-certificate level, that product jumps
can rescue a table after stationarity, credible First, and every ordinary AC
singleton-flow path have all failed.

Reviews 27--30 and Questions 118--121 now separate mechanism from the solved
certificates. The six observed supports give rational or selected-quadratic
predecessor charts. On one rational phase-5 box, exact exhaustion leaves only
the three observed phase-4 masks. The true four-dimensional returns have exact
derivative norm below 0.1, refuting the local invariant-circle reading. The
three nondegenerate roots and strict margins give a common open payoff
neighborhood with three analytic sheets. The exact parameter theorem at
`b988da7` keeps all three fixed words strict and strategically valid when only
(r_0(\{0\})=-2+\theta) varies over (|\theta|\le1/200), but does not yet
make payoff separation, return contraction, or support exhaustion uniform on
that interval. Question 120 now proves, at independently audited mathematical
status, the general fixed-word analytic-sheet theorem and the qualified
chamber-wall continuation law. It also gives a valid period-one producer on a
nonempty open two-active-player chamber and a constant-loss example showing
that strict nonsingular lassos are not necessary for equilibrium existence.
Question 121 replaces exact-lasso production by the correct accuracy-indexed
periodic exploitability infimum, and its exact negative-payoff calibration
shows that playerwise-contracting lassos are not universally complete. Review
30 proves the fully opponent-absorbing finite-block closing case and gives an
exact prefix-reset obstruction to naive closure under mere total absorption.
Its abstract affine/Snell bounds are Lean-checked at `cdd9faf`; selection or
fallback for the unique exceptional opponent clock is now split cleanly by
quantifier strength. Under all-tail/subgame-perfect optimality, the Q121
addendum proves a late stationary one-active-player fallback with error
\(\beta+4M\eta_t\), or a credible First tail when absorption is sure at one
stage. Under designated-phase optimality alone the selection problem remains
open, and a First profile need not be periodic. The exact 27-box/81-edge atlas
does prove a local graph-directed full shift for the block-pair table; no
entry theorem from the surrounding continuation region, global exhaustion,
global degree, or universal periodic producer theorem has yet been proved.

### Exact-debt update after Questions 125--131

The finite-chain route now has a proved exhaustive first split, but not yet a
complete solution.

For each cutoff, minimize the largest playerwise exact dynamic debt over the
compact set of zero-boundary exact Nash--Bellman chains. The optimum is
attained and antitone in the cutoff. If its infimum is zero, the landed finite
compiler and terminal-to-uniform selection theorem produce a uniform-equilibrium
payoff. If the infimum is positive, compact projective extraction produces an
infinite exact-debt path with a fixed player carrying positive debt and a
summable opponent clock. This dichotomy is in Lean through `28df2d0`; the
optimizer/calibration layer is in `89164d1`.

The positive branch is now much less mysterious. Question 127 proves that the
same owner's debt persists to the terminal edge of every finite approximant
and forces a positive-mass full simultaneous-quitter packet. Question 129
identifies the exact optimal deviation: Continue through the prefix and take
the terminal solo option. Quantitatively, if the owner's solo payoff is
\(q_i>0\), its opponent-survival mass \(\pi_i\) satisfies

\[
  D_i/q_i\le \pi_i.
\]

The selector-free provenance is machine-checked in `4600601`, and the direct
linear terminal-packet bound is in `0ab9d31`.
The packet must retain its full quitter set. It does **not** automatically
create debt for an active or inactive joiner; Question 129 gives exact
two- and three-player counterexamples to that proposed owner-transfer rule.

Questions 128 and 130 then delimit the exceptional compactification. A
divergent own clock closes the extracted path positively: the prescribed
profile absorbs almost surely and is exact terminal Nash. If the own clock is
summable as well, the continuation values converge and split into an absorbed
part plus positive Never mass, but the limiting barycenter need not itself be
sustainable. Nor do repeated temporal owner labels force a compatible cycle:
Q130 gives a summable-clock, vanishing-scale fence escape. These examples
refute two proof architectures, not equilibrium existence; the Q130 table has
a separate credible singleton-First equilibrium. Q128's corrected status is
important: its scalar tail identities survive, while global-clock statements
must be suffix-indexed, the proposed Palm law is not exhaustive or invariant,
and the payoff-separation proof must retain the Never atom.

Question 131 closes the consumer side. A supplied terminal tail with payoff
matching the end of any finite exact prefix and relative deviation debt
\(\beta_i\) splices with exact initial exploitability equal to the backward
debt \(B_i^0\). If the payoff mismatch in coordinate \(i\) is \(e_i\), then
with full prescribed prefix survival \(P\) and opponent-only survival
\(\chi_i\), the exact best-response perturbation is

\[
 \max\{A_i,T_i+\chi_i e_i\}-(v_i^0+P e_i),
\]

and hence the additional exploitability is at most

\[
 (\chi_i-P)(e_i)_+ + P(-e_i)_+
 \le \|e\|_\infty\max\{P,\chi_i-P\}
 \le \|e\|_\infty.
\]

There is no depth factor. This theorem is a sharp semantic compiler, not a
producer: completeness requires arbitrary exact prefixes, including length
zero, and at length zero the certified branch is simply the supplied terminal
approximate equilibrium itself. The remaining task is therefore exact and
unavoidable: manufacture the relative boundary certificate from the
positive-debt exceptional object, or turn failure of every such manufacture
into a uniform positive exploitability gap.

Section 79 of the proof-mining report adds one genuine positive class and a
finite boundary calculus. If every player with positive solo reward weakly
benefits from joining every nonempty opponent quitting coalition, the terminal
packet required by positive debt is impossible. Cutoff one already has zero
debt, so a uniform-equilibrium payoff exists. Consequently any counterexample
must contain a positive-solo player strictly harmed by joining some nonempty
coalition. This theorem is now in production (`23ed68a`).

More generally, cutoff-one success is exactly the semialgebraic condition
\(C_i^+(x)\le V_i(x)\) for every player at one zero-tail Nash root. Every
longer finite prefix has a five-scalar playerwise summary: early stopping
\(A\), continue-to-tail offset/survival \((T,\chi)\), and prescribed
offset/survival \((B,P)\). Its acceptable terminal values are the intersection
of two explicit affine halfspaces, and positive-length summaries form a
max-affine composition semigroup. They are not literally a monoid over five
finite real scalars: a global identity would require an early-stopping floor
of \(-\infty\), or an extended/restricted domain. The cutoff-one
characterization and finite-prefix geometry are now production theorems
(`6b5ab61`, `76d82df`). This makes boundary production finitely testable for a
supplied prefix without making the attainable tail set convex or supplied.

The linear terminal packet also corrects the compactification picture. Fixed
forward-time marks may vanish, but the transported last-edge cylinder has raw
mass bounded below linearly in the positive optimized debt. It escapes by
moving to the cutoff. The next compact object must therefore couple the
forward positive-debt plateau to a reverse-time marked atom at infinity.

The first off-chain repair is also exact. For a positive-debt owner \(i\),
prescribing only \(i\) to quit at rate \(p>0\) is terminal Nash precisely when

\[
(1-p)r_j(\{j\})+p\,r_j(\{i,j\})\le r_j(\{i\})
\qquad(j\ne i).
\]

Thus either the owner's solo payoff is already a uniform-equilibrium payoff,
or every \(p\in(0,1]\) has a strict opponent obstruction; the latter yields a
strict sure-joiner and a weak preemptor. The complete rate dichotomy is now in
production (`ee560bb`).

With two players the obstruction is completely repairable. Let the unique
opponent quit surely and let the owner quit with hazard \(p\downarrow0\).
The exact arbitrary-behavior caps give exploitability at most

\[
p\left(r_i(\{j\})-r_i(\{i,j\})
  +|r_j(\{i,j\})-r_j(\{j\})|\right),
\]

so the opponent-solo payoff is a uniform-equilibrium payoff (`a1e7ccb`,
generalized role-parametrically in `6960e5f`). The genuinely multiplayer
residue is set credibility: when a whole marked set \(T\) quits, a member may
profit by leaving \(T\), and an outsider may profit by joining it. A scoped
three-player regression defeats every opponents-sure repair in the
vanishing-owner limit. It does **not** exclude the rest of the owner-hazard
interval—the same calibration has a credible sure coalition containing the
owner at \(p=1\).

A second calibrated table now closes that entire static grammar (`9f6614c`).
For every owner hazard \(p\in(0,1]\) and every subset of sure-quitting
opponents, including the empty set, terminal exploitability is at least
\(1/3\); every nonempty direct pure First profile has gap at least \(1\).
This is an exact behavioral-cap result, not a one-stage proxy. It does **not**
survive the complete stationary hazard cube. The exact mixed root

\[
(p_0,p_1,p_2)=(1/2,1,1/4)
\]

has payoff `(1,3/4,1/2)`, equals every player's exact unilateral cap, and is
an exact stationary terminal Nash equilibrium (`bc86435`). Thus the table is
a regression against the owner-plus-sure-set grammar, not evidence that a
dynamic or memory-bearing repair is required.

The generic lesson is now machine-checked. For every supplied stationary
product root, including all sure-continuation boundary faces, the piecewise
full-rate cap is attained and its playerwise inequalities are equivalent to
terminal ε-Nash against arbitrary behavioral deviations (`6a64b15`). This
finishes the stationary **verifier**, not stationary root construction or
existence. A negative table must be excluded against this complete cap system
before it can honestly be called a nonstationarity stress test.

Beyond stationary repair, cycles must be sought in certified continuation
space. Each block carries \((w,\beta)\) and the five-scalar prefix summary, and
adjacent blocks must satisfy exact prescribed-value compatibility plus the
max-affine cap inequality. Playerwise opponent contraction, or one explicit
exceptional-owner fallback, is still required. This “boundary-repair lasso”
is the finite object to search before passing to a proper-path/chattering
limit; player-label cycles and atomwise regret transfer are known-unsound
proxies.

Inside an already certified uniformly contracting graph-directed component,
periodic support codes now have periodic unique value lifts, and a common code
prefix of length \(n\) controls the current-value distance by \(q^nD\)
(`66d22b8`). This justifies periodic lassos as a dense verification skeleton
in such a component; it neither constructs the component nor covers neutral,
noncontracting, or vanishing-hazard boundaries.

## 1. Exact conjecture and the two payoff levels

For a finite player set \(I\), a quitting game has one active state. Each player
chooses `Continue` or `Quit`. If the nonempty set \(S\subseteq I\) quits, the
game enters an absorbing state with payoff \(r(S)\in\mathbb R^I\). In the
repository, the active-state payoff is zero.

The model is implemented in
[`QuittingGame.lean`](../../GameTheory/Concepts/Stochastic/QuittingGame.lean), and
the repository's exact general target is the deviation-cap constructor in
[`Uniform.lean`](../../GameTheory/Concepts/Stochastic/Uniform.lean#L207): for every
positive error, construct one behavior profile and one horizon threshold that
simultaneously

1. deliver a common payoff vector at every longer finite horizon; and
2. cap every unilateral behavioral deviation at every such horizon.

This constructor is exactly equivalent to the semantic uniform-equilibrium
payoff definition. It is not merely a sufficient strengthening.

There are nevertheless two logically distinct payoff levels:

### Terminal/asymptotic level

For each fixed profile, finite Cesàro payoffs converge to expected terminal
reward. This is formalized by
`tendsto_finiteAveragePayoff_quittingGame` in
[`QuittingAsymptotic.lean`](../../GameTheory/Concepts/Stochastic/QuittingAsymptotic.lean#L221).
A uniform finite-horizon equilibrium therefore induces a terminal-payoff
approximate equilibrium.

### Uniform finite-horizon level

The converse is not a consequence of pointwise convergence alone: pointwise
limits do not ordinarily produce one horizon threshold valid simultaneously
for all behavior deviations.  Quitting games nevertheless have a special
positive theorem.  Solan--Vieille (2001), Proposition 2.13 proves that a fixed
terminal \(\varepsilon\)-equilibrium is a common-horizon uniform
\(\varepsilon'\)-equilibrium for every strict
\(\varepsilon'>\varepsilon\).  Its proof obtains the common horizon by reducing
a unilateral behavior deviation to a randomized quit time and treating the
opponent-only absorbing and nonabsorbing tails separately.

This conclusion is now formalized for the repository's ordinary behavior
profiles by
`quittingGame_isUniformεEquilibrium_of_terminalNash_finite` in
[`QuittingTerminalUniformization.lean`](../../GameTheory/Concepts/Stochastic/QuittingTerminalUniformization.lean).
The Lean proof uses the equivalent live-mass bookkeeping directly. If the
deviator's singleton reward is nonnegative, the same deviation is compared to
its terminal payoff. If it is negative, the comparison deviation agrees up to
a cutoff and then always continues. Non-solo absorption is bounded by the
opponent-only live tail. The theorem assumes no absorption or nonabsorption
regime, and its horizon is common to all players and arbitrary behavioral
deviations.

The repository also retains the negative direction:
`quittingGame_not_exists_uniformEquilibriumPayoff_of_no_terminalNash` at
[`QuittingAsymptotic.lean`](../../GameTheory/Concepts/Stochastic/QuittingAsymptotic.lean#L235).
A fixed positive terminal exploitability gap rules out a uniform-equilibrium
payoff.  Conversely, Proposition 2.13 implies that failure of uniform
approximate existence forces failure of terminal approximate existence and
hence some positive terminal exploitability gap.  A direct late-horizon
obstruction remains a legitimate proof route, but it is no longer a logically
different failure mode at the existence level.

Compactness closes the payoff quantifier as well. From terminal
\(\varepsilon_k\)-equilibria with \(\varepsilon_k\downarrow0\), extract a
convergent subsequence of terminal payoff vectors.  Given a target accuracy,
choose one sufficiently accurate member, use Proposition 2.13 with a strict
error enlargement, and then use fixed-profile Cesàro convergence.  This yields
one fixed common-horizon uniform-equilibrium payoff. This is now formalized by
`quittingGame_exists_uniformEquilibriumPayoff_iff_terminalNash_all_errors` in
[`QuittingTerminalUniformPayoffSelection.lean`](../../GameTheory/Concepts/Stochastic/QuittingTerminalUniformPayoffSelection.lean),
landed at `daf2780` and publicly routed at `08f5dd1`. It does not fill the
general stochastic-game `sorry` in `Uniform.lean`; it proves the exact
existence equivalence only for finite quitting games.

## 2. External status

The literature cited in this section uses the standard
terminal/undiscounted \(\varepsilon\)-equilibrium notion.  The definitions are
not identical, but Proposition 2.13 makes their approximate-existence problems
equivalent for ordinary finite quitting-game behavior profiles.

The terminal/undiscounted problem remains open at four or more players. The
2024 absorption-path paper states explicitly that whether every quitting game
admits an \(\varepsilon\)-equilibrium for every positive \(\varepsilon\) is
open. Its main
contribution is a compactification of absorbing profiles by absorption mass and
a sequential-perfectness framework:

- Ashkenazi-Golan, Krasikov, Rainer, and Solan,
  [*Absorption Paths and Equilibria in Quitting Games*](https://link.springer.com/article/10.1007/s10107-022-01807-6),
  *Mathematical Programming* 203 (2024), 735--762.

The 2026 essential-APS paper also says that terminal equilibrium existence is
not known for at least four players. It characterizes only the payoff subset supported by
continuous-time Flesch absorption paths, where at most one player randomizes
at each mass time:

- Ashkenazi-Golan, Krasikov, Rainer, and Solan,
  [*The APS Approach for Undiscounted Quitting Games*](https://link.springer.com/article/10.1007/s00182-026-00982-6),
  *International Journal of Game Theory* (2026).

All multiplayer quitting games do have sunspot approximate equilibria in the
standard undiscounted/terminal-payoff sense used in that literature.  Because
the sunspot device enlarges the behavior model, the ordinary-profile proof of
Proposition 2.13 should not be silently imported into that model. The result
nevertheless identifies a central obstruction: public or external correlation
changes the product-implementation and credible-punishment problem.

- Solan and Solan,
  [*Quitting Games and Linear Complementarity Problems*](https://arxiv.org/abs/1707.02598).

The known two- and three-player terminal results therefore do not currently
extend to the first open case, (n=4).  For ordinary behavior profiles, that
terminal problem is now the same existence problem as the repository's
common-horizon uniform conjecture, and that equivalence is now formalized
against the repository definitions.

## 3. What is already formalized

| Layer | Current status | Research significance |
|---|---|---|
| Uniform solution concept | Complete except for the general existence constructor | Gives the exact quantitative target and prevents quantifier slippage |
| Quitting-game stochastic model | Complete | Lets a final result specialize directly to the library's behavior-strategy semantics |
| Terminal payoff and Cesàro convergence | Complete | Supplies the asymptotic semantics and the negative bridge |
| Absorbed starting states | Complete | Removes the trivial states from the conjecture |
| Exact root decomposition | Complete | Restores the off-path continuation value after all players continue |
| Arbitrary root-deviation bound | Complete | Reduces a full behavioral deviation to a one-stage continuation game |
| `Never` branch | Complete | Gives an exact criterion in terms of singleton quitting rewards |
| `First` branch, including arbitrary and near-sure supplied profiles | Complete through `c0fd129`, `a1e6f4a`, and `0e5109c` | Exact sure-root iff plus continuation-preserving error transfer from all-continue mass at most \(d^{|I|}\) to a sure quitter |
| Local-to-global fallback regression | Complete in direct-checked commits `1217074` and `e7730a1` | Formalizes the exact local root indifference, terminal regret one, and all-continue stationary fallback; this is the two-player regression, not Q107's three-player plateau counterexample |
| Stationary root extraction | Complete through `b60f08c` and routed at `2f7c709` | A stationary terminal \(\varepsilon\)-equilibrium induces an \(\varepsilon\)-Nash root in its own terminal continuation value; this is the finite stationary necessity kernel, not the four-regime compactness theorem |
| Pure-time extremality and finite Snell kernel | Complete in the finite-cutoff/product-weight form through `5d4650d`; stationary \(q<1\) selected-cap slice through `eb8b36d` | Every supplied own hazard is an exact convex combination of deterministic quit times and the cutoff-Never atom; the time-inhomogeneous infinite boundary remains a separate adapter |
| Exceptional opponent-clock telescope | Finite scalar/clock layer and exact finite prescribed/cap/gap plus residual-atom bounds landed through `58f6f37`; infinite nonnegative-solo tail selection remains | Question 115 supplies the exact own-never atom and survival-weighted closure statement |
| Corrected proper absorption paths | Mathematically specified and audited in Q107; not implemented | The plateau correction and proper endpoint convention are now fixed |
| Arbitrary-profile branch extraction / path necessity | Answered in Q107 modulo imported compactness/refinement lemmas; not formalized | Covers all four stationary regimes and the nonstationary localized-jump route to First |
| Path discretization and regret | Answered in Q107 at proof level; not formalized | Tail-relative cell errors control continuous flow, jumps, product errors, and accumulating tails without a survival lower bound |
| Terminal-to-uniform positive bridge and fixed-payoff selection | Complete through `54f3d9b`, `eb57312`, `daf2780`, and public routing at `08f5dd1` | The bound-free fixed-profile theorem matches Proposition 2.13 for finite quitting games; compact selection proves terminal approximate existence at every positive error iff a uniform equilibrium payoff exists |
| Explicit cyclic four-player discriminant | Positively answered in Question 116 and Lean-checked through `902797d` | The former \(A=1,C=3\) candidate has an exact stationary terminal Nash equilibrium, hence a uniform-equilibrium payoff, and is retired |
| Cyclic-family mechanism phase diagram | Hand-verified, not Lean | Rotating continuous / uniform-singleton / stationary rescues cover \(0<C<2A\), \(C=2A\), and \(C>2A\) |
| Exact local zero-hazard root fiber | Answered in Question 114; not Lean | Semialgebraic directional germs are exact locally; global chattering remains separate |
| Mixed-sign block-pair finite discriminant | Exact rational certificates through `ff5ff0f`; Review 23 audit | No stationary terminal Nash and no credible sure-First root; this separates those classes from the successful lasso |
| Block-pair ordinary AC path class | Hand-verified Baire/pair-sum obstruction in Review 23; not Lean | Excludes bounded complete singleton flow even with measurable chattering |
| Block-pair period-eleven product-jump class | Three exact external rational-interval roots through `909e5ef`; common one-parameter validity on \(|\theta|\le1/200\) at `b988da7`; exact phase-4 fan at `5e64336`; true return contractions at `a823e73`; exact 27-box/81-edge graph-directed full shift at `8e0d0c3`/`e1fe897`; repaired exact replay on the full-dimensional radius-\(10^{-12}\) payoff ball at `a656c9d`; conditional five-mask strict return grammar closed through `2dea62a`--`3cacc1a`, with zero remaining return families and common charge \(A-a\ge(1/50)(1-S)\); one-sided strict-interior support-3/9 paths excluded externally at `663ecef`; generic Lean consumers landed, concrete certificates remain external | Three pairwise payoff-distinct support sheets rescue the nominal table, and every infinite word over the three whole blocks has a compatible credible pullback path inside the local atlas. The strict nonperiodic 3/9 spine is closed, but the common charge is only a finite support-6 return theorem. A full lifted/boundary/atlas potential, projective zero-hazard/chattering limits, entry from the surrounding region, exhaustiveness outside the atlas, a value-only decoder, and canonical selection remain open |
| Perturbed block-pair discriminant | Exact external period-ten interval certificate at `1d22fd0` | The perturbation \(r_0(\{0\})=-189/100\) is rescued by \((7,7,14,14,8,10,9,13,13,7)\), with strict inactive gaps and opponent contraction. It has zero terminal exploitability and a uniform-equilibrium payoff, so it is retired as a counterexample. Its \(14\to8\to10\to9\) escape is the mandatory atlas-exhaustiveness regression |
| Finite Nash--Bellman debt and projective tails | Exact finite debt semantics, max optimization, antitonicity/calibration, two-player nonnecessity fence, and the zero-limit/positive-tail split are in Lean through `a97fe85`, `89164d1`, and `28df2d0` | This is now an exhaustive split for the zero-boundary exact-chain program. Vanishing debt closes the game; positive debt yields an exact-D projective tail with a summable opponent clock, not yet an equilibrium |
| Positive-debt provenance and marked boundary | Persistence, positive singleton reward, exact Continue-to-terminal-solo witness, \(D/q\le\pi\), and the linear-mass full-set packet are in Lean through `0ab9d31`; Q129's no-owner-transfer regression is in `4b9f10d` | Positive debt is strategically interpretable, but the full simultaneous quitter set cannot be singletonized and even unit atomwise regret need not create dynamic debt for the marked player |
| Certified relative-boundary reinsertion | Q131 independently audited and its exact/approximate scalar compiler is in Lean at `801095a`; terminal-to-uniform and payoff selection were already landed | A supplied tail splices with exact backward relative debt and a depth-free mismatch penalty. This closes the consumer only: allowing \(K=0\) is necessary and makes clear that the theorem does not produce a certificate |
| Exceptional summable-clock boundary | Q128/Q130 answered with corrections; not yet fully Lean | Divergent own clock closes positively. Fully summable clocks retain Never mass and allow vanishing-scale fence escape; a limiting barycenter or repeated owner label need not be sustainable/compatible |
| Global proper-path existence or obstruction | Open | This remains the four-player-and-beyond mathematical hinge |

### 3.1 Root continuation is a substantive advance

[`QuittingRootContinuation.lean`](../../GameTheory/Concepts/Stochastic/QuittingRootContinuation.lean)
proves the exact first-stage payoff decomposition and the key theorem
`quittingTerminalPayoff_update_rootThenContinuation_le` at line 376.

Suppose a scalar bounds every continuation deviation by player (i). Then any
complete behavioral deviation from a root/continuation splice is bounded by
the finite one-shot quitting game in which the all-continue outcome has that
continuation value. This is precisely the datum lost by assigning continuation
value zero to a sure terminal jump.

Consequences:

- the `First` branch can be stated using genuine continuation strategies, not
  a fictitious terminal payoff;
- an augmented terminal jump can carry a checkable credibility witness;
- local deviation inequalities can be separated into a root action inequality
  and an inductive continuation cap;
- the same lemma is a natural interface between absorption paths and the
  general deviation-cap constructor.

### 3.2 The `Never` branch is exact

[`QuittingSimpleBranches.lean`](../../GameTheory/Concepts/Stochastic/QuittingSimpleBranches.lean)
proves that the all-continue profile is a terminal
\(\varepsilon\)-equilibrium exactly when every player's singleton-quitter
payoff is at most \(\varepsilon\). Consequently, all-continue works for every positive
error exactly when

\[
r_i(\{i\})\le 0\qquad(i\in I).
\]

This branch landed in commit `edaaff1`. It closes one full component of the
desired quitting-game trichotomy, not merely an example.

### 3.3 The scheduling kernel has advanced

[`BoundedDiscrepancyCirculation.lean`](../../GameTheory/Concepts/Stochastic/BoundedDiscrepancyCirculation.lean)
now proves the exact finite rational equivalence between a
bounded-discrepancy infinite walk, an eventually periodic witness, a
zero-charge lasso, and a reachable connected zero-charge integer circulation.
The chain culminates at `20d3136`, including exact multiplicity realization
through the directed edge-token Euler construction.

This is relevant to absorption-path discretization: rational singleton-flow or
block-frequency data can potentially be compiled into a deterministic schedule
whose prefix occupation error remains bounded. It does **not** yet give a
causal policy under deviation-dependent histories, nor does it establish
strategic regret bounds.

Separately, Q108's binary selected-fiber gadget, two-context joint-packet
obstruction, and three-context every-proper-subset strengthening are now in
Lean through `fe0a481`, `ccff923`, `3269b70`, and `80d7cb2`. These are exact
abstract packet theorems. They have not been realized as the full strategic
correspondence of a quitting game and therefore do not refute a quitting-game
compiler or the root conjecture.

### 3.4 Debt and marked-tail formalization has reached the producer seam

The finite Nash--Bellman lane is now composed through its first exhaustive
split. Exact finite debt has unrestricted finite-deviation semantics; the
min-of-max objective is attained and antitone; vanishing optimized debt
compiles to a uniform payoff; and a positive infimum produces a projective
exact-D tail with a positive owner and summable opponent clock. The former
proposal that exact debt should always vanish is false even for two players,
and that counterexample is machine-checked at `a97fe85`.

Commits `4600601` and `0ab9d31` formalize the strategic provenance of the positive
branch. Positive debt propagates to every later edge, forces a positive solo
reward, is attained by the explicit Continue-through-prefix/terminal-solo
deviation, and forces a full-set advantage atom whose raw mass is bounded
linearly below by the root debt. The common-subsequence packaging of that
terminal packet remains to be landed.

The older player-marked transfer machinery remains useful but is not a
compiler. Q124 showed that repeated player names need not be temporal state
recurrence. Q129 now shows something stronger: an actual active or inactive
joiner with a profitable boundary comparison need not inherit any dynamic
debt, because simultaneous atoms cancel in its own Bellman equation; the
two-player regression is machine-checked at `4b9f10d`. Q130
adds a vanishing-scale, fully summable escape that survives strict-time owner
repetition. Therefore an induction over player labels, even augmented by
actual marks, is incomplete unless it also transports compatible values,
relative deviation caps, and nonvanishing scale.

Q131 supplies the exact endpoint for such a transport. Once an actual tail
and its relative cap are supplied, finite-prefix reinsertion is exact and an
approximate value match costs at most the mismatch itself, independently of
prefix length. This removes semantic splicing from the list of unknowns. It
does not construct the tail; with a length-zero prefix, the certified branch
is exactly the terminal-equilibrium existence statement one is trying to
prove. The synthesis seam is now the relative-boundary producer, not another
finite debt estimate.

For the perturbed block-pair table, the external exact checkers
`2dea62a`--`3cacc1a` now close all six finite strict support-6 return families
inside the conditional five-mask core and give the common charge

\[
A-a\ge\frac1{50}(1-S).
\]

This is a finite return certificate, not a potential on the full lifted
relation. The separate exact checker at `663ecef` excludes every one-sided
strict-interior nonperiodic path confined to supports 3 and 9: a positive
hazard grows geometrically along self-blocks and \(9\to3^+\to9\) returns.
Thus no strict 3/9 spine remains *inside that atlas*. Commit `1d22fd0` proves
that the atlas is not exhaustive: the same perturbed table has an exact
contracting period-ten terminal Nash cycle with support word

\[
(7,7,14,14,8,10,9,13,13,7),
\]

escaping through \(14\to8\to10\to9\). Its largest certified inactive upper
bound is below \(-0.115635705\), and every opponent-cycle survival is below
\(0.119784300\). The cyclic compiler gives zero terminal exploitability and a
uniform-equilibrium payoff. The perturbation is therefore retired as a
counterexample candidate; the conditional rank survives only as an
atlas-exhaustiveness regression.

## 4. The absorption-path endpoint defect

The published absorption-path definition permits a jump that reaches total
absorption mass one, but its printed discrete sequential-perfectness condition
tests only jumps whose **post-jump** mass is strictly below one. A sure terminal
jump can therefore evade the local Nash test.

Testing every terminal jump against continuation value zero is not a valid
repair. A first-stage equilibrium may rely on punishment after the off-path
event that the designated quitter instead continues. The continuation is not
represented by the residual on-path payoff after sure absorption.

The exact audit, including minimal sanity examples, is in
`ephemeral/reviews/Review07-AbsorptionPathTerminalJumpConvention.md`.
No proof plan should cite the printed path equivalence without repairing this
endpoint.  This defect is distinct from Q107's posed plateau transcription:
the published (A.2) correctly removes (S(\pi)\cup T(\pi)), while the launched
question omitted (S(\pi)) and was therefore false as stated.

There are two viable corrected objects:

1. **Proper nonterminal paths.** Require every path jump to leave positive
   survival probability. Treat `Never` and `First` as separate branches.
2. **Augmented terminal paths.** Permit a terminal jump only together with a
   credible continuation payoff and a strategy/deviation-cap witness for the
   off-path all-continue outcome.

Q107 proves the first route at the mathematical level: Never, credible First,
or a standard-proper sequentially perfect path is equivalent to terminal
approximate equilibrium existence.  The augmented object may still be useful
compositionally, but it is no longer required to state the quitting-game
existence hinge.

## 5. The missing proof chain

### 5.1 Exact `First` theorem

This supplied-profile theorem is now exact and landed in
[`QuittingFirstBranch.lean`](../../GameTheory/Concepts/Stochastic/QuittingFirstBranch.lean)
at `c0fd129`. If a root product law has a sure quitter, then its splice with a
continuation profile is a terminal \(\varepsilon\)-equilibrium exactly when
the root law is an \(\varepsilon\)-Nash action in the one-stage continuation
game whose all-continue coordinate is the playerwise continuation
best-response supremum. The theorem proves both directions and does not assume
that the suprema are attained.

For a completely arbitrary behavior profile, take its time-zero marginals and
shift the profile after the unique all-continue root action. Before absorption,
these are the only live histories. `QuittingFirstStageAdapter.lean` now proves
the exact prescribed and every-unilateral-deviation payoff identities and
uses them to classify arbitrary sure-first profiles at `a1e6f4a`. Behavior
after an already absorbed history is correctly discarded as payoff-irrelevant.

This small adapter is distinct from the limiting near-sure regime. The finite
profile transfer is now also landed at `0e5109c`: if the supplied root's actual
all-continue mass is at most \(d^{|I|}\), forcing a selected near-sure quitter
to quit surely and retaining the shifted continuation raises terminal regret
by at most \(4Md\). The canonical unique live history and its probability are
now exposed at `00c6c73`. What remains is the compactness theorem that extracts
such roots from a normalized terminal jump.

### 5.2 Necessity of the proper-path branch

**Mathematical status after Q107:** answered and adversarially audited, with
only finite kernels formalized. The two-player local-to-global regression is
machine-checked in `1217074`/`e7730a1`, the unique live-history/mass and its
recurrence are machine-checked through `00c6c73`/`467ccc5`, and stationary
root necessity is routed at `2f7c709`. The absorption-path
compactness/extraction theorem itself is not formalized. The following list is
therefore a decomposition of the remaining formalization, not an open request
for the theorem's statement.

Assume terminal \(\varepsilon_k\)-equilibria exist with
\(\varepsilon_k\downarrow0\), while `Never` and `First` fail. A correct
compactness argument must cover every limiting regime of stationary one-stage
absorption probabilities \(p_k\):

1. \(p_k=0\) on a subsequence, which should force `Never`;
2. \(p_k\to1\), which should force `First` after a quantified near-sure-to-sure
   perturbation and a continuation-optimality argument;
3. \(p_k\to p\in(0,1)\), which should yield a genuine nonterminal jump;
4. \(p_k>0\) and \(p_k\to0\), which should yield continuous singleton flow,
   not `Never`.

The fourth regime is especially easy to lose by taking strategy profiles in
the ordinary product topology: infinitesimal quitting can converge pointwise
to all-continue while retaining a nontrivial absorption distribution.

For nonstationary profiles, a limiting terminal jump must likewise be converted
into a credible `First` witness or excluded. The proof cannot derive that
credibility from the terminal residual payoff alone.

Q107 supplies the needed localized-jump argument: sequential compactness gives
\(t_k\to t<1\) with

\[
\widehat\pi^k_{t_k}
=t_k+(1-t_k)p_k\longrightarrow1,
\]

so \(p_k\to1\). The landed `0e5109c` transfer then consumes the finite root
once the corresponding shifted profile is available.  Formalization still
needs the full absorption-path compactness theorem and the refinement
trichotomy that produces subgame-perfect tails or a stationary fallback.

### 5.3 Sufficiency: compile a proper path into strategies

**Mathematical status after Q107:** answered with a tail-relative compiler,
not formalized.  The obligations below identify the kernel that should be
encoded rather than a conjectural existence statement.

For a proper sequentially perfect path \(\pi\), construct behavior profiles
\(\sigma^k\) by discretizing absorption mass. At every reached survival history,
the compiler must approximate the path's residual continuation payoff
uniformly:

\[
d_k=
\sup_n
\left\|
\gamma_{s_n^k}(\pi^{\sigma^k})-
\gamma_{s_n^k}(\pi)
\right\|_\infty
\longrightarrow0.
\]

It must then prove a cellwise regret estimate of the form

\[
\operatorname{regret}_{n,k}
\le C_{I,M}(d_k+\omega_k),
\qquad \omega_k\to0,
\]

uniformly over:

- genuine product-action jumps;
- continuous singleton flow;
- cells mixing continuous flow with small jumps;
- unintended multiple-quitter outcomes created by simultaneous product mixing;
- countably many jumps accumulating at mass one.

Pointwise properness does not provide a uniform positive lower bound on
surviving mass. Any proof that divides by survival probability must explicitly
control the terminal tail.

The full theorem-or-counterexample specification is
[Question 107](../../questions/old/Question107-ProperAbsorptionPathBridge.md).

### 5.4 Uniformization

After obtaining terminal equilibrium inequalities, apply Solan--Vieille
(2001), Proposition 2.13. If \(\sigma\) is a terminal
\(\varepsilon\)-equilibrium, then for every strict
\(\varepsilon'>\varepsilon\) there is one horizon threshold such that the same
\(\sigma\) is an \(\varepsilon'\)-equilibrium for every longer finite average,
simultaneously against all unilateral behavior deviations.

The proof is not pointwise convergence in disguise. The formal proof tracks
the unique live history, opponent-only survival, and absorption outside the
deviator's singleton. For a nonnegative singleton reward, the same deviation's
finite payoff is bounded by its terminal payoff plus a Cesàro opponent-tail
error. For a negative singleton reward, a cutoff deviation agrees up to the
cutoff and then always continues; its prefix cost is \(O(K/N)\), and both
post-cutoff errors are bounded by the opponent-only live tail. This covers the
almost-sure and positive-nonabsorption regimes without assuming either one.

The generic one-sided transfer interface and its strict-margin equilibrium
theorem are landed at `333d9c5`. The quitting-specific approximation and
strict-margin transfer are landed at `54f3d9b`; `eb57312` discharges the reward
bound automatically from finiteness. The compact target selector and the exact
terminal-existence/uniform-payoff equivalence are landed at `daf2780`. A false
shortcut would be to assert uniform absolute convergence of every deviating
payoff: a deviation scheduled to quit after the current horizon can have a
nonzero terminal payoff and zero finite-horizon payoff.  Only the equilibrium
regret comparison is uniform.

For a fixed target payoff, choose terminal
\(\varepsilon_k\)-equilibria with convergent payoffs, reserve a strict error
margin, apply Proposition 2.13, and use fixed-profile Cesàro convergence for
delivery. `QuittingTerminalUniformPayoffSelection.lean` now checks this
quantifier argument. This result is independent of, and does not formalize,
Q107's path compactness, branch extraction, or product-cell compiler.

### 5.5 Global existence or global barrier

Even a perfect path compiler does not show that a path exists. The final
mathematical step must be one of:

- prove that every quitting game outside `Never` and `First` has a proper or
  augmented sequentially perfect absorption path; or
- give a finite quitting game and prove that `Never`, `First`, and every
  corrected path certificate all fail with one positive exploitability gap.

This is the conjecture-level hinge.

## 6. Large theorems that appear within reach

The following are substantial, useful results that the present repository is
plausibly positioned to prove without first solving the entire conjecture.

### Theorem A: root-splice terminal equilibrium compiler

**Landed through `c0fd129` and `a1e6f4a`.** The exact theorem constructs and characterizes a
terminal approximate equilibrium from:

- one root product action;
- one continuation profile;
- on-path continuation payoffs;
- credible playerwise deviation caps; and
- approximate Nash inequalities in the induced one-shot continuation game.

It proves both the constructive and converse directions for every supplied
sure-root/continuation splice. The later adapter proves exact prescribed and
unilateral payoff preservation from an arbitrary sure-first profile to its
root/shifted-continuation splice. The exact simple First branch is closed.

### Theorem B: exact simple-branch classification

**Landed.** The `Never` criterion, supplied-splice `First` iff, and arbitrary
sure-first adapter now classify the two simple exact branches. The quantified
near-sure \(p_k\to1\) extraction remains part of Theorem C: existing root
perturbation bounds do not themselves select a convergent sure quitter or
credible limiting continuation.

### Theorem C: corrected terminal-equilibrium trichotomy

Prove, or find the smallest counterexample to,

\[
\begin{aligned}
&\text{terminal }\varepsilon\text{-equilibria exist for every }\varepsilon>0
\\
&\quad\Longleftrightarrow\quad
\text{Never}\ \lor\ \text{credible First}\ \lor\
\text{proper sequentially perfect absorption path}.
\end{aligned}
\]

This is already publication-scale. It repairs a load-bearing endpoint issue,
separates all limiting stationary regimes, and gives the search program a
sound certificate language.

### Theorem D: bounded-complexity path compiler

First prove sufficiency for a restricted but expressive class:

- finitely many jumps bounded away from mass one;
- piecewise-constant singleton flow with rational rates;
- rational payoff data; and
- a uniform strict slack in local deviation inequalities.

The periodic bounded-discrepancy machinery should make this class especially
tractable. This theorem would validate the full compiler architecture before
addressing vanishing slack and countably accumulating jumps.

### Theorem E: SFAP essential-APS adapter

Formalize the 2026 essential APS operator for the Flesch-path subclass and
relate its greatest fixed point to the repository's local continuation game.
This would not solve the conjecture—the characterized set can be empty—but it
would give an exact positive island, computational experiments, and a common
language between the literature and the existing APS library.

### Theorem F: exact rational barrier certificate

For a supplied rational four-player payoff table and a supplied finite global
barrier/rank, prove mechanically that every allowed path step decreases the
rank or enters a uniformly exploitable region. Together with exclusion of the
simple branches and the existing terminal nonexistence bridge, this would
certify a negative solution.

The qualification “supplied global barrier” matters. There is no generic
completeness theorem saying that a finite semialgebraic barrier must exist.

## 7. Positive attack route

A credible affirmative architecture is:

```text
no Never / no credible First
        ↓
Q107 corrected proper-path extraction
        ↓
nonempty viable continuation-payoff set
        ↓
standard-proper sequentially perfect absorption path
        ↓
Q107 tail-relative product-cell discretization
        ↓
terminal approximate equilibrium or stationary fallback
        ↓
Solan--Vieille Proposition 2.13 + compact target selection
        ↓
uniform equilibrium payoff
```

The essential APS operator is relevant to the viability and path arrows. The
existing discounted APS machinery in
[`MonitoringSelfGeneration.lean`](../../GameTheory/Concepts/Repeated/MonitoringSelfGeneration.lean)
already contains the fixed-point/self-generation proof pattern, selector-built
public strategies, continuation decomposition, and one-shot-deviation logic.
It cannot be applied verbatim: the current theorems are discounted, while an
undiscounted quitting path uses absorption mass as the recursion parameter.

The main positive mathematical question is now how to produce a credible live
spine from a general payoff table. Q107's corrected path class remains one
route. The block-pair certificate supplies another concrete route: a finite
contracting product-jump lasso assembled from support-transition charts.
General paths allow both product jumps and continuous singleton flow, and the
new table proves that product jumps are not cosmetic: they can succeed after
every bounded complete ordinary singleton flow fails. What is missing is an
exhaustive construction or a chart-covering/trapping theorem, not another
fixed-profile verifier.

## 8. Negative attack route

One strong negative route has a demanding but reusable certificate burden. It
uses one finite, preferably rational, four-player payoff table and the
following exact chain:

1. exclude `Never` using the singleton-payoff criterion;
2. exclude every credible `First` profile, including all permissible off-path
   continuations;
3. exclude every proper or augmented sequentially perfect path;
4. obtain one fixed positive terminal exploitability gap, not merely
   nonexistence of an exact path;
5. invoke the formal terminal-to-uniform nonexistence bridge.

Step 3 contributes to step 4 only after the corrected simple/path classes have
been proved exhaustive. Otherwise it excludes a proposed certificate grammar,
not every behavior profile.

This terminal-gap route is equivalent at the existence level to a direct
target-free or targetwise arbitrarily-late finite-horizon obstruction.  For
example, one may prove one \(\delta>0\) such that for every behavior profile
and every horizon threshold, some later horizon admits a unilateral gain at
least \(\delta\). Such a theorem refutes the common-horizon solution directly;
Proposition 2.13 then implies that terminal approximate equilibria also fail,
so a positive terminal exploitability gap exists even if the direct proof did
not exhibit it first.

The natural experimental workflow is path-or-barrier CEGIS: alternate between
finding longer approximate paths and strengthening candidate separating
barriers. Neither failure of a bounded path grammar nor failure of a numerical
solver is evidence of nonexistence.

The preferred exact barrier now has a normal form. For every current-to-future
root edge

\[
w=g(x)+s(x)v,\qquad p(x)=1-s(x),
\]

seek a bounded potential \(\Phi\) and \(c>0\) with

\[
\Phi(w)-\Phi(v)\ge c\,p(x).
\tag{8.1}
\]

Telescoping gives a **uniform bound on every finite absorption clock**, not
merely the absence of one infinite proper path. This stronger quantifier is
necessary. A compact semialgebraic relation can have only finite-clock
individual paths while their finite clock budgets are unbounded; such an
accuracy-indexed family may be the positive branch. Thus the negative search
must distinguish:

1. a divergent proper path;
2. arbitrarily large finite proper clocks without a divergent limit; and
3. a uniform finite-clock ranking certificate.

A global rational affine \(\Phi\) should be tried first because its inequality
is polynomial and survives convexified zero-clock/chattering limits. A finite
piecewise-affine rank is the next language, but it needs exact chart-wall and
tangent coverage. ProofMiningReport item 76, Review 31, and Question 122 give
the full certificate and its falsification tests.

The strategic extraction from those budget regimes has now separated more
sharply. For a positive-density ergodic Bellman component with one exceptional
opponent clock, only the exceptional player can quit. The identity

\[
v-r(\{i\})=(1-x_i)(w-r(\{i\}))
\]

and equality of current/successor marginals force the entire component to the
singleton value \(r(\{i\})\). Any positive component hazard supplies one
common solo stationary root satisfying every inactive inequality. It is an
exact terminal equilibrium when \(r_i(\{i\})\ge0\); Never closes the case in
which all self-singletons are nonpositive.

The residual sign crossing,
\(r_i(\{i\})<0<r_j(\{j\})\), cannot be decided from that component. An exact
dummy-player graft leaves an arbitrary residual quitting table on the unused
cells while producing the same bad exceptional fixed edge. The negative
owner's finite-chain fence is nevertheless quantitatively visible after
deleting its own Quit action:

\[
\delta\le M\Pr(\text{some opponent eventually quits}).
\tag{8.2}
\]

The semantic form of (8.2) is Lean-checked at `740cbfb`. The finite
weighted-law core of the exceptional square-norm calculation is checked at
`c9f89e1`; it assumes the Bellman equation and equal squared-distance moments
and does not itself derive the ergodic component law or common stationary
hazard. The normalized first-opponent law has a hand-proved compact limit
retaining the full quitter set, its active support inequalities, and a negative
old-owner payoff moment. It is not invariant and not yet a path. The abstract
one-step weighted-packet dichotomy is Lean-checked at `e0c7c08`. The
first-opponent adapter and suffix re-rooting iteration remain hand-proved:
within at most \(|I|\)
transfers one reaches either a positive-mass boundary packet whose active
quitters are all above the negative threshold, or a repeated player name.
That name repeat is not recurrence of the payoff/chart state. Question 124
makes the next producer step explicit: extend the player-indexed
essential-APS/SCC architecture from
singleton modes to arbitrary product-jump hyperedges and zero-density
owner-deletion fences. A repeated player-name SCC is not enough; value
compatibility, product realization, playerwise clocks, and terminal debt are
the unproved lift.

The first rational perturbation separated two issues. At
\(r_0(\{0\})=-2+11/100\), commit 5c04bff exactly retains the Never,
stationary, and credible-First negative fences. However, commit 6f90dbd gives
five exact local Nash-predecessor edges whose normalized drifts have zero in
their positive convex hull. Therefore no **single global affine** potential
can rank the full local predecessor relation. The decisive composition test
is now positive: `1d22fd0` certifies an exact period-ten lasso using the
outside-atlas transition \(14\to8\to10\to9\). Thus the table is rescued and
retired as a counterexample candidate. The negative fences remain useful
strategy-class separations, and the five-edge affine obstruction remains a
warning that one global linear rank is too coarse.

A successful path barrier must be global for the exact
duration-one/path-successor relation and robust under arbitrarily many jumps.
It becomes a terminal or uniform nonexistence theorem only through an
exhaustiveness bridge or a direct all-profile late-horizon argument. Local
polynomial templates are useful search languages but are not complete.

## 9. Connections to the rest of the uniform-equilibrium effort

### 9.1 General deviation-cap waist

The final quitting-game theorem should target
`HasUniformDeviationCapConstructor`, not reprove the semantic equilibrium
assembly. This lets all quitting-specific work stop at on-path approximation
and uniform unilateral caps.

### 9.2 Adaptive and public-response recursion

The broad stochastic-game effort has compilers from completed adaptive/public
response systems to the uniform constructor. Quitting games collapse the state
recursion to a single live state, but do not eliminate continuation credibility.
The root-splice theorem is the quitting-specific one-node version of this
general recursion.

### 9.3 Product-image convexification

[`ProductImageConvexification.lean`](../../GameTheory/Concepts/Correlation/ProductImageConvexification.lean)
proves that the convex hull of outcomes generated by independent product laws
equals the correlated observation image. This identifies the correlation gap
precisely:

- convexified absorption flows may be easy to select;
- implementing one selected flow by one legal product action is a separate
  fiber problem;
- exact local equality permits replacement, but convex-hull equality alone
  does not choose a product point on the required fiber.

This is directly relevant to why sunspot equilibria exist while ordinary
equilibria remain open.

Q108 sharpens the quantifier fence. There are rational affine packet systems
in which every context separately has a product-realizable packet over every
target, and even every proper context subset is jointly realizable, while no
single packet realizes all contexts. The binary gadget, two-context
obstruction, and three-context proper-subset strengthening are formalized at
`fe0a481`, `ccff923`, and `3269b70`.

This is an abstract packet theorem, not a quitting-game or root
counterexample. The affine correspondence has not been derived as the exact
phase-lifted path/continuation correspondence of a quitting game, and no
theorem reduces every behavior profile to it. The useful next selector result
must exploit game-shaped balance and continuation structure or realize the
obstruction inside an actual game with the required strategic quantifiers.

### 9.4 Bounded discrepancy and FTV-style schedules

Continuous singleton absorption flow resembles a target occupation vector.
The landed offline equivalence in
[`BoundedDiscrepancyCirculation.lean`](../../GameTheory/Concepts/Stochastic/BoundedDiscrepancyCirculation.lean)
converts a reachable connected zero-charge integer circulation into an exact
closed walk and eventually periodic bounded-discrepancy schedule, and extracts
such a circulation from every bounded-discrepancy witness. The FTV cyclic
example demonstrates why temporal correlation can be strategically essential
even when no stationary profile works.

The missing connection is causal robustness: the schedule must remain a valid
deviation cap under the deviator's induced survival law, not only an offline
frequency realization.

### 9.5 Cesàro trigger and account machinery

The periodic Cesàro trigger files already turn bounded cumulative debt into
finite-horizon payoff bounds. A quitting-path compiler should therefore expose
its discretization error as a bounded or sublinear account. This is more likely
to integrate cleanly than a proof phrased only as convergence in distribution.

### 9.6 Single-controller and zero-sum results

The closed single-controller theorem validates much of the gain/bias,
occupation, and deviation-cap plumbing. It does not synthesize multiplayer
punishments. In a quitting game every player controls their own quit action,
so there is no single controller whose optimal policy resolves the strategic
compatibility problem.

## 10. Tempting shortcuts that do not solve the problem

- **Terminal continuation equals zero.** False off path; punishment after an
  attempted all-continue escape matters.
- **Pointwise Cesàro convergence gives uniform equilibrium.** False as a
  quantifier inference; the horizon must be common to all deviations.
- **The printed absorption-path equivalence can be imported unchanged.** The
  terminal-jump condition must first be repaired.
- **Stationary limits with quitting probability tending to zero are `Never`.**
  They may encode nontrivial continuous absorption flow.
- **Properness bounds all survival denominators away from zero.** It is only a
  pointwise condition.
- **Correlated or sunspot existence gives an ordinary profile.** It supplies
  precisely the correlation that ordinary independent play must manufacture.
- **Convexification supplies product realization.** It supplies a convex hull,
  not a point on an arbitrary selected fiber.
- **A bounded path search that finds nothing proves nonexistence.** Path
  complexity is not known to have a uniform finite bound.
- **A generic semialgebraic barrier is complete.** No such effective
  completeness theorem is available for the exact hybrid path relation.

## 11. Recommended research order

The operative order after E48 and the Q132 audit is:

1. **Keep the supplied-root stationary verifier closed and use it as a
   gate.** This is complete at `6a64b15`: every supplied stationary product
   root, including degenerate faces, is characterized by exact cap
   inequalities against arbitrary behavioral deviations. Do not infer
   nonstationarity from failure of a narrower grammar; `bc86435` is the
   permanent regression.
2. **Formalize Q132's behavioral nonattainment/nonclosedness theorem.** Land
   only the stopping-law bridge actually needed by the two-player table. This
   protects every compactness, closure, and separation argument used by the
   producer.
3. **Extend, rather than restate, the two-ended extraction.** `e2d5170`
   already retains the forward exact-debt ray, reverse terminal-face ray, same
   positive owner, and a quantitative packet selected at reverse depth one.
   `9334ab4` separately lower-bounds the finite preterminal survival and final
   marked-action mass, so the off-by-one bookkeeping is closed. The bridge
   theorem must additionally retain their common-subsequence limits, the
   opponent scale, the preselected full-set atom and transported cylinder
   mass, and calibrated-prefix provenance as distinct fields. The terminal
   factor must not be folded into the prefix clock.
4. **Attack the actual relative-boundary producer.** On the augmented compact
   exact-debt state, prove a bounded packet-anchored repair or a uniform
   decrease of optimized debt. Q132 supplies finite consumers and shows why a
   fixed decrease would close the plateau branch; it does not supply the
   extension theorem.
5. **Run the negative program in parallel.** Use the full-rate stationary
   verifier, credible-First criteria, and sound periodic/path compilers to
   screen four-player tables. A negative certificate counts only after its
   behavior/path class is exhaustive; failure of one atlas or one repair
   grammar is not a conjecture refutation.

The following work packages remain useful, but they are a retained secondary
backlog rather than an override of the P0 order above.

### 11.1 Retained secondary work packages

1. **Land source-faithful definitions only with a consumer.** Avoid a broad
   path API before its invariants are exercised. Either introduce the minimal
   published \(S\cup T\) plateau/proper-jump structure together with the first
   theorem that consumes it, or begin with the concrete stationary-regime and
   localized-jump lemmas that determine the eventual interface.
2. **Formalize Q107 necessity.** Land the four stationary regimes, the
   refinement trichotomy, absorption-path compactness, localized terminal
   jumps, and the `0e5109c` transfer to credible First.
3. **Formalize Q107 sufficiency.** Start with the exact countable cell
   partition, tail-relative residual bound, support routing, and the 2001
   stationary-fallback theorem.  A finite-jump strict-slack subclass is useful
   only if it shortens the route to this full theorem.
4. **Formalize the block-pair period-eleven rescue, then resume the global
   discriminant.** The periodic compiler, Banach/Krawczyk bridge, and exact
   31-polynomial external checker are landed. Evaluate the canonical rational
   witness from `044a3cb` in Lean using the dyadic export at `fccb7c9`,
   reconstruct its cyclic values, and discharge the concrete endpoint packet;
   do not replace the root by its decimal center. Then reuse the adapter for
   the other two roots.
   In parallel, Reviews 28--30 and Questions 119--121 isolate the
   basin/coverage problem and the transferable lasso-sheet theorem
   for the exact rational/quadratic support fan. The exact 27-box memory-three
   atlas now realizes all 81 transitions among the three whole block words;
   formalize a graph-directed pullback/Bellman consumer and its concrete
   invocation. Then prove entry from a surrounding admissible region, or an
   exact compatible escape/progress measure. Do not inflate the local full
   shift into global coverage, an injective payoff code, or a general
   existence theorem. The conditional five-mask strict-return grammar has
   zero unresolved families and a common \(1/50\) return charge, and the
   one-sided strict-interior 3/9 spine is excluded through `663ecef`; however,
   `1d22fd0` proves the atlas nonexhaustive by the exact
   \(14\to8\to10\to9\) period-ten rescue. Preserve this as a regression and do
   not pursue a global negative certificate for the retired perturbation. The
   fixed-word analytic continuation is now proved
   mathematically; formalize it only with its strict strategic conditions.
   Keep production separate and use the
   accuracy-indexed target: does the infimum over all periods and periodic
   product hazards vanish, with Never tails retained? Do not require one exact
   root or universal playerwise contraction. The fully opponent-absorbing
   prefix-closing case is available. For the at-most-one exceptional opponent
   clock, Q107's all-tail hypothesis now yields a stationary fallback with
   exact \(\beta+4M\eta_t\) error (or a credible First tail); formalize this
   theorem without pretending that designated-phase optimality supplies its
   late-tail inequalities or that First is automatically periodic.
   Then search other tables for a viable corrected path or an exact global
   barrier. Q107 makes that broader search game-theoretically
   decisive at the mathematical level. A positive result for one four-player
   table does not settle all four-player games or larger player sets, whereas
   one exhaustive four-player barrier would refute the universal conjecture.
5. **In parallel mathematically, adapt essential APS to SFAPs.** Use it as a
   positive island and as a source of candidate viability sets, not as a claim
   of full coverage.

Their internal dependency still matters. Without the corrected bridge, a path
search and a barrier search do not have a sound game-theoretic interpretation.

## 12. What would count as genuine resolution

### Affirmative resolution

An affirmative proof must construct, for every finite payoff table, one payoff
vector and profiles satisfying the repository's common-horizon deviation-cap
constructor.  Mathematically, it is enough to prove terminal approximate
existence: Proposition 2.13 plus compact payoff selection supplies the fixed
common-horizon payoff. That conversion is now repository-complete for finite
quitting games; the unresolved task is terminal approximate existence itself.

### Negative resolution

A fixed-terminal-gap proof needs one explicit finite game and one positive
\(\varepsilon_0\) such that every behavior profile has a terminal deviation
gain at least \(\varepsilon_0\). The existing formal bridge then rules out
every uniform-equilibrium payoff.

That is an existence-level normal form by Proposition 2.13.  A direct
targetwise or target-free arbitrarily-late finite-horizon obstruction with the
full all-profile quantifiers is an equally valid proof route and implies that
some terminal gap exists. Merely showing that no exact equilibrium, no
stationary equilibrium, no SFAP, or no bounded-complexity path exists is
insufficient for either route.

### Decisive intermediate resolution

The immediate decisive checkpoint is the first concrete period-eleven theorem:
evaluate its exact rational witness in Lean and connect it to the already
landed root, cyclic Nash, and uniform-payoff consumers. Reusing the adapter for
the other two roots then proves a machine-checked non-singleton periodic payoff
correspondence for one table. The broader decisive resolution is still
geometric/dynamical production: either formalize Q107's full corrected path
route, prove entry into the landed local graph-directed atlas (or an exact
escape) for a genuine chart class, or find a globally exhaustive barrier.

## Conclusion

The project has reached a sharper transition point. Quitting games are no
longer merely a motivating special case of the broad uniform-equilibrium
program: exact terminal semantics, simple branches, continuation-preserving
near-sure transfer, the corrected proper-path bridge, and the
terminal-to-common-horizon theorem now form a coherent mathematical chain.
The full terminal-to-uniform and compact fixed-target steps, arbitrary
behavioral-to-pure-time reduction, cyclic credibility compiler, uniform-payoff
corollary, and generic Banach/Krawczyk root consumer are machine-checked. The
concrete K11 interval evaluations and general Q107 path theorem are not. The
new exact dynamic-debt discharge and projective-tail extraction are also
machine-checked, but their hypotheses do not yet compose into an equilibrium
profile. The conditional five-mask core has no remaining finite strict return
family and has a common \(1/50\) return charge; moreover, `663ecef` excludes
every one-sided strict-interior nonperiodic path confined to supports 3 and 9.
But `1d22fd0` now certifies the exact outside-atlas period-ten rescue
\(14\to8\to10\to9\). Atlas exhaustiveness is therefore false, not open, and
the perturbed table is no longer a negative target. Its conditional ranks
remain valuable regression tests for any future exhaustive construction.

The next formal advance should finish the concrete K11 adapter and instantiate
it on all three witnesses. The next mathematical advance remains two-pronged:
formalize Q107 without weakening its quantifiers—including the all-tail
exceptional stationary fallback—while testing the surrounding support region
for entry into the exact local full shift or a compatible escape. The
designated-phase exceptional problem and the conversion of credible First
tails to periodic products remain separate rather than silently inherited.
The unresolved core is now:

\[
\boxed{
\begin{array}{c}
\text{Outside Never and credible First, does every finite quitting game}\\
\text{admit a credible proper live spine—periodic, hybrid, or limiting—}\\
\text{or is there a global barrier for some finite player set?}\\
\text{Four players is the first open and highest-priority test.}
\end{array}
}
\]

At present, that alternative is open. The terminal/uniform bridge is in Lean;
the corrected path normal form remains only partially formalized, and the
decisive global argument is absent. No reduction from all larger player sets
to the four-player case is currently available.
