# FTV as a Question 56 Response Architecture — Verified Analysis

Dated analysis record, 2026-08-02. The Flesch–Thuijsman–Vrieze cyclic
equilibrium encoded as a finite closed response architecture in the
sense of Question 56, with all four conditions verified exactly. This
is the acceptance test for the credibility bridge (Question 56 criterion
→ enforcement ledger), performed at the mathematical level; the Lean
criterion direction is committed at `24b5bf7`, while this actual-game
instantiation remains pending.

## The architecture

Game: `quittingGame r` on three players (the in-tree quitting-game
construction fits exactly; quit actions B/R/F), with
r{1}=(1,3,0), r{2}=(0,1,3), r{3}=(3,0,1), r{1,2}=(1,0,1),
r{1,3}=(0,1,1), r{2,3}=(1,1,0), r{1,2,3}=(0,0,0); live entry pays 0.

Configurations: 3 live phases z1,z2,z3 plus 7 absorbed children c_S
(10 total); initial z1 with target v=(1,2,1). Phase k: only player k
randomizes (half/half), targets v1=(1,2,1), v2=(1,1,2), v3=(2,1,1);
children carry their complete vectors r S. Transitions: clock advance
on live, child on absorption; the transition map never inspects the
action profile. The period-3 clock is a public account of finite
range 3 — inside Question 56's stated class, no generalization needed.

## Condition verdicts (all exact rationals)

- (T0) target harmonicity: EQUALITY at all 10 configurations
  (e.g. half*A + half*v2 = (1,2,1) = v1).
- (Ti) unilateral charges nonneg: CONFIRMED; exactly one strictly
  charged pair per player (charge 3/2), each player charged at the
  phase where its cyclic predecessor is active.
- (N) neutral-occupation test: CONFIRMED with max = 0, two routes:
  (a) occupation — every player's live-cycle retention product is 1/4,
  so live occupations vanish (the LP shadow of the verified
  per-block-survival <= 1/4); (b) pointwise — all 66 surpluses
  g_i - u_i <= 0, six binding zeros (the quit actions of the two
  local target-1 players).
- (P) prescribed delivery: CONFIRMED with equality (prescribed
  recurrent classes are the children, where g = u; live configs
  transient; the all-stationary reading also collapses by the 1/8
  balance).

## The mechanism (the thing to generalize)

Per live configuration, three positions: the ACTIVE player
(target coordinate 1) is indifferent — both actions pay exactly the
target, zero-cost enforcement; the PREDECESSOR (coordinate 1) is
neutral-but-absorbing — quitting earns exactly the target and absorbs,
which is where (N) bites; the SUCCESSOR (coordinate 2) is deterred by
COLLISION — its rent is paid by the active player's quit, and its own
quit forfeits exactly that rent (charge 3/2).

**The conditions determine the data.** Support-neutrality (prescribed
mixing forces every support action neutral) pins u_k(z_k) = 1 and
u_k(z_{k+1}) = 1; (T0) alone forces the sum 4 at every live config;
together these force the targets to be exactly v1, v2, v3; and (T0) at
the rich coordinate forces the mixing probability 1/2. The
architecture is DERIVED from (T0)+(Ti), not merely certified.

**Exact rigidity boundary (Q97).** Question 97 now proves, within the stated
uniformly absorbing cyclic quitting-architecture class, that one or two live
phases cannot deliver the named FTV target and that a three-phase witness is
the half-quitting cycle, unique at the named node up to the stated cyclic
normalization. This is a checked mathematical theorem, not yet a Lean theorem,
and it is not a uniqueness claim among arbitrary public controllers. The
earlier structured grid, 1.5M random draws, and 200k perturbations are retained
only as regression evidence; they no longer carry the rigidity claim.

Q97 also separates the approximate interfaces. Supportwise residuals are
qualitatively stable after fixing a support pattern and treating simultaneous
boundary degeneracies. Ordinary probability-weighted local regret is not: a
slow-absorption family has vanishing local residual while unilateral
exploitability tends to \(2/5\). No quantitative stability rate is credited.

**Two reusable lemmas for the general theorem:** support-neutrality
(fully general), and uniform-escape (live-cycle retention < 1 for
every player + children delivering exact targets ⇒ (N) is free).

## Statement fixes for Question 56 (recorded in-file there)

1. (22) should read one normal mode per (baseline mode x clock phase)
   — Q_normal is a finite cover of the state set, not a copy. FTV: 3
   normal modes over 1 live state.
2. (P) is degenerate for absorbing games (all recurrent content in
   children); the absorbing-case delivery constant is exactly
   phi-minus at the entry, not merely bounded.
3. The analytic-germ route of Q56 §6 provably cannot produce this
   architecture: the unique discounted branch endpoint (1,1,1) misses
   every architecture target by a full unit in the sum functional —
   FTV is a quantitative witness for Q56's own opening caveat.
4. §5 (detectors), §6 (Puiseux transport), §7 (epochs) are untested by
   this instance — FTV needs no monitoring (conclusive instant
   detection); the validation covers the occupation-LP core only.

## Sharp constants (improving the Question 87 certificate)

Explicit Farkas witnesses: positive potentials identically 0 (the
positive residual budget is EXACTLY zero — the surplus table is
pointwise <= 0); negative potentials phi-minus =
(9/7,11/7,8/7)/(8/7,9/7,11/7)/(11/7,8/7,9/7) on the live configs, 0 on
children, satisfying the delivery identity with exact equality. Hence:
deviation gain <= (11/7)/N, so N0(eps) = ceil(11/(7 eps)) — versus the
Q87 certificate's 24/eps — and the unbounded running-deficit potential
is replaced by a BOUNDED configuration-measurable one (norm <= 11/7).
Cross-checked by exact finite-horizon DP for N <= 15 (tight for
players 1 and 3; 2N - 1/2 for player 2). The alpha-family boundary of
the uniform set is exactly the (Ti) inequality d3(z0,F) = 1 - alpha
>= 0, tight at alpha = 1.

## Lean instantiation plan (next actual-data step)

Use `quittingGame r` directly (no bespoke game; the eight-cell match
is verified); Config := Fin 3 ⊕ {S // S.Nonempty}; the transition
discharges its public-state condition by rfl. Do NOT route through the
phase-lifted calculus (the clock lives in Config). Sequencing per the
module snapshot: the architecture structure and the four condition
definitions are the clean part; repair the configAt/phaseProfile
plumbing and the four expectedTarget rewrites first; the Farkas
existence block is bypassed by the explicit witnesses above and can be
repaired later. Feeding the explicit witnesses to the module's generic
bound reproduces Q87's constant 24; replacing 2*configBound by osc in
the two telescope lemmas recovers the sharp 11/7.

## Question-95 interpretation and formal status

Q95 identifies this architecture as a zero-cost gain--bias equilibrium, not a
costly punishment. The active player and one inactive player are dynamically
indifferent; the remaining inactive player is strictly deterred. Equations
(T0) and (Ti) encode the continuation-gain tier, while (N) is the
neutral-occupation test on the binding tier. In the quitting-game presentation
these
are exactly the promise and complementarity equations (Q1)--(Q5), with the
live-cycle escape probability giving the geometric absorption tail.

The mathematics recorded here is an actual-data adapter on paper. It does not
yet earn the Lean adapter seal: no theorem currently constructs this ten-node
architecture in Lean and feeds its four verified conditions to the generic
ledger producer. Question 97 has independently checked that (Q1)--(Q5) are
necessary and sufficient on its uniformly absorbing cyclic domain and has
supplied the exact minimum/rigidity theorem there. Neither result is a general
architecture-synthesis theorem, and neither has yet been formalized in Lean.
