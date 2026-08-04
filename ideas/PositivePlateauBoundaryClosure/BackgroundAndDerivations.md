# Positive-plateau boundary closure

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `MIXED` |
| Objective priority | `P0` |
| Last audited | 2026-08-03, through E50 and the production finite-chain `QuittingBoundaryHolonomy` interface |
| Central live claim | Every fully summable positive plateau of optimized exact zero-boundary quitting chains yields an executable accuracy-indexed repair, retaining the full terminal-packet anchor, within the zero-pinned exact-`D` grammar. The bounded exact chain-extension descent alternative is closed — no bounded-length extension achieves a cutoff-independent debt decrement (see [`AnchoredRepairOrUniformDebtDescent.md`](AnchoredRepairOrUniformDebtDescent.md)) — and the plateau itself is manufactured by pinning the terminal continuation to zero, not shown to be intrinsic to the game. |
| Next discriminant | Prove or refute closedness of the *realized* anchored-holonomy correspondence under unbounded middle length, then decode its limiting seam or exit as repair within the zero-pinned grammar — root-debt descent is closed ([`AnchoredRepairOrUniformDebtDescent.md`](AnchoredRepairOrUniformDebtDescent.md)). The scalar coefficient envelope is now compact, but scalar projection deliberately forgets the source roots and does not prove realized closedness. |
| Production destination | Finite-quitting terminal-equilibrium existence, followed by terminal-to-uniform payoff selection. |
| Supersedes / superseded by | Consolidates the positive-plateau lane of Q132 and proof-mining §79; no successor. |

## Claim ledger

| ID | Exact claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- | --- |
| PB1 | Finite exact zero-boundary Nash--Bellman chain sets are compact; optimized aggregate debt is attained and nonincreasing in the cutoff; chain-plus-Never exploitability is its exact initial dynamic debt. | `PROVED` | `M+L+A` | Finite quitting games and exact finite chains. | Positive-plateau split. |
| PB2 | If optimized finite-chain debt tends to zero, terminal approximate equilibria exist at every accuracy. | `PROVED` | `M+L+C` | Finite quitting games. | Terminal-to-uniform payoff selection. |
| PB3 | A positive optimized-debt limit yields a fixed positive-solo debt owner and a projective exact-D forward path with summable opponent-only clock; divergence of the owner's own clock closes by an exact terminal equilibrium, leaving the fully summable branch. | `PROVED` | `M+L+A` | The owner is selected from calibrated minimizers. | PB4 and PB7. |
| PB4 | Positive root debt yields a nonempty full simultaneous opponent set \(T_*\) with positive owner joining loss and transported raw mass bounded below linearly in the debt. | `PROVED` | `M+L+A` | The survival product stops immediately before the marked terminal root. | Anchored boundary relation. |
| PB5 | One common diagonal subsequence retains all fixed forward windows, fixed reverse windows, \((i_*,T_*,\omega)\), and every bridge-survival product with its exact factorization. | `PROVED` | `M+X` | E50 Lean-checks the common forward/reverse exact-D rays, terminal face, positive reverse depth-one debt, and a newly selected limiting packet. It does not yet package the preselected finite mark or bridge-survival coordinates, so `X` covers only that stated subclaim. | Anchored boundary relation. |
| PB6 | Cutoff-one, direct First, owner-solo, two-player pair, arbitrary stationary-product, sure-set/owner, contracting periodic, and finite max-affine prefix certificates have exact all-behavior cap criteria or compilers at their stated scopes. | `PROVED` | `M+L` | Verification of supplied finite data; the list is not complete. | R1/R2 repair verification. |
| PB7 | Positive plateau plus the fully summable branch implies, at every accuracy, an explicit finite repair, an attainable-tail intersection after a positive calibrated prefix, or a standard-proper sequentially perfect absorption path. | `OPEN` | `I` | PPBC; at least as strong as the unresolved finite-quitting existence step. | Terminal approximate existence. |
| PB8 | For fixed accuracy there are \(L,c,m_0\), independent of the large cutoff, such that either PB7 produces a repair or every calibrated minimizer admits an exact zero-boundary extension of length \(L\) lowering total initial debt by \(c>0\). | `OPEN` | `I` | Must construct new exact Nash roots and preserve the original entry and terminal boundary. The descent disjunct is refuted as a general mechanism by an explicit witness ([`AnchoredRepairOrUniformDebtDescent.md`](AnchoredRepairOrUniformDebtDescent.md)); this claim's live content is whether PB7's repair disjunct holds for every such family. | PB7 by plateau contradiction. |
| PB9 | If the fixed-\((L,c)\) alternative in PB8 holds, its descent branch contradicts convergence to the positive plateau. | `PROVED` | `M` | Fixed \(c>0\); a merely positive scale-dependent decrement is insufficient. | PB8-to-PB7 implication. |
| PB10 | The displayed standard-proper path axioms have been matched to a complete path-to-profile proof including the negative-solo Never fallback. | `CONDITIONAL` | `I+M` | The literature theorem has exact hypotheses; Q132 contains only a citation-dependent sketch and no checked adapter. | R3 compiler. |
| PB11 | Attainable terminal payoff--exact-cap pairs form a closed set, so relaxed closure intersection or ordinary separation produces an executable tail. | `WRONG` | `M` | Refuted by an exact two-player behavioral-nonattainment example. | Prevents a false R2 compactness proof. |
| PB12 | Failure of owner-solo and every owner-hazard/sure-opponent-set profile forces a nonstationary or cyclic repair. | `WRONG` | `M+L+C` | A three-player table excludes that grammar and all direct pure First sets but has a different exact mixed stationary equilibrium. | Prevents invalid escalation to lassos. |
| PB13 | In two players, the terminal packet and universal owner-solo obstruction yield an accuracy-indexed pair repair with \(O(p)\) exploitability. | `PROVED` | `M+L+C` | Exactly two players. | Closes the two-player escalation. |
| PB14 | Terminal approximate equilibria at every positive error are equivalent, at the existence level, to a uniform-equilibrium payoff in a finite quitting game. | `PROVED` | `M+L+C` | All finite quitting games. | Final semantic consumer of PB7. |
| PB15 | The packet lower bound controls the owner's opponent clock over the whole finite chain, including the marked final root. | `WRONG` | `M` | The preterminal survival product excludes the final root, whose opponent-Continue mass may be zero. | Correct state design for PB5/PB8. |
| PB16 | Every nonempty block of a selected finite min-max chain has one compositional multiplayer boundary holonomy with exact playerwise `(B,P)` and `(A,T,χ)` semantics; its source retains exact-D entry/exit, all common product roots, calibrated minimizer provenance, owner, full marked action/quitter set, and separate preterminal-survival/final-atom factors. All scalar coordinates lie in one compact product box and fixed-word cap safety is two affine inequalities per player. | `PROVED` | `M+L` | `QuittingBoundaryHolonomy`. Compactness is for the coefficient envelope; the subset realized by arbitrary-length finite blocks is not proved closed, and the provenance-carrying wrapper is not asserted compact. | Finite-middle bridge producer. |

## Falsifiers and wrong turns

- **Closed attainable-tail shortcut:** false by PB11. A relaxed minimizer may
  have zero cap gap without any behavior profile attaining it.
- **Whole-chain clock shortcut:** false by PB15. The correct retained datum is
  \[
  \left(
    \prod_{t=0}^{K_m-2}c_{i_*}(x_m^t),
    p_{m,-i_*}^{K_m-1}(T_*)
  \right),
  \]
  not one opponent-survival product through the final root.
- **Length-zero or arbitrary-tail repair:** tautological. R2 requires a
  positive prefix from a supplied calibrated minimizing chain and an actual
  tail profile with its exact cap.
- **Projective-boundary substitution:** the surviving Bellman boundary
  \(L\) need not be attainable or close to an equilibrium payoff.
- **Debt-owner transfer:** a joining or leaving defect for another player
  does not transfer dynamic debt. The owner, full terminal set, action date,
  raw mass, and relative comparison are distinct data.
- **Exact-only repair:** false as a universal demand. Stationary
  exploitability may tend to zero while no exact stationary equilibrium
  exists.
- **Small-hazard sure-set completeness:** false. A repair may occur at a
  positive or full-rate endpoint, so all \(p\in(0,1]\) need exact cap tests.
- **Static-grammar failure implies lasso:** false by PB12. Search all
  stationary product roots before declaring nonstationarity necessary.
- **Finite atlas or bounded-period failure implies nonexistence:** false.
  Accuracy-indexed unbounded periods, continuous flow, and arbitrary
  behavioral profiles remain.
- **Ordinary chain recurrence supplies one exact seam:** false. Multiple
  pseudo-edge errors require a closing theorem, and a downstream exact return
  may discard the calibrated anchor.
- **Compact scalar holonomy is a compact repair relation:** not established.
  PB16 puts the five playerwise coefficients in a fixed compact box, but the
  forgetful map drops the full chronological root word. Retaining the actual
  selected chain restores splice admissibility and provenance at finite
  length, at the cost of an unbounded-length witness whose realized image is
  not known to be closed. A subsequential scalar limit is therefore not yet
  an executable finite block or an anchor-persistent bridge.
- **Pointwise debt decrease gives fixed descent:** false in general. If
  \(S_K\downarrow s_\infty\), a one-step decrement \(c_m\) contradicts the
  plateau only when
  \[
  c_m>S_{K_m}-s_\infty,
  \]
  or finitely accumulated decrements exceed the remaining plateau gap.
- **Local Bellman perfection is global credibility:** false when a deviator
  can remove absorption forever. Every compiler must close each
  noncontracting opponent clock, including the negative-solo Never branch.
- A table satisfying the positive plateau and fully summable provenance for
  which every anchored relation loses closedness, seriality, or a uniform
  decoder would refute PB8 as stated without itself refuting equilibrium
  existence.
- An all-profile terminal exploitability gap would refute PB7 and the
  quitting-game existence conjecture. Failure of selected prefixes or
  certificate grammars would not.

## Production map

    exact zero-boundary chain factory + optimizer                         [L]
            |
            v
    zero debt ----------------> terminal approximate profiles             [L]
            |                              |
            | positive plateau             v
            v                    terminal-to-uniform selection             [L+C]
    positive projective exact-D owner and clock split                     [L]
            |
            +---- owner clock diverges --> exact terminal equilibrium      [L]
            |
            v
    fully summable forward boundary + full terminal packet                [L]
            |
            v
    common forward/reverse extraction with bridge products                [M]
            |
            v
    actual finite middle -> compact five-scalar holonomy envelope          [L]
            |
            v
    closed, serial, anchor-preserving exact-D relation                     [?]
            |
            +---- supplied finite/static/cyclic repair ------------------> [L verifiers]
            |
            +---- positive calibrated prefix + attainable tail ----------> [? adapter]
            |
            +---- standard-proper absorption path -----------------------> [CONDITIONAL]
            |
            +---- bounded exact extension with uniform root-debt drop ----> [?]
            |
            v
    terminal approximate existence at every accuracy                     [?]
            |
            v
    uniform-equilibrium payoff                                            [L consumer]

### Landed theorem families

- finite-chain topology, minimizers, monotonicity, calibration, and
  zero-debt compilation (`QuittingFiniteNashBellmanFactory`,
  `QuittingFiniteNashBellmanMinimizer`, and the
  `QuittingFiniteDynamicDebt*` modules);
- projective positive-debt tails, owner provenance, and the quantitative
  terminal packet (`QuittingPositiveDynamicDebtProvenance` and its imported
  positive-limit chain);
- cutoff-one safety and join-monotone closure;
- owner-solo certification and its universal joining obstruction
  (`QuittingOwnerSoloCertification`);
- two-player pair repair (`QuittingTwoPlayerPairRepair`);
- stationary best-response caps and full-rate sure-set/owner caps
  (`QuittingStationaryBestResponse`, `QuittingSureSetOwnerRepair`, and
  `QuittingFullRateStationaryVerifier`);
- certified-boundary reinsertion and max-affine acceptance geometry
  (`QuittingCertifiedBoundaryReinsertion` and
  `QuittingCertifiedBoundaryPolyhedron`);
- actual finite-chain multiplayer holonomy, compact coefficient envelope,
  exact arbitrary-behavior evaluation, and calibrated terminal-anchor
  provenance (`QuittingBoundaryHolonomy`);
- contracting periodic compilers; and
- terminal-to-uniform transfer and payoff selection
  (`QuittingTerminalUniformization` and
  `QuittingTerminalUniformPayoffSelection`).

### Missing production arrows

1. **Coupled extraction package.** PB5 is audited mathematics, and E50 checks
   its unscaled two-ray core plus the limiting terminal-edge packet. The
   corrected preterminal bridge products, preselected finite mark, and their
   exact factorization still need a production representation only when they
   feed the next arrow.
2. **Anchored relation.** `QuittingBoundaryHolonomy` now retains all actual
   roots, exact-D entry/exit, \(i_*,T_*,\omega\), the separated packet factors,
   and calibrated-minimizer provenance at each finite length, and its scalar
   image lies in a compact box. What is still missing is closedness of the
   *realized* arbitrary-length correspondence (or a strategically sound
   relaxation) together with plateau seriality. Compactness of the scalar
   envelope does not supply either fact.
3. **Decoder.** A downstream close seam must yield an actual cap-certified
   repair, and a buffered exit must lower debt measured at the original
   entry. Topology alone proves neither.
4. **Attainable-tail topology.** PB11 rules out ordinary Euclidean closure as
   an executable continuation space. A replacement must retain enough
   behavioral or stopping-law data to preserve payoff and every unilateral
   cap.
5. **Exact path adapter.** Before using R3, match the chosen absorption-path
   definitions and extended-Dini cases to the complete strategic compiler.

### Immediate production work

1. **Behavioral nonattainment/nonclosedness packet.** For
   \[
   r(\{1\})=(1,-1),\quad
   r(\{2\})=(-1,-1),\quad
   r(\{1,2\})=(-2,0),
   \]
   prove that no exact behavioral terminal Nash equilibrium exists, although
   stationary profiles have exploitability tending to zero. Existing
   live-spine and pure-time extremality results supply most of the reduction;
   the missing explicit bridge is the induced stopping-time law on
   \(\mathbb N\cup\{\infty\}\) and its exact-time atoms. This packet is the
   production falsifier for closed-attainable-tail arguments.
2. **Realized-holonomy closedness test.** The finite calibrated anchor now
   packages the preterminal survival scale and preselected marked terminal
   atom separately, and every actual middle block has compositional exact cap
   semantics. Determine whether limits in the compact coefficient envelope
   admit a closed support/root/provenance lift. If not, produce two calibrated
   chain families with the same limiting coefficients but incompatible splice
   data; if so, connect that lift to E50's two endpoint charts.
3. **Wire the landed full-rate static regression.** The exact table already
   excludes all owner/sure-set profiles by a uniform gap and closes through a
   different stationary product root. Keep
   `QuittingSureSetRepairFullIntervalCounterexample` and
   `QuittingFullRateStationaryVerifier` as regression consumers protecting
   the repair order from ansatz bias; this is no longer an open theorem.

## Exit conditions

- `MINED` when PB7/PB8 is proved with an actual semantic consumer, or PB8 is
  refuted and its strongest correct replacement and falsifier are extracted.
- `BLOCKED` only after repeated attempts reach the same precise prerequisite:
  no compact closed state can retain both the full packet scale and
  calibrated-prefix anchor. Name that missing compactification rather than
  saying only “chattering.”
- `PARKED` if another P0 route proves terminal approximate existence without
  consuming this boundary and the group retains no independent live theorem.
- PB7 becomes `WRONG` only on an explicit positive-plateau, fully summable
  table for which every R1--R3 output is rigorously excluded. That may refute
  this architecture without proving an all-profile gap.
- The quitting-game conjecture is refuted only by a uniform positive
  exploitability gap over every behavioral profile.
- `SUPERSEDED` only when another group owns both the relative-boundary object
  and the complete repair-or-descent consumer.

## Working notes

### 1. The exact exceptional input

The input is not an arbitrary quitting table. Optimized exact zero-boundary
chains have aggregate initial dynamic debt converging to a positive number.
Calibration selects one owner whose debt remains uniformly positive. Exact
debt recursion makes its opponents' survival product stay positive, so its
opponent-only clock is summable and its solo payoff is strictly positive.

If the owner's own clock diverges, prescribed play absorbs almost surely,
every other player's opponent clock contracts, and the owner's positive late
Quit endpoint closes the sole exceptional Never remainder. The unresolved
branch is fully summable: all hazards are summable, prescribed play has
positive Never mass, and its Bellman value contains a relative boundary term
which is not automatically attainable.

### 2. The two ends must remain coupled

The forward limit retains the positive-debt exact-D path rooted at the
original live history. The reverse limit retains the zero boundary and a full
simultaneous quitter set \(T_*\) with positive owner joining loss. Its
transported terminal-cylinder weight stays positive although its date tends
to infinity.

The common subsequence must retain raw bridge products between every fixed
forward and reverse depth. The preterminal product excludes the marked last
root; the final product-action atom is separate. Independently normalized
forward, reverse, and packet limits are insufficient.

Discarding a transient prefix to obtain downstream recurrence can lose the
owner, terminal set, scale, terminal distance, or minimizing-prefix status.
Anchor persistence is strategic data, not total boundedness.

### 3. What counts as a repair

A repair is executable data:

- a finite table certificate with exact arbitrary-behavior caps;
- an actual tail profile whose payoff--cap pair is accepted after a positive
  calibrated minimizing prefix; or
- a fully specified standard-proper absorption path with its strategic
  compiler.

Accuracy-indexed stationary or cyclic families are allowed. Free cap
variables, a length-zero prefix, an arbitrary already-known equilibrium, a
relaxed closure point, or a support word without chronological value/cap
compatibility are not repairs.

### 4. Behavioral nonclosedness

In the PB11 table, each behavior strategy is equivalent on the unique live
history to a stopping-time law on \(\mathbb N\cup\{\infty\}\). If player 1's
law is \(\alpha\), player 2's pure-time payoff is \(-1+\alpha_t\). A
countable probability law has a positive attained maximum and a finite
argmax, so equilibrium would force player 2 onto a finite argmax support.

If player 2 assigns positive mass to Never, player 1 improves by stopping
after that finite support. If it assigns no mass to Never, player 1 improves
from the largest supported time to the next time. Thus no exact behavioral
equilibrium exists. Yet an explicit stationary family has exact regrets
tending to zero, so its payoff--cap pairs converge to a zero-debt pair outside
the attainable set.

This kills closedness and exact attainment, not accuracy-indexed repair.

### 5. The quantified descent target

For each \(\varepsilon>0\), PB8 requires
\[
L=L(r,d_0,\varepsilon),\qquad
c=c(r,d_0,\varepsilon)>0,\qquad m_0,
\]
independent of the large cutoff. It must construct an exact chain of cutoff
\(K_m+L\), preserve the zero boundary, and satisfy
\[
\sum_iD_i^0(\mathcal C'_m)\le S_{K_m}(r)-c
\qquad(m\ge m_0).
\]

Both outer optimized debts converge to the same plateau, so this descent is
impossible. All content lies in constructing exact roots, preserving the
anchor, and obtaining a uniform \(c\); the final contradiction is elementary.

### 6. Objective research order

1. Test every cheap exact finite repair, including general stationary product
   roots rather than only owner/sure-set charts.
2. Define the smallest anchored exact-D state retaining the corrected
   two-ended data.
3. Prove closedness and anchor-preserving seriality, or produce a
   plateau-compatible chattering counterexample.
4. Decode a one-seam return as a certified continuation cycle, checking
   chronological payoff/cap compatibility and every opponent clock.
5. Decode a buffered exit as an exact bounded-length debt decrease at the
   original entry.
6. Only after finite decoding fails for a precise compactness reason, pass to
   a standard-proper path or a richer measure-valued boundary.

This order attacks the producer directly while keeping independent
formalization and falsification lanes active.
