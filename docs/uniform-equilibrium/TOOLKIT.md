# Uniform-equilibrium toolkit

This page organizes the production library by mathematical job.  It is a
stable entry map, not a progress report: current priorities and open work live
in [`PIPELINE.md`](PIPELINE.md), while [`FRONTIER.md`](FRONTIER.md) states the
current mathematical boundary.

The central distinction is between a **compiler**, which turns a supplied
certificate into a uniform payoff, and a **producer**, which constructs that
certificate from more primitive game data.  A verifier, compactness theorem,
or counterexample restriction is not silently counted as either one.

## Dependency shape

```text
game or analytic data
        |
        v
producer / selector -----> certificate or executable path
                                  |
                                  v
                         verifier / compiler
                                  |
                                  v
                   IsUniformEquilibriumPayoff

closure and transfer tools move proved results between nearby games or
payoff descriptions; diagnostics and no-go results constrain every branch
without producing a witness.
```

## Canonical public entry points

| Family | Canonical import | What it exports |
| --- | --- | --- |
| Uniform-payoff consequences | `UniformEquilibrium/Diagnostics/Uniform/Consequences.lean` | Semantic waist dependencies, target equivalence under vanishing payoff gaps, potential shaping, tail-width and bounded-work characterizations, and transition discontinuity. |
| Adaptive-potential systems | `UniformEquilibrium/Certificates/Adaptive/PotentialSystemTools.lean` | The single `AdaptivePotentialSystemAt` structure together with retargeting, profile transport, ledger conversion, finite-time bounds, and owner-separated assembly. |
| Quitting terminal selection | `UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean` | The equivalence between terminal approximate Nash existence at every accuracy and uniform-payoff existence for finite quitting games. |
| Diagonal target tails | `UniformEquilibrium/Quitting/Terminal/TargetTail/DiagonalTargetTail.lean` | Exact-prefix plus player-indexed closed-tail compilation and its counterexample restriction. |
| Support-retaining paths | `UniformEquilibrium/Quitting/Paths/SupportWitnessUniform.lean` | Infinite support-rational paths, finite periodic witnesses, and signed, absolute-weighted, and single-seam projective-lasso compilation. |
| Essential APS | `UniformEquilibrium/Quitting/EssentialAPS/All.lean` | The singleton-flow APS layer, including multivalued chronological execution under explicit segment closure, the adaptive-mesh capstone, and the formal fence separating invariant occupation cancellation from executable chronology. |
| Projective packets and lassos | `UniformEquilibrium/Quitting/Projective/LassoAll.lean` | Matching-order analytic packets, packet-target mismatch, resolved-chart/Farkas contracts, exact signed monodromy, finite charged return, forward-block single-seam closing, and lasso compilation. |
| Punishment-completed cycles | `UniformEquilibrium/Quitting/Punishment/CompletedCycle.lean` | Coupled phase-switch caps, exact instant-punishment characterization, and exact absorbing cycles completed coordinatewise by contraction or credible punishment. |
| Solved-cycle reward strata | `UniformEquilibrium/Quitting/Cycles/ExactCycleStrata.lean`, `UniformEquilibrium/Quitting/Cycles/OwnShiftCycleExactification.lean` | Raw versus behaviorally solved exact cycles, compilation and reward closure of solved strata, robust neighborhood exclusion for any counterexample, and the exact finite global feedback system for own-set reward perturbations. |
| Truncated-ledger boundary | `UniformEquilibrium/Quitting/Debt/Ledger/TruncatedLedgerCapBoundary.lean` | The sound package compiler interface together with one- and two-player counterexamples to treating it as a universal normal form. |
| Face circulations | `UniformEquilibrium/Quitting/Circulation/FaceCirculationAll.lean` | Certificate/orbit production, finite charged closing, the compatible compact-path route, concrete payoff examples, and boundary analyses. Use `MultiOwnerFaceCirculationFiniteClosing.lean` for the finite compiler. |
| Boundary holonomy | `UniformEquilibrium/Quitting/Boundary/Holonomy/All.lean` | Source-retaining fixed-cutoff compactness together with residual, self-similar, tangent, and realized-coordinate analysis. |
| Marked absorption paths | `UniformEquilibrium/Quitting/AbsorptionPath/All.lean` | Finite source-retaining and source-free cylinders; the compact metrizable joint-semantic completion with `Never`; bounded real holonomy, obstacle-cap, and continuous all-tail repair decoders; and correlated closed exact-seam relations and coherent associativity diagrams. |
| Reward closure | `Models/Quitting/UniformPayoffExistenceClosure.lean` | Fixed-skeleton quitting-game existence under uniform reward limits and dense solved approximants. |
| Nonexistence certificates | `UniformEquilibrium/Diagnostics/Uniform/NonexistenceCertificate.lean` | Late-horizon exploitability, quitting-terminal gaps, and the equivalence between finite-quitting nonexistence and some fixed positive terminal gap. |
| Combined quitting counterexample regime | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeAll.lean` | An exact normal form combining a positive terminal gap with finite canonical punishment-floor prefix capacity. It derives `η ≤ inf_N D_N ≤ D_N ≤ K ≤ M`, a global floor-admissible bounded potential and zero-charge recurrence, computable toggle/stationary ceilings, and the independent charge-side fact that every stable nonempty pure coalition would make prefix capacity infinite. It also supplies a supported packet with a table-uniform compact refusal margin and a summably absorbing exact-D tail converging to a positive-debt all-Continue self-loop. Every unaugmented tail value dominates the punishment floor, every finite segment reverses to a legal floor prefix with unchanged charge, and the tail is uniformly ballistic in absorption time. Dynamic debt has exact finite/infinite conservation and a logarithmic owner-clock ceiling; honest late-tail payoffs vanish while the positive prescribed plateau survives; augmented caps remain in the floor carrier; and a canonical periodic family is uniformly blocked with a fixed player and evaluator branch on infinitely many windows. Any hypothetical counterexample has a cardinal-minimal `Fin n` form with `n ≥ 4`. A product-root ballistic-return or terminal-realization theorem, compatible periodic attachment, and general augmented-cap realization remain open. |

Import an internal file directly when its narrower interface is the point of
the proof.  The umbrellas are navigation and downstream entry points, not a
ban on precise dependencies.

## Semantic waist and terminal bridge

`Uniform.lean` owns `StochasticGame.IsUniformEquilibriumPayoff` and
`HasUniformDeviationCapConstructor`.  Their exact equivalence is the
construction waist: a candidate mechanism is complete only after it supplies
the uniform finite-horizon delivery and unilateral-deviation bounds encoded by
that constructor.

For finite quitting games, the preferred higher-level waist is
`UniformEquilibrium/Quitting/Terminal/TargetTail/TerminalUniformPayoffSelection.lean`.  It selects one bounded target
from terminal approximate equilibria available at every positive accuracy and
then invokes the terminal-to-uniform bridge.  Terminal verification,
target selection, and uniformization remain separate steps in lower-level
proofs.

`UniformEquilibrium/Certificates/Adaptive/PotentialSystemTools.lean` is the transformation facade for the
proof-facing adaptive-potential waist. It deliberately reuses the one
`AdaptivePotentialSystemAt` definition: consolidation here means a canonical
API surface, not a second structure. Public stopping and response compilers
remain separate because they add causal-law realization and credibility
obligations.

## Positive construction families

| Family | Required input | Production output | Remaining nonclaim |
| --- | --- | --- | --- |
| Diagonal target tail | Accuracy-indexed exact Nash--Bellman prefixes with small joint survival and player-indexed target-closed tails | Terminal approximate equilibria and hence a uniform payoff | Does not construct the prefixes or prove their survival certificate. |
| Support witness | At every tolerance, a support-wise approximately optimal root path, divergent absorption, and continuation-by-continuation individual rationality; alternatively a finite periodic witness with one absorbing phase | A terminal `3ε` profile and target-free uniform-payoff existence | Does not produce the paths or cycles for arbitrary games. |
| Signed projective lasso | An accepted target and, at every tolerance, a finite root word whose signed survival-weighted monodromy is small relative to absorption for every cyclic entry phase, with support optimality and punishment rationality | Exact periodic correction, a divergent support-rational path, and a uniform payoff | Matching analytic packet extraction neither accepts its endpoint nor constructs the required physical candidate; absolute-weighted variation is only a stronger compatibility interface. |
| Finite charged forward packets | At every charge target, one exact finite forward Bellman packet in a fixed compact carrier, with support optimality and punishment rationality | Compact charged return, a single-seam lasso, and a uniform payoff | Does not produce the packets or consume the complementary bounded-charge branch. |
| Punishment-floor exact prefixes | An arbitrary finite quitting game and arbitrary finite exact Bellman prefixes in the canonical box starting above the behavioral punishment floor | Either a uniform payoff, or one common finite absorption-charge bound for every such prefix; on the global boxed floor-admissible exact-predecessor relation the latter is an exact finite budget with a canonical bounded potential | The potential is an accounting certificate, not a marked-cylinder realization, terminal repair, or prefix-consumption theorem. |
| Essential APS | A compact convex functional unique-live component with finite-window face avoidance, terminal-freeness, and bounds; or, for chronology alone, any owner carrier satisfying exact segment closure | A coherent executable path, qualitative deleted-player survival, adaptive finite meshes, and a uniform payoff for every initial component value in the compiler stratum | Algebraic APS invariance or a balanced occupation alone does not imply segment closure or select a chronological path; arbitrary-game component production remains open. |
| Multi-owner face circulation | A bounded balanced circulation with positive phase ratios, one common ratio ceiling below `1`, and a payoff floor above the quitting punishment value | Arbitrarily charged finite packets and a uniform payoff by finite closing; independently, a chronological compact path | Does not construct such a circulation for every game or identify the selected target with a named certificate vertex. |
| Punishment-completed finite cycle | An exact absorbing Nash--Bellman cycle where each coordinate either contracts in deleted survival or has punishment value at most its selected solo value | The selected phase value is a uniform-equilibrium payoff; the old nonnegative-solo admissible-cycle compiler is a corollary | Does not produce an exact cycle, and does not cover an isolated coordinate whose punishment value exceeds its negative solo value. |
| Dense solved-cycle strata | Arbitrarily close reward tables carrying absorbing, punishment-admissible exact finite cycles | A uniform-equilibrium payoff at the original reward table by fixed-skeleton reward closure | Density is not proved. For a fixed cycle, the landed own-set system is exact and playerwise after feedback elimination, but it is only an `|ι|`-dimensional perturbation family. |
| Two-player closure | An arbitrary finite two-player quitting game | Unconditional uniform-payoff existence | Does not extend the pair-repair classification to three or more players. |

The essential-APS and circulation families contain genuine producers relative
to their stated structured inputs.  They are conditional positive strata, not
generic quitting-game existence theorems.

## Reusable infrastructure

| Tool | Module | Use |
| --- | --- | --- |
| Discrete hazard stopping | `Math/Probability/DiscreteHazardStopping.lean`, `Math/Probability/SurvivalAmplification.lean` | Survival products, first-hit weights, stopped-payoff accounting, and the generic conversion of bounded positive gap amplification into survival lower bounds, division-free clock budgets, and summability. |
| Survival products | `Math/SurvivalProduct.lean` | Generic finite-product and cumulative-hazard estimates shared by stopping arguments. |
| Compact finite-prefix relations | `Math/Topology/CompactFinitePrefixRelation.lean` | Inverse-limit selection from compatible compact finite prefixes; used by circulation paths. |
| Finite charged return | `Math/FiniteChargedReturn.lean`, `Math/CompactFiniteChargedReturn.lean` | Converts sufficiently charged finite prefixes in one compact carrier into a close ordered block with fixed charge, without one orbit uniform in the target. |
| Charged-path budget, selection, and execution | `Math/ChargedPathBudget.lean`, `Math/ChargedPathSelection.lean`, `Math/ChargedPathExecution.lean`, `Math/ChargedPathFiniteHorizon.lean` | Separates finite-path capacity from charge on one infinite path, constructs divergence-preserving and renewal block selections, turns local progress into a finite terminal path or an infinite chronological edge stream, identifies a finite budget with the least bounded potential, and attains every finite-edge horizon maximum by a literal path. |
| Periodic-window and phantom-boundary evaluation | `UniformEquilibrium/Quitting/Cycles/PeriodicWindowEvaluation.lean`, `UniformEquilibrium/Quitting/Cycles/PhantomBoundaryRestart.lean`, `UniformEquilibrium/Quitting/Cycles/PeriodicNormalizedSeam.lean` | Reduces a full behavioral reply against periodic opponents to finitely many phase stops plus refusal/`Never`, identifies the exact surviving-boundary discrepancy, and computes both periodic attachment branches.  An exact Nash--Bellman word is controlled by endpoint drift normalized by the joint and opponent survival gaps; unnormalized recurrence is insufficient. |
| Global cycle exactification | `UniformEquilibrium/Quitting/Cycles/OwnShiftCycleExactification.lean` | Tracks continuation-value feedback from one common own-set reward shift, characterizes exact cyclic policy/Nash feasibility by a finite linear sign system, and on absorbing cycles uniquely eliminates phase corrections as probability-scale multipliers times one scalar shift per player. It does not establish feasibility or represent arbitrary coalition-dependent perturbations. |
| Summable-tail limit geometry | `UniformEquilibrium/Quitting/Cycles/PhantomBoundaryLimitGeometry.lean`, `UniformEquilibrium/Quitting/Terminal/TailCompression/SummableTailBestResponse.lean` | Produces one simultaneous annotation boundary with a `2 M` remaining-charge modulus, passes singleton lower bounds to it, pins every cofinally active owner to its singleton reward, and bounds the literal all-behavior suffix best response by the same charge scale. |
| Dynamic-debt cap seam | `UniformEquilibrium/Quitting/Debt/Dynamic/DynamicDebtCapBridge.lean` | Identifies the exact coordinatewise obstruction `quitProbability * currentDebt`; the displayed root transports the augmented cap iff this seam vanishes, and a zero-seam edge lifts to an exact Nash–Bellman edge between augmented-cap states. This is a local edge criterion, not a suffix realization theorem. |
| Periodic debt holonomy | `UniformEquilibrium/Quitting/Debt/Dynamic/PeriodicDebtHolonomy.lean` | A positive debt coordinate returning across a supplied exact-debt window forces every opponent-Continue factor to one; two distinct returning coordinates force the whole window to all-Continue, so an absorbing return has at most one. It does not produce a periodic closure from an arbitrary tail. |
| Packet defect algebra | `UniformEquilibrium/Quitting/Classification/SingletonPacketDefectAlgebra.lean` | Separates the two stabilized window branches: a pinned phase defect is underfunded, whereas a positive refusal defect is strictly funded and quantitatively forces positive owner mass; any remaining packet-clause failure in that branch is the punishment floor. |
| Singleton packet energy | `UniformEquilibrium/Quitting/Classification/SingletonPacketEnergy.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimePacketEnergy.lean` | Identifies weighted packet surplus and aggregate refusal gain with the quadratic solo-effect energy. The skew part vanishes; every counterexample packet supports a positive reciprocal-synergy pair. Pairwise nonpositive reciprocal solo effects form a solved class via the complementary singleton-mixture compiler. |
| Weighted collision concentration | `Math/PMFProduct/CollisionMass.lean`, `Math/Probability/WeightedCollisionConcentration.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/CollisionConcentration.lean` | Proves the product-law bound `collision ≤ choose(card,2) * absorption²`, propagates it through finite survival-weighted windows with an explicit zero-absorption branch, and bounds conditional delivery error relative to the normalized singleton mixture by `2 M choose(card,2) rho`. |
| Normalized finite-window occupation | `UniformEquilibrium/Quitting/AbsorptionPath/NormalizedFiniteWindowOccupation.lean` | Retains source roots, exact singleton/collision/absorption masses, zero-denominator branching, normalized owner occupation, and conditional delivery. Normalization by total absorption gives an `M × collision-share` delivery error without a positive singleton denominator; arbitrary windows escaping to infinity have vanishing conditional collision. Positive limiting owner mass supplies a literal active phase and pins the annotation boundary. |
| Counterexample-tail ballisticity | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeBallisticity.lean` | Combines all-date punishment rationality, exact restart accounting, compact normalized singleton occupation, collision concentration, and the uniform packet defect. It excludes endpoint drift little-o of absorbed mass and gives one eventual positive lower speed for every positive-absorption selected-tail window. This is not recurrence because the total absorption clock is finite. |
| Counterexample tangent packet | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeTangentPacket.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeTangentPacketEnergy.lean` | Uses the exact finite charge-tangent identity to extract a coherent normalized owner occupation, boundary, and signed endpoint tangent from the actual optimized tail. The tail is eventually all-Continue or yields a nonzero packet; every such packet has a negative coordinate or an active positive coordinate. After excluding negative coordinates, the active-positive packet is itself a normalized singleton-source packet and supports a positive reciprocal-synergy pair. Phase repair and simultaneous product-root selection remain separate consumers. |
| Tangent-to-projective LCP bridge | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeTangentAnchoredProjectiveLCP.lean` | Rebases any charge tangent packet at a positive cemetery weight as an exact anchored projective singleton packet. On active support the anchored LCP direction is the negative rescaled tangent, so active positivity gives a strict negative projective direction. This supplies first-event projective data but not the resolved chart or real/Puiseux feasible lift needed to construct simultaneous quit rates. |
| First-order tangent mixing dispatch | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeTangentMixingCompatibility.lean` | Collapses each positive-mass first-order mixing row to the weighted pair-join effect `sum_{j≠i} mass_j*(r_i({i,j})-r_i({i}))`. Incompatible rows expose a same-sign supported pair-join pivot and a finite sign separator. If all rows are compatible, collision-increment energy cancels singleton energy; active positivity then forces a supported pair with negative reciprocal collision increment. These are algebraic pivot directions, not product-root arcs. |
| Regular tangent arc interface | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeTangentRegularArcLift.lean` | Removes the common radial factor from the full Bellman and active-mixing equations under `hazard=t*leading`, `continuation=boundary+t*drift`, retaining all coalition terms. Surjective derivative plus an outward kernel direction would give a positive analytic equality arc, with strict physical signs decoding exact Nash--Bellman roots. For the literal compatible ungauged chart these premises are incompatible, so this is the consumer for a future gauged formulation rather than a current producer. |
| Tangent support transversality | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeTangentSupportTransversality.lean` | Compatibility gives `J*mass=0` for the reduced pair-join Jacobian and puts the nonzero projective scale direction in the full blow-up derivative kernel. Dimension then excludes simultaneous derivative surjectivity and positive-radial kernel motion. The outward branch has a finite left-costate certificate; on three active owners an explicit radial minor decides transverse/no-outward versus singular/outward. A projective gauge or radial-parameter lift remains necessary. |
| Tangent projective gauge | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeTangentProjectiveGauge.lean` | The affine normalization `sum leading=1` removes exactly the packet scale line and identifies gauged full zeros with ungauged full zeros on the slice. Because the gauged full system is square, the usable arc theorem takes a codimension-one reduced residual plus explicit local exact recovery; regularity then produces a full-zero analytic arc and exact Nash--Bellman roots. Constructing that reduced/recovery pair remains visible. |
| Projective-gauge scalar obstruction | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeTangentProjectiveGaugeDefect.lean`, `CounterexampleRegimeTangentProjectiveGaugeScalarClosure.lean`, `CounterexampleRegimeTangentProjectiveGaugeSecondJet.lean` | Deleting one mixing row is not locally recoverable. For three owners, a nonzero radial minor gives a fixed one-sided defect. In the zero-minor branch the exact affine-path second jet is `s²(Q+sC)`: nonzero `Q` or `C` is again fixed-sign, while `Q=C=0` makes the omitted scalar vanish identically on that path. Retained nonlinear rows and global realization remain separate. |
| Two-owner tangent support | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeTangentTwoOwnerSupport.lean`, `CounterexampleRegimeTangentTwoOwnerExactRoot.lean`, `CounterexampleRegimeTangentTwoOwnerPacketEdge.lean`, `CounterexampleRegimeTangentTwoOwnerPacketDichotomy.lean`, `CounterexampleRegimeTangentTwoOwnerApproxPunishment.lean` | Exact compatibility has a rational root manifold. Strict physical slack gives small positive-charge exact edges; otherwise a punishment boundary, inactive singleton row, or upper-box coordinate is tight. Active tight-floor deficit vanishes with scale and admits target-specific approximate punishment tails, but a common all-accuracy row would require attainment of the min--max infimum. Co-realized suffix and return remain open. |
| Period-one tangent atlas | `UniformEquilibrium/Quitting/Cycles/PeriodOneTangentAtlas.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimePeriodOneTangentReadout.lean` | Identifies the exact one-root joint/opponent survival split with normalized singleton-owner mass, then rewrites the phase and proper-mass refusal evaluators as signed endpoint-tangent terms with their finite strategic slacks retained. The canonical one-stage extraction supplies actual root-mass/tangent convergence and one-edge complementarity. On the active-positive branch the refusal slack is eventually zero and the diagnostic refusal gain converges to `mass/(1-mass)*tangent > 0`. Exact attachment to the actual suffix retains an additional opponent-survival boundary defect and a suffix-value realization premise; under explicit favorable versions of both, the diagnostic becomes a literal profitable deviation. Neither premise follows from the current infinite Nash--Bellman tail. |
| Fixed-prefix terminal repair floor | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimePeriodOneAttachmentRepair.lean` | A uniform terminal exploitability gap lower-bounds the behavioral-tail repair value after every positive finite prefix, with prescribed payoff and behavioral envelope co-realized by one actual suffix. Elementary tail compression preserves the obstruction up to arbitrary tolerance; behind each selected one-root prefix a canonical elementary cap retains exploitability above half the regime gap. This does not identify the deviator with the active tangent owner or realize a stored annotation. |
| Aggregate prefix-consumption gate | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeAggregatePrefixConsumption.lean` | Sandwiches the terminal gap below the canonical full-prefix behavioral repair value and that value below the minimum aggregate exact-`D` objective. At every cutoff a marked aggregate anchor therefore carries the gap with an explicit reward/cardinality packet-mass bound. Immediate `Never` exploitability is exactly maximum dynamic debt. A literal predecessor satisfies `residual ≤ jointContinue * oldDebt + |I| * M * charge`; hence charge pays the new seam, while surviving old debt is the exact remaining potential. A rational local regression in `CounterexampleRegimeAggregatePrefixResidualRegression.lean` shows that this carried term cannot be erased from an exact-Nash theorem. Sure caps and positive internal cutoffs still need boundary reinsertion. |
| Reachable carried-debt telescope and terminal funding screen | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeReachableCarryTelescope.lean`, `CounterexampleRegimeTerminalIncomingPathAlternative.lean`, `CounterexampleRegimeTerminalFundingFarkasDecoder.lean`, `CounterexampleRegimeTerminalFundingSupportNecessity.lean`, `CounterexampleRegimeTerminalFundingSupportEnlargement.lean` | Scaled remaining prefix capacity pays every seam and telescopes carried debt to the terminal singleton cap. The aggregate cap is at most `M`; in a counterexample it is positive and strictly below `|I|M`. The canonical one-owner funding root is nevertheless always Farkas because its owner has positive singleton reward. Any physical zero-target funding root must enlarge support and use a strictly negative collision payoff; compatible two-owner zero-pair-join support is insufficient. Nonpositive punishment alone need not make the cap zero. |
| State-preserving chronology capacity | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeCapacityNearMaximizerRebase.lean`, `CounterexampleRegimeStatePreservingChronologyCapacity.lean` | Supremizes charge over literal zero-boundary exact-`D` chains. A near-maximal chain has actual state-matched predecessor edges of arbitrarily small charge while retaining the terminal gap, with payoff drift, debt loss, and owner hazards uniformly bounded after charge normalization. Re-rooting or payoff rebasing can erase the debt. At zero absorption the exact equations leave the successor root arbitrary, so the compact limit may still be a positive-debt all-Continue phantom plateau rather than a strategic return. |
| Phantom-boundary conditioning and diffuse compilation | `UniformEquilibrium/Quitting/Cycles/PhantomBoundaryConditioning.lean`, `ConditionedProductPurification.lean`, `ConditionedSingletonStrategicPurification.lean`, `ConditionedTangentSeam.lean`, `ConditionedDiffuseChronology.lean`, `ConditionedDiffuseProductRescaling.lean`, `ConditionedDiffuseStrategicRescaling.lean`, `ConditionedDiffuseCompiler.lean`, `ConditionedDiffuseUniform.lean`, `ConditionedDeletedClockMonopoly.lean`, `ConditionedDeletedClockTerminalConcentration.lean`, `ConditionedDeletedClockSoloCompletion.lean`, `UniformEquilibrium/Quitting/Paths/HazardScaledResidualCompiler.lean`, `JointPolicySeparatedErrorCompiler.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeConditionedFloorViability.lean`, `CounterexampleRegimeConditionedSlackThreshold.lean`, `CounterexampleRegimeAtomicOwner.lean`, `CounterexampleRegimeConditionedDiffuseClosure.lean` | Conditions a positive-survival exact tail on eventual absorption without losing consecutive chronology. Singleton rows purify exactly; diffuse hazard rescaling approximates multi-owner conditional laws quadratically. Complete deleted clocks feed the two-clock compiler, while a deficient clock forces a unique rescaled owner and a punishment-completed solo equilibrium. Exact source Nash charges singleton-floor deficit to the deleted clock, eliminating that premise. Thus every singleton-tight diffuse branch compiles under singleton punishment rationality. A canonical diffuse counterexample has a strict phantom plateau player who is eventually literal `Never`; all late quitters lie on a proper singleton-tight face. Controlling those outsiders or enlarging support is the conditioned residual. |
| Eventual all-Continue plateau | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeEventualAllContinuePlateau.lean` | Two consecutive all-Continue roots force equality of complete exact-debt states, so this branch is eventually the constant extracted phantom boundary and literally delivers zero. Its selected owner has positive singleton reward at least the terminal gap. Every positive solo rate is strictly blocked; any exact endpoint-Nash root at the singleton target must include a second positive quitter. Finite blockers reduce to one universal joiner or two overlapping blockers. This forces support enlargement but does not solve the enlarged complementarity system. |
| Approximate punishment-completed cycles | `UniformEquilibrium/Quitting/Punishment/ApproximateCompletedCycle.lean` | Extends punishment completion to cycles whose contracting-coordinate root residual is charged against the deleted contraction gap, and to fixed-period families with vanishing error and convergent targets. For solo cycles, positive hazards with endpoint-Nash error and continuation error tending to zero compile the singleton payoff whenever the owner is punishment-rational; no positive lower hazard bound is needed. |
| Collision-aware and singleton finite-return compilers | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeCollisionAwareFiniteReturn.lean`, `UniformEquilibrium/Quitting/EssentialAPS/NashBellmanSingletonCycle.lean`, `CounterexampleRegimeDebtSourceStrategicDecoder.lean` | A supplied finite state-matched product-root return with full collision-aware affine delivery, exact Nash, and punishment admissibility is a solved exact cycle. On proper singleton roots, physical Nash--Bellman edges are essential-APS arcs, and a changing-owner viable cycle compiles without a separate punishment field. A simultaneous zero-debt-source face return is another exact solved-cycle interface. Counterexamples forbid these return words; current compactness and packet data do not construct them. |
| Common-word and circulation obstructions | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeCommonWordRealization.lean`, `CounterexampleRegimeTargetTailGluingObstruction.lean`, `CounterexampleRegimePreferenceLassoCirculationObstruction.lean` | Zero common repair is equivalent to arbitrarily accurate one-word elementary terminal Nash realization, but a counterexample's terminal gap forces this repair value positive after every prefix even though all player-indexed target-closed punishment tails exist. Thus separate punishment tails do not glue. The strict packet preference lasso also rules out using the whole packet mass as a singleton face-circulation phase; new phase weights and full-vector state matching are required. |
| Finite-window refusal reweighting | `UniformEquilibrium/Quitting/AbsorptionPath/FiniteWindowRefusalReweighting.lean` | Separates current-root deletion from the switch from joint to opponent-only chronology. It gives exact forced-Continue masses, zero-denominator semantics, raw triangular-factor error bounds, and a normalized error bound conditional on a positive joint-weighted deleted-absorption denominator. It does not prove the required scale ratio vanishes. |
| Outsider-`Never` gluing | `UniformEquilibrium/Quitting/Paths/OutsiderNeverGluing.lean` | Decomposes an outsider's original-coordinate Quit gain into its survived solo gap and a joining term, bounds the latter by `2 M` times insider absorption, and lifts the resulting `eta + 2 M delta` estimate from deterministic quit times to all behavioral deviations. The continuation and absorption estimates remain explicit hypotheses. |
| Boolean Möbius stage adapter | `GameTheory/Cooperative/CoalitionalGame/MultilinearExtension.lean`, `UniformEquilibrium/Quitting/Bellman/Finite/BooleanMobiusAdapter.lean` | Defines the generic multilinear extension, coordinate derivative, and singleton/pair/higher-order split of a coalitional game; then centers the quitting payoff cube at its continuation value and identifies product-root expectation and unilateral gain with those objects. It supplies no coefficient-sign or support-pivot theorem. |
| Frozen-root continuation lift | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeTangentSupportLiftFarkas.lean` | For one supplied product root and intended interior support, encodes the full Bellman, support-indifference, off-support Nash, punishment-floor, and payoff-box continuation problem as a finite homogeneous affine system with all collision and higher Möbius terms retained. Feasibility decodes an exact Nash--Bellman edge; infeasibility has explicit Farkas multipliers. Quit-rate selection remains a multiaffine problem, so the pointwise alternative is a search/duality interface rather than a support-enlargement theorem. |
| Finite phase occupation duality | `Math/Probability/PhaseOccupationDuality.lean` | Semantic/LP primal equivalence, bounded attainment, phase-bias decoding, and strong duality conditional on occupation feasibility. |
| Cyclic exposure | `Math/CyclicExposure.lean` | Sharp exposure bounds for finite permutation systems; the shared-punishment calculation is an application. |
| Nonperiodic Snell supersolution | `UniformEquilibrium/Quitting/Paths/InfinitePathSupersolution.lean` | Turns exact Continue transport, vanishing local Quit error, and survival decay into history-dependent unilateral caps. |
| Target-anchored stopping tail | `UniformEquilibrium/Quitting/Terminal/TargetTail/TargetAnchoredTail.lean` | Constructs one player's stationary-opponent closed tail at a prescribed target. |
| Joint-survival selection | `UniformEquilibrium/Quitting/Paths/JointSurvivalSelection.lean` | Identifies compactly selected continuation values with actual infinite-path terminal values under joint-survival decay. |
| Projective first-event algebra | `Math/ProjectiveBellmanPacket.lean` | Exact cemetery/absorption normalization and Bellman balance before any chart or recurrence argument. |
| Affine equality/Farkas alternative | `Math/AffineEqualityFarkas.lean` | A finite feasible-tangent-or-dual-row alternative; strategic decoding and arc lifting are separate inputs. |
| Graded survival transport | `Math/SurvivalWeightedObstruction.lean`, `Math/LinearProgramming/FlowCostateDuality.lean`, `Math/Probability/KilledTailPotential.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/SurvivalWeightedObstructionAdapter.lean`, `UniformEquilibrium/Quitting/AbsorptionPath/FlowCostateObstructionAdapter.lean` | Separates survival-grade-one raw charges from grade-zero endpoint coboundaries, transports finite co-states by the adjoint map, and folds killed scalar potentials while retaining the terminal boundary remainder. Literal adjacent quitting windows preserve both the generic block law and a sparse two-grade flow/co-state pairing exactly. A client must still supply a feasible strategic current, select a compatible co-state, and prove any boundary comparison used to eliminate dissipation. |
| Counterexample killed-capacity account | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeKilledTailPotential.lean`, `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeKilledCapacityPotential.lean` | Identifies exact dynamic debt as a killed reference and constructs a natural excessive account by scaling remaining canonical prefix capacity. Boundary dominance is equivalent to zero killed dissipation once initial values agree, but the capacity account has an explicit uncontrolled initial mismatch; the theorem therefore isolates rather than assumes the missing normalization. |
| Exact one-stage obstruction carrier | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeOneStageObstructionCarrier.lean` | Takes the compact graph of boxed exact dynamic-debt Nash–Bellman edges satisfying the punishment floor at both endpoints and maps it continuously to unnormalized two-grade obstruction flows. Every canonical one-stage tail flow belongs, and every finite co-state support is attained. Co-state selection, recurrence, exposed-face decoding, and strategic realization remain separate. |
| Playerwise debt-source obstruction carrier | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeDebtSourceObstructionCarrier.lean` | Enriches the exact compact one-stage carrier with the grade-one coordinate `quitProbability_i * dynamicDebt_i`. Consecutive exact edges fold this coordinate to current debt minus survival-weighted terminal debt. The negative coordinate selector exposes precisely the zero-source face, which on exact source edges is equivalent to playerwise augmented-cap transport; all coordinates vanish exactly when the vector cap transports. It does not prove that the canonical tail enters or returns to this face. |
| Debt-source dynamic alternative | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeDebtSourceDynamicAlternative.lean` | Rewrites finite and infinite dynamic-debt conservation as exact survival-priced co-state pairings. Locally, the canonical flow lies in the selected zero-source face now, lies there next, or the canonical killed-capacity account dissipates strictly. This dissipation is exactly growth of the survival-scaled debt/capacity boundary mismatch; nonexpansion at arbitrarily late starts forces zero-face recurrence. The counterexample regime does not supply that boundary comparison. |
| Boundary-provenance alternative | `UniformEquilibrium/Diagnostics/Quitting/CounterexampleRegimeBoundaryProvenanceAlternative.lean` | Formalizes why moving zero terminal boundaries can disappear under fixed-coordinate projective convergence, and strengthens the metrizable decoder to retain both exact-D anchors together with path and repair state. The decoder lacks the canonical capacity coordinate. On the actual tail, capacity dissipation is summable and the one-step boundary-mismatch excess tends to zero, but finite nonexpansion need not occur. |

Phase-occupation duality is optimization infrastructure.  Until a concrete
strategic construction supplies a feasible phase occupation, it is not itself
a game or strategy producer.

## Closure and transfer

- `Equilibrium/Uniform/AsymptoticPayoffEquivalence.lean` transfers an exact target across
  profile-uniform finite-average payoff gaps tending to zero.
- `Equilibrium/Uniform/ExpectedPotentialShaping.lean` applies that transfer to bounded
  expected-potential coboundaries with an `O(1/T)` endpoint telescope.
- `Equilibrium/Uniform/PayoffExistenceClosure.lean` proves target-free existence closure
  under uniform stage-payoff limits on a fixed finite skeleton.
- `Models/Quitting/UniformPayoffExistenceClosure.lean` specializes the closure theorem
  to uniformly convergent quitting reward tables.
- `Models/Quitting/RootPerturbation.lean` gives local one-coordinate payoff and regret
  bounds; it should not be confused with target-free closure.

These tools transport an existing mechanism or existence result.  They do not
supply density of solved games or construct a missing certificate.

## Boundary analysis and diagnostics

`UniformEquilibrium/Quitting/Boundary/Holonomy/All.lean` has two complementary
local compactness modes.  Fixed-cutoff and fixed-last lifts retain the actual
root block, endpoints, and provenance.  Tangent compactness retains only
bounded coefficient coordinates and normalized safety obstructions.
`UniformEquilibrium/Quitting/AbsorptionPath/All.lean` supplies the separate
escaping-length carrier: a compact metrizable closure of one joint semantic
encoding, with finite sequential density, `Never`, decoder-facing continuous
projections, and a correlated closed exact-seam relation.  Its bounded real
decoder agrees exactly with every finite holonomy and makes the all-tail repair
value and obstacle cap continuous on the completion.  Its marked-stage
hyperspace is an extensional graph rather than an ordered history, and its
coherent six-coordinate diagrams do not imply total seam lifting or
amalgamation of arbitrary independently selected splice witnesses.  The
strategic charged-replacement constructor therefore remains separate.  The
punishment-floor bounded potential and this marked completion are complementary
but not interchangeable: the former controls accumulated absorption on every
reachable exact-predecessor path, while the latter compactifies semantically
coherent calibrated cylinders.  A proved calibration/realization map is needed
before the potential can be used as a marked boundary observable.

The general reverse diagnostics are:

- arbitrarily thin eventual payoff/deviation intervals are equivalent to
  uniform-payoff existence;
- a fixed target is uniform exactly when it has a bounded excess-work
  certificate;
- positive tail width and late exploitability gaps give exact nonexistence
  witnesses;
- for finite quitting games, existence of some fixed positive terminal
  exploitability gap is exactly equivalent to nonexistence; and
- convergence of transition kernels alone does not preserve uniform-payoff
  targets.

`UniformEquilibrium/Quitting/Debt/Ledger/TruncatedLedgerCapCounterexample.lean` adds a certificate-specific
fence: even a solved two-player zero-solo game need not admit a common-cutoff
truncated-ledger package.  The package compiler is sound, but its hypothesis is
not a necessary normal form for equilibrium existence.

These characterize or falsify proposed routes.  They are not forward
construction mechanisms.

## Semantic fences

The following distinctions are load-bearing across the toolkit:

1. probabilistic stopped-law accounting is not strategic law realization;
2. a public response or detector is not a credible punishment certificate;
3. positive occupation circulation does not transport a continuation target
   without a separate harmonicity or target-identification theorem;
4. compact coefficient projections do not imply closedness of the set of
   realized strategic blocks;
5. terminal approximate Nash, fixed-profile uniform approximation, and a
   uniform-equilibrium payoff are different notions until a named bridge is
   invoked;
6. a fixed-target closure theorem and target-free existence closure solve
   different problems;
7. positive debt on one explicit legal chain is not positivity of the optimized
   minimum over all chains;
8. the general polynomial Bellman variety is not the physical
   vanishing-discount domain until an explicit slice such as `0 < disc ≤ 1` is
   imposed;
9. a neutral or subsingleton promotion socket—including a vacuous `CellFiber`
   instance—is not realization, compatibility, or an all-accuracy producer;
   and
10. a global occupation that cancels signed defects across different recurrent
    SCCs is not one legal path.  Future flow synthesis must choose one reachable
    recurrent component or prove a separate strategic common-randomization
    theorem.

## Open leaves

The two intentional conjecture leaves remain in
`UniformExistenceConjecture.lean` and `UniformEquilibrium/Quitting/Conjecture/Basic.lean`.  The former
truncated-ledger producer leaf was removed after a two-player counterexample;
its valid conditional compiler is indexed above.  Existing positive compilers
narrow what the two genuine leaves must produce, but do not discharge the
arbitrary-game producer.

For new work, first identify the row above whose required input is closest to
the available data.  If no row accepts it, record the missing adapter or
producer explicitly.  In particular, failed subgame reinsertion should preserve
the entering player or marked join inequality, and failed flow synthesis should
preserve the recurrent component and componentwise separator rather than
creating another parallel compiler surface.
