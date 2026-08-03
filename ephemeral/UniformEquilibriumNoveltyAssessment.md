# Provisional novelty assessment for the uniform-equilibrium program

**Dated:** 2026-08-03. **Mathematical checkpoint:** `14d75ff`.

This is an evidence-calibrated research assessment, not a publication or
priority authority. No exhaustive literature search has been performed. “New”
below means “no close antecedent found in the sources actually audited,” not a
claim of first discovery. Update the exact claim/literature record—not this
assessment alone—when prior art, a stronger proof, formalization, or a
refutation appears.

## Categories

- **Known/classical mathematics:** source-attributed theorem or standard
  machinery with clear antecedents.
- **Likely-new formal packaging/application:** abstract ingredients are known,
  but their exact Lean interface or stochastic-game specialization appears
  distinctive.
- **Plausibly substantive new mathematics:** a nontrivial theorem/fence with no
  close antecedent found; external comparison is still required.
- **Conjectural original idea:** precise mechanism or conjecture, not a result.
- **Formalization novelty:** apparent novelty as a proof-assistant artifact,
  separately from mathematical novelty.

`INDEPENDENT` in the idea venue is only a lifecycle resolution; it does not
mean novel or publishable.

## Assessment table

| Family | Abstract mathematics | Stochastic-game application / result | Formalization novelty | Confidence and reason |
| --- | --- | --- | --- | --- |
| Fixed public-response credibility | Finite average-reward gain/bias, Poisson equations, controlled Farkas alternatives, and telescoping are classical families. | The exact split-domain semantic-credibility iff finite gain--bias packet, owner-reachable arenas, enforcement ledger, and target-rigidity packaging are **likely-new formal application**; universality/producer claims are not made. See `PublicResponseCredibilityCriterion.lean` and [credible-target rigidity](../ideas/CredibleTargetRigidity/README.md). | **High** within the audited proof-assistant sample. | `medium` mathematical novelty; interfaces appear distinctive, but APS/self-generating-set and multichain average-reward literatures are close neighbors. |
| Quitting terminal-to-uniform bridge | Solan--Vieille Proposition 2.13 is known. Compact payoff selection and horizon uniformization use classical compactness/accounting. | The complete repository bridge and fixed-payoff selection are source-aligned/internal packaging, not a new existence theorem. [Claim](../ideas/QuittingGameConjecture/TerminalApproximateExistenceIffUniformPayoff.md). | **High**: no other formalization found. | `high` that the mathematics is known; `high` that the Lean packaging is novel within the checked sample. |
| Pure quit-time/Never reduction | Behavioral stopping laws as mixtures over deterministic stopping times plus infinity are standard optimal-stopping/probability ideas. | Exact preservation of quitting terminal payoffs and every unilateral behavioral deviation on the canonical live spine is **likely-new formal application**. | **High**. | `medium`; search optimal stopping, behavioral-strategy realization, Kuhn equivalence, and quitting-game best-response literature. |
| Optimized finite-chain debt split | Compact minimization and monotone cutoff limits are classical. | The exact Nash--Bellman debt objective, attained zero/positive split, projective exact-D tail, and semantic zero-branch consumer are **plausibly substantive new mathematics**. See [optimized-debt split](../ideas/QuittingGameConjecture/OptimizedDebtSplitIsExhaustive.md). | **High**. | `medium`; no source antecedent found, but absorption-path, LCP, and self-generation literatures may contain equivalent potentials under different language. |
| Exceptional owner/clock classification | Nonnegative-series domination and stopping telescopes are elementary/classical. | “All players close except possibly one owner with summable opponent clock and negative/positive solo boundary,” together with the exhaustive owner-own-hazard split, is **likely-new application** and may be substantive as a structural theorem. [Clock claim](../ideas/TailClockPatternExhaustion/OwnerHazardSplitExhaustsExceptionalClockPatterns.md). | **High**. | `medium`; compare quitting absorption paths, Snell envelopes, and recursive-game exceptional-player arguments. |
| Terminal packet and two-ended compactification | Diagonal compactness and reading finite paths from two ends are classical techniques. | Retaining one quantitative full terminal action packet at reverse depth one while the middle escapes is **plausibly substantive new mathematics/application**. [Two-ended claim](../ideas/CycleGeometryResolution/TwoEndedCompactificationRetainsPacketButLosesMiddle.md). | **High**. | `medium-high` for distinctiveness of the exact object; antecedents may exist in concentration-compactness, pointed Gromov/trajectory compactification, or absorption-path blow-ups. |
| Finite boundary holonomy and resolved topology | Affine/max-affine block composition, continuous images of compact sets, and compact subsets of `ℕ × X` having bounded first coordinate are elementary/classical. “Holonomy” is terminology, not proof of geometric novelty. | `QuittingBoundaryHolonomy`'s simultaneous prescribed/all-behavior semantics, exact-D roots, packet factors, and calibrated provenance are **likely-new formal packaging/application**. At `14d75ff`, the full fixed-cutoff source graph and fixed-last calibrated lift are compact/closed, while a compact lift retaining literal unbounded length is impossible. This sharp game-facing packaging/fence is plausibly distinctive, but the arbitrary-length tightness/infinity-chart decoder remains a **conjectural original idea**. [Landed claim](../ideas/PositivePlateauBoundaryClosure/FiniteCalibratedBlocksHaveCompositionalBoundaryHolonomy.md), [partial/open claim](../ideas/PositivePlateauBoundaryClosure/RealizedAnchoredHolonomyClosedness.md). | **High** for the finite algebra and fixed-cutoff topology; no formalization claim for the missing decoder. | `high` that the abstract ingredients are not novel; `medium` that their provenance-complete game-facing bundle and exact length fence are new; `low` on the open compactification principle until proved/refuted. |
| Greedy buffered return/exit/dead-end | Finite-cover pigeonhole and greedy first-exit arguments are elementary. | The exact trichotomy is useful but probably not mathematically novel; its optimized-debt decoder is a **conjectural original application**, not landed. [Claim](../ideas/CycleGeometryResolution/GreedyBufferedPathsReturnExitOrDie.md). | **Medium-high** as reusable Lean infrastructure. | `high` on low abstract novelty; `low` on novelty/value of the unproved decoder until it closes a game theorem. |
| Stationary cap and classification | Snell envelopes, geometric stopping, and one-state stationary best responses are classical. | The exact two-regime full-rate cap, arbitrary-behavior iff terminal-Nash verifier, and gap/escape typing are **likely-new formal application**. [Exact cap](../ideas/StationaryRepairExhaustion/FullRateStationaryCapIsExact.md), [gap split](../ideas/StationaryRepairExhaustion/StationaryExploitabilityHasGapOrEscapeDichotomy.md). | **High**. | `medium`; compare quitting LCP/stationary equilibrium and optimal-stopping literature. The verifier is not a new stationary existence theorem. |
| Stationary nonattainment fence | Nonclosed best-response correspondences at zero hazard are a familiar boundary phenomenon. | The exact two-player table with vanishing stationary exploitability but no exact behavioral terminal equilibrium is **plausibly a new explicit fence**, subject to source search. [Claim](../ideas/StationaryRepairExhaustion/NaiveStationaryCompactificationNeedNotAttainEquilibrium.md). | **High** once packaged. | `medium`; small exact examples are easy to rediscover and may be known in quitting-game folklore. |
| Self-similarity / graph-directed coding | Contracting graph-directed IFS, periodic coding, and common-prefix estimates are classical. | Certified K11/full-shift cycle families and their equilibrium interpretation are **likely-new explicit applications/examples**. An invariant-circle/Sturmian characterization was weakened by multiplier evidence and is not a result. [Cycle group](../ideas/CycleGeometryResolution/README.md). | **Medium-high** for formalized coding kernels; table certificates vary. | `medium`; compare graph-directed IFS, piecewise rational dynamics, symbolic dynamics, and computational game-equilibrium atlases. |
| Explicit cyclic/nonstationary examples | FTV, Sorin, and Solan--Vieille four-player fences are known and must remain attributed. | Block-pair support fans, K11 contracting cycles, pure-externality counterexamples, and several exact no-go tables appear **plausibly new repository examples/fences**, but each needs a dedicated literature comparison and stable certificate audit. See [literature group](../ideas/UniformEquilibriumLiterature/README.md) and production counterexample modules. | **High** for formal transcriptions/internal exact examples. | `medium-low` mathematical novelty until table-by-table search; `high` that published examples themselves are not new. |
| Zero-sum and single-controller work | Shapley, Bewley--Kohlberg, Mertens--Neyman, Kohlberg, Vrieze, and single-controller projection/value results are classical source mathematics. | The repository's Puiseux/account route and unconditional finite zero-sum single-controller proof are mostly **independent formal reconstructions/applications**, not new claims of existence. Some internal algebraic no-go results may be new. [Literature dependency](../ideas/UniformEquilibriumLiterature/MertensNeymanDependsOnBewleyKohlbergSelection.md). | **High** within audited systems. | `high` on classical attribution; `medium` on novelty of the exact alternative proof architecture. |
| Broader Lean corpus | Most constituent finite probability, fixed-point, game, learning, mechanism, and fair-division theorems have classical relatives. | The integrated average-reward stochastic-game corpus, semantic uniform-equilibrium APIs, Big Match, quitting chain machinery, and permanent falsifier suite appear unusually broad and likely novel as a formal artifact. | **High but not field-wide certified.** | `medium-high`: direct Isabelle/AFP and limited Coq comparison found no close counterpart, but Lean/Rocq/Agda/HOL4/PVS/Mizar search was incomplete. |

## Independent side-result harvest

Proof-mining sections 36--49 produced several sound standalone results. Their
claim files deliberately carry attribution caveats: harmonic pure-Nash
flatness, Hodge-defect approximation, Nash-set convergence of fictitious play,
IESDS/correlation rigidity, direct recommendation, DSIC cyclic holonomy, data-
processing equality, joint posterior completion, and EF1-to-MMS. These are
primarily **likely-new formal packaging of classical or folklore mathematics**,
not claimed mathematical discoveries. See the populated `INDEPENDENT` section
of [`ideas/INDEX.md`](../ideas/INDEX.md).

## Neighboring literatures requiring comparison

Before any external novelty claim, search at least:

- quitting, absorbing, recursive, and positive-recursive stochastic games;
- absorption paths, linear complementarity, sunspot/correlated equilibria, and
  APS/self-generating sets;
- average-reward MDPs, multichain gain--bias/Poisson equations, Blackwell
  optimality, optimal stopping, and Snell envelopes;
- viability, differential inclusions, Young measures, concentration-
  compactness, Conley theory, graph-directed IFS, symbolic dynamics, tropical
  and max-plus systems;
- occupation-measure LP duality and dynamic mechanism design;
- cyclic monotonicity/implementability, Bayesian persuasion, and epistemic
  common-belief thresholds; and
- proof-assistant libraries and papers in Lean, Isabelle, Rocq/Coq, Agda,
  HOL4, PVS, and Mizar.

## Update triggers

Update an assessment row when a primary-source audit finds an antecedent, a
claim is strengthened or formalized, a counterexample refutes it, a new
application makes an abstract theorem load-bearing, or a reproducible broader
proof-assistant search changes formalization confidence. Mathematical and
formalization novelty must be updated separately.

For authoritative status, use [`FRONTIER.md`](../docs/uniform-equilibrium/FRONTIER.md),
[`PIPELINE.md`](../docs/uniform-equilibrium/PIPELINE.md), the linked claim file,
and production Lean. This provisional assessment controls none of them.
