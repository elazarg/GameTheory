# Complexity implementation review

Reviewed after merging Nash PPAD membership to `main` in `bdd92765`
(PR #78), October 2026. The review covered three perspectives: reusable proof
mining, software engineering, and proof simplification. It inspected the
dependency-free arithmetic, pivot and path mathematics; executable codecs and
certificates; and the optional NP, End-of-Line, Sperner, Brouwer and Nash
reductions and their polynomial-time machine proofs.

No critical or high-severity correctness defect was found. In particular,
the reviewed reductions preserve every accepted target answer, including
answers outside the source component. Malformed-instance fallbacks and
invalid-node self-loops remain explicit. This is a review conclusion about
the implemented statements, not an assertion that Nash hardness, unrestricted
Brouwer representations, or FIXP have been established.

## Implemented findings

| Perspective | Finding | Resolution |
|---|---|---|
| Proof mining | Numeric Cramer storage bounds assumed a nonzero determinant even though singular input produces zero sign-adjusted numerators. | Removed that premise from natural and signed numerator bounds and propagated the stronger statement through dictionary coefficient, direction and cross-product bounds. Nonsingularity remains on decoding and positive-denominator results. |
| Proof simplification | Integer and optional dictionary selection repeated cancellation of a positive common denominator. | Added the game-independent `Math.isLeavingRow_div_iff` and reused it in both consumers. The optional selector no longer needs its local transparency workaround. |
| Proof mining and simplification | Reduction soundness repeated pointer agreement at a witness and its two neighbors. | Added `Math.EndOfLine.rawWitness_congrOn`, with domain closure as an explicit premise. Normalized End-of-Line and bimatrix reductions reuse it on fixed-width words. |
| Software engineering | Three arithmetic modules contained the same little-endian append proof. | Exposed the existing `Backend.BinaryCertificateArithmetic.fromBitsLE_append` lemma and removed the two duplicates. No new abstraction or module was introduced. |
| Software engineering | The optional README described completed Nash membership/totality as future work and advertised an obsolete base pin. | Corrected the status and release instructions. Nash hardness and FIXP remain identified as future work. |
| Software engineering | The released-consumer CI smoke omitted Brouwer entry points. | Added the Brouwer tests and public simplicial Brouwer module to the released-pin build. |

The singular regression uses `[[1,2],[2,4]]` with right-hand side `[-1,1]`:
the replacement determinant is -6, while the original determinant is zero
and the stored sign-adjusted numerator is zero. Kernel-checked controls also
exercise the unconditional dictionary storage bounds.

## Priority implementation

The first six opportunities below are now implemented. Generic feasibility
lives in `Math.IntegerDictionaryFeasibility`, integer sum estimates in
`Math.IntegerSumBounds`, and equal-width block extraction in `Math.FixedBlockList`.
Their existing consumers reuse the canonical statements, including packed
binary matrix extraction. Linear feasibility existence no longer asks callers
for `DecidableEq`; an abstract finite-carrier control checks this interface.
`Math.constrainedNashCertificateWidth` owns the width formula, with executable
ruler agreement. One indexed-bit specification now reuses ComplexityLib's
`bitAt_eq` instead of six separate recursive proofs.

The full base and lint-scope build passes 4,519 jobs, including the changed
finite-carrier and codec tests. The full local-path companion/lint/axiom build
passes 4,336 jobs, both linters pass, and transitive auditing accepts 164 base
declarations and all 3,769 owned companion declarations using only the three
standard Lean axioms. Regular architecture and optional-boundary audits pass,
as do all 19 optional-boundary regression tests. The namespace move is checked
against both the base codec and the concrete node-validation machine proofs.
The full companion/lint/axiom build and lint also pass without a local override
against published base pin `2c8e70ebae382a0db21f2441ebff28c7b1e41689`.

## Reviewed opportunities

These are useful follow-ups, not defects in the supported membership claim.
The first six were implemented in the priority follow-up; the final facade
suggestion remains consumer-gated.

| Priority | Opportunity | Location and suggested boundary |
|---|---|---|
| Implemented | Extract integer lexicographic feasibility into reusable mathematics. | `Math.IntegerDictionaryFeasibility` now owns `IntegerFeasible` and `integerFeasible_iff`; basis specialization stays in the codec. |
| Implemented | Share bounded finite absolute sums. | `Math.IntegerSumBounds` uses Mathlib's `Int.natAbs_sum_le`; Bird iteration and endpoint capacity proofs reuse it. |
| Implemented | Extract fixed-block list encoding facts. | `Math.FixedBlockList` replaces private table lemmas and the packed binary table extraction induction. |
| Implemented | Remove theorem-only `DecidableEq` assumptions. | `Math/SmallRationalWitness.exists_small_nonnegative_solution` and bounded linear certificate existence wrappers use classical proof reasoning internally. |
| Implemented | Consolidate width accounting. | `Math.constrainedNashCertificateWidth` is shared by the relation, witness proofs and executable ruler agreement. |
| Implemented | Reuse the upstream bit-extraction specification. | The arithmetic and node modules share `Backend.bitAt_getElem?`, proved from ComplexityLib's `bitAt_eq`. |
| Later | Further insulate explicitly computational clients from backend details. | The semantic facade already separates the opt-in dependency, but clients naming concrete backend machines still couple to it. Add a narrower public specialization only when a real client needs it; avoid a general certificate hierarchy. |

The independently reusable additions in this change need only Mathlib and
are suitable for upstream discussion. Game-specific reductions stay in the
optional companion. All companion public modules are covered by its lint
driver, and all test modules are covered by its axiom audit. The dependency
audit checks that the base does not require ComplexityLib/CSLib. The reviewed
public entry-point import closures avoid the Analysis root; this was an import
review, not a check implemented by that dependency script.

## Validation

- `lake build GameTheory.Math.EndOfLineNormalization
  GameTheory.Math.IntegerDictionaryComputation
  GameTheory.Finite.BimatrixCramerCertificate
  GameTheory.Tests.IntegerCramerEncoding
  GameTheory.Tests.IntegerCramerComputation GameTheory.LintAll`: passed,
  4,163 jobs, warning-free; `lake lint`: passed.
- Companion local-path build of `GameTheoryComplexity.LintAll`,
  `GameTheoryComplexity.AxiomAudit`, Brouwer tests and bimatrix reduction tests:
  passed, 4,332 jobs; local-path `lake lint`: passed.
- Transitive axiom checks: all 3,777 owned companion declarations and all
  115 declarations in the eight changed base modules use only `propext`,
  `Classical.choice`, and `Quot.sound`. The base check is a local probe in
  `.codex/scratch/ComplexityReviewAxiomAudit.lean`.
- Regular `scripts/phase2-audit.ps1`, `scripts/phase3-audit.ps1 -VerifyExpected`,
  and `scripts/complexity-audit.ps1`: passed. All 19 complexity boundary
  regression tests and the architecture mutation regression passed.
- Lean version check: 4.34.1; targeted Mathlib cache check: no missing files.
- The initial review base pin was `572e3b675ade7364d1cc86cb79e9c801eb47d47f`, the
  published review implementation. Lake resolved that git revision and the
  toolchain/cache checks passed. The released-pin build was stopped at the
  user's request to finish statically; it is not claimed as completed.
  The subsequent implementation request advances the default pin to
  `2c8e70ebae382a0db21f2441ebff28c7b1e41689`; its complete 4,336-job
  companion/lint/axiom build and lint pass in released git mode.

## Post-completeness proof mining

PRs #79 and #80 are merged to `main` at `9765b42a`. The follow-up reviews the
complete every-answer Nash reduction and its independently reusable mathematics.
The mathematical refactor changes theorem assumptions; gate definitions and
payoff semantics are unchanged.

| Perspective | Finding | Implemented result |
|---|---|---|
| Proof mining | Feedback callers supplied nonnegativity of the inward scale and error budgets, although the inward and absolute-error bounds already imply it. | `clampedFeedback_residual_bound` derives `0 ≤ L`, `0 ≤ ρ` and `0 ≤ η`; robust feedback and jitter wrappers drop the redundant premises. |
| Proof mining | Clipped minimum correctness unnecessarily restricted the signal to the unit interval. | `min_eq_clipped_sub` and `clippedSub_min_error` now require only a nonnegative signal. Minimum, interpolation and Brouwer-gate consumers use the stronger statements. |

Existing tests now exercise both exact and perturbed signals above one. The
full base/library/lint build passes 4,556 jobs, base lint passes, and the
transitive standard-axiom audit accepts all 557 owned gate/math declarations.
