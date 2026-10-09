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

## Further opportunities

These are useful follow-ups, not defects in the supported membership claim.
They were deliberately kept out of this focused refactor.

| Priority | Opportunity | Location and suggested boundary |
|---|---|---|
| First | Extract integer lexicographic feasibility into reusable mathematics. | `Finite/BimatrixPathBinaryCodec.lean` currently owns game-independent `IntegerFeasible` and `integerFeasible_iff`. Move their canonical definition and proof into a Math integer-dictionary leaf; keep basis specialization in the codec. |
| Next | Share bounded finite absolute sums. | Bird iteration and endpoint capacity proofs can reuse Mathlib's `Int.natAbs_sum_le` and a small finite-sum bound. Search and reuse those APIs before adding a helper. |
| Next | Extract fixed-block list encoding facts. | Private uniform flat-map length and extraction lemmas in `Finite/BimatrixTableCorrectness.lean` have independent binary-field consumers. |
| Next | Remove theorem-only `DecidableEq` assumptions. | `Math/SmallRationalWitness.exists_small_nonnegative_solution` and bounded linear certificate existence wrappers already use classical proof reasoning. |
| Next | Consolidate width accounting. | `Backend.NashNP`, `BoundedSupportWitness`, `NashWitnessCompleteness`, and the executable certificate ruler repeat the constrained-Nash width formula. Use one semantic formula and prove the executable ruler agrees with it. |
| Later | Reuse the upstream bit-extraction specification. | Several backend arithmetic/node modules repeat `bitAt` semantics. ComplexityLib already provides `Extract.bitAt_eq`; prefer that primitive over another private recursive proof. |
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
- Released-pin consumer validation is recorded with the final base pin below.
