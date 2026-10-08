# Complexity and computational results roadmap

This is the active dependency order after continuous approximate Brouwer
PPAD-completeness. The delivery ledger records compiled results; this document
records targets and acceptance gates. Ordinary game clients must continue to
need neither ComplexityLib nor CSLib.

## Starting point

Delivered: NP-completeness of payoff-constrained symmetric mixed Nash existence;
standard End-of-Line, succinct Sperner and continuous approximate Brouwer
PPAD-completeness; actual FP/FPn reductions and independent polynomial verifiers.
The base has bimatrix support identities, potential-game termination,
multiplicative-weights regret bounds, zero-sum regret-to-Nash transfer and
Gale–Shapley stability.

The earlier machine-certified Nash certificates concern one square payoff
matrix, its transpose, and payoff-one constraints. General rectangular
certificates now have mathematical correctness and bounded-witness completeness;
their serialized machine verifier remains the next delivery. Real learning and
matching constructions are not automatically executable finite-bit algorithms.

## 1. Generic prerequisites and general bimatrix witnesses

**First slice, delivered.** The dedicated `Math.FiniteLinearBinaryBound` and
`Math.BoundedLinearCertificate` modules extend small rational solutions of
integer linear systems with bounds polynomial in coefficient **bit width**.
The earlier bound polynomial in coefficient magnitude suffices for the
restricted SAT game family but is inadequate for arbitrary binary payoffs.
The new modules have no game or machine imports and are independently portable.

Their first consumer is one canonical rectangular bimatrix certificate with two independent
integer payoff matrices, natural probability numerators, positive denominators
and signed utility numerators, without payoff thresholds. Exact executable
checking is proved sound against ordinary PMF mixed Nash, and every real Nash
witness admits bounded rational certificates. A fixed-support linear system
splits signed payoff variables into two nonnegative coordinates so the generic
rational-witness theorem applies without a payoff-normalization policy.

Controls cover a rectangular asymmetric game, negative payoffs, a mixed
equilibrium, and rejected simplex or best-response certificates. This slice
claims bounded witnesses and exact verification, not polynomial runtime, TFNP
or PPAD membership of serialized general Nash search.

**Next slice.** Define explicit two-matrix binary input/output codecs, a precise
malformed-input convention and an independent actual FP verifier. Prove witness
balance, FNP membership and totality for nonempty games. Empty or malformed
instances need an explicit fallback. Widths must depend on input bit length,
not payoff magnitude. Any generic binary arithmetic or bounded-record verifier
lemmas needed here belong in dedicated game-free companion modules.

## 2. Bimatrix Nash PPAD membership

Use a complementary-label or complementary-pivot formulation with an explicit
binary encoding. Validate a degenerate hostile game first, then prove every
non-source endpoint supplies a canonical Nash certificate. Certify construction
and decoding in FP/FPn independently of FNP. No nondegeneracy premise may
silently narrow the general theorem. An exact support-enumeration solver is
an independent deliverable; its exponential runtime does not replace this
reduction.

## 3. Bimatrix Nash PPAD hardness and completeness

Reduce the classified fixed-point problem to a finite game. Introduce generalized
circuits only if they shorten the actual reduction and have a concrete game
consumer. Fix gate semantics, fan-out and precision before gadget recovery;
verify every-answer soundness, accumulated error and ambiguous comparators.
The current two-dimensional Brouwer family does not automatically classify
another continuous-map language or generalized circuits.

Certify actual polynomial serialization, then prove every target Nash answer
decodes to a source answer. Combine membership and hardness on the same relation.
Restricted-game corollaries (graphical, polymatrix, sparse or win/lose) follow
only when their own reductions justify their scope.

## 4. Positive algorithms on established semantics

Independent deliveries after their shared APIs settle:

- **Potential/congestion improvement search:** executable finite deviations,
  strict potential progress, correctness and finite step bounds. Integer-range
  bounds are pseudo-polynomial unless their binary encoding is controlled.
  Then define PLS and prove membership for a concrete succinct congestion
  representation; PLS-hardness is a separate reduction project.
- **Zero-sum approximation and approximate CCE:** rational learning updates,
  rounding errors, explicit horizon and bit-cost bounds connected to existing
  regret theorems. External regret gives CCE; CE needs internal or swap regret.
- **Exact correlated equilibrium:** rational linear feasibility and certificate
  correctness first; exact solver next; an actual polynomial-time LP algorithm
  last. Polynomially many constraints do not constitute a runtime certificate.
  Start with explicit payoff tables before succinct games.
- **Deferred acceptance:** ranked finite inputs, executable proposals and
  agreement with stable-matching semantics. Bound proposals by the number of
  possible pairs and separately bound total work. Proposer optimality and
  strategyproofness follow as semantic theorem deliveries.

## 5. Later domains

Scarf and balanced-core search need the balancedness converse and a finite
certificate language. Fisher/Arrow–Debreu results need a market model, utility
representation and precise approximation; linear and Leontief cases must not
be conflated. Exact Nash with three or more players and FIXP need algebraic
circuits and real output semantics rather than rational-witness FNP machinery.

## Module and validation policy

Generic mathematics lives in dedicated Math leaves. Executable rational
algorithms live in Finite; real correctness uses separate modules and canonical
Core predicates. Machine classes and certificates live in the optional
companion, with reusable game-free modules separated from game reductions.
Introduce no universal backend abstraction or duplicate game semantics.
Upstream readiness means minimal imports, generic statements, no placeholders
and independent consumers; submission is separate work.

Compile hostile controls, update lint scopes, run relevant targets and lint,
and audit transitive axioms. Import or package changes require the full affected
build. Update the owning ledger row with its evidence in the same commit.
Use .codex/scratch for probes and release-test companion pins when new base
APIs are used. Ordinary recovery needs no architecture experiment entry.

## Validation of the first slice

The full base and lint-scope build passes 4,426 jobs. Base lint passes, and the
transitive audit checks all 143 new declarations using only propext,
Classical.choice and Quot.sound. Architecture and optional-dependency isolation
audits pass, as do all 30 boundary regressions. Independent review confirms
signed splitting, support preservation and polynomial binary widths.
The analytic existence corollary supplies a bounded certificate for every
nonempty integer bimatrix game while keeping fixed-point imports in Analysis.

Commands from the repository root:

    lake build GameTheory GameTheory.LintAll
    lake lint
    lake env lean .codex/scratch/BimatrixWitnessAxiomAudit.lean
    pwsh -File scripts/phase2-audit.ps1 -VerifyExpected
    pwsh -File scripts/complexity-audit.ps1
    python -m unittest discover -s scripts/tests

The sole added representation owner is the Nash-to-linear-system bridge which
extracts native atom weights. Raw probability representation tokens remain
forbidden in the linear systems, certificates, algorithms and all other
non-owner modules.

## Primary proof references

- [Chen–Deng–Teng: bimatrix Nash](https://arxiv.org/abs/0704.1678).
- [Fabrikant–Papadimitriou–Talwar: congestion complexity](https://alex.fabrikant.us/papers/fpt04.pdf).
- [Papadimitriou–Roughgarden: correlated equilibrium](https://timroughgarden.org/papers/cor.pdf).
- [Generalized-circuit tolerance semantics](https://arxiv.org/abs/1907.12854).
- [Etessami–Yannakakis: Nash and FIXP](https://www.research.ed.ac.uk/en/publications/on-the-complexity-of-nash-equilibria-and-other-fixed-points-exten/).
