# D33: quasilinear direct mechanisms have a capability-free native owner

- **Status:** adopted; stable promotion pending
- **Date:** 2026-08-08
- **Experiment ID:** EXP-066

## Decision / question

Whether weak monotonicity and its affine-maximizer and Myerson consumers should
share a native quasilinear direct-mechanism owner, overload the existing
Groves-specific `Mechanism.Auction.VCGSetup`, or be reconstructed from the
outcome-generic `Languages.BayesianMechanism` with extra certificates.

## Competing designs

1. Define capability-free direct-mechanism data containing report types,
   type-dependent valuations, an allocation rule, and payments.  Compile it to
   the canonical Bayesian mechanism and state DSIC through canonical incentive
   compatibility.
2. Generalize `VCGSetup` until it also owns arbitrary quasilinear direct
   mechanisms, weak monotonicity, affine maximizers, and Myerson.
3. Use `BayesianMechanism` alone and attach allocation/payment decomposition
   certificates to every theorem that needs quasilinear structure.

Design 1 is adopted.  The native record owns exactly the structure shared by
the three pinned families.  `VCGSetup` includes Groves-specific offsets and
welfare-maximizing allocation assumptions that weak monotonicity does not need.
Conversely, an arbitrary Bayesian outcome does not expose the allocation and
payment terms whose cancellation is the mathematical content of the theorem.

The native DSIC name is not a parallel solution concept: it is a transparent
abbreviation of `BayesianMechanism.IsIncentiveCompatible` after compilation.

## Representative hostile slice

EXP-066 uses Boolean players, types, and alternatives.  The first player's
report changes both the selected alternative and a nonconstant payment.  At
the false type, truthful utility is `2` while the true-report replacement by
the other report gives `-1`.  The allocation satisfies a strict
weak-monotonicity witness.  Reversing the allocation rule while preserving the
same nonconstant valuation and payment data creates a profitable deviation and
refutes DSIC.

The generic theorem applies the two opposite canonical incentive constraints,
rewrites only canonical `Profile.update` laws, and cancels the two payments.
The existing `VCGSetup` embeds into the candidate with definitional equality of
true utility.

## Measurements

| Measure | EXP-066 result |
|---|---|
| candidate artifact | 169 nonblank lines; 22 structure/definition/theorem declarations |
| direct imports | canonical Bayesian mechanism and existing VCG leaf only |
| stored capabilities | none: no prior, finiteness, decidable equality, probability law, topology, or Groves certificate |
| incentive semantics | `IsDSIC` abbreviates canonical `IsIncentiveCompatible` |
| hostile variability | allocation, valuation, payment, and deviation utility all nonconstant |
| source hazards | zero raw updates, transports, `Fintype.ofFinite`, probability projections, placeholders, or custom axioms |
| axiom profile | `propext`, `Classical.choice`, and `Quot.sound` only |
| focused gate | warning-free 1,726-job build |

## Kill condition

Reject native ownership if the slice needs a prior, expected utility, stored
finiteness, a dummy strategic game, raw update, public transport, or duplicate
equilibrium predicate; if VCG and affine/Myerson inputs do not specialize
transparently; or if the hostile theorem is vacuous because its allocation,
valuation, payment, or deviation behavior cannot vary.

No kill condition fired.  Finiteness occurs only on the existing VCG consumer
bridge, and the canonical IC compilation retains the full report profile in
the chosen outcome precisely because payments may depend on every report.

## Consequences for the public API

The stable owner belongs under the opt-in `GameTheory.Mechanism` branch.  Its
base data remains capability-free and its DSIC surface remains definitionally
canonical.  Weak monotonicity is the first owned allocation certificate.
Groves/VCG conversion is a named downstream bridge, while affine maximizers and
Myerson add only their own extra fields and assumptions after promotion.

Executable finite mechanism search, priors and expected utility, continuous
type spaces, and measurable payment identities remain separate consumers; none
is added to the base record.
