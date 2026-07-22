# Phase 1 core competition gate

The initial Phase 1 gate was committed as `4f308a0`; this record includes the
subsequent automated-review corrections to its evidence and affine slice.

- D1 provisionally selects a form storing its signature. The result is not
  frozen until the Phase 2 usability and transformation slice passes.
- D2 selects a finite-support `PMF` subtype behind the future `FinDist` API.
- The D2 Analysis bridge is an equivalence with `stdSimplex ℝ α`; mixed-game
  semantics will keep one logical API. The bridge now proves pure-vertex,
  expectation, product, and affine-mixture preservation for the winning law.
- Experimental modules are isolated under
  `GameTheory.Experimental.Phase1`; no v1 source is imported and no stable API
  imports the losing representation.

Exact metrics and commands are in
[`D1-signature-ownership.md`](decisions/D1-signature-ownership.md),
[`D2-finite-law-representation.md`](decisions/D2-finite-law-representation.md),
and [`ExperimentLog.md`](ExperimentLog.md). The reproducible source audit is
`pwsh -NoProfile -File scripts/phase1-audit.ps1 -VerifyExpected`; add `-Time`
for machine-dependent warm elaboration timings.

The phase-gate build is:

```text
lake build
```

The RFC's `GameTheory2.*` names were illustrative. The repository contract
deliberately uses package, library, and public namespace `GameTheory`; the
directory name `GameTheory2` is not part of the API.
