# Uniform-equilibrium documentation

This directory contains durable documentation for the uniform-equilibrium
program. It is intentionally separate from mutable working state under
[`ephemeral/`](../../ephemeral/) and lifecycle-owned research ideas under
[`ideas/`](../../ideas/).

## Coordination and methods

- [Program.md](Program.md) defines the stable research/formalization workflow.
- [methods/MathResearchMethod.md](methods/MathResearchMethod.md)
- [methods/LeanFormalizationMethod.md](methods/LeanFormalizationMethod.md)
- [methods/ParallelResearchMethod.md](methods/ParallelResearchMethod.md)

## Evidence and design records

- [references/](references/) is the citation-of-record collection.
- [audits/ResearchSynthesis.md](audits/ResearchSynthesis.md),
  [audits/ProofScaffoldingReview.md](audits/ProofScaffoldingReview.md), and
  [audits/LeanSettlementAudit.md](audits/LeanSettlementAudit.md) preserve
  durable audits without pretending to be the current frontier.
- [design/RootTargetStratification.md](design/RootTargetStratification.md) is a
  dated design record.
- [case-studies/FTVArchitectureAnalysis.md](case-studies/FTVArchitectureAnalysis.md)
  records the verified FTV architecture analysis.
- [manuscript/UniformEquilibriumFrontierManuscript.tex](manuscript/UniformEquilibriumFrontierManuscript.tex)
  is the manuscript source; the generated PDF is kept beside it locally.

The mutable frontier remains
[ephemeral/UniformEquilibriumCurrentFrontier.md](../../ephemeral/UniformEquilibriumCurrentFrontier.md).
When a durable document and the frontier disagree about current status, the
frontier and the lifecycle cards in [`ideas/`](../../ideas/) control.
