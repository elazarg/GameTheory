# Uniform-equilibrium documentation

This directory contains durable documentation for the uniform-equilibrium
program.

## Cold-handoff read order

1. [PIPELINE.md](PIPELINE.md) — current decisions, objective priorities,
   active gates, blockers, and acceptance conditions.
2. [FRONTIER.md](FRONTIER.md) — the mathematical theorem chain, exact open
   hinge, known boundaries, alternatives, and falsifiers.
3. Follow the direct links there to one exact
   [`ideas/<Group>/<Claim>.md`](../../ideas/README.md) scientific object or
   attributed result under
   [`ideas/UniformEquilibriumLiterature/`](../../ideas/UniformEquilibriumLiterature/README.md).
4. Read [Program.md](Program.md) when changing the research/formalization
   method, and the [research atlas](manuscript/UniformEquilibriumFrontierManuscript.tex)
   for long-form exposition.

For a provisional, non-authoritative literature/novelty assessment, see
[`ephemeral/UniformEquilibriumNoveltyAssessment.md`](../../ephemeral/UniformEquilibriumNoveltyAssessment.md).
The measured repository/CI assessment is
[`ephemeral/ProofEngineeringAudit.md`](../../ephemeral/ProofEngineeringAudit.md).

## Coordination and methods

- [Program.md](Program.md) defines the stable research/formalization workflow.
- [PIPELINE.md](PIPELINE.md) is project-control truth.
- [FRONTIER.md](FRONTIER.md) is the curated mathematical state of knowledge.
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

Questions, reviews, proof-mining notebooks, experiments, and archived
`ephemeral/` files are intake/evidence; none is current truth by itself. The
manuscript is refreshed periodically from the frontier rather than updated on
every theorem commit.
