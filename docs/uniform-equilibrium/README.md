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
   method, the [research atlas](manuscript/UniformEquilibriumFrontierManuscript.tex)
   for the detailed theorem/idea map, and
   [intuition.tex](manuscript/intuition.tex) for a shorter conceptual account of
   the current escaping-middle problem.

For a provisional, non-authoritative literature/novelty assessment, see
[`ephemeral/UniformEquilibriumNoveltyAssessment.md`](../../ephemeral/UniformEquilibriumNoveltyAssessment.md).
The measured repository/CI assessment is
[`ephemeral/ProofEngineeringAudit.md`](../../ephemeral/ProofEngineeringAudit.md).

## Coordination and methods

- [Program.md](Program.md) defines the stable research/formalization workflow.
- [PIPELINE.md](PIPELINE.md) is project-control truth.
- [FRONTIER.md](FRONTIER.md) is the curated mathematical state of knowledge.
- [EssentialAPS.md](EssentialAPS.md) states the exact algebraic/executable
  boundary of the essential-APS singleton-flow formalization.
- [SupportWitnessCompiler.md](SupportWitnessCompiler.md) records the
  deterministic support-witness path and periodic-cycle compiler, including
  its remaining producer obligation.
- [CirculationUniformPayoff.md](CirculationUniformPayoff.md) records the
  conditional multi-owner face-circulation producer class, its compact path
  selection, and its concrete quitting-game corollaries.
- [PayoffPerturbationClosure.md](PayoffPerturbationClosure.md) records
  fixed-skeleton reward stability and target-free existence closure.
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
  is the detailed manuscript source;
- [manuscript/intuition.tex](manuscript/intuition.tex) is its conceptual
  companion.  Both are derivative exposition: resolve status conflicts in
  favor of `PIPELINE.md`, `FRONTIER.md`, the owning claim file, and finally the
  production Lean declaration. Generated PDFs are local build artifacts.

Questions, reviews, proof-mining notebooks, experiments, and archived
`ephemeral/` files are intake/evidence; none is current truth by itself. The
manuscript is refreshed periodically from the frontier rather than updated on
every theorem commit.
