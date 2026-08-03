# Repository reorganization (2026-08-03)

The research workspace was reorganized so file location communicates lifecycle
instead of topic alone. Do not recreate the old paths.

| Material | Canonical location | Rule |
| --- | --- | --- |
| production Lean and reusable mathematics | `GameTheory/`, `Math/`, `Semantics/` | tracked and imported normally |
| durable uniform-equilibrium documentation | `docs/uniform-equilibrium/` | stable methods, references, audits, design records, and manuscript |
| lifecycle-owned ideas | `ideas/` | one coherent group per file, using `ideas/README.md` |
| cross-field survey portfolios | `ideas/wild/` | intake only; extract an actionable claim to its own lifecycle group |
| isolated proof and computation probes | `experiments/` | gitignored by default; production never imports it |
| active self-contained questions | `questions/` | launch queue; no project-specific cross-references in question bodies |
| farmed questions and appended answers | `questions/old/` | `old` means already dispatched, not verified or closed |
| mutable research state and local evidence | `ephemeral/` | frontier, proof-mining ledgers, reviews, certificates, monitor, old scratch |

## Important moves

- `ephemeral/experiments/` moved to root `experiments/` and remains ignored.
  Files already tracked in a future promotion remain tracked under ordinary Git
  semantics; the directory ignore rule governs new files only.
- Stable methods, references, audits, the FTV case study, root-target design
  record, and frontier manuscript moved from `ephemeral/` to
  `docs/uniform-equilibrium/`.
- Lifecycle-card idea groups moved from `ephemeral/` to `ideas/`; wild-idea
  surveys moved to `ideas/wild/` and are explicitly not lifecycle owners.
- Numbered Questions 19--133 moved to `questions/old/` after farming. The
  unnumbered independent-question collection remains at the top level because
  it uniquely contains unfarmed Questions 1--18.

## Working rules

1. Add experimental Lean proofs freely under `experiments/`; promote only the
   smallest audited theorem surface with a known production consumer.
2. Update `ideas/INDEX.md` whenever a lifecycle card changes status, verdict,
   priority, or current gate.
3. Keep question packets self-contained. Record commit hashes, adapters,
   reviewer status, and implementation links outside the question file.
4. Use `ephemeral/` only for genuinely mutable or local material. Move a record
   to `docs/` once its role is durable, even if later evidence may supersede
   its dated conclusions.
5. Paths in older prose may describe historical locations; new links and
   commands must use the canonical locations above.
