# Pinned v1 reference

`GameTheory-v1/` contains only the old repository's `GameTheory/` and `Math/`
trees at commit:

```text
a3d8c67ed91d58e197b8c978ddcc00ba96f87c29
```

The snapshot is ignored by Git and need not compile. It exists to measure the
old hub, bridge, probability, and proof-engineering costs called out by the
design RFC.

Rules:

- never import it from the new library;
- never edit it to prototype the rewrite;
- cite its commit and path when using it as evidence;
- use `git archive` from the old repository to refresh it deliberately.
