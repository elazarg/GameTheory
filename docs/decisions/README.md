# Architecture decision records

Add one short record for each experiment-gated RFC decision before its public
API freezes. Use the decision identifier in the filename, for example
`D1-signature-indexing.md`.

```text
Decision:
Experiment IDs:
Hypothesis:
Competing designs:
Representative examples:
Measurements:
Evidence from existing libraries:
Unexpected costs:
Kill condition:
Result: accept / reject / narrow
Consequences for public API:
```

The concise chronological evidence belongs in `../ExperimentLog.md`; link its
experiment IDs and the exact spike artifacts here. This record interprets the
evidence and fixes the resulting API decision. A rejected design and its
counterexample are useful project results and should remain documented.
