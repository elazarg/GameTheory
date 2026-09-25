# Architecture decision records

Add one short record for each experiment-gated RFC decision before its public
API freezes. Use the decision identifier in the filename, for example
`D1-signature-indexing.md`.

```text
Decision:
Status:
Experiment IDs:
Hypothesis:
Competing designs:
Representative examples:
Comparative measurements that determine the choice:
Evidence from existing libraries:
Costs and mathematical limitations:
Kill condition:
Result: accept / reject / narrow
Consequences for public API:
```

The concise chronological evidence belongs in `../ExperimentLog.md`; link its
experiment IDs and the exact spike artifacts here. This record interprets the
evidence and fixes the resulting API decision. A rejected design and its
counterexample are useful project results and should remain documented.

Write decisions as durable explanations of the chosen design and its limits.
Keep a measurement here only when it explains the choice between alternatives;
link to the experiment log for exact commands and results. Build job counts,
"now compiles" reports, recovery checklists, and work-in-progress updates belong
in the experiment log, delivery ledger, or worklog, not in a decision record.
