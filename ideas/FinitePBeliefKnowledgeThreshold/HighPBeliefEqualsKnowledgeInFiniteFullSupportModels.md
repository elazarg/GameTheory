# High p-belief equals knowledge in finite full-support models

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| One-cell theorem `PROVED`; common-belief lift `OPEN`, maturity `M+I` | Proof-mining §44, extracted 2026-08-03 | Target: `Knowledge/ApproximateCommonKnowledge.lean` | `PENDING`; promote after threshold conventions and common lift are checked |

Let `m = min_ω μ(ω) > 0` and `p* = 1-m`. If an information cell is not
contained in event `E`, it contains an outside state of mass at least `m`.
Since the cell has total mass at most one, its posterior probability of `E` is
at most `1-m`. Therefore, for `p>p*`,

\[
  PBelief_\mu(P,p,E)=Knows(P,E).
\]

This single-agent/operator identity is proved by the displayed finite-atom
argument. The proposed common version replaces every high-`p` belief step by
knowledge and invokes finite reachability/self-evidence. That lift must be
checked against whether the repository uses weak or strict thresholds and how
zero-probability cells are handled.

Falsifiers: dropping full support destroys a positive uniform atom bound;
allowing infinite state spaces can make the minimum atom zero; `p = p*` may
fail because equality is possible. No state-uniform threshold independent of
the prior is claimed.

Audience/value: epistemic game theory and finite probabilistic knowledge.
Likely known folklore; do not claim novelty. Promote to `INDEPENDENT` only
after the common-operator theorem is audited and the strict-threshold
conventions are explicit.
