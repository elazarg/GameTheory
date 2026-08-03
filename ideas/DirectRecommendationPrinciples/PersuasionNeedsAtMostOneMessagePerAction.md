# Persuasion needs at most one message per receiver action

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `PROVED`, maturity `M` | Proof-mining §43, extracted 2026-08-03; direct-signal attribution required | Target: `Mechanism/Bayesian/InformationDesign.lean` | `INDEPENDENT` |

Given a finite signal kernel `κ` and persuasive decision rule
`r : Msg -> Act`, push `κ` forward through `r` and use the identity rule on
messages of type `Act`. For recommended action `a`, each receiver score
difference against `a'` is the sum of the old nonnegative score differences
over the fiber `r^{-1}(a)`. Empty fibers contribute zero. Regrouping the sender
score sum preserves expected utility exactly.

Hence any achieved persuasion payoff has a persuasive direct scheme using at
most `card Act` messages. The construction preserves payoff and obedience, not
the interpretation or distribution of the old messages. It does not assert an
optimal scheme in infinite spaces. The theorem is classical in spirit;
novelty is not claimed.
