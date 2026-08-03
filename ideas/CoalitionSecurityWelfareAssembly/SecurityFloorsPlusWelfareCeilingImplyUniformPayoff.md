# Security floors plus a positive welfare ceiling imply a uniform payoff

| Status | Provenance | Lean | Producer |
| --- | --- | --- | --- |
| `PROVED`, maturity `M+L` | coalition-splitting audit | `WeightedSecurityWelfareAssembly.lean`, `WeightedWelfareBias.lean` | positive-separator group or actual split adapters |

Let target `v` have, for each player, one uniform one-sided strategy securing
`v_i` against the complementary coalition. Suppose also that strictly positive
weights `α` give an all-profile uniform ceiling
`α·payoff <= α·v + o(1)` saturated at `v`. Then `v` is a uniform-equilibrium
payoff. A bounded weighted Bellman bias supplies the ceiling with endpoint loss
`2C/T`.

This is an assembly/verification theorem. It does not produce compatible
security strategies, positive weights, or the bias. Those hypotheses are
substantial and cannot be inferred from separate split equilibria alone.
