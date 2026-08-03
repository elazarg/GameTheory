# DSIC implementability iff cycle holonomy is nonpositive

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| `PROVED` in finite mathematics, maturity `M` | Proof-mining §45, extracted 2026-08-03; Rochet-style attribution required | Target: companion to `Mechanism/Bayesian/Monotonicity.lean` using `OwnerLabeledFlowHolonomy` | `INDEPENDENT`; reactivate for dynamic-mechanism circulation constraints |

Fix agent `i` and opponents' report `θ_-i`. Vertices are types `t`; a report
edge `(t,r)` moves deterministically from `t` to `r` and has charge

\[
c(t,r)=v_i(t,x(r,θ_{-i}))-v_i(t,x(t,θ_{-i})).
\]

For account `H(t)=-payment_i(t,θ_-i)`, the inequality

\[
c(t,r)+H(r)-H(t)\le0
\]

is exactly DSIC. The landed finite flow theorem says such an account exists iff
every nonnegative circulation has nonpositive total charge. Deterministic
circulations decompose into cycles, giving the usual cyclic-monotonicity form;
weak monotonicity is only its two-cycle shadow. Choosing an account for each
`(i,θ_-i)` gives the global payment rule.

Nonclaims: this is finite deterministic quasilinear implementability; it does
not automatically cover randomized allocation, interdependent values, budget
balance, individual rationality, or infinite type spaces. The result is
Rochet-style and almost certainly known; novelty is not claimed. Standalone
value is the exact bridge between mechanism design and the repository's flow-
cohomology library.

It returns to `ACTIVE` if a dynamic mechanism needs the same circulation
certificate with state/time labels.
