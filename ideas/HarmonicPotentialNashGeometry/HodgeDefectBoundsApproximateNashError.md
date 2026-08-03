# Hodge defect bounds pure approximate-Nash error

| Claim status | Provenance | Formalization | Resolution |
| --- | --- | --- | --- |
| Exact edge-defect theorem `PROVED`; norm bound `OPEN`, maturity `M+I` | Proof-mining §38, extracted 2026-08-03 | Target: companion to `Potential/Decomposition.lean` | `INDEPENDENT` |

Write a finite game uniquely as `u=p+h+n`, with potential, harmonic, and
nonstrategic components. Choose a global maximizer `σ` of an exact potential
for `p`. Potential deviation flows at `σ` are nonpositive and nonstrategic
flows vanish. Therefore every profitable deviation in `u` is bounded by the
positive harmonic edge defect

\[
\Delta(h)=\max_{\sigma,i,a_i'}[flow_h(\sigma,i,a_i')]_+,
\qquad
Expl_u(\sigma)\le\Delta(h).
\]

Thus every finite game has a pure `Δ(h)`-Nash profile. If the potential
maximum has strict outgoing margin `γ` and every harmonic edge flow has
absolute value below `γ`, it remains a strict Nash equilibrium of `u`.

The stronger display `Expl <= C ||h||` needs a chosen finite-dimensional norm
and an explicit operator constant; no dimension-free statement is claimed.
The exact edge theorem is ready for Lean once the global-maximizer and flow
interfaces are aligned. Likely audiences are potential games and equilibrium
approximation; attribution remains to be audited.
