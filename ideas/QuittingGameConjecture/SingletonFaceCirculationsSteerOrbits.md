# Singleton-face circulations steer orbits

| Status | Provenance | Consumer | Falsifier |
| --- | --- | --- | --- |
| `OPEN`, maturity `L` (singleton-support phases, `n`-agnostic) / `M [reported]` (multi-owner phases), P0 | Q159 §5; `SingletonFaceCirculation.lean`, `SingletonFaceCirculationOrbit.lean` | the relaxed compiler (K4); certsearch as a new certificate mode; the Q160-thread family's Part B | the certificate class being empty beyond the calibrated example |

**Machine-checked**: the certificate structure over an arbitrary finite index
type; the one-phase step delivering support-perfection; the calibration
certificate on the scaled cyclic weight (`norm_num` throughout); and the
orbit theorem — for every `ε > 0` and every `Q`, a support-perfect rational
orbit with prefix quit mass `≥ Q`. Scope: **singleton-support phases only**,
which covers the answer's own calibration and is uniform in `n`; the
multi-owner balanced-word case remains reported. One sharpening from
recomputation: for singleton supports the answer's tolerance bound carries a
spurious summand — the owner word is exactly balanced, the owner's gain
exactly `0`, rationality exact — so `H ≤ ε/(2M)` suffices there; the
published bound is sound but not tight for its own instance. The floor is an
abstract vector with `solo ≤ floor`; the min-max quotation `χ ≤ 1/3` is used,
not proved.

## The theorem

A **singleton-face circulation certificate** for a weight: a closed polygon
of feasible vectors `z⁰, …, z^L = z⁰`, phase mixtures `λ^ℓ ∈ Δ(I)` over
singleton targets `u^ℓ = Σ λ^ℓ_i·w({i})`, contraction weights
`α_ℓ ∈ (0,1)` with `z^{ℓ+1} = α_ℓ z^ℓ + (1−α_ℓ) u^ℓ`, every vertex and
segment above the floor `r̲_i = max{d_i, χ_i}`, and **every phase owner
exactly pinned at their solo value**: `i ∈ supp λ^ℓ ⟹ z^ℓ_i = u^ℓ_i = d_i`.

> **If a weight admits such a certificate, then for every `ε > 0` and every
> `Q`, it admits a feasible `ε`-rational `ε`-orbit with quit mass `≥ Q`.**

Uniform in `n`, with explicit constants (the tremble bound `H` explicit in
`ε, M`, the certificate data). The construction discretizes each polygon edge
into balanced owner words of small hazards, and — crucially — delivers the
**support-perfect** one-stage condition, so the theorem is robust to the
weighted-versus-support-perfect correction recorded in
[[weighted-one-stage-nash-cannot-price-motion]]. No part uses the refuted
granted constant.

## Why it matters

- **With the compiler (K4), the certificate class inherits uniform
  equilibrium payoffs** — a new existence class on the open core, produced by
  this program rather than ported.
- **It replaces connectedness for the class**: the answer's B3 verdict is
  that neither a motion-sandwich potential nor bare degree/parity can
  substitute for the external fate-structure's connectedness input, but a
  certified face circulation does, wherever it exists.
- **The certificate is finitely checkable**: at `L = 1, z⁰ = u⁰` it is a
  per-support linear system (`λ` supported on `J`, `(Vλ)_i = d_i` on `J`,
  `Vλ ≥ r̲`, simplex constraints — `V` the matrix of singleton payoff
  vectors); for fixed length and support pattern, a finite semialgebraic
  feasibility problem. **This is a new certsearch mode**: sweep for
  circulation certificates; every hit is a solved weight.
- **Calibration**: at the scaled cyclic three-player weight — the very
  counterexample that killed the granted constant — an explicit three-phase
  certificate exists (`z`-triangle at heights `(1/3,1/3,2/3)` rotated,
  owners `1,3,2`, all `α = 1/2`), so the theorem independently produces
  arbitrarily-large-quit-mass rational orbits there. A genuine `n = 3`
  subcase reproved; not the whole external `n = 3` theorem.

## Open

- Machine-check the theorem. Dispatched (the counterexample computation
  travels with it).
- Run the `L = 1` linear check and small-`L` search over Q160's `F(x, ε)`
  family — the first question is which part of the phase diagram the
  certificate class covers.
- The floor uses the true min-max `χ`; for concrete tables the punishment
  floor/ceiling machinery brackets it, and the bracket may suffice for
  certificate verification (`r̲` only needs an upper bound on `χ` to be
  *sound*... check the direction carefully — the certificate needs
  `z ≥ max{d, χ}`, so an **upper** bound on `χ` weakens the requirement and
  an exact value is safest; state which is used).
- Whether the certificate class is closed under the affine normalization,
  and how it sits relative to the trichotomy's branches.
