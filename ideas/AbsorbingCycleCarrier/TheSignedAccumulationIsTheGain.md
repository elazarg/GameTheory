# The signed accumulation is the gain

## Lifecycle

| Field | Value |
| --- | --- |
| Lifecycle | `ACTIVE` |
| Verdict | `PROVED` for the identity and the instance; general case `OPEN` |
| Objective priority | `P0` |
| Last audited | 2026-08-04, `b76aa8f` |
| Central live claim | The controlling quantity is the **signed** phasewise accumulation of the local gaps, which *equals* the gain exactly — not the worst-case envelope `ε·C`, which is sharp as an upper bound but not necessary. On the defect-vanishing family it tends to zero, so that family does have vanishing gains. |
| Next discriminant | Does every weight admit a defect-vanishing family whose signed accumulation tends to zero? The instance is settled; the general statement is not. |
| Production destination | none yet; the identity is formalizable as stated |
| Supersedes / superseded by | supersedes the `ε·C` reading in [the conversion claim](UniformDefectToGainConversionIsFalse.md) |

## Claim ledger

| Claim | Verdict | Seals | Scope | Consumer |
| --- | --- | --- | --- | --- |
| The exact phasewise excess satisfies `d_k = max{(1−p_k)g_k, q_k d_{k+1} − p_k g_k}` | `PROVED` | `M` `[reported]` | any relaxed cycle, `P_i < 1` | everything below |
| `ε·C₁` is the least *worst-case* envelope, obtained by replacing every permitted violation by `ε` | `PROVED` | `M` `[reported]` | as above | upper bound only |
| The signed accumulation `Q_{i,1}` **equals** `gain_i`, hence `gain_i → 0 ⟺ Q_{i,1} → 0` | `PROVED` | `M` `[reported]` | `P_i < 1`; and `Q = [−r_i({i})]₊` when `P_i = 1` | the necessary-and-sufficient answer |
| `Q_{i,1} → 0` on the period-`3m` family | `PROVED` | `M` `[reported]` | that family | the instance |
| The coefficient's limit is `1 + log 2`, not `(4/3)·log 2` | `PROVED` | `M` `[reported]` | that family | corrects an in-house derivation |
| Every weight admits a defect-vanishing family with vanishing signed accumulation | — | — | — | `OPEN` — the general statement |

## The distinction

Two quantities were being conflated.

**The worst-case envelope.** Replace every permitted violation by `ε` and solve
the resulting cyclic max-affine system. That gives `ε·C₁`, an upper bound on the
gain, and it is the *least* bound derivable from the local relaxed inequalities
alone. It is sharp — the blow-up witness attains it — but it is **not
necessary**: it discards the signs of the local gaps.

**The signed accumulation.** Keep the signs. The resulting quantity `Q_{i,1}`
does not merely bound the gain, it **equals** it. So it is necessary and
sufficient by construction, and the convergence question has an exact answer
rather than a two-sided estimate.

That the envelope is not necessary is the substantive content: a family can
have `ε·C₁` bounded away from zero while its gains vanish, because the
violations cancel rather than accumulate.

## The instance, and what it does not depend on

On the period-`3m` family the signed accumulation tends to zero, so that family
**does** have vanishing gains. A defect-vanishing family therefore is an
approximate-solution family for that weight.

**This does not consume the unaudited attribution.** The gain computation uses
only the block structure, the block survivals, and the defect asymptotic. It
does *not* use the external theorem asserting the weight admits no exact finite
cycle. So this result stands whatever the audit of that citation finds — which
is worth knowing, because `PC-009` does depend on the citation and this does
not.

## Correction to an in-house derivation

An earlier internal derivation gave the limiting coefficient as
`(4/3)·log 2`. The correct value is `1 + log 2`. The error was keeping only
the "continue forever" branch of the max; on this family the finite-stopping
branch is larger. The missing `1` is the option to select one stopping phase in
a block where the coordinate is inactive — **paid once, not once per phase**.

The substantive conclusion of that derivation survives unchanged: the
coefficient is bounded independently of the period, whereas the raw product of
period and defect stays constant only because phase-counting assigns unit
weight to increasingly negligible phases.

## Falsifiers and wrong turns

- If some family has `Q_{i,1} → 0` but gains bounded away from zero, the
  identity is wrong — it is an equality, so any counterexample kills it
  outright rather than weakening it.
- Do not substitute `ε·C₁` for `Q` in a necessity argument. It is an envelope;
  using it in the necessary direction is the error this claim exists to record.
- Do not carry the `(4/3)·log 2` figure; it is superseded.
- The `P_i = 1` case is separate and takes the value `[−r_i({i})]₊`. A family
  crossing between the regimes needs both.

## Production map

Nothing formalized. The identity is the natural first target: it is a statement
about a cyclic max-affine system with signs retained, and the repository already
has the companion-map machinery and `Math/CyclicMaxAffineBound.lean` for the
envelope side. Formalizing the identity would make the necessary-and-sufficient
statement machine-checked and give the conversion question a citable answer.

## Exit conditions

`MINED` when the general statement is decided — whether every weight admits a
defect-vanishing family with vanishing signed accumulation.
