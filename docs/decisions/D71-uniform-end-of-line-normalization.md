# D71: uniform normalized End-of-Line instances

Status: adopted for the optional complexity companion.

## Question and alternatives

EXP-163 tests whether normalization can emit actual circuit instances in FP.
Direct gate substitution would require another serialized compiler and its
execution proof. The selected route specializes uniform circuits for the
already certified normalized pointer evaluators. Circuit-size existence alone
would fail the gate: the reduction requires a polynomial-time word mapper.

## Representative slice and measurements

The upstream unconditional uniform-containment target builds on the pinned
Lean/Mathlib toolchain in 3,361 jobs without diagnostics, taking approximately
15 minutes locally. Its 435-module source closure includes upstream Turing
machine helper routines and has no placeholders, custom axioms, `native_decide`
or `ofReduceBool`. The final companion axiom audit checks the compiled claims
transitively; exact validation is recorded in EXP-163.

The scalar query computes one normalized pointer bit from a fixed instance,
unary coordinate and live vertex. The uniform generator is FL-certified and
therefore FP-certified. Validated prefix restriction fixes the instance and
coordinate while preserving exact evaluation. Bounded recursion emits the
coordinates in ascending order. If scalar code size is bounded by `p(m)`, its
accumulator has bound `n * (2*p(m) + 2)`, represented by a Cobham length bound.
The proof certifies the machine construction, not just the final output size.

## Kill conditions and observations

No vertex enumeration or nonuniform circuit choice replaces the instance map.
Uniform-family existence supplies a single certified word generator. The
positive live-width requirement is derived from the genuine-source promise:
at width zero both pointers return the origin, contradicting a nontrivial
successor. Invalid source promises map to `[]`, which accepts exactly the empty
raw witness. This includes malformed input and zero-width cases.

Serialized normalized pointers agree at every vertex of the original width.
Their outputs retain that width, so nested predecessor/successor evaluations
stay within the agreement theorem. Every raw target answer is an original
non-origin endpoint; the FPn decoder returns it unchanged. The existing forward
reduction and this reverse reduction prove filtered endpoint PPAD completeness.

## Decision and next action

Keep uniform generation, prefix compilation and vector emission in separate
backend leaves. Expose their word operations and narrow correctness theorems;
the final mapper is existentially certified, without a new certificate hierarchy
or public choice of backend machines. The base library acquires no dependency.

Adopt the specialization route. This discharges the encoding equivalence and
PPAD membership gap. Next deliver a concrete Sperner/Brouwer reduction on these
search APIs before attempting Nash search completeness; approximation and FIXP
conventions remain distinct obligations.
