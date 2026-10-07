# D70: serialized circuit prefix restriction

Status: adopted for positive live arity and exact raw-code evaluation.

## Question and alternatives

EXP-162 compares two layouts for hardwiring a seed. The smaller layout adds
only seed constants and conditionally remaps old input references. The chosen
layout adds seed constants and copies of all live inputs, then uniformly shifts
every original reference by the live width. Unary reference encoding turns
that shift into a ruler prefix, simplifying actual polynomial-time emission.

## Representative slice and measurements

The slice includes a shared-gate diamond, invalid forward references, empty
circuits, zero live width, missing unary terminators, truncated gates and
trailing garbage. After the new prefix executes, the memo is
`input ++ seed ++ input`. Dropping its first live-width block recovers the old
memo `seed ++ input`; upstream relocation semantics gives exact optional
agreement, including reference failures.

Constant-prefix serialization is linear in seed length. Live-copy serialization
has length `n * (n + 4)`. A declared-count scanner relocates old unary references
with a polynomial bound on every intermediate state. The exact syntax validator
uses a linear state bound and proves acceptance equivalent to successful raw
circuit decoding. Cobham bounded recursion and iteration supply actual FP
certificates; output lengths are supporting evidence, not execution proofs.

## Kill conditions and observations

An empty source circuit would acquire the last prefix gate as an unintended
output. A checked fixture preserves this failure of unguarded hardwiring.
The final compiler explicitly rejects empty circuits. It also rejects zero live
width because this gate basis needs an existing wire to construct constants.
Its evaluation theorem therefore assumes positive live width.

The raw relocation scanner discards unconsumed suffixes, so canonical-code
agreement alone does not guarantee correctness for arbitrary words. Exact
syntax validation precedes emission. Invalid topology is preserved rather than
repaired. The resulting theorem equates optional evaluation for every source
code at the stated positive live width; malformed syntax remains rejected.

## Decision and next action

Keep the word compiler and machine evidence in backend leaves of the optional
package. Its public word functions use locally owned names; raw gate types
appear only in canonical correctness lemmas. Do not introduce a generic
compiler certificate hierarchy.

Adopt the larger uniform-relocation prefix after the semantic and FP slice
passes. Exact commands and axiom evidence are recorded in EXP-162. Next connect
uniform machine unrolling to this compiler and emit normalized End-of-Line
circuit vectors. This component alone does not establish the reverse search
reduction or filtered endpoint PPAD membership.
