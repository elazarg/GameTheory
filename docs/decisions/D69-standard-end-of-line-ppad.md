# D69: standard End-of-Line and the PPAD interface

Status: adopted for the standard raw target and local PPAD classification;
serialized circuit normalization remains open.

## Question and alternatives

EXP-161 compares compiling normalized circuit instances with anchoring PPAD
directly to standard raw witnesses. The standard condition treats the origin
asymmetrically: an outgoing inconsistency there is an answer; an incoming
inconsistency alone is not. See [Daskalakis, Goldberg and Papadimitriou,
Section 3.1](https://www.cs.ox.ac.uk/people/paul.goldberg/papers/SICOMP-dgp09.pdf).

## Evidence and limits

Generic normalization preserves consistent edges and endpoints. Its word
computations have actual FP certificates. The raw verifier has polynomial
execution and balanced witnesses, with finite totality under weak source
promises. Broken initial links and isolated inconsistent pointers distinguish
the conventions in checked fixtures.

A certified identity-instance reduction from raw search to filtered-edge
search decodes every target answer, returning the origin for a broken initial
link. This establishes filtered-edge hardness. The reverse direction still
needs a machine that emits serialized normalized circuits. Upstream uniform
unrolling and typed hardwiring do not alone certify serialized restriction or
substitution in FP. Polynomial circuit-size existence is insufficient.

## Decision

Use the standard raw relation directly as the PPAD reference problem. Keep
PPAD, hardness and completeness definitions in the local public namespace,
with machine-specific relations and builders in backend leaves. Membership
requires independent FNP verification and balance, as well as a certified
search reduction. A target totality theorem and decoder alone cannot verify
arbitrary source witnesses.

Raw End-of-Line is complete by definition; PPAD lies in TFNP. Filtered-edge
search is PPAD-hard, with membership explicitly pending the serialized
compiler. No Nash search completeness follows from these foundations.
The base graph mathematics remains independent of optional dependencies.

Next: validate an FP serialized prefix restriction/substitution operation,
then normalized instance emission and concrete mathematical reductions.
Exact commands and validation evidence belong to EXP-161.
