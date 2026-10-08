# D68: succinct End-of-Line endpoint search

Status: adopted for consistent-edge endpoint search; PPAD convention agreement
remains open.

## Question and competing designs

EXP-160 asks whether a genuine total search relation can be polynomially
verified without enumerating an exponential vertex set. Explicit pointer tables
are straightforward but cannot validate succinct circuit search. Circuit-coded
successor/predecessor vectors can, provided serialization, lookup and evaluation
have actual machine bounds.

A second choice concerns malformed pointers and source promises. Requiring
global inverses excludes hostile inputs. Instead, define edges by locally
consistent nontrivial pointers and accept exactly the vertices incident to one
such edge. Require agreement on the distinguished source's outgoing edge;
invalid promises receive an empty witness. This totalization is explicit in the
relation and its verifier.

## Representative slice and measurements

The slice joins `Math.EndOfLine` finite cardinality totality to serialized circuit
vectors, fixed-width binary words, exact endpoint verification and upstream TFNP.
`Backend.SearchReduction` supplies only efficient instance mapping,
original-instance decoding and preservation of every target solution.

Vector serialization has exactly `2 * sum(code lengths) + 2 * output count`
bits. Evaluation appends exactly the supplied vertex's number of bits, using a
verified scalar circuit machine and polynomial-time bounded code selection.
The verifier performs a constant number of pointer evaluations. Accepted
witness length is at most the input length. These length facts supplement actual
FP certificates rather than substituting for execution bounds.

The representative slice proves finite-word totality, exact verifier correctness,
a single polynomial-time verifier machine and TFNP membership. Exact validation
commands and transitive axiom evidence are recorded in EXP-160.

## Kill conditions and observations

The kill conditions were runtime depending on `2^n`, short output used as a
runtime argument, endpoint totality relying on global inverse assumptions, or a
supposedly total relation that excludes malformed inputs. None is needed by the
selected implementation.

The usual weaker source conditions alone do not suffice for this filtered-edge
endpoint convention: a broken initial link can leave no incident edges at all.
An explicit counterexample preserves that failure. The broader raw
pointer-inconsistency witness condition can also accept isolated vertices that
the endpoint verifier rejects. This narrows the result to the stated endpoint
convention; it does not freeze a PPAD class or claim Nash PPAD-completeness.

The benchmark formulation in [Daskalakis, Goldberg and Papadimitriou,
Section 3.1](https://www.cs.ox.ac.uk/people/paul.goldberg/papers/SICOMP-dgp09.pdf)
also treats the origin asymmetrically: an outgoing pointer inconsistency there
is an accepted answer, while another source must differ from the origin. The
next normalization must preserve that distinction, including broken initial
links, rather than excluding the origin from both raw inconsistency cases.

## Decision and next action

Keep generic finite graph totality in the dependency-free base package and all
circuit/machine evidence in the existing optional companion. Use the linear
head-prefix circuit list encoding, not a variable-arity tuple encoding that
repeatedly doubles its tail. Retain total scalar decoding and exact-width
witnesses rather than introducing a global syntax-validation obligation.

Keep search reductions small. In particular, target TFNP and a search reduction
do not establish source FNP: an efficient decoder can ignore arbitrarily large
or undecidable extra source witnesses. Source verification and balance remain
independent premises.

Next, normalize against the usual raw End-of-Line convention, then define the
corresponding PPAD class and develop concrete reductions in dependency order.
Brouwer/Sperner and Nash completeness remain mathematical reductions to prove.
