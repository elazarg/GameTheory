# D77: native computation certificates and directed-parity classes

Status: adopted for the successor backend API; downstream delivery and final
stable-toolchain verification remain tracked in the delivery ledger.

Experiment: [EXP-172](../ExperimentLog.md#exp-172-native-cslib-computation-certificates-and-search-classes).

The competing choices were to recreate the historical Cobham/FPn interface and
local search-class calculus around the successor, or to use its encoded machine
certificates, search reductions and classes directly. The former would preserve
two computation interfaces and leave class membership tied to our chosen raw
reference relation. The native interface already supports arbitrary encoded
instance types, source-aware answer decoders, and composition.

Use native `ComputableInPolyTime`, `SearchReducible`, `FNP`, `TFNP`, `PPAD`,
`SearchHard` and `SearchComplete`. Do not introduce compatibility aliases or a
replacement reduction record. Concrete game relations retain their own codecs;
native framed inputs are an internal machine argument convention. Independent
source verification and witness bounds remain requirements for membership.

The representative arithmetic slice preserves exact bytes, including underflow,
negative zero, truncation and multiplication's bit-dependent width. Uniform
native circuit families have certified concrete serializers and evaluators;
polynomial circuit size alone is insufficient. In particular, arbitrary binary
wire numbers cannot be serialized to unary merely from a short output claim.
The serializer explicitly caps references, and its cost includes writing them.

Native End-of-Line suppresses inactive edges and masks the origin. Directly
identifying it with arbitrary concrete pointers would be false. Filtered incoming
pointers and the native filtered outgoing map fix this difference. Uniform
compilation realizes these maps on the prescribed cube, including width zero.
Every concrete endpoint or raw answer decodes to a native answer; failed source
promises return the native zero witness. Both concrete relations are therefore
complete for native PPAD, rather than complete by a local definition. This
supersedes D69's local class definitions and the backend-specific compilation
route of D70/D71; their mathematical distinctions and earlier evidence remain.

The probability slice uses native PPT program laws. Saved random tapes preserve
the full PMF law, and intrinsic-halting compilation supplies one machine before
the sample degree is chosen. Serialization and its parameter-polynomial input
bound are explicit. No new probability semantics or claim that every rational
sampler is a bounded fair-coin machine follows.

EXP-172's kill conditions remain: losing any target answer, changing a canonical
relation or PMF law, inferring runtime from output size, or resolving optional
packages from the base invalidates the design. Its measured slice supports the
native choice. All declarations remain subject to transitive axiom auditing.

The optional package boundary of D67 is unchanged. The successor's larger
probability closure needs newer Mathlib infinite-sum APIs than stable 4.35.
Validation in an isolated matching-toolchain source copy does not adopt an RC
in the repository. Shared final-release upgrades follow normal maintenance;
full downstream builds, lint, axioms and local/published consumers must pass
before the migration is ready to merge.
