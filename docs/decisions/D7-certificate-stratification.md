# D7: no certificate stratification in v1

- **Status:** rejected for v1; reopenable on a named transfer that the shared
  target cannot carry
- **Date:** 2026-07-28
- **Experiment IDs:** EXP-009, EXP-014, EXP-015

**Decision:** Do not introduce named adequacy certificates stratified by
preservation level. Languages compile into the shared static form by ordinary
functions, and a transfer between them is function composition, which needs no
witness.

## What the budget required

A certificate level earns its place only against the bespoke bridge it replaces.
The recorded conditions were: fields stating independently meaningful
preservation facts rather than the target theorem; declaration plus construction
at most twice its direct baseline; either two downstream consumers or one
checked composition; consumers reusing the compiler's named evaluation theorem
rather than reproving it; and no more than a 25% elaboration penalty.

## The measurement

Two native shapes were encoded — an influence diagram and a two-round
simultaneous game — and both taken to a `GameForm`. The evidence is
`GameTheory/Tests/Transfer.lean`.

| Cost of reaching the static core | per language |
|---|---:|
| new structures | 0 |
| new constructions discharging certificate fields | 0 |
| new evaluation theorems | 0 |
| declarations added | 1 `def`, applying an existing function |

Both languages obtain their outcome law from the *same* theorem,
`ExecutionProtocol.toGameForm_play`, instantiated twice. Nothing is reproved per
language, and every static concept — `IsNash`, `WeaklyDominates`, and the rest —
applies without either language contributing a definition or a lemma.

So the baseline a certificate level would have to beat is zero. It cannot: a
record plus its composition laws plus a construction per language is strictly
more than nothing, and it would enable no theorem that composition does not
already give.

## Why this was not obvious in advance

The earlier evidence pointed the same way from a different direction. Auditing a
compositional presentation that *does* carry its equilibrium as a field found
that the carried predicate was derivable from the native semantics, that each
constructor hand-wrote its own optimality condition, and that its contravariant
channel had no consumer at all. A stored witness for something already derivable
is how a certificate hierarchy decays into duplicated concepts.

## Scope of the rejection

This applies to languages that compile *into* a shared target. It says nothing
about a transfer between two languages that must preserve something the target
forgets — recall, or the identity of a decision site. That is where a
certificate could still earn its place, and no such transfer exists here yet.

## Result

Reject for v1. Keep compilation as functions and named evaluation theorems.
Reopen only on a concrete transfer that the shared static form provably cannot
carry, and measure that transfer against its direct bridge before adding a
level.

## Consequences for public API

No `Adequacy` record, at any level. A language exposes its protocol and whatever
named laws its own semantics justify. Downstream transfer is composition, and
the compiled `GameForm` is the meeting point.

---

## Second measurement (2026-07-29)

The first rejection was for want of a consumer. A candidate consumer has since
appeared and been examined, and the rejection stands for a stronger reason.

**Experiment ID:** EXP-019.

The pinned snapshot proves the behavioral-from-mixed direction of the
strategy-representation equivalence not from recall but from three conditions
about reach mass, with recall demoted to sufficient. Structurally those are named
adequacy certificates, and restating the theorem over them would have been the
first real consumer of a certificate level. Two things came out of trying.

*The generality is real but is not where the snapshot puts it.* Nothing in the
proof reads a player's record except through the set of policies it rules out,
so the hypothesis the theorem needs is that two histories a player cannot tell
apart constrain its policy the same way. That is strictly weaker than recall —
a player forgetting the order of its own moves satisfies it and fails recall —
and the whole direction now runs on it. One condition, not three.

*Two of the three conditions have no content in this layer, and one of those
findings is a theorem rather than an argument.* The snapshot must assume that
reaching a state factors player by player, because it conditions on reach
probability and reach is not a product event. Here the conditioning event is a
product event by construction, so the corresponding split is proved
unconditionally about the law type. The mass condition has no counterpart at
all: no reach mass is ever formed.

So the level's content does not survive the move into this architecture. It is
not that nothing consumes it; it is that after the layer's own construction is
taken into account, there is nothing left for it to say. That is a stronger
result than the first measurement and it points the same way.

**Unchanged:** the rejection remains scoped to what has been examined. A
transport between two languages preserving something the shared target forgets
would still be a different question, and no such transport exists here.
