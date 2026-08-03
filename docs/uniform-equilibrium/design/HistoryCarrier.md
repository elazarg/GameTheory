# Design record: the history carrier and `Hist.StartsAt`

Status: **evaluated by prototype, not adopted.** Dated 2026-08-04.

## The question

`GameTheory.StochasticGame.Hist` is

```lean
StageRecord t = Fin t → State × JointAct
Hist t        = StageRecord t × State
```

— the record of `t` completed stages, plus the current state stored
*separately*. Nothing at the type level links entry `i` to entry `i+1`, or
the last entry to the current state. It is a deliberately loose carrier: the
dynamics enter only through `histDist`, whose support is the genuine plays.

Consequently `appendHist` (`PublicSuffixHistory.lean`)

```lean
appendHist base suffix = (Fin.append base.1 suffix.1, suffix.2)
```

**discards `base.2`**, the base's current state: it appears neither in the
result's record nor as the result's current state. `Hist.StartsAt`
(`PublicTerminalChildDispatcher.lean`) supplies exactly that missing boundary
state:

```lean
StartsAt state h = match length with
  | 0     => h.2 = state
  | _ + 1 => (h.1 0).1 = state
```

`suffix.StartsAt base.2` is threaded through the dispatcher lemmas, where it
does **two** jobs:

1. *recoverability* — without it `appendHist` is not injective in the base,
   since two bases differing only in current state give the same append
   (`terminalBase_eq_of_appendHist_eq` takes it on both sides); and
2. *fixed-depth branch-cone disjointness*, which follows from (1) and is what
   makes the terminal-child dispatcher well defined.

The question evaluated here: would a different carrier remove this?

## The candidate

```lean
Path S A t = S × (Fin t → A × S)
```

an initial state followed by `t` `(action, resulting state)` pairs, with the
current state *computed* rather than stored.

## Prototype

`experiments/PathCarrierPrototype.lean` (untracked; run with
`lake env lean`). It compiles clean. Results:

**(1) Prefix recovery becomes unconditional — confirmed.**

```lean
theorem take_append_left (base : Path S A m) (suffix : Path S A n) :
    take (append base suffix) ⟨m, by omega⟩ = base
```

No boundary hypothesis, four lines of proof. `append_left_injective` follows
immediately, also unconditionally — so branch-cone disjointness no longer
needs `StartsAt`.

**(2) Consecutive-stage continuity becomes structural — confirmed, and this
is a stronger property than mere removal of redundancy.** `stateAt` assigns
exactly one state per position, so the source state of stage `i+1` *is* the
result state of stage `i` by construction. A chaining hypothesis is not
merely unnecessary, it is inexpressible.

**(3) A boundary predicate survives — confirmed.** With a nonempty suffix,
`current (append base suffix) = current suffix` needs no hypothesis. With an
*empty* suffix the append's current state is the base's, so the equation
genuinely requires `suffix.1 = current base`. Semantic composition still
needs a predicate; only the recoverability role is eliminated.

**(4) `StartsAt` becomes a theorem, not an obligation.**

```lean
theorem startsAt_toHist (h : Path S A t) : Hist.StartsAt h.1 (toHist h)
```

by `rfl` in both cases, where `toHist` denotes a `Path` as a `Hist`. The
image of `toHist` is exactly the chained histories, so the candidate carrier
is the well-formed part of the production one.

**(5) Transport cost — measured, and it is the *length* dimension only.** The
single proof that did not go through first time was `current_append_zero`,
needing a case split on `m` plus an explicit `Fin.castAdd` / `Fin.append_left`
rewrite, because `m + 0` and `Fin.append` do not reduce definitionally. **No
`HEq` arose anywhere.** The prototype deliberately does *not* index `Path` by
start/end state; that variant would add a second, more pervasive transport
dimension and was not measured.

## Verdict

The design works and its benefit is real but bounded: recovery and cone
disjointness become unconditional, semantic composition still needs a
boundary predicate, and continuity becomes structural. The cost is
translating every API that consumes a directly indexed `(state, action)`
record — `Basic.lean` and the whole `Public*` layer.

**Not adopted.** The benefit does not justify changing the spine on its own.
It should be revisited if the public-history layer is extracted to `Math`
(see the `Stochastic → Math` review), since that migration would touch the
same APIs anyway and the two changes share their cost.

## Corrections folded in

Three claims made during the analysis were wrong and are corrected here:

* "Concatenation cannot be type-correct" — false. `appendHist` is perfectly
  type-correct; it cannot enforce semantic boundary compatibility *through
  its type*.
* The candidate representation was described as merely removing redundancy.
  It does more: it makes continuity structural, per (2).
* `terminalSuffixLE_appendHist_heq` was cited as evidence that a stricter
  carrier would cost `HEq` transport. It is evidence of *arithmetic-index*
  transport caused by lengths, and says nothing about state indexing. The
  prototype confirms the length dimension exists and produced no `HEq` at all.
