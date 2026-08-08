# Design record: the history carrier and `Hist.StartsAt`

Status: **two candidates evaluated by prototype; neither adopted.** The
first candidate was rejected for a stronger reason than originally recorded;
a second, better candidate is identified but unpriced. Dated 2026-08-04,
revised the same day after review.

## The question

`GameTheory.StochasticGame.Hist` is

```lean
StageRecord t = Fin t → State × JointAct
Hist t        = StageRecord t × State
```

Appending (`UniformEquilibrium/Certificates/Public/SuffixHistory.lean`) is

```lean
appendHist base suffix = (Fin.append base.1 suffix.1, suffix.2)
```

which **discards `base.2`**, the base's current state. `Hist.StartsAt`
(`UniformEquilibrium/Certificates/Public/TerminalChildDispatcher.lean`) supplies exactly that missing state,
and `suffix.StartsAt base.2` is threaded through the dispatcher lemmas.

## What is really being chosen

At a seam, the base's terminal state and the suffix's initial state are **two
copies of one semantic datum**. Any concatenation must drop one. The choice
is *which*, and each choice makes one side of the API unconditional and the
other side conditional:

| | production `appendHist` | candidate A `Path` |
| --- | --- | --- |
| drops | `base.2` | `suffix.1` |
| prefix side | needs `StartsAt` (`terminalPrefix_appendHist`, `terminalBase_eq_of_appendHist_eq`) | **free** |
| suffix side | **free** (`terminalSuffix_appendHist`, `appendHist_injective`) | needs the boundary predicate; injectivity in the suffix *fails* |

So candidate A does not eliminate the boundary predicate. It **relocates**
it from the prefix side to the suffix side.

The suffix side is not idle: `appendHist_injective`
(`UniformEquilibrium/Certificates/Public/CausalStoppingEventRatio.lean:395`) is unconditional and drives the
`PMF.map` argument in `histDistAfter_apply_appendHist`. Losing it is a real
cost, and the first version of this record did not price it.

## Candidate A: `Path t = S × (Fin t → A × S)`

Prototype: `experiments/PathCarrierPrototype.lean` (untracked, compiles
clean).

Genuine result:

```lean
theorem take_append_left (base : Path S A m) (suffix : Path S A n) :
    take (append base suffix) ⟨m, by omega⟩ = base
```

unconditional, hence `append_left_injective` and cone disjointness likewise.

Measured cost, which the first version of this record omitted:

```lean
theorem append_not_injective_in_suffix :
    ∃ (base s₁ s₂ : Path Bool Unit 0), s₁ ≠ s₂ ∧ append base s₁ = append base s₂
```

Two suffixes differing only in their dropped initial state have the same
append. The dual of production's `appendHist_injective` is therefore false
here.

**Verdict: rejected**, and more decisively than first recorded. At nearly
every call site the relocation is a wash — the splice proofs
(`FixedDepthAdaptivePotentialSplice.lean:73-75`) use the prefix lemma with
`hstart` and the suffix lemma without; under candidate A they would use the
same hypothesis at the other lemma. The one clean win, unconditional cone
disjointness, arrives at sites that already have `hstart` in scope, because
the dispatcher only ever decomposes genuine plays.

## Candidate B: split the two roles

Histories stay rooted; continuations become **unrooted** — `Cont n = Fin n →
A × S`, with the start state supplied by context. Then `appendCont` uses the
base's terminal state as the source state of the continuation's first stage,
so **nothing is dropped**:

```lean
theorem baseState_appendCont (base : Hist S A m) (c : Cont S A (n+1)) :
    ((appendCont base c).1 (Fin.natAdd m ⟨0, _⟩)).1 = base.2
theorem histTake_appendCont (base : Hist S A m) (c : Cont S A n) (i : Fin m) :
    (appendCont base c).1 (Fin.castAdd n i) = base.1 i
theorem appendCont_injective (base : Hist S A m) :
    Function.Injective (appendCont base : Cont S A n → Hist S A (m + n))
```

All unconditional, all verified in the prototype. Both sides are recoverable
and the boundary predicate **genuinely disappears** rather than migrating,
because a continuation cannot carry a competing copy of the seam state.

Cost, unpriced: suffixes stop being the same type as histories, so every
`histDistAfter`-shaped signature changes. This is the only design on the
table that delivers what candidate A was hoped to deliver, and it is the one
to price if this is reopened.

## Corrections to the first version of this record

Five claims were wrong; all are corrected above.

1. **"The candidate is the well-formed part of the production carrier."**
   False. The two carriers are **isomorphic** — `Hist t` stores `t+1` states
   and `t` actions, exactly as `Path t` does, and no state appears twice, so
   there is no chaining condition a `Hist` could violate. Verified by
   constructing the inverse:
   `theorem toHist_ofHist (h : Hist S A t) : toHist (ofHist h) = h`.
2. **"Continuity becomes structural" is a benefit of the candidate.** It is
   equally true of the production carrier, for the same reason, so it is not
   a differentiator at all.
3. **"`Hist` stores the current state redundantly."** It does not: the record
   covers positions `0 … t-1` and `h.2` is position `t`.
4. **"The benefit is that the boundary predicate is removed."** For candidate
   A it is relocated, not removed. Only candidate B removes it.
5. **"Concatenation cannot be type-correct."** `appendHist` is perfectly
   type-correct; it cannot enforce boundary compatibility *through its type*.

A sixth correction from the previous revision stands: the production
`terminalSuffixLE_appendHist_heq` is evidence of *arithmetic-index* transport
from length subtraction, not of state-indexing friction. The prototype
reproduced exactly that length-dimension transport (`current_append_zero`
needed a case split plus explicit `Fin.castAdd` / `Fin.append_left`) and
produced **no `HEq` at all**.

## Provenance

The dual-side accounting, the isomorphism correction, and candidate B are due
to a review of the first version of this record. The prototype was extended
to verify each of them rather than accept them on argument; every claim above
that is stated as a Lean theorem compiles.
