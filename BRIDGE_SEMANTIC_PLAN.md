# FOSG Augmented-EFG Semantic Plan

## Current state

The theorem-facing bounded bridge is on the correct architecture:

- semantic infosets are encoded original player views
- semantic strategy/profile translation is implemented
- semantic augmented wrapper uses encoded public/player views
- the repo builds cleanly

What is still missing is the semantic theorem layer:

1. semantic plain bridge outcome-kernel equality with the older trace plain bridge
2. EU equality with the native bounded FOSG compile path in `GameTheory/Languages/FOSG/Compile.lean`

## Main conclusion

There is no inherent mathematical issue. The failed attempts used the wrong proof boundary.

The semantic plain bridge and the older trace plain bridge share:

- the same underlying `TracePosition` state machine
- the same chance structure
- the same terminal outcomes/payoffs

They differ only at decision nodes:

- semantic bridge labels decisions by encoded player views
- trace bridge labels decisions by control positions
- action sets are related by a canonical equivalence

So the proof should factor the **decision-node action reindexing seam**, not recursively compare whole tree definitions by broad unfolding.

## Durable helper already extracted

In `GameTheory/Languages/Bridges/FOSG/AugmentedEFG.lean`:

- `bind_eq_bind_of_equiv` (around line 2989)

This is the right local tool. It proves equality of `PMF.bind` under an action-type equivalence and matching probability/child laws.

## Correct proof boundary

Prove a local relabeling theorem at the `GameTree.evalDist` level.

Do **not** frame the main theorem first on `EFGGame.toKernelGame.outcomeKernel`; that is just `tree.evalDist`.

The reusable theorem should be about decision-node evaluation under an action equivalence.
This is already essentially what `bind_eq_bind_of_equiv` states, so Step 1 is
mostly wiring rather than a fresh foundational proof.

### Target shape

For decision nodes, prove a theorem morally of this form:

```lean
theorem evalDist_decision_relabel
  {α β Outcome}
  [Fintype α] [Fintype β]
  (e : α ≃ β)
  (μ₁ : PMF α) (μ₂ : PMF β)
  (f : α → PMF Outcome)
  (g : β → PMF Outcome)
  (hμ : ∀ a, μ₁ a = μ₂ (e a))
  (hg : ∀ a, f a = g (e a)) :
  μ₁.bind f = μ₂.bind g
```

This is exactly the role of `bind_eq_bind_of_equiv`.

## Instantiation for the bridge

At a semantic decision node corresponding to a trace decision node:

- action equivalence:
  - `Semantic.viewIndexEquivPositionIndex`
- probability compatibility:
  - `Semantic.translateBehavioralStrategy_infosetOfPosition_apply`

So the decision-node step should be:

1. rewrite both sides only to `EFG.evalDist_decision`
2. apply `bind_eq_bind_of_equiv`
3. discharge:
   - action-distribution equality using
     `Semantic.translateBehavioralStrategy_infosetOfPosition_apply`
   - child equality by the recursive/inductive hypothesis on the corresponding child positions

There is one extra local obligation before that:

- prove a tiny **chance-indexing agreement** lemma

The current expectation is that the chance branch agrees definitionally or by a
trivial `Equiv.refl`-style identification, but this should be stated and proved
explicitly before the main tree theorem so the chance branch is mechanically
simple.

## What to avoid

Do not:

- `simp [Semantic.treeFromAccum, traceTreeFromAccum]` on the full goal
- compare full `GameTree` constructors across different `InfoStructure`s
- mix replay, augmentation, and outcome semantics in one induction

Those are what caused the earlier transport blowups.

## Recommended theorem stack

## Induction measure

The tree theorem should **not** use structural induction on `GameTree`.

It should be stated and proved by strong induction on:

- `pos.remaining`

or equivalently by a well-founded recursion on the same measure.

That is the actual recursion used by `treeFromAccum`, and it avoids trying to
compare two different `GameTree` types structurally.

### Step 1

Prove a local semantic-vs-trace decision compatibility theorem:

- semantic decision-node `evalDist`
- equals trace decision-node `evalDist`
- via relabeling only

This theorem should stay in `namespace Semantic` unless
`bind_eq_bind_of_equiv` is made non-`private`.

### Step 2

Lift that to a tree theorem:

- semantic plain bridge `evalDist`
- equals trace plain bridge `evalDist`

But structure the proof so:

- terminal branch: immediate
- chance branch: same PMF / same child indexing, using the explicit
  chance-indexing agreement lemma
- decision branch: use the relabeling lemma

### Step 3

Derive outcome-kernel equality:

- semantic plain bridge outcome kernel
- equals trace plain bridge outcome kernel

### Step 4

Connect the trace plain bridge to the native bounded compile path in
`GameTheory/Languages/FOSG/Compile.lean`.

This is the next theorem after semantic-vs-trace plain equality, but it should
be treated as a separate spike first:

- determine whether the gap is another pure relabeling argument, or
- whether it requires a more explicit simulation/bisimulation theorem between
  the trace bridge machine and the native bounded compile path

Do not assume this is a one-lemma handoff until that classification is done.

### Step 5

Derive EU equality.

Once outcome kernels match, EU should be a short corollary **provided** the
utility functions are definitionally aligned. Before treating this as trivial,
check whether any outcome transport or `PMF.map` commutation is required.

## Immediate next implementation task

Resume from the current green state and prove:

1. a small decision-node relabeling theorem using `bind_eq_bind_of_equiv`
2. the semantic-vs-trace plain bridge outcome-kernel equality

Only after that, move on to the native bounded compile comparison.

## Lessons learned while implementing

1. Do not reduce `treeFromAccum` or `traceTreeFromAccum` with
   `simp [treeFromAccum]` / `simp [traceTreeFromAccum]`.
   On these well-founded recursive definitions that triggers the generated
   `.eq_1` rewrite lemmas and loops.

2. The stable reduction method is:
   - prove one-step branch lemmas
   - use `unfold treeFromAccum` / `unfold traceTreeFromAccum` once
   - then discharge the branch with `simp` on the fixed hypotheses
     `hrem`, `hterm`, `hplayer`

3. Keep the main induction purely on `pos.remaining`.
   The branch lemmas are what let the induction stay small; without them the
   proof drifts back into whole-definition comparison and stalls again.

4. The branch lemmas themselves must avoid dependent `rw` on the local branch
   equations produced by `treeFromAccum` / `traceTreeFromAccum`.
   Rewriting expressions like `pos.player? = some ...` directly into the
   generated match proof arguments breaks motive elaboration.

5. A theorem statement that quantifies over an arbitrary semantic infoset
   equal to `infosetOfPosition Ipos` is too general. It lets the action type
   drift and reintroduces the same transport seam. The stable statement should
   use `infosetOfPosition Ipos` directly.

6. The next proof attempt should not start with custom helper lemmas proved by
   `rfl` after `change`. Those branch equalities are not definitional enough.
   The better route is a generic EFG-level relabeling/simulation lemma phrased
   over already-built decision/chance nodes, and only then instantiate it for
   the bridge trees.

7. A dedicated `treeFromAccum_eq_decision` / `treeFromAccum_eq_chance` layer on
   top of `TracePosition.player?` is still the wrong boundary. `player?` itself
   unfolds through `Position.player?`, which first branches on truncation via a
   `Decidable` recursor. That means any lemma trying to normalize the whole
   `treeFromAccum` branch from just `hplayer : pos.player? = ...` recreates the
   same dependent-elimination problem in a different file.

8. The stable surface is one level lower: reason on the concrete serialized
   state cases (`.base`, `.decide`, `.chance`) and on the already-built
   decision/chance nodes, not on a whole-tree lemma indexed by `hplayer`.
   In practice this means the next theorem should compare branch-local
   `evalDist` expressions after explicit state splitting, or factor a generic
   `evalDist` lemma for already-built `GameTree.decision` / `GameTree.chance`
   nodes and instantiate that.

9. Even the `GameTree.decision` wrapper can be one layer too high for a stable
   helper theorem. On the trace side, Lean may still get stuck inferring the
   action type from the infoset wrapper. The stable reusable statement is the
   underlying `PMF.bind` equality:
   - semantic decision distribution `bind` over semantic indices
   - trace decision distribution `bind` over position indices
   related by `viewIndexEquivPositionIndex`

   In other words: land local relabeling lemmas at the `bind` level first, then
   use `evalDist_decision` only in the final tree proof.

10. Concrete-state `player?` simplification lemmas are worth extracting:
    - base + empty `orderedActive` -> `player? = none`
    - base + `current :: rest` -> `player? = some current`
    - decide-state -> `player? = some current`
    - chance-state -> `player? = none`

    These reduce branch proofs to actual game semantics instead of repeatedly
    unfolding `TracePosition.toPosition`.

11. Branch-local node equalities are still delicate if they try to rewrite the
    named binder in
    `match hplayer : TracePosition.player? G pos with ...`.
    The right direction is:
    - keep the concrete `player?` simplification lemmas,
    - build already-normalized chance/decision nodes under explicit state cases,
    - avoid direct `rw` on the match binder in the goal.

12. Even branch-normalization theorems can be too ambitious if their conclusion
    is still the full recursive term `treeFromAccum pos acc = ...`.
    In the base/empty and similar cases, `simp` does not fully discharge the
    named `match hplayer : TracePosition.player? G pos with ...` binder in the
    conclusion, even after concrete-state hypotheses are available.

    So the next step should not be another family of
    `treeFromAccum_eq_*` theorems. The remaining stable route is:
    - use the concrete `player?` lemmas to split the main proof by state,
    - form the already-built decision/chance node expressions locally,
    - and compare those local nodes directly with the bind-level helpers.

13. Even an `evalDist`-level branch-shape theorem around the full recursive term
    is still too ambitious. For example, trying to prove
    `treeFromAccum ... .evalDist = chanceNode.evalDist` for a `player? = none`
    branch still leaves the entire recursively expanded child term on the
    right-hand side after unfolding.

    Two concrete sub-lessons:
    - rewriting the named `match hplayer : ...` binder is still the wrong seam;
      if a local branch theorem is needed, split on the match rather than `rw`
      on the binder
    - but even after that, the stable comparison surface is not a
      `treeFromAccum.evalDist = ...` shape theorem; it is the already-exposed
      `PMF.bind` / `evalDist_chance` layer with child equalities supplied
      directly

14. A better comparison surface than `GameTree.evalDist` is a direct recursive
    PMF semantics for the semantic and trace bridges:
    - `Semantic.runDistAccum`
    - `Semantic.traceRunDistAccum`

    These recurse on `TracePosition.remaining` directly and differ only at the
    decision-node bind, which is exactly the seam handled by
    `decision_bind_eq_of_children_eq`.

    This does not finish the proof by itself, but it removes one entire layer
    of `GameTree` constructor noise. The remaining comparison should target
    these recursive PMF definitions first, and only then reconnect them to
    `treeFromAccum.evalDist` / `traceTreeFromAccum.evalDist`.

## File organization

The Step 1-3 theorem stack should not grow `AugmentedEFG.lean` further.

Preferred destination:

- `GameTheory/Languages/Bridges/FOSG/SemanticEquiv.lean`

This file should import `AugmentedEFG` and contain only:

- the relabeling lemma(s)
- semantic-vs-trace plain bridge outcome-kernel equality
- any immediate corollaries needed before the native compile comparison
